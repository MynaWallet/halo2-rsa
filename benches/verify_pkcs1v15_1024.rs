use criterion::{black_box, criterion_group, criterion_main, Criterion};
use halo2_dynamic_sha256::{Sha256Chip, Sha256Config, Table16Chip};
use halo2_rsa::{
    big_integer::{BigIntConfig, UnassignedInteger},
    RSAChip, RSAConfig, RSAInstructions, RSAPubE, RSAPublicKey, RSASignature, RSASignatureVerifier,
};
use halo2wrong::{
    curves::FieldExt,
    halo2::{
        circuit::SimpleFloorPlanner,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error, Fixed, Instance, ProvingKey, VerifyingKey,
        },
        poly::{
            commitment::CommitmentScheme,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverGWC, VerifierGWC},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    },
};
use maingate::{
    decompose_big, MainGate, MainGateInstructions, RangeChip, RangeInstructions, RegionCtx,
};
use num_bigint::BigUint;
use rand::rngs::OsRng;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct Pkcs1v15BenchConfig {
    rsa_config: RSAConfig,
    sha256_config: Sha256Config,
}

struct Pkcs1v15BenchCircuit<F: FieldExt> {
    signature: RSASignature<F>,
    public_key: RSAPublicKey<F>,
    msg: Vec<u8>,
    _f: PhantomData<F>,
}

impl<F: FieldExt> Pkcs1v15BenchCircuit<F> {
    const BITS_LEN: usize = 1024;
    const LIMB_WIDTH: usize = RSAChip::<F>::LIMB_WIDTH;
    const EXP_LIMB_BITS: usize = 5;
    const DEFAULT_E: u128 = 65537;
    fn rsa_chip(&self, config: RSAConfig) -> RSAChip<F> {
        RSAChip::new(config, Self::BITS_LEN, Self::EXP_LIMB_BITS)
    }
    fn sha256_chip(&self, config: Sha256Config) -> Sha256Chip<F> {
        Sha256Chip::new(config)
    }
}

impl<F: FieldExt> Circuit<F> for Pkcs1v15BenchCircuit<F> {
    type Config = Pkcs1v15BenchConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!();
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // 1. Configure `MainGate`.
        let main_gate_config = MainGate::<F>::configure(meta);
        // 2. Compute bit length parameters by calling `RSAChip::<F>::compute_range_lens` function.
        let (composition_bit_lens, overflow_bit_lens) =
            RSAChip::<F>::compute_range_lens(Self::BITS_LEN / Self::LIMB_WIDTH);
        // 3. Configure `RangeChip`.
        let range_config = RangeChip::<F>::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );
        // 4. Configure `BigIntConfig`.
        let bigint_config = BigIntConfig::new(range_config.clone(), main_gate_config.clone());
        // 5. Configure `RSAConfig`.
        let rsa_config = RSAConfig::new(bigint_config);
        // 6. Configure `Sha256Config`.
        let table16_congig = Table16Chip::configure(meta);
        let sha256_config =
            Sha256Config::new(main_gate_config, range_config, table16_congig, 128 + 64);
        Self::Config {
            rsa_config,
            sha256_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2wrong::halo2::circuit::Layouter<F>,
    ) -> Result<(), Error> {
        let rsa_chip = self.rsa_chip(config.rsa_config);
        let sha256_chip = self.sha256_chip(config.sha256_config);
        let bigint_chip = rsa_chip.bigint_chip();
        let main_gate = rsa_chip.main_gate();
        // 1. Assign a public key and signature.
        let (public_key, signature) = layouter.assign_region(
            || "rsa signature with hash test using 2048 bits public keys",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                let sign = rsa_chip.assign_signature(ctx, self.signature.clone())?;
                let public_key = rsa_chip.assign_public_key(ctx, self.public_key.clone())?;
                Ok((public_key, sign))
            },
        )?;
        // 2. Create a RSA signature verifier from `RSAChip` and `Sha256BitChip`
        let verifier = RSASignatureVerifier::new(rsa_chip, sha256_chip);
        // 3. Receives the verification result and the resulting hash of `self.msg` from `RSASignatureVerifier`.
        let (is_valid, hashed_msg) = verifier.verify_pkcs1v15_signature(
            layouter.namespace(|| "verify pkcs1v15 signature"),
            &public_key,
            &self.msg,
            &signature,
        )?;
        // 4. Expose the RSA public key as public input.
        for (i, limb) in public_key.n.limbs().into_iter().enumerate() {
            main_gate.expose_public(
                layouter.namespace(|| format!("expose {} th public key limb", i)),
                limb.assigned_val(),
                i,
            )?;
        }
        let num_limb_n = Self::BITS_LEN / RSAChip::<F>::LIMB_WIDTH;
        // 5. Expose the resulting hash as public input.
        for (i, val) in hashed_msg.into_iter().enumerate() {
            main_gate.expose_public(
                layouter.namespace(|| format!("expose {} th hashed_msg limb", i)),
                val,
                num_limb_n + i,
            )?;
        }
        // 6. The verification result must be one.
        layouter.assign_region(
            || "assert is_valid==1",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                main_gate.assert_one(ctx, &is_valid)?;
                Ok(())
            },
        )?;
        // Create lookup tables for range check in `range_chip`.
        let range_chip = bigint_chip.range_chip();
        range_chip.load_table(&mut layouter)?;
        Ok(())
    }
}

fn pkcs1v15_1024() {
    use halo2wrong::curves::bn256::{Bn256, Fr, G1Affine};
    use halo2wrong::halo2::dev::MockProver;
    use rand::{thread_rng, Rng};
    use rsa::{Hash, PaddingScheme, PublicKeyParts, RsaPrivateKey, RsaPublicKey};
    use sha2::{Digest, Sha256};

    let limb_width = Pkcs1v15BenchCircuit::<Fr>::LIMB_WIDTH;
    let num_limbs = Pkcs1v15BenchCircuit::<Fr>::BITS_LEN / Pkcs1v15BenchCircuit::<Fr>::LIMB_WIDTH;
    // 1. Uniformly sample a RSA key pair.
    let mut rng = thread_rng();
    let private_key = RsaPrivateKey::new(&mut rng, Pkcs1v15BenchCircuit::<Fr>::BITS_LEN)
        .expect("failed to generate a key");
    let public_key = RsaPublicKey::from(&private_key);
    // 2. Uniformly sample a message.
    let mut msg: [u8; 128] = [0; 128];
    for i in 0..128 {
        msg[i] = rng.gen();
    }
    // 3. Compute the SHA256 hash of `msg`.
    let hashed_msg = Sha256::digest(&msg);
    // 4. Generate a pkcs1v15 signature.
    let padding = PaddingScheme::PKCS1v15Sign {
        hash: Some(Hash::SHA2_256),
    };
    let mut sign = private_key
        .sign(padding, &hashed_msg)
        .expect("fail to sign a hashed message.");
    sign.reverse();
    let sign_big = BigUint::from_bytes_le(&sign);
    let sign_limbs = decompose_big::<Fr>(sign_big.clone(), num_limbs, limb_width);
    let signature = RSASignature::new(UnassignedInteger::from(sign_limbs));

    // 5. Construct `RSAPublicKey` from `n` of `public_key` and fixed `e`.
    let n_big = BigUint::from_radix_le(&public_key.n().clone().to_radix_le(16), 16).unwrap();
    let n_limbs = decompose_big::<Fr>(n_big.clone(), num_limbs, limb_width);
    let n_unassigned = UnassignedInteger::from(n_limbs.clone());
    let e_fix = RSAPubE::Fix(BigUint::from(Pkcs1v15BenchCircuit::<Fr>::DEFAULT_E));
    let public_key = RSAPublicKey::new(n_unassigned, e_fix);

    // 6. Create our circuit!
    let circuit = Pkcs1v15BenchCircuit::<Fr> {
        signature,
        public_key,
        msg: msg.to_vec(),
        _f: PhantomData,
    };

    // 7. Create public inputs
    let n_fes = n_limbs;
    let mut hash_fes = hashed_msg
        .iter()
        .map(|byte| Fr::from(*byte as u64))
        .collect::<Vec<Fr>>();
    let mut column0_public_inputs = n_fes;
    column0_public_inputs.append(&mut hash_fes);
    //let public_inputs = vec![column0_public_inputs];

    // 8. Generate a proof.
    let k = 18;
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk, &circuit).unwrap();
    let proof = {
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[&column0_public_inputs]],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };
    // 9. Verify the proof.
    {
        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(verify_proof::<_, VerifierGWC<_>, _, _, _>(
            &params,
            pk.get_vk(),
            strategy,
            &[&[&column0_public_inputs]],
            &mut transcript
        )
        .is_ok());
    }
}

fn pkcs1v15_1024_benchmark(c: &mut Criterion) {
    c.bench_function("pkcs1v15 1024 bits", |b| b.iter(|| pkcs1v15_1024()));
}

criterion_group!(benches, pkcs1v15_1024_benchmark);
criterion_main!(benches);
