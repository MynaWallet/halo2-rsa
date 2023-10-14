use super::utils::decompose_biguint;
use crate::{AssignedBigUint, BigUintInstructions, Fresh, Muled, RangeType, RefreshAux};
use halo2_base::halo2_proofs::plonk::Error;
use halo2_base::utils::fe_to_bigint;
use halo2_base::QuantumCell;
use halo2_base::{
    gates::{flex_gate::GateChip, range::RangeChip, GateInstructions, RangeInstructions},
    utils::{bigint_to_fe, biguint_to_fe, fe_to_biguint, BigPrimeField},
    AssignedValue, Context,
};
use halo2_ecc::bigint::{
    big_is_equal, big_is_zero, mul_no_carry, select, sub, FixedOverflowInteger, OverflowInteger,
};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};

#[derive(Clone, Debug)]
pub struct BigUintConfig<F: BigPrimeField> {
    pub range: RangeChip<F>,
    pub limb_bits: usize,
}

impl<F: BigPrimeField> BigUintInstructions<F> for BigUintConfig<F> {
    /// Getter for [`GateChip`].
    fn gate(&self) -> &GateChip<F> {
        &self.range.gate
    }

    /// Getter for [`RangeChip`].
    fn range(&self) -> &RangeChip<F> {
        &self.range
    }

    /// Return limb bits.
    fn limb_bits(&self) -> usize {
        self.limb_bits
    }

    fn assign_integer(
        &self,
        ctx: &mut Context<F>,
        value: &BigUint,
        bit_len: usize,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        assert_eq!(bit_len % self.limb_bits, 0);
        let num_limbs = bit_len / self.limb_bits;
        let range = self.range();
        let limbs = decompose_biguint(value, num_limbs, self.limb_bits);
        let assigned_limbs: Vec<AssignedValue<F>> =
            limbs.into_iter().map(|v| ctx.load_witness(v)).collect();
        for limb in assigned_limbs.iter() {
            range.range_check(ctx, *limb, self.limb_bits);
        }
        let int = OverflowInteger::new(assigned_limbs, self.limb_bits);
        Ok(AssignedBigUint::new(int, value.clone()))
    }

    fn assign_constant(
        &self,
        ctx: &mut Context<F>,
        value: BigUint,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let num_limbs = self.num_limbs(&BigInt::from_biguint(Sign::Plus, value.clone()));
        let limbs = decompose_biguint::<F>(&value, num_limbs, self.limb_bits);
        let fixed_int = FixedOverflowInteger::construct(limbs);
        let int = fixed_int.assign(ctx).into_overflow(self.limb_bits);
        Ok(AssignedBigUint::new(int, value))
    }

    fn max_value(
        &self,
        ctx: &mut Context<F>,
        num_limbs: usize,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let value = (BigUint::from(1u64) << (self.limb_bits * num_limbs)) - BigUint::from(1u64);
        self.assign_constant(ctx, value)
    }

    fn refresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        aux: &RefreshAux,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        // For converting `a` to a [`Fresh`] type integer, we decompose each limb of `a` into `self.limb_width`-bits values.
        assert_eq!(self.limb_bits, aux.limb_bits);
        // The i-th value of `aux.increased_limbs_vec` represents the number of increased values when converting i-th limb of `a` into `self.limb_width`-bits values.
        let increased_limbs_vec = aux.increased_limbs_vec.clone();
        let num_limbs_l = aux.num_limbs_l;
        let num_limbs_r = aux.num_limbs_r;
        // The following assertion holds since `a` is the product of two integers `l` and `r` whose number of limbs is `num_limbs_l` and `num_limbs_r`, respectively.
        assert_eq!(a.num_limbs(), num_limbs_l + num_limbs_r - 1);
        let num_limbs_fresh = increased_limbs_vec.len();

        let gate = self.gate();
        let mut refreshed_limbs = Vec::with_capacity(num_limbs_fresh);
        let zero_assigned = ctx.load_zero();
        let a_limbs = a.limbs();
        (0..a.num_limbs()).for_each(|i| {
            refreshed_limbs.push(a_limbs[i]);
        });
        for _ in 0..(num_limbs_fresh - a.num_limbs()) {
            refreshed_limbs.push(zero_assigned);
        }
        let limb_max = BigInt::from(1u64) << self.limb_bits;
        for i in 0..num_limbs_fresh {
            // `i`-th overflowing limb value.
            let mut limb = refreshed_limbs[i];
            for j in 0..(increased_limbs_vec[i] + 1) {
                // `n` is lower `self.limb_width` bits of `limb`.
                // `q` is any other upper bits.
                let (q, n) = self.div_mod_unsafe(ctx, &limb, &limb_max);
                if j == 0 {
                    // When `j=0`, `n` is a new `i`-th limb value.
                    refreshed_limbs[i] = n;
                } else {
                    // When `j>0`, `n` is carried to the `i+j`-th limb.
                    refreshed_limbs[i + j] = gate.add(
                        ctx,
                        QuantumCell::Existing(refreshed_limbs[i + j]),
                        QuantumCell::Existing(n),
                    );
                }
                // We use `q` as the next `limb`.
                limb = q;
            }
            // `limb` should be zero because we decomposed all bits of the `i`-th overflowing limb value into `self.limb_width` bits values.
            gate.assert_is_const(ctx, &limb, &F::from(0));
        }
        let range = self.range();
        for limb in refreshed_limbs.iter() {
            range.range_check(ctx, *limb, self.limb_bits);
        }
        let int = OverflowInteger::new(refreshed_limbs, self.limb_bits);
        let new_assigned_int = AssignedBigUint::new(int, a.value());
        Ok(new_assigned_int)
    }

    /// Given a bit value `sel`, return `a` if `a`=1 and `b` otherwise.
    fn select<T: RangeType>(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, T>,
        b: &AssignedBigUint<F, T>,
        sel: &AssignedValue<F>,
    ) -> Result<AssignedBigUint<F, T>, Error> {
        let int = select::assign(self.gate(), ctx, a.int.clone(), b.int.clone(), *sel);
        let value = {
            if sel.value() == &F::from(1) {
                a.value().clone()
            } else {
                b.value().clone()
            }
        };

        Ok(AssignedBigUint::new(int, value))
    }

    /// Given two inputs `a,b`, performs the addition `a + b`.
    fn add(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let gate = self.gate();
        let range = self.range();
        let out_value = a.value.clone() + b.value.clone();
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let max_n = if n1 < n2 { n2 } else { n1 };
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(max_n - n1, zero_value);
        let b = b.extend_limbs(max_n - n2, zero_value);

        // Compute a sum and a carry for each limb values.
        let mut c_vals = Vec::with_capacity(max_n);
        let mut carrys = Vec::with_capacity(max_n + 1);
        carrys.push(zero_value);
        let limb_max = BigUint::from(1usize) << self.limb_bits;
        let limb_max_f = biguint_to_fe(&limb_max);
        for i in 0..max_n {
            let a_b = gate.add(
                ctx,
                QuantumCell::Existing(*a.limb(i)),
                QuantumCell::Existing(*b.limb(i)),
            );
            let sum = gate.add(
                ctx,
                QuantumCell::Existing(a_b),
                QuantumCell::Existing(carrys[i]),
            );
            let sum_big = fe_to_biguint(sum.value());
            // `c_val_f` is lower `self.limb_bits` bits of `a + b + carrys[i]`.
            let c_val = biguint_to_fe::<F>(&(&sum_big.clone() % &limb_max));
            let carry_val = biguint_to_fe::<F>(&(sum_big >> self.limb_bits));
            // `c` and `carry` should fit in `self.limb_bits` bits.
            let c = ctx.load_witness(c_val);
            range.range_check(ctx, c, self.limb_bits);
            let carry = ctx.load_witness(carry_val);
            range.range_check(ctx, carry, self.limb_bits);
            let c_add_carry = gate.mul_add(
                ctx,
                QuantumCell::Existing(carry),
                QuantumCell::Constant(limb_max_f),
                QuantumCell::Existing(c),
            );
            // `a + b + carrys[i] == c + carry`
            gate.is_equal(
                ctx,
                QuantumCell::Existing(sum),
                QuantumCell::Existing(c_add_carry),
            );
            c_vals.push(c);
            carrys.push(carry);
        }
        // Add the last carry to the `c_vals`.
        c_vals.push(carrys[max_n]);
        let int = OverflowInteger::new(c_vals, self.limb_bits);
        Ok(AssignedBigUint::new(int, out_value))
    }

    /// Given two inputs `a,b`, performs the subtraction `a - b`.
    /// The result is correct iff `a>=b`.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `a` - input of subtraction.
    /// * `b` - input of subtraction.
    ///
    /// # Return values
    /// Returns the subtraction result as [`AssignedInteger<F, Fresh>`] and the assigned bit as [`AssignedValue<F, Fresh>`] that represents whether the result is overflowed or not.
    /// If `a>=b`, the result is equivalent to `a - b` and the bit is zero.
    /// Otherwise, the bit is one.
    fn sub_unsafe(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<(AssignedBigUint<F, Fresh>, AssignedValue<F>), Error> {
        let gate = self.gate();
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let max_n = if n1 < n2 { n2 } else { n1 };
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(max_n - n1, zero_value);
        let b = b.extend_limbs(max_n - n2, zero_value);
        let limb_base = biguint_to_fe::<F>(&(BigUint::one() << self.limb_bits));

        // TODO: Underconstrained? Convert overflow int to proper int
        let a_proper =
            FixedOverflowInteger::construct(a.limbs().iter().map(|x| *x.value()).collect())
                .assign(ctx);
        let b_proper =
            FixedOverflowInteger::construct(b.limbs().iter().map(|x| *x.value()).collect())
                .assign(ctx);

        let (int, overflow) = sub::assign(
            self.range(),
            ctx,
            a_proper,
            b_proper,
            self.limb_bits,
            limb_base,
        );
        // let int_neg = negative::assign(gate, ctx, &int);
        let is_overflow_zero = gate.is_zero(ctx, overflow);
        let is_overflow = gate.not(ctx, QuantumCell::Existing(is_overflow_zero));
        // let actual_int = select::assign(gate, ctx, &int_neg, &int, &is_overflow);
        let value = {
            if a.value >= b.value {
                a.value - b.value
            } else {
                BigUint::zero()
            }
        };
        Ok((AssignedBigUint::new(int, value), is_overflow))
    }

    fn mul(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Muled>, Error> {
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let num_limbs = n1 + n2 - 1;
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(num_limbs - n1, zero_value);
        let b = b.extend_limbs(num_limbs - n2, zero_value);
        let num_limbs_log2_ceil = (num_limbs as f32).log2().ceil() as usize;
        let int = mul_no_carry::truncate(self.gate(), ctx, a.int, b.int, num_limbs_log2_ceil);
        let value: BigUint = a.value * b.value;
        Ok(AssignedBigUint::new(int, value))
    }

    fn square(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Muled>, Error> {
        self.mul(ctx, a, a)
    }

    /// Given two inputs `a,b` and a modulus `n`, performs the modular addition `a + b mod n`.
    fn add_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        // 1. Compute `a + b`.
        // 2. Compute `a + b - n`.
        // 3. If the subtraction is overflowed, i.e., `a + b < n`, returns `a + b`. Otherwise, returns `a + b - n`.
        let added = self.add(ctx, a, b)?;
        // The number of limbs of `subed` is `added.num_limbs() = max(a.num_limbs(), b.num_limbs()) + 1`.
        let (subed, is_overflow) = self.sub_unsafe(ctx, &added, n)?;
        let result = self.select(ctx, &added, &subed, &is_overflow)?;
        Ok(result.slice_limbs(0, result.num_limbs() - 2))
    }

    /// Given two inputs `a,b` and a modulus `n`, performs the modular subtraction `a - b mod n`.
    fn sub_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        // 1. Compute `a - b`.
        // 2. Compute `(a + n) - b = a - b + n`.
        // 3. If the subtraction in 1 is overflowed, i.e., `a - b < 0`, returns `a - b + n`. Otherwise, returns `a - b`.
        // The number of limbs of `subed1` is `max(a.num_limbs(), b.num_limbs())`.
        let (subed1, is_overflowed1) = self.sub_unsafe(ctx, a, b)?;
        // If `is_overflowed1=1`, `subed2` is equal to `a - b + n` because `subed1` is `b - a` in that case.
        // The number of limbs of `subed2` is `max(n.num_limbs(), subed1.num_limbs()) >= subed1.num_limbs()`.
        let added = self.add(ctx, a, n)?;
        let (subed2, is_overflowed2) = self.sub_unsafe(ctx, &added, b)?;
        self.gate()
            .assert_is_const(ctx, &is_overflowed2, &F::from(0));
        let result = self.select(ctx, &subed2, &subed1, &is_overflowed1)?;
        Ok(result.slice_limbs(0, result.num_limbs() - 2))
    }

    /// Given two inputs `a,b` and a modulus `n`, performs the modular multiplication `a * b mod n`.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `a` - input of multiplication.
    /// * `b` - input of multiplication.
    /// * `n` - a modulus.
    ///
    /// # Return values
    /// Returns the modular multiplication result `a * b mod n` as [`AssignedInteger<F, Fresh>`].
    /// # Requirements
    /// Before calling this function, you must assert that `a<n` and `b<n`.
    fn mul_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        // The following constraints are designed with reference to AsymmetricMultiplierReducer template in https://github.com/jacksoom/circom-bigint/blob/master/circuits/mult.circom.
        // However, we do not regroup multiple limbs like the circom-bigint implementation because addition is not free, i.e., it makes constraints as well as multiplication, in the Plonk constraints system.
        // Besides, we use lookup tables to optimize range checks.
        let limb_bits = self.limb_bits;
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        assert_eq!(n1, n.num_limbs());
        let (a_big, b_big, n_big) = (&a.value(), &b.value(), &n.value());
        // 1. Compute the product as `BigUint`.
        let full_prod_big = a_big * b_big;
        // 2. Compute the quotient and remainder when the product is divided by `n`.
        let (q_big, prod_big) = (&full_prod_big / n_big, &full_prod_big % n_big);

        // 3. Assign the quotient and remainder after checking the range of each limb.
        let assign_q = self.assign_integer(ctx, &q_big, n2 * limb_bits)?;
        let assign_n = self.assign_integer(ctx, n_big, n1 * limb_bits)?;
        let assign_prod = self.assign_integer(ctx, &prod_big, n1 * limb_bits)?;
        // 4. Assert `a * b = quotient_int * n + prod_int`, i.e., `prod_int = (a * b) mod n`.
        let ab = self.mul(ctx, a, b)?;
        let qn = self.mul(ctx, &assign_q, &assign_n)?;
        let gate = self.gate();
        let n_sum = n1 + n2;
        let qn_prod = {
            let value = qn.value.clone() + assign_prod.value.clone();
            let mut limbs = Vec::with_capacity(n1 + n2 - 1);
            let qn_limbs = qn.limbs();
            let prod_limbs = assign_prod.limbs();
            for i in 0..(n_sum - 1) {
                if i < n1 {
                    limbs.push(gate.add(
                        ctx,
                        QuantumCell::Existing(qn_limbs[i]),
                        QuantumCell::Existing(prod_limbs[i]),
                    ));
                } else {
                    limbs.push(qn_limbs[i]);
                }
            }
            let int = OverflowInteger::new(limbs, self.limb_bits);
            AssignedBigUint::<F, Muled>::new(int, value)
        };
        let is_eq = self.is_equal_muled(ctx, &ab, &qn_prod, n1, n2)?;
        gate.assert_is_const(ctx, &is_eq, &F::from(1));
        Ok(assign_prod)
    }

    /// Given a input `a` and a modulus `n`, performs the modular square `a^2 mod n`.
    fn square_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        self.mul_mod(ctx, a, a, n)
    }

    /// Given a base `a`, a variable exponent `e`, and a modulus `n`, performs the modular power `a^e mod n`.
    fn pow_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        e: &AssignedValue<F>,
        n: &AssignedBigUint<F, Fresh>,
        exp_bits: usize,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let gate = self.gate();
        let e_bits = gate.num_to_bits(ctx, *e, exp_bits);
        let num_limbs = a.num_limbs();
        assert_eq!(num_limbs, n.num_limbs());
        let mut acc = self.assign_constant(ctx, BigUint::one())?;
        let zero = ctx.load_zero();
        acc = acc.extend_limbs(num_limbs - acc.num_limbs(), zero);
        let mut squared = a.clone();
        for e_bit in e_bits.into_iter() {
            // Compute `acc * squared`.
            let muled = self.mul_mod(ctx, &acc, &squared, n)?;
            // If `e_bit = 1`, update `acc` to `acc * squared`. Otherwise, use the same `acc`.
            acc = self.select(ctx, &muled, &acc, &e_bit)?;
            // Square `squared`.
            squared = self.square_mod(ctx, &squared, n).unwrap();
        }
        Ok(acc)
    }

    /// Given a base `a`, a fixed exponent `e`, and a modulus `n`, performs the modular power `a^e mod n`.
    fn pow_mod_fixed_exp(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        e: &BigUint,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let num_limbs = a.num_limbs();
        assert_eq!(num_limbs, n.num_limbs());
        let num_e_bits = Self::bits_size(&BigInt::from_biguint(Sign::Plus, e.clone()));
        // Decompose `e` into bits.
        let e_bits = e
            .to_bytes_le()
            .into_iter()
            .flat_map(|v| {
                (0..8)
                    .map(|i: u8| (v >> i) & 1u8 == 1u8)
                    .collect::<Vec<bool>>()
            })
            .collect::<Vec<bool>>();
        let e_bits = e_bits[0..num_e_bits].to_vec();
        let mut acc = self.assign_constant(ctx, BigUint::from(1usize))?;
        let zero = ctx.load_zero();
        acc = acc.extend_limbs(num_limbs - acc.num_limbs(), zero);
        let mut squared = a.clone();
        for e_bit in e_bits.into_iter() {
            let cur_sq = squared;
            // Square `squared`.
            squared = self.square_mod(ctx, &cur_sq, n).unwrap();
            if !e_bit {
                continue;
            }
            // If `e_bit = 1`, update `acc` to `acc * cur_sq`.
            acc = self.mul_mod(ctx, &acc, &cur_sq, n)?;
        }
        Ok(acc)
    }

    /// Returns an assigned bit representing whether `a` is zero or not.
    fn is_zero(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        // TODO: Underconstrained
        let a_proper =
            FixedOverflowInteger::construct(a.limbs().iter().map(|x| *x.value()).collect())
                .assign(ctx);
        let out = big_is_zero::assign(self.gate(), ctx, a_proper);
        Ok(out)
    }

    /// Returns an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    fn is_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let a_proper =
            FixedOverflowInteger::construct(a.limbs().iter().map(|x| *x.value()).collect())
                .assign(ctx);
        let b_proper =
            FixedOverflowInteger::construct(b.limbs().iter().map(|x| *x.value()).collect())
                .assign(ctx);
        Ok(big_is_equal::assign(self.gate(), ctx, a_proper, b_proper))
    }

    /// Returns an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Muled`].
    fn is_equal_muled(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        b: &AssignedBigUint<F, Muled>,
        num_limbs_l: usize,
        num_limbs_r: usize,
    ) -> Result<AssignedValue<F>, Error> {
        // The following constraints are designed with reference to EqualWhenCarried template in https://github.com/jacksoom/circom-bigint/blob/master/circuits/mult.circom.
        // We use lookup tables to optimize range checks.
        let min_n = if num_limbs_r >= num_limbs_l {
            num_limbs_l
        } else {
            num_limbs_r
        };
        // Each limb of `a` and `b` is less than `min_n * (1^(limb_bits) - 1)^2  + (1^(limb_bits) - 1)`.
        let muled_limb_max = Self::compute_muled_limb_max(self.limb_bits, min_n);
        let muled_limb_max_fe = bigint_to_fe::<F>(&muled_limb_max);
        let num_limbs = num_limbs_l + num_limbs_r - 1;
        let muled_limb_max_bits = Self::bits_size(&(&muled_limb_max * 2u32));
        let carry_bits = muled_limb_max_bits - self.limb_bits;
        let gate = self.gate();
        let range = self.range();

        // The naive approach is to subtract the two integers limb by limb and:
        //  a. Verify that they sum to zero along the way while
        //  b. Propagating carries
        // but this doesn't work because early sums might be negative.
        // So instead we verify that `a - b + word_max = word_max`.
        let limb_max = BigInt::from(1) << self.limb_bits;
        let zero = ctx.load_constant(F::from(0));
        let mut accumulated_extra = zero;
        let mut carry = Vec::with_capacity(num_limbs);
        let mut cs = Vec::with_capacity(num_limbs);
        carry.push(zero);
        let mut eq_bit = ctx.load_constant(F::from(1));
        let a_limbs = a.limbs();
        let b_limbs = b.limbs();
        for i in 0..num_limbs {
            // `sum = a - b + word_max`
            let a_b_sub = gate.sub(
                ctx,
                QuantumCell::Existing(a_limbs[i]),
                QuantumCell::Existing(b_limbs[i]),
            );
            let sum = gate.sum(
                ctx,
                vec![
                    QuantumCell::Existing(a_b_sub),
                    QuantumCell::Existing(carry[i]),
                    QuantumCell::Constant(muled_limb_max_fe),
                ],
            );
            // `c` is lower `self.limb_width` bits of `sum`.
            // `new_carry` is any other upper bits.
            let (new_carry, c) = self.div_mod_unsafe(ctx, &sum, &limb_max);
            carry.push(new_carry);
            cs.push(c);

            // `accumulated_extra` is the sum of `word_max`.
            accumulated_extra = gate.add(
                ctx,
                QuantumCell::Existing(accumulated_extra),
                QuantumCell::Constant(muled_limb_max_fe),
            );
            let (q_acc, mod_acc) = self.div_mod_unsafe(ctx, &accumulated_extra, &limb_max);
            // If and only if `a` is equal to `b`, lower `self.limb_width` bits of `sum` and `accumulated_extra` are the same.
            let cs_acc_eq = gate.is_equal(
                ctx,
                QuantumCell::Existing(cs[i]),
                QuantumCell::Existing(mod_acc),
            );
            eq_bit = gate.and(
                ctx,
                QuantumCell::Existing(eq_bit),
                QuantumCell::Existing(cs_acc_eq),
            );
            accumulated_extra = q_acc;

            if i < num_limbs - 1 {
                // Assert that each carry fits in `carry_bits` bits.
                range.range_check(ctx, carry[i + 1], carry_bits);
            } else {
                // The final carry should match the `accumulated_extra`.
                let final_carry_eq = gate.is_equal(
                    ctx,
                    QuantumCell::Existing(carry[i + 1]),
                    QuantumCell::Existing(accumulated_extra),
                );
                eq_bit = gate.and(
                    ctx,
                    QuantumCell::Existing(eq_bit),
                    QuantumCell::Existing(final_carry_eq),
                );
            }
        }
        Ok(eq_bit)
    }

    /// Returns an assigned bit representing whether `a` is less than `b` (`a<b`).
    fn is_less_than(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let (_, is_overfloe) = self.sub_unsafe(ctx, a, b)?;
        // let gate = self.gate();
        // let is_overflow_zero = gate.is_zero(ctx, &overflow);
        // let is_overfloe = gate.not(ctx, QuantumCell::Existing(&is_overflow_zero));
        Ok(is_overfloe)
    }

    /// Returns an assigned bit representing whether `a` is less than or equal to `b` (`a<=b`).
    fn is_less_than_or_equal(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let is_less = self.is_less_than(ctx, a, b)?;
        let is_eq = self.is_equal_fresh(ctx, a, b)?;
        let gate = self.gate();
        let is_not_eq = gate.not(ctx, QuantumCell::Existing(is_eq));
        Ok(gate.and(
            ctx,
            QuantumCell::Existing(is_less),
            QuantumCell::Existing(is_not_eq),
        ))
    }

    /// Returns an assigned bit representing whether `a` is greater than `b` (`a>b`).
    fn is_greater_than(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let is_less_than_or_eq = self.is_less_than_or_equal(ctx, a, b)?;
        Ok(self
            .gate()
            .not(ctx, QuantumCell::Existing(is_less_than_or_eq)))
    }

    /// Returns an assigned bit representing whether `a` is greater than or equal to `b` (`a>=b`).
    fn is_greater_than_or_equal(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let is_less_than = self.is_less_than(ctx, a, b)?;
        Ok(self.gate().not(ctx, QuantumCell::Existing(is_less_than)))
    }

    /// Returns an assigned bit representing whether `a` is in the order-`n` finite field.
    fn is_in_field(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        self.is_less_than(ctx, a, n)
    }

    /// Assert that an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    fn assert_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<(), Error> {
        let result = self.is_equal_fresh(ctx, a, b)?;
        self.gate().assert_is_const(ctx, &result, &F::from(1));
        Ok(())
    }

    /// Assert that an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    fn assert_equal_muled(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        b: &AssignedBigUint<F, Muled>,
        num_limbs_l: usize,
        num_limbs_r: usize,
    ) -> Result<(), Error> {
        let result = self.is_equal_muled(ctx, a, b, num_limbs_l, num_limbs_r)?;
        self.gate().assert_is_const(ctx, &result, &F::from(1));
        Ok(())
    }

    /// Assert that an assigned bit representing whether `a` is in the order-`n` finite field.
    fn assert_in_field(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<(), Error> {
        let result = self.is_in_field(ctx, a, b)?;
        self.gate().assert_is_const(ctx, &result, &F::from(1));
        Ok(())
    }
}

impl<F: BigPrimeField> BigUintConfig<F> {
    /// Construct a new [`BigIntChip`] from the configuration and parameters.
    ///
    /// # Arguments
    ///
    /// # Return values
    /// Returns a new [`BigIntChip`]
    pub fn construct(range: RangeChip<F>, limb_bits: usize) -> Self {
        Self { range, limb_bits }
    }

    /// Returns the fewest bits necessary to express the [`BigUint`].
    fn bits_size(val: &BigInt) -> usize {
        val.bits() as usize
    }

    fn num_limbs(&self, val: &BigInt) -> usize {
        let bits = Self::bits_size(val);

        if bits % self.limb_bits == 0 {
            bits / self.limb_bits
        } else {
            bits / self.limb_bits + 1
        }
    }

    // fn native_modulus_uint() -> BigUint {
    //     modulus::<F>()
    // }

    // fn native_modulus_int() -> BigInt {
    //     BigInt::from_biguint(Sign::Plus, modulus::<F>())
    // }

    // fn compute_max_mul(&self, num_limbs_l: usize, num_limbs_r: usize) -> BigInt {
    //     // let one = BigInt::from(1u64);
    //     // let l_max = &(BigInt::from(1u64) << (self.limb_bits * num_limbs_l)) - &one;
    //     // let r_max = &(BigInt::from(1u64) << (self.limb_bits * num_limbs_r)) - &one;
    //     // l_max * r_max + one
    //     BigInt::from(1u64) << (self.limb_bits * (num_limbs_l + num_limbs_r))
    // }

    /// Returns the maximum limb size of [`Muled`] type integers.
    fn compute_muled_limb_max(limb_width: usize, min_n: usize) -> BigInt {
        let one = BigInt::from(1usize);
        let out_base = BigInt::from(1usize) << limb_width;
        BigInt::from(min_n) * (&out_base - &one) * (&out_base - &one) + (&out_base - &one)
    }

    /// Given a integer `a` and a divisor `n`, performs `a/n` and `a mod n`.
    /// # Panics
    /// Panics if `n=0`.
    fn div_mod_unsafe(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedValue<F>,
        b: &BigInt,
    ) -> (AssignedValue<F>, AssignedValue<F>) {
        let gate = self.gate();
        let (q_val, n_val) = {
            let a = fe_to_bigint(a.value());
            let (q_val, n_val) = (&a / b, &a % b);
            (bigint_to_fe(&q_val), bigint_to_fe(&n_val))
        };

        let q = ctx.load_witness(q_val);
        let n = ctx.load_witness(n_val);
        let prod = gate.mul(
            ctx,
            QuantumCell::Existing(q),
            QuantumCell::Constant(bigint_to_fe(b)),
        );
        let a_prod_sub = gate.sub(ctx, QuantumCell::Existing(*a), QuantumCell::Existing(prod));
        let is_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(n),
            QuantumCell::Existing(a_prod_sub),
        );
        gate.assert_is_const(ctx, &is_eq, &F::from(1));
        (q, n)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
    use halo2_base::utils::testing::base_test;
    use std::str::FromStr;

    #[test]
    fn test_add() {
        // Uncomment to enable RUST_LOG
        // env_logger::init();

        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;

        base_test().k(k as u32).lookup_bits(k - 1).run(|ctx, range| {
            // Configure range chip
            let range = range.clone();
            let chip = BigUintConfig::construct(range, 64);
            let a_limbs = vec![
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
            ];
            let b_limbs = vec![
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::zero()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
                ctx.load_witness(Fr::one()),
            ];
            // 1 + 2^64 + 2^128 + 2^192 + 2^256 + 2^320
            let a = AssignedBigUint::<Fr, Fresh>::new(
                OverflowInteger::new(a_limbs.clone(), limb_bits),
                BigUint::from_str("2135987035920910082510813795406868310032552609100727358564487664277988894699682310826844728852481").unwrap(),
            );
            // 1 + 2^128 + 2^192 + 2^256 + 2^320
            let b = AssignedBigUint::<Fr, Fresh>::new(
                OverflowInteger::new(b_limbs.clone(), limb_bits),
                BigUint::from_str("2135987035920910082510813795406868310032552609100727358564487664277988894699663864082771019300865").unwrap(),
            );

            let output = chip.add(ctx, &a, &b).unwrap();
            assert_eq!(output.value(), a.value() + b.value());
            for i in 0..a_limbs.len() {
                assert_eq!(*output.limb(i).value(), a_limbs[i].value() + b_limbs[i].value());
            }
        });
    }
}
