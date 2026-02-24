use std::cmp::min;

use feanor_math::algorithms::int_factor::is_prime_power;
use feanor_math::algorithms::linsolve::LinSolveRingStore;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::rings::extension::FreeAlgebraStore;
use feanor_math::divisibility::*;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{int_cast, BigIntRing, IntegerRingStore};
use feanor_math::matrix::OwnedMatrix;
use feanor_math::primitive_int::*;
use feanor_math::ring::*;
use feanor_math::rings::extension::extension_impl::FreeAlgebraImpl;
use feanor_math::seq::*;
use feanor_math::rings::poly::{PolyRing, PolyRingStore};
use feanor_math::rings::zn::*;
use tracing::instrument;

use crate::circuit::PlaintextCircuit;
use crate::*;

///
/// Returns the best arithmetic circuit that computes a function
/// ```text
///   digitex: Z/2^eZ -> (Z/2^eZ)^log(e)
/// ```
/// that satisfies `digitex(x)[i] = (x mod 2) mod 2^(2^i)`.
/// `e` must be a power of two.
/// 
/// Uses a lookup-table, consisting mainly of the values from <https://ia.cr/2022/1364>, except for
/// `e > 8`, where there seemed to be a mistake in the paper.
/// 
pub fn precomputed_p_2(e: usize) -> PlaintextCircuit<StaticRingBase<i64>> {
    assert!(e <= 23, "no precomputed tables are available for t > 2^23");
    let log2_e_ceil = ZZi64.abs_log2_ceil(&(e as i64)).unwrap();
    
    let id = || PlaintextCircuit::linear_transform_ring(&[1], ZZi64);
    let f0 = id().clone(ZZi64);
    if log2_e_ceil == 0 {
        return f0;
    }

    let f1 = id().tensor(PlaintextCircuit::square(ZZi64), ZZi64).compose(PlaintextCircuit::select(1, &[0, 0], ZZi64).compose(f0, ZZi64), ZZi64);
    if log2_e_ceil == 1 {
        return f1;
    }

    let f2 = id().tensor(id(), ZZi64).tensor(PlaintextCircuit::square(ZZi64), ZZi64).compose(PlaintextCircuit::select(2, &[0, 1, 1], ZZi64).compose(f1, ZZi64), ZZi64);
    if log2_e_ceil == 2 {
        return f2;
    }
    
    let f3_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[112], ZZi64).tensor(PlaintextCircuit::square(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[94, 121], ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(2, &[0, 0, 1], ZZi64), ZZi64
    );
    let f3 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f3_comp, ZZi64).compose(
        PlaintextCircuit::select(3, &[0, 1, 2, 1, 2], ZZi64), ZZi64
    ).compose(f2, ZZi64);
    if log2_e_ceil == 3 {
        return f3;
    }

    let f4_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[1984, 528, 22620], ZZi64).tensor(PlaintextCircuit::mul(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[226, 113], ZZi64).tensor(PlaintextCircuit::linear_transform_ring(&[8, 2, 301], ZZi64), ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(3, &[0, 1, 2, 1, 2, 0, 1, 2], ZZi64), ZZi64
    );
    let f4 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f4_comp, ZZi64).compose(
        PlaintextCircuit::select(4, &[0, 1, 2, 3, 1, 2, 3], ZZi64), ZZi64
    ).compose(f3, ZZi64);
    if log2_e_ceil == 4 {
        return f4;
    }

    let f5_comp = PlaintextCircuit::add(ZZi64).compose(
        PlaintextCircuit::linear_transform_ring(&[4849408, 3564625, 2737008, 6563608], ZZi64).tensor(PlaintextCircuit::mul(ZZi64).compose(
            PlaintextCircuit::linear_transform_ring(&[997183, 8295548, 419894, 879825], ZZi64).tensor(PlaintextCircuit::linear_transform_ring(&[443729, 555132, 491350, 758385], ZZi64), ZZi64), ZZi64
        ), ZZi64), ZZi64
    ).compose(
        PlaintextCircuit::select(4, &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3], ZZi64), ZZi64
    );
    let f5 = id().tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(id(), ZZi64).tensor(f5_comp, ZZi64).compose(
        PlaintextCircuit::select(5, &[0, 1, 2, 3, 4, 1, 2, 3, 4], ZZi64), ZZi64
    ).compose(f4, ZZi64);
    if log2_e_ceil == 5 {
        return f5;
    }
    unreachable!()
}

///
/// Heuristically chooses a low-depth, low-complexity circuit that
/// evaluates all the given univariate polynomials.
/// 
#[instrument(skip_all)]
pub fn poly_to_circuit<P>(poly_ring: P, polys: &[El<P>]) -> PlaintextCircuit<<<<P::Type as RingExtension>::BaseRing as RingStore>::Type as ZnRing>::IntegerRingBase>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing + DivisibilityRing
{
    let degrees = polys.iter().map(|f| poly_ring.degree(f).unwrap() as usize).collect::<Vec<_>>();
    let max_deg = <_ as Iterator>::max(degrees.iter().copied()).unwrap();
    let optimal_depths = degrees.iter().copied().map(|d| ZZi64.abs_log2_ceil(&(d as i64)).unwrap()).collect::<Vec<_>>();
    
    let baby_steps = (1..max_deg).filter(|bs| {
            let (depths, _) = low_depth_paterson_stockmeyer_cost((&degrees).copy_els(), *bs);
            (0..optimal_depths.len()).all(|i| depths.at(i) <= optimal_depths[i] + 1)
        })
        .min_by_key(|bs| low_depth_paterson_stockmeyer_cost((&degrees).copy_els(), *bs).1)
        .unwrap();

    return low_depth_paterson_stockmeyer(&poly_ring, polys, baby_steps);
}

///
/// Computes the cost of the circuit [`low_depth_paterson_stockmeyer()`] would return, without
/// actually building the circuit.
/// 
pub fn low_depth_paterson_stockmeyer_cost<V>(degrees: V, baby_steps: usize) -> (/* mul depths */ impl VectorFn<usize>, /* mul count */ usize)
    where V: VectorFn<usize>
{
    let max_deg = degrees.iter().max().unwrap();
    let giant_steps = max_deg / baby_steps + 1;
    let giant_steps_half = giant_steps / 2 + 1;

    let baby_steps_mul_count = baby_steps - 1;
    let giant_steps_mul_count = giant_steps_half - 2;
    let mut final_mul_count = 0;
    for d in degrees.iter() {
        final_mul_count += d / baby_steps;
        // in this case we need one multiplication to get x^(d - (d % baby_steps)) and one to multiply it with the block
        if d / baby_steps > 1 && (d / baby_steps) % 2 == 1 {
            final_mul_count += 1;
        }
    }
    let mul_count = baby_steps_mul_count + giant_steps_mul_count + final_mul_count;

    let mul_depths = degrees.map_fn(move |d| ZZi64.abs_log2_ceil(&min(baby_steps as i64, d as i64)).unwrap() as usize + ZZi64.abs_log2_ceil(&((d / baby_steps) as i64)).map(|x| x + 1).unwrap_or(0) as usize);

    return (mul_depths, mul_count);
}

///
/// A low-depth variant of Paterson-Stockmeyer evaluation of polynomials.
/// 
/// # Algorithm
/// 
/// Currently, the circuit is built according to the following strategy:
///  - First, the first consecutive `baby_steps` powers of the input are computed, i.e.
///    `1, x, x^2, ..., x^baby_steps`
///  - Then the powers `1, x^baby_steps, x^(2 baby_steps), ...` are computed (the "giant steps")
///  - For each giant step and desired polynomial, a suitable linear combination of the baby steps 
///    is taken, and then multiplied with the giant step
///  - The results are summed up
/// 
/// In other words, to compute a single polynomial, the required number of multiplications is `baby_steps + 2 * giant_steps`.
/// The multiplicative depth is minimal (except possibly `+ 1` if divisions are not exact).
/// 
#[instrument(skip_all)]
pub fn low_depth_paterson_stockmeyer<P>(poly_ring: P, polys: &[El<P>], baby_steps: usize) -> PlaintextCircuit<<<<P::Type as RingExtension>::BaseRing as RingStore>::Type as ZnRing>::IntegerRingBase>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: ZnRing
{
    let max_deg = polys.iter().map(|f| poly_ring.degree(f).unwrap_or(0)).max().unwrap();
    let ZZ = poly_ring.base_ring().integer_ring();

    fn compute_power_circuit<I>(ZZ: I, deg_exclusive: usize) -> PlaintextCircuit<I::Type>
        where I: RingStore + Copy,
            I::Type: IntegerRing
    {
        let mut result = PlaintextCircuit::constant(ZZ.one(), ZZ).tensor(PlaintextCircuit::identity(1, ZZ), ZZ);
        while result.output_count() < deg_exclusive {
            let l = result.output_count();
            if l % 2 == 0 {
                result = PlaintextCircuit::identity(l, ZZ).tensor(
                    PlaintextCircuit::square(ZZ).compose(PlaintextCircuit::select(l, &[l / 2], ZZ), ZZ), ZZ
                ).compose(
                    result.output_twice(ZZ), ZZ
                );
            } else {
                result = PlaintextCircuit::identity(l, ZZ).tensor(
                    PlaintextCircuit::mul(ZZ).compose(PlaintextCircuit::select(l, &[l / 2, l - (l / 2)], ZZ), ZZ), ZZ
                ).compose(
                    result.output_twice(ZZ), ZZ
                );
            }
            assert_eq!(l + 1, result.output_count());
        }
        assert!(result.output_count() == deg_exclusive);
        return result;
    }

    let giant_steps = max_deg / baby_steps + 1;
    let giant_steps_half = giant_steps / 2 + 1;
    assert!((giant_steps - 1) * baby_steps + baby_steps > max_deg);
    assert!((giant_steps - 1) * baby_steps <= max_deg);

    // now baby_step_circuit computes (1, x, x^2, ..., x^baby_steps)
    let baby_step_circuit = compute_power_circuit(ZZ, baby_steps + 1);
    assert_eq!(baby_steps - 1, baby_step_circuit.multiplication_gate_count());
    assert_eq!(ZZi64.abs_log2_ceil(&(baby_steps as i64)).unwrap() as usize, baby_step_circuit.max_mul_depth());
    let baby_step_circuit_mul_depth = baby_step_circuit.max_mul_depth();

    // giant_step_circuit computes (1, x, ..., x^(baby_steps - 1), 1, x^baby_steps, x^(2 baby_steps), ..., x^(floor(giant_steps / 2) * baby_steps - baby_steps))
    let giant_step_circuit = PlaintextCircuit::identity(baby_steps, ZZ).tensor(compute_power_circuit(ZZ, giant_steps_half), ZZ).compose(baby_step_circuit, ZZ);
    assert_eq!(baby_steps - 1 + giant_steps_half - 2, giant_step_circuit.multiplication_gate_count());
    assert_eq!(ZZi64.abs_log2_ceil(&(giant_steps_half as i64 - 1)).unwrap() as usize, giant_step_circuit.max_mul_depth() - baby_step_circuit_mul_depth);
    assert_eq!(giant_step_circuit.input_count(), 1);
    assert_eq!(giant_step_circuit.output_count(), baby_steps + giant_steps_half);

    let all_poly_parts: Vec<Vec<PlaintextCircuit<_>>> = polys.iter().map(|f: &_| (0..(poly_ring.degree(f).unwrap() / baby_steps + 1)).map(|i| PlaintextCircuit::linear_transform_ring(&(0..baby_steps).map(|j|
        poly_ring.base_ring().smallest_lift(poly_ring.base_ring().clone_el(poly_ring.coefficient_at(f, i * baby_steps + j)))
    ).collect::<Vec<_>>(), ZZ)).collect()).collect();

    let select_baby_steps = PlaintextCircuit::select(baby_steps + giant_steps_half, &(0..baby_steps).collect::<Vec<_>>(), ZZ);

    let mut result = PlaintextCircuit::empty();
    for (poly, poly_parts) in polys.iter().zip(all_poly_parts.iter()) {

        let mut compute_poly_circuit = poly_parts[0].clone(ZZ).compose(select_baby_steps.clone(ZZ), ZZ);
        let highest_block = poly_ring.degree(poly).unwrap() / baby_steps;
        
        for i in 1..=(highest_block / 2) {
            assert_eq!(baby_steps + giant_steps_half, compute_poly_circuit.input_count());
            assert_eq!(1, compute_poly_circuit.output_count());

            let low_part = poly_parts[i].clone(ZZ);
            let high_part = poly_parts[i + highest_block / 2].clone(ZZ);

            let compute_part = PlaintextCircuit::mul(ZZ).compose(
                PlaintextCircuit::add(ZZ).compose(
                    low_part.compose(select_baby_steps.clone(ZZ), ZZ).tensor(
                        PlaintextCircuit::mul(ZZ).compose(high_part.compose(select_baby_steps.clone(ZZ), ZZ).tensor(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2], ZZ), ZZ), ZZ), ZZ
                    ), ZZ
                ).tensor(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + i], ZZ), ZZ), ZZ
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_times(4, ZZ), ZZ);

            compute_poly_circuit = PlaintextCircuit::add(ZZ).compose(compute_poly_circuit.tensor(compute_part, ZZ), ZZ)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_twice(ZZ), ZZ);
        }

        if highest_block == 1 {
            let compute_part = PlaintextCircuit::mul(ZZ).compose(
                poly_parts[highest_block].clone(ZZ).compose(select_baby_steps.clone(ZZ), ZZ).tensor(
                    PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + 1], ZZ), ZZ
                ), ZZ
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_times(2, ZZ), ZZ);  
            compute_poly_circuit = PlaintextCircuit::add(ZZ).compose(compute_poly_circuit.tensor(compute_part, ZZ), ZZ)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_twice(ZZ), ZZ);
        } else if highest_block % 2 == 1 {
            let highest_block_power = PlaintextCircuit::mul(ZZ).compose(PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2], ZZ).tensor(
                PlaintextCircuit::select(baby_steps + giant_steps_half, &[baby_steps + highest_block / 2 + 1], ZZ), ZZ
            ), ZZ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_twice(ZZ), ZZ);
            let compute_part = PlaintextCircuit::mul(ZZ).compose(
                poly_parts[highest_block].clone(ZZ).compose(select_baby_steps.clone(ZZ), ZZ).tensor(highest_block_power, ZZ), ZZ
            ).compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_twice(ZZ), ZZ);
            compute_poly_circuit = PlaintextCircuit::add(ZZ).compose(compute_poly_circuit.tensor(compute_part, ZZ), ZZ)
                .compose(PlaintextCircuit::identity(baby_steps + giant_steps_half, ZZ).output_twice(ZZ), ZZ);
        }

        result = result.tensor(compute_poly_circuit, ZZ);
    }
    let result = result.compose(giant_step_circuit.output_times(polys.len(), ZZ), ZZ);

    let (expected_mul_depths, expected_mul_count) = low_depth_paterson_stockmeyer_cost(polys.as_fn().map_fn(|f| poly_ring.degree(f).unwrap() as usize), baby_steps);
    for i in 0..polys.len() {
        assert_eq!(expected_mul_depths.at(i), result.mul_depth(i));
    }
    assert_eq!(expected_mul_count, result.multiplication_gate_count());
    return result;
}

///
/// Computes a low-degree polynomial `f` such that `f(x + py) = x` for
/// `x` in `{ -B, ..., B }` over `Z/p^eZ`.
/// 
#[instrument(skip_all)]
pub fn bounded_digit_retain_poly<P>(poly_ring: P, bound: i64) -> El<P>
    where P: RingStore,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    let base_ring = poly_ring.base_ring();
    let (p, e) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    assert!(base_ring.integer_ring().is_lt(&int_cast(2 * bound, base_ring.integer_ring(), ZZi64), &p));
    let p = base_ring.coerce(base_ring.integer_ring(), p);
    let hom = base_ring.can_hom(&ZZi64).unwrap();

    // poly that is zero modulo p on the support
    let base_null_poly = poly_ring.prod((-bound..=bound).map(|i| poly_ring.from_terms([(base_ring.one(), 1), (hom.map(i), 0)])));
    // poly that is zero modulo p^e on the support
    let null_poly = poly_ring.pow(poly_ring.clone_el(&base_null_poly), e);
    let modulus = (0..poly_ring.degree(&null_poly).unwrap()).map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(&null_poly, i)))).collect::<Vec<_>>();
    let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);
    // poly whose value is `= x mod p` and independent of `y` on `x + p y`
    let base_poly = mod_null_poly_ring.poly_repr(&poly_ring, &mod_null_poly_ring.pow_gen(mod_null_poly_ring.canonical_gen(), base_ring.modulus(), base_ring.integer_ring()), base_ring.identity());

    let len = 2 * bound as usize + 1;
    let x = (0..len).map_fn(|i| hom.map(i as i64 - bound));
    let mut matrix = OwnedMatrix::from_fn(len, len, |i, j| base_ring.pow(x.at(i), j));
    let mut expected = OwnedMatrix::from_fn(len, 1, |i, _| base_ring.sub(x.at(i), poly_ring.evaluate(&base_poly, &x.at(i), base_ring.identity())));
    let mut result = OwnedMatrix::zero(len, 1, base_ring);
    <_ as LinSolveRingStore>::solve_right(base_ring, matrix.data_mut(), expected.data_mut(), result.data_mut()).assert_solved();
    let digit_extraction_poly = poly_ring.add(
        base_poly,
        poly_ring.from_terms((0..len).map(|i| (base_ring.clone_el(result.at(i, 0)), i)))
    );
    let mut digit_retain_poly = mod_null_poly_ring.canonical_gen();
    for _ in 1..e {
        digit_retain_poly = poly_ring.evaluate(&digit_extraction_poly, &digit_retain_poly, mod_null_poly_ring.inclusion());
    }

    let mut current = mod_null_poly_ring.poly_repr(&poly_ring, &digit_retain_poly, base_ring.identity());
    let mut current_e = 0;
    while base_ring.checked_div(poly_ring.lc(&current).unwrap(), &base_ring.pow(base_ring.clone_el(&p), current_e)).is_some() {
        let null_poly = poly_ring.inclusion().mul_map(
            poly_ring.pow(poly_ring.clone_el(&base_null_poly), e - current_e),
            base_ring.pow(base_ring.clone_el(&p), current_e)
        );
        while let Some(quo) = base_ring.checked_div(poly_ring.lc(&current).unwrap(), &poly_ring.lc(&null_poly).unwrap()) {
            if poly_ring.degree(&current).unwrap() < poly_ring.degree(&null_poly).unwrap() {
                break;
            }
            let mut subtractor = poly_ring.inclusion().mul_ref_map(&null_poly, &quo);
            poly_ring.mul_assign_monomial(&mut subtractor, poly_ring.degree(&current).unwrap() - poly_ring.degree(&null_poly).unwrap());
            poly_ring.sub_assign(&mut current, subtractor);
        }
        current_e += 1;
    }
    return current;
}

///
/// Computes `min { n | n! % k == 0 }`
/// 
pub fn mu(k: i64) -> i64 {
    const ZZbig: BigIntRing = BigIntRing::RING;
    let mut n = 1;
    let mut n_fac = ZZbig.one();
    while ZZbig.checked_div(&n_fac, &int_cast(k, &ZZbig, &ZZi64)).is_none() {
        n += 1;
        ZZbig.mul_assign(&mut n_fac, int_cast(n, &ZZbig, &ZZi64));
    }
    return n;
}

///
/// Computes `prod_(i < m) (X - i)`.
/// 
pub fn falling_factorial_poly<P>(poly_ring: P, m: usize) -> El<P>
    where P: RingStore,
        P::Type: PolyRing
{
    poly_ring.prod((0..m).map(|j| poly_ring.sub(poly_ring.indeterminate(), poly_ring.int_hom().map(j as i32))))
}

///
/// Returns the lowest-degree polynomial `f` such that `f(x + py) = x mod p^e` for
/// `x in { 0, ..., p - 1 }` and any `y`.
/// 
/// The degree of this polynomial is at most `(p - 1)(e - 1) + 1`, but may be smaller
/// than that. This function will always compute the polynomial of lowest degree with
/// above property. For the reason why a polynomial of degree `<= (p - 1)(e - 1) + 1`
/// with the property exists, see Chen and Han's paper <https://ia.cr/2022/1364>.
/// 
#[instrument(skip_all)]
pub fn digit_retain_poly<P>(poly_ring: P, e: usize) -> El<P>
    where P: RingStore + Copy,
        P::Type: PolyRing,
        <<P::Type as RingExtension>::BaseRing as RingStore>::Type: NiceZn
{
    assert!(e > 0);
    if e == 1 {
        return poly_ring.indeterminate();
    }
    let base_ring = poly_ring.base_ring();
    let (p, _) = is_prime_power(base_ring.integer_ring(), base_ring.modulus()).unwrap();
    let p = int_cast(p, ZZi64, base_ring.integer_ring());
    let pe = ZZi64.pow(p, e);

    let hom = base_ring.can_hom(&ZZi64).unwrap();
    // poly that is zero modulo p^e on the support
    let null_poly = falling_factorial_poly(&poly_ring, mu(pe) as usize);
    let modulus = (0..poly_ring.degree(&null_poly).unwrap()).map(|i| base_ring.negate(base_ring.clone_el(poly_ring.coefficient_at(&null_poly, i)))).collect::<Vec<_>>();
    let mod_null_poly_ring = FreeAlgebraImpl::new(base_ring, poly_ring.degree(&null_poly).unwrap(), modulus);
    // poly whose value is `= x mod p` and independent of `y` on `x + p y`
    let base_poly = mod_null_poly_ring.poly_repr(&poly_ring, &mod_null_poly_ring.pow(mod_null_poly_ring.canonical_gen(), pe as usize), base_ring.identity());

    let len = p as usize;
    let mut matrix = OwnedMatrix::from_fn(len, len, |i, j| base_ring.pow(hom.map(i as i64), j));
    let mut expected = OwnedMatrix::from_fn(len, 1, |i, _| base_ring.sub(hom.map(i as i64), poly_ring.evaluate(&base_poly, &hom.map(i as i64), base_ring.identity())));
    let mut result = OwnedMatrix::zero(len, 1, base_ring);
    <_ as LinSolveRingStore>::solve_right(base_ring, matrix.data_mut(), expected.data_mut(), result.data_mut()).assert_solved();
    let digit_extraction_poly = poly_ring.add(
        base_poly,
        poly_ring.from_terms((0..len).map(|i| (base_ring.clone_el(result.at(i, 0)), i)))
    );
    let mut digit_retain_poly = mod_null_poly_ring.canonical_gen();
    for _ in 1..e {
        digit_retain_poly = poly_ring.evaluate(&digit_extraction_poly, &digit_retain_poly, mod_null_poly_ring.inclusion());
    }

    let mut current = mod_null_poly_ring.poly_repr(&poly_ring, &digit_retain_poly, base_ring.identity());
    let mut current_e = 0;
    while base_ring.checked_div(poly_ring.lc(&current).unwrap(), &base_ring.pow(hom.map(p), current_e)).is_some() {
        let null_poly = poly_ring.inclusion().mul_map(
            falling_factorial_poly(&poly_ring, mu(ZZi64.pow(p, e - current_e)) as usize),
            base_ring.pow(hom.map(p), current_e)
        );
        while let Some(quo) = base_ring.checked_div(poly_ring.lc(&current).unwrap(), &poly_ring.lc(&null_poly).unwrap()) {
            if poly_ring.degree(&current).unwrap() < poly_ring.degree(&null_poly).unwrap() {
                break;
            }
            let mut subtractor = poly_ring.inclusion().mul_ref_map(&null_poly, &quo);
            poly_ring.mul_assign_monomial(&mut subtractor, poly_ring.degree(&current).unwrap() - poly_ring.degree(&null_poly).unwrap());
            poly_ring.sub_assign(&mut current, subtractor);
        }
        current_e += 1;
    }
    return current;
}

#[cfg(test)]
use feanor_math::rings::zn::zn_64::Zn;
#[cfg(test)]
use feanor_math::assert_el_eq;
#[cfg(test)]
use feanor_math::rings::poly::dense_poly::*;
#[cfg(test)]
use feanor_math::rings::finite::FiniteRingStore;

#[test]
#[ignore]
fn test_digit_extraction_p_2_complete() {
    let circuit = precomputed_p_2(23);
    let ring = Zn::new(1 << 23);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 23) {
        for (e, actual) in [1, 2, 4, 8, 16, 23].into_iter().zip(circuit.evaluate_no_galois(&[hom.map(x)], &hom)) {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_digit_extraction_p_2() {
    let circuit = precomputed_p_2(17);
    let ring = Zn::new(1 << 17);
    let hom = ring.can_hom(&ZZi64).unwrap();
    for x in 0..(1 << 17) {
        for (e, actual) in [1, 2, 4, 8, 16, 17].into_iter().zip(circuit.evaluate_no_galois(&[hom.map(x)], &hom)) {
            assert_eq!(x % 2, ring.smallest_positive_lift(actual) % (1 << e));
        }
    }
}

#[test]
fn test_digit_retain_poly() {
    let Zn = Zn::new(1024);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_eq!(Some(3), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 8);
    }
    let digit_retain = digit_retain_poly(&P, 6);
    assert_eq!(Some(6), P.degree(&digit_retain));
    for k in 0..1024 {
        assert_eq!(k % 2, Zn.smallest_positive_lift(P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity())) % 64);
    }

    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_eq!(Some(33), P.degree(&digit_retain));
    for k in 0..(17 * 17 * 17) {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, k % 17), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, k), &Zn.identity()));
    }
    
    let Zn = Zn::new(257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 2);
    assert_eq!(Some(257), P.degree(&digit_retain));
    for k in 0..257 {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }
}

#[test]
fn test_bounded_digit_retain_poly() {
    let Zn = Zn::new(17 * 17 * 17);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 3);
    assert_eq!(Some(17), P.degree(&digit_retain));
    for x in -3..=3 {
        for y in 0..(17 * 17) {
            assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, x), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 17 * y), &Zn.identity()));
        }
    }
    
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = bounded_digit_retain_poly(&P, 4);
    assert_eq!(Some(25), P.degree(&digit_retain));
    for x in -4..=4 {
        for y in 0..(257 * 257) {
            assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, x), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, x + 257 * y), &Zn.identity()));
        }
    }
}

#[test]
fn test_digit_retain_poly_large() {
    let Zn = Zn::new(257 * 257 * 257);
    let P = DensePolyRing::new(Zn, "X");
    let digit_retain = digit_retain_poly(&P, 3);
    assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 251), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 132092), &Zn.identity()));
    for k in 0..(257 * 257) {
        assert_el_eq!(&Zn, &Zn.coerce(&ZZi64, 2), &P.evaluate(&digit_retain, &Zn.coerce(&ZZi64, 2 + k * 257), &Zn.identity()));
    }
}

#[test]
fn test_paterson_stockmeyer() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let poly = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_paterson_stockmeyer(&P, &[P.clone_el(&poly)], 3);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(4, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        assert_el_eq!(Zn, P.evaluate(&poly, &x, &P.base_ring().identity()), circuit.evaluate_no_galois(&[x], P.base_ring().can_hom(&ZZi64).unwrap()).into_iter().next().unwrap());
    }
}

#[test]
fn test_paterson_stockmeyer_multiple_polys() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    // 1 + 2 X^3 + 3 X^4 + 4 X^5 + 8 X^7
    let f = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    // 2 + X + 2 X^2 + 3 X^3 + 4 X^4 + 5 X^5 + 6 X^6 + 7 X^7 + 8 X^8 + 9 X^9
    let g = P.from_terms([(2, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_paterson_stockmeyer(&P, &[P.clone_el(&f), P.clone_el(&g)], 4);
    assert_eq!(4, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(6, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZi64).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X^12
    let h = P.from_terms([(1, 0), (3, 6), (7, 9), (1, 12)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = low_depth_paterson_stockmeyer(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h)], 4);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(11, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZi64).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    // 1 + X + X^2 + ... + X^15 + X^16
    let l = P.from_terms((0..=16).map(|i| (Zn.one(), i)));
    let circuit = low_depth_paterson_stockmeyer(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h), P.clone_el(&l)], 4);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(3, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(5, circuit.mul_depth(3));
    assert_eq!(5 + 1 + 2 + 3 + 4, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZi64).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&l, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }
}

#[test]
fn test_best_circuit_multiple_polys() {
    let Zn = Zn::new(17);
    let P = DensePolyRing::new(Zn, "X");
    let f = P.from_terms([(1, 0), (2, 3), (3, 4), (4, 5), (8, 7)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let g = P.from_terms([(2, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let h = P.from_terms([(1, 0), (3, 6), (7, 9), (1, 12)].into_iter().map(|(c, d)| (Zn.int_hom().map(c), d)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h)]);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(4, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(8, circuit.multiplication_gate_count());
    
    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZi64).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }

    let l = P.from_terms((0..=16).map(|i| (Zn.one(), i)));
    let circuit = poly_to_circuit(&P, &[P.clone_el(&f), P.clone_el(&g), P.clone_el(&h), P.clone_el(&l)]);
    assert_eq!(5, circuit.max_mul_depth());
    assert_eq!(4, circuit.mul_depth(0));
    assert_eq!(4, circuit.mul_depth(1));
    assert_eq!(5, circuit.mul_depth(2));
    assert_eq!(5, circuit.mul_depth(3));
    assert_eq!(11, circuit.multiplication_gate_count());

    for x in Zn.elements() {
        let mut result_it = circuit.evaluate_no_galois(std::slice::from_ref(&x), P.base_ring().can_hom(&ZZi64).unwrap()).into_iter();
        assert_el_eq!(Zn, P.evaluate(&f, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&g, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&h, &x, &P.base_ring().identity()), result_it.next().unwrap());
        assert_el_eq!(Zn, P.evaluate(&l, &x, &P.base_ring().identity()), result_it.next().unwrap());
    }
}