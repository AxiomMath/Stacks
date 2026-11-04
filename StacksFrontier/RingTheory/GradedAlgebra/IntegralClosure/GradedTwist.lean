module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.GradedAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded twist and integrality over `R[T;T⁻¹]`

The grading-respecting condition `RespectsGrading`, the graded twist
`Ψ : S →+* S[T;T⁻¹]` (`exists_gradedTwist`), the integrality of the twist of an integral
element (`gradedTwist_isIntegral`), and the unit-times-integral descent
`isIntegralElem_of_unit_mul`.
-/

/-!
# The integral closure of a graded ring is graded

We work with `ℕ`-graded commutative rings, following the Stacks project convention
(Tag 077G, Section 10.56): a graded ring is a commutative ring `A` together with a
direct-sum decomposition of its underlying additive group `A = ⨁_{d ≥ 0} A_d` into
additive subgroups `A_d` (the homogeneous part of degree `d`) satisfying `1 ∈ A_0`
and `A_d · A_e ⊆ A_{d+e}` for all `d, e ≥ 0`.  In Lean we model this with Mathlib's
`GradedRing` structure on a family `A : ℕ → AddSubgroup A`.

A homomorphism of graded rings
`φ : R → S` is a ring homomorphism that respects the gradings, i.e.
`φ (R_d) ⊆ S_d` for every `d ≥ 0`.  Such a `φ` makes `S` into an `R`-algebra; in the
formalization we take the `Algebra R S` structure as given and require its
structure map `algebraMap R S` (playing the role of `φ`) to respect the gradings.

For an `R`-algebra `S`, an element `s ∈ S` is
integral over `R` if it satisfies a monic polynomial with coefficients (mapped) from
`R`.  The integral closure of `R` in `S` is the `R`-subalgebra of all such elements;
in Mathlib this is `integralClosure R S : Subalgebra R S`.

An `R`-subalgebra `T ⊆ S` is a graded
`R`-subalgebra if it is a graded submodule for the grading on `S`, i.e.
`T = ⨁_{d ≥ 0} (T ∩ S_d)`; equivalently, for every `s ∈ T` each homogeneous
component of `s` again lies in `T`.

## The statement

Let `φ : R → S` be a homomorphism of `ℕ`-graded commutative rings.  Let `S'` be the
integral closure of `R` in `S`.  Then `S'` is a graded `R`-subalgebra of `S`; that is,
`S' = ⨁_{d ≥ 0} (S' ∩ S_d)`.  Equivalently and explicitly: if `s ∈ S` is integral
over `R` and `s = s_n + ⋯ + s_m` is its decomposition into homogeneous parts, then
each homogeneous part `s_d` is integral over `R`.

## Notes

- The core content is that the integral closure is closed under taking homogeneous
  components (every homogeneous component of an integral element is integral).  We
  state this directly via the homogeneous projection `GradedRing.proj 𝒮 d`.
- The reverse inclusion `⨁_{d ≥ 0} (S' ∩ S_d) ⊆ S'` is immediate, so the
  "homogeneous-component-closed" condition is equivalent to the internal direct-sum
  equality of the carrier; see `integralClosure_carrier_eq` below.

## Architecture

The main theorem `integralClosure_isHomogeneous` is reduced to three named sub-lemmas:

* `exists_gradedTwist`  — the grading ("twist by degree") ring homomorphism
  `Ψ : S →+* S[T;T⁻¹]`, `Ψ s = ∑_i (proj_i s) · Tⁱ`.  Its defining property here is
  that the `Tⁱ`-coefficient of `Ψ s` is exactly the homogeneous component
  `proj 𝒮 i s` (and `Ψ s` is supported in nonnegative degrees).
* `gradedTwist_isIntegral` — if `s` is integral over `R` then `Ψ s` is integral over
  the subring `R[T;T⁻¹]` (image under the coefficient map
  `Φ = AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) : R[T;T⁻¹] →+* S[T;T⁻¹]`),
  using `RespectsGrading` to keep the coefficients of the integral equation inside
  the image of `Φ`.
* `coeff_isIntegral` — every `T`-coefficient of an element of `S[T;T⁻¹]` that is
  integral over `R[T;T⁻¹]` (along `Φ`) is itself integral over `R`.  This is the
  analytic kernel: the specialization / Vandermonde argument of the Stacks proof.

The assembly: `proj 𝒮 d s = (Ψ s)(d)` is a `T`-coefficient of `Ψ s`, which is
integral over `R[T;T⁻¹]` by `gradedTwist_isIntegral`, hence integral over `R` by
`coeff_isIntegral`.
-/

@[expose] public section

universe u_1 u_2
variable {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [Algebra R S]
variable (ℛ : ℕ → AddSubgroup R) (𝒮 : ℕ → AddSubgroup S)
variable [GradedRing ℛ] [GradedRing 𝒮]

/-- The structure map `R → S` respects the gradings: it carries `ℛ d` into `𝒮 d` for every
degree `d`. -/
@[ega "II 2.1.2" "special case"]
def RespectsGrading : Prop :=
  ∀ d : ℕ, ∀ r ∈ ℛ d, (algebraMap R S) r ∈ 𝒮 d

-- The degree-`i` summand `a ↦ C a · Tⁱ` of the graded twist, as an additive hom.
open LaurentPolynomial in
/-- The degree-`i` summand `a ↦ C a · Tⁱ` of the graded twist, as an additive hom. -/
noncomputable def gradedTwistDeg (i : ℕ) : 𝒮 i →+ S[T;T⁻¹] :=
  (AddMonoidHom.mulRight (T (i : ℤ))).comp
    (LaurentPolynomial.C.toAddMonoidHom.comp (AddSubgroupClass.subtype (𝒮 i)))

omit [GradedRing 𝒮] in
open LaurentPolynomial in
/-- The degree-`i` summand of the graded twist sends `a` to `C a * T i`. -/
theorem gradedTwistDeg_apply (i : ℕ) (a : 𝒮 i) :
    gradedTwistDeg 𝒮 i a = C ((a : S)) * T (i : ℤ) := rfl

-- The graded twist as a ring homomorphism `(⨁ i, 𝒮 i) →+* S[T;T⁻¹]`.
open LaurentPolynomial in
/-- The graded twist as a ring homomorphism `(⨁ i, 𝒮 i) →+* S[T;T⁻¹]`, assembled from the
degreewise summands. -/
noncomputable def gradedTwistAux : (DirectSum ℕ (fun i => 𝒮 i)) →+* S[T;T⁻¹] :=
  DirectSum.toSemiring (fun i => gradedTwistDeg 𝒮 i)
    (by rw [gradedTwistDeg_apply, SetLike.coe_gOne]; simp)
    (by
      intro i j ai aj
      rw [gradedTwistDeg_apply, gradedTwistDeg_apply, gradedTwistDeg_apply, SetLike.coe_gMul,
        map_mul]
      push_cast; rw [LaurentPolynomial.T_add]; ring)

open LaurentPolynomial in
/-- The `n`-th coefficient of `C a * T j` is `a` when `n = j`, and `0` otherwise. -/
theorem gradedTwist_coeff_C_mul_T (a : S) (j n : ℤ) :
    (C a * T j : LaurentPolynomial S).coeff n = if n = j then a else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split <;> rename_i h <;> simp [h]; tauto

open Classical LaurentPolynomial in
/-- The `n`-th coefficient of the graded twist of `x` is the sum over the support of `x` of its
degree-`i` component when `n = i`, and `0` otherwise. -/
theorem gradedTwistAux_coeff (x : DirectSum ℕ (fun i => 𝒮 i)) (n : ℤ) :
    (gradedTwistAux 𝒮 x).coeff n
      = ∑ i ∈ (DFinsupp.support x), (if n = (i:ℤ) then ((x i : S)) else 0) := by
  conv_lhs => rw [← DirectSum.sum_support_of x]
  rw [map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  rw [gradedTwistAux, DirectSum.toSemiring_apply, DirectSum.toAddMonoid_of, gradedTwistDeg_apply,
    gradedTwist_coeff_C_mul_T]

open LaurentPolynomial in
/-- **(L1) The graded twist ring homomorphism `Ψ : S → S[T;T⁻¹]`.**

Mathematically `Ψ` is the map `s ↦ ∑_d (proj_d s) · T^d`, where the (finite) sum runs
over the homogeneous support of `s`.  It is a ring homomorphism:
* additivity is `DirectSum.decompose_add` (the decomposition is additive), composed
  with the additivity of `LaurentPolynomial.C` and of the finite sum;
* it sends `1 = proj_0 1` to `C 1 · T^0 = 1` (since `1` is homogeneous of degree `0`,
  `GradedRing`);
* multiplicativity is `DirectSum.decompose_mul`: the degree-`(d+e)` component of
  `x · y` is `∑_{i+j = d+e} (proj_i x)(proj_j y)`, which matches the `T^{d+e}`
  coefficient of `(∑_i (proj_i x)Tⁱ)(∑_j (proj_j y)Tʲ)` because in `S[T;T⁻¹]`,
  `Tⁱ · Tʲ = T^{i+j}` (`LaurentPolynomial.T_add`).

We expose `Ψ` only through the two facts the rest of the argument needs:
  (i) the `T^i`-coefficient of `Ψ s` is the homogeneous component `proj 𝒮 i s`
      (`hΨ.1`), which is just `GradedRing.proj_apply` / the definition of `Ψ`;
  (ii) `Ψ s` is supported in nonnegative degrees (`hΨ.2`), since the grading is by `ℕ`.

The construction: build `Ψ` via
`(AddMonoidAlgebra.lift S ℤ S[T;T⁻¹]) ...` or directly as the `RingHom` whose
underlying function is `fun s => ∑ i ∈ (decompose 𝒮 s).support, C (proj 𝒮 i s) * T i`
(decidability of the support via `Classical`), with the three `RingHom` field proofs
discharged as above.  The coefficient fact (i) follows from
`Finset.sum`/`Finsupp` coefficient computation (`LaurentPolynomial.single`/`C_mul_T`
coefficients are `single` at the relevant degree). -/
theorem exists_gradedTwist :
    ∃ Ψ : S →+* S[T;T⁻¹],
      (∀ s : S, ∀ i : ℕ, (Ψ s).coeff (i : ℤ) = GradedRing.proj 𝒮 i s) ∧
      (∀ s : S, ∀ n : ℤ, n < 0 → (Ψ s).coeff n = 0) := by
  -- Strategy: construct Ψ as the degree-twist ring hom (see docstring) and read off
  -- the two coefficient facts. Uses `DirectSum.toSemiring`/`decomposeRingEquiv`,
  -- `GradedRing.proj_apply`, `LaurentPolynomial.{C, T, single_eq_C_mul_T, T_add}`,
  -- and `Classical` for the support `Finset`.
  classical
  refine ⟨(gradedTwistAux 𝒮).comp (DirectSum.decomposeRingEquiv 𝒮).toRingHom, ?_, ?_⟩
  · intro s i
    rw [RingHom.comp_apply]
    show (gradedTwistAux 𝒮 (DirectSum.decompose 𝒮 s)).coeff (i : ℤ) = _
    rw [gradedTwistAux_coeff, GradedRing.proj_apply]
    simp only [Nat.cast_inj]
    rw [Finset.sum_ite_eq (DFinsupp.support ((DirectSum.decompose 𝒮) s)) i
      (fun k => (((DirectSum.decompose 𝒮) s) k : S))]
    split
    · rfl
    · rename_i h
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at h
      rw [h]; simp
  · intro s n hn
    rw [RingHom.comp_apply]
    show (gradedTwistAux 𝒮 (DirectSum.decompose 𝒮 s)).coeff n = 0
    rw [gradedTwistAux_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ite_eq_right]
    intro hcon
    have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    omega

/-- A finite sum `∑ i ≤ n, C (g i) * X ^ i` is monic when `g n = 1`. -/
private theorem monic_sum_C_mul_X_pow {B : Type*} [CommRing B] (n : ℕ) (g : ℕ → B)
    (hg : g n = 1) : (∑ i ∈ Finset.range (n + 1), Polynomial.C (g i) * Polynomial.X ^ i).Monic := by
  classical
  have hcoeff : ∀ k, (∑ i ∈ Finset.range (n + 1),
      Polynomial.C (g i) * Polynomial.X ^ i).coeff k = if k ≤ n then g k else 0 := by
    intro k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range (n + 1)) k]
    simp [Finset.mem_range]
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hcoeff m]; simp [Nat.not_le.mpr hm]
  · rw [hcoeff n]; simpa using hg

open LaurentPolynomial in
/-- **(L2) The twist of an integral element is integral over `R[T;T⁻¹]`.**

Let `Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) : R[T;T⁻¹] →+* S[T;T⁻¹]`,
the coefficient-wise map (it sends `T ↦ T` and acts on coefficients by `algebraMap`).

Suppose `s` is integral over `R`: there is a monic `p = Y^n + a_{n-1}Y^{n-1} + ⋯ + a_0`
with `aᵢ ∈ R` and `s^n + φ(a_{n-1})s^{n-1} + ⋯ + φ(a_0) = 0` in `S` (here `φ = algebraMap R S`).
Apply the ring homomorphism `Ψ` (from L1) to this equation.  Because `Ψ` is a ring hom,
`Ψ(s)^n + Ψ(φ(a_{n-1}))·Ψ(s)^{n-1} + ⋯ + Ψ(φ(a_0)) = 0` in `S[T;T⁻¹]`.

It remains to see each `Ψ(φ(aᵢ))` lies in the image of `Φ`, i.e. equals `Φ(bᵢ)` for some
`bᵢ ∈ R[T;T⁻¹]`.  Decompose `aᵢ = ∑_e proj_e(aᵢ)` over the source grading `ℛ`.  Then
`φ(aᵢ) = ∑_e φ(proj_e aᵢ)`, and by `RespectsGrading`, `φ(proj_e aᵢ) ∈ 𝒮 e`, hence it is
its own degree-`e` homogeneous component: `proj_e (φ aᵢ) = φ(proj_e aᵢ)` and
`proj_k (φ aᵢ) = 0` for `k ≠ e` on that summand.  Therefore
`Ψ(φ aᵢ) = ∑_e φ(proj_e aᵢ)·T^e = ∑_e C(φ(proj_e aᵢ))·T^e = Φ(∑_e C(proj_e aᵢ)·T^e)`,
using `Φ ∘ C = C ∘ φ` and `Φ(T) = T` (`AddMonoidAlgebra.mapRingHom` fixes `T` and acts
as `algebraMap` on `C`).  Setting `bᵢ := ∑_e C(proj_e aᵢ)·T^e ∈ R[T;T⁻¹]` gives
`Ψ(φ aᵢ) = Φ(bᵢ)`.

Thus `Ψ(s)` satisfies the monic equation `Y^n + Φ(b_{n-1})Y^{n-1} + ⋯ + Φ(b_0)` with
coefficients in the image of `Φ`, i.e. `Φ.IsIntegralElem (Ψ s)` with witness the monic
polynomial `Y^n + ∑ bᵢ Yⁱ ∈ R[T;T⁻¹][Y]` mapped through `Φ`.  Concretely, take the
monic polynomial `q := (p.map C-then-twist) ∈ R[T;T⁻¹][Y]` and check
`Polynomial.aeval (Ψ s) (q.map Φ) = Ψ (Polynomial.aeval s p) = Ψ 0 = 0`. -/
theorem gradedTwist_isIntegral
    (hφ : RespectsGrading ℛ 𝒮)
    (Ψ : S →+* S[T;T⁻¹])
    (hΨ : ∀ s : S, ∀ i : ℕ, (Ψ s).coeff (i : ℤ) = GradedRing.proj 𝒮 i s)
    (hΨ0 : ∀ s : S, ∀ n : ℤ, n < 0 → (Ψ s).coeff n = 0)
    (s : S) (hs : IsIntegral R s) :
    (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem (Ψ s) := by
  -- Strategy: unfold `IsIntegral`/`RingHom.IsIntegralElem` to a monic `p ∈ R[Y]` with
  -- `aeval s p = 0`; transport along the ring hom `Ψ`; rewrite each coefficient image
  -- `Ψ (φ aᵢ)` as `Φ bᵢ` using `RespectsGrading` (`hφ`) and `Φ ∘ C = C ∘ φ`, `Φ T = T`.
  classical
  set Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) with hΦ
  set φ := algebraMap R S with hφdef
  -- coefficient-wise computations for `Φ`.
  have hΦC : ∀ r : R, Φ (LaurentPolynomial.C r) = LaurentPolynomial.C (φ r) := by
    intro r
    ext k
    rw [hΦ, AddMonoidAlgebra.coeff_mapRingHom]
    simp only [LaurentPolynomial.C_apply]; split <;> simp
  have hΦT : ∀ k : ℤ, Φ (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
    intro k
    ext k'
    rw [hΦ, AddMonoidAlgebra.coeff_mapRingHom]
    simp only [LaurentPolynomial.T_apply]; split <;> simp
  -- **Homogeneous helper_077g.** For `y ∈ 𝒮 e`, `Ψ y = C y · T^e`.  Here the nonnegative
  -- coefficients come from `hΨ`/`GradedRing.proj`, and the (otherwise undetermined)
  -- negative coefficients vanish by `hΨ0`.
  have hΨhom : ∀ (e : ℕ) (y : S), y ∈ 𝒮 e →
      Ψ y = LaurentPolynomial.C y * LaurentPolynomial.T (e : ℤ) := by
    intro e y hy
    ext m
    rw [gradedTwist_coeff_C_mul_T]
    rcases lt_or_ge m 0 with hm | hm
    · rw [ite_eq_right (by intro hc; omega), hΨ0 y m hm]
    · lift m to ℕ using hm with i
      rw [hΨ y i, GradedRing.proj_apply]
      by_cases h : i = e
      · subst h; rw [ite_eq_left rfl, DirectSum.decompose_of_mem_same 𝒮 hy]
      · rw [ite_eq_right (by exact_mod_cast h),
          DirectSum.decompose_of_mem_ne 𝒮 hy (by exact_mod_cast (Ne.symm h))]
  -- The per-scalar lift `b : R → R[T;T⁻¹]`, `b r = ∑_e (proj_e r)·T^e` (finite sum).
  set b : R → LaurentPolynomial R := fun r =>
    ∑ e ∈ (DirectSum.decompose ℛ r).support,
      LaurentPolynomial.C (GradedRing.proj ℛ e r) * LaurentPolynomial.T (e : ℤ) with hb
  -- `b` respects homogeneity: for `y ∈ ℛ e`, `b y = C y · T^e`.
  have hbhom : ∀ (e : ℕ) (y : R), y ∈ ℛ e →
      b y = LaurentPolynomial.C y * LaurentPolynomial.T (e : ℤ) := by
    intro e y hy
    rw [hb]; simp only
    have hsupp : ∀ k, k ∈ (DirectSum.decompose ℛ y).support →
        LaurentPolynomial.C (GradedRing.proj ℛ k y) * LaurentPolynomial.T (k:ℤ)
          = if k = e then LaurentPolynomial.C y * LaurentPolynomial.T (e:ℤ) else 0 := by
      intro k hk
      rw [GradedRing.proj_apply]
      by_cases h : k = e
      · subst h; rw [DirectSum.decompose_of_mem_same ℛ hy, ite_eq_left rfl]
      · rw [DirectSum.decompose_of_mem_ne ℛ hy (by exact_mod_cast (Ne.symm h)), ite_eq_right h]
        simp
    rw [Finset.sum_congr rfl hsupp, Finset.sum_ite_eq']
    by_cases he : e ∈ (DirectSum.decompose ℛ y).support
    · rw [ite_eq_left he]
    · rw [ite_eq_right he]
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at he
      have hp : GradedRing.proj ℛ e y = y := by
        rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same ℛ hy]
      rw [GradedRing.proj_apply, he] at hp
      simp only [ZeroMemClass.coe_zero] at hp
      rw [← hp]; simp
  have hb1 : b 1 = 1 := by
    have h1mem : (1:R) ∈ ℛ 0 := SetLike.GradedOne.one_mem
    rw [hbhom 0 1 h1mem]; simp
  -- **Key per-scalar identity:** `Ψ (φ r) = Φ (b r)`.
  have hΨφ : ∀ r : R, Ψ (φ r) = Φ (b r) := by
    intro r
    have hdec : φ r = ∑ e ∈ (DirectSum.decompose ℛ r).support, φ (GradedRing.proj ℛ e r) := by
      conv_lhs => rw [← DirectSum.sum_support_decompose ℛ r]
      rw [map_sum]; rfl
    rw [hdec, map_sum, hb, map_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hmem : φ (GradedRing.proj ℛ e r) ∈ 𝒮 e := by
      apply hφ e; rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
    rw [hΨhom e _ hmem, map_mul, hΦC, hΦT]
  -- Unfold integrality of `s` and build the monic witness over `R[T;T⁻¹]`.
  obtain ⟨p, hpmonic, hpeval⟩ := hs
  set n := p.natDegree with hn
  refine ⟨∑ i ∈ Finset.range (n + 1),
      Polynomial.C (b (p.coeff i)) * Polynomial.X ^ i,
    monic_sum_C_mul_X_pow n _ (by rw [hn, hpmonic.coeff_natDegree, hb1]), ?_⟩
  · -- it `eval₂ Φ (Ψ s)`-vanishes, by transporting the relation for `s` through `Ψ`.
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
      Polynomial.eval₂_X]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        Φ (b (p.coeff i)) * (Ψ s) ^ i = Ψ (φ (p.coeff i) * s ^ i) := by
      intro i hi; rw [← hΨφ, map_mul, map_pow]
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have heq : ∑ i ∈ Finset.range (n + 1), φ (p.coeff i) * s ^ i
        = Polynomial.eval₂ φ s p := by
      rw [Polynomial.eval₂_eq_sum_range, ← hn]
    rw [heq, hpeval, map_zero]

/-- **(L3a-i) Unit-times-integral descent (general algebra fact).**

If `f : A →+* B` is a ring hom, `u : Bˣ` a unit whose value `(u : B)` and inverse
`(↑u⁻¹ : B)` both lie in the image of `f`, and `f.IsIntegralElem ((u : B) * x)`, then
`f.IsIntegralElem x`.  (Divide the monic equation for `u·x` by powers of `u`, absorbing
each `u^{j-d}` into the base coefficients since `u^{±1} ∈ im f`.)

Used at the end of the L3a argument (after isolating `Δ·(w n)·Tⁿ` and making `Δ` a
unit) to strip the unit `Δ` and conclude `(w n)·Tⁿ` is integral.  Mechanical but needs
the explicit coefficient manipulation. -/
theorem isIntegralElem_of_unit_mul
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (u : Bˣ) (hu' : (↑u⁻¹ : B) ∈ Set.range f)
    (x : B) (hx : f.IsIntegralElem ((u : B) * x)) :
    f.IsIntegralElem x := by
  -- Divide the monic relation `(u·x)^d + ∑_{j<d} f(a_j)(u·x)^j = 0` by `u^d`:
  -- `x^d + ∑_{j<d} f(a_j)·u^{j-d}·x^j = 0`; each `u^{j-d} ∈ im f` (as `u,u⁻¹ ∈ im f`),
  -- so `f(a_j)·u^{j-d} = f(a_j')` for some `a_j' ∈ A`, giving a monic relation over `im f`.
  classical
  obtain ⟨p, hpmonic, hpeval⟩ := hx
  obtain ⟨c, hc⟩ := hu'
  set d := p.natDegree with hd
  refine ⟨∑ i ∈ Finset.range (d + 1),
      Polynomial.C (p.coeff i * c ^ (d - i)) * Polynomial.X ^ i,
    monic_sum_C_mul_X_pow d _ (by simp [hd, hpmonic.coeff_natDegree]), ?_⟩
  · -- the witness evaluates to zero at `x`
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Polynomial.eval₂_X, map_mul, map_pow, hc]
    rw [Polynomial.eval₂_eq_sum_range, ← hd] at hpeval
    -- key per-term identity: divide by `u^d`
    have hkey : ∀ i ∈ Finset.range (d + 1),
        f (p.coeff i) * (↑u⁻¹ : B) ^ (d - i) * x ^ i
          = (↑u⁻¹ : B) ^ d * (f (p.coeff i) * (↑u * x) ^ i) := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      have hpow : (↑u⁻¹ : B) ^ (d - i) = (↑u⁻¹ : B) ^ d * (↑u : B) ^ i := by
        have hsplit : (↑u⁻¹ : B) ^ d = (↑u⁻¹ : B) ^ (d - i) * (↑u⁻¹ : B) ^ i := by
          rw [← pow_add, Nat.sub_add_cancel hi]
        rw [hsplit, mul_assoc, ← mul_pow]
        simp [Units.inv_mul]
      rw [hpow]
      ring
    rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum, hpeval, mul_zero]
