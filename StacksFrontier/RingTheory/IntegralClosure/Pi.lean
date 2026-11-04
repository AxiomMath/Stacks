module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Integrality in a finite product of rings is componentwise

All rings here are commutative with unit and all ring maps are unital. Given ring
maps `φ_i : R_i → S_i` for `i = 1, …, n`, form the product rings `R = ∏ R_i` and
`S = ∏ S_i` with componentwise operations and unit `(1, …, 1)`, and the product map
`φ = ∏ φ_i : R → S`, `φ (r_1, …, r_n) = (φ_1 r_1, …, φ_n r_n)`. Then an element
`s = (s_1, …, s_n)` of `S` is integral over `R` via `φ` if and only if each component
`s_i` is integral over `R_i` via `φ_i`. This is Stacks Tag 0CY8, "finite product
integral".

Recall that `s ∈ S` is *integral over* `R` along `φ : R → S` when there is a monic
`p = X^m + a_{m-1} X^{m-1} + ⋯ + a_1 X + a_0` with `a_j ∈ R` and `m ≥ 1` such that
`s^m + φ(a_{m-1}) s^{m-1} + ⋯ + φ(a_1) s + φ(a_0) = 0` in `S`. In Mathlib this is
`IsIntegral R s`, the `R`-algebra structure on `S` being the one whose `algebraMap`
is `φ`.

## Main results

* `isIntegral_pi_iff`: `IsIntegral (∀ i, R i) s ↔ ∀ i, IsIntegral (R i) (s i)`, for a
  finite index type.
* `isIntegral_pi_fin_iff`: the same statement indexed by `Fin n`, matching the shape
  of the source.
* `algebraMap_pi_apply`: the structure map of the product algebra is the
  componentwise product of the `φ_i`, which is what identifies the Mathlib set-up
  with the product map of the source.
* `IsIdempotentElem.isIntegral`: an idempotent of an `R`-algebra is integral over
  `R`, being a root of `X² - X`. Not a statement about products; it lives here
  because this is the lowest module shared by the proofs that need it.

## Implementation notes

The finite product of the rings `R_i` over an index type `ι` is the dependent function
type `∀ i, R i` with the `Pi` ring structure, and the product of the ring maps is the
`Pi.algebra` instance. The forward direction of the equivalence projects a witnessing
monic polynomial componentwise. The reverse direction pads each component's witness
`f i` by a power of `X` up to the common degree `D = sup_i deg (f i)`, so that the
padded polynomials have coefficient `1` in degree `D`, and then assembles them into a
single monic polynomial over `∀ i, R i` coefficientwise.
-/

@[expose] public section

/-- The structure map `φ = algebraMap (∏ R_i) (∏ S_i)` of the
product `R`-algebra acts componentwise as `φ_i = algebraMap (R i) (S i)`. -/
theorem algebraMap_pi_apply (ι : Type*) (R : ι → Type*) (S : ι → Type*)
    [∀ i, CommSemiring (R i)] [∀ i, Semiring (S i)] [∀ i, Algebra (R i) (S i)]
    (r : ∀ i, R i) (i : ι) :
    (algebraMap (∀ i, R i) (∀ i, S i) r) i = algebraMap (R i) (S i) (r i) :=
  rfl

/-- **Stacks Tag 0CY8 (finite product integral).**
Let `ι` be a finite index type and let `φ_i : R_i → S_i` be ring maps (recorded as the
`Algebra (R i) (S i)` instances). For the product rings `∏ R_i = ∀ i, R i` and
`∏ S_i = ∀ i, S i` with the product algebra structure, an element `s = (s_i)_i` of
`∏ S_i` is integral over `∏ R_i` if and only if each component `s_i` is integral over
`R_i`. -/
@[stacks 0CY8]
theorem isIntegral_pi_iff (ι : Type*) [Finite ι] (R : ι → Type*) (S : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (s : ∀ i, S i) :
    IsIntegral (∀ i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) := by
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · -- forward direction: project a witnessing monic polynomial componentwise, i.e. push the
    -- integrality along the evaluation maps `Pi.evalRingHom R i`, `Pi.evalRingHom S i`, which
    -- form a commuting square with the two structure maps.
    intro hs i
    exact hs.map_of_comp_eq (Pi.evalRingHom R i) (Pi.evalRingHom S i) rfl
  · -- backward direction: assemble a single monic polynomial out of the components
    intro h
    choose f hfmonic hfeval using h
    set D : ℕ := Finset.univ.sup (fun i => (f i).natDegree) with hD
    have hdle : ∀ i, (f i).natDegree ≤ D :=
      fun i => Finset.le_sup (f := fun i => (f i).natDegree) (Finset.mem_univ i)
    set g : ∀ i, Polynomial (R i) := fun i => Polynomial.X ^ (D - (f i).natDegree) * f i with hg
    -- coeff D of g i is 1
    have hgcoeff : ∀ i, (g i).coeff D = 1 := by
      intro i
      have hDeq : (f i).natDegree + (D - (f i).natDegree) = D := by
        have := hdle i; omega
      have hc := Polynomial.coeff_X_pow_mul (f i) (D - (f i).natDegree) (f i).natDegree
      rw [hDeq] at hc
      rw [hg]
      simp only
      rw [hc, (hfmonic i).coeff_natDegree]
    -- natDegree of g i ≤ D
    have hgdeg : ∀ i, (g i).natDegree ≤ D := by
      intro i
      rw [hg]; simp only
      calc (Polynomial.X ^ (D - (f i).natDegree) * f i).natDegree
          ≤ (Polynomial.X ^ (D - (f i).natDegree)).natDegree + (f i).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ (D - (f i).natDegree) + (f i).natDegree := by
              gcongr; exact Polynomial.natDegree_X_pow_le _
        _ = D := by have := hdle i; omega
    -- eval₂ of g i at s i is zero
    have hgeval : ∀ i, Polynomial.eval₂ (algebraMap (R i) (S i)) (s i) (g i) = 0 := by
      intro i
      rw [hg]; simp only
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, hfeval i, mul_zero]
    -- assemble the product polynomial
    set c : ℕ → (∀ i, R i) := fun j => fun i => (g i).coeff j with hc
    set F : Polynomial (∀ i, R i) := ∑ j ∈ Finset.range (D + 1), Polynomial.monomial j (c j) with hF
    -- the coefficients of `F`: those of `c` up to degree `D`, and zero beyond
    have hFcoeff : ∀ N, F.coeff N = if N ≤ D then c N else 0 := by
      intro N
      simp [hF, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    -- F maps componentwise to g i
    have hmap : ∀ i, F.map (Pi.evalRingHom R i) = g i := by
      intro i
      ext N
      rw [Polynomial.coeff_map, hFcoeff]
      split_ifs with hN
      · rfl
      · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hgdeg i; omega)).symm
    have hFmonic : F.Monic := by
      refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one D ?_ ?_
      · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
        simp [hFcoeff, hN.not_ge]
      · simp [hFcoeff, hc, funext_iff, hgcoeff]
    -- conclude
    refine ⟨F, hFmonic, ?_⟩
    funext i
    show (Pi.evalRingHom S i) (Polynomial.eval₂ (algebraMap (∀ i, R i) (∀ i, S i)) s F)
        = (0 : ∀ i, S i) i
    rw [Polynomial.hom_eval₂]
    have key : (Pi.evalRingHom S i).comp (algebraMap (∀ i, R i) (∀ i, S i))
        = (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i) := rfl
    rw [key]
    have hsi : (Pi.evalRingHom S i) s = s i := rfl
    rw [hsi, ← Polynomial.eval₂_map, hmap i, hgeval i]
    rfl

/-- The `Fin n` formulation matching the source statement: an element
`s = (s_1, …, s_n)` of `∏_i S_i` is integral over `∏_i R_i` if and only if each
component `s_i` is integral over `R_i`.

The source assumes `n ≥ 1`; no such hypothesis is needed, the equivalence holding for
every `n` (for `n = 0` both sides are vacuously true). -/
theorem isIntegral_pi_fin_iff (n : ℕ) (R : Fin n → Type*) (S : Fin n → Type*)
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (s : ∀ i, S i) :
    IsIntegral (∀ i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) :=
  isIntegral_pi_iff (Fin n) R S s

/-! ### The constant-base variant, and the integral closure of a product -/

/-- **Integrality over a fixed base is componentwise.** -/
theorem isIntegral_pi_iff_const
    {R ι : Type*} [CommRing R] [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] (x : ∀ i, S i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  refine ⟨fun h i => h.map (Pi.evalAlgHom R S i), fun h => ?_⟩
  let := Fintype.ofFinite ι
  choose p hp hz using h
  refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ (fun i _ => hp i), funext fun i => ?_⟩
  show (Pi.evalAlgHom R S i) (Polynomial.aeval x (∏ j, p j)) = 0
  rw [← Polynomial.aeval_algHom_apply]
  simp only [Pi.evalAlgHom_apply, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i)

/-- **Nilpotence in a finite product is componentwise.** -/
theorem isNilpotent_pi_iff {ι : Type*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] (x : ∀ i, S i) :
    IsNilpotent x ↔ ∀ i, IsNilpotent (x i) := by
  let := Fintype.ofFinite ι
  refine ⟨fun h i => h.map (Pi.evalRingHom S i), fun h => ?_⟩
  choose n hn using h
  exact ⟨∑ i, n i, funext fun i => pow_eq_zero_of_le (Finset.single_le_sum
    (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)) (hn i)⟩

/-- **The integral closure of a finite product over a fixed base is the product of the integral
closures.** -/
noncomputable def integralClosurePiEquiv
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] :
    integralClosure R (∀ i, S i) ≃ₐ[R] ∀ i, integralClosure R (S i) :=
  { toFun := fun x i => ⟨x.1 i, (isIntegral_pi_iff_const x.1).mp x.2 i⟩
    invFun := fun x => ⟨fun i => (x i).1, (isIntegral_pi_iff_const _).mpr fun i => (x i).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

/-- An idempotent is integral over any base ring, as a root of `X² - X`. -/
theorem IsIdempotentElem.isIntegral {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {e : A}
    (he : IsIdempotentElem e) : IsIntegral R e :=
  ⟨Polynomial.X ^ 2 - Polynomial.X,
    Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)),
    by simp [sq, he.eq]⟩
