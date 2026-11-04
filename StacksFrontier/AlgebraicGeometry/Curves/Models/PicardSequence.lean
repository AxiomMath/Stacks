module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
import StacksCore.Tactic.StacksAttribute

/-!
# The Picard sequence of a regular proper model

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve `C` over the fraction
field of a discrete valuation ring, with `H⁰(C, 𝒪_C) = K`, and write the special fibre as a sum
of effective Cartier divisors `X_k = Σ mᵢ Cᵢ`. [Stacks, Tag 0C63] asserts that

`0 ⟶ ℤ ⟶ ℤ^{⊕n} ⟶ Pic(X) ⟶ Pic(C) ⟶ 0`

is exact, where the first map sends `1` to `(m₁, …, mₙ)`, the second sends the `i`th basis
vector to the class of `𝒪_X(Cᵢ)`, and the third is restriction to the generic fibre.

This file constructs the three maps as homomorphisms of abelian groups and proves that the
composite of the first two maps vanishes and that the first map is injective: the sequence is a
complex at `ℤ^{⊕n}` and exact at `ℤ`.

## Main definitions

* `Stacks.Models.RegularModelSituation.genericFiberToModel` — the morphism `C ⟶ X`
  identifying the curve with the generic fibre of its model.
* `Stacks.Models.multiplicityHom` — the first map `ℤ ⟶ ℤ^{⊕n}`, multiplication by the
  multiplicity vector.
* `Stacks.Models.componentPicardHom` — the second map `ℤ^{⊕n} ⟶ Pic(X)`,
  `a ↦ Σ aᵢ [𝒪_X(Cᵢ)]`.
* `Stacks.Models.genericFiberPicardRestriction` — the third map `Pic(X) ⟶ Pic(C)`, pullback of
  Picard classes along the generic-fibre inclusion.

## Main results

* `Stacks.Divisors.picardClass_prod_pow` — the Picard class of a finite sum `Σ mᵢ Dᵢ` of
  effective Cartier divisors is `Σ mᵢ [𝒪_X(Dᵢ)]`.
* `Stacks.Models.multiplicityHom_one` — the first map sends `1` to `(m₁, …, mₙ)`.
* `Stacks.Models.componentPicardHom_single` — the second map sends the `i`th basis vector to
  `[𝒪_X(Cᵢ)]`.
* `Stacks.Models.componentPicardHom_multiplicityHom` — the composite `ℤ ⟶ ℤ^{⊕n} ⟶ Pic(X)`
  is zero.
* `Stacks.Models.exists_multiplicity_ne_zero` — some multiplicity is nonzero.
* `Stacks.Models.injective_multiplicityHom` — the first map is injective, which is exactness of
  the sequence at `ℤ`.
* `Stacks.Models.picardSequence_specialFiberComponents` — the four statements above at once, for
  the canonical family: the irreducible components of `X_k` with their reduced induced
  structure.

## References

* [Stacks Project, Tag 0C63](https://stacks.math.columbia.edu/tag/0C63)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme schemePullbackClassHom)

universe u

namespace Stacks.Divisors

/-! ### The Picard class of a finite sum of effective Cartier divisors -/

variable {X : Scheme.{u}} {ι : Type*}

/-- The sum `Σ nᵢ Dᵢ` of finitely many effective Cartier divisors with nonnegative
multiplicities is an effective Cartier divisor. -/
instance IsEffectiveCartierDivisor.finsetProdPow (s : Finset ι) (C : ι → X.IdealSheafData)
    (m : ι → ℕ) [∀ i, IsEffectiveCartierDivisor (C i)] :
    IsEffectiveCartierDivisor (∏ i ∈ s, C i ^ m i) :=
  isEffectiveCartierDivisor_prod s C m fun _ _ => inferInstance

/-- **The Picard class of a finite sum of effective Cartier divisors**,
`[𝒪_X(Σ mᵢ Dᵢ)] = Σ mᵢ [𝒪_X(Dᵢ)]`. -/
theorem picardClass_prod_pow (s : Finset ι) (C : ι → X.IdealSheafData) (m : ι → ℕ)
    [∀ i, IsEffectiveCartierDivisor (C i)] :
    picardClass (∏ i ∈ s, C i ^ m i) = ∑ i ∈ s, (m i : ℤ) • picardClass (C i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      have hone : (∏ i ∈ (∅ : Finset ι), C i ^ m i) = (⊤ : X.IdealSheafData) :=
        (Finset.prod_empty).trans Scheme.IdealSheafData.one_eq_top
      rw [Finset.sum_empty]
      exact (picardClass_congr hone).trans picardClass_top
  | cons i s hi ih =>
      have hp : (∏ j ∈ Finset.cons i s hi, C j ^ m j) = C i ^ m i * ∏ j ∈ s, C j ^ m j :=
        Finset.prod_cons hi
      rw [Finset.sum_cons]
      refine (picardClass_congr hp).trans ?_
      rw [picardClass_mul, picardClass_pow, ih]

end Stacks.Divisors

namespace Stacks.Models

open Stacks.Divisors

namespace RegularModelSituation

/-- **The inclusion of the curve as the generic fibre of its model.** The identification of `C`
with `X_K` carried by the situation, followed by the projection `X_K ⟶ X`. -/
def genericFiberToModel (S : RegularModelSituation.{u}) : S.C ⟶ S.X :=
  S.genericFiberIso.hom ≫
    pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))

end RegularModelSituation

/-! ### The three maps of the sequence -/

section Maps

variable (S : RegularProperModelSituation.{u}) {ι : Type*} [Fintype ι]
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ) [∀ i, IsEffectiveCartierDivisor (C i)]

/-- **The first map `ℤ ⟶ ℤ^{⊕n}` of the Picard sequence of a regular model**: multiplication by
the vector of multiplicities of the components of the special fibre. -/
def multiplicityHom {ι : Type*} (m : ι → ℕ) : ℤ →+ (ι → ℤ) where
  toFun a := fun i => a * (m i : ℤ)
  map_zero' := funext fun i => zero_mul (m i : ℤ)
  map_add' a b := funext fun i => add_mul a b (m i : ℤ)

/-- The first map of the sequence is multiplication by the multiplicity vector. -/
@[simp] theorem multiplicityHom_apply {ι : Type*} (m : ι → ℕ) (a : ℤ) :
    multiplicityHom m a = fun i => a * (m i : ℤ) := rfl

/-- The first map of the sequence sends `1` to the vector `(m₁, …, mₙ)` of multiplicities. -/
@[stacks 0C63 "the first map, which sends 1 to (m_1, ..., m_n)"]
theorem multiplicityHom_one {ι : Type*} (m : ι → ℕ) :
    multiplicityHom m 1 = fun i => (m i : ℤ) :=
  funext fun i => one_mul (m i : ℤ)

/-- **The second map `ℤ^{⊕n} ⟶ Pic(X)` of the Picard sequence of a regular model**: the integral
combination `a ↦ Σ aᵢ [𝒪_X(Cᵢ)]` of the classes of the invertible sheaves of the components of
the special fibre. -/
def componentPicardHom : (ι → ℤ) →+ ofScheme S.X where
  toFun a := ∑ i, a i • picardClass (C i)
  map_zero' := Finset.sum_eq_zero fun i _ => zero_smul ℤ (picardClass (C i))
  map_add' a b := by
    change ∑ i, (a i + b i) • picardClass (C i) = _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_smul (a i) (b i) (picardClass (C i))

/-- The second map of the sequence is the integral combination of the component classes. -/
@[simp] theorem componentPicardHom_apply (a : ι → ℤ) :
    componentPicardHom S C a = ∑ i, a i • picardClass (C i) := rfl

/-- The second map of the sequence sends the `i`th basis vector of `ℤ^{⊕n}` to the class of
`𝒪_X(Cᵢ)`. -/
@[stacks 0C63 "the second map, which sends the ith basis vector to O_X(C_i)"]
theorem componentPicardHom_single [DecidableEq ι] (i : ι) :
    componentPicardHom S C (Pi.single i 1) = picardClass (C i) := by
  rw [componentPicardHom_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]), Pi.single_eq_same, one_smul]

/-- **The third map `Pic(X) ⟶ Pic(C)` of the Picard sequence of a regular model**: restriction
of Picard classes along the inclusion of the generic fibre. -/
@[stacks 0C63 "the third map, restriction of Picard classes to the generic fibre"]
def genericFiberPicardRestriction : ofScheme S.X →+ ofScheme S.C :=
  schemePullbackClassHom S.genericFiberToModel

end Maps

/-! ### Some multiplicity of the decomposition is nonzero -/

section Nondegeneracy

variable (S : RegularProperModelSituation.{u}) {ι : Type*} [Fintype ι]
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ)

/-- **Some multiplicity of the decomposition is nonzero.** If the special fibre of a regular
proper model is `X_k = Σ mᵢ Cᵢ`, then some `mᵢ` is nonzero. -/
theorem exists_multiplicity_ne_zero (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i) :
    ∃ i, m i ≠ 0 := by
  by_contra hcon
  have hzero : ∀ i, m i = 0 := fun i => by
    by_contra hi
    exact hcon ⟨i, hi⟩
  have htop : S.specialFiberι.ker = (⊤ : S.X.IdealSheafData) := by
    have h1 : (∏ i, C i ^ m i) = ∏ _i : ι, (1 : S.X.IdealSheafData) :=
      Finset.prod_congr rfl fun i _ => by rw [hzero i, pow_zero]
    refine hdec.trans (h1.trans ?_)
    rw [Finset.prod_const_one]
    exact Scheme.IdealSheafData.one_eq_top
  have : Nonempty S.specialFiber := S.nonempty_specialFiber
  have hne : (S.specialFiberι.ker.support : Set S.X).Nonempty := by
    rw [Scheme.Hom.support_ker]
    exact Set.Nonempty.mono subset_closure (Set.range_nonempty _)
  rw [htop, Scheme.IdealSheafData.support_top] at hne
  simp at hne

end Nondegeneracy

/-! ### The sequence is a complex at `ℤ^{⊕n}` and exact at `ℤ` -/

section Exactness

variable (S : RegularProperModelSituation.{u}) {ι : Type*} [Fintype ι]
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ) [∀ i, IsEffectiveCartierDivisor (C i)]
  (hdec : S.specialFiberIdeal = ∏ i, C i ^ m i)

include hdec

/-- **The class of the special fibre as a combination of the classes of its components**: if
`X_k = Σ mᵢ Cᵢ`, then `Σ mᵢ [𝒪_X(Cᵢ)] = 0`. -/
theorem sum_nsmul_picardClass_eq_zero : ∑ i, (m i : ℤ) • picardClass (C i) = 0 :=
  ((picardClass_prod_pow Finset.univ C m).symm.trans
    (picardClass_congr hdec.symm)).trans (picardClass_specialFiberIdeal S)

/-- The composite of the first two maps of the sequence vanishes. -/
@[stacks 0C63 "the composite Z -> Z^n -> Pic(X) vanishes"]
theorem componentPicardHom_multiplicityHom (a : ℤ) :
    componentPicardHom S C (multiplicityHom m a) = 0 := by
  have hsum : ∑ i, (a * (m i : ℤ)) • picardClass (C i) =
      a • ∑ i, (m i : ℤ) • picardClass (C i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul a (m i : ℤ) (picardClass (C i))
  show ∑ i, (a * (m i : ℤ)) • picardClass (C i) = 0
  rw [hsum, sum_nsmul_picardClass_eq_zero S C m hdec, smul_zero]

omit [∀ i, IsEffectiveCartierDivisor (C i)] in
/-- The first map of the sequence is injective, which is exactness at `ℤ`. -/
@[stacks 0C63 "exactness at Z, i.e. injectivity of the first map"]
theorem injective_multiplicityHom : Function.Injective (multiplicityHom (ι := ι) m) := by
  obtain ⟨i, hi⟩ := exists_multiplicity_ne_zero S C m hdec
  intro a b hab
  exact mul_right_cancel₀ (Int.natCast_ne_zero.2 hi) (congrFun hab i)

end Exactness

/-! ### The sequence for the canonical components of the special fibre -/

section CanonicalComponents

/-- The reduced closed subscheme of the model supported on an irreducible component of the
special fibre is an effective Cartier divisor. -/
instance isEffectiveCartierDivisor_specialFiberComponentIdeal (S : RegularModelSituation.{u})
    (Z : irreducibleComponents S.specialFiber) :
    IsEffectiveCartierDivisor (S.specialFiberComponentIdeal Z) :=
  S.isEffectiveCartierDivisor_specialFiberComponent Z

variable (S : RegularProperModelSituation.{u})
  [Fintype (irreducibleComponents S.specialFiber)]
  [DecidableEq (irreducibleComponents S.specialFiber)]
  (m : irreducibleComponents S.specialFiber → ℕ)

/-- Take the family `C₁, …, Cₙ` to be the irreducible components of `X_k` with their reduced
induced structure, and let `mᵢ` be multiplicities with `X_k = Σ mᵢ Cᵢ`. Then the first map of
the sequence sends `1` to `(m₁, …, mₙ)`, the second sends the `i`th basis vector to
`[𝒪_X(Cᵢ)]`, the composite of the two vanishes, and the first map is injective. -/
@[stacks 0C63 "the two named maps and the clauses proved here, for the components of X_k"]
theorem picardSequence_specialFiberComponents
    (hdec : S.specialFiberIdeal =
      ∏ Z, RegularModelSituation.specialFiberComponentIdeal S.toRegularModelSituation Z ^ m Z) :
    multiplicityHom m 1 = (fun Z => (m Z : ℤ)) ∧
      (∀ Z, componentPicardHom S
          (RegularModelSituation.specialFiberComponentIdeal S.toRegularModelSituation)
          (Pi.single Z 1) =
        picardClass
          (RegularModelSituation.specialFiberComponentIdeal S.toRegularModelSituation Z)) ∧
      (∀ a, componentPicardHom S
        (RegularModelSituation.specialFiberComponentIdeal S.toRegularModelSituation)
        (multiplicityHom m a) = 0) ∧
      Function.Injective (multiplicityHom m) :=
  ⟨multiplicityHom_one m,
    fun Z => componentPicardHom_single S _ Z,
    fun a => componentPicardHom_multiplicityHom S _ m hdec a,
    injective_multiplicityHom S _ m hdec⟩

end CanonicalComponents

end Stacks.Models

end
