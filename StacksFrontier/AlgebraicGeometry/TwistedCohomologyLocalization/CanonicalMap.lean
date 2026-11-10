module

public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.Untwisting
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.PowerSectionGradedRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of [Stacks, Tag 09MR] and its bijectivity on the nonvanishing open

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` a global section, `ℱ` an
`𝒪_X`-module, `p` a cohomological degree and `U ⊆ X` an open. [Stacks, Tag 09MR] asserts that the
canonical map

`H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ∩ X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

out of the degree-zero localization at `s` of the graded module
`H^p_*(U, ℒ, ℱ) = ⨁_{j ∈ ℤ} H^p(U, ℱ ⊗ ℒ^{⊗ j})` over `Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` is an
isomorphism when `U` is quasi-compact and quasi-separated.

This file constructs that map and proves it **bijective whenever `U` is contained in the
nonvanishing open `X_s`**, with no hypothesis on `X`, on `ℱ` or on `p`.

## The map

Every element of `H^p_*(U, ℒ, ℱ)₍s₎` is a fraction `ξ / sⁿ` with `ξ ∈ H^p(U, ℱ ⊗ ℒ^{⊗ n})`. Its
image is `s^{-n} ξ`: restrict `ξ` to `U ∩ X_s` and undo the twist there, which is possible
because multiplication by `sⁿ` is invertible on the cohomology of any open inside `X_s`.

## Main definitions

* `Stacks.Cohomology.TwistedLocalizationMap.untwistIso`: multiplication by `sⁿ` as an isomorphism
  `H^p(U ∩ X_s, ℱ) ≅ H^p(U ∩ X_s, ℱ ⊗ ℒ^{⊗ n})`.
* `Stacks.Cohomology.TwistedLocalizationMap.numeratorMap`: the family `ξ ↦ s^{-n} ξ|_{U ∩ X_s}`
  indexed by the exponent of the denominator.
* `Stacks.Cohomology.TwistedLocalizationMap.canonicalMap`: **the comparison map of
  [Stacks, Tag 09MR]**.

## Main results

* `Stacks.Cohomology.TwistedLocalizationMap.canonicalMap_fraction`: **the formula
  `ξ / sⁿ ↦ s^{-n} ξ`**.
* `Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_of_le_nonvanishingOpen`:
  **[Stacks, Tag 09MR] for an open contained in `X_s`**: there the comparison map is bijective,
  for an arbitrary scheme, an arbitrary module and every degree.

## The case `U ⊆ X_s`

The case `U ⊆ X_s` needs no finiteness hypothesis: no quasi-compactness or quasi-separatedness
of `U`, no quasi-coherence of `ℱ`. It is **not** a vanishing statement: taking `U = X_s` it says
that

`H^p_*(X_s, ℒ, ℱ)₍s₎ ⟶ H^p(X_s, ℱ)`

is an isomorphism on any scheme at all, and neither side is forced to be zero; contrast
`Stacks.Cohomology.TwistedGradedModule.bijective_of_isAffineOpen`, where the conclusion holds
because both sides are trivial. Neither this case nor the quasi-compact quasi-separated case of
the tag subsumes the other.

## Implementation notes

Isomorphy is carried as explicit data, never as an instance: `untwistIso` is a bundled
`CategoryTheory.Iso` rather than an `IsIso` instance, because in these categories instance search
does not recover the sheaf of rings from a morphism's type. For the same reason the cancellation
of an isomorphism against its inverse is done by `inv_comp_eq_inv`, stated for an abstract
isomorphism of abelian groups, rather than by rewriting inside the concrete types.

The degree of `s` in the graded section ring is `1`, so a numerator over the denominator `sⁿ` has
degree `((n * 1 : ℕ) : ℤ)`.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules DirectSum
open Stacks.Cohomology.TwistedGradedModule
open scoped DirectSum

universe u

namespace Stacks.Cohomology.TwistedLocalizationMap

/-! ### Restriction along an equality of opens -/

section Restriction

variable {Y : Type u} [TopologicalSpace Y]
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **Restriction of cohomology along `le_refl` is the identity.** -/
theorem hrestrict_refl (W : Opens Y) (p : ℕ) (G : SheafOfModules.{u} R) :
    Hrestrict R (le_refl W) p G = 𝟙 (Hgroup R W p G) := by
  have h : secRestrict R (le_refl W) = 𝟙 (secF R W) := by
    unfold secRestrict
    rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]
    rfl
  change (NatTrans.rightDerived (secRestrict R (le_refl W)) p).app G = _
  rw [h, NatTrans.rightDerived_id]
  rfl

/-- **Restriction of cohomology along an equality of opens is an isomorphism.** -/
theorem isIso_hrestrict_of_eq {V W : Opens Y} (h : W ≤ V) (he : W = V) (p : ℕ)
    (G : SheafOfModules.{u} R) : IsIso (Hrestrict R h p G) := by
  subst he
  rw [hrestrict_refl]
  infer_instance

end Restriction

/-! ### Cancelling an isomorphism against its inverse -/

/-- If `e₁.hom ≫ f = e₂.hom` then `e₂.inv ∘ f = e₁.inv` on elements. -/
theorem inv_comp_eq_inv {A B₁ B₂ : AddCommGrpCat.{u}} (e₁ : A ≅ B₁) (e₂ : A ≅ B₂)
    (f : B₁ ⟶ B₂) (hf : e₁.hom ≫ f = e₂.hom) (x : B₁) :
    (ConcreteCategory.hom e₂.inv) ((ConcreteCategory.hom f) x) =
      (ConcreteCategory.hom e₁.inv) x := by
  have h1 : (ConcreteCategory.hom f) x =
      (ConcreteCategory.hom e₂.hom) ((ConcreteCategory.hom e₁.inv) x) := by
    conv_lhs => rw [← Iso.inv_hom_id_apply e₁ x]
    rw [← ConcreteCategory.comp_apply, hf]
  rw [h1, Iso.hom_inv_id_apply]

/-- An element whose image under an isomorphism of abelian groups is zero is itself zero. -/
private theorem eq_zero_of_hom_apply_eq_zero {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : A)
    (h : ConcreteCategory.hom e.hom x = 0) : x = 0 := by
  simpa using congrArg (ConcreteCategory.hom e.inv) h

/-! ### A bijectivity criterion for the lift to the degree-zero localization -/

/-- **A compatible family whose degree-one member is surjective and whose members kill no
homogeneous element lifts to a bijection out of the degree-zero localization.** -/
theorem bijective_degreeZeroLocalizationLiftOfDegree {R : Type u} {M : Type u} {σ : Type u}
    {τ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
    [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
    [SetLike.GradedSMul A B] {f : R} (hf : f ∈ A 1)
    {N : Type u} [AddCommGroup N] (e : ℕ → M →+ N)
    (he : ∀ (n k : ℕ) (x : M), x ∈ B ((n * 1 : ℕ) : ℤ) → e (n + k) (f ^ k • x) = e n x)
    (hsurj : ∀ y : N, ∃ x : M, ∃ _ : x ∈ B ((1 * 1 : ℕ) : ℤ), e 1 x = y)
    (hinj : ∀ (n : ℕ) (x : M), x ∈ B ((n * 1 : ℕ) : ℤ) → e n x = 0 → x = 0) :
    Function.Bijective (degreeZeroLocalizationLiftOfDegree A B hf e he) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz0 ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, x, hx, hfrac⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
    rw [degreeZeroLocalizationLiftOfDegree_fraction A B hf e he z n x hx hfrac] at hz0
    rw [eq_zero_iff_exists_pow_smul_eq_zero A B z n x hfrac]
    exact ⟨0, by rw [pow_zero, one_smul, hinj n x hx hz0]⟩
  · obtain ⟨x, hxmem, hxy⟩ := hsurj y
    exact ⟨⟨LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ 1, by exact ⟨1, rfl⟩⟩,
      mk_mem_degreeZeroLocalization_of_degree A B hf 1 x hxmem⟩,
      (degreeZeroLocalizationLiftOfDegree_fraction A B hf e he _ 1 x hxmem rfl).trans hxy⟩

/-! ### The comparison map -/

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections) (F : X.Modules) (p : ℕ) (U : X.Opens)

/-- The part of the open `U` on which `s` does not vanish, `U ∩ X_s`. -/
abbrev nonvanishingPart : X.Opens := U ⊓ nonvanishingOpen L s

/-- **Multiplication by `sⁿ` on the cohomology of `U ∩ X_s`.** -/
def untwist (n : ℕ) :
    Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F ⟶
      Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p (twist X L F (n : ℤ)) :=
  (Hfunctor X.ringCatSheaf (nonvanishingPart X L s U) p).map
    (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
      (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n))

/-- Multiplication by `sⁿ` is an isomorphism on the cohomology of `U ∩ X_s`, which lies inside
the nonvanishing open of `s`. -/
theorem isIso_untwist (n : ℕ) : IsIso (untwist X L s F p U n) :=
  Stacks.Cohomology.Untwisting.isIso_hfunctor_map_sectionPowerAction X L s F n
    (nonvanishingPart X L s U) inf_le_right p

/-- **Multiplication by `sⁿ` as an isomorphism** `H^p(U ∩ X_s, ℱ) ≅ H^p(U ∩ X_s, ℱ ⊗ ℒ^{⊗ n})`.
Its inverse is the map written `s^{-n}` in [Stacks, Tag 09MR]. -/
def untwistIso (n : ℕ) :
    Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F ≅
      Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p (twist X L F (n : ℤ)) :=
  @asIso _ _ _ _ (untwist X L s F p U n) (isIso_untwist X L s F p U n)

/-- Restriction from `U` to `U ∩ X_s` on the cohomology of the `j`-th twist. -/
abbrev restrictTwist (j : ℤ) :
    Hgroup X.ringCatSheaf U p (twist X L F j) ⟶
      Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p (twist X L F j) :=
  Hrestrict X.ringCatSheaf (inf_le_left (a := U) (b := nonvanishingOpen L s)) p (twist X L F j)

/-- **The family `ξ ↦ s^{-n} ξ|_{U ∩ X_s}`, indexed by the exponent `n` of the denominator.**
It reads off the degree-`n` homogeneous component of a class of `H^p_*(U, ℒ, ℱ)`, restricts it to
`U ∩ X_s` and undoes the twist by `sⁿ` there. -/
def numeratorMap (n : ℕ) :
    twistedCohomologyModule X L F p U →+
      (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u) :=
  (ConcreteCategory.hom (untwistIso X L s F p U n).inv).comp
    ((ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))).comp
      (DFinsupp.evalAddMonoidHom (β := fun j : ℤ => gradedPiece X L F p U j) (n : ℤ)))

/-- The value of the family on a homogeneous class of degree `n`: restrict and untwist. -/
theorem numeratorMap_of (n : ℕ) (ξ : gradedPiece X L F p U (n : ℤ)) :
    numeratorMap X L s F p U n (DirectSum.of _ (n : ℤ) ξ) =
      (ConcreteCategory.hom (untwistIso X L s F p U n).inv)
        ((ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))) ξ) := by
  change (ConcreteCategory.hom (untwistIso X L s F p U n).inv)
    ((ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ)))
      ((DirectSum.of _ (n : ℤ) ξ) (n : ℤ))) = _
  rw [DirectSum.of_eq_same]

/-- **Multiplying by `s^k` and raising the exponent of the denominator by `k` is multiplying by
`s^{k + n}`.** -/
theorem sectionPowerAction_comp_actionOf_powerSectionValue (k n : ℕ) :
    sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
        (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n) ≫
      TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
        (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) =
      sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F ((k : ℤ) + (n : ℤ))
        (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s (k + n)) := by
  refine Eq.trans (SectionPower.sectionPowerAction_comp_actionOf (sectionSiteRing X)
    (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
    (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)) ?_
  refine SectionPower.sectionPowerAction_congr (sectionSiteRing X) (sectionSiteSheaf X) L F _ ?_
  rw [tensorPowerMulHom_apply, globalSectionHom_apply]
  exact (Stacks.Cohomology.PowerSection.powerSectionValue_add X L s k n).symm

/-- The untwisting isomorphisms compose: untwisting by `sⁿ` and then multiplying the twist by
`s^k` is untwisting by `s^{k + n}`. -/
theorem untwist_comp (k n : ℕ) :
    untwist X L s F p U n ≫ (Hfunctor X.ringCatSheaf (nonvanishingPart X L s U) p).map
      (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
        (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)) =
      untwist X L s F p U (k + n) :=
  ((Hfunctor X.ringCatSheaf (nonvanishingPart X L s U) p).map_comp _ _).symm.trans
    (congrArg (Hfunctor X.ringCatSheaf (nonvanishingPart X L s U) p).map
      (sectionPowerAction_comp_actionOf_powerSectionValue X L s F k n))

/-- **Multiplying numerator and denominator by `s^k` does not change the value of the family**,
on a homogeneous numerator. -/
theorem numeratorMap_smul_pow (k n : ℕ) (ξ : gradedPiece X L F p U (n : ℤ)) :
    numeratorMap X L s F p U (k + n)
        (homogeneousSection X L s ^ k •
          (DirectSum.of _ (n : ℤ) ξ : twistedCohomologyModule X L F p U)) =
      numeratorMap X L s F p U n (DirectSum.of _ (n : ℤ) ξ) := by
  have e1 : (homogeneousSection X L s ^ k •
        (DirectSum.of _ (n : ℤ) ξ : twistedCohomologyModule X L F p U)) =
      DirectSum.of _ ((k + n : ℕ) : ℤ)
        (act X L F p U (k : ℤ) (n : ℤ)
          (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ) := by
    rw [← Stacks.Cohomology.PowerSection.of_powerSectionValue]
    exact of_smul_of X L F p U k (n : ℤ)
      (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ
  rw [e1, numeratorMap_of, numeratorMap_of]
  have hcancel := inv_comp_eq_inv (untwistIso X L s F p U n) (untwistIso X L s F p U (k + n))
    ((Hfunctor X.ringCatSheaf (nonvanishingPart X L s U) p).map
      (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
        (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)))
    (untwist_comp X L s F p U k n)
    ((ConcreteCategory.hom (restrictTwist X L s F p U (n : ℤ))) ξ)
  refine Eq.trans (congrArg (ConcreteCategory.hom (untwistIso X L s F p U (k + n)).inv) ?_)
    hcancel
  have hnat := congrArg (fun g => (ConcreteCategory.hom g) ξ)
    ((HrestrictNT X.ringCatSheaf (inf_le_left (a := U) (b := nonvanishingOpen L s)) p).naturality
      (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
        (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)))
  simp only [ConcreteCategory.comp_apply] at hnat
  exact hnat

/-- **The family is compatible with multiplying numerator and denominator by `s`.** -/
theorem numeratorMap_compatible (n k : ℕ) (x : twistedCohomologyModule X L F p U)
    (hx : x ∈ grading X L F p U ((n * 1 : ℕ) : ℤ)) :
    numeratorMap X L s F p U (n + k) (homogeneousSection X L s ^ k • x) =
      numeratorMap X L s F p U n x := by
  rw [Nat.mul_one] at hx
  obtain ⟨ξ, rfl⟩ := hx
  rw [Nat.add_comm n k]
  exact numeratorMap_smul_pow X L s F p U k n ξ

/-- **The comparison map of [Stacks, Tag 09MR]**

`H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ∩ X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`.

It is the descent of the family `numeratorMap` to the degree-zero localization. -/
def canonicalMap :
    degreeZeroLocalization X L F p U (homogeneousSection X L s) →+
      (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u) :=
  degreeZeroLocalizationLiftOfDegree
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
    (homogeneousSection_mem X L s) (numeratorMap X L s F p U)
    (numeratorMap_compatible X L s F p U)

/-- **The comparison map sends `ξ / sⁿ` to `s^{-n} ξ`.** -/
theorem canonicalMap_fraction
    (z : degreeZeroLocalization X L F p U (homogeneousSection X L s)) (n : ℕ)
    (x : twistedCohomologyModule X L F p U)
    (hx : x ∈ grading X L F p U ((n * 1 : ℕ) : ℤ))
    (hz : (z : LocalizedModule.Away (homogeneousSection X L s)
        (twistedCohomologyModule X L F p U)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s)) x
        ⟨homogeneousSection X L s ^ n, by exact ⟨n, rfl⟩⟩) :
    canonicalMap X L s F p U z = numeratorMap X L s F p U n x :=
  degreeZeroLocalizationLiftOfDegree_fraction
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
    (homogeneousSection_mem X L s) (numeratorMap X L s F p U)
    (numeratorMap_compatible X L s F p U) z n x hx hz

/-! ### Bijectivity on an open contained in the nonvanishing open -/

section LeNonvanishing

/-- On an open inside `X_s` the intersection with `X_s` is the open itself. -/
theorem nonvanishingPart_eq_self (hU : U ≤ nonvanishingOpen L s) :
    nonvanishingPart X L s U = U := inf_eq_left.mpr hU

/-- On an open inside `X_s` the restriction entering the comparison map is an isomorphism. -/
theorem isIso_restrictTwist (hU : U ≤ nonvanishingOpen L s) (j : ℤ) :
    IsIso (restrictTwist X L s F p U j) :=
  isIso_hrestrict_of_eq X.ringCatSheaf _ (nonvanishingPart_eq_self X L s U hU) p _

/-- The restriction entering the comparison map, as an isomorphism, on an open inside `X_s`. -/
def restrictTwistIso (hU : U ≤ nonvanishingOpen L s) (j : ℤ) :
    Hgroup X.ringCatSheaf U p (twist X L F j) ≅
      Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p (twist X L F j) :=
  @asIso _ _ _ _ (restrictTwist X L s F p U j) (isIso_restrictTwist X L s F p U hU j)


/-- **No homogeneous numerator over an open inside `X_s` is killed by the comparison.** -/
theorem eq_zero_of_numeratorMap_eq_zero (hU : U ≤ nonvanishingOpen L s) (n : ℕ)
    (x : twistedCohomologyModule X L F p U)
    (hx : x ∈ grading X L F p U ((n * 1 : ℕ) : ℤ))
    (h0 : numeratorMap X L s F p U n x = 0) : x = 0 := by
  rw [Nat.mul_one] at hx
  obtain ⟨ξ, rfl⟩ := hx
  rw [numeratorMap_of] at h0
  rw [eq_zero_of_hom_apply_eq_zero (restrictTwistIso X L s F p U hU (n : ℤ)) ξ
    (eq_zero_of_hom_apply_eq_zero (untwistIso X L s F p U n).symm _ h0), map_zero]

/-- **Over an open inside `X_s` every class of `H^p(U ∩ X_s, ℱ)` is `s^{-1} ξ` for a class `ξ` of
`H^p(U, ℱ ⊗ ℒ)`.** -/
theorem exists_numeratorMap_one_eq (hU : U ≤ nonvanishingOpen L s)
    (y : (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u)) :
    ∃ x : twistedCohomologyModule X L F p U,
      ∃ _ : x ∈ grading X L F p U ((1 * 1 : ℕ) : ℤ),
        numeratorMap X L s F p U 1 x = y := by
  refine ⟨DirectSum.of _ ((1 : ℕ) : ℤ)
      ((ConcreteCategory.hom (restrictTwistIso X L s F p U hU ((1 : ℕ) : ℤ)).inv)
        ((ConcreteCategory.hom (untwistIso X L s F p U 1).hom) y)),
    by rw [Nat.mul_one]; exact ⟨_, rfl⟩, ?_⟩
  rw [numeratorMap_of]
  exact (congrArg (ConcreteCategory.hom (untwistIso X L s F p U 1).inv)
    (Iso.inv_hom_id_apply (restrictTwistIso X L s F p U hU ((1 : ℕ) : ℤ))
      ((ConcreteCategory.hom (untwistIso X L s F p U 1).hom) y))).trans
    (Iso.hom_inv_id_apply (untwistIso X L s F p U 1) y)

/-- **The comparison map is bijective on an open contained in the nonvanishing open of `s`.** Let
`X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ`, `ℱ` an arbitrary
`𝒪_X`-module, `p` a cohomological degree and `U ⊆ X_s` an open contained in the nonvanishing
locus of `s`. Then the canonical map

`H^p_*(U, ℒ, ℱ)₍s₎ ⟶ H^p(U ∩ X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

of `Stacks.Cohomology.TwistedLocalizationMap.canonicalMap` is **bijective**.

Neither quasi-compactness nor quasi-separatedness of `U`, nor quasi-coherence of `ℱ`, nor
positivity of `p` is assumed, and this is **not** a both-sides-vanish statement: taking
`U = X_s` it reads `H^p_*(X_s, ℒ, ℱ)₍s₎ ≅ H^p(X_s, ℱ)` on an arbitrary scheme, with neither side
forced to be zero. -/
@[stacks 09MR "for an open U inside the nonvanishing locus X_s: the canonical map \
H^p_*(U,L,F)_(s) to H^p(U ∩ X_s,F), xi/s^n to s^(-n) xi, is bijective, on an arbitrary scheme, \
for an arbitrary module and in every degree. The quasi-compact quasi-separated case of the tag \
is bijective_canonicalMap_of_isCompact, and neither case subsumes the other."]
theorem bijective_canonicalMap_of_le_nonvanishingOpen (hU : U ≤ nonvanishingOpen L s) :
    Function.Bijective (canonicalMap X L s F p U) :=
  bijective_degreeZeroLocalizationLiftOfDegree
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
    (homogeneousSection_mem X L s) (numeratorMap X L s F p U)
    (numeratorMap_compatible X L s F p U)
    (exists_numeratorMap_one_eq X L s F p U hU)
    (eq_zero_of_numeratorMap_eq_zero X L s F p U hU)

end LeNonvanishing

end Stacks.Cohomology.TwistedLocalizationMap

end
