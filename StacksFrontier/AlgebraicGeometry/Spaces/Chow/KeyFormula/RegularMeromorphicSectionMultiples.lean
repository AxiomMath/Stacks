module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRatio

/-!
# Every meromorphic section is a multiple of a regular one

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `ℒ` be an
invertible `𝒪_X`-module.  The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ makes the global
meromorphic sections of `ℒ` a free module of rank one over the field `Γ(X, 𝒦_X) = R(X)` of
global meromorphic functions.  This file records the consequence that the section-generic
reading of Section 0EQU needs: **every** meromorphic section `s` of `ℒ`, regular or not, is
`a · s₀` for a unique global meromorphic function `a`, as soon as `s₀` is regular.

`AlgebraicGeometry.Space.existsUnique_units_smul_eq_of_isRegularMeromorphicSection` is the case
of a regular `s`, where `a` is moreover a unit; the argument here is the same, without the
regularity of `s`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_smul_eq_of_isRegularMeromorphicSection`: every
  meromorphic section of `ℒ` is a unique global meromorphic multiple of a given regular one.

## References

* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **Every meromorphic section of an invertible module is a unique global meromorphic multiple
of a regular one.**  The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ writes `s` and the regular
section `s₀` as multiples `a · t`, `b · t` of one section `t`; `b` is nonzero because `s₀` is,
hence a unit of the field of global meromorphic functions, and `s = (a b⁻¹) · s₀`.  Uniqueness
is the injectivity of multiplication by the regular section `s₀`. -/
theorem existsUnique_smul_eq_of_isRegularMeromorphicSection
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s₀ : MeromorphicSection.{u, u} B S hS X hX L)
    (hs₀ : IsRegularMeromorphicSection.{u, u} B S hS X hX L s₀)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    ∃! a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
      s = a • s₀ := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hmono := IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
    ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩
  obtain ⟨e⟩ := nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints B S hS hX
    hwa hfin hmono L hL
  have hfieldK := isField_globalMeromorphicFunctions B S hS hX hInt hN
  have hrep : ∀ x : MeromorphicSection.{u, u} B S hS X hX L, ∃ a : ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
      x = a • SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS X hX) := fun x => by
    obtain ⟨a, ha, -⟩ := existsUnique_smul_meromorphicUnitSection B S hS hX
      (SheafOfModules.sectionsMap e.inv x)
    have hround : SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv x) = x :=
      Subtype.ext (funext fun V =>
        congrArg (fun φ : meromorphicSectionSheaf.{u, u} B S hS X hX L ⟶
          meromorphicSectionSheaf.{u, u} B S hS X hX L =>
            PresheafOfModules.Hom.app φ.val V (x.eval V)) e.inv_hom_id)
    exact ⟨a, hround.symm.trans ((congrArg (SheafOfModules.sectionsMap e.hom) ha).symm.trans
      (((Stacks.Cohomology.SiteModules.globalSectionsFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O)).map e.hom).hom.map_smul a _))⟩
  obtain ⟨a, hsa⟩ := hrep s
  obtain ⟨b, hsb⟩ := hrep s₀
  have hb0 : b ≠ 0 := fun h => ne_zero_of_isRegularMeromorphicSection B S hS hX hInt hN L s₀ hs₀
    (by rw [hsb, h, zero_smul])
  obtain ⟨z, hz⟩ := hfieldK.mul_inv_cancel hb0
  have hcancel : ∀ c c' : ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
      c • s₀ = c' • s₀ → c = c' :=
    fun c c' hc =>
      Subtype.ext (funext fun W => hs₀ W.unop (congrFun (congrArg Subtype.val hc) W))
  have hmain : s = (a * z) • s₀ := by
    rw [hsa, hsb, smul_smul, mul_assoc, hfieldK.mul_comm z b, hz, mul_one]
  exact ⟨a * z, hmain, fun c hc => hcancel _ _ (hc.symm.trans hmain)⟩

end AlgebraicGeometry.Space

end
