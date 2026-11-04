module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoheratorQCQS
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceQuasiCoherentCriterion
public import
  StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PseudoCoherentPushforwardLocallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafy trace of a proper morphism of Noetherian schemes is an isomorphism

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]), `L ∈ D^-_Coh(𝒪_X)` and
`K ∈ D^+_QCoh(𝒪_Y)`. The sheafy trace map of [Stacks, Tag 0B6H]

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

is an isomorphism ([Stacks, Tag 0GEW]). The proof is the source's: `L` is pseudo-coherent
([Stacks, Tag 08E8]), so is `Rf_*L` (`Rf_*` of a proper morphism preserves pseudo-coherence,
from [Stacks, Tag 08E2] and the bound of [Stacks, Tag 08D5]), `a(K)` is bounded below
([Stacks, Tag 0A9I]), and clause (2) of [Stacks, Tag 0GEV] applies, its input
[Stacks, Tag 0A9Q] being `Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs`.

Everything is stated at the standard model, with the tensor–internal-Hom adjunctions of
[Stacks, Tag 08J8] and the adjunction `Rf_* ⊣ a` at which [Stacks, Tag 0A9Q] is proved.

## Main results

* `Stacks.Duality.isPseudoCoherent_derivedPushforward_standard_of_isProper`: `Rf_*` of a proper
  morphism preserves pseudo-coherence, at the standard model.
* `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_standard`: [Stacks, Tag 0A9I] at the
  standard model.
* `Stacks.Duality.isIso_sheafyTrace_of_isProper_of_adjunction`: the same for any right adjoint
  of `Rf_*`.
* `Stacks.Duality.isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus`: **[Stacks, Tag 0GEW]**.

## References

* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace Stacks.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Rf_*` of a proper morphism preserves pseudo-coherence**, at the standard model. -/
theorem isPseudoCoherent_derivedPushforward_standard_of_isProper [IsNoetherian Y] [IsProper f]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) ((derivedPushforward f).obj E) :=
  AlgebraicGeometry.ProperSupportCoherent.isPseudoCoherent_derivedPushforwardModules_of_isProper
    f E hE

/-- **[Stacks, Tag 0A9I] at the standard model**: the right adjoint `a` of `Rf_*` carries a
bounded below object of `D_QCoh(𝒪_Y)` to a bounded below object. -/
theorem isBoundedBelow_twistedInverseImage_obj_standard [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow
      ((twistedInverseImage f (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj
        K).obj := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel.{u + 1} f
  obtain ⟨n₀, hn₀⟩ := hK
  have := isGE_rightAdjoint_obj f _
    (twistedInverseImageAdjunction f (StandardModel.isQuasicoherent_homology_derivedPushforward f))
    N hN K n₀ ((DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn₀ i hi)
  exact ⟨n₀ - N, fun n hn ↦ DerivedCategory.isZero_of_isGE _ (n₀ - N) n hn⟩

section Adjunction

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f
    (StandardModel.isQuasicoherent_homology_derivedPushforward f) ⊣ a)

include adj in
/-- [Stacks, Tag 0A9I] for any right adjoint `a` of `Rf_*` at the standard model. -/
theorem isBoundedBelow_rightAdjoint_obj_of_adjunction (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow (a.obj K).obj :=
  DerivedCategoryB.isBoundedBelow_of_iso ((ObjectProperty.ι _).mapIso
      (((twistedInverseImageAdjunction f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)).rightAdjointUniq adj).app K))
    (isBoundedBelow_twistedInverseImage_obj_standard f K hK)

/-- [Stacks, Tag 0A9Q] for any right adjoint `a` of `Rf_*` at the standard model. -/
theorem isIso_coherator_map_sheafyTrace_of_adjunction (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso ((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.rightAdjoint.map
      (sheafyTrace f
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
        (StandardModel.isQuasicoherent_homology_derivedPushforward f) adj L K)) :=
  isIso_coherator_map_of_bijective _ (Adjunction.ofIsLeftAdjoint _) _
    (bijective_comp_sheafyTrace_of_qcqs f _ adj _ _ L K)

/-- **[Stacks, Tag 0GEW] for any right adjoint of `Rf_*`.** Let `f : X ⟶ Y` be a proper morphism
of Noetherian schemes, `a` a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`,
`L ∈ D^-_Coh(𝒪_X)` and `K ∈ D^+_QCoh(𝒪_Y)`. Then the map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)` of [Stacks, Tag 0B6H] is an isomorphism. -/
theorem isIso_sheafyTrace_of_isProper_of_adjunction [IsProper f] [IsNoetherian X]
    [IsNoetherian Y] (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (hL : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent) L.obj)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (sheafyTrace f
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
      (StandardModel.isQuasicoherent_homology_derivedPushforward f) adj L K) := by
  have hLp := isPseudoCoherent_of_derivedCategoryBMinus_isCoherent L hL
  exact isIso_sheafyTrace_of_isPseudoCoherent f _ _ _ adj (Adjunction.ofIsLeftAdjoint _) L K
    (isBoundedBelow_rightAdjoint_obj_of_adjunction f adj K)
    (isIso_coherator_map_sheafyTrace_of_adjunction f adj L K) hK hLp
    (isPseudoCoherent_derivedPushforward_standard_of_isProper f L.obj hLp)

end Adjunction

/-- **Stacks Project, Tag 0GEW.** Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let
`L ∈ D^-_Coh(𝒪_X)` and `K ∈ D^+_QCoh(𝒪_Y)`. Then the map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)` of [Stacks, Tag 0B6H], for `a` the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, is an isomorphism. -/
@[stacks 0GEW]
theorem isIso_sheafyTrace_of_isProper_of_derivedCategoryBMinus [IsProper f] [IsNoetherian X]
    [IsNoetherian Y] (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (hL : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent) L.obj)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso (sheafyTrace f
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
      (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
      (StandardModel.isQuasicoherent_homology_derivedPushforward f)
      (twistedInverseImageAdjunction f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K) :=
  isIso_sheafyTrace_of_isProper_of_adjunction f _ L K hL hK

end Stacks.Duality

end
