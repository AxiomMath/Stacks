module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTraceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportDerivedPushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# The trace map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` for a proper morphism

Let `f : X ⟶ Y` be a proper morphism of Noetherian algebraic spaces, `L` in `D^-_Coh(𝒪_X)` and
`K` in `D^+_QCoh(𝒪_Y)`. Then the map of Stacks 0E57 is an isomorphism (Stacks 0GG5): `L` and
`Rf_*L` are pseudo-coherent by Stacks 08IK, since `Rf_*` carries `D^-_Coh(𝒪_X)` into
`D^-_Coh(𝒪_Y)`, and Stacks 0GG4 (2) applies.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryBMinus_derivedModulePushforward`: `Rf_*` carries
  `D^-_Coh(𝒪_X)` into `D^-_Coh(𝒪_Y)` for `f` proper and `Y` Noetherian.
* `AlgebraicGeometry.Space.isIso_smallEtalePushforwardTrace_of_isProper`: **Stacks 0GG5**.

## References

* [Stacks Project, Tag 0GG5](https://stacks.math.columbia.edu/tag/0GG5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)

/-- **`Rf_*` carries `D^-_Coh(𝒪_X)` into `D^-_Coh(𝒪_Y)`** for a proper morphism `f` to a
Noetherian algebraic space: the cohomology of `Rf_*E` in degree `i` is that of `Rf_*τ_{≥ m}E`
for `m ≪ i` by the uniform bound of Stacks 08FA, and `τ_{≥ m}E` is in `D^b_Coh(𝒪_X)`. -/
theorem derivedCategoryBMinus_derivedModulePushforward (hf : IsProper B S hS f.hom)
    (hY : IsNoetherian B S hS hZ Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS X.1 X.2) E) :
    DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj E) := by
  have hft : IsLocallyOfFiniteType B S hS f.hom := hf.2.1.1
  have hEq : QcohDerived B S hS X E := fun i => (hE.2 i).toIsQuasicoherentOnSite
  have hBX := WeakSerre.isWeakSerre_of_isWeakSerreClass (isCoherent.{u, u} B S hS X.1 X.2)
  have hQX := WeakSerre.isWeakSerre_of_isWeakSerreClass
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
  obtain ⟨N, hN⟩ := exists_isLE_derivedModulePushforward_obj f hf.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hf.1) hY.1
  obtain ⟨b, hb⟩ := hE.1
  have hEb : E.IsLE b := (DerivedCategory.isLE_iff E b).2 fun i hi => hb i hi
  refine ⟨⟨b + N, fun i hi => ?_⟩, fun i => ?_⟩
  · have := hN E hEq b hEb
    exact DerivedCategory.isZero_of_isLE _ (b + N) i hi
  · let m := i - N
    let T := (DerivedCategory.TStructure.t.triangleLTGE m).obj E
    have hT' := (derivedModulePushforward B S hS f).map_distinguished T
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished m E)
    have hlt : QcohDerived B S hS X ((DerivedCategory.TStructure.t.truncLT m).obj E) :=
      DerivedCategoryB.derivedCategoryB_truncLT_obj _ hQX m E hEq
    have hltLE : ((DerivedCategory.TStructure.t.truncLT m).obj E).IsLE (m - 1) :=
      DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _ (by omega)
    have h₁ : ((derivedModulePushforward B S hS f).mapTriangle.obj T).obj₁.IsLE (m - 1 + N) :=
      hN _ hlt (m - 1) hltLE
    have hiso := DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _ hT' i (m - 1 + N) h₁
      (by omega)
    have hge : DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2)
        ((DerivedCategory.TStructure.t.truncGE m).obj E) := by
      refine ⟨⟨⟨m, fun j hj => DerivedCategory.isZero_of_isGE _ m j hj⟩, ⟨b, fun j hj => ?_⟩⟩,
        DerivedCategoryB.derivedCategoryB_truncGE_obj _ hBX m E hE.2⟩
      by_cases hjm : m ≤ j
      · exact (hb j hj).of_iso
          ((DerivedCategory.truncGECompHomologyFunctorIso m j hjm).app E).symm
      · exact DerivedCategory.isZero_of_isGE _ m j (by omega)
    have hcoh := derivedCategoryBBounded_derivedModulePushforward B S hS hZ f hft hY _ hge
      (fun j => by
        have := (hge.2 j).toIsCoherentOnSite
        have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X
          ((DerivedCategory.homologyFunctor _ j).obj
            ((DerivedCategory.TStructure.t.truncGE m).obj E))
        have hF := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2
          ((DerivedCategory.homologyFunctor _ j).obj
            ((DerivedCategory.TStructure.t.truncGE m).obj E))
        exact ⟨hF, isProperOver_of_isProper B S hS X.2 Y.2 f.hom hft hf _ hF⟩)
    exact (isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        ((derivedModulePushforward B S hS f).mapTriangle.obj T).mor₂)).symm (hcoh.2 i)

/-- **Stacks 0GG5.** Let `f : X ⟶ Y` be a proper morphism of Noetherian algebraic spaces over
`S`, `L` in `D^-_Coh(𝒪_X)` and `K` in `D^+_QCoh(𝒪_Y)`. Then the map
`Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of Stacks 0E57 is an isomorphism. -/
@[stacks 0GG5]
theorem isIso_smallEtalePushforwardTrace_of_isProper (hf : IsProper B S hS f.hom)
    (hX : IsNoetherian B S hS hZ X.1) (hY : IsNoetherian B S hS hZ Y.1)
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hL : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS X.1 X.2) L)
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K) :
    IsIso (smallEtalePushforwardTrace hZ f hX.1 hX.2.1 hY.2.1
      ⟨L, fun i => (hL.2 i).toIsQuasicoherentOnSite⟩ ⟨K, hK.2⟩) := by
  have hfL := derivedCategoryBMinus_derivedModulePushforward hZ f hf hY L hL
  refine isIso_smallEtalePushforwardTrace_of_isPseudoCoherent hZ f hX.1 hX.2.1 hY.2.1 _ _ hY.1
    hK.1 ?_ ?_
  · exact (isPseudoCoherent_iff_isCoherent_homology hZ X hX
      ⟨L, fun i => (hL.2 i).toIsQuasicoherentOnSite⟩).2 ⟨hL.1, hL.2⟩
  · exact (isPseudoCoherent_iff_isCoherent_homology hZ Y hY
      ⟨_, fun i => (hfL.2 i).toIsQuasicoherentOnSite⟩).2 ⟨hfL.1, hfL.2⟩

end AlgebraicGeometry.Space

end
