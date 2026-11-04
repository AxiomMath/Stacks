module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base-change comparison of a derived internal hom along a flat morphism

Let `h : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a flat morphism of ringed spaces, `E` a pseudo-coherent
object of `D(𝒪_X)` and `G` a complex of `𝒪_X`-modules whose class is locally bounded below. Then
the base-change comparison

`Lh^*R𝓗om(E, G) ⟶ R𝓗om(Lh^*E, h^*G)`

(`Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison` at the comparison
`Lh^*G ⟶ h^*G` of the derived with the degreewise pullback) is an isomorphism: its first factor is
the map of Stacks 08I3, invertible by Stacks 0GM7 (2), and its second factor is `R𝓗om(Lh^*E, -)`
of the comparison `Lh^*G ⟶ h^*G`, invertible because the degreewise pullback along a flat
morphism is exact.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeComparison.isIso_derivedPullbackNatTrans_app_of_isFlat`
* `Stacks.Cohomology.DerivedBaseChangeComparison.isIso_baseChangeSheafHomComparison_of_isFlat`

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)

namespace Stacks.Cohomology.DerivedBaseChangeComparison

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X)

/-- Along a flat morphism of ringed spaces the comparison `Lh^*(QG) ⟶ Q(h^*G)` of the derived
with the degreewise pullback is invertible, at every complex `G`. -/
theorem isIso_derivedPullbackNatTrans_app_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso ((derivedPullbackNatTrans h).app G) := by
  have hc := Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackComparison_app_of_isFlat
    h hh ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)
  dsimp only [derivedPullbackNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **The base-change comparison of a derived internal hom along a flat morphism.** For `h` flat,
`E` pseudo-coherent and `G` with locally bounded below class, the comparison
`Lh^*R𝓗om(E, QG) ⟶ R𝓗om(Lh^*E, Q(h^*G))` is an isomorphism. -/
@[sga "6 I 3.7" "Clause a), special case"]
theorem isIso_baseChangeSheafHomComparison_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    (E : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E)
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hG : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X (DerivedCategory.Q.obj G)) :
    IsIso (baseChangeSheafHomComparison h E (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj ((pullbackComplex h).obj G)) ((derivedPullbackNatTrans h).app G)) := by
  have h₁ := DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
    h hh E hE (DerivedCategory.Q.obj G) hG
  have h₂ := isIso_derivedPullbackNatTrans_app_of_isFlat h hh G
  dsimp only [baseChangeSheafHomComparison]
  infer_instance

end Stacks.Cohomology.DerivedBaseChangeComparison

end
