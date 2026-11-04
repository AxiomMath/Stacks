module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit

/-!
# The derived pullback along a morphism of ringed topoi is exact

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi. The total left derived
pullback `Lf^* : D(𝒪_D) ⟶ D(𝒪_C)` of [Stacks, Tag 06YY] commutes with the shift; this file
proves the remaining exactness assertion of that tag: `Lf^*` is a triangulated functor. It also
computes `Lf^*` on the structure sheaf placed in degree zero, `Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`.

Both are read off the class of K-flat complexes with flat terms, on which `Lf^*` is computed by
the degreewise pullback. That class is stable under mapping cones, so every morphism of
`D(𝒪_D)` is, up to isomorphism, the image of a morphism between such complexes whose mapping
cone is again such a complex, and the degreewise pullback, being an additive functor of
complexes, carries mapping-cone triangles to distinguished triangles. The structure sheaf
placed in degree zero is K-flat with flat terms, and its pullback is the structure sheaf by the
corepresentability argument of [Stacks, Tag 03D6].

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison_commShift`: the
  canonical comparison `Lf^* ⟶ f^*` is compatible with the shift.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated`: **the exactness
  assertion of [Stacks, Tag 06YY]** for a morphism of ringed topoi.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIso`: `Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`.

## Implementation notes

The argument is the one recorded for a morphism of ringed topoi presented by a functor of sites,
`Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated`, with the computation
of `Lf^*` on K-flat complexes with flat terms taken from
`DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat`, which holds
for every morphism of ringed topoi. The stability of the class under mapping cones,
`Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone`, is a statement about the target
alone and is reused.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- The canonical comparison `Lf^* ⟶ f^*` of [Stacks, Tag 06YY] is compatible with the
commutation of `Lf^*` with the shift. -/
instance derivedPullbackComparison_commShift :
    NatTrans.CommShift (derivedPullbackComparison f) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (derivedPullback f)
    (derivedPullbackComparison f) (quasiIsoTarget (Y := Y)) ℤ

/-- **[Stacks, Tag 06YY], exactness, for a morphism of ringed topoi.** The derived pullback
`Lf^* : D(𝒪_D) ⟶ D(𝒪_C)` is a triangulated functor. Every morphism of `D(𝒪_D)` is, up to
isomorphism, the image of a morphism between K-flat complexes with flat terms; its mapping cone
is again such a complex, and on such complexes `Lf^*` is computed by the degreewise pullback,
which carries the mapping-cone triangle to a distinguished triangle. -/
@[stacks 06YY "exactness of the derived pullback, for a morphism of ringed topoi whose geometric
datum is a morphism of the underlying topoi"]
theorem derivedPullback_isTriangulated :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).IsTriangulated := by
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)
  let P : ObjectProperty (HomotopyCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
    IsKFlat (Y := Y)
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, hK, s, hs⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y) M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
  apply Functor.isTriangulated_of_rightExtension (derivedPullback f)
    (derivedPullbackComparison f)
  intro K L g
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  refine ⟨CochainComplex.mappingCone.triangleh (P.ι.map a.hom).out,
    HomotopyCategory.mappingCone_triangleh_distinguished _, ?_, ?_, ?_, ?_⟩
  · exact DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
      f _ a.left.property
  · exact DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
      f _ a.right.property
  · exact DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
      f _ (Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone (P.ι.map a.hom).out
        a.left.property a.right.property)
  · exact ⟨eqToIso (congrArg (fun m => Arrow.mk (DerivedCategory.Qh.map m))
      (HomotopyCategory.quotient_map_out (P.ι.map a.hom))) ≪≫ ea⟩

/-- **The derived pullback of the structure sheaf placed in degree zero is the structure sheaf
placed in degree zero**, `Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]`, for a morphism of ringed topoi.

The complex `𝒪_D[0]` is K-flat with flat terms, so `Lf^*` is computed on it by the degreewise
pullback ([Stacks, Tag 06YY]); the degreewise pullback of a complex concentrated in degree zero
is the pullback of its module placed in degree zero; and the pullback of the structure sheaf is
the structure sheaf, `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`. -/
def derivedPullbackUnitIso :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  have := DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
    f _ (Stacks.Cohomology.LerayOfToposHom.isKFlat_single_unit Y)
  (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≪≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm.app _) ≪≫
    asIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex f.toModulesHom.pullbackModules
          (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).symm)) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
