module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHomTriangulated

/-!
# The derived pullback along a morphism of ringed topoi is exact, at free universes

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi. The total left derived
pullback `Lf^* : D(𝒪_D) ⟶ D(𝒪_C)` of [Stacks, Tag 06YY] is a triangulated functor. This is
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated` with the six
universes of the two ringed topoi free and unrelated, so that it applies to a ringed topos whose
site has its objects one universe above its morphisms, such as a chosen big site of schemes.

The argument is the same: `Lf^*` is computed by the degreewise pullback on K-flat complexes with
flat terms (`DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat`),
that class resolves every complex ([Stacks, Tag 06YS]) and is stable under mapping cones, and the
degreewise pullback carries mapping-cone triangles to distinguished triangles.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.isTriangulated_derivedPullback`: the exactness
  assertion of [Stacks, Tag 06YY] for a morphism of ringed topoi at free universes.

## Implementation notes

The two module-category abelian instances stated at an ambient universe are switched off, as
they are in the free-universe statement of [Stacks, Tag 07A6] this accompanies: at a site whose
objects lie above its sections they leave instance search with a stuck universe constraint.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe v u w v' u' w'

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  (f : RingedToposHom X Y)

/-- **[Stacks, Tag 06YY], exactness, for a morphism of ringed topoi at free universes.** The
derived pullback carries distinguished triangles to distinguished triangles: every morphism of
`D(𝒪_D)` is, up to isomorphism, the image of a morphism between K-flat complexes with flat
terms, whose mapping cone is again such a complex, and on such complexes `Lf^*` is computed by
the degreewise pullback. -/
theorem isTriangulated_derivedPullback :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f
    (derivedPullback f).IsTriangulated := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f
  have : NatTrans.CommShift (derivedPullbackComparison f) ℤ :=
    Functor.IsLeftDerivedFunctor.natTrans_commShift (derivedPullback f)
      (derivedPullbackComparison f) (quasiIsoTarget (Y := Y)) ℤ
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)
  let P : ObjectProperty (HomotopyCategory
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
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

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
