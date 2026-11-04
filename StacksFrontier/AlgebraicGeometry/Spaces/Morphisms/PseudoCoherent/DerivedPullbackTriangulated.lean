module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi

/-!
# The derived pullback along a morphism of algebraic spaces is exact

For a morphism `f : X ⟶ Y` of algebraic spaces, the derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` of Stacks 06YY on the small étale ringed topoi is a triangulated
functor.

## Main results

* `AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedModulePullback`: `Lf^*` is
  triangulated.

## Implementation notes

The argument is the one of
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated`, which is stated for
ringed topoi whose object, morphism and structure-ring universes agree, whereas the small étale
ringed topos of an algebraic space has its objects one universe higher.  Every morphism of
`D(𝒪_Y)` is, up to isomorphism, the image of a morphism between K-flat complexes with flat
terms, whose mapping cone is again such a complex; on such complexes `Lf^*` is computed by the
degreewise pullback, which carries the mapping-cone triangle to a distinguished triangle.  The
inputs — K-flat resolutions (Stacks 06YS), the computation on K-flat complexes (Stacks 06YY) and
the stability of the class under mapping cones — hold at the universes of the small étale ringed
topoi.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
  (isIso_derivedPullbackComparison_app_isKFlat)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian structure of the modules on the small étale site of an algebraic space, with its
universes given.  It is the instance that instance search finds on its own; naming it lets it be
supplied where the universe of the morphisms of the module category would otherwise be left as an
unsolved maximum. -/
abbrev abelian_ringedToposStructureRingSheafModules (X : AlgebraicSpaces B S hS) :
    Abelian (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  SheafOfModules.instAbelian.{u, u, u, u + 1} (ringedToposStructureRingSheaf B S hS X)

attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules


/-- The derived pullback along a morphism of algebraic spaces commutes with the shift. -/
instance commShift_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (smallEtaleDerivedModulePullback B S hS f).CommShift ℤ :=
  derivedPullback_commShift (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- **Stacks 06YY, exactness, for a morphism of algebraic spaces.** The derived pullback along
the morphism of small étale ringed topoi of a morphism of algebraic spaces is triangulated. -/
instance isTriangulated_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (smallEtaleDerivedModulePullback B S hS f).IsTriangulated := by
  let W := smallEtaleModuleQuasiIso B S hS Y
  let P : ObjectProperty (HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, hK, s, hs⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
          (Y := smallEtaleRingedTopos B S hS Y) M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
  have := Functor.IsLeftDerivedFunctor.natTrans_commShift
    (smallEtaleDerivedModulePullback B S hS f) (smallEtaleDerivedModulePullbackComparison B S hS f)
    (smallEtaleModuleQuasiIso B S hS Y) ℤ
  apply Functor.isTriangulated_of_rightExtension (smallEtaleDerivedModulePullback B S hS f)
    (smallEtaleDerivedModulePullbackComparison B S hS f)
  intro K L g
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  refine ⟨CochainComplex.mappingCone.triangleh (P.ι.map a.hom).out,
    HomotopyCategory.mappingCone_triangleh_distinguished _, ?_, ?_, ?_, ?_⟩
  · exact isIso_derivedPullbackComparison_app_isKFlat
      (smallEtaleRingedToposHom B S hS f) _ a.left.property
  · exact isIso_derivedPullbackComparison_app_isKFlat
      (smallEtaleRingedToposHom B S hS f) _ a.right.property
  · exact isIso_derivedPullbackComparison_app_isKFlat
      (smallEtaleRingedToposHom B S hS f) _
      (Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone (P.ι.map a.hom).out
        a.left.property a.right.property)
  · exact ⟨eqToIso (congrArg (fun m => Arrow.mk (DerivedCategory.Qh.map m))
      (HomotopyCategory.quotient_map_out (P.ι.map a.hom))) ≪≫ ea⟩

/-- The derived pullback along a morphism of algebraic spaces is additive, being triangulated. -/
instance additive_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleDerivedModulePullback B S hS f).Additive := by
  have := isTriangulated_smallEtaleDerivedModulePullback B S hS f
  infer_instance

/-- The derived pullback along a morphism of algebraic spaces preserves zero morphisms. -/
instance preservesZeroMorphisms_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (smallEtaleDerivedModulePullback B S hS f).PreservesZeroMorphisms := by
  have := additive_smallEtaleDerivedModulePullback B S hS f
  infer_instance

end AlgebraicGeometry.Space

end
