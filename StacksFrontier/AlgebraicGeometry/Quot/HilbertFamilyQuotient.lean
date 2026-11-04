module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealChartFiniteType

/-!
# The quotient of the structure sheaf determined by a Hilbert family

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`T` be a scheme of the site over `Y`.  A family classified by the Hilbert functor of Stacks 0CZY
is a closed subspace `Z ⊆ X_T` which is of finite presentation, flat and proper over `T`, and
Stacks 0D00 identifies it with the quotient `𝒪_{X_T} ⟶ i_*𝒪_Z` of the structure sheaf of `X_T`
determined by its inclusion `i`.  For that identification the three defining conditions on
`Z ⟶ T` have to be matched with the three conditions on the module `i_*𝒪_Z` that the Quot
functor of Stacks 09TR imposes.

This file carries out the match for the first of the three: the module `i_*𝒪_Z` of a Hilbert
family is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_schemeBaseChangeProjection`: the projection
  `X_T ⟶ T` of a base change of a morphism of finite presentation is of finite presentation.
* `isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily_unconditional`:
  **the quotient of the structure sheaf determined by a Hilbert family is a module of finite
  presentation.**

## Implementation notes

The ambient space is the base change `X_T`, which is
`AlgebraicGeometry.Space.schemeBaseChangeSpace`, and the closed subspace is the field `Z` of
the family together with its closedness, read as an element of
`AlgebraicGeometry.Space.ClosedSubspaces`.  Finite presentation of the projection `X_T ⟶ T` is
Stacks 03XR, the stability of finite presentation under base change, applied to the cartesian
square `CategoryTheory.IsPullback.of_hasPullback` read in the category of algebraic spaces
through the faithful inclusion of the full subcategory.

**Nothing is carried by the unconditional form.**  Stacks 084Q's own input is passed through as
the hypothesis `hchart` by
`AlgebraicGeometry.Space.isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily`;
it is now a theorem for the inclusion of a closed subspace,
`AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_fg_ideal_ker_rep_snd` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealChartFiniteType.lean`, so
`isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily_unconditional`
supplies it and takes no such hypothesis.

No tag attribute is placed.  This is one of the dictionary entries that the proof of
Stacks 0D00 runs through, not a clause of Stacks 0D00 itself: the tag belongs on the
identification of the two functors.

## References

* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The projection of a base change of a morphism of finite presentation is of finite
presentation.**  For `f : X ⟶ Y` of finite presentation and a scheme `T` of the site over `Y`,
the projection `X_T ⟶ T` is of finite presentation.

This is Stacks 03XR applied to the cartesian square exhibiting `X_T` as the base change of `X`
along `T ⟶ Y`, read in the category of algebraic spaces over `S` through the faithful inclusion
of the full subcategory. -/
theorem isFinitePresentation_schemeBaseChangeProjection (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y) :
    IsFinitePresentation B S hS (pullback.snd f.hom T.hom) := by
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom T.hom) : schemeBaseChangeSpace f T ⟶ X)
      (ObjectProperty.homMk (pullback.snd f.hom T.hom) :
        schemeBaseChangeSpace f T ⟶ schemeOverSpace T)
      f (ObjectProperty.homMk T.hom : schemeOverSpace T ⟶ Y) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (IsPullback.of_hasPullback f.hom T.hom)
  have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
  simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {F G : AlgebraicSpaces B S hS} (k : F ⟶ G) => IsFinitePresentation B S hS k.hom)
    hsq (by simpa using hf)

/-- **The quotient of the structure sheaf determined by a family classified by the Hilbert
functor is a module of finite presentation.**  Let `f : X ⟶ Y` be of finite presentation, let `T`
be a scheme of the site over `Y` and let `z` be a family classified by the Hilbert functor of
`f` over `T`, that is, a closed subspace `Z ⊆ X_T` of finite presentation, flat and proper over
`T`.  Then the `𝒪_{X_T}`-module `i_*𝒪_Z` is of finite presentation.

This is the finite-presentation entry of the dictionary of Stacks 0D00.  The family's own
hypothesis is finite presentation of `Z ⟶ T`; finite presentation of the projection `X_T ⟶ T` is
`AlgebraicGeometry.Space.isFinitePresentation_schemeBaseChangeProjection`, and the two together
give the conclusion by `AlgebraicGeometry.Space`'s
`isFinitePresentationOnSite_pushforwardStructureSheaf_of_isFinitePresentation`.
Flatness and properness of `Z ⟶ T` are not used.

Stacks 084Q's own chart input, which
`AlgebraicGeometry.Space.isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily`
takes as the hypothesis `hchart`, is supplied here from
`AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_fg_ideal_ker_rep_snd`. -/
theorem isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily_unconditional
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y)
    (z : HilbertFamily f T) :
    (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T)
      ⟨z.Z, z.closed⟩).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_pushforwardStructureSheaf_of_isFinitePresentation B S hS
    (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩
    (ObjectProperty.homMk (pullback.snd f.hom T.hom) :
      schemeBaseChangeSpace f T ⟶ schemeOverSpace T)
    (isFinitePresentation_schemeBaseChangeProjection f hf T)
    (isFiniteTypeOnSite_kernelIdealSheaf_iff_fg_ideal_ker_rep_snd B S hS
      (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩)
    z.finitePresentation

/-- **The quotient of the structure sheaf determined by a family classified by the Hilbert
functor is a module of finite presentation.**  Let `f : X ⟶ Y` be of finite presentation, let `T`
be a scheme of the site over `Y` and let `z` be a family classified by the Hilbert functor of
`f` over `T`, that is, a closed subspace `Z ⊆ X_T` of finite presentation, flat and proper over
`T`.  Then the `𝒪_{X_T}`-module `i_*𝒪_Z` is of finite presentation.

This is the finite-presentation entry of the dictionary of Stacks 0D00.  The family's own
hypothesis is finite presentation of `Z ⟶ T`; finite presentation of the projection `X_T ⟶ T` is
`AlgebraicGeometry.Space.isFinitePresentation_schemeBaseChangeProjection`, and the two together
give the conclusion by `AlgebraicGeometry.Space`'s
`isFinitePresentationOnSite_pushforwardStructureSheaf_of_isFinitePresentation`.
Flatness and properness of `Z ⟶ T` are not used. -/
theorem isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y)
    (z : HilbertFamily f T)
    (hchart : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ schemeBaseChange f T),
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS
            (subspaceInclusion B S hS (schemeBaseChangeSpace f T)
              ⟨z.Z, z.closed⟩)).toSheafOfModules ↔
        ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
          (((BigFppfOver.toScheme B S hS).map (z.closed.2.rep.snd b)).ker.ideal A).FG)) :
    (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T)
      ⟨z.Z, z.closed⟩).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_pushforwardStructureSheaf_of_isFinitePresentation B S hS
    (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩
    (ObjectProperty.homMk (pullback.snd f.hom T.hom) :
      schemeBaseChangeSpace f T ⟶ schemeOverSpace T)
    (isFinitePresentation_schemeBaseChangeProjection f hf T) hchart z.finitePresentation

end AlgebraicGeometry.Space

end
