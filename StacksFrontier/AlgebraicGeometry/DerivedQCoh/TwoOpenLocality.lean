module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionPerfectSupport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness

/-!
# Cohomological support and perfectness are local on a cover by two open immersions

Let `X` be a scheme covered by the images of two open immersions `g₁ : Y₁ ⟶ X` and
`g₂ : Y₂ ⟶ X`. An object of `D(𝒪_X)` whose restrictions along `g₁` and `g₂` have their cohomology
supported on the preimages of a subset `T` of `X` has its own cohomology supported on `T`; and an
object whose two restrictions are perfect is perfect.

These are the converses of `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor` and
of `Stacks.DerivedQCoh.isPerfect_derivedRestrict`, and they are what a glueing argument needs of
the object it has just glued: [Stacks, Tag 08DG] produces an object of `D(𝒪_X)` from its two
restrictions and says nothing about either property, which have to be read off the restrictions
afterwards.

## Main results

* `Stacks.DerivedQCoh.isZero_stalk_homology_of_restrict`: a cohomology stalk of an object of
  `D(𝒪_X)` at a point of an open subscheme is the corresponding stalk of the restriction.
* `Stacks.DerivedQCoh.cohomologySupportedOn_of_cover`: the support condition is local on a cover
  by two open immersions.
* `Stacks.DerivedQCoh.isPerfect_restrict_opensRange`: perfectness of a restriction along an open
  immersion is perfectness of the restriction to its image.
* `Stacks.DerivedQCoh.isPerfect_of_cover`: perfectness is local on a cover by two open
  immersions.

## Implementation notes

The support condition `AlgebraicGeometry.CohomologySupportedOn` is a condition on stalks, so its
locality is the comparison of a stalk of a cohomology sheaf with the corresponding stalk of the
restriction -- Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` after the
identification of the cohomology of a restriction with the restriction of the cohomology. That
comparison is read here in the direction opposite to
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor`, which is the only difference
between the two proofs; it is stated for an arbitrary open immersion rather than for the
inclusion of an open subscheme, since nothing in it needs the inclusion, and that generality is
what [Stacks, Tag 08DG] consumes: there one of the two opens is the spectrum of the sections over
an affine open, not a subspace of the ambient space.

**Both spellings of restriction are crossed by the two comparisons already in the library.**
Perfectness is local on the space by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`, which is written in the
ringed-space spelling `AlgebraicGeometry.RingedSpace.restrictModules` of restriction, while the
support condition and [Stacks, Tag 08EK] are written in Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The passage between the two on derived
categories is `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`, which
pays for the crossing by supplying all six exactness instances as terms; no instance of the
`StrictlyPerfect.OXMod` spelling is ever asked for, which is what makes the crossing go through
where instance search on its own does not. Passing from a general open immersion to the inclusion
of its image is then `AlgebraicGeometry.Scheme.Hom.isoOpensRange` together with
`Stacks.DerivedQCoh.isPerfect_derivedRestrict` along its inverse.

## References

* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.SchemeCohomology (ringedSpace)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A cohomology stalk at a point of an open subscheme is a stalk of the restriction.** If the
`i`-th cohomology sheaf of `K|_Y` has vanishing stalk at `y`, then the `i`-th cohomology sheaf of
`K` has vanishing stalk at the image of `y`.

The cohomology of a restriction is the restriction of the cohomology, and the stalk of a
restriction at `y` is the stalk at the image of `y`, by
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. -/
theorem isZero_stalk_homology_of_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (K : DerivedCategory X.Modules) (i : ℤ) (y : Y)
    (h : IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K)).val.presheaf) y)) :
    IsZero (TopCat.Presheaf.stalk
      (((DerivedCategory.homologyFunctor X.Modules i).obj K).val.presheaf) (g.base y)) :=
  IsZero.of_iso h
    (((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (Scheme.Modules.restrictFunctor g) i).app K)) ≪≫
      ((Scheme.Modules.restrictStalkNatIso g y).app
        ((DerivedCategory.homologyFunctor X.Modules i).obj K))).symm

/-- **The cohomological support condition is local on a cover by two open immersions.** If the
images of `g₁` and `g₂` cover `X` and the cohomology of `K|_{Y₁}` and of `K|_{Y₂}` is supported
on the preimages of `T`, then the cohomology of `K` is supported on `T`.

The condition is on stalks, and every point is in the image of `g₁` or of `g₂`. -/
theorem cohomologySupportedOn_of_cover {X Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    [IsOpenImmersion g₁] [IsOpenImmersion g₂]
    (hcover : ∀ x : X, x ∈ Set.range g₁.base ∨ x ∈ Set.range g₂.base)
    (T : Set X) (K : DerivedCategory X.Modules)
    (h₁ : CohomologySupportedOn Y₁.ringCatSheaf (⇑g₁.base ⁻¹' T)
      ((Scheme.Modules.restrictFunctor g₁).mapDerivedCategory.obj K))
    (h₂ : CohomologySupportedOn Y₂.ringCatSheaf (⇑g₂.base ⁻¹' T)
      ((Scheme.Modules.restrictFunctor g₂).mapDerivedCategory.obj K)) :
    CohomologySupportedOn X.ringCatSheaf T K := by
  intro i x hx
  wlog h : x ∈ Set.range g₁.base generalizing Y₁ Y₂ g₁ g₂
  · exact this g₂ g₁ (fun x => (hcover x).symm) h₂ h₁ ((hcover x).resolve_left h)
  obtain ⟨y, rfl⟩ := h
  exact isZero_stalk_homology_of_restrict g₁ K i y (h₁ i y hx)

/-- **Perfectness of a restriction along an open immersion is perfectness of the restriction to
its image.** Restricting further along the inverse of
`AlgebraicGeometry.Scheme.Hom.isoOpensRange` turns one into the other, and restriction preserves
perfectness. -/
theorem isPerfect_restrict_opensRange {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (K : DerivedCategory X.Modules)
    (h : IsPerfect (X := ringedSpace Y)
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K)) :
    IsPerfect (X := ringedSpace g.opensRange.toScheme)
      ((Scheme.Modules.restrictFunctor g.opensRange.ι).mapDerivedCategory.obj K) := by
  have hι : g.isoOpensRange.inv ≫ g = g.opensRange.ι :=
    (Iso.inv_comp_eq _).2 g.isoOpensRange_hom_ι.symm
  have h2 := isPerfect_derivedRestrict g.isoOpensRange.inv
    ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K) h
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} ?_ h2
  exact (Functor.mapDerivedCategoryCompIso
    ((Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hι)).app K

/-- **Perfectness is local on a cover by two open immersions.** If the images of `g₁` and `g₂`
cover `X` and the restrictions of `K` along them are perfect, then `K` is perfect.

Perfectness is local on the space by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`, which asks for an open
*subspace* around each point; the image of whichever of the two open immersions contains the point
is such a neighbourhood, and `Stacks.DerivedQCoh.isPerfect_restrict_opensRange` identifies the two
restrictions there. -/
theorem isPerfect_of_cover {X Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    [IsOpenImmersion g₁] [IsOpenImmersion g₂]
    (hcover : ∀ x : X, x ∈ Set.range g₁.base ∨ x ∈ Set.range g₂.base)
    (K : DerivedCategory X.Modules)
    (h₁ : IsPerfect (X := ringedSpace Y₁)
      ((Scheme.Modules.restrictFunctor g₁).mapDerivedCategory.obj K))
    (h₂ : IsPerfect (X := ringedSpace Y₂)
      ((Scheme.Modules.restrictFunctor g₂).mapDerivedCategory.obj K)) :
    IsPerfect (X := ringedSpace X) K := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect K fun x => ?_
  wlog h : x ∈ g₁.opensRange generalizing Y₁ Y₂ g₁ g₂
  · exact this g₂ g₁ (fun x => (hcover x).symm) h₂ h₁ ((hcover x).resolve_left h)
  exact ⟨g₁.opensRange, h, Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X
      g₁.opensRange).app K).symm (isPerfect_restrict_opensRange g₁ K h₁)⟩

end Stacks.DerivedQCoh

end
