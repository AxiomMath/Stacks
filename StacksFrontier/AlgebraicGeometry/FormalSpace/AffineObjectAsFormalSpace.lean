module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# An affine object of the big fppf site as a sheafified functor of points

Let `S` be a scheme contained in a big fppf site `B`. An object `A` of the big fppf site of `S`
whose underlying scheme is affine presents a sheaf `h_A^#`
(`CategoryTheory.Sheaf.sheafifiedYoneda`), and that sheaf is the sheafification of the
restricted functor of points of an affine scheme over `S`. Together with
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sheafifiedYoneda`, which says that
the sheaf is an affine formal algebraic space (**Stacks 0AI7**), these are the two clauses that
the atlas hypothesis of `AlgebraicGeometry.FormalSpace.isAlgebraicSpace_of_affineSchemeAtlas`
asks of each of its members.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_points_iso_sheafifiedYoneda`: the sheaf of an
  affine object of the big fppf site of `S` is the sheafified restricted functor of points of an
  affine scheme over `S`.

## Implementation notes

The affine scheme over `S` is `A` itself, pushed into the schemes over `S` along the inclusion
of the site; the restricted functor of points of the image of `A` is the presheaf represented
by `A`, because the pushforward functor is fully faithful. That identification is
`AlgebraicGeometry.Space.pointsYonedaIso`. Whiskering it with `ULift` turns it into an
identification of the lifted functor of points with the universe-lifted Yoneda presheaf of `A`,
whose sheafification is the sheaf of `A` by definition of the sheafified Yoneda embedding.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of an affine object of the big fppf site of `S` is the sheafified restricted
functor of points of an affine scheme over `S`. -/
theorem exists_affine_points_iso_sheafifiedYoneda (A : BigFppfOver B S hS)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A)) :
    ∃ U : Over S, IsAffine U.left ∧
      Nonempty ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj A ≅
        (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
          (Stacks.Groupoids.points (Over.post B.inclusion) U ⋙ uliftFunctor.{u + 1, u})) := by
  refine ⟨(Over.post B.inclusion).obj A, hA, ⟨?_⟩⟩
  exact (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
    (Functor.isoWhiskerRight
      (Space.pointsYonedaIso (Over.post B.inclusion) A) uliftFunctor.{u + 1, u}).symm

end AlgebraicGeometry.FormalSpace

end
