module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison

/-!
# Affine objects are cofinal in the doubly localized big fppf site

Let `S` be a scheme of a big fppf site, let `U` be an object of the big fppf site over `S` and let
`g` be an object of the site over `U`. The affine opens of the underlying scheme of `g` that lie
over affine opens of `S` cover it, so a sieve on `g` which contains the open immersion of every
such affine open is a covering sieve for the topology that the localized fppf topology induces
on the site over `U`.

This is the shape in which a statement proved over affine objects is turned into a *local*
statement over an arbitrary object: both clauses of local bijectivity of a map of morphism
presheaves — a sieve of equalities and a sieve of liftings — are sieves on an object of the site
over `U`, and this is what makes them covering once they are known over affine objects.

## Main results

* `AlgebraicGeometry.BigFppfOver.mem_overTopology_of_openSubObj`: a sieve on an object of the
  site over `U` containing the open immersions of the affine opens lying over affine opens of `S`
  is a covering sieve.

## Implementation notes

The covering family is transported from
`AlgebraicGeometry.BigFppfOver.affineSubordinateCover`, read on the underlying object of the site
over `S`: its index type is reused verbatim, and its members are lifted to the site over `U` by
composing with the structure morphism of `g`. The resulting sieve is covering because
`CategoryTheory.GrothendieckTopology.mem_over_iff` and
`CategoryTheory.Sieve.overEquiv_ofArrows` identify it with the sieve the family generates
downstairs, which is
`AlgebraicGeometry.BigFppfOver.mem_topology_sieve₀_affineSubordinateCover`. A sieve containing a
covering sieve is covering, and containment of a generated sieve is containment of its
generators.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : BigFppfOver B S hS} (g : Over U)

/-- The covering of an object of the site over `U` by the affine opens of its underlying scheme
that lie over affine opens of `S`. -/
noncomputable def affineSubordinateCoverSlice : PreZeroHypercover.{u + 1} g where
  I₀ := (affineSubordinateCover B S hS g.left).I₀
  X i := Over.mk (openSubHom B S hS g.left i.down.1.1 ≫ g.hom)
  f i := Over.homMk (openSubHom B S hS g.left i.down.1.1)

/-- **The affine opens lying over affine opens of `S` cover an object of the site over `U`.** -/
theorem mem_overTopology_sieve₀_affineSubordinateCoverSlice :
    (affineSubordinateCoverSlice B S hS g).sieve₀ ∈ ((topology B S hS).over U) g := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact mem_topology_sieve₀_affineSubordinateCover B S hS g.left

/-- **A sieve on an object of the site over `U` which contains the open immersion of every affine
open of its underlying scheme lying over an affine open of `S` is a covering sieve.** -/
theorem mem_overTopology_of_openSubObj (R : Sieve g)
    (hR : ∀ i : (affineSubordinateCover B S hS g.left).I₀,
      R.arrows (Over.homMk (openSubHom B S hS g.left i.down.1.1) :
        Over.mk (openSubHom B S hS g.left i.down.1.1 ≫ g.hom) ⟶ g)) :
    R ∈ ((topology B S hS).over U) g := by
  refine ((topology B S hS).over U).superset_covering ?_
    (mem_overTopology_sieve₀_affineSubordinateCoverSlice B S hS g)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact hR

/-- The underlying scheme of a member of
`AlgebraicGeometry.BigFppfOver.affineSubordinateCoverSlice` is affine. -/
instance isAffine_affineSubordinateCoverSlice_obj
    (i : (affineSubordinateCover B S hS g.left).I₀) :
    IsAffine ((toScheme B S hS).obj ((affineSubordinateCoverSlice B S hS g).X i).left) :=
  i.down.1.2

end AlgebraicGeometry.BigFppfOver

end
