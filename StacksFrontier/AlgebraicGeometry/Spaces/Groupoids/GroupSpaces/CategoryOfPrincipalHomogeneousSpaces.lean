module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfFppfTorsors

/-!
# The category of principal homogeneous spaces

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`.
Stacks 04UN defines the category `G-Principal`: an object is a triple `(U, b, X)` with `U` an
object of `(Sch/S)_fppf`, `b : U ⟶ B` a morphism, and `X` a *principal homogeneous* `G_U`-space
over `U` for `G_U = U ×_{b, B} G` — that is, by Stacks 04TY part (1), a pseudo-torsor which is
trivialized by an **fpqc** covering of `U`; a morphism `(U, b, X) ⟶ (U', b', X')` is a pair
`(f, g)` with `f : U ⟶ U'` over `B` and `g` an equivariant identification of `X` with
`U ×_{f, U'} X'`. Sending `(U, b, X)` to `U` is a functor `p : G-Principal ⥤ (Sch/S)_fppf`, and
the fibre category over `U` is the disjoint union over the morphisms `b : U ⟶ B` of the
categories of principal homogeneous `U ×_{b, B} G`-spaces, hence is a groupoid.

`G-Principal` is a different category from the category `G-Torsors` of Stacks 04UR, whose objects
are trivialized by an *fppf* covering: by Stacks 077B there is a principal homogeneous space
isomorphic to no fppf torsor, so the canonical functor `G-Torsors ⥤ G-Principal` is not
essentially surjective in general, which is
`Stacks.Examples.RadicalTower.exists_not_isEquivalence_fppfTorsors_toPrincipal`. So neither the
category nor any property of `p` may be read off from Stacks 04UR and Stacks 04US.

## Main definitions

* `AlgebraicGeometry.Space.CoveringPredicate.fpqc`: the fpqc coverings, as the trivializing
  condition of Stacks 04TY part (1).
* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces`: the objects of `G-Principal`, and
  `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.isPrincipal`: the principal homogeneous
  space condition they carry.
* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.projection`: the functor
  `p : G-Principal ⥤ (Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.Space.TorsorsFor.isIso_of_isIso_base`: **Stacks 04UN**, a morphism of
  `G-Principal` lying over an isomorphism of the site is an isomorphism, that is the fibre
  categories of `p` are groupoids.

## Implementation notes

The objects, the morphisms, the base changes of the group and of the action, the category and
the functor `p` are those of `AlgebraicGeometry.Space.TorsorsFor` at the fpqc coverings; only
the covering property distinguishes `G-Principal` from `G-Torsors`, so that is the only datum
supplied here. The morphisms, the category and the groupoid property of the fibre categories
therefore carry Stacks 04UN on the declarations stating them for an arbitrary covering
property, which is where Stacks 04UR sits as well.

Stacks 04UP *conjectures* that, up to a replacement as in Stacks 03ZZ, `p` is a stack in groupoids
over `(Sch/S)_fppf`, and reduces that conjecture to the effectivity of a descent datum of
principal homogeneous spaces along an fppf covering. The source proves neither, and calls the
reduced statement a problem with a suggested approach; nothing here asserts it. That `p` is fibred
in groupoids, the first of the three conditions of Stacks 02ZI, is proved in the module
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.PrincipalHomogeneousSpacesFibred`.

## References

* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

/-- Being an fpqc covering of the target, as a property of families of morphisms. -/
abbrev CoveringPredicate.fpqc (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) :
    CoveringPredicate 𝒞 S hS :=
  fun _ _ _ f => IsFpqcCovering 𝒞 S hS f

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- **Stacks 04UN.** An object of the category `G-Principal`: an object `U` of the big fppf site
of `S`, a morphism `b : U ⟶ B`, and a principal homogeneous space `X` over `U` under
`G_U = U ×_{b, B} G`, that is a pseudo-torsor trivialized by an fpqc covering of `U`. -/
@[stacks 04UN "the objects of G-Principal"]
abbrev PrincipalHomogeneousSpaces := TorsorsFor hB G (CoveringPredicate.fpqc 𝒞 S hS)

namespace PrincipalHomogeneousSpaces

variable {hB G}

/-- The total space of an object of `G-Principal` is a principal homogeneous space under `G_U`
over `U`, in the sense of Stacks 04TY part (1). -/
theorem isPrincipal (T : PrincipalHomogeneousSpaces hB G) :
    @IsPrincipalHomogeneousSpace 𝒞 S hS (yoneda.obj T.base)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda 𝒞 S hS T.base)
      (fppfPullbackGroup hB G T.base T.sec).obj.X T.total _ T.action
      (fppfPullbackGroup hB G T.base T.sec).property T.isAlgebraicSpace :=
  T.isTorsor

end PrincipalHomogeneousSpaces

/-- **Stacks 04UN.** The functor `p : G-Principal ⥤ (Sch/S)_fppf` sending `(U, b, X)` to `U`,
which is how `G-Principal` is regarded as a category over the big fppf site of `S`. -/
@[stacks 04UN "the functor p to the site"]
abbrev PrincipalHomogeneousSpaces.projection :
    PrincipalHomogeneousSpaces hB G ⥤ BigFppfOver 𝒞 S hS :=
  TorsorsFor.projection hB G (CoveringPredicate.fpqc 𝒞 S hS)

end AlgebraicGeometry.Space

end
