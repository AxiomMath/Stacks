module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalImmersionSquareAmbient

/-!
# The ambient pair of a square of immersions, taken over the coborder ambient of the upper row

Let
```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B` whose two horizontal morphisms are immersions of schemes.
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalImmersionSquareAmbient.lean` builds for such a
square an ambient open of `V` on which `j` becomes a **closed** immersion and which `a` carries
into the coborder ambient of `j'`.

This file applies that construction **one level up**: not to the square itself, but to the square
obtained by replacing `j` with its own closed factorisation
`AlgebraicGeometry.Space.immersionCoborderLift` through
`AlgebraicGeometry.Space.immersionCoborderObj`, and `a` with the restriction of `a` to that
ambient.  The result is again a commutative square with the same lower row whose two horizontal
morphisms are immersions — the upper one is even a closed immersion.

The reason to take it there is the **morphism of ambients it adds**.  Applied to the square over
`V`, the construction produces an open of `V` which need not lie inside `j.coborderRange`, so
nothing relates it to the ambient at which part (1) of [Stacks Project, Tag 04G2]
(`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`) is defined — and that is the
only ambient at which part (1) is available.  Applied one level up, the ambient it produces is by
construction an open of an open of `AlgebraicGeometry.Space.immersionCoborderObj`, and
`AlgebraicGeometry.Space.squareAmbientHom` is then a morphism **into**
`AlgebraicGeometry.Space.immersionCoborderObj`, which is exactly the datum a change of ambient
between two closed factorisations of `j` needs.  Writing `L` and `L'` for the coborder lifts of
`j` and `j'`, `C` and `C'` for their ambients, `J` for the lift of `j` built here, `W` for its
ambient, `w` for the morphism to `C` and `A` for the one to `C'`, both squares
```
R --J--→ W            R --J--→ W
|        |            |        |
𝟙        w            b        A
↓        ↓            ↓        ↓
R --L--→ C            R' -L'-→ C'
```
have **both** horizontal morphisms closed immersions, so the naturality of part (1) of
[Stacks Project, Tag 04G2] in the closed immersion applies to each of them.

## Main definitions

* `AlgebraicGeometry.Space.coborderAmbientMap`: the restriction of `a` to the coborder ambient of
  `j`, the right-hand vertical morphism of the lifted square.
* `AlgebraicGeometry.Space.coborderSquareObj` and `AlgebraicGeometry.Space.coborderSquareLift`:
  the ambient `W` of the lifted square and the closed factorisation `J` of `j` through it.
* `AlgebraicGeometry.Space.coborderSquareHom` and `AlgebraicGeometry.Space.coborderSquareMap`:
  the morphisms `w : W ⟶ C` and `A : W ⟶ C'`.

## Main results

* `AlgebraicGeometry.Space.coborderSquare_comm`: the lifted square commutes.
* `AlgebraicGeometry.Space.coborderSquareLift_comp_coborderSquareHom`: `J ≫ w = L`, with
  `AlgebraicGeometry.Space.coborderSquareLift_comp_coborderSquareHom_id` the same equation with
  the identity in front, which is the shape a commutative square of the site takes.
* `AlgebraicGeometry.Space.coborderSquareLift_comp_coborderSquareMap`: `J ≫ A = b ≫ L'`.

No `@[stacks]` attribute is claimed: this is the construction the source's proof of part (2) of
[Stacks Project, Tag 04G2] makes, not a statement of the tag.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The restriction of `a` to the coborder ambient of `j`**: the inclusion of that ambient
followed by `a`.  It is the right-hand vertical morphism of the lifted square. -/
noncomputable abbrev coborderAmbientMap : immersionCoborderObj B S hS j ⟶ V' :=
  openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange ≫ a

omit hj' in
/-- **The square read at the coborder ambient of `j`.**  Replacing `j` by its closed
factorisation through its own ambient open and `a` by the restriction of `a` to that ambient
leaves a commutative square with the same lower row. -/
theorem coborderSquare_comm (hsq : j ≫ a = b ≫ j') :
    immersionCoborderLift B S hS j ≫ coborderAmbientMap B S hS j a = b ≫ j' :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ a) (immersionCoborderLift_comp_openSubHom B S hS j)).trans hsq)

/-- **The ambient of the lifted square**: an open of an open of the coborder ambient of `j`. -/
noncomputable abbrev coborderSquareObj (hsq : j ≫ a = b ≫ j') : BigFppfOver B S hS :=
  squareAmbientObj B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- **The closed factorisation of `j` through the ambient of the lifted square.** -/
noncomputable abbrev coborderSquareLift (hsq : j ≫ a = b ≫ j') :
    R ⟶ coborderSquareObj B S hS j j' b a hsq :=
  squareAmbientLift B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- **The morphism from the ambient of the lifted square to the coborder ambient of `j`**, along
which the two closed factorisations of `j` are compared. -/
noncomputable def coborderSquareHom (hsq : j ≫ a = b ≫ j') :
    coborderSquareObj B S hS j j' b a hsq ⟶ immersionCoborderObj B S hS j :=
  squareAmbientHom B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- **The morphism from the ambient of the lifted square to the coborder ambient of `j'`.** -/
noncomputable def coborderSquareMap (hsq : j ≫ a = b ≫ j') :
    coborderSquareObj B S hS j j' b a hsq ⟶ immersionCoborderObj B S hS j' :=
  squareAmbientMap B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- **The change-of-ambient factorisation of the coborder lift of `j`.** -/
theorem coborderSquareLift_comp_coborderSquareHom (hsq : j ≫ a = b ≫ j') :
    coborderSquareLift B S hS j j' b a hsq ≫ coborderSquareHom B S hS j j' b a hsq =
      immersionCoborderLift B S hS j :=
  squareAmbientLift_comp_squareAmbientHom B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- The change of ambient as a **commutative square** of the site, the identity down the left. -/
theorem coborderSquareLift_comp_coborderSquareHom_id (hsq : j ≫ a = b ≫ j') :
    coborderSquareLift B S hS j j' b a hsq ≫ coborderSquareHom B S hS j j' b a hsq =
      𝟙 R ≫ immersionCoborderLift B S hS j :=
  (coborderSquareLift_comp_coborderSquareHom B S hS j j' b a hsq).trans
    (Category.id_comp _).symm

/-- **The square of closed immersions over the two coborder ambients.** -/
theorem coborderSquareLift_comp_coborderSquareMap (hsq : j ≫ a = b ≫ j') :
    coborderSquareLift B S hS j j' b a hsq ≫ coborderSquareMap B S hS j j' b a hsq =
      b ≫ immersionCoborderLift B S hS j' :=
  squareAmbientLift_comp_squareAmbientMap B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

end AlgebraicGeometry.Space

end
