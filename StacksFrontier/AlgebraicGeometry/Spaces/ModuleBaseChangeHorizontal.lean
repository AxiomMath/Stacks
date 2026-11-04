module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeHorizontalScaffolding
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteBaseChangeHorizontal

/-!
# Horizontal pasting of the comparison of composite inverse images, at the module spelling

Two commutative squares of algebraic spaces sharing a vertical edge paste to a commutative
rectangle:

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

The comparison of the two composite inverse images of `𝒪`-modules around the rectangle is the
horizontal pasting of the comparisons of its two squares, read through the comparisons of
Stacks 03LU for the two composite horizontal legs.  This is the geometric content of the
degree-zero horizontal pasting law of Stacks 0E47 for sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal`: the comparison of the
  two composite inverse images around a rectangle is the horizontal pasting of the comparisons
  of its two squares.

## Implementation notes

The five hypotheses of `Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal`
are discharged in `ModuleBaseChangeHorizontalScaffolding`, where the result is assembled as
`AlgebraicGeometry.Space.modulePasting_factors`.  The three square comparisons are kept opaque:
`Stacks.CategoryTheory.squareComparison_app_of_eq` takes them together with the equations
`AlgebraicGeometry.Space.modulePullbackSquareComparison_inv_eq` identifying each with its three
factors, and passes to components where the functors are variables.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-- The comparison of the two composite inverse images around a rectangle is the horizontal
pasting of the comparisons of its two squares, read through the comparisons
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU. -/
theorem modulePullbackSquareComparison_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f'').map ((modulePullbackCompIso B S hS h g).inv.app M) ≫
        (modulePullbackSquareComparison f' h f'' g'' comm').inv.app
          ((modulePullback B S hS g).obj M) ≫
        (modulePullback B S hS g'').map
          ((modulePullbackSquareComparison f g f' g' comm).inv.app M) ≫
        (modulePullbackCompIso B S hS g'' g').hom.app ((modulePullback B S hS f).obj M) =
      (modulePullbackSquareComparison f (h ≫ g) f'' (g'' ≫ g')
        (pasteBaseComm f g f' g' h f'' g'' comm comm')).inv.app M :=
  Stacks.CategoryTheory.squareComparison_app_of_eq
    (modulePullbackCompIso B S hS h g) (modulePullbackCompIso B S hS g'' g')
    (modulePullbackCompIso B S hS f' g) (modulePullbackCompIso B S hS g' f)
    (modulePullbackCompIso B S hS f'' h) (modulePullbackCompIso B S hS g'' f')
    (modulePullbackCompIso B S hS f'' (h ≫ g))
    (modulePullbackCompIso B S hS (g'' ≫ g') f)
    (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm
    (congrArg (fun k : X'' ⟶ Y' => modulePullback B S hS k) comm').symm
    (congrArg (fun k : X'' ⟶ Y => modulePullback B S hS k)
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).symm
    (modulePullbackSquareComparison f g f' g' comm).inv
    (modulePullbackSquareComparison f' h f'' g'' comm').inv
    (modulePullbackSquareComparison f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).inv
    (modulePullbackSquareComparison_inv_eq f g f' g' comm)
    (modulePullbackSquareComparison_inv_eq f' h f'' g'' comm')
    (modulePullbackSquareComparison_inv_eq f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    M
    (modulePasting_factors f f' f'' g g' h g'' comm comm'
      (by rw [Category.assoc, comm]) (by rw [← Category.assoc, ← comm', Category.assoc]) M)

end Horizontal

end AlgebraicGeometry.Space

end
