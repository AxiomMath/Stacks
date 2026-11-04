module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeHorizontal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare

/-!
# Horizontal pasting of the degree-zero base change map, at the module spelling

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

The degree-zero base change map `AlgebraicGeometry.Space.moduleBaseChangeMap` of the rectangle
is the composite of the two base change maps of its squares, read through the comparisons of
Stacks 03LU for the two composite horizontal inverse images.  This is the degree-zero shape of
Stacks 0E47 for sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso`: the comparison
  `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a commutative square, as a
  named isomorphism.

## Main results

* `AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mate`: the base change map is the base change
  mate of `modulePushforwardSquareComparisonIso`, in the idiom
  `Stacks.Cohomology.BaseChange.mate_horizontal` consumes.
* `AlgebraicGeometry.Space.moduleBaseChangeMap_horizontal`: **the base change map of the
  rectangle is the composite of the two base change maps of its squares.**

## Implementation notes

The pasting law is `Stacks.Cohomology.BaseChange.mate_horizontal` applied to the comparisons
of inverse images, `AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal`.  Each base
change map is first rewritten as a mate by `moduleBaseChangeMap_eq_mate`, which keeps
`Stacks.Cohomology.BaseChange.mate` out of the unification problem.

Stacks 0E47 asserts the pasting law for the base change map of derived direct images; the
degree-zero shape proved here is not registered under that tag.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- The comparison `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a
commutative square of algebraic spaces: both composites are the direct image along the common
composite `g' ≫ f = f' ≫ g` of the square (Stacks 03LU). -/
def modulePushforwardSquareComparisonIso (comm : g' ≫ f = f' ≫ g) :
    modulePushforward B S hS g' ⋙ modulePushforward B S hS f ≅
      modulePushforward B S hS f' ⋙ modulePushforward B S hS g :=
  modulePushforwardCompIso B S hS g' f ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm) ≪≫
    (modulePushforwardCompIso B S hS f' g).symm

/-- The forward direction of `AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso` is
the comparison morphism `AlgebraicGeometry.Space.modulePushforwardSquareComparison`. -/
theorem modulePushforwardSquareComparisonIso_hom (comm : g' ≫ f = f' ≫ g) :
    (modulePushforwardSquareComparisonIso f g f' g' comm).hom =
      modulePushforwardSquareComparison B S hS g' f' f g comm := rfl

/-- The comparison of the two composite direct images around a square is the conjugate of the
comparison of the two composite inverse images, with the direct-image comparison read as the
named isomorphism `AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso`. -/
theorem conjugateEquiv_modulePullbackSquareComparison_inv_eq (comm : g' ≫ f = f' ≫ g) :
    conjugateEquiv ((modulePullbackAdjunction B S hS f).comp
          (modulePullbackAdjunction B S hS g'))
        ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f'))
        (modulePullbackSquareComparison f g f' g' comm).inv =
      (modulePushforwardSquareComparisonIso f g f' g' comm).hom :=
  conjugateEquiv_modulePullbackSquareComparison_inv f g f' g' comm

/-- The degree-zero base change map is the base change mate
`Stacks.Cohomology.BaseChange.mate` of the comparison of the two composite direct images around
the square. -/
theorem moduleBaseChangeMap_eq_mate (comm : g' ≫ f = f' ≫ g) :
    moduleBaseChangeMap f g f' g' comm =
      Stacks.Cohomology.BaseChange.mate (modulePullbackAdjunction B S hS g)
        (modulePullbackAdjunction B S hS g') (modulePushforward B S hS f)
        (modulePushforward B S hS f') (modulePushforwardSquareComparisonIso f g f' g' comm) := by
  rw [Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_vertical
    (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS g')
    (modulePushforwardSquareComparisonIso f g f' g' comm)
    (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS f')
    (TwoSquare.mk (modulePullback B S hS g) (modulePullback B S hS f)
      (modulePullback B S hS f') (modulePullback B S hS g')
      (modulePullbackSquareComparison f g f' g' comm).inv)
    (conjugateEquiv_modulePullbackSquareComparison_inv_eq f g f' g' comm)]
  exact moduleBaseChangeMap_eq_mateEquiv f g f' g' comm

end Square

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-- Stacks 0E47 in degree zero: for two commutative squares of algebraic spaces sharing a
vertical edge, the degree-zero base change map of the pasted rectangle is the composite of the
base change maps of the two squares, read through the comparisons of Stacks 03LU. -/
theorem moduleBaseChangeMap_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h) (K : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS h g).inv.app ((modulePushforward B S hS f).obj K) ≫
        (modulePullback B S hS h).map ((moduleBaseChangeMap f g f' g' comm).app K) ≫
        (moduleBaseChangeMap f' h f'' g'' comm').app ((modulePullback B S hS g').obj K) ≫
        (modulePushforward B S hS f'').map
          ((modulePullbackCompIso B S hS g'' g').hom.app K) =
      (moduleBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
        (pasteBaseComm f g f' g' h f'' g'' comm comm')).app K := by
  simp only [moduleBaseChangeMap_eq_mate]
  exact Stacks.Cohomology.BaseChange.mate_horizontal (hα :=
    conjugateEquiv_modulePullbackSquareComparison_inv_eq f g f' g' comm)
    (hα₂ := conjugateEquiv_modulePullbackSquareComparison_inv_eq f' h f'' g'' comm')
    (hα₀ := conjugateEquiv_modulePullbackSquareComparison_inv_eq f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (hs := modulePullbackSquareComparison_horizontal f f' f'' g g' h g'' comm comm') (K := K)

end Horizontal

end AlgebraicGeometry.Space

end
