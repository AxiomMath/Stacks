module

public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeHorizontal

/-!
# The derived base change map of a square of algebraic spaces

For a commutative square

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

of algebraic spaces, this file defines the base change map `g^*Rf_* ⟶ Rf'_*(g')^*` on the bounded
below derived categories of modules over `AlgebraicGeometry.Space.Modules`, identifies it with
`Stacks.Cohomology.ToposBaseChange.baseChangeMap` of the square of small étale ringed topoi, and
proves its horizontal pasting law.

## Main definitions

* `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`: the base change map
  `g^*Rf_* ⟶ Rf'_*(g')^*` of a commutative square of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_eq_baseChangeMap`: it is
  `Stacks.Cohomology.ToposBaseChange.baseChangeMap` of the square of small étale ringed topoi.
* `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_horizontal`: the base change map of a
  pasted rectangle is the composite of the base change maps of its two squares, through the
  comparisons of the derived inverse images along the composite horizontal legs.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard enoughInjectives_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-! ### The base change map of a square -/

section Square

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]

/-- The base change map `g^*Rf_* ⟶ Rf'_*(g')^*` of a commutative square of algebraic spaces,
on the bounded below derived categories of `AlgebraicGeometry.Space.Modules`: the morphism
`Stacks.Cohomology.BaseChange.derived` induced by the degree-zero base change map
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` and the derived-functor unit of `g^*`. -/
def toposModuleDerivedBaseChangeMap (comm : g' ≫ f = f' ≫ g) :
    (toposModulePushforward f).rightDerivedFunctorPlus ⋙
        (modulePullback B S hS g).rightDerivedFunctorPlus ⟶
      (modulePullback B S hS g').rightDerivedFunctorPlus ⋙
        (toposModulePushforward f').rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derived (toposModulePushforward f) (toposModulePushforward f')
    (modulePullback B S hS g) (modulePullback B S hS g')
    (toposModuleBaseChangeMap f g f' g' comm)
    (asIso (modulePullback B S hS g).rightDerivedFunctorPlusUnit)

/-- `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` is the base change map
`Stacks.Cohomology.ToposBaseChange.baseChangeMap` of the square of small étale ringed topoi. -/
theorem toposModuleDerivedBaseChangeMap_eq_baseChangeMap (comm : g' ≫ f = f' ≫ g)
    (hg : RingedToposHom.IsFlat (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g))
    (hg' : RingedToposHom.IsFlat (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')) :
    toposModuleDerivedBaseChangeMap f g f' g' comm =
      Stacks.Cohomology.ToposBaseChange.baseChangeMap
        (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS g')
        (toposPushforwardSquareComparisonIso f g f' g' comm) hg hg' := rfl

end Square

/-! ### Horizontal pasting -/

section Horizontal

variable {X'' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]
    [PreservesFiniteLimits (modulePullback B S hS h)]
    [PreservesFiniteColimits (modulePullback B S hS h)]
    [PreservesFiniteLimits (modulePullback B S hS (h ≫ g))]
    [PreservesFiniteColimits (modulePullback B S hS (h ≫ g))]
    [PreservesFiniteLimits (modulePullback B S hS g'')]
    [PreservesFiniteColimits (modulePullback B S hS g'')]

/-- For two commutative squares of algebraic spaces sharing a vertical edge, the base change map
of the pasted rectangle, evaluated at an object, is the composite of the base change maps of the
two squares, read through the comparisons of the derived inverse images along the two composite
horizontal legs. -/
theorem toposModuleDerivedBaseChangeMap_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    (toposModuleDerivedBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
          (pasteBaseComm f g f' g' h f'' g'' comm comm')).app M =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact (modulePullback B S hS g)
            (modulePullback B S hS h) (modulePullback B S hS (h ≫ g))
            (modulePullbackCompIso B S hS h g)).inv.app
          ((toposModulePushforward f).rightDerivedFunctorPlus.obj M) ≫
        (modulePullback B S hS h).rightDerivedFunctorPlus.map
            ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) ≫
          (toposModuleDerivedBaseChangeMap f' h f'' g'' comm').app
              ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M) ≫
            (toposModulePushforward f'').rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact (modulePullback B S hS g')
                (modulePullback B S hS g'') (modulePullback B S hS (g'' ≫ g'))
                (modulePullbackCompIso B S hS g'' g')).hom.app M) :=
  toposModuleDerivedBaseChange_horizontal f f' f'' g g' h g'' comm comm' M

end Horizontal

end AlgebraicGeometry.Space

end
