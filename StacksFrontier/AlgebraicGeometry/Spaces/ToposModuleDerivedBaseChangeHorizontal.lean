module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeHorizontal
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePastingNamed

/-!
# The derived horizontal pasting law for algebraic spaces

Let

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

be two commutative squares of algebraic spaces sharing a vertical edge. Each square has a
degree-zero base change map `AlgebraicGeometry.Space.toposModuleBaseChangeMap`, and
`Stacks.Cohomology.BaseChange.derived` descends it to the bounded below derived categories of
`𝒪`-modules. The derived comparison of the outer rectangle is the composite of the derived
comparisons of the two squares, read through the comparisons
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact` of the derived inverse images
along the two composite horizontal legs.

## Main results

* `AlgebraicGeometry.Space.toposModuleDerivedBaseChange_horizontal`: the derived horizontal
  pasting law, evaluated at an object of `D⁺(𝒪_X)`.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard enoughInjectives_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]
    [PreservesFiniteLimits (modulePullback B S hS h)]
    [PreservesFiniteColimits (modulePullback B S hS h)]
    [PreservesFiniteLimits (modulePullback B S hS (h ≫ g))]
    [PreservesFiniteColimits (modulePullback B S hS (h ≫ g))]
    [PreservesFiniteLimits (modulePullback B S hS g'')]
    [PreservesFiniteColimits (modulePullback B S hS g'')]

/-- For two commutative squares of algebraic spaces sharing a vertical edge, the descent to
`D⁺(𝒪_Y'')` of the degree-zero base change map
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` of the pasted rectangle, evaluated at an
object, is the composite of the descents of the two squares' base change maps, read through the
comparisons of the derived inverse images along the two composite horizontal legs. -/
theorem toposModuleDerivedBaseChange_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    (Stacks.Cohomology.BaseChange.derived (toposModulePushforward f) (toposModulePushforward f'')
          (modulePullback B S hS (h ≫ g)) (modulePullback B S hS (g'' ≫ g'))
          (toposModuleBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
            (pasteBaseComm f g f' g' h f'' g'' comm comm'))
          (asIso (modulePullback B S hS (h ≫ g)).rightDerivedFunctorPlusUnith)).app M =
      (Functor.rightDerivedFunctorPlusCompIsoOfExact (modulePullback B S hS g)
            (modulePullback B S hS h) (modulePullback B S hS (h ≫ g))
            (modulePullbackCompIso B S hS h g)).inv.app
          ((toposModulePushforward f).rightDerivedFunctorPlus.obj M) ≫
        (modulePullback B S hS h).rightDerivedFunctorPlus.map
            ((Stacks.Cohomology.BaseChange.derived (toposModulePushforward f)
              (toposModulePushforward f')
              (modulePullback B S hS g) (modulePullback B S hS g')
              (toposModuleBaseChangeMap f g f' g' comm)
              (asIso (modulePullback B S hS g).rightDerivedFunctorPlusUnith)).app M) ≫
          (Stacks.Cohomology.BaseChange.derived (toposModulePushforward f')
              (toposModulePushforward f'')
              (modulePullback B S hS h) (modulePullback B S hS g'')
              (toposModuleBaseChangeMap f' h f'' g'' comm')
              (asIso (modulePullback B S hS h).rightDerivedFunctorPlusUnith)).app
              ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M) ≫
            (toposModulePushforward f'').rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusCompIsoOfExact (modulePullback B S hS g')
                (modulePullback B S hS g'') (modulePullback B S hS (g'' ≫ g'))
                (modulePullbackCompIso B S hS g'' g')).hom.app M) :=
  Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app_named
    (Modules.{u, u} B S hS X.1 X.2) (Modules.{u, u} B S hS X'.1 X'.2)
    (Modules.{u, u} B S hS X''.1 X''.2) (Modules.{u, u} B S hS Y.1 Y.2)
    (Modules.{u, u} B S hS Y'.1 Y'.2) (Modules.{u, u} B S hS Y''.1 Y''.2)
    (toposModulePushforward f) (toposModulePushforward f') (toposModulePushforward f'')
    (modulePullback B S hS g) (modulePullback B S hS h) (modulePullback B S hS (h ≫ g))
    (modulePullback B S hS g') (modulePullback B S hS g'') (modulePullback B S hS (g'' ≫ g'))
    (modulePullbackCompIso B S hS h g) (modulePullbackCompIso B S hS g'' g')
    (toposModuleBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (toposModuleBaseChangeMap f g f' g' comm)
    (toposModuleBaseChangeMap f' h f'' g'' comm')
    (toposModuleBaseChangeMap_horizontal f f' f'' g g' h g'' comm comm') M

end AlgebraicGeometry.Space

end
