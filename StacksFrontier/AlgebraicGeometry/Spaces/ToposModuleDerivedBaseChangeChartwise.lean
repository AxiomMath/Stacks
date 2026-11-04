module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseDerivedIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeMap

/-!
# Invertibility of the base change map of Stacks 0736 is detected on the étale charts of the base

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a commutative square of algebraic spaces over a scheme `S`.  The base change map
`g^*Rf_* ⟶ Rf'_*(g')^*` of **Stacks 0736** is
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`, and
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_eq_baseChangeMap` says it *is*
`Stacks.Cohomology.ToposBaseChange.baseChangeMap`.  This file carries two facts about
that map — the horizontal pasting law of **Stacks 0E47** and the étale-chart detection of
isomorphisms in `D⁺(𝒪_{Y'})` — to a single statement: invertibility of the base change map of the
square is implied by invertibility of the base change maps of the rectangles obtained by pasting
the cartesian square of an étale chart of `Y'` onto it.

That is the locality half of the reduction of **Stacks 073K**, part (1), to its chart-local case.
It is *not* part (1); see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app`:
  for two commutative squares sharing a vertical edge, the derived inverse image along the lower
  horizontal leg `h` of the base change map of the right-hand square is invertible as soon as the
  base change map of the pasted rectangle and the base change map of the left-hand square are.
* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart`:
  **the base change map of the square is invertible as soon as it is chart-locally so** — if for
  every étale scheme chart of `Y'` there is a commutative square over that chart whose pasted
  rectangle's base change map, and whose own base change map, are invertible.

## Implementation notes

*What the glue is.*  The pasting law
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_horizontal` writes the rectangle's base
change map at an object as a composite of four morphisms, of which the first and the last are
isomorphisms unconditionally:  the first is the inverse of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact` for the two base legs, and the last
is the direct image of the corresponding comparison for the two source legs.  The second factor is
the derived inverse image along `h` of the right-hand square's base change map, which is what the
chart criterion asks about, and the third is the left-hand square's base change map.  So
invertibility of the rectangle's map together with invertibility of the third factor gives
invertibility of the second, and nothing else is used.

*Why the third factor has to be carried.*  For the chart square of an étale `V ⟶ Y'` the third
factor is the base change map of a cartesian square whose base leg is étale, so the source asserts
it is invertible; that invertibility is not proved here, so the étale case is carried as part of
the chart-local hypothesis rather than discharged.

*The exactness binders.*  They are the pasting engine's and no more.  The two base legs of the
chart square — the chart's own structure morphism — are exact here with nothing assumed, because
an étale morphism is flat (`AlgebraicGeometry.Space.isFlat_of_isEtale` at
`AlgebraicGeometry.Space.isEtale_chartToSpace`) and the inverse image along a flat morphism is
exact (**Stacks 04JC**, `AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`); the two
local instances below record that.  Exactness of the composite base leg and of the source leg of
the chart square is part of the chart-local hypothesis, since neither is determined by the square
alone; for a flat `g` and a cartesian chart square both hold, by **Stacks 04JC** again and by
**Stacks 03MO**.

*The pinned derived category.*  `HasDerivedCategory` is data, not a proposition, so the two
statements this file composes are only composable if instance search produces the same witness for
both.  The import closure here contains
`Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory`, which is found in
preference to `CategoryTheory.HasDerivedCategory.standard` and is *not* the witness either
statement was elaborated against; with it in force every application below is an application type
mismatch at the derived category argument.  The local instance below pins
`HasDerivedCategory.standard`, through its alias
`AlgebraicGeometry.Space.chartwiseLocalityHasDerivedCategory`, so that it is found first.
Nothing else in this file is sensitive to the instance environment:  `PreservesFiniteLimits`,
`PreservesFiniteColimits` and `CategoryTheory.Functor.Additive` are propositions, so which
witness is found cannot change a type.

*This is not Stacks 073K, part (1).*  Part (1) asserts invertibility of this map for a cartesian
square with `g` flat and `f` quasi-compact and quasi-separated, with nothing carried.  What is
below is an implication whose hypothesis is the chart-local case of that very assertion, so it is
a reduction and not the theorem.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules

-- The standard derived category of the `𝒪`-modules of an algebraic space, pinned so that it is
-- the witness instance search produces: the chaotic comparison instance is in this import
-- closure and wins otherwise, and the two statements composed below were elaborated against the
-- standard one.
attribute [local instance] chartwiseLocalityHasDerivedCategory

/-- In a composite of four morphisms whose first, third and fourth factors are invertible, the
second factor is invertible as soon as the composite is. -/
private theorem isIso_second_of_isIso_comp_four {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) [IsIso a] [IsIso c] [IsIso d]
    (habcd : IsIso (a ≫ b ≫ c ≫ d)) : IsIso b := by
  have := habcd
  have : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a (b ≫ c ≫ d)
  exact IsIso.of_isIso_comp_right b (c ≫ d)

/-! ### Transferring invertibility across a pasted rectangle -/

section Paste

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

/-- **Invertibility of the base change map of Stacks 0736 transfers from a pasted rectangle to
the derived inverse image along the lower horizontal leg.**  For two commutative squares of
algebraic spaces sharing a vertical edge, if the base change map of the pasted rectangle at `M`
and the base change map of the left-hand square at `(g')^*M` are both invertible, then the derived
inverse image along `h` of the base change map of the right-hand square at `M` is invertible.

This is the pasting law `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_horizontal` and
nothing else:  that law writes the rectangle's map as a four-fold composite whose outer two
factors are isomorphisms unconditionally, whose second factor is the morphism in the conclusion
and whose third factor is the left-hand square's map.

The hypotheses on the inverse images are the pasting engine's; for flat morphisms they are
**Stacks 04JC**, through
`AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`. -/
theorem isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app
    (comm : g' ≫ f = f' ≫ g) (comm' : g'' ≫ f' = f'' ≫ h)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hrect : IsIso ((toposModuleDerivedBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).app M))
    (hchart : IsIso ((toposModuleDerivedBaseChangeMap f' h f'' g'' comm').app
      ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M))) :
    IsIso ((modulePullback B S hS h).rightDerivedFunctorPlus.map
      ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M)) := by
  have hpaste := toposModuleDerivedBaseChangeMap_horizontal f f' f'' g g' h g'' comm comm' M
  rw [hpaste] at hrect
  have := hchart
  exact isIso_second_of_isIso_comp_four _ _ _ _ hrect

end Paste

/-! ### Detection on the étale charts of the base -/

section Chartwise

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Exactness of the inverse image of `𝒪`-modules along the structure morphism of an étale chart,
in the form the pasting law asks for.  An étale morphism is flat and the inverse image along a
flat morphism is exact, **Stacks 04JC**. -/
local instance chartwiseReductionPreservesFiniteLimits {Z : AlgebraicSpaces B S hS}
    (V : SmallEtale B S hS Z.obj) :
    PreservesFiniteLimits (modulePullback B S hS (chartToSpace B S hS Z V)) :=
  ((exactFunctor_iff _).1 (exactFunctor_modulePullback_of_isFlat B S hS
    (chartToSpace B S hS Z V)
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS (chartToSpace B S hS Z V)).1
      (isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS Z V))))).1

/-- Cocontinuity of the inverse image of `𝒪`-modules along the structure morphism of an étale
chart; the companion of `chartwiseReductionPreservesFiniteLimits`. -/
local instance chartwiseReductionPreservesFiniteColimits {Z : AlgebraicSpaces B S hS}
    (V : SmallEtale B S hS Z.obj) :
    PreservesFiniteColimits (modulePullback B S hS (chartToSpace B S hS Z V)) :=
  ((exactFunctor_iff _).1 (exactFunctor_modulePullback_of_isFlat B S hS
    (chartToSpace B S hS Z V)
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS (chartToSpace B S hS Z V)).1
      (isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS Z V))))).2

variable {X X' Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]

/-- **The base change map of Stacks 0736 is invertible as soon as it is chart-locally so.**  Let
the square `(f, g, f', g')` of algebraic spaces commute and let `M` be an object of `D⁺(𝒪_X)`.
Suppose that for every étale scheme chart `V` of `Y'` there is a commutative square over the
chart's structure morphism — a space `X''`, morphisms `f'' : X'' ⟶ V` and `g'' : X'' ⟶ X'` with
`g'' ≫ f' = f'' ≫ (V ⟶ Y')` — whose inverse images are exact where the pasting law needs them,
such that the base change map of the rectangle pasted out of the two squares is invertible at `M`
and the base change map of the chart square is invertible at `(g')^*M`.  Then the base change map
of the square itself is invertible at `M`.

This is the locality half of the reduction of **Stacks 073K**, part (1):  étale charts detect
isomorphisms in `D⁺(𝒪_{Y'})`
(`AlgebraicGeometry.Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace`), and the
derived inverse image along a chart of the square's base change map is invertible by
`isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app` applied to the rectangle.
It is not part (1) itself:  its hypothesis is the chart-local case of part (1)'s conclusion. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart (comm : g' ≫ f = f' ≫ g)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hchart : ∀ V : SmallEtale B S hS Y'.obj,
      ∃ (X'' : AlgebraicSpaces B S hS) (f'' : X'' ⟶ chartSpace B S hS Y' V) (g'' : X'' ⟶ X')
        (comm' : g'' ≫ f' = f'' ≫ chartToSpace B S hS Y' V)
        (_ : PreservesFiniteLimits
          (modulePullback B S hS (chartToSpace B S hS Y' V ≫ g)))
        (_ : PreservesFiniteColimits
          (modulePullback B S hS (chartToSpace B S hS Y' V ≫ g)))
        (_ : PreservesFiniteLimits (modulePullback B S hS g''))
        (_ : PreservesFiniteColimits (modulePullback B S hS g'')),
        IsIso ((toposModuleDerivedBaseChangeMap f (chartToSpace B S hS Y' V ≫ g) f''
            (g'' ≫ g') (pasteBaseComm f g f' g' (chartToSpace B S hS Y' V) f'' g''
              comm comm')).app M) ∧
          IsIso ((toposModuleDerivedBaseChangeMap f' (chartToSpace B S hS Y' V) f'' g''
            comm').app ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M))) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) := by
  refine isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace B S hS Y'
    ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) fun V => ?_
  obtain ⟨X'', f'', g'', comm', _, _, _, _, hrect, hsq⟩ := hchart V
  exact isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app f f' f'' g g'
    (chartToSpace B S hS Y' V) g'' comm comm' M hrect hsq

end Chartwise

end AlgebraicGeometry.Space

end
