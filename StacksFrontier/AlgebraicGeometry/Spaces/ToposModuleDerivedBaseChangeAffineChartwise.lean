module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeChartwise

/-!
# The chart-local reduction of Stacks 0736's base change map runs over the affine charts alone

`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart`
(`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeChartwise.lean`) reduces
invertibility of the base change map of **Stacks 0736** to the étale charts of the base `Y'`, and
quantifies over *every* object of the small étale site of `Y'`.  An étale scheme over `Y'` need not
be affine, so that form of the reduction cannot meet an affine case.  This file replaces the
quantifier by one over an arbitrary family of charts which *has enough objects* for the small
étale topology — in particular by one over the affine charts alone.

The degree-zero statement that makes this possible is available:
`AlgebraicGeometry.Space.isIso_of_forall_bijective_val_app_affine_chart` tests invertibility of a
morphism of `𝒪_Y`-modules on the sections over the affine charts only, through
`CategoryTheory.GrothendieckTopology.HasEnoughObjects`.  What this file does is carry that from
degree zero to `D⁺(𝒪_{Y'})` and then through the pasting law.

## Main results

* `Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace_of_hasEnoughObjects`:
  a family of charts with enough objects detects isomorphisms of `𝒪_Y`-modules.  This is
  `AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_affine_chartToSpace` with the
  affine charts replaced by an arbitrary such family.
* `Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace_of_hasEnoughObjects`:
  **the same family detects isomorphisms in `D⁺(𝒪_Y)`.**
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_affine_chartToSpace`:
  **the affine étale charts alone detect isomorphisms in `D⁺(𝒪_Y)`.**
* `Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart_of_hasEnoughObjects`
  and `…_of_forall_affine_chart`: **the locality half of the reduction of Stacks 073K, part (1),
  with the chart quantifier restricted to a family with enough objects, resp. to the affine
  charts.**
* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_paste`: the direction of the
  pasting law the reduction needs in order to *build* the invertibility of a rectangle's base
  change map out of the two squares it is pasted from.

## Implementation notes

*Why a family with enough objects, and not a covering family.*  The bounded below locality
criterion over a covering family is available —
`Stacks.SheafOfModules.isIso_of_coversTop_rightDerivedFunctorPlus`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/DerivedIsomorphismLocalityBoundedBelow.lean`) —
but it tests restriction to the *slice* site, taken by `SheafOfModules.overFunctor`, whereas the
pasting law of **Stacks 0E47** delivers the inverse image along a morphism of algebraic spaces,
`AlgebraicGeometry.Space.modulePullback`.  Identifying the two is the transport of **Stacks 04M1**
to sheaves of modules, which this development does not have;  the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartwiseDerivedIsomorphismDetection.lean` record that.
`CategoryTheory.GrothendieckTopology.HasEnoughObjects` needs no such transport:  it is consumed by
`Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app`, which is a statement about
*sections*, and the sections of the inverse image along a chart over the identity chart of the
space the chart represents are the sections over the chart on the nose
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_map_val_app_idEtaleChart`).

*What the reduction to an affine base still owes, and why it is one statement.*  The affine case of
**Stacks 073K** is about a square whose base *and* base' are affine.  Over an affine chart `V` of
`Y'` the rectangle of the reduction has base leg `V ⟶ Y' ⟶ Y`, with `Y` not localized, so the
affine case does not apply to it;  what applies is the pasting law, through a factorization of that
base leg as `V ⟶ W ⟶ Y` with `W` an *affine chart of `Y`*, whose two squares are an étale square
(the chart `W`) and a square over an affine base (`V ⟶ W` between affines).  The pasting direction
is `isIso_toposModuleDerivedBaseChangeMap_app_paste` below and the étale square's own case is
`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale`
(`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeEtaleSquare.lean`), which is
unconditional.

An arbitrary affine chart `V` admits no such factorization:  a morphism from a scheme to an
algebraic space lifts to an étale chart of the target only *locally on the source*.  That is
exactly why the statements below are given for an arbitrary family with enough objects and not only
for the affine charts, and it reduces the geometry part (1) still owes to a single statement, with
`P V` the conjunction of "`V` is an affine chart" and "`chartToSpace B S hS Y' V ≫ g` factors
through `chartToSpace B S hS Y W` for some affine chart `W` of `Y`":

> `(SmallEtale.topology B S hS Y'.obj).HasEnoughObjects P`.

This is the source's own "the question is local on `Y'`" step, and it is not a declaration of the library.
The nearest available input is
`AlgebraicGeometry.Space.exists_affine_etale_chart_factorization`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineEtaleChartFactorization.lean`), which does lift a
morphism from a scheme to an algebraic space through an affine étale chart locally on the source —
but its covering family is a covering family for `AlgebraicGeometry.BigFppfOver.topology`, not for
`AlgebraicGeometry.Space.SmallEtale.topology`, so it does not give the display above as it stands.

*The pinned instances.*  `HasDerivedCategory` is data, so the statements composed here are only
composable against the witness they were elaborated with;  the pin is
`AlgebraicGeometry.Space.chartwiseLocalityHasDerivedCategory`, reused from
`ChartwiseDerivedIsomorphismDetection.lean` exactly as
`ToposModuleDerivedBaseChangeChartwise.lean` reuses it.  The two exactness instances for the
inverse image along a chart are that file's
`AlgebraicGeometry.Space.chartwiseReductionPreservesFiniteLimits` and `…Colimits`, and the
additivity instance is `ChartwiseDerivedIsomorphismDetection.lean`'s
`chartwiseLocalityAdditiveModulePullback`;  all three are reused rather than restated.

*This is not Stacks 073K, part (1).*  Part (1) asserts invertibility of the base change map for a
cartesian square with `g` flat and `f` quasi-compact and quasi-separated.  Nothing below asserts
that any base change map is invertible:  the chart statements are implications whose hypothesis is
the chart-local case of part (1)'s conclusion, and the pasting statement is an implication between
invertibility of three base change maps.  No `@[stacks 073K]` attribute is carried, and the
part-(2) carrier `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` is
untouched.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules

-- The standard derived category of the `𝒪`-modules of an algebraic space, pinned so that it is
-- the witness instance search produces.  See the implementation notes: the chaotic comparison
-- instance is in this import closure and wins otherwise.
attribute [local instance] chartwiseLocalityHasDerivedCategory

attribute [local instance] chartwiseReductionPreservesFiniteLimits
attribute [local instance] chartwiseReductionPreservesFiniteColimits
attribute [local instance] chartwiseLocalityAdditiveModulePullback

/-! ### Detection on a family of charts with enough objects -/

section Detection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of étale charts with enough objects detects isomorphisms of `𝒪_Y`-modules.**  Let
`P` be a property of the étale scheme charts of `Y` such that every chart is covered by charts
with `P`.  A morphism of `𝒪_Y`-modules whose restriction along the structure morphism of every
chart with `P` is invertible is itself invertible.

This is `AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_affine_chartToSpace`
with the affine charts replaced by `P`; the proof is the same one, since
`Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app` already takes an arbitrary
property of objects of the site. -/
theorem isIso_of_forall_isIso_etaleModulePullback_chartToSpace_of_hasEnoughObjects
    (Y : AlgebraicSpaces B S hS) {P : ObjectProperty (SmallEtale B S hS Y.obj)}
    (hP : (SmallEtale.topology B S hS Y.obj).HasEnoughObjects P)
    {M N : Modules.{u, u} B S hS Y.obj Y.property} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS Y.obj, P V →
      IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).map φ)) :
    IsIso φ := by
  refine Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app φ hP
    fun V hV => ?_
  have hiso : IsIso (φ.val.app (op V)) := by
    rw [← etaleModulePullback_chartToSpace_map_val_app_idEtaleChart B S hS φ V]
    have := hφ V hV
    exact Stacks.SheafOfModules.isIso_val_app_of_isIso_freeModuleUniverse _ _
  exact ConcreteCategory.bijective_of_isIso (φ.val.app (op V))

/-- **A family of étale charts with enough objects detects isomorphisms in `D⁺(𝒪_Y)`.**  A
morphism of the bounded below derived category of `𝒪_Y`-modules whose image under the bounded
below right derived functor of the inverse image along the structure morphism of every chart with
`P` is invertible is itself invertible.

The passage from degree zero is the one of
`AlgebraicGeometry.Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace`: a morphism
of `D⁺` is invertible exactly when all of its cohomology maps are, and the inverse image along a
chart is exact, so its right derived functor carries the degree-`n` cohomology map of `φ` to the
degree-`n` cohomology map of the inverse image of `φ`.  The hypothesis therefore says that each
cohomology map of `φ` is invertible after inverse image along every chart with `P`, and the
degree-zero statement above concludes. -/
theorem isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace_of_hasEnoughObjects
    (Y : AlgebraicSpaces B S hS) {P : ObjectProperty (SmallEtale B S hS Y.obj)}
    (hP : (SmallEtale.topology B S hS Y.obj).HasEnoughObjects P)
    {K L : DerivedCategory.Plus (Modules.{u, u} B S hS Y.obj Y.property)} (φ : K ⟶ L)
    (h : ∀ V : SmallEtale B S hS Y.obj, P V →
      IsIso ((modulePullback B S hS (chartToSpace B S hS Y V)).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_etaleModulePullback_chartToSpace_of_hasEnoughObjects B S hS Y hP
    ((DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y.obj Y.property) n).map φ)
    fun V hV => ?_
  rw [← NatIso.isIso_map_iff
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y V)
      (isEtale_chartToSpace B S hS Y V))]
  exact Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map
    (modulePullback B S hS (chartToSpace B S hS Y V)) φ (h V hV) n

/-- **The affine étale charts alone detect isomorphisms in `D⁺(𝒪_Y)`.**  A morphism of
`D⁺(𝒪_Y)` whose image under the bounded below right derived functor of the inverse image along
the structure morphism of every étale scheme chart with affine underlying scheme is invertible is
itself invertible.

The affine charts have enough objects in the small étale topology
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`). -/
theorem isIso_of_forall_isIso_rightDerivedFunctorPlus_affine_chartToSpace
    (Y : AlgebraicSpaces B S hS)
    {K L : DerivedCategory.Plus (Modules.{u, u} B S hS Y.obj Y.property)} (φ : K ⟶ L)
    (h : ∀ V : SmallEtale B S hS Y.obj, IsAffineChart B S hS Y.obj V →
      IsIso ((modulePullback B S hS (chartToSpace B S hS Y V)).rightDerivedFunctorPlus.map φ)) :
    IsIso φ :=
  isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace_of_hasEnoughObjects B S hS Y
    (hasEnoughObjects_isAffineChart B S hS Y.obj) φ h

end Detection

/-! ### The reduction over a family of charts with enough objects -/

section Chartwise

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]

/-- **The base change map of Stacks 0736 is invertible as soon as it is chart-locally so over a
family of charts with enough objects.**  This is
`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart` with the
quantifier over all étale charts of `Y'` replaced by one over the charts with `P`, for any `P`
such that every chart of `Y'` is covered by charts with `P`.

It is not **Stacks 073K**, part (1):  its hypothesis is the chart-local case of part (1)'s
conclusion. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart_of_hasEnoughObjects
    (comm : g' ≫ f = f' ≫ g)
    {P : ObjectProperty (SmallEtale B S hS Y'.obj)}
    (hP : (SmallEtale.topology B S hS Y'.obj).HasEnoughObjects P)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hchart : ∀ V : SmallEtale B S hS Y'.obj, P V →
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
  refine isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace_of_hasEnoughObjects B S hS Y'
    hP ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) fun V hV => ?_
  obtain ⟨X'', f'', g'', comm', _, _, _, _, hrect, hsq⟩ := hchart V hV
  exact isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app f f' f'' g g'
    (chartToSpace B S hS Y' V) g'' comm comm' M hrect hsq

/-- **The base change map of Stacks 0736 is invertible as soon as it is invertible over the
affine étale charts of the base.**  The affine charts have enough objects, so this is the
previous statement at that family;  it is the form of the locality half of the reduction of
**Stacks 073K**, part (1) that can meet an affine case, since the charts it quantifies over are
affine schemes.

It is still not part (1):  the hypothesis is part (1)'s conclusion over the affine charts. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_of_forall_affine_chart
    (comm : g' ≫ f = f' ≫ g)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hchart : ∀ V : SmallEtale B S hS Y'.obj, IsAffineChart B S hS Y'.obj V →
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
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) :=
  isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart_of_hasEnoughObjects f g f' g' comm
    (hasEnoughObjects_isAffineChart B S hS Y'.obj) M hchart

end Chartwise

/-! ### Building a rectangle's base change map out of the two squares -/

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

/-- **Invertibility of the base change map of Stacks 0736 for a pasted rectangle, out of the two
squares it is pasted from.**  For two commutative squares of algebraic spaces sharing a vertical
edge, if the base change map of the left-hand square is invertible at `M` and the base change map
of the right-hand square is invertible at `(g')^*M`, then the base change map of the pasted
rectangle is invertible at `M`.

This is the direction of the pasting law
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_horizontal` opposite to
`AlgebraicGeometry.Space.isIso_rightDerivedFunctorPlus_map_toposModuleDerivedBaseChangeMap_app`:
that law writes the rectangle's map as a four-fold composite whose outer two factors are
isomorphisms unconditionally, whose second factor is the derived inverse image along `h` of the
left-hand square's map and whose third factor is the right-hand square's map.  Here all four are
invertible, so the composite is.

It is what a reduction of **Stacks 073K**, part (1) to an affine base consumes:  the base leg of
a rectangle over a chart of `Y'` is a composite, and the two squares it factors through are the
étale square of a chart of `Y` and a square over an affine base.  Nothing here asserts that any
of the three maps is invertible. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_paste (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hsquare : IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M))
    (hright : IsIso ((toposModuleDerivedBaseChangeMap f' h f'' g'' comm').app
      ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M))) :
    IsIso ((toposModuleDerivedBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).app M) := by
  rw [toposModuleDerivedBaseChangeMap_horizontal f f' f'' g g' h g'' comm comm' M]
  have := hsquare
  have := hright
  have : IsIso ((modulePullback B S hS h).rightDerivedFunctorPlus.map
      ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M)) := Functor.map_isIso _ _
  infer_instance

end Paste

end AlgebraicGeometry.Space

end
