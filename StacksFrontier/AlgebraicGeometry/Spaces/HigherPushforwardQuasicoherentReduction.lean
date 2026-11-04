module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction

/-!
# Quasi-coherence of the higher direct images: the reduction to an affine base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 0720 asserts that if `f` is quasi-compact and quasi-separated then every
higher direct image `R^i f_*` carries quasi-coherent `𝒪_X`-modules to quasi-coherent
`𝒪_Y`-modules; its degree-zero case is Stacks 03M9.  This file carries out the *first step* of
that proof — the reduction to the case of an affine base — for every degree `i` at once, and in
the reading in which the remaining steps of the source's argument are statements about modules
on the small étale site of an algebraic space.

The reduction is: quasi-coherence of a module on the small étale site of `Y` is tested on the
restrictions to the affine étale scheme charts `V` of `Y` (Stacks 03M0, condition (4), in the
pullback form `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_forall_affine_chart`), and on
such a chart the restriction of `R^i f_*F` is `R^i f'_*(F|_U)` for `U = V ×_Y X` and `f'` the
base change of `f` — the higher-direct-image clause of Stacks 03LX for the cartesian square

```
U  --ι--> X
|f'       |f
V  --g--> Y
```

whose bottom arrow `g` is the étale structure morphism of the chart.  In degree zero that
clause is proved unconditionally, so the degree-zero reduction below is unconditional; in higher
degree it is `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso`, which is
proved unconditionally as well.  The statements below nevertheless carry the
injective-preservation half of Stacks 03F3 for `ι` as the hypothesis `h03F3` and consume the
conditional form
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`;
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` discharges it.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeSpace` is the algebraic space `U = V ×_Y X` attached
  to an étale scheme chart `V` of `Y`, and
  `AlgebraicGeometry.Space.chartBaseChangeInclusion` its étale structure morphism `ι : U ⟶ X`.
* `AlgebraicGeometry.Space.ChartwiseIsQuasicoherentHigherDirectImage` is the hypothesis
  `haffine`: quasi-coherence of the degree-`n` higher direct image of `F|_U` along the base
  change of `f` to every affine étale scheme chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartBaseChangeInclusion`: the base change of a morphism
  of algebraic spaces at an étale scheme chart of its target is a cartesian square *of
  algebraic spaces*, with the chart's structure morphism as its bottom arrow.
* `AlgebraicGeometry.Space.isEtale_chartBaseChangeInclusion`: the top arrow `ι : U ⟶ X` of that
  square is étale.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_iff_forall_affine_chart`:
  the degree-zero reduction, an unconditional equivalence.
* `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_forall_affine_chart`: Stacks
  03M9 in the binders of its source statement, conditional on its affine-base case.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart`: the same
  two statements in arbitrary degree, conditional in addition on `h03F3`.  The second is the
  first step of the proof of Stacks 0720 in the binders of its source statement.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise_of_representable`:
  for a *representable* morphism the arbitrary-degree reduction carries nothing beyond the
  affine case, since there the chartwise identification is Stacks 071Z.

## Implementation notes

**No `@[stacks 0720]` or `@[stacks 03M9]` attribute is carried here.**  What is proved is the
first step of the source's proof, the reduction to an affine base in every degree; the
affine-base case is the hypothesis `haffine`, which is Stacks 0720's own content.  Stacks 0720
with it discharged is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`, and Stacks 03M9
is `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`, which consumes the
degree-zero reduction of this file.

*Why the reduction is taken in the pullback reading and not in the slice reading.*  In the
slice reading, `F|_U` is restriction to the slice of the *spaces-étale* site of `X` at `U` and
`f'_*` the direct image along the localized base-change functor, as
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso` (Stacks 04CF) delivers; there the
reduction cannot be continued, because the citations of the second step are statements about
modules on the small étale site of an algebraic space and the slice of `X_{spaces,étale}` at `U`
is not identified with the small étale site of `U`.  The obstruction is avoided here by routing
through Stacks 03LX instead: the objects of the spaces-étale site of `X` are algebraic spaces
over `X`, so `ι : U ⟶ X` is an honest étale morphism of algebraic spaces and `F|_U` can be taken
to be `AlgebraicGeometry.Space.etaleModulePullback` along it, after which `f'_*` is
`AlgebraicGeometry.Space.modulePushforward` of a morphism of algebraic spaces and the restriction
of the conclusion to the chart is read through the same pullback by Stacks 03M0, condition (4),
in the form `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_forall_affine_chart`.  Every
citation of the second step then applies to `f'_*(F|_U)` on the nose.

*What `h03F3` is, and why degree zero does not need it.*  The degree-zero clause of Stacks 03LX
is `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, which is proved with no
hypothesis.  The higher-degree clause is obtained from it by base change for right derived
functors, which needs the restriction along `ι` to carry injective modules to injective modules
— Stacks 03F3, part (1), at the small étale site.  For the structure morphism of an étale scheme
*chart* that is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback_chartToSpace`, which
routes through the comparison equivalence of Stacks 04M0, and `U = V ×_Y X` is an algebraic
space and not a scheme chart of `X` unless `f` is representable; for an arbitrary étale morphism
it is `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`.  It is carried as
a hypothesis in the statements below.  For a representable `f` the whole square is a square of
charts, as `AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso` (Stacks 071Z).

*What the hypotheses on `f` are used for.*  Quasi-compactness and quasi-separatedness of `f` are
consumed in the two statements phrased in the binders of the source: they produce
quasi-compactness and quasi-separatedness of the base-changed morphism `f'` (Stacks 03HF and
Stacks 03KL, part (3)) and quasi-compactness of `U` over an affine chart, which are the
hypotheses the affine case takes, and they are supplied by
`AlgebraicGeometry.Space.isQuasiCompact_chartBaseChangeProjection`,
`AlgebraicGeometry.Space.isQuasiSeparated_chartBaseChangeProjection` and
`AlgebraicGeometry.Space.isQuasiCompactSpace_chartBaseChange`.  From the last of these the
affine surjective étale chart on `U` that the second step feeds to Stacks 03M8 is
`AlgebraicGeometry.Space.exists_affine_etale_surjective_chart_chartBaseChange`, Stacks 03H6.
The reductions themselves use neither hypothesis, and neither uses quasi-coherence of `F`.

*The inherited caveat.*  The isomorphisms of Stacks 03LX used here have the right endpoints but
are not identified with the canonical base-change comparison maps.  The caveat does not
propagate: the conclusions here are quasi-coherence of an object, and quasi-coherence transports
along an arbitrary isomorphism by `SheafOfModules.IsQuasicoherentOnSite.of_iso`.

*The module universe* is the universe `u` of the schemes and not a free module universe, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.  *The degree* runs over `ℕ` in
the injective-resolution convention `CategoryTheory.Functor.rightDerived`, which is the
convention the source's proof is written in.

*The two local priority raises*: with the module-universe-`max u v r w` instances in the import
closure, instance search for `Abelian` and for `EnoughInjectives` on the modules at module
universe `u` commits to them and then fails on the universe constraint.  Both attributes are
`local`, so no global instance is declared.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The base change at an étale chart as a cartesian square of algebraic spaces -/

/-- The algebraic space `U = V ×_Y X` attached to an étale scheme chart `V` of `Y`.

This is the object `AlgebraicGeometry.Space.chartBaseChange` of the spaces-étale site of `X`,
read as an algebraic space over `S`. -/
noncomputable abbrev chartBaseChangeSpace (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    AlgebraicSpaces B S hS :=
  (SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)

/-- The structure morphism `ι : U ⟶ X` of the algebraic space `U = V ×_Y X` over `X`. -/
noncomputable abbrev chartBaseChangeInclusion (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    chartBaseChangeSpace B S hS f V ⟶ X :=
  (chartBaseChange B S hS f V).1.hom

/-- **The base change at an étale chart is cartesian, as a square of algebraic spaces.** For a
morphism `f : X ⟶ Y` of algebraic spaces and an étale scheme chart `V` of `Y`, the algebraic
space `U = V ×_Y X` is the fibre product of `f` and the structure morphism of `V`.

This is the `isPullback` field of the base-change datum
`AlgebraicGeometry.Space.spacesBaseChange` at the object of the spaces-étale site of `Y`
attached to `V` by the comparison functor of Stacks 03G1.  Unlike
`AlgebraicGeometry.Space.isPullback_chartBaseChangeProjection`, which transports the same datum
to presheaves, this is a cartesian square in the category of algebraic spaces over `S`, which is
what the base-change clauses of Stacks 03LX consume. -/
theorem isPullback_chartBaseChangeInclusion (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    IsPullback (chartBaseChangeInclusion B S hS f V) (chartBaseChangeProjection B S hS f V) f
      (chartToSpace B S hS Y V) :=
  ((spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj V)).flip

/-- The structure morphism `ι : V ×_Y X ⟶ X` is étale, being a base change of the étale
structure morphism of the chart `V`. -/
theorem isEtale_chartBaseChangeInclusion (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    IsEtale B S hS (chartBaseChangeInclusion B S hS f V).hom :=
  isEtale_of_isPullback B S hS _ _ _ _
    (isPullback_chartBaseChangeInclusion B S hS f V).flip (isEtale_chartToSpace B S hS Y V)

/-- The restriction `F ↦ F|_U` of modules to the algebraic space `U = V ×_Y X`, along the étale
structure morphism `ι : U ⟶ X`. -/
noncomputable abbrev chartBaseChangeModulePullback (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      Modules.{u, u} B S hS (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2 :=
  etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
    (isEtale_chartBaseChangeInclusion B S hS f V)

/-! ### The degree-zero reduction -/

/-- **The first step of the proof of Stacks 03M9, in the pullback reading.** The direct image
`f_*F` of an `𝒪_X`-module along an arbitrary morphism of algebraic spaces is quasi-coherent
exactly when, for every affine étale scheme chart `V` of `Y`, the direct image `f'_*(F|_U)` along
the base change `f' : U ⟶ V` of `f` is quasi-coherent, where `U = V ×_Y X` and `F|_U` is the
restriction of `F` along the étale structure morphism `U ⟶ X`.

Quasi-coherence is tested on the affine étale charts by Stacks 03M0, condition (4), in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_forall_affine_chart`, and the restriction of
`f_*F` to such a chart is identified with `f'_*(F|_U)` by the ordinary-direct-image clause of
Stacks 03LX, `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, applied to the
cartesian square of `AlgebraicGeometry.Space.isPullback_chartBaseChangeInclusion`.  The forward
implication needs no affineness, since quasi-coherence is inherited by every étale pullback.
No hypothesis on `f` and no quasi-coherence of `F` is used. -/
theorem isQuasicoherentOnSite_modulePushforward_iff_forall_affine_chart (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite ↔
      ∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS Y.1).obj V)) →
        ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
          ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite := by
  have e (V : SmallEtale B S hS Y.1) :=
    (modulePushforwardEtaleBaseChangeIso B S hS (chartBaseChangeInclusion B S hS f V)
      (chartBaseChangeProjection B S hS f V) f (chartToSpace B S hS Y V)
      (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)).app F
  refine ⟨fun h V _ ↦ ?_, fun h ↦ ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso (e V).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V) _ h)
  · exact isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun V hV ↦
      SheafOfModules.IsQuasicoherentOnSite.of_iso (e V) (h V hV)

/-- **Stacks 03M9, conditional on its affine-base case, in the pullback reading.** Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let
`F` be a quasi-coherent `𝒪_X`-module on the small étale site of `X`.  Then `f_*F` is
quasi-coherent, granted `haffine`: the same conclusion for the base change of `f` at every
affine étale scheme chart of `Y`.

The quasi-compactness and quasi-separatedness of the base-changed morphism and the
quasi-compactness of its source, which `haffine` takes as hypotheses, are supplied here from
those of `f` by Stacks 03HF, Stacks 03KL, part (3), and Stacks 03HE; the affine surjective étale
chart on `U` that the second step of the source's argument consumes follows from the last of
them by Stacks 03H6,
`AlgebraicGeometry.Space.exists_affine_etale_surjective_chart_chartBaseChange`.  **This is not a
proof of Stacks 03M9**: `haffine` holds the whole of the second step, and no `@[stacks 03M9]`
attribute is carried. -/
theorem pushforward_isQuasicoherentOnSite_of_forall_affine_chart (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (haffine : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 →
      ((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_modulePushforward_iff_forall_affine_chart B S hS f F).2 fun V hV ↦
    haffine V hV (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)

/-! ### The reduction in arbitrary degree -/

/-- The hypothesis `haffine` of the two theorems below: for every affine étale scheme chart `V`
of `Y` the degree-`n` higher direct image of `F|_U` along the base change `f' : U ⟶ V` of `f` is
quasi-coherent, where `U = V ×_Y X`.

For a quasi-compact and quasi-separated `f` and a quasi-coherent `F` this is the case of an
affine base of Stacks 0720, which is the whole mathematical content of that tag. -/
def ChartwiseIsQuasicoherentHigherDirectImage (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) : Prop :=
  ∀ V : SmallEtale B S hS Y.1,
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
    have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
      (chartBaseChangeSpace B S hS f V).2
    (((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).rightDerived n).obj
      ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite

/-- **The first step of the proof of Stacks 0720, with `h03F3` carried.** If for every affine
étale scheme chart `V` of `Y` the degree-`n` higher direct image `R^n f'_*(F|_U)` along the base
change `f' : U ⟶ V` of `f` is quasi-coherent, then so is `R^n f_*F` — given that the restriction
of modules along the étale structure morphism `U ⟶ X` carries injective `𝒪_X`-modules to
injective `𝒪_U`-modules for each such chart.

That last statement is Stacks 03F3, part (1), for the modules on the small étale site, which
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` proves; it is carried
here as `h03F3` and fed to
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`, from
which the chartwise identification is taken. Quasi-coherence is then tested on the affine étale
charts by Stacks 03M0, condition (4). -/
theorem isQuasicoherentOnSite_rightDerived_of_chartwise (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (h03F3 : ∀ V : SmallEtale B S hS Y.1,
      (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects)
    (haffine : ChartwiseIsQuasicoherentHigherDirectImage B S hS f F n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun V hV ↦ ?_
  have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
    (chartBaseChangeSpace B S hS f V).2
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives B S hS
      (chartBaseChangeInclusion B S hS f V)
      (chartBaseChangeProjection B S hS f V) f (chartToSpace B S hS Y V)
      (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)
      (h03F3 V) n).app F) (haffine V hV)

/-- **Stacks 0720, the first step of the source's proof: the reduction to an affine base.** Let
`f : X ⟶ Y` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let `F`
be a quasi-coherent `𝒪_X`-module on the small étale site of `X`.  Then `R^n f_*F` is
quasi-coherent, granted `h03F3` and `haffine`: the same conclusion for the base change of `f` at
every affine étale scheme chart of `Y`.

As in degree zero the quasi-compactness and quasi-separatedness of the base-changed morphism and
the quasi-compactness of its source are supplied here from those of `f`, by Stacks 03HF,
Stacks 03KL, part (3), and Stacks 03HE.  The second step of the source's argument, its affine
base case, is `haffine`. -/
theorem isQuasicoherentOnSite_rightDerived_of_forall_affine_chart (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (n : ℕ)
    (h03F3 : ∀ V : SmallEtale B S hS Y.1,
      (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects)
    (haffine : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
      IsQuasiCompactSpace B S hS (chartBaseChangeSpace B S hS f V).1 →
      have := hasInjectiveResolutions_modules B S hS (chartBaseChangeSpace B S hS f V).1
        (chartBaseChangeSpace B S hS f V).2
      (((modulePushforward B S hS (chartBaseChangeProjection B S hS f V)).rightDerived n).obj
        ((chartBaseChangeModulePullback B S hS f V).obj F)).IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_chartwise B S hS f F n h03F3
    fun V hV ↦ haffine V hV (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)

/-- **The first step of the proof of Stacks 0720 for a representable morphism,
unconditionally.** If `f : X ⟶ Y` is a representable morphism of algebraic spaces and, for every
affine étale scheme chart `V` of `Y`, the degree-`n` higher direct image `R^n f'_*(F|_U)` along
the base change `f' : U ⟶ V` of `f` to the pullback chart `U = V ×_Y X` is quasi-coherent, then
so is `R^n f_*F`.

Representability is what makes `U` an étale scheme *chart* of `X`, so the chartwise
identification is Equation 69.3.0.1 of the source, Stacks 071Z
(`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`), in which the
injective-preservation half of Stacks 03F3 is discharged.  Nothing is carried here beyond the
affine case itself; the hypothesis `h03F3` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_chartwise` is
needed only because for a general `f` the fibre product `U` is an algebraic space rather than a
scheme chart.  The source states Stacks 0720 for a quasi-compact and quasi-separated `f` and a
quasi-coherent `F`; the reduction uses neither, so both are left out. -/
theorem isQuasicoherentOnSite_rightDerived_of_chartwise_of_representable
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (haffine : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      have := hasInjectiveResolutions_modules B S hS
        (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1
        (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).2
      (((modulePushforward B S hS (smallBaseChangeChartMap B S hS f hf V)).rightDerived n).obj
        ((etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
          (isEtale_chartToSpace B S hS X
            ((smallBaseChange B S hS f hf).obj V))).obj F)).IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun V hV ↦ ?_
  have := hasInjectiveResolutions_modules B S hS
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).2
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((moduleHigherPushforwardChartBaseChangeIso B S hS f hf V n).app F) (haffine V hV)

end AlgebraicGeometry.Space

end
