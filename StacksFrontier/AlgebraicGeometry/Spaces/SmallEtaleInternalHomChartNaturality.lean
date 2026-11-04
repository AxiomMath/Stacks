module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekContinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCompEq
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# Chart restriction of modules at two charts, strictly

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B` and let `w : V ⟶ U` be a
morphism of étale scheme charts of `X`.  The restriction of an `𝒪_X`-module to the small étale
site of a chart, `AlgebraicGeometry.Space.chartSmallEtaleRestriction`, is then available at both
charts, and the two readings are compared by restricting the one at `U` along the represented
morphism `chartSpace V ⟶ chartSpace U` of chart spaces.

**This file shows that comparison is an equality, not merely an isomorphism**, in the *strict*
form of Equation [Stacks Project, Tag 03LW]: the restriction used is
`AlgebraicGeometry.Space.etaleModulePullback`, which is `CategoryTheory.SheafOfModules.pushforward`
along postcomposition of charts, and not the adjoint inverse image
`AlgebraicGeometry.Space.modulePullback` of [Stacks Project, Tag 03LU].

## Main results

* `AlgebraicGeometry.Space.chartLocalization_smallEtalePostcomp_obj`: **the comparison functor of
  [Stacks Project, Tag 04M0] turns postcomposition of charts into `CategoryTheory.Over.map`, on
  objects and on the nose.**  An étale chart of the chart space of `V`, pushed to a chart of the
  chart space of `U` and then read in the slice of the small étale site of `X` at `U`, *is* the
  chart read in the slice at `V` and pushed along `w`.
* `AlgebraicGeometry.Space.smallEtalePostcomp_comp_chartLocalization`: the same as an equality of
  functors, which strengthens `AlgebraicGeometry.Space.chartLocalizationPostcompIso` from a
  natural isomorphism to an equality.
* `AlgebraicGeometry.Space.chartSmallEtaleRestriction_eq_etaleModulePullback_obj`: the chart
  restriction of an `𝒪_X`-module is its étale restriction along the structure morphism of the
  chart.
* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionEtaleModulePullbackEq`: **Equation
  [Stacks Project, Tag 03LW] at two charts, strictly** — the étale restriction along the
  represented morphism of chart spaces of the chart restriction at `U` *equals* the chart
  restriction at `V`.
* `AlgebraicGeometry.Space.etaleModulePullback_obj_comp`: étale restriction of modules composes on
  the nose on objects.
* `AlgebraicGeometry.Space.overMap_comp_chartLocalizationPushforward_eq`: **the commuting square
  of the naturality step of [Stacks Project, Tag 04AM], as an equality of functors** — restricting
  an `𝒪_X`-module to the slice at `V` and reading it on the small étale site of the chart space of
  `V` equals reading it at `U` and restricting along the represented morphism of chart spaces.
* `AlgebraicGeometry.Space.overMap_comp_chartLocalizationPushforward_map_heq`: the same square on
  morphisms, necessarily as a heterogeneous equation.

## Why the strict form

The comparison of the two chart restrictions is already in the tree against the *adjoint* inverse
image, as `AlgebraicGeometry.Space.chartSmallEtaleRestrictionPullbackIso` (Equation
[Stacks Project, Tag 03LY]) and, at the respelling, as
`AlgebraicGeometry.Space.modulePullbackChartMapEtaleModulePullbackIso`.  Both are built on
`AlgebraicGeometry.Space.modulePullbackCompIso`, so relating either to a reindexing of sheaves of
modules is
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, which this
development does not have: it is reduced to an equality of two units by
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` and otherwise carried only
as a hypothesis.  Everything in this file is pushforward-only, so that coherence does not arise
and no hypothesis is carried.

## Implementation notes

The two spellings `AlgebraicGeometry.Space.Modules` and
`CategoryTheory.SheafOfModules.{u} (AlgebraicGeometry.Space.structureRingSheaf …)` of one category
— the difference recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent` — decide how these proofs
have to be written.  Each individual crossing is `rfl` and cheap, but *two* of them inside one
`rfl` is a 200 000-heartbeat `whnf` timeout, both for the object equality of
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionEtaleModulePullbackEq` proved in one step and
for `AlgebraicGeometry.Space.etaleModulePullback_obj_comp` stated directly at the
`structureRingSheaf` spelling.  So the comparison is assembled from *stated* steps composed with
`Eq.trans`, and the composition law is stated once at the `AlgebraicGeometry.Space.Modules`
spelling and applied; the application is cheap.  For the same reason the composition law is
available on objects only: the corresponding equality of *functors* is a `whnf` timeout, which is
why the tree carries `AlgebraicGeometry.Space.etaleModulePullbackComp` as an isomorphism.

`AlgebraicGeometry.Space.chartLocalization_smallEtalePostcomp_obj` needs no transport.  The two
slice objects have the same underlying object of the big fppf site, and their structure maps to
`X` agree by the commuting triangle `CategoryTheory.CostructuredArrow.w` of `w`; since the
étale-chart property is a proposition and a costructured arrow is its own constructor, substituting
that equality of structure maps makes the two objects definitionally equal, which is what
`AlgebraicGeometry.Space.over_mk_eq_of_hom_eq` packages.  `aesop_cat` does not find this.

No `@[stacks]` attribute is claimed: Tag 04M0 is registered at the comparison equivalence and
Tag 03LW where the identification is built, and these are interior steps of
[Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An object of a slice category over an object of a full subcategory of a costructured-arrow
category is determined by the structure map of its source together with the underlying morphism of
its structure morphism.**  The property cutting out the subcategory is a proposition and a
costructured arrow is its own constructor, so an equality of the two structure maps can be
substituted and the two objects become definitionally equal. -/
theorem over_mk_eq_of_hom_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {T : D}
    {P : ObjectProperty (CostructuredArrow F T)} {A : P.FullSubcategory}
    {Y : C} {f g : F.obj Y ⟶ T} (h : f = g)
    {pf : P (CostructuredArrow.mk f)} {pg : P (CostructuredArrow.mk g)}
    (k : (⟨CostructuredArrow.mk f, pf⟩ : P.FullSubcategory) ⟶ A)
    (k' : (⟨CostructuredArrow.mk g, pg⟩ : P.FullSubcategory) ⟶ A)
    (hk : k.hom.left = k'.hom.left) :
    (Over.mk k : Over A) = Over.mk k' := by
  subst h
  exact congrArg Over.mk (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hk))

/-- **Étale restriction of modules composes on the nose, on objects**: restricting an
`𝒪_W`-module along an étale `g : Z ⟶ W` and then along an étale `f : Y ⟶ Z` gives the restriction
along `f ≫ g`.  Étale restriction is restriction of sections along postcomposition of charts,
which is strictly functorial.

Stated at the `AlgebraicGeometry.Space.Modules` spelling of the module category because at the
`AlgebraicGeometry.Space.structureRingSheaf` spelling the same `rfl` does not elaborate; see the
implementation notes.  Only the equality of *objects* is available: the corresponding equality of
functors is a `whnf` timeout, and that is what
`AlgebraicGeometry.Space.etaleModulePullbackComp` is for. -/
theorem etaleModulePullback_obj_comp {Y Z W : AlgebraicSpaces B S hS} (f : Y ⟶ Z) (g : Z ⟶ W)
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) (M : Modules.{u, u} B S hS W.1 W.2) :
    (etaleModulePullback.{u, u} B S hS f hf).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M) =
      (etaleModulePullback.{u, u} B S hS (f ≫ g) hfg).obj M :=
  rfl

variable (X : AlgebraicSpaces B S hS)

/-- **The comparison functor of [Stacks Project, Tag 04M0] turns postcomposition of charts into
`CategoryTheory.Over.map`, on the nose.**  Let `w : V ⟶ U` be a morphism of étale scheme charts of
`X` and let `W` be an étale chart of the chart space of `V`.  Pushing `W` forward to a chart of the
chart space of `U` and then reading it in the slice of the small étale site of `X` at `U` gives
*the same object* as reading `W` in the slice at `V` and pushing it along `w`.

This is the object-level equality underlying
`AlgebraicGeometry.Space.chartLocalizationPostcompIso`, which only provides an isomorphism — its
component is the identity on the underlying object of the big fppf site together with a proof for
the structure map.  The equality needs no transport: the two structure maps agree by the commuting
triangle `CategoryTheory.CostructuredArrow.w` of `w`, and
`AlgebraicGeometry.Space.over_mk_eq_of_hom_eq` turns that agreement into the equality of
objects. -/
theorem chartLocalization_smallEtalePostcomp_obj {V U : SmallEtale B S hS X.1} (w : V ⟶ U)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1) :
    (SmallEtale.chartLocalization B S hS X.1 U).obj
        ((smallEtalePostcomp B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)).obj W) =
      (Over.map w).obj ((SmallEtale.chartLocalization B S hS X.1 V).obj W) :=
  (over_mk_eq_of_hom_eq
    (((Category.assoc W.obj.hom (yoneda.map ((SmallEtale.toOver B S hS X.1).map w))
        U.obj.hom).trans
      (congrArg (fun t => W.obj.hom ≫ t) (CostructuredArrow.w w.hom))).symm) _ _ rfl).symm

/-- **The comparison of [Stacks Project, Tag 04M0] turns postcomposition of charts into
`CategoryTheory.Over.map`, as an equality of functors.**  This strengthens
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` from a natural isomorphism to an equality:
the two functors agree on objects by
`AlgebraicGeometry.Space.chartLocalization_smallEtalePostcomp_obj`, and on morphisms because a
morphism of the small étale site of `X` is determined by the underlying morphism of the big fppf
site, which neither reading changes. -/
theorem smallEtalePostcomp_comp_chartLocalization {V U : SmallEtale B S hS X.1} (w : V ⟶ U) :
    smallEtalePostcomp B S hS (chartMap B S hS X w) (isEtale_chartMap B S hS X w) ⋙
        SmallEtale.chartLocalization B S hS X.1 U =
      SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map w :=
  CategoryTheory.Functor.ext fun W => chartLocalization_smallEtalePostcomp_obj B S hS X w W

/-- **The chart restriction of an `𝒪_X`-module is its étale restriction along the structure
morphism of the chart**, by `rfl`: restriction to the slice of the small étale site of `X` at a
chart followed by the comparison of [Stacks Project, Tag 04M0] is restriction along the comparison
followed by the slice projection, and that composite is postcomposition with the structure
morphism of the chart, `AlgebraicGeometry.Space.chartLocalization_comp_forget`. -/
theorem chartSmallEtaleRestriction_eq_etaleModulePullback_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1) :
    chartSmallEtaleRestriction B S hS X M A =
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A)).obj M :=
  rfl

/-- **Equation [Stacks Project, Tag 03LW] at two charts, strictly.**  For a morphism `w : V ⟶ U`
of étale scheme charts of `X`, the étale restriction along the represented morphism of chart
spaces of the chart restriction of an `𝒪_X`-module at `U` *equals* its chart restriction at `V`.

Everything entering is pushforward-only — `AlgebraicGeometry.Space.etaleModulePullback` is
`CategoryTheory.SheafOfModules.pushforward` along postcomposition of charts — so the adjoint
inverse image of [Stacks Project, Tag 03LU] never appears and the coherence
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, which this
development does not have, is not needed.  Contrast
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionPullbackIso` and
`AlgebraicGeometry.Space.modulePullbackChartMapEtaleModulePullbackIso`, which compare the same two
chart restrictions across the *adjoint* inverse image and are therefore only isomorphisms, built
on `AlgebraicGeometry.Space.modulePullbackCompIso`.

The proof is the junction with étale restriction, the composition law on objects, and transport
along `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` — each as a stated step, for the reason
in the implementation notes. -/
theorem chartSmallEtaleRestrictionEtaleModulePullbackEq
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {V U : SmallEtale B S hS X.1} (w : V ⟶ U) :
    (etaleModulePullback.{u, u} B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)).obj (chartSmallEtaleRestriction B S hS X M U) =
      chartSmallEtaleRestriction B S hS X M V :=
  (congrArg (etaleModulePullback.{u, u} B S hS (chartMap B S hS X w)
        (isEtale_chartMap B S hS X w)).obj
      (chartSmallEtaleRestriction_eq_etaleModulePullback_obj B S hS X M U)).trans
    ((etaleModulePullback_obj_comp B S hS (chartMap B S hS X w) (chartToSpace B S hS X U)
        (isEtale_chartMap B S hS X w) (isEtale_chartToSpace B S hS X U)
        (isEtale_chartMap_comp_chartToSpace B S hS X w) M).trans
      ((Functor.congr_obj (etaleModulePullback_congr B S hS
          (isEtale_chartMap_comp_chartToSpace B S hS X w)
          (isEtale_chartToSpace B S hS X V)
          (chartMap_comp_chartToSpace B S hS X w)) M).trans
        (chartSmallEtaleRestriction_eq_etaleModulePullback_obj B S hS X M V).symm))

section ChartNaturality

variable {V U : SmallEtale B S hS X.1} (w : V ⟶ U)

/-- **The left-hand leg of the square, contracted.**  Restricting an `𝒪_X`-module from the slice
of the small étale site of `X` at `U` to the slice at `V`, and then reading it on the small étale
site of the chart space of `V`, is restriction along the single functor of sites
`chartLocalization V ⋙ Over.map w`.

Both legs are `CategoryTheory.SheafOfModules.pushforward` with the identity structure map — for
`CategoryTheory.SheafOfModules.overMap` because `CategoryTheory.Sheaf.pushforwardOverMapIso` is
the identity — so this is `Stacks.SheafOfModules.pushforwardComp_id_eq`.  The contraction is
cheap precisely because that lemma's `rfl` is checked at generic functors of sites; the same
`rfl` written here is a `whnf` timeout. -/
theorem overMap_comp_chartLocalizationPushforward_eq_pushforward :
    SheafOfModules.overMap (structureRingSheaf B S hS X) w ⋙ (@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          (SmallEtale.chartLocalization B S hS X.1 V)
          (chartStructureRingSheaf B S hS X V)
          ((structureRingSheaf B S hS X).over V)
          (isContinuous_chartLocalization_chartSpace B S hS X V)
          (𝟙 _)) =
      (@SheafOfModules.pushforward _ _ _ _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)
        ((SmallEtale.chartLocalization B S hS X.1 V) ⋙ Over.map w)
        (chartStructureRingSheaf B S hS X V)
        ((structureRingSheaf B S hS X).over U)
        (@Functor.isContinuous_comp _ _ _ _ _ _
          (SmallEtale.chartLocalization B S hS X.1 V) (Over.map w)
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          ((SmallEtale.topology B S hS X.1).over U)
          (isContinuous_chartLocalization_chartSpace B S hS X V) inferInstance)
        (𝟙 _)) :=
  @Stacks.SheafOfModules.pushforwardComp_id_eq _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_chartLocalization_chartSpace B S hS X V) inferInstance _ _ _

/-- **The right-hand leg of the square, contracted.**  Reading an `𝒪_X`-module on the small
étale site of the chart space of `U` and then restricting it along the represented morphism of
chart spaces is restriction along the single functor of sites
`smallEtalePostcomp (chartMap w) ⋙ chartLocalization U`.

`AlgebraicGeometry.Space.etaleModulePullback` is `CategoryTheory.SheafOfModules.pushforward` with
the identity structure map, so this is again
`Stacks.SheafOfModules.pushforwardComp_id_eq`. -/
theorem chartLocalizationPushforward_comp_etaleModulePullback_eq_pushforward :
    (@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)
          (SmallEtale.chartLocalization B S hS X.1 U)
          (chartStructureRingSheaf B S hS X U)
          ((structureRingSheaf B S hS X).over U)
          (isContinuous_chartLocalization_chartSpace B S hS X U)
          (𝟙 _)) ⋙
        (etaleModulePullback.{u, u} B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)) =
      (@SheafOfModules.pushforward _ _ _ _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)
        ((smallEtalePostcomp B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)) ⋙
          (SmallEtale.chartLocalization B S hS X.1 U))
        (chartStructureRingSheaf B S hS X V)
        ((structureRingSheaf B S hS X).over U)
        (@Functor.isContinuous_comp _ _ _ _ _ _
          (smallEtalePostcomp B S hS (chartMap B S hS X w) (isEtale_chartMap B S hS X w))
          (SmallEtale.chartLocalization B S hS X.1 U)
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)
          inferInstance (isContinuous_chartLocalization_chartSpace B S hS X U))
        (𝟙 _)) :=
  @Stacks.SheafOfModules.pushforwardComp_id_eq _ _ _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1) _ _
    (smallEtalePostcomp B S hS (chartMap B S hS X w) (isEtale_chartMap B S hS X w)) _
    inferInstance (isContinuous_chartLocalization_chartSpace B S hS X U) _ _ _

/-- **The two contracted legs agree**: restriction of `𝒪_X`-modules along
`chartLocalization V ⋙ Over.map w` is restriction along
`smallEtalePostcomp (chartMap w) ⋙ chartLocalization U`.

The two functors of sites are equal by
`AlgebraicGeometry.Space.smallEtalePostcomp_comp_chartLocalization`, and the identity structure
map is carried across that equality by `Stacks.SheafOfModules.pushforward_eq_of_heq`.  The
heterogeneous equation of structure maps is `HEq.rfl`: the two functors of sites have
*definitionally equal* direct images of the restriction of `𝒪_X` to `U`, because a chart of the
chart space of `V` has the same ring of regular functions whichever of the two routes reads it in
the slice at `U`.

The *section modules* are not identified here, and cannot be: at a chart of the chart space of
`V` the two readings give modules over propositionally distinct rings, so there is no equality of
`ModuleCat`s to state.  Only the structure sheaves, where the two readings agree definitionally,
are compared. -/
theorem pushforward_chartLocalization_comp_overMap_eq :
    (@SheafOfModules.pushforward _ _ _ _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)
        ((SmallEtale.chartLocalization B S hS X.1 V) ⋙ Over.map w)
        (chartStructureRingSheaf B S hS X V)
        ((structureRingSheaf B S hS X).over U)
        (@Functor.isContinuous_comp _ _ _ _ _ _
          (SmallEtale.chartLocalization B S hS X.1 V) (Over.map w)
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          ((SmallEtale.topology B S hS X.1).over U)
          (isContinuous_chartLocalization_chartSpace B S hS X V) inferInstance)
        (𝟙 _)) =
      (@SheafOfModules.pushforward _ _ _ _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)
        ((smallEtalePostcomp B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)) ⋙
          (SmallEtale.chartLocalization B S hS X.1 U))
        (chartStructureRingSheaf B S hS X V)
        ((structureRingSheaf B S hS X).over U)
        (@Functor.isContinuous_comp _ _ _ _ _ _
          (smallEtalePostcomp B S hS (chartMap B S hS X w) (isEtale_chartMap B S hS X w))
          (SmallEtale.chartLocalization B S hS X.1 U)
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)
          inferInstance (isContinuous_chartLocalization_chartSpace B S hS X U))
        (𝟙 _)) :=
  @Stacks.SheafOfModules.pushforward_eq_of_heq _ _ _ _ _ _ _ _
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
      (isContinuous_chartLocalization_chartSpace B S hS X V) inferInstance)
    (@Functor.isContinuous_comp _ _ _ _ _ _
      (smallEtalePostcomp B S hS (chartMap B S hS X w) (isEtale_chartMap B S hS X w)) _ _ _ _
      inferInstance (isContinuous_chartLocalization_chartSpace B S hS X U))
    (smallEtalePostcomp_comp_chartLocalization B S hS X w).symm _ _ _ _ HEq.rfl

/-- **The commuting square of the naturality step of [Stacks Project, Tag 04AM], strictly.**  For
a morphism `w : V ⟶ U` of étale scheme charts of `X`, restricting an `𝒪_X`-module to the slice of
the small étale site of `X` at `V` and reading it on the small étale site of the chart space of
`V` *equals* reading it at `U` and restricting along the represented morphism of chart spaces.

This is the functor-level form of
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionEtaleModulePullbackEq`, which gives the same
identification on objects only.  Everything entering is pushforward-only, so the adjoint inverse
image of [Stacks Project, Tag 03LU] never appears and the coherence
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, which this
development does not have, is not needed; in particular no representability hypothesis is
carried.

Being an equality of functors rather than an isomorphism, this feeds
`CategoryTheory.Functor.congr_hom` and `CategoryTheory.Functor.hcongr_hom` directly. -/
theorem overMap_comp_chartLocalizationPushforward_eq :
    SheafOfModules.overMap (structureRingSheaf B S hS X) w ⋙ (@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          (SmallEtale.chartLocalization B S hS X.1 V)
          (chartStructureRingSheaf B S hS X V)
          ((structureRingSheaf B S hS X).over V)
          (isContinuous_chartLocalization_chartSpace B S hS X V)
          (𝟙 _)) =
      (@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)
          (SmallEtale.chartLocalization B S hS X.1 U)
          (chartStructureRingSheaf B S hS X U)
          ((structureRingSheaf B S hS X).over U)
          (isContinuous_chartLocalization_chartSpace B S hS X U)
          (𝟙 _)) ⋙
        (etaleModulePullback.{u, u} B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w)) :=
  (overMap_comp_chartLocalizationPushforward_eq_pushforward B S hS X w).trans
    ((pushforward_chartLocalization_comp_overMap_eq B S hS X w).trans
      (chartLocalizationPushforward_comp_etaleModulePullback_eq_pushforward B S hS X w).symm)

/-- **The commuting square of the naturality step of [Stacks Project, Tag 04AM] on morphisms.**
A morphism of `𝒪_X`-modules on the slice of the small étale site of `X` at `U`, restricted to the
slice at `V` and read on the small étale site of the chart space of `V`, is the morphism read at
`U` and restricted along the represented morphism of chart spaces.

The comparison is heterogeneous, and must be: at a chart of the chart space of `V` the two
readings of the source and target are modules over propositionally distinct rings, so the two
morphisms do not share a type.  This is
`CategoryTheory.Functor.hcongr_hom` of
`AlgebraicGeometry.Space.overMap_comp_chartLocalizationPushforward_eq`. -/
theorem overMap_comp_chartLocalizationPushforward_map_heq
    {M N : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)} (f : M ⟶ N) :
    (SheafOfModules.overMap (structureRingSheaf B S hS X) w ⋙ (@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          (SmallEtale.chartLocalization B S hS X.1 V)
          (chartStructureRingSheaf B S hS X V)
          ((structureRingSheaf B S hS X).over V)
          (isContinuous_chartLocalization_chartSpace B S hS X V)
          (𝟙 _))).map f ≍
      ((@SheafOfModules.pushforward _ _ _ _
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)
          (SmallEtale.chartLocalization B S hS X.1 U)
          (chartStructureRingSheaf B S hS X U)
          ((structureRingSheaf B S hS X).over U)
          (isContinuous_chartLocalization_chartSpace B S hS X U)
          (𝟙 _)) ⋙
        (etaleModulePullback.{u, u} B S hS (chartMap B S hS X w)
          (isEtale_chartMap B S hS X w))).map f :=
  Functor.hcongr_hom (overMap_comp_chartLocalizationPushforward_eq B S hS X w) f

end ChartNaturality

end AlgebraicGeometry.Space

end
