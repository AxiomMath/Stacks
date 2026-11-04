module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartPresieves
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# The chart morphisms of a direct-image algebra map, and the point of `Z` they define

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `Y` be an object of
`CategoryTheory.Over X` with representable structure morphism, let `Z` be affine over `X`, and let
`φ : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y` be a morphism of the direct-image algebras of
`AlgebraicGeometry.Space.pushforwardAlgebra`.  At every *affine* étale chart `V` of `X`,
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` produces a morphism `Y ×_X V ⟶ Z ×_X V`
of the big fppf category inducing the chart value of `φ` on global regular functions.  **This
file proves that that family is compatible**, which is the step the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullChart` record as absent — there the
morphisms are "produced one affine chart at a time and nothing here shows them compatible".

Two statements of compatibility are proved, and the second is the one fullness consumes.  The
first is naturality in the chart: base changing the chart morphism at an affine chart `V` along a
morphism of charts `W ⟶ V` gives the chart morphism at `W`.  The second says that a point of `Y`
with values in an object of the site, factored through an affine chart of `X` in two different
ways, gives the *same* point of `Z` — which is what lets the chart morphisms define a point of `Z`
locally, the factorization of a point of `Y` through an affine chart of `X` existing only locally
and only after a choice.

## Main results

* `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso_naturality`: **the sections of a
  direct-image algebra at a chart are natural in the chart.**  The identification
  `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` of `(Y.hom_* 𝒪_Y)(V)` with
  `Γ(Y ×_X V)` carries the restriction map of the algebra along a morphism `V ⟶ W` of charts to
  pullback of regular functions along the base change
  `AlgebraicGeometry.Space.smallBaseChange` of that morphism.
* `AlgebraicGeometry.Space.chartHom_smallBaseChange_naturality`: **the compatibility itself.**
  For `k : W ⟶ V` a morphism of affine étale charts of `X`, base changing a chart morphism of
  `φ` at `V` along `k` gives the chart morphism of `φ` at `W`: the square formed by the two
  chart morphisms and the two base changes of `k` commutes.
* `AlgebraicGeometry.Space.chartPoint_eq`: **the point of `Z` does not depend on the chart.**
  Two points of `Y ×_X V₁` and `Y ×_X V₂`, for `V₁` and `V₂` affine étale charts of `X`, lying
  over the same point of `Y`, induce the same point of `Z`.
* `AlgebraicGeometry.Space.chartPoint_eq_of_chartMap` is the nested case of that, where one chart
  maps to the other; `AlgebraicGeometry.Space.exists_chart_pair_factor` and
  `AlgebraicGeometry.Space.exists_covering_affineChart_factor` reduce the general case to it.
* `AlgebraicGeometry.Space.comp_conj_eq_conj_comp` is the algebra of the naturality proof, a
  naturality square conjugated by isomorphisms at its four corners, stated in an abstract
  category.

## Implementation notes

**Why naturality in the chart is free and the compatibility is not.**
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` is the component at `V` of a morphism of
sheaves on the small étale site of `X` — Stacks 03G8 in the shape
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`, read at the structure sheaf
of `Y` — so its naturality in `V` is `CategoryTheory.NatTrans.naturality` of that morphism and
costs nothing.  What is not free is the passage from the *sections* to the *morphisms*: equal maps
on global regular functions force equal morphisms of schemes only into an affine target, and the
target here is the base change `Z ×_X V`, which is an affine scheme exactly at the affine charts
(`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`).  So the compatibility below asks `V` to
be an affine chart, and `W` as well, only because the chart morphism at `W` is what it compares
against; `AlgebraicGeometry.ext_of_isAffine` consumes affineness of the **target** alone, matching
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` at the level of schemes.

**One spelling throughout, which is why four things are data and not definitions.**  The base
change of a chart morphism, the fibre product of two charts, the affine chart an open of a chart
cuts out, and the chart morphism it carries all have two spellings — the one their definition is
written in and the one the representing object of a relatively representable morphism is written
in — equal only after unfolding a semireducible definition.  A `rw` whose motive mixes the two is
not type-correct at implicit transparency, which is the failure the notes of
`AlgebraicGeometry.Space.smallBaseChangeOverMap_naturality` describe.  So the two base changes are
taken as *data* satisfying their universal property, exactly as that lemma takes them, and the
chart refinements are produced by *existentials*
(`AlgebraicGeometry.Space.exists_chart_pair_factor`,
`AlgebraicGeometry.Space.exists_covering_affineChart_factor`) whose witnesses are opaque where
they are consumed.  The defeq is then discharged once per statement, at the point where the
witness is supplied.  For the same reason the two applications of
`CategoryTheory.Functor.map_comp` in the naturality proof are `congrArg`s rather than rewrites.

**What fullness still needs beyond this file, and where it is done.**  By
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff` fullness is the existence, for
every `φ`, of a morphism `f : Y ⟶ Z` over `X` with `pushforwardAlgebraMap f = φ`, and
`AlgebraicGeometry.Space.pushforwardAlgebraMap_eq_of_appTop_smallBaseChangeOverMap_eq` reduces
that to exhibiting an `f` whose chart base changes are the chart morphisms of `φ`.  What is proved
here is that those chart morphisms assign to every point of `Y` that factors through an affine
chart of `X` a well-defined point of `Z`.  **What is not proved here is that those local points
amalgamate.**  Concretely, the two statements still missing here are

* a morphism of presheaves `d : Y ⟶ Z` whose restriction along each cartesian projection
  `Y ×_X V ⟶ Y`, at an affine chart `V`, is `yoneda.map (m V) ≫ hZ.fst V.obj.hom` — obtained from
  `AlgebraicGeometry.Space.generate_affineChartPresieve_mem`, which covers each object of the site
  by objects over which a point of `Y` does factor through an affine chart, by amalgamating the
  local points `AlgebraicGeometry.Space.chartPoint_eq` shows to be independent of the choice; and
* the identification of its chart base changes with the chart morphisms at *every* chart, not only
  the affine ones, which is separatedness of the sheaf `Y.hom_* 𝒪_Y` against the covering of a
  chart by the affine opens of its scheme
  (`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology`).

Both are proved in `StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness`, the first
as `AlgebraicGeometry.Space.exists_overHom_of_algebraHom` and the second as
`AlgebraicGeometry.Space.sheafHom_eq_of_affineChart`, and with them fullness of
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` is
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` there.  So **fullness is not proved
in this file** and no `@[stacks]` attribute is placed here; the tag's fullness clause is carried
by that file and its faithfulness clause by
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`, which between them deliver
clause (a) of
`AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A naturality square conjugated at its four corners -/

/-- **A naturality square conjugated by isomorphisms at all four corners is again a naturality
square.**

Read with `iZV`, `iZW`, `iYV`, `iYW` the identifications of the sections of two sheaves over two
charts with the regular functions on two base-changed charts, `rZ` and `rY` the restriction maps
of those sheaves along a morphism of charts, `fV` and `fW` the two components of a morphism
between them, and `b` and `a` pullback of regular functions along the two base-changed
morphisms, this is the whole content of
`AlgebraicGeometry.Space.chartHom_smallBaseChange_naturality`.

It is stated in an abstract category and at variables so that no term of that proof carries the
four identifications twice over. -/
theorem comp_conj_eq_conj_comp {C : Type*} [Category C]
    {PZV PZW PYV PYW GZV GZW GYV GYW : C}
    (iZV : PZV ≅ GZV) (iZW : PZW ≅ GZW) (iYV : PYV ≅ GYV) (iYW : PYW ≅ GYW)
    {rZ : PZV ⟶ PZW} {rY : PYV ⟶ PYW} {b : GZV ⟶ GZW} {a : GYV ⟶ GYW}
    {fV : PZV ⟶ PYV} {fW : PZW ⟶ PYW}
    (hZ : rZ ≫ iZW.hom = iZV.hom ≫ b) (hY : rY ≫ iYW.hom = iYV.hom ≫ a)
    (hf : rZ ≫ fW = fV ≫ rY) :
    b ≫ iZW.inv ≫ fW ≫ iYW.hom = (iZV.inv ≫ fV ≫ iYV.hom) ≫ a := by
  have hb : b ≫ iZW.inv = iZV.inv ≫ rZ := by
    rw [Iso.comp_inv_eq, Category.assoc, hZ, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hb, Category.assoc, Category.assoc, ← Category.assoc rZ fW,
    hf, Category.assoc, hY, Category.assoc]

/-! ### Naturality of the chart sections in the chart -/

/-- **The sections of a direct-image algebra over a chart are natural in the chart.**

For `k : V ⟶ W` a morphism of étale scheme charts of `X`, the restriction map of
`Y.hom_* 𝒪_Y` from `W` to `V`, read through
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at both ends, is pullback of regular
functions along the base change of `k` to `Y`.

This is `CategoryTheory.NatTrans.naturality` of Stacks 03G8 in the shape
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`, read at the structure sheaf
of `Y`: the identification is the component at `V` of a morphism of sheaves on the small étale
site, so its naturality in the chart is the naturality of that morphism.

The base-changed morphism is given as data satisfying its universal property rather than as the
value of `AlgebraicGeometry.Space.smallBaseChange` on `k`, for the reason recorded in the notes of
`AlgebraicGeometry.Space.smallBaseChangeOverMap_naturality`: that value is typed at the étale
chart `(smallBaseChange …).obj V`, whose underlying object is the representing object
`hY.pullback V.obj.hom` only after unfolding a semireducible definition, so stated there it makes
every rewrite downstream build a motive that is not type-correct at implicit transparency.  The
defeq is discharged once, here, by `CategoryTheory.Functor.relativelyRepresentable.hom_ext`. -/
theorem pushforwardAlgebraSectionsIso_naturality {X : AlgebraicSpaces B S hS} (Y : Over X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {V W : SmallEtale B S hS X.1} (k : V ⟶ W)
    (a : hY.pullback V.1.hom ⟶ hY.pullback W.1.hom)
    (ha₁ : yoneda.map a ≫ hY.fst W.1.hom = hY.fst V.1.hom)
    (ha₂ : a ≫ hY.snd W.1.hom = hY.snd V.1.hom ≫ k.hom.left) :
    (pushforwardAlgebra B S hS Y).right.obj.map k.op ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom =
      (pushforwardAlgebraSectionsIso B S hS Y hY W).hom ≫
        ((BigFppfOver.toScheme B S hS).map a).appTop := by
  let := isContinuous_smallBaseChange B S hS Y.hom hY
  refine Eq.trans (((smallEtaleRingedToposHom_representableRing B S hS Y.hom hY).app
    (smallEtaleRingedTopos B S hS Y.left).O).hom.hom.naturality k.op) ?_
  refine congrArg (fun m : hY.pullback V.1.hom ⟶ hY.pullback W.1.hom =>
    (pushforwardAlgebraSectionsIso B S hS Y hY W).hom ≫
      ((BigFppfOver.toScheme B S hS).map m).appTop) ?_
  exact hY.hom_ext ((smallBaseChange_map_fst B S hS Y.hom hY k).trans ha₁.symm)
    ((smallBaseChange_map_snd B S hS Y.hom hY k).trans ha₂.symm)

/-! ### The chart morphisms of a morphism of direct-image algebras are compatible -/

/-- **The chart morphisms built from a morphism of direct-image algebras are compatible with base
change of the chart.**

Let `Y` be an object of `CategoryTheory.Over X` with representable structure morphism, let `Z` be
affine over `X`, let `φ : Z.hom_* 𝒪_Z ⟶ Y.hom_* 𝒪_Y`, and let `k : W ⟶ V` be a morphism of étale
charts of `X` with `V` affine.  If `mV : Y ×_X V ⟶ Z ×_X V` and `mW : Y ×_X W ⟶ Z ×_X W` both
induce the chart value of `φ` on global regular functions — the conclusion of
`AlgebraicGeometry.Space.exists_chartHom_of_algebraHom` — then the square they form with the base
changes `a` and `b` of `k` to `Y` and to `Z` commutes.

So the chart morphisms of `φ` are a compatible family, which is what
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullChart` records as the missing first
half of the fullness clause of Stacks 081V.

The proof is the affineness of the target `Z ×_X V`
(`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`), which by
`AlgebraicGeometry.ext_of_isAffine` reduces the square to its reading on global regular functions,
together with three naturality statements assembled by
`AlgebraicGeometry.Space.comp_conj_eq_conj_comp`: that of
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at `Z` and at `Y`, and that of `φ` itself.
Affineness of `W` is not used, and affineness of `Y` is not assumed at all. -/
theorem chartHom_smallBaseChange_naturality {X : AlgebraicSpaces B S hS} {Y : Over X}
    (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    {V W : SmallEtale B S hS X.1} (k : W ⟶ V)
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V))
    (mV : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom)
    (hmV : ((BigFppfOver.toScheme B S hS).map mV).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
        φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
    (mW : hY.pullback W.1.hom ⟶ hZ.pullback W.1.hom)
    (hmW : ((BigFppfOver.toScheme B S hS).map mW).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ W).inv ≫
        φ.right.hom.app (op W) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY W).hom)
    (a : hY.pullback W.1.hom ⟶ hY.pullback V.1.hom)
    (ha₁ : yoneda.map a ≫ hY.fst V.1.hom = hY.fst W.1.hom)
    (ha₂ : a ≫ hY.snd V.1.hom = hY.snd W.1.hom ≫ k.hom.left)
    (b : hZ.pullback W.1.hom ⟶ hZ.pullback V.1.hom)
    (hb₁ : yoneda.map b ≫ hZ.fst V.1.hom = hZ.fst W.1.hom)
    (hb₂ : b ≫ hZ.snd V.1.hom = hZ.snd W.1.hom ≫ k.hom.left) :
    mW ≫ b = a ≫ mV := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hZ.pullback V.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS Z.obj.hom hZ Z.property V hV
  refine (BigFppfOver.toScheme B S hS).map_injective (AlgebraicGeometry.ext_of_isAffine ?_)
  refine Eq.trans ((congrArg (fun m => Scheme.Hom.appTop m)
    ((BigFppfOver.toScheme B S hS).map_comp mW b)).trans (Scheme.Hom.comp_appTop _ _)) ?_
  refine Eq.trans ?_ ((congrArg (fun m => Scheme.Hom.appTop m)
    ((BigFppfOver.toScheme B S hS).map_comp a mV)).trans (Scheme.Hom.comp_appTop _ _)).symm
  rw [hmV, hmW]
  exact comp_conj_eq_conj_comp _ _ _ _
    (pushforwardAlgebraSectionsIso_naturality B S hS Z.obj hZ k b hb₁ hb₂)
    (pushforwardAlgebraSectionsIso_naturality B S hS Y hY k a ha₁ ha₂)
    (φ.right.hom.naturality k.op)

/-! ### Reading a point of `Z` through a refinement of the chart -/

/-- **A point of `Y` factored through two nested charts gives the same point of `Z`.**

Let `κ : Vj ⟶ V` be a morphism of étale charts of `X` with `V` affine, let `m` and `mj` be chart
morphisms of `φ` at `V` and at `Vj`, and let `a`, `b` be the base changes of `κ` to `Y` and to
`Z`.  A point `c` of `Y ×_X V` with values in an object `T` of the site and a point `cj` of
`Y ×_X Vj` which lies over the same point of `Y` and over `c`'s point of `V` give the same point
of `Z`.

This is `AlgebraicGeometry.Space.chartHom_smallBaseChange_naturality` read at a point: the two
hypotheses say exactly that `cj` and `c` agree after the two projections of the fibre product
`Y ×_X V`, so `c` factors through `cj`, and the compatibility then identifies the two
composites. -/
theorem chartPoint_eq_of_chartMap {X : AlgebraicSpaces B S hS} {Y : Over X}
    (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    {V Vj : SmallEtale B S hS X.1} (κ : Vj ⟶ V)
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V))
    (m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom)
    (hm : ((BigFppfOver.toScheme B S hS).map m).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
        φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
    (mj : hY.pullback Vj.1.hom ⟶ hZ.pullback Vj.1.hom)
    (hmj : ((BigFppfOver.toScheme B S hS).map mj).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ Vj).inv ≫
        φ.right.hom.app (op Vj) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY Vj).hom)
    (a : hY.pullback Vj.1.hom ⟶ hY.pullback V.1.hom)
    (ha₁ : yoneda.map a ≫ hY.fst V.1.hom = hY.fst Vj.1.hom)
    (ha₂ : a ≫ hY.snd V.1.hom = hY.snd Vj.1.hom ≫ κ.hom.left)
    (b : hZ.pullback Vj.1.hom ⟶ hZ.pullback V.1.hom)
    (hb₁ : yoneda.map b ≫ hZ.fst V.1.hom = hZ.fst Vj.1.hom)
    (hb₂ : b ≫ hZ.snd V.1.hom = hZ.snd Vj.1.hom ≫ κ.hom.left)
    {T : BigFppfOver B S hS} (c : T ⟶ hY.pullback V.1.hom) (cj : T ⟶ hY.pullback Vj.1.hom)
    (hfst : yoneda.map cj ≫ hY.fst Vj.1.hom = yoneda.map c ≫ hY.fst V.1.hom)
    (hsnd : cj ≫ hY.snd Vj.1.hom ≫ κ.hom.left = c ≫ hY.snd V.1.hom) :
    yoneda.map c ≫ yoneda.map m ≫ hZ.fst V.1.hom =
      yoneda.map cj ≫ yoneda.map mj ≫ hZ.fst Vj.1.hom := by
  have hc : cj ≫ a = c :=
    hY.hom_ext (by rw [yoneda.map_comp, Category.assoc, ha₁, hfst])
      (by rw [Category.assoc, ha₂, hsnd])
  rw [← hc, yoneda.map_comp cj a, Category.assoc, ← Category.assoc (yoneda.map a),
    ← yoneda.map_comp,
    ← chartHom_smallBaseChange_naturality B S hS Z hY hZ φ κ hV m hm mj hmj a ha₁ ha₂ b hb₁ hb₂,
    yoneda.map_comp mj b, Category.assoc, hb₁]


/-! ### Refining two chart factorizations to one affine chart -/

/-- **Two chart factorizations of a point of `X` factor through a common chart.**  Given maps
from an object `T` of the site to the schemes of two étale charts of `X` which agree as points of
`X`, there is an étale chart receiving both factorizations: the fibre product
`AlgebraicGeometry.Space.SmallEtale.prodObj`, which is a chart because an étale chart is
representable and its base changes are étale.

The chart and the two projections are produced existentially rather than named, so that the
spelling of the fibre product — the representing object of the base change of one chart along the
other — does not enter the statements downstream.  That matters here: a `rw` whose motive mixes
that spelling with `AlgebraicGeometry.Space.SmallEtale.prodObj`'s own is not type-correct at
implicit transparency. -/
theorem exists_chart_pair_factor {X : AlgebraicSpaces B S hS} (V₁ V₂ : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (g₁ : T ⟶ (SmallEtale.toOver B S hS X.1).obj V₁)
    (g₂ : T ⟶ (SmallEtale.toOver B S hS X.1).obj V₂)
    (hg : yoneda.map g₁ ≫ V₁.1.hom = yoneda.map g₂ ≫ V₂.1.hom) :
    ∃ (V₀ : SmallEtale B S hS X.1) (p₁ : V₀ ⟶ V₁) (p₂ : V₀ ⟶ V₂)
      (τ : T ⟶ (SmallEtale.toOver B S hS X.1).obj V₀),
      τ ≫ p₁.hom.left = g₁ ∧ τ ≫ p₂.hom.left = g₂ :=
  ⟨SmallEtale.prodObj B S hS X.1 V₁ V₂, SmallEtale.prodFst B S hS X.1 V₁ V₂,
    SmallEtale.prodSnd B S hS X.1 V₁ V₂, V₁.property.rep.lift' g₁ g₂ hg,
    Functor.relativelyRepresentable.lift'_fst _ _ _ _,
    Functor.relativelyRepresentable.lift'_snd _ _ _ _⟩

/-- **A map to a chart factors, on a covering sieve, through affine charts.**  Let `V₀` be an
étale chart of `X` and `τ` a map from an object `T` of the site to its scheme.  There is a
covering sieve of `T` each of whose members factors `τ` through an *affine* étale chart of `X`
mapping to `V₀`.

This is the step that makes the fibre product of two affine charts usable even though it need not
be affine: the chart `V₀` is covered by the affine opens of its scheme, each of which is again an
étale chart of `X` — being an open immersion followed by an étale chart — and the covering sieve
is the pullback along `τ` of the cover those opens generate. -/
theorem exists_covering_affineChart_factor {X : AlgebraicSpaces B S hS}
    (V₀ : SmallEtale B S hS X.1) {T : BigFppfOver B S hS}
    (τ : T ⟶ (SmallEtale.toOver B S hS X.1).obj V₀) :
    ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), R.arrows h →
        ∃ (Vj : SmallEtale B S hS X.1) (κ : Vj ⟶ V₀)
          (_ : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj Vj))
          (k : T' ⟶ (SmallEtale.toOver B S hS X.1).obj Vj),
          h ≫ τ = k ≫ κ.hom.left := by
  obtain ⟨J, Wm, π, hWaff, hπ, hcov⟩ := BigFppfOver.exists_affine_open_cover B S hS
    ((SmallEtale.toOver B S hS X.1).obj V₀)
  refine ⟨_, (BigFppfOver.topology B S hS).pullback_stable τ hcov, ?_⟩
  intro T' h hmem
  obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hmem
  have hπj := hπ j
  exact ⟨⟨CostructuredArrow.mk (yoneda.map (π j) ≫ V₀.1.hom),
      etale_comp_of_scheme B S hS (π j) V₀.1.hom inferInstance V₀.property⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk (π j) rfl), hWaff j, k, hk⟩


/-! ### The local point of `Z` does not depend on the chart -/

/-- **Two affine-chart factorizations of the same point of `Y` give the same point of `Z`.**

Let `V₁` and `V₂` be affine étale charts of `X` with chart morphisms `m₁`, `m₂` of `φ`, and let
`c₁`, `c₂` be points of `Y ×_X V₁` and `Y ×_X V₂` with values in an object `T` of the site which
lie over the *same* point of `Y`.  Then they induce the same point of `Z`.

**This is what makes the chart morphisms of `φ` define a point of `Z` at all**: a point of `Y`
factors through an affine chart of `X` only locally and only after a choice, and this says the
choice does not matter.  It is the obstacle the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullChart` describe —
"the compatibility that argument needs is the one this file does not prove".

The proof refines the two factorizations to one chart by
`AlgebraicGeometry.Space.exists_chart_pair_factor`, cuts that chart down to affine charts on a
covering sieve of `T` by `AlgebraicGeometry.Space.exists_covering_affineChart_factor`, and on each
member identifies both sides with the point coming from the affine chart there, by
`AlgebraicGeometry.Space.chartPoint_eq_of_chartMap` applied to the two composite chart morphisms.
`Z` being a sheaf, agreement on a covering sieve is agreement.  The common refinement is *not*
assumed affine, and is not: the fibre product of two affine charts of an algebraic space need not
be an affine scheme, which is why the covering sieve is taken and why the affine opens of that
fibre product are what the compatibility is read at. -/
theorem chartPoint_eq {X : AlgebraicSpaces B S hS} {Y : Over X}
    (Z : AffineOver B S hS X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y)
    {V₁ V₂ : SmallEtale B S hS X.1}
    (hV₁ : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V₁))
    (hV₂ : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V₂))
    (m₁ : hY.pullback V₁.1.hom ⟶ hZ.pullback V₁.1.hom)
    (hm₁ : ((BigFppfOver.toScheme B S hS).map m₁).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V₁).inv ≫
        φ.right.hom.app (op V₁) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V₁).hom)
    (m₂ : hY.pullback V₂.1.hom ⟶ hZ.pullback V₂.1.hom)
    (hm₂ : ((BigFppfOver.toScheme B S hS).map m₂).appTop =
      (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V₂).inv ≫
        φ.right.hom.app (op V₂) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V₂).hom)
    {T : BigFppfOver B S hS} (c₁ : T ⟶ hY.pullback V₁.1.hom) (c₂ : T ⟶ hY.pullback V₂.1.hom)
    (hc : yoneda.map c₁ ≫ hY.fst V₁.1.hom = yoneda.map c₂ ≫ hY.fst V₂.1.hom) :
    yoneda.map c₁ ≫ yoneda.map m₁ ≫ hZ.fst V₁.1.hom =
      yoneda.map c₂ ≫ yoneda.map m₂ ≫ hZ.fst V₂.1.hom := by
  have hcond : yoneda.map (c₁ ≫ hY.snd V₁.1.hom) ≫ V₁.1.hom =
      yoneda.map (c₂ ≫ hY.snd V₂.1.hom) ≫ V₂.1.hom := by
    rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
      ← hY.w V₁.1.hom, ← hY.w V₂.1.hom, ← Category.assoc, ← Category.assoc, hc]
  obtain ⟨V₀, p₁, p₂, τ, hτ₁, hτ₂⟩ := exists_chart_pair_factor B S hS V₁ V₂
    (c₁ ≫ hY.snd V₁.1.hom) (c₂ ≫ hY.snd V₂.1.hom) hcond
  obtain ⟨R, hR, hfac⟩ := exists_covering_affineChart_factor B S hS V₀ τ
  have hZt : Presieve.IsSheaf (BigFppfOver.topology B S hS) Z.obj.left.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).mp Z.obj.left.property.isSheaf
  refine yonedaEquiv.injective ?_
  refine (hZt _ hR).isSeparatedFor.ext ?_
  intro T' h hmem
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
  refine congrArg _ ?_
  obtain ⟨Vj, κ, hVjaff, k, hk⟩ := hfac h hmem
  obtain ⟨mj, hmj, hmjsnd⟩ := exists_chartHom_of_algebraHom B S hS Z hY hZ φ Vj hVjaff
  have hbase : ∀ {V : SmallEtale B S hS X.1} (p : V₀ ⟶ V) (c : T ⟶ hY.pullback V.1.hom),
      τ ≫ p.hom.left = c ≫ hY.snd V.1.hom →
        (h ≫ c) ≫ hY.snd V.1.hom = k ≫ (κ ≫ p).hom.left := fun p c hτ => by
    rw [show (κ ≫ p).hom.left = κ.hom.left ≫ p.hom.left from rfl, Category.assoc, ← hτ,
      ← Category.assoc h τ _, hk, Category.assoc]
  have hconej : (yoneda.map (h ≫ c₁) ≫ hY.fst V₁.1.hom) ≫ Y.hom.hom =
      yoneda.map k ≫ Vj.1.hom := by
    rw [Category.assoc, hY.w V₁.1.hom, ← Category.assoc, ← yoneda.map_comp, hbase p₁ c₁ hτ₁,
      yoneda.map_comp k _, Category.assoc, ← CostructuredArrow.w (κ ≫ p₁).hom]
  set cj := hY.lift (yoneda.map (h ≫ c₁) ≫ hY.fst V₁.1.hom) k hconej with hcj
  have hcjfst : yoneda.map cj ≫ hY.fst Vj.1.hom = yoneda.map (h ≫ c₁) ≫ hY.fst V₁.1.hom :=
    hY.lift_fst _ _ hconej
  have hcjsnd : cj ≫ hY.snd Vj.1.hom = k := hY.lift_snd _ _ hconej
  have step : ∀ {V : SmallEtale B S hS X.1} (hV : IsAffineOver B S hS
      ((SmallEtale.toOver B S hS X.1).obj V)) (m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom)
      (hm : ((BigFppfOver.toScheme B S hS).map m).appTop =
        (pushforwardAlgebraSectionsIso B S hS Z.obj hZ V).inv ≫
          φ.right.hom.app (op V) ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)
      (p : V₀ ⟶ V) (c : T ⟶ hY.pullback V.1.hom) (hτ : τ ≫ p.hom.left = c ≫ hY.snd V.1.hom),
      yoneda.map cj ≫ hY.fst Vj.1.hom = yoneda.map (h ≫ c) ≫ hY.fst V.1.hom →
        yoneda.map (h ≫ c) ≫ yoneda.map m ≫ hZ.fst V.1.hom =
          yoneda.map cj ≫ yoneda.map mj ≫ hZ.fst Vj.1.hom := fun hV m hm p c hτ hfst =>
    chartPoint_eq_of_chartMap B S hS Z hY hZ φ (κ ≫ p) hV m hm mj hmj
      ((smallBaseChange B S hS Y.hom hY).map (κ ≫ p)).hom.left
      (smallBaseChange_map_fst B S hS Y.hom hY (κ ≫ p))
      (smallBaseChange_map_snd B S hS Y.hom hY (κ ≫ p))
      ((smallBaseChange B S hS Z.obj.hom hZ).map (κ ≫ p)).hom.left
      (smallBaseChange_map_fst B S hS Z.obj.hom hZ (κ ≫ p))
      (smallBaseChange_map_snd B S hS Z.obj.hom hZ (κ ≫ p))
      (h ≫ c) cj hfst (by rw [← Category.assoc, hcjsnd, hbase p c hτ])
  have key := (step hV₁ m₁ hm₁ p₁ c₁ hτ₁ hcjfst).trans
    (step hV₂ m₂ hm₂ p₂ c₂ hτ₂ (by
      rw [hcjfst, yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hc])).symm
  rwa [yoneda.map_comp h c₁, yoneda.map_comp h c₂, Category.assoc, Category.assoc] at key

end AlgebraicGeometry.Space

end
