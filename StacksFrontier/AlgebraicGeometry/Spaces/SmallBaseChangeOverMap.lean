module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsMorphism

/-!
# The base change of a morphism over an algebraic space to an étale chart

`AlgebraicGeometry.Space.smallBaseChange` is Stacks 03G2, part (4): base change of étale scheme
charts along a representable morphism of algebraic spaces.  It is a functor of the **chart** — for
a fixed morphism `Y ⟶ X` it sends a chart `V` of `X` to the chart `Y ×_X V` of `Y` — and it is
*not* a functor of the morphism, because `smallBaseChange` has a different target category for
each source space.  So for `Y`, `Z` two algebraic spaces over `X` with representable structure
morphisms and `f : Y ⟶ Z` a morphism over `X`, the base-changed morphism of schemes

`Y ×_X V ⟶ Z ×_X V`

is not the value of any functor already in this development, and had no name at all.  This file
names it.

It is needed to *state* the faithfulness clause of Stacks 081V in the chart presentation.  What
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` gives is that the sections of
`Y.hom_* 𝒪_Y` over `V` are the regular functions on `Y ×_X V`; the chart value of the
direct-image map `AlgebraicGeometry.Space.pushforwardRingMap f` is therefore a ring map
`Γ(Z ×_X V) ⟶ Γ(Y ×_X V)`, and the assertion that identifies it — the assertion whose injectivity
in `f` is faithfulness — is that it is pullback of regular functions **along the base-changed
morphism**.  Until that morphism has a name the assertion cannot be written down.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeOverMap` is the morphism itself, as a morphism of the
  big fppf site: for `f : Y ⟶ Z` over `X` and `V` an étale scheme chart of `X`, the morphism
  `Y ×_X V ⟶ Z ×_X V` over `V` which covers `f`.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeOverMap_snd` and
  `AlgebraicGeometry.Space.yoneda_map_smallBaseChangeOverMap_fst` are the two characterising
  identities: the base-changed morphism is a morphism over the chart `V`, and after `yoneda` it
  carries the cartesian projection to `Z` to the cartesian projection to `Y` followed by `f`.
* `AlgebraicGeometry.Space.eq_smallBaseChangeOverMap`: those two identities determine it.  This is
  what makes "the" base-changed morphism a definite description rather than a choice.
* `AlgebraicGeometry.Space.smallBaseChangeOverMap_id` and
  `AlgebraicGeometry.Space.smallBaseChangeOverMap_comp`: **it is functorial in the morphism**,
  which is exactly the structure `AlgebraicGeometry.Space.smallBaseChange` does not have.
* `AlgebraicGeometry.Space.smallBaseChangeOverMap_naturality`: it is also natural in the chart,
  stated against restriction morphisms given by their universal property.
* `AlgebraicGeometry.Space.smallBaseChange_map_fst`: the companion of
  `AlgebraicGeometry.Space.smallBaseChange_map_snd` for the other cartesian projection, which is
  what supplies that universal property for the values of
  `AlgebraicGeometry.Space.smallBaseChange` on a morphism of charts.
* `AlgebraicGeometry.Space.smallBaseChangeOverMap_appTop_comp_cartesianProjectionAppTop`: pullback
  of regular functions along it is a map of `Γ(V)`-algebras.
* `AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq`: **the chart
  value of the direct-image map and pullback along the base-changed morphism agree on the regular
  functions pulled back from the chart.**  This is the triangle over the base of the naturality
  square that the full identification is; the square itself is
  `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`, see the
  implementation notes.
* `AlgebraicGeometry.Space.pushforwardRingMap_app_eq_of_surjective`: **the identification itself,
  under the hypothesis that pullback along the cartesian projection `Z ×_X V ⟶ V` is surjective.**
  That hypothesis turns the triangle into the square, a surjection being an epimorphism; it is
  what the triangle gives on its own, and it is removed by
  `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`.

## Implementation notes

**The shape.**  The morphism is defined in `AlgebraicGeometry.BigFppfOver`, not in `Scheme` and
not in a category of charts.  Three considerations fix that choice.

* It cannot be a morphism of étale charts: `Y ×_X V` is a chart of `Y` and `Z ×_X V` is a chart of
  `Z`, and those live in the *different* categories `SmallEtale … Y.left.1` and
  `SmallEtale … Z.left.1`.  There is no category of charts containing both.
* The universal property that pins it down —
  `CategoryTheory.Functor.relativelyRepresentable.lift`, through which it is defined — is a
  universal property in `AlgebraicGeometry.BigFppfOver`, since that is where the representing
  objects of `CategoryTheory.Functor.relativelyRepresentable.pullback` live.  Defining it in
  `Scheme` would mean its characterisation could only be stated after applying
  `AlgebraicGeometry.BigFppfOver.toScheme`, which is not full, so the uniqueness clause would be
  lost.
* The scheme-level reading, which is what the sections statements need, is
  `(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map` of it; that is a functor application and
  needs no declaration of its own.

The source and target are written as `hY.pullback V.obj.hom` and `hZ.pullback V.obj.hom`, not as
`((smallBaseChange B S hS Y.hom hY).obj V).obj.left` and its counterpart.  The two are equal by
`rfl`, but only after unfolding `AlgebraicGeometry.Space.smallBaseChange`, which is semireducible;
a goal mentioning both spellings is therefore not type-correct at the transparency `rw` builds its
motive at, and the rewriting steps below fail on a visibly present pattern.  With the representing
objects named directly, the universal property and the morphism are in one spelling throughout.
The defeq is discharged exactly where the chart spelling is genuinely wanted: in the statements of
the last two results, which name `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, whose
target is stated at `AlgebraicGeometry.Space.chartScheme` of the base-changed chart — and those are
proved by terms, not by `rw`.

**What the two last results are, and where the identification itself is.**  The identification
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq` is the
composite of the two candidate maps with pullback along the cartesian projection `Z ×_X V ⟶ V`,
not the two maps themselves, and that is weaker: it says the two agree on the regular functions
coming from the chart.  Where those are all of them the triangle does give the square, which is
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq_of_surjective`.  The equality of the two maps
with no hypothesis on `Z` is `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`, which is not proved
here because it needs the composition law of chart base change, read on sections by
`AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso`, and the
factorisation of `AlgebraicGeometry.Space.smallBaseChangeOverMap` through the component of
`AlgebraicGeometry.Space.smallBaseChangeComp`, neither of which is available at this import.

**No `@[stacks]` attribute is placed.**  A base change of a morphism of schemes is not a statement
of the Stacks project, and the identification that Stacks 081V's faithfulness clause needs is not
proved here.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4), base change of
  étale scheme charts.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map and the
  sections of a direct image over a chart.
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-! ### The cartesian projection to the source space -/

/-- Base change of a morphism of étale charts is compatible with the projections to the
base-changed charts.  This is the companion of
`AlgebraicGeometry.Space.smallBaseChange_map_snd` for the other projection. -/
theorem smallBaseChange_map_fst {Xx Yy : AlgebraicSpaces B S hS} (f : Xx ⟶ Yy)
    (hf : yoneda.relativelyRepresentable f.hom) {V W : SmallEtale B S hS Yy.1} (k : V ⟶ W) :
    yoneda.map ((smallBaseChange B S hS f hf).map k).hom.left ≫ hf.fst W.obj.hom =
      hf.fst V.obj.hom :=
  hf.lift_fst _ _ _

/-! ### The base-changed morphism -/

variable {Y Z : Over X}

/-- The compatibility that defines `AlgebraicGeometry.Space.smallBaseChangeOverMap`: the cartesian
projection `Y ×_X V ⟶ Y` followed by `f` and the structure morphism of `Z` is the cartesian
projection `Y ×_X V ⟶ V` followed by the chart. -/
theorem smallBaseChangeOverMap_cond (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom) (V : SmallEtale B S hS X.1) :
    (hY.fst V.obj.hom ≫ f.left.hom) ≫ Z.hom.hom =
      yoneda.map (hY.snd V.obj.hom) ≫ V.obj.hom := by
  have hw : f.left.hom ≫ Z.hom.hom = Y.hom.hom :=
    congrArg (fun k : Y.left ⟶ X => k.hom) (Over.w f)
  rw [Category.assoc, hw]
  exact hY.w V.obj.hom

/-- **The base change of a morphism over `X` to an étale chart of `X`.**  For `f : Y ⟶ Z` a
morphism of algebraic spaces over `X` whose two structure morphisms are representable and `V` an
étale scheme chart of `X`, this is the morphism

`Y ×_X V ⟶ Z ×_X V`

over `V` whose composite with the cartesian projection to `Z` is the cartesian projection to `Y`
followed by `f`.  It exists because `Z ×_X V` is a fibre product: it is
`CategoryTheory.Functor.relativelyRepresentable.lift` of that pair of morphisms, and
`AlgebraicGeometry.Space.eq_smallBaseChangeOverMap` says the pair determines it.

This is the morphism of which the chart value of
`AlgebraicGeometry.Space.pushforwardRingMap f` is the pullback of regular functions, by
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`. -/
def smallBaseChangeOverMap (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    hY.pullback V.obj.hom ⟶ hZ.pullback V.obj.hom :=
  hZ.lift (hY.fst V.obj.hom ≫ f.left.hom) (hY.snd V.obj.hom)
    (smallBaseChangeOverMap_cond B S hS f hY V)

/-- **The base-changed morphism is a morphism over the chart.** -/
@[simp]
theorem smallBaseChangeOverMap_snd (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    smallBaseChangeOverMap B S hS f hY hZ V ≫ hZ.snd V.obj.hom = hY.snd V.obj.hom :=
  hZ.lift_snd _ _ _

/-- **The base-changed morphism covers `f`.** -/
@[simp]
theorem yoneda_map_smallBaseChangeOverMap_fst (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    yoneda.map (smallBaseChangeOverMap B S hS f hY hZ V) ≫ hZ.fst V.obj.hom =
      hY.fst V.obj.hom ≫ f.left.hom :=
  hZ.lift_fst _ _ _

/-- **The two identities determine the base-changed morphism.**  Being over the chart and
covering `f` is a definite description: `Z ×_X V` is a fibre product, so a morphism into it is
determined by its two projections. -/
theorem eq_smallBaseChangeOverMap (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (g : hY.pullback V.obj.hom ⟶ hZ.pullback V.obj.hom)
    (hfst : yoneda.map g ≫ hZ.fst V.obj.hom = hY.fst V.obj.hom ≫ f.left.hom)
    (hsnd : g ≫ hZ.snd V.obj.hom = hY.snd V.obj.hom) :
    g = smallBaseChangeOverMap B S hS f hY hZ V :=
  hZ.hom_ext (hfst.trans (yoneda_map_smallBaseChangeOverMap_fst B S hS f hY hZ V).symm)
    (hsnd.trans (smallBaseChangeOverMap_snd B S hS f hY hZ V).symm)

/-! ### Functoriality in the morphism -/

/-- **The base change of an identity is an identity.** -/
@[simp]
theorem smallBaseChangeOverMap_id (Y : Over X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom) (V : SmallEtale B S hS X.1) :
    smallBaseChangeOverMap B S hS (𝟙 Y) hY hY V = 𝟙 _ := by
  refine (eq_smallBaseChangeOverMap B S hS (𝟙 Y) hY hY V (𝟙 _) ?_ ?_).symm
  · rw [yoneda.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  · rw [Category.id_comp]

/-- **The base change of a composite is the composite of the base changes**, so the base-changed
morphism is functorial in the morphism over `X`.  This is the structure
`AlgebraicGeometry.Space.smallBaseChange` does not have, its target category depending on the
source space of the morphism it base changes along. -/
@[simp]
theorem smallBaseChangeOverMap_comp {Y Z W : Over X} (f : Y ⟶ Z) (g : Z ⟶ W)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (hW : yoneda.relativelyRepresentable W.hom.hom) (V : SmallEtale B S hS X.1) :
    smallBaseChangeOverMap B S hS (f ≫ g) hY hW V =
      smallBaseChangeOverMap B S hS f hY hZ V ≫ smallBaseChangeOverMap B S hS g hZ hW V :=
  (eq_smallBaseChangeOverMap B S hS (f ≫ g) hY hW V _
    (by
      simp only [yoneda.map_comp, Category.assoc, yoneda_map_smallBaseChangeOverMap_fst]
      rw [← Category.assoc, yoneda_map_smallBaseChangeOverMap_fst, Category.assoc]
      rfl)
    (by simp)).symm

/-! ### Naturality in the chart -/

/-- **The base-changed morphism is natural in the chart.**  Let `k : V ⟶ W` be a morphism of
étale scheme charts of `X`, let `a` be a morphism `Y ×_X V ⟶ Y ×_X W` over `k` which is the
identity on the `Y`-component, and let `b` be the same for `Z`.  Then restricting along `k` and
then base changing `f` is base changing `f` and then restricting along `k`.

The two restriction morphisms are given as data satisfying their universal property rather than
as the values of `AlgebraicGeometry.Space.smallBaseChange` on `k`, which are supplied by
`AlgebraicGeometry.Space.smallBaseChange_map_fst` and
`AlgebraicGeometry.Space.smallBaseChange_map_snd`.  The reason is that those values are typed at
the étale charts `(smallBaseChange …).obj V`, whose underlying objects are the representing
objects `hY.pullback V.obj.hom` only after unfolding
`AlgebraicGeometry.Space.smallBaseChange`; stated here they would make every intermediate term of
the proof type-correct only at default transparency.  In the form below the statement is in the
one spelling throughout, and the defeq is discharged once, at the call site, when the two
restriction morphisms are handed in. -/
theorem smallBaseChangeOverMap_naturality (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    {V W : SmallEtale B S hS X.1} (k : V ⟶ W)
    (a : hY.pullback V.obj.hom ⟶ hY.pullback W.obj.hom)
    (ha₁ : yoneda.map a ≫ hY.fst W.obj.hom = hY.fst V.obj.hom)
    (ha₂ : a ≫ hY.snd W.obj.hom = hY.snd V.obj.hom ≫ k.hom.left)
    (b : hZ.pullback V.obj.hom ⟶ hZ.pullback W.obj.hom)
    (hb₁ : yoneda.map b ≫ hZ.fst W.obj.hom = hZ.fst V.obj.hom)
    (hb₂ : b ≫ hZ.snd W.obj.hom = hZ.snd V.obj.hom ≫ k.hom.left) :
    a ≫ smallBaseChangeOverMap B S hS f hY hZ W =
      smallBaseChangeOverMap B S hS f hY hZ V ≫ b := by
  refine hZ.hom_ext ?_ ?_
  · simp [hb₁, reassoc_of% ha₁]
  · simp only [Category.assoc, smallBaseChangeOverMap_snd, ha₂, hb₂]
    rw [← Category.assoc, smallBaseChangeOverMap_snd]

/-! ### The chart value of the direct-image map, over the base -/

/-- **Pullback of regular functions along the base-changed morphism is a map of
`Γ(V)`-algebras.**  This is `AlgebraicGeometry.Space.smallBaseChangeOverMap_snd` read on global
regular functions. -/
theorem smallBaseChangeOverMap_appTop_comp_cartesianProjectionAppTop (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop ≫
        ((BigFppfOver.toScheme B S hS).map
          (smallBaseChangeOverMap B S hS f hY hZ V)).appTop =
      ((BigFppfOver.toScheme B S hS).map (hY.snd V.obj.hom)).appTop :=
  (Scheme.Hom.comp_appTop ((BigFppfOver.toScheme B S hS).map
        (smallBaseChangeOverMap B S hS f hY hZ V))
      ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom))).symm.trans
    (congrArg (fun m => Scheme.Hom.appTop m)
      (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (congrArg (fun m => (BigFppfOver.toScheme B S hS).map m)
          (smallBaseChangeOverMap_snd B S hS f hY hZ V))))

/-- **The chart value of the direct-image map and pullback along the base-changed morphism agree
on the regular functions pulled back from the chart.**

Let `f : Y ⟶ Z` be a morphism of algebraic spaces over `X` with representable structure
morphisms and let `V` be an étale scheme chart of `X`.  Two ring maps
`Γ(Z ×_X V) ⟶ Γ(Y ×_X V)` are now available: the component at `V` of
`AlgebraicGeometry.Space.pushforwardRingMap f`, read through
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at the source and the target, and pullback
of regular functions along `AlgebraicGeometry.Space.smallBaseChangeOverMap`.  They agree after
precomposition with pullback along the cartesian projection `Z ×_X V ⟶ V`.

The faithfulness clause of Stacks 081V needs the two to be *equal*, which is strictly more: this
is the triangle over the base of that naturality square, and it is the triangle because both maps
are `Γ(V)`-algebra maps — the left one by
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app` and the right one
by `AlgebraicGeometry.Space.smallBaseChangeOverMap_appTop_comp_cartesianProjectionAppTop`.  The
square is `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`. -/
theorem cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop ≫
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv ≫
        (pushforwardRingMap B S hS f).hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop ≫
        ((BigFppfOver.toScheme B S hS).map
          (smallBaseChangeOverMap B S hS f hY hZ V)).appTop :=
  (cartesianProjectionAppTop_comp_pushforwardRingMap_app B S hS f hY hZ V).trans
    (smallBaseChangeOverMap_appTop_comp_cartesianProjectionAppTop B S hS f hY hZ V).symm

/-- **Where the regular functions on `Z ×_X V` all come from the chart, the identification does
hold**: the chart value of the direct-image map *is* pullback of regular functions along the
base-changed morphism.

The hypothesis is surjectivity of pullback along the cartesian projection `Z ×_X V ⟶ V`.  Under
it the triangle of
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq` determines the
square, because a surjective morphism of a concrete category is an epimorphism.  This is what the
triangle gives on its own; the square with no hypothesis on `Z` is
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`, which reads the factors
of `AlgebraicGeometry.Space.pushforwardRingMap` instead. -/
theorem pushforwardRingMap_app_eq_of_surjective (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (hsurj : Function.Surjective
      ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop) :
    (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv ≫
        (pushforwardRingMap B S hS f).hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS f hY hZ V)).appTop :=
  have : Epi ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop :=
    ConcreteCategory.epi_of_surjective _ hsurj
  (cancel_epi ((BigFppfOver.toScheme B S hS).map (hZ.snd V.obj.hom)).appTop).mp
    (cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq B S hS f hY hZ V)

end AlgebraicGeometry.Space

end
