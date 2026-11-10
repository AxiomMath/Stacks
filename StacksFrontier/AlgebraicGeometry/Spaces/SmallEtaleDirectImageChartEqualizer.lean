module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleGlobalSectionsFork
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image on the small étale sites, on sections over a chart, as an equalizer

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `P` be a sheaf of sets on the small étale site of `X`.  Let `V` be an étale
scheme chart of `Y`.  This file presents the sections of the direct image
`f_{small,*}P` over `V` as an equalizer of sections of `P` itself (Tag 03H7, Remark 66.18.4):
for a scheme `W` étale and surjective over `X ×_Y V` and a scheme `W'` presenting
`W ×_{X ×_Y V} W`, with projections `a, b : W' ⟶ W`,

`(f_{small,*}P)(V) ≃ {y : P(W) // a^*y = b^*y}`.

The sections of `f_{small,*}P` over `V` are the sections over `X ×_Y V` of the sheaf `P'` on the
spaces-étale site of `X` that restricts to `P` (Stacks 03G1, 03G2), and the presentation
isomorphism identifies the sections of `P'` over a chart with those of `P`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDirectImagePresentationIso`: the presentation
  isomorphism — the identification of the restriction to the scheme charts of the spaces-étale
  sheaf produced by the quasi-inverse of Stacks 03G1 with the original small étale sheaf, the
  counit of that equivalence.
* `AlgebraicGeometry.Space.smallEtaleDirectImageChartSection`: restriction of a section of
  `f_{small,*}P` over `V` to the chart `W` of `X` — the first arrow of the equalizer diagram.
* `AlgebraicGeometry.Space.smallEtaleDirectImageChartEqualizerEquiv`: the equalizer
  presentation itself, as a bijection, given a chart `W` covering `X ×_Y V` and a chart `W'`
  presenting the self-fibre product of `W` over it.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv`: **Tag 03H7 for the
  small étale direct image.**  For every sheaf and every chart of the target, charts `W`, `W'`
  of the source and the bijection exist.
* `AlgebraicGeometry.Space.smallEtaleDirectImageChartEqualizerEquiv_injective` and
  `AlgebraicGeometry.Space.smallEtaleDirectImageChartEqualizerEquiv_exists`: the two halves of
  that bijection read on the chart-restriction map — a section of the direct image is
  determined by its restriction to `W`, and every section over `W` equalized by the two
  projections is such a restriction.
* `CategoryTheory.Limits.Fork.injective_of_isLimit_type` and
  `CategoryTheory.Limits.Fork.exists_of_isLimit_type`: the same two halves for an arbitrary
  limiting fork of types.
* `CategoryTheory.Sheaf.isIso_of_bijective_app`: a morphism of sheaves of sets is invertible as
  soon as each of its components is a bijection.

## References

* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v u

namespace CategoryTheory.Limits

/-- The first projection of an equivalence onto a subtype is injective. -/
private theorem injective_val_comp_equiv_subtype {A α : Type*} {p : α → Prop}
    (e : A ≃ {x // p x}) : Function.Injective fun a => (e a).1 :=
  Subtype.val_injective.comp e.injective

/-- Every element satisfying the predicate is the first projection of the equivalence. -/
private theorem exists_val_eq_of_equiv_subtype {A α : Type*} {p : α → Prop}
    (e : A ≃ {x // p x}) {x : α} (hx : p x) : ∃ a, (e a).1 = x :=
  ⟨e.symm ⟨x, hx⟩, by simp⟩

/-- **A limiting fork of types is injective on its vertex.**  Two elements of the vertex with
the same image under the fork's arrow are equal. -/
theorem Fork.injective_of_isLimit_type {X Y : Type v} {f g : X ⟶ Y} {c : Fork f g}
    (hc : IsLimit c) : Function.Injective c.ι :=
  injective_val_comp_equiv_subtype (Fork.IsLimit.ptEquivSubtype hc)

/-- **A limiting fork of types hits every element equalized by its two parallel maps.** -/
theorem Fork.exists_of_isLimit_type {X Y : Type v} {f g : X ⟶ Y} {c : Fork f g}
    (hc : IsLimit c) {x : X} (hx : f x = g x) : ∃ p : c.pt, c.ι p = x :=
  exists_val_eq_of_equiv_subtype (Fork.IsLimit.ptEquivSubtype hc) hx

end CategoryTheory.Limits

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **A morphism of sheaves of sets whose every component is a bijection is an
isomorphism.** -/
theorem isIso_of_bijective_app {F G : Sheaf J (Type w)} (η : F ⟶ G)
    (h : ∀ U : Cᵒᵖ, Function.Bijective (η.hom.app U)) : IsIso η := by
  have (U : Cᵒᵖ) : IsIso (η.hom.app U) := (isIso_iff_bijective _).2 (h U)
  have : IsIso ((sheafToPresheaf J (Type w)).map η) := NatIso.isIso_of_isIso_app η.hom
  exact isIso_of_reflects_iso η (sheafToPresheaf J (Type w))

/-- **An isomorphism of sheaves of sets is a bijection on the sections over every object.** -/
noncomputable def sheafIsoSectionsEquiv {F G : Sheaf J (Type w)} (e : F ≅ G) (U : Cᵒᵖ) :
    F.obj.obj U ≃ G.obj.obj U :=
  (((sheafToPresheaf J (Type w)).mapIso e).app U).toEquiv

/-- `CategoryTheory.Sheaf.sheafIsoSectionsEquiv e U` is the component of `e` at `U`. -/
@[simp]
theorem sheafIsoSectionsEquiv_apply {F G : Sheaf J (Type w)} (e : F ≅ G) (U : Cᵒᵖ)
    (x : F.obj.obj U) : sheafIsoSectionsEquiv e U x = e.hom.hom.app U x :=
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The presentation isomorphism -/

/-- **The presentation isomorphism of a sheaf on the small étale site.**  The quasi-inverse of
the comparison equivalence of Stacks 03G1 produces, from a sheaf `P` on the small étale site of
`X`, a sheaf on the spaces-étale site of `X`; this is the identification of the restriction of
that sheaf to the scheme charts with `P` itself: the counit of the equivalence, read on
underlying presheaves. -/
noncomputable def smallEtaleDirectImagePresentationIso
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (comparisonFunctor B S hS X).op ⋙
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj ≅ P.obj :=
  (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).mapIso
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app P)

/-- The sections, over an étale scheme chart `W` of `X`, of the restriction to the charts of the
spaces-étale sheaf presenting `P` are the sections of that sheaf over the comparison image of
`W`. -/
theorem smallEtaleDirectImagePresentationIso_obj_obj
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS X.1) :
    ((comparisonFunctor B S hS X).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj).obj
        (op W) =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.obj
        (op ((comparisonFunctor B S hS X).obj W)) :=
  rfl

/-- **Naturality of the presentation isomorphism in the chart.**  Restricting a section of the
spaces-étale sheaf along the comparison image of a morphism of charts and then passing to `P`
is the same as passing to `P` and then restricting. -/
theorem smallEtaleDirectImagePresentationIso_hom_app_naturality
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) {W W' : SmallEtale B S hS X.1}
    (a : W' ⟶ W)
    (x : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.obj
      (op ((comparisonFunctor B S hS X).obj W))) :
    (smallEtaleDirectImagePresentationIso B S hS P).hom.app (op W')
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map
          ((comparisonFunctor B S hS X).map a).op x) =
      P.obj.map a.op
        ((smallEtaleDirectImagePresentationIso B S hS P).hom.app (op W) x) :=
  ConcreteCategory.congr_hom
    ((smallEtaleDirectImagePresentationIso B S hS P).hom.naturality a.op) x

/-- **Naturality of the inverse of the presentation isomorphism in the chart.** -/
theorem smallEtaleDirectImagePresentationIso_inv_app_naturality
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) {W W' : SmallEtale B S hS X.1}
    (a : W' ⟶ W) (y : P.obj.obj (op W)) :
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map
        ((comparisonFunctor B S hS X).map a).op
        ((smallEtaleDirectImagePresentationIso B S hS P).inv.app (op W) y) =
      (smallEtaleDirectImagePresentationIso B S hS P).inv.app (op W') (P.obj.map a.op y) :=
  (ConcreteCategory.congr_hom
    ((smallEtaleDirectImagePresentationIso B S hS P).inv.naturality a.op) y).symm

/-- **The inverse of the presentation isomorphism is injective on the sections over a
chart.** -/
theorem smallEtaleDirectImagePresentationIso_inv_app_injective
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS X.1) :
    Function.Injective ((smallEtaleDirectImagePresentationIso B S hS P).inv.app (op W)) :=
  ((smallEtaleDirectImagePresentationIso B S hS P).app (op W)).toEquiv.symm.injective

/-- The presentation isomorphism and its inverse undo one another on the sections over a
chart. -/
theorem smallEtaleDirectImagePresentationIso_inv_hom_app_eq
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS X.1)
    (x : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.obj
      (op ((comparisonFunctor B S hS X).obj W))) :
    (smallEtaleDirectImagePresentationIso B S hS P).inv.app (op W)
        ((smallEtaleDirectImagePresentationIso B S hS P).hom.app (op W) x) = x :=
  ((smallEtaleDirectImagePresentationIso B S hS P).app (op W)).toEquiv.symm_apply_apply x

/-! ### The equalizer presentation at a chart -/

/-- The commutation of the two arrows of the equalizer diagram of Tag 03H7: when `W'` is the
self-fibre product of `g`, restricting along `g` and then along `a` is restricting along `g` and
then along `b`. -/
theorem smallEtaleDirectImageChartEqualizer_fork_comm
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {U : SpacesEtale B S hS X} {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ U}
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g) :
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map g.op ≫
        ((comparisonFunctor B S hS X).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj).map a.op =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map g.op ≫
        ((comparisonFunctor B S hS X).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj).map
            b.op := by
  change ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map g.op ≫
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map
          ((comparisonFunctor B S hS X).map a).op =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map g.op ≫
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map
          ((comparisonFunctor B S hS X).map b).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hpb.w]

/-- **The equalizer presentation of the sections of the direct image over a chart.**  Let `V`
be an étale scheme chart of `Y`, let `W` be an étale scheme chart of `X` whose comparison image
covers `X ×_Y V` through `g`, and let `W'` be an étale scheme chart of `X` presenting the
self-fibre product of `g`.  Then the sections of `f_{small,*}P` over `V` are in bijection with
the sections of `P` over `W` on which restriction along `a` and along `b` agree. -/
noncomputable def smallEtaleDirectImageChartEqualizerEquiv (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V}
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩)
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g) :
    ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V) ≃
      {y : P.obj.obj (op W) // P.obj.map a.op y = P.obj.map b.op y} :=
  (Fork.IsLimit.ptEquivSubtype (isLimitForkOfEtaleChartCovering B S hS X
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).property hg hpb
      (smallEtaleDirectImageChartEqualizer_fork_comm B S hS P hpb))).trans
    (Functor.equalizerSubtypeEquivOfIso
      (smallEtaleDirectImagePresentationIso B S hS P) a.op b.op)

/-- **Restriction of a section of the direct image to a chart of the source.**  The first arrow
of the equalizer diagram: a section of `f_{small,*}P` over `V`, a section of the presenting
spaces-étale sheaf over `X ×_Y V`, restricted along `g` and carried to a section of `P` over `W`
by the presentation isomorphism. -/
noncomputable def smallEtaleDirectImageChartSection (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W : SmallEtale B S hS X.1}
    (g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V)
    (s : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) : P.obj.obj (op W) :=
  (smallEtaleDirectImagePresentationIso B S hS P).hom.app (op W)
    (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P).obj.map g.op s)

/-- The bijection of the equalizer presentation is restriction to the chart. -/
theorem smallEtaleDirectImageChartEqualizerEquiv_apply (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V}
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩)
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g)
    (s : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (smallEtaleDirectImageChartEqualizerEquiv B S hS f P V hg hpb s).1 =
      smallEtaleDirectImageChartSection B S hS f P V g s :=
  rfl

/-- **The restriction of a section of the direct image to a chart is equalized by the two
projections.** -/
theorem smallEtaleDirectImageChartSection_equalizes (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V}
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g)
    (s : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    P.obj.map a.op (smallEtaleDirectImageChartSection B S hS f P V g s) =
      P.obj.map b.op (smallEtaleDirectImageChartSection B S hS f P V g s) := by
  rw [smallEtaleDirectImageChartSection,
    ← smallEtaleDirectImagePresentationIso_hom_app_naturality B S hS P a,
    ← smallEtaleDirectImagePresentationIso_hom_app_naturality B S hS P b]
  exact congrArg ((smallEtaleDirectImagePresentationIso B S hS P).hom.app (op W'))
    (ConcreteCategory.congr_hom
      (smallEtaleDirectImageChartEqualizer_fork_comm B S hS P hpb) s)

/-- **A section of the direct image over a chart of the target is determined by its restriction
to a chart covering the base change.** -/
theorem smallEtaleDirectImageChartEqualizerEquiv_injective (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V}
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩)
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g) :
    Function.Injective (smallEtaleDirectImageChartSection B S hS f P V g) :=
  injective_val_comp_equiv_subtype (smallEtaleDirectImageChartEqualizerEquiv B S hS f P V hg hpb)

/-- **Every section over the chart equalized by the two projections is the restriction of a
section of the direct image.** -/
theorem smallEtaleDirectImageChartEqualizerEquiv_exists (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W W' : SmallEtale B S hS X.1} {a b : W' ⟶ W}
    {g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V}
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩)
    (hpb : IsPullback ((comparisonFunctor B S hS X).map a)
      ((comparisonFunctor B S hS X).map b) g g)
    (y : P.obj.obj (op W)) (hy : P.obj.map a.op y = P.obj.map b.op y) :
    ∃ s : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V),
      smallEtaleDirectImageChartSection B S hS f P V g s = y :=
  exists_val_eq_of_equiv_subtype (smallEtaleDirectImageChartEqualizerEquiv B S hS f P V hg hpb) hy

/-- **The equalizer presentation of the sections of the direct image over a chart, from a
covering chart of the base change.**  Given an étale scheme chart `W` of `X` whose comparison
image covers `X ×_Y V` through `g`, there are an étale scheme chart `W'` of `X` and morphisms
`a, b : W' ⟶ W` such that the sections of `f_{small,*}P` over `V` are in bijection with the
sections of `P` over `W` on which restriction along `a` and along `b` agree. -/
theorem exists_smallEtaleDirectImageChartEqualizerEquiv_of_presentation (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    {W : SmallEtale B S hS X.1}
    (g : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V)
    (hg : SpacesEtale.IsCovering B S hS X
      ⟨chartBaseChange B S hS f V, PreZeroHypercover.singleton.{u + 1} g⟩) :
    ∃ (W' : SmallEtale B S hS X.1) (a b : W' ⟶ W),
      Nonempty (((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V) ≃
        {y : P.obj.obj (op W) // P.obj.map a.op y = P.obj.map b.op y}) := by
  obtain ⟨W', a, b, hpb⟩ :=
    exists_etaleChart_isPullback_self B S hS X (chartBaseChange B S hS f V) W g
  exact ⟨W', a, b, ⟨smallEtaleDirectImageChartEqualizerEquiv B S hS f P V hg hpb⟩⟩

/-- **Tag 03H7 for the direct image on the small étale sites.**  Let `f : X ⟶ Y` be a morphism
of algebraic spaces, let `P` be a sheaf of sets on the small étale site of `X`, and let `V` be
an étale scheme chart of `Y`.  Then there are étale scheme charts `W`, `W'` of `X` and two
morphisms `a, b : W' ⟶ W` such that

`(f_{small,*}P)(V) ⟶ P(W) ⇉ P(W')`

is an equalizer: the sections of the direct image over `V` are in bijection with the sections of
`P` over `W` on which restriction along `a` and restriction along `b` agree. -/
@[stacks 03H7 "the equalizer diagram, for the direct image on the small etale sites: the \
sections of f_{small,*}P over an etale scheme chart V of Y are the equalizer of the sections \
of P over an etale scheme chart W covering X x_Y V and over a chart W' presenting the \
self-fibre product of W over X x_Y V"]
theorem exists_smallEtaleDirectImageChartEqualizerEquiv (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1) :
    ∃ (W W' : SmallEtale B S hS X.1) (a b : W' ⟶ W),
      Nonempty (((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V) ≃
        {y : P.obj.obj (op W) // P.obj.map a.op y = P.obj.map b.op y}) := by
  obtain ⟨W, g, -, -, hg⟩ :=
    exists_etaleChart_singleton_covering B S hS X (chartBaseChange B S hS f V)
  exact ⟨W, exists_smallEtaleDirectImageChartEqualizerEquiv_of_presentation B S hS f P V g hg⟩

end AlgebraicGeometry.Space

end
