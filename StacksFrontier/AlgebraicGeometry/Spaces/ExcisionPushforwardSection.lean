module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardGluing

/-!
# Evaluating a pair at a section of the fibre product

Keep the data of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforwardGluing.lean`: a separated étale
`f : V ⟶ W`, a subfunctor `T` of `W` whose preimage is carried isomorphically onto it, a
subfunctor `W₀` containing the open complement of `T`, and `h : Y ⟶ V` invertible over
`f^{-1}W₀`.

A pair `(w, y)` of Stacks 05Y1 over a scheme `A` consists of `w : A ⟶ W` and
`y : A ×_{w, W} V ⟶ Y`. When `w` factors as `β` followed by `f` for some `β : A ⟶ V`, the
fibre product `A ×_{w, W} V` has a canonical section, the graph of `β`, and *evaluating* `y`
there produces a section of `Y` over `A`. That evaluation is the inverse of the construction
which turns a section of `Y` into a pair, and the whole identification of the base change of the
quasi-inverse of Stacks 0BGY with the given object is the statement that the two are mutually
inverse.

This file supplies the evaluation and the one thing that makes it faithful: a pair whose second
component is a morphism over `V` is *determined* by its evaluation, because the two pieces of
the fibre square cover `A ×_{w, W} V` and on the diagonal piece everything is pulled back from
the canonical section.

## Main definitions

* `AlgebraicGeometry.Space.pairEval`: the evaluation of a pair at the graph of `β`.

## Main results

* `AlgebraicGeometry.Space.pairEval_congr` and
  `AlgebraicGeometry.Space.pairEval_congr_beta`: the evaluation depends on the pair and on `β`
  only through their values.
* `AlgebraicGeometry.Space.pairEval_comp`: the image in `V` of the evaluation is `β`.
* `AlgebraicGeometry.Space.excisionGlue_ext_section`: two lifts along `h` of the second
  projection which agree on the graph of `β` are equal.
* `AlgebraicGeometry.Space.relativeMorphism_ext_of_pairEval`: **a pair over `β` whose second
  component is a morphism over `V` is determined by its evaluation.**

## Implementation notes

`AlgebraicGeometry.Space.pairEval` carries the factorisation `q.base = β ≫ f` as an explicit
argument, so that the two congruence lemmas are proved by substituting a variable and appealing
to proof irrelevance. That is what the dependence of the type of the second component of a pair
on its first component costs: the evaluation cannot be stated as a function of the pair alone.

For the same reason `AlgebraicGeometry.Space.relativeMorphism_ext_of_pairEval` destructs the two
pairs and substitutes the two factorisations before comparing the second components, which is
the only way to bring them into one type.

`AlgebraicGeometry.Space.excisionGlue_ext_section` is
`AlgebraicGeometry.Space.excisionGlue_ext` at the morphism `κ` which reads a section of
`A ×_{β ≫ f, W} V` as a section of `V ×_W V`; the hypothesis that the two lifts agree on the
diagonal piece holds because on that piece the identity of `A ×_{β ≫ f, W} V` factors through
the graph of `β`.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)

/-! ### The graph of a morphism to `V` -/

/-- The graph of `β : P ⟶ V` inside the fibre product of `β ≫ f` with `f`. -/
noncomputable def graphSection {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    P ⟶ pullback (β ≫ f) f :=
  pullback.lift (𝟙 P) β (Category.id_comp _)

/-- The first component of the graph of `β` is the identity. -/
@[simp, reassoc (attr := simp)]
theorem graphSection_fst {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    graphSection B S hS f β ≫ pullback.fst (β ≫ f) f = 𝟙 P :=
  pullback.lift_fst _ _ _

/-- The second component of the graph of `β` is `β`. -/
@[simp, reassoc (attr := simp)]
theorem graphSection_snd {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    graphSection B S hS f β ≫ pullback.snd (β ≫ f) f = β :=
  pullback.lift_snd _ _ _

/-! ### Evaluating a pair -/

/-- **The evaluation of a pair at the graph of `β`.** For a pair `(w, y)` whose first component
factors as `β ≫ f`, this is the section of `Y` obtained by restricting `y` along the graph
of `β`. -/
noncomputable def pairEval {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V)
    (q : RelativeMorphism B S hS V Y W f (h ≫ f) P) (hq : q.base = β ≫ f) : P ⟶ Y :=
  pullback.lift (𝟙 P) β (by rw [Category.id_comp, hq]) ≫ q.morphism

/-- The evaluation of a pair depends on the pair only through its value. -/
theorem pairEval_congr {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V)
    {q₁ q₂ : RelativeMorphism B S hS V Y W f (h ≫ f) P} (hq₁ : q₁.base = β ≫ f)
    (hq₂ : q₂.base = β ≫ f) (e : q₁ = q₂) :
    pairEval B S hS f h β q₁ hq₁ = pairEval B S hS f h β q₂ hq₂ := by
  subst e; rfl

/-- The evaluation of a pair depends on `β` only through its value. -/
theorem pairEval_congr_beta {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {β₁ β₂ : P ⟶ V}
    (e : β₁ = β₂) (q : RelativeMorphism B S hS V Y W f (h ≫ f) P) (hq₁ : q.base = β₁ ≫ f)
    (hq₂ : q.base = β₂ ≫ f) :
    pairEval B S hS f h β₁ q hq₁ = pairEval B S hS f h β₂ q hq₂ := by
  subst e; rfl

/-- The image in `V` of the evaluation of a pair whose second component is a morphism over `V`
is `β`. -/
theorem pairEval_comp {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V)
    (q : RelativeMorphism B S hS V Y W f (h ≫ f) P) (hq : q.base = β ≫ f)
    (hm : q.morphism ≫ h = pullback.snd q.base f) :
    pairEval B S hS f h β q hq ≫ h = β := by
  rw [pairEval, Category.assoc, hm, pullback.lift_snd]

/-! ### A pair over `β` is determined by its evaluation -/

variable (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y) (T W₀ : Subfunctor W)
  (hT : IsIso (T.fromPreimage f)) (hcompl : openComplement B S hS T ≤ W₀)
  (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)
  (hiso : IsIso (pullback.snd h (W₀.preimage f).ι))

/-- The morphism reading a section of `A ×_{β ≫ f, W} V` as a section of `V ×_W V`. -/
noncomputable def graphKappa {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    pullback (β ≫ f) f ⟶ pullback f f :=
  pullback.lift (pullback.fst (β ≫ f) f ≫ β) (pullback.snd (β ≫ f) f)
    (by rw [Category.assoc, pullback.condition])

/-- The first component of `graphKappa` is the first projection followed by `β`. -/
@[simp, reassoc (attr := simp)]
theorem graphKappa_fst {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    graphKappa B S hS f β ≫ pullback.fst f f = pullback.fst (β ≫ f) f ≫ β :=
  pullback.lift_fst _ _ _

/-- The second component of `graphKappa` is the second projection. -/
@[simp, reassoc (attr := simp)]
theorem graphKappa_snd {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V) :
    graphKappa B S hS f β ≫ pullback.snd f f = pullback.snd (β ≫ f) f :=
  pullback.lift_snd _ _ _

include hV hW hY hf hsep hT hcompl hiso in
/-- **Two lifts along `h` of the second projection which agree on the graph of `β` are
equal.** -/
theorem excisionGlue_ext_section {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P) (m₁ m₂ : pullback (β ≫ f) f ⟶ Y)
    (hm₁ : m₁ ≫ h = pullback.snd (β ≫ f) f) (hm₂ : m₂ ≫ h = pullback.snd (β ≫ f) f)
    (hgraph : graphSection B S hS f β ≫ m₁ = graphSection B S hS f β ≫ m₂) : m₁ = m₂ := by
  have hQ : IsAlgebraicSpace B S hS (pullback (β ≫ f) f) :=
    isAlgebraicSpace_pullback B S hS (β ≫ f) f hP hV hW
  have hback : ((diagOpen B S hS f).preimage (graphKappa B S hS f β)).ι ≫
      pullback.fst (β ≫ f) f ≫ graphSection B S hS f β =
        ((diagOpen B S hS f).preimage (graphKappa B S hS f β)).ι := by
    have hdiag := diagPreimage_comp_fst_eq_snd B S hS f hV hW hf hsep (graphKappa B S hS f β)
    simp only [graphKappa_fst, graphKappa_snd] at hdiag
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [Category.assoc, graphSection_snd]
      exact hdiag
  refine excisionGlue_ext B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
    (graphKappa B S hS f β) hQ m₁ m₂ ?_ ?_ ?_
  · rw [hm₁, graphKappa_snd]
  · rw [hm₂, graphKappa_snd]
  · rw [← hback]
    simp only [Category.assoc]
    rw [hgraph]

include hV hW hY hf hsep hT hcompl hiso in
/-- **A pair over `β` whose second component is a morphism over `V` is determined by its
evaluation.** -/
theorem relativeMorphism_ext_of_pairEval {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (β : P ⟶ V)
    (hP : IsAlgebraicSpace B S hS P)
    {q₁ q₂ : RelativeMorphism B S hS V Y W f (h ≫ f) P}
    (hq₁ : q₁.base = β ≫ f) (hq₂ : q₂.base = β ≫ f)
    (hm₁ : q₁.morphism ≫ h = pullback.snd q₁.base f)
    (hm₂ : q₂.morphism ≫ h = pullback.snd q₂.base f)
    (heval : pairEval B S hS f h β q₁ hq₁ = pairEval B S hS f h β q₂ hq₂) : q₁ = q₂ := by
  obtain ⟨b₁, m₁, c₁⟩ := q₁
  obtain ⟨b₂, m₂, c₂⟩ := q₂
  cases hq₁
  cases hq₂
  refine RelativeMorphism.ext_of_heq rfl (heq_of_eq ?_)
  exact excisionGlue_ext_section B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso β hP
    m₁ m₂ hm₁ hm₂ heval

end AlgebraicGeometry.Space

end
