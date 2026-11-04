module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# Morphisms into the relative morphism functor

Let `S` be a scheme contained in a big fppf site `B` and let `z : Z ⟶ Q` and `x : X ⟶ Q` be
morphisms of algebraic spaces over `S`. The relative morphism functor `Mor_Q(Z, X)` of
Stacks 05Y2 is a presheaf on the big fppf site of `S` whose sections over a *scheme* `V` are the
pairs `(a, b)` of Stacks 05Y1 at `V`. This file identifies the morphisms *into* it from an
arbitrary test presheaf — in particular from an algebraic space over `S` — with the pairs
`(a, b)` at that test object, which is part (2) of Stacks 05Y3.

The identification needs no sheaf condition and no algebraicity of the test object: a pair is a
morphism `a` to `Q` together with a morphism out of the base change `T ×_{a, Q} Z`, and both of
those are determined by, and can be glued from, their restrictions along the morphisms from
representable presheaves.

Because the identification holds at an arbitrary test presheaf, it can be read at the presheaf
of a covering sieve, and the file then also proves part (1) of Stacks 05Y3: the relative
morphism functor is a sheaf on the big fppf site of `S`. The sheaf condition at a covering
sieve `R` of a scheme `V` becomes the statement that a pair over the presheaf of `R` extends
uniquely to a pair over `V`, which splits into the sheaf condition for `Q` on the first
component and, on the second, descent of morphisms into `X` along the base change of the
inclusion `R ⊆ V`. No descent theory for algebraic spaces is needed: the inclusion of a sieve
is a monomorphism, and the inclusion of a *covering* sieve is locally surjective, and both
properties pass to a base change for elementary reasons.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism.eval`: the value of a pair `(a, b)` at a point of
  `T ×_{a, Q} Z` presented by a morphism to `T` and a morphism to `Z` agreeing over `Q`, and
  `AlgebraicGeometry.Space.RelativeMorphism.evalPt`, its form at a scheme-valued point.
* `AlgebraicGeometry.Space.relativeMorphismOfHom` and
  `AlgebraicGeometry.Space.homOfRelativeMorphism`: the two mutually inverse constructions of
  part (2) of Stacks 05Y3.
* `AlgebraicGeometry.Space.relativeHomEquivPresheaf`: part (2) of Stacks 05Y3 with the
  algebraicity of the test object dropped.

## Main results

* `AlgebraicGeometry.Space.relativeHomEquiv`: **Stacks 05Y3**, part (2) — the canonical
  bijection between the morphisms from a test object `T` to `Mor_Q(Z, X)` and the pairs `(a, b)`
  of Stacks 05Y1 at `T`.
* `CategoryTheory.Presheaf.IsSheaf.existsUnique_comp_eq`: maps into a sheaf extend uniquely
  along a morphism of presheaves of types which is injective on sections and locally
  surjective. Applied to the base change of the inclusion of a covering sieve
  (`AlgebraicGeometry.Space.existsUnique_comp_mapFst_functorInclusion_eq`), it is what makes
  the second component of a pair descend.
* `AlgebraicGeometry.Space.existsUnique_restrict_functorInclusion_eq` and
  `AlgebraicGeometry.Space.RelativeMorphism.ext_of_restrict_functorInclusion`: part (1) read
  through the pairs of Stacks 05Y1 — a pair over the presheaf of a covering sieve extends
  uniquely to a pair over the represented presheaf.
* `AlgebraicGeometry.Space.relativeHomEquiv_yoneda` and
  `AlgebraicGeometry.Space.relativeHomEquiv_naturality`: the bijection extends the
  identification `AlgebraicGeometry.Space.relativeHomSections` of the sections over a scheme
  with pairs, and is natural in the test object. Together these pin the bijection down, so it
  is *the* canonical one.
* `AlgebraicGeometry.Space.RelativeMorphism.ext_of_restrict`: a pair over a test presheaf is
  determined by its restrictions along the morphisms from representable presheaves.

## Implementation notes

The second component of a pair goes out of a base change, so it cannot be evaluated at a point
of the test object alone; `AlgebraicGeometry.Space.RelativeMorphism.eval` evaluates it at a
*compatible* pair of morphisms, and
`AlgebraicGeometry.Space.RelativeMorphism.evalPt_restrict` is the one law needed about it: the
second component of the pair attached to a morphism `v : T ⟶ Mor_Q(Z, X)` is built out of
`evalPt` applied to the pairs `v` produces over schemes, and its naturality is exactly that law.

Because the second component's type depends on the first, equalities of pairs are consumed
through `AlgebraicGeometry.Space.RelativeMorphism.eval_eq_of_eq`, and pairs are compared through
`AlgebraicGeometry.Space.RelativeMorphism.ext_of_eval`; both avoid transporting a morphism along
an equality of base changes.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- The morphism from a representable presheaf attached to a member of a sieve lifts that member
along the inclusion of the sieve into the represented presheaf. -/
theorem Sieve.toFunctor_comp_functorInclusion {V : C} (R : Sieve V) {W : C} (f : W ⟶ V)
    (hf : R f) : R.toFunctor f hf ≫ R.functorInclusion = yoneda.map f := rfl

/-- A morphism between representable presheaves is the image of the morphism it corresponds to. -/
private theorem yoneda_map_yonedaEquiv {V W : C} (γ : yoneda.obj W ⟶ yoneda.obj V) :
    yoneda.map (yonedaEquiv γ) = γ :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

namespace Presheaf

/-- **Maps into a sheaf extend uniquely along a morphism of presheaves which is injective on
sections and locally surjective.** The hypotheses say that `m : A ⟶ P` is a monomorphism, as
seen on morphisms from representable presheaves, and that every morphism from a representable
presheaf to `P` factors through `m` after restriction along some covering sieve. Both are
checked on morphisms from representable presheaves rather than on sections, which is the form
in which a base change of a sieve inclusion satisfies them. -/
theorem IsSheaf.existsUnique_comp_eq {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ Type v₁}
    (hG : Presheaf.IsSheaf J G) {A P : Cᵒᵖ ⥤ Type v₁} (m : A ⟶ P)
    (hinj : ∀ {W : C} (u₁ u₂ : yoneda.obj W ⟶ A), u₁ ≫ m = u₂ ≫ m → u₁ = u₂)
    (hsurj : ∀ (W : C) (p : yoneda.obj W ⟶ P), ∃ R : Sieve W, R ∈ J W ∧
      ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g →
        ∃ u : yoneda.obj W' ⟶ A, u ≫ m = yoneda.map g ≫ p)
    (c : A ⟶ G) : ∃! b : P ⟶ G, m ≫ b = c := by
  classical
  have hG' : Presieve.IsSheaf J G := (isSheaf_iff_isSheaf_of_type J G).mp hG
  have hinj' : ∀ {W : C} (a₁ a₂ : A.obj (op W)),
      m.app (op W) a₁ = m.app (op W) a₂ → a₁ = a₂ := by
    intro W a₁ a₂ h
    refine yonedaEquiv.symm.injective (hinj (yonedaEquiv.symm a₁) (yonedaEquiv.symm a₂) ?_)
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  have hsurj' : ∀ (W : C) (pe : P.obj (op W)), ∃ R : Sieve W, R ∈ J W ∧
      ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g →
        ∃ ae : A.obj (op W'), m.app (op W') ae = P.map g.op pe := by
    intro W pe
    obtain ⟨R, hR, hfac⟩ := hsurj W (yonedaEquiv.symm pe)
    refine ⟨R, hR, ?_⟩
    intro W' g hg
    obtain ⟨u, hu⟩ := hfac g hg
    exact ⟨yonedaEquiv u, by
      rw [← yonedaEquiv_comp, hu, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]⟩
  have key : ∀ (W : C) (pe : P.obj (op W)), ∃! t : G.obj (op W),
      ∀ ⦃W' : C⦄ (g : W' ⟶ W) (ae : A.obj (op W')),
        m.app (op W') ae = P.map g.op pe → G.map g.op t = c.app (op W') ae := by
    intro W pe
    obtain ⟨R, hR, hfac⟩ := hsurj' W pe
    choose sec hsec using fun (W' : C) (g : W' ⟶ W) (hg : R g) => hfac g hg
    have hA : ∀ (W' W'' : C) (g : W' ⟶ W) (r : W'' ⟶ W') (hrg : R (r ≫ g))
        (ae : A.obj (op W')), m.app (op W') ae = P.map g.op pe →
        A.map r.op ae = sec W'' (r ≫ g) hrg := by
      intro W' W'' g r hrg ae hae
      refine hinj' _ _ ?_
      rw [NatTrans.naturality_apply, hae, hsec, ← Functor.map_comp_apply, ← op_comp]
    let fam : Presieve.FamilyOfElements G R.arrows :=
      fun W' g hg => c.app (op W') (sec W' g hg)
    have hcompat : fam.Compatible := by
      intro W₁ W₂ Y e₁ e₂ g₁ g₂ h₁ h₂ hcomm
      have hAA : A.map e₁.op (sec W₁ g₁ h₁) = A.map e₂.op (sec W₂ g₂ h₂) := by
        refine hinj' _ _ ?_
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hsec, hsec,
          ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
      show G.map e₁.op (c.app (op W₁) (sec W₁ g₁ h₁)) =
        G.map e₂.op (c.app (op W₂) (sec W₂ g₂ h₂))
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hAA]
    obtain ⟨t, ht, htu⟩ := hG' R hR fam hcompat
    refine ⟨t, ?_, fun t' ht' => htu t' fun W' g hg => ht' g (sec W' g hg) (hsec W' g hg)⟩
    intro W' g ae hae
    refine (hG' (R.pullback g) (J.pullback_stable g hR)).isSeparatedFor.ext ?_
    intro W'' r hr
    have hrR : R (r ≫ g) := hr
    calc G.map r.op (G.map g.op t) = G.map (r ≫ g).op t := by
          rw [← Functor.map_comp_apply, ← op_comp]
      _ = fam (r ≫ g) hrR := ht _ hrR
      _ = c.app (op W'') (sec W'' (r ≫ g) hrR) := rfl
      _ = c.app (op W'') (A.map r.op ae) := by rw [hA W' W'' g r hrR ae hae]
      _ = G.map r.op (c.app (op W') ae) := NatTrans.naturality_apply c r.op ae
  let b : P ⟶ G :=
    { app := fun W => ↾fun pe => (key W.unop pe).choose
      naturality := by
        intro Y Z f
        obtain ⟨Y⟩ := Y
        obtain ⟨Z⟩ := Z
        ext pe
        show (key Z (P.map f pe)).choose = G.map f ((key Y pe).choose)
        refine ((key Z (P.map f pe)).choose_spec.2 _ ?_).symm
        intro W' g ae hae
        have h1 : m.app (op W') ae = P.map (g ≫ f.unop).op pe := by
          rw [hae, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]
        have h2 := (key Y pe).choose_spec.1 (g ≫ f.unop) ae h1
        rwa [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] at h2 }
  refine ⟨b, ?_, ?_⟩
  · refine NatTrans.ext (funext fun W => ?_)
    obtain ⟨W⟩ := W
    apply ConcreteCategory.ext
    ext ae
    show (key W (m.app (op W) ae)).choose = c.app (op W) ae
    simpa using (key W (m.app (op W) ae)).choose_spec.1 (𝟙 W) ae (by simp)
  · intro b' hb'
    refine NatTrans.ext (funext fun W => ?_)
    obtain ⟨W⟩ := W
    apply ConcreteCategory.ext
    ext pe
    show b'.app (op W) pe = (key W pe).choose
    refine (key W pe).choose_spec.2 _ ?_
    intro W' g ae hae
    rw [← NatTrans.naturality_apply, ← hae]
    have h := congrArg (fun α : A ⟶ G => α.app (op W') ae) hb'
    simpa using h

end Presheaf

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-! ### Evaluating a pair at a point of the base change -/

/-- The second component of a restricted pair, written through
`CategoryTheory.Limits.pullback.mapFst`. -/
theorem RelativeMorphism.restrict_morphism_mapFst
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.restrict t p).morphism = pullback.mapFst t p.base z ≫ p.morphism := by
  rw [RelativeMorphism.restrict_morphism, pullback.map_id_eq_mapFst]

/-- The value of a pair `(a, b)` over `T` at the point of `T ×_{a, Q} Z` presented by a morphism
`γ : W ⟶ T` and a morphism `s : W ⟶ Z` which agree over `Q`. -/
noncomputable def RelativeMorphism.eval {T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) (γ : W ⟶ T) (s : W ⟶ Z)
    (h : γ ≫ p.base = s ≫ z) : W ⟶ X :=
  pullback.lift γ s h ≫ p.morphism

/-- The evaluation of a pair lies over `Q`. -/
theorem RelativeMorphism.eval_comp {T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) (γ : W ⟶ T) (s : W ⟶ Z)
    (h : γ ≫ p.base = s ≫ z) : p.eval γ s h ≫ x = s ≫ z := by
  rw [RelativeMorphism.eval, Category.assoc, p.commutes, ← Category.assoc, pullback.lift_snd]

/-- The evaluation of a pair depends only on the two morphisms presenting the point. -/
theorem RelativeMorphism.eval_congr {T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) {γ γ' : W ⟶ T} {s s' : W ⟶ Z} (hγ : γ = γ')
    (hs : s = s') (h : γ ≫ p.base = s ≫ z) (h' : γ' ≫ p.base = s' ≫ z) :
    p.eval γ s h = p.eval γ' s' h' := by
  cases hγ
  cases hs
  rfl

/-- Equal pairs have equal evaluations. This is the form in which an equality of pairs is used:
the second component's type depends on the first, so the two evaluations are compared directly
rather than after a transport. -/
theorem RelativeMorphism.eval_eq_of_eq {T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : RelativeMorphism B S hS Z X Q z x T} (hpq : p = q) (γ : W ⟶ T) (s : W ⟶ Z)
    (hp : γ ≫ p.base = s ≫ z) (hq : γ ≫ q.base = s ≫ z) :
    p.eval γ s hp = q.eval γ s hq := by
  cases hpq
  rfl

/-- Evaluation is compatible with precomposition. -/
theorem RelativeMorphism.comp_eval {T W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) (δ : W' ⟶ W) (γ : W ⟶ T) (s : W ⟶ Z)
    (h : γ ≫ p.base = s ≫ z) (h' : (δ ≫ γ) ≫ p.base = (δ ≫ s) ≫ z) :
    δ ≫ p.eval γ s h = p.eval (δ ≫ γ) (δ ≫ s) h' := by
  have key : δ ≫ pullback.lift γ s h = pullback.lift (δ ≫ γ) (δ ≫ s) h' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [RelativeMorphism.eval, RelativeMorphism.eval, ← Category.assoc, key]

/-- Precomposing the comparison map of base changes with a lift. -/
theorem pullback.lift_comp_mapFst {C : Type*} [Category C] {W W' A Y P : C} (t : W' ⟶ W)
    (a : W ⟶ Y) (zz : A ⟶ Y) [HasPullback a zz] [HasPullback (t ≫ a) zz] (γ : P ⟶ W')
    (s : P ⟶ A) (h : γ ≫ t ≫ a = s ≫ zz) (h' : (γ ≫ t) ≫ a = s ≫ zz) :
    pullback.lift γ s h ≫ pullback.mapFst t a zz = pullback.lift (γ ≫ t) s h' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.mapFst_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst]
  · rw [Category.assoc, pullback.mapFst_snd, pullback.lift_snd, pullback.lift_snd]

/-- Evaluating a restricted pair is evaluating the original pair. -/
theorem RelativeMorphism.eval_restrict {T T' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) (t : T' ⟶ T) (γ : W ⟶ T') (s : W ⟶ Z)
    (h : γ ≫ (RelativeMorphism.restrict t p).base = s ≫ z) (h' : (γ ≫ t) ≫ p.base = s ≫ z) :
    (RelativeMorphism.restrict t p).eval γ s h = p.eval (γ ≫ t) s h' := by
  have h₀ : γ ≫ t ≫ p.base = s ≫ z := h
  have key : pullback.lift γ s h₀ ≫ pullback.mapFst t p.base z = pullback.lift (γ ≫ t) s h' :=
    pullback.lift_comp_mapFst t p.base z γ s h₀ h'
  show pullback.lift γ s h ≫ (RelativeMorphism.restrict t p).morphism =
    pullback.lift (γ ≫ t) s h' ≫ p.morphism
  rw [RelativeMorphism.restrict_morphism_mapFst]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p.morphism) key)

/-- A restricted pair, evaluated at the identity, is the original pair evaluated at the
restricting morphism. -/
theorem RelativeMorphism.eval_restrict_id {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) (t : T' ⟶ T) (s : T' ⟶ Z)
    (h : t ≫ p.base = s ≫ z)
    (h' : 𝟙 T' ≫ (RelativeMorphism.restrict t p).base = s ≫ z) :
    (RelativeMorphism.restrict t p).eval (𝟙 T') s h' = p.eval t s h := by
  rw [RelativeMorphism.eval_restrict p t (𝟙 T') s h'
    (by rwa [Category.id_comp])]
  exact RelativeMorphism.eval_congr p (Category.id_comp t) rfl _ h

/-- Two pairs over the same test object agree as soon as their first components agree and all
their evaluations at points coming from representable presheaves agree. -/
theorem RelativeMorphism.ext_of_eval {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : RelativeMorphism B S hS Z X Q z x T} (hbase : p.base = q.base)
    (h : ∀ (W : BigFppfOver B S hS) (γ : yoneda.obj W ⟶ T) (s : yoneda.obj W ⟶ Z)
      (hp : γ ≫ p.base = s ≫ z) (hq : γ ≫ q.base = s ≫ z), p.eval γ s hp = q.eval γ s hq) :
    p = q := by
  refine RelativeMorphism.ext_of_base_eq hbase (hom_ext_yoneda fun W γ => ?_)
  have hp : (γ ≫ pullback.fst p.base z) ≫ p.base = (γ ≫ pullback.snd p.base z) ≫ z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hq : (γ ≫ pullback.fst p.base z) ≫ q.base = (γ ≫ pullback.snd p.base z) ≫ z := by
    rwa [← hbase]
  have e1 : pullback.lift (γ ≫ pullback.fst p.base z) (γ ≫ pullback.snd p.base z) hp = γ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  have e2 : pullback.lift (γ ≫ pullback.fst p.base z) (γ ≫ pullback.snd p.base z) hq =
      γ ≫ (pullback.congrHom hbase (rfl : z = z)).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc]
      simp
    · rw [pullback.lift_snd, Category.assoc]
      simp
  calc γ ≫ p.morphism
      = pullback.lift (γ ≫ pullback.fst p.base z) (γ ≫ pullback.snd p.base z) hp ≫
          p.morphism := by rw [e1]
    _ = q.eval (γ ≫ pullback.fst p.base z) (γ ≫ pullback.snd p.base z) hq :=
        h W _ _ hp hq
    _ = pullback.lift (γ ≫ pullback.fst p.base z) (γ ≫ pullback.snd p.base z) hq ≫
          q.morphism := rfl
    _ = (γ ≫ (pullback.congrHom hbase (rfl : z = z)).hom) ≫ q.morphism := by rw [e2]
    _ = γ ≫ (pullback.congrHom hbase (rfl : z = z)).hom ≫ q.morphism := Category.assoc _ _ _

/-- A pair over a test presheaf is determined by its restrictions along the morphisms from
representable presheaves. -/
theorem RelativeMorphism.ext_of_restrict {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : RelativeMorphism B S hS Z X Q z x T}
    (h : ∀ (V : BigFppfOver B S hS) (η : yoneda.obj V ⟶ T),
      RelativeMorphism.restrict η p = RelativeMorphism.restrict η q) : p = q := by
  have hbase : p.base = q.base := by
    refine hom_ext_yoneda fun V η => ?_
    simpa only [RelativeMorphism.restrict_base] using
      congrArg RelativeMorphism.base (h V η)
  refine RelativeMorphism.ext_of_eval hbase fun W γ s hp hq => ?_
  have hp' : 𝟙 (yoneda.obj W) ≫ (RelativeMorphism.restrict γ p).base = s ≫ z := by
    rwa [RelativeMorphism.restrict_base, Category.id_comp]
  have hq' : 𝟙 (yoneda.obj W) ≫ (RelativeMorphism.restrict γ q).base = s ≫ z := by
    rwa [RelativeMorphism.restrict_base, Category.id_comp]
  rw [← RelativeMorphism.eval_restrict_id p γ s hp hp',
    ← RelativeMorphism.eval_restrict_id q γ s hq hq']
  exact RelativeMorphism.eval_eq_of_eq (h W γ) _ _ hp' hq'

/-- The value of a pair over a representable presheaf at the scheme-valued point presented by a
morphism `sm` to `Z` whose composite with `z` is the first component of the pair. -/
noncomputable def RelativeMorphism.evalPt {V : BigFppfOver B S hS}
    (r : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) (sm : yoneda.obj V ⟶ Z)
    (h : r.base = sm ≫ z) : X.obj (op V) :=
  yonedaEquiv (r.eval (𝟙 (yoneda.obj V)) sm (by rw [Category.id_comp]; exact h))

/-- The scheme-valued evaluation of a pair lies over `Q`. -/
theorem RelativeMorphism.x_app_evalPt {V : BigFppfOver B S hS}
    (r : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) (sm : yoneda.obj V ⟶ Z)
    (h : r.base = sm ≫ z) :
    x.app (op V) (r.evalPt sm h) = z.app (op V) (yonedaEquiv sm) := by
  rw [RelativeMorphism.evalPt, ← yonedaEquiv_comp, RelativeMorphism.eval_comp,
    yonedaEquiv_comp]

/-- The scheme-valued evaluation of a restricted pair. This is the naturality of the second
component of the pair attached to a morphism into the relative morphism functor. -/
theorem RelativeMorphism.evalPt_restrict {V W : BigFppfOver B S hS}
    (r : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) (f : W ⟶ V)
    (sm : yoneda.obj V ⟶ Z) (h : r.base = sm ≫ z)
    (h' : (RelativeMorphism.restrict (yoneda.map f) r).base = (yoneda.map f ≫ sm) ≫ z) :
    (RelativeMorphism.restrict (yoneda.map f) r).evalPt (yoneda.map f ≫ sm) h' =
      X.map f.op (r.evalPt sm h) := by
  have hid : 𝟙 (yoneda.obj W) ≫ (RelativeMorphism.restrict (yoneda.map f) r).base =
      (yoneda.map f ≫ sm) ≫ z := by rwa [Category.id_comp]
  have hcomp : yoneda.map f ≫ r.base = (yoneda.map f ≫ sm) ≫ z := by
    rw [h, Category.assoc]
  have hid' : 𝟙 (yoneda.obj V) ≫ r.base = sm ≫ z := by rwa [Category.id_comp]
  have hstep : (yoneda.map f ≫ 𝟙 (yoneda.obj V)) ≫ r.base =
      (yoneda.map f ≫ sm) ≫ z := by rwa [Category.comp_id]
  rw [RelativeMorphism.evalPt, RelativeMorphism.evalPt,
    RelativeMorphism.eval_restrict_id r (yoneda.map f) (yoneda.map f ≫ sm) hcomp hid,
    yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  rw [RelativeMorphism.comp_eval r (yoneda.map f) (𝟙 (yoneda.obj V)) sm hid' hstep]
  exact RelativeMorphism.eval_congr r (Category.comp_id _) rfl hstep hcomp

/-! ### The pair attached to a morphism into the relative morphism functor -/

/-- The projection of the relative morphism functor reads off the first component of a pair. -/
theorem relativeHomProjection_app (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (x : X ⟶ Q) (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (V : BigFppfOver B S hS)
    (p : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op V)) :
    (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op V) p =
      yonedaEquiv (relativeHomSections B S hS Z X Q z x hZ hX hQ V p).base :=
  (relativeHomData B S hS Z X Q z x hZ hX hQ).projection_sections V p

section Equiv

variable {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
variable {hQ : IsAlgebraicSpace B S hS Q}

/-- The first component of the pair attached to a morphism into the relative morphism functor:
the composite with the projection to `Q`. -/
noncomputable def relativeHomBase {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) : T ⟶ Q :=
  v ≫ relativeHomProjection B S hS Z X Q z x hZ hX hQ

/-- At a scheme-valued point of the test object, the first component of the pair attached to a
morphism into the relative morphism functor is the first component of the pair that morphism
produces there. -/
theorem relativeHomBase_app {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (t : T.obj (op V)) :
    (relativeHomBase v).app (op V) t =
      yonedaEquiv (relativeHomSections B S hS Z X Q z x hZ hX hQ V (v.app (op V) t)).base := by
  show (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op V) (v.app (op V) t) = _
  exact relativeHomProjection_app B S hS Z X Q z x hZ hX hQ V (v.app (op V) t)

/-- The pair which a morphism into the relative morphism functor produces over a scheme has the
expected first component. -/
theorem relativeHomSections_base_eq {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (t : T.obj (op V)) :
    (relativeHomSections B S hS Z X Q z x hZ hX hQ V (v.app (op V) t)).base =
      yonedaEquiv.symm ((relativeHomBase v).app (op V) t) := by
  rw [relativeHomBase_app, Equiv.symm_apply_apply]

/-- At a point of the base change of the first component, the pair produced over a scheme by a
morphism into the relative morphism functor lies over the second coordinate of the point. -/
theorem relativeHomSections_base_comp {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (w : (pullback (relativeHomBase v) z).obj (op V)) :
    (relativeHomSections B S hS Z X Q z x hZ hX hQ V
        (v.app (op V)
          ((pullback.fst (relativeHomBase v) z).app (op V) w))).base =
      yonedaEquiv.symm
          ((pullback.snd (relativeHomBase v) z).app (op V) w) ≫ z := by
  rw [relativeHomSections_base_eq, yonedaEquiv_symm_naturality_right]
  refine congrArg yonedaEquiv.symm ?_
  have h := pullback.condition (f := relativeHomBase v) (g := z)
  exact congrArg (fun k : pullback (relativeHomBase v) z ⟶ Q =>
    k.app (op V) w) h

/-- The second component of the pair attached to a morphism into the relative morphism functor,
read at a point of the base change over a scheme. -/
noncomputable def relativeHomMorphismApp
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (w : (pullback (relativeHomBase v) z).obj (op V)) :
    X.obj (op V) :=
  (relativeHomSections B S hS Z X Q z x hZ hX hQ V
      (v.app (op V)
        ((pullback.fst (relativeHomBase v) z).app (op V) w))).evalPt
    (yonedaEquiv.symm
      ((pullback.snd (relativeHomBase v) z).app (op V) w))
    (relativeHomSections_base_comp v V w)

/-- The defining formula for `AlgebraicGeometry.Space.relativeHomMorphismApp`, with the pair and
the morphism to `Z` supplied as data. -/
theorem relativeHomMorphismApp_eq {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (w : (pullback (relativeHomBase v) z).obj (op V))
    (r : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) (sm : yoneda.obj V ⟶ Z)
    (hr : relativeHomSections B S hS Z X Q z x hZ hX hQ V
      (v.app (op V)
        ((pullback.fst (relativeHomBase v) z).app (op V) w)) = r)
    (hs : yonedaEquiv.symm
      ((pullback.snd (relativeHomBase v) z).app (op V) w) = sm)
    (h : r.base = sm ≫ z) :
    relativeHomMorphismApp v V w = r.evalPt sm h := by
  cases hr
  cases hs
  rfl

/-- The second component of the pair attached to a morphism into the relative morphism
functor. -/
noncomputable def relativeHomMorphism {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) :
    pullback (relativeHomBase v) z ⟶ X where
  app V := ↾fun w => relativeHomMorphismApp v V.unop w
  naturality := by
    intro V W k
    obtain ⟨V⟩ := V
    obtain ⟨W⟩ := W
    ext w
    have hfst := NatTrans.naturality_apply
      (pullback.fst (relativeHomBase v) z) k w
    have hsnd := NatTrans.naturality_apply
      (pullback.snd (relativeHomBase v) z) k w
    have hv := NatTrans.naturality_apply v k
      ((pullback.fst (relativeHomBase v) z).app (op V) w)
    have hmap := relativeHomSections_map B S hS Z X Q z x hZ hX hQ k.unop
      (v.app (op V)
        ((pullback.fst (relativeHomBase v) z).app (op V) w))
    simp only [Quiver.Hom.op_unop] at hmap
    have hsec : relativeHomSections B S hS Z X Q z x hZ hX hQ W
        (v.app (op W)
          ((pullback.fst (relativeHomBase v) z).app (op W)
            ((pullback (relativeHomBase v) z).map k w))) =
        RelativeMorphism.restrict (yoneda.map k.unop)
          (relativeHomSections B S hS Z X Q z x hZ hX hQ V
            (v.app (op V)
              ((pullback.fst (relativeHomBase v) z).app
                (op V) w))) := by
      rw [hfst, hv, hmap]
    have hsm : yonedaEquiv.symm
        ((pullback.snd (relativeHomBase v) z).app (op W)
          ((pullback (relativeHomBase v) z).map k w)) =
        yoneda.map k.unop ≫ yonedaEquiv.symm
          ((pullback.snd (relativeHomBase v) z).app (op V) w) := by
      rw [hsnd]
      exact yonedaEquiv_symm_map k _
    have hbase := relativeHomSections_base_comp v V w
    have hbase' : (RelativeMorphism.restrict (yoneda.map k.unop)
        (relativeHomSections B S hS Z X Q z x hZ hX hQ V
          (v.app (op V)
            ((pullback.fst (relativeHomBase v) z).app
              (op V) w)))).base =
        (yoneda.map k.unop ≫ yonedaEquiv.symm
          ((pullback.snd (relativeHomBase v) z).app
            (op V) w)) ≫ z := by
      rw [RelativeMorphism.restrict_base, hbase, Category.assoc]
    change relativeHomMorphismApp v W
        ((pullback (relativeHomBase v) z).map k w) =
      X.map k.unop.op (relativeHomMorphismApp v V w)
    rw [relativeHomMorphismApp_eq v W
        ((pullback (relativeHomBase v) z).map k w) _ _ hsec hsm hbase',
      relativeHomMorphismApp_eq v V w _ _ rfl rfl hbase,
      RelativeMorphism.evalPt_restrict _ k.unop _ hbase hbase']

/-- The pair attached to a morphism into the relative morphism functor. -/
noncomputable def relativeMorphismOfHom {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) :
    RelativeMorphism B S hS Z X Q z x T where
  base := relativeHomBase v
  morphism := relativeHomMorphism v
  commutes := by
    refine NatTrans.ext (funext fun V => ?_)
    obtain ⟨V⟩ := V
    ext w
    have hbase := relativeHomSections_base_comp v V w
    change x.app (op V) (relativeHomMorphismApp v V w) =
      z.app (op V)
        ((pullback.snd (relativeHomBase v) z).app (op V) w)
    rw [relativeHomMorphismApp_eq v V w _ _ rfl rfl hbase,
      RelativeMorphism.x_app_evalPt, Equiv.apply_symm_apply]

/-- The morphism into the relative morphism functor attached to a pair: over a scheme `V` it
sends a `V`-valued point of the test object to the pair restricted along it. -/
noncomputable def homOfRelativeMorphism {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RelativeMorphism B S hS Z X Q z x T) :
    T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ where
  app V := ↾fun t => (relativeHomSections B S hS Z X Q z x hZ hX hQ V.unop).symm
    (RelativeMorphism.restrict (yonedaEquiv.symm t) p)
  naturality := by
    intro V W k
    obtain ⟨V⟩ := V
    obtain ⟨W⟩ := W
    ext t
    change (relativeHomSections B S hS Z X Q z x hZ hX hQ W).symm
        (RelativeMorphism.restrict (yonedaEquiv.symm (T.map k t)) p) =
      (relativeHom B S hS Z X Q z x hZ hX hQ).map k
        ((relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
          (RelativeMorphism.restrict (yonedaEquiv.symm t) p))
    refine (relativeHomSections B S hS Z X Q z x hZ hX hQ W).injective ?_
    have hmap := relativeHomSections_map B S hS Z X Q z x hZ hX hQ k.unop
      ((relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
        (RelativeMorphism.restrict (yonedaEquiv.symm t) p))
    simp only [Quiver.Hom.op_unop] at hmap
    rw [Equiv.apply_symm_apply, hmap, Equiv.apply_symm_apply, RelativeMorphism.restrict_comp,
      yonedaEquiv_symm_map]

/-- The pair attached to a morphism into the relative morphism functor restricts, along a
scheme-valued point of the test object, to the pair that morphism produces at that point. -/
theorem relativeMorphismOfHom_restrict {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) (V : BigFppfOver B S hS)
    (η : yoneda.obj V ⟶ T) :
    RelativeMorphism.restrict η (relativeMorphismOfHom v) =
      relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v)) := by
  have hvt : yonedaEquiv (η ≫ v) = v.app (op V) (yonedaEquiv η) := yonedaEquiv_comp η v
  have hbase : (RelativeMorphism.restrict η (relativeMorphismOfHom v)).base =
      (relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v))).base := by
    rw [hvt, relativeHomSections_base_eq]
    refine (yonedaEquiv (X := V) (F := Q)).injective ?_
    rw [Equiv.apply_symm_apply, RelativeMorphism.restrict_base]
    show yonedaEquiv (η ≫ relativeHomBase v) = _
    rw [yonedaEquiv_comp]
  refine RelativeMorphism.ext_of_eval hbase fun W γ s hp hq => ?_
  have hγ : γ = yoneda.map (yonedaEquiv γ) := (yoneda_map_yonedaEquiv γ).symm
  have hp' : yoneda.map (yonedaEquiv γ) ≫
      (RelativeMorphism.restrict η (relativeMorphismOfHom v)).base = s ≫ z := by
    rwa [← hγ]
  have hq' : yoneda.map (yonedaEquiv γ) ≫
      (relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v))).base =
      s ≫ z := by rwa [← hγ]
  rw [RelativeMorphism.eval_congr _ hγ (rfl : s = s) hp hp',
    RelativeMorphism.eval_congr _ hγ (rfl : s = s) hq hq']
  have hcomp : (yoneda.map (yonedaEquiv γ) ≫ η) ≫ (relativeMorphismOfHom v).base = s ≫ z := by
    rw [RelativeMorphism.restrict_base, ← Category.assoc] at hp'
    exact hp'
  rw [RelativeMorphism.eval_restrict _ η _ _ hp' hcomp]
  have hcomp' : (yoneda.map (yonedaEquiv γ) ≫ η) ≫
      relativeHomBase v = s ≫ z := hcomp
  set δ := pullback.lift (yoneda.map (yonedaEquiv γ) ≫ η) s hcomp' with hδ
  have hδfst : δ ≫ pullback.fst (relativeHomBase v) z =
      yoneda.map (yonedaEquiv γ) ≫ η := pullback.lift_fst _ _ _
  have hδsnd : δ ≫ pullback.snd (relativeHomBase v) z = s :=
    pullback.lift_snd _ _ _
  have hwfst : (pullback.fst (relativeHomBase v) z).app (op W)
      (yonedaEquiv δ) = T.map (yonedaEquiv γ).op (yonedaEquiv η) := by
    rw [← yonedaEquiv_comp, hδfst, ← yonedaEquiv_naturality]
  have hwsnd : (pullback.snd (relativeHomBase v) z).app (op W)
      (yonedaEquiv δ) = yonedaEquiv s := by
    rw [← yonedaEquiv_comp, hδsnd]
  have hsec : relativeHomSections B S hS Z X Q z x hZ hX hQ W
      (v.app (op W)
        ((pullback.fst (relativeHomBase v) z).app (op W)
          (yonedaEquiv δ))) =
      RelativeMorphism.restrict (yoneda.map (yonedaEquiv γ))
        (relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v))) := by
    rw [hwfst, NatTrans.naturality_apply v (yonedaEquiv γ).op (yonedaEquiv η), ← hvt]
    exact relativeHomSections_map B S hS Z X Q z x hZ hX hQ (yonedaEquiv γ)
      (yonedaEquiv (η ≫ v))
  have hsm : yonedaEquiv.symm
      ((pullback.snd (relativeHomBase v) z).app (op W)
        (yonedaEquiv δ)) = s := by
    rw [hwsnd, Equiv.symm_apply_apply]
  have hr' : (RelativeMorphism.restrict (yoneda.map (yonedaEquiv γ))
      (relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v)))).base =
      s ≫ z := by rwa [RelativeMorphism.restrict_base]
  have hid : 𝟙 (yoneda.obj W) ≫ (RelativeMorphism.restrict (yoneda.map (yonedaEquiv γ))
      (relativeHomSections B S hS Z X Q z x hZ hX hQ V (yonedaEquiv (η ≫ v)))).base =
      s ≫ z := by rwa [Category.id_comp]
  refine (yonedaEquiv (X := W) (F := X)).injective ?_
  calc yonedaEquiv ((relativeMorphismOfHom v).eval (yoneda.map (yonedaEquiv γ) ≫ η) s hcomp)
      = relativeHomMorphismApp v W (yonedaEquiv δ) := by
        rw [RelativeMorphism.eval, yonedaEquiv_comp]
        rfl
    _ = (RelativeMorphism.restrict (yoneda.map (yonedaEquiv γ))
          (relativeHomSections B S hS Z X Q z x hZ hX hQ V
            (yonedaEquiv (η ≫ v)))).evalPt s hr' :=
          relativeHomMorphismApp_eq v W (yonedaEquiv δ) _ s hsec hsm hr'
    _ = yonedaEquiv ((RelativeMorphism.restrict (yoneda.map (yonedaEquiv γ))
          (relativeHomSections B S hS Z X Q z x hZ hX hQ V
            (yonedaEquiv (η ≫ v)))).eval (𝟙 (yoneda.obj W)) s hid) := rfl
    _ = yonedaEquiv ((relativeHomSections B S hS Z X Q z x hZ hX hQ V
          (yonedaEquiv (η ≫ v))).eval (yoneda.map (yonedaEquiv γ)) s hq') := by
        rw [RelativeMorphism.eval_restrict_id _ (yoneda.map (yonedaEquiv γ)) s hq' hid]

/-! ### The bijection -/

variable (B S hS Z X Q z x hZ hX hQ) in
/-- **Stacks 05Y3**, part (2). For a test object `T` — in the source an algebraic space over
`S` — the morphisms `T ⟶ Mor_Q(Z, X)` are canonically the pairs `(a, b)` of Stacks 05Y1 at `T`:
a morphism `a : T ⟶ Q` together with a morphism `b : T ×_{a, Q} Z ⟶ X` over `Q`.

The bijection extends the identification of the sections over a scheme with pairs
(`AlgebraicGeometry.Space.relativeHomEquiv_yoneda`) and is natural in `T`
(`AlgebraicGeometry.Space.relativeHomEquiv_naturality`); the algebraicity of `T` is recorded
because the source states the bijection for algebraic spaces, but it is not used. -/
@[stacks 05Y3 "part (2): the canonical bijection between the morphisms from an algebraic space \
`T` into `Mor_B(Z, X)` and the pairs `(a, b)` of Stacks 05Y1 at `T`"]
noncomputable def relativeHomEquiv (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hT : IsAlgebraicSpace B S hS T) :
    (T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) ≃ RelativeMorphism B S hS Z X Q z x T where
  toFun v := relativeMorphismOfHom v
  invFun p := homOfRelativeMorphism p
  left_inv v := by
    refine NatTrans.ext (funext fun V => ?_)
    obtain ⟨V⟩ := V
    ext t
    change (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
        (RelativeMorphism.restrict (yonedaEquiv.symm t) (relativeMorphismOfHom v)) =
      v.app (op V) t
    rw [relativeMorphismOfHom_restrict, Equiv.symm_apply_apply, yonedaEquiv_comp,
      Equiv.apply_symm_apply]
  right_inv p := by
    refine RelativeMorphism.ext_of_restrict fun V η => ?_
    rw [relativeMorphismOfHom_restrict]
    have hη : yonedaEquiv (η ≫ homOfRelativeMorphism (hZ := hZ) (hX := hX) (hQ := hQ) p) =
        (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
          (RelativeMorphism.restrict η p) := by
      rw [yonedaEquiv_comp]
      change (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
        (RelativeMorphism.restrict (yonedaEquiv.symm (yonedaEquiv η)) p) = _
      rw [Equiv.symm_apply_apply]
    rw [hη, Equiv.apply_symm_apply]

/-- The bijection of Stacks 05Y3, part (2), extends the identification of the sections of the
relative morphism functor over a scheme with the pairs of Stacks 05Y1. -/
theorem relativeHomEquiv_yoneda (V : BigFppfOver B S hS)
    (hV : IsAlgebraicSpace B S hS (yoneda.obj V))
    (p : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op V)) :
    relativeHomEquiv B S hS Z X Q z x hZ hX hQ (yoneda.obj V) hV (yonedaEquiv.symm p) =
      relativeHomSections B S hS Z X Q z x hZ hX hQ V p := by
  have h := relativeMorphismOfHom_restrict (yonedaEquiv.symm p) V (𝟙 (yoneda.obj V))
  rw [RelativeMorphism.restrict_id, Category.id_comp, Equiv.apply_symm_apply] at h
  exact h

/-- The bijection of Stacks 05Y3, part (2), is natural in the test object: precomposing a
morphism into the relative morphism functor restricts the corresponding pair. -/
theorem relativeHomEquiv_naturality {T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hU : IsAlgebraicSpace B S hS U) (f : U ⟶ T)
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) :
    relativeHomEquiv B S hS Z X Q z x hZ hX hQ U hU (f ≫ v) =
      RelativeMorphism.restrict f
        (relativeHomEquiv B S hS Z X Q z x hZ hX hQ T hT v) := by
  refine RelativeMorphism.ext_of_restrict fun V η => ?_
  show RelativeMorphism.restrict η (relativeMorphismOfHom (f ≫ v)) =
    RelativeMorphism.restrict η (RelativeMorphism.restrict f (relativeMorphismOfHom v))
  rw [relativeMorphismOfHom_restrict, RelativeMorphism.restrict_comp,
    relativeMorphismOfHom_restrict, Category.assoc]

/-! ### The bijection for an arbitrary test presheaf -/

/-- A morphism into the relative morphism functor is recovered from its pair. This is one of
the two round trips inside `AlgebraicGeometry.Space.relativeHomEquiv`, stated for an arbitrary
test presheaf. -/
theorem homOfRelativeMorphism_relativeMorphismOfHom
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) :
    homOfRelativeMorphism (relativeMorphismOfHom v) = v := by
  refine NatTrans.ext (funext fun V => ?_)
  obtain ⟨V⟩ := V
  ext t
  show (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
      (RelativeMorphism.restrict (yonedaEquiv.symm t) (relativeMorphismOfHom v)) =
    v.app (op V) t
  rw [relativeMorphismOfHom_restrict, Equiv.symm_apply_apply, yonedaEquiv_comp,
    Equiv.apply_symm_apply]

/-- A pair is recovered from the morphism into the relative morphism functor it determines.
This is the other round trip inside `AlgebraicGeometry.Space.relativeHomEquiv`, stated for an
arbitrary test presheaf. -/
theorem relativeMorphismOfHom_homOfRelativeMorphism
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RelativeMorphism B S hS Z X Q z x T) :
    relativeMorphismOfHom (homOfRelativeMorphism (hZ := hZ) (hX := hX) (hQ := hQ) p) = p := by
  refine RelativeMorphism.ext_of_restrict fun V η => ?_
  rw [relativeMorphismOfHom_restrict]
  have hη : yonedaEquiv (η ≫ homOfRelativeMorphism (hZ := hZ) (hX := hX) (hQ := hQ) p) =
      (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
        (RelativeMorphism.restrict η p) := by
    rw [yonedaEquiv_comp]
    show (relativeHomSections B S hS Z X Q z x hZ hX hQ V).symm
      (RelativeMorphism.restrict (yonedaEquiv.symm (yonedaEquiv η)) p) = _
    rw [Equiv.symm_apply_apply]
  rw [hη, Equiv.apply_symm_apply]

/-- A morphism into the relative morphism functor is determined by its pair. -/
theorem relativeMorphismOfHom_injective {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {v₁ v₂ : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ}
    (h : relativeMorphismOfHom v₁ = relativeMorphismOfHom v₂) : v₁ = v₂ := by
  rw [← homOfRelativeMorphism_relativeMorphismOfHom v₁,
    ← homOfRelativeMorphism_relativeMorphismOfHom v₂, h]

variable (B S hS Z X Q z x hZ hX hQ) in
/-- **Stacks 05Y3**, part (2), for an arbitrary test presheaf: the morphisms `T ⟶ Mor_Q(Z, X)`
out of a presheaf `T` on the big fppf site of `S` are canonically the pairs `(a, b)` of
Stacks 05Y1 at `T`. The algebraicity of `T` that the source assumes is not used — see
`AlgebraicGeometry.Space.relativeHomEquiv_eq_relativeHomEquivPresheaf` — and dropping it is
what lets the bijection be applied at the presheaf of a covering sieve, which is how the sheaf
condition of part (1) is checked. -/
noncomputable def relativeHomEquivPresheaf (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) ≃ RelativeMorphism B S hS Z X Q z x T where
  toFun v := relativeMorphismOfHom v
  invFun p := homOfRelativeMorphism p
  left_inv v := homOfRelativeMorphism_relativeMorphismOfHom v
  right_inv p := relativeMorphismOfHom_homOfRelativeMorphism p

/-- The bijection of part (2) of Stacks 05Y3 at an algebraic space is the bijection at the
underlying presheaf. -/
theorem relativeHomEquiv_eq_relativeHomEquivPresheaf
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T) :
    relativeHomEquiv B S hS Z X Q z x hZ hX hQ T hT =
      relativeHomEquivPresheaf B S hS Z X Q z x hZ hX hQ T := rfl

/-- The bijection of part (2) of Stacks 05Y3 is natural in an arbitrary test presheaf:
precomposing a morphism into the relative morphism functor restricts the corresponding pair. -/
theorem relativeMorphismOfHom_comp {T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : U ⟶ T)
    (v : T ⟶ relativeHom B S hS Z X Q z x hZ hX hQ) :
    relativeMorphismOfHom (f ≫ v) =
      RelativeMorphism.restrict f (relativeMorphismOfHom v) := by
  refine RelativeMorphism.ext_of_restrict fun V η => ?_
  rw [relativeMorphismOfHom_restrict, RelativeMorphism.restrict_comp,
    relativeMorphismOfHom_restrict, Category.assoc]

end Equiv

/-! ### The sheaf condition -/

/-- **The base change of the inclusion of a sieve is injective on morphisms.** The fibre
product `R ×_{a, Q} Z` of the presheaf of a sieve `R` on `V` sits inside the fibre product
`V ×_{a, Q} Z` as the base change of `R ⊆ V` along the first projection, and a base change of
a monomorphism is a monomorphism. -/
theorem hom_ext_comp_mapFst_functorInclusion {V : BigFppfOver B S hS} (R : Sieve V)
    (a : yoneda.obj V ⟶ Q) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u₁ u₂ : W ⟶ pullback (R.functorInclusion ≫ a) z)
    (h : u₁ ≫ pullback.mapFst R.functorInclusion a z =
      u₂ ≫ pullback.mapFst R.functorInclusion a z) : u₁ = u₂ := by
  refine pullback.hom_ext ?_ ?_
  · refine (cancel_mono R.functorInclusion).mp ?_
    rw [Category.assoc, Category.assoc, ← pullback.mapFst_fst R.functorInclusion a z,
      ← Category.assoc, ← Category.assoc, h]
  · rw [← pullback.mapFst_snd R.functorInclusion a z, ← Category.assoc, ← Category.assoc, h]

/-- **The base change of the inclusion of a covering sieve is locally surjective.** A
scheme-valued point of `V ×_{a, Q} Z` lies in `R ×_{a, Q} Z` as soon as its first coordinate
lies in `R`, and that happens after restriction along the covering sieve obtained by pulling
`R` back along the first coordinate. -/
theorem exists_comp_mapFst_functorInclusion_eq {V : BigFppfOver B S hS} (R : Sieve V)
    (hR : R ∈ BigFppfOver.topology B S hS V) (a : yoneda.obj V ⟶ Q)
    (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ pullback a z) :
    ∃ R' : Sieve W, R' ∈ BigFppfOver.topology B S hS W ∧
      ∀ ⦃W' : BigFppfOver B S hS⦄ (g : W' ⟶ W), R' g →
        ∃ u : yoneda.obj W' ⟶ pullback (R.functorInclusion ≫ a) z,
          u ≫ pullback.mapFst R.functorInclusion a z = yoneda.map g ≫ p := by
  set k : W ⟶ V := yonedaEquiv (p ≫ pullback.fst a z) with hk
  have hkmap : yoneda.map k = p ≫ pullback.fst a z := yoneda_map_yonedaEquiv _
  refine ⟨R.pullback k, (BigFppfOver.topology B S hS).pullback_stable k hR, ?_⟩
  intro W' g hg
  have hgk : R (g ≫ k) := hg
  have hι : R.toFunctor (g ≫ k) hgk ≫ R.functorInclusion =
      yoneda.map g ≫ p ≫ pullback.fst a z := by
    rw [Sieve.toFunctor_comp_functorInclusion, Functor.map_comp, hkmap]
  have hcond : R.toFunctor (g ≫ k) hgk ≫ (R.functorInclusion ≫ a) =
      (yoneda.map g ≫ p ≫ pullback.snd a z) ≫ z := by
    rw [reassoc_of% hι]
    simp [pullback.condition]
  refine ⟨pullback.lift (R.toFunctor (g ≫ k) hgk) (yoneda.map g ≫ p ≫ pullback.snd a z)
    hcond, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.mapFst_fst, ← Category.assoc, pullback.lift_fst, hι,
      Category.assoc]
  · rw [Category.assoc, pullback.mapFst_snd, pullback.lift_snd, Category.assoc]

/-- **Maps into a sheaf descend along the base change of the inclusion of a covering sieve.**
This is `CategoryTheory.Presheaf.IsSheaf.existsUnique_comp_eq` applied to the two preceding
lemmas. -/
theorem existsUnique_comp_mapFst_functorInclusion_eq
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {V : BigFppfOver B S hS}
    (R : Sieve V) (hR : R ∈ BigFppfOver.topology B S hS V) (a : yoneda.obj V ⟶ Q)
    (c : pullback (R.functorInclusion ≫ a) z ⟶ G) :
    ∃! b : pullback a z ⟶ G, pullback.mapFst R.functorInclusion a z ≫ b = c :=
  hG.existsUnique_comp_eq (pullback.mapFst R.functorInclusion a z)
    (fun u₁ u₂ hu => hom_ext_comp_mapFst_functorInclusion R a u₁ u₂ hu)
    (exists_comp_mapFst_functorInclusion_eq R hR a) c

/-- Precomposing the evaluation of a pair at a point of a represented presheaf with a morphism
lying in a sieve is the evaluation of the restriction of the pair to the presheaf of the sieve. -/
private theorem comp_eval_restrict_functorInclusion {V W W' : BigFppfOver B S hS} {k : W ⟶ V}
    (R : Sieve V) (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) (r : W' ⟶ W)
    (hr : R (r ≫ k)) (s : yoneda.obj W ⟶ Z) (hp : yoneda.map k ≫ p.base = s ≫ z) :
    ∃ hres : R.toFunctor (r ≫ k) hr ≫ (RelativeMorphism.restrict R.functorInclusion p).base =
        (yoneda.map r ≫ s) ≫ z,
      yoneda.map r ≫ p.eval (yoneda.map k) s hp =
        (RelativeMorphism.restrict R.functorInclusion p).eval (R.toFunctor (r ≫ k) hr)
          (yoneda.map r ≫ s) hres := by
  have hδ : yoneda.map r ≫ yoneda.map k = R.toFunctor (r ≫ k) hr ≫ R.functorInclusion := by
    rw [Sieve.toFunctor_comp_functorInclusion, Functor.map_comp]
  have hrs : (yoneda.map r ≫ yoneda.map k) ≫ p.base = (yoneda.map r ≫ s) ≫ z := by
    rw [Category.assoc, hp, ← Category.assoc]
  have hδι : (R.toFunctor (r ≫ k) hr ≫ R.functorInclusion) ≫ p.base = (yoneda.map r ≫ s) ≫ z := by
    rwa [← hδ]
  have hres : R.toFunctor (r ≫ k) hr ≫ (RelativeMorphism.restrict R.functorInclusion p).base =
      (yoneda.map r ≫ s) ≫ z := by
    rwa [RelativeMorphism.restrict_base, ← Category.assoc]
  exact ⟨hres, (RelativeMorphism.comp_eval p _ _ s hp hrs).trans
    ((RelativeMorphism.eval_congr p hδ rfl hrs hδι).trans
      (RelativeMorphism.eval_restrict p R.functorInclusion _ _ hres hδι).symm)⟩

/-- **A pair over a represented presheaf is determined by its restriction along the inclusion
of a covering sieve.** The first components agree because `Q` is a sheaf, and the evaluations
of the two pairs at a scheme-valued point agree locally on that point — on the covering sieve
obtained by pulling the given one back along it — hence agree because `X` is a sheaf. -/
theorem RelativeMorphism.ext_of_restrict_functorInclusion
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hQ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) {V : BigFppfOver B S hS}
    (R : Sieve V) (hR : R ∈ BigFppfOver.topology B S hS V)
    {p₁ p₂ : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)}
    (h : RelativeMorphism.restrict R.functorInclusion p₁ =
      RelativeMorphism.restrict R.functorInclusion p₂) : p₁ = p₂ := by
  have hX'' : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ X).mp hX'
  have hQ'' : Presieve.IsSheaf (BigFppfOver.topology B S hS) Q :=
    (isSheaf_iff_isSheaf_of_type _ Q).mp hQ'
  have hbase : p₁.base = p₂.base := by
    refine (hQ'' R hR).hom_ext _ _ ?_
    have hb := congrArg RelativeMorphism.base h
    rwa [RelativeMorphism.restrict_base, RelativeMorphism.restrict_base] at hb
  refine RelativeMorphism.ext_of_eval hbase ?_
  intro W γ s hp₁ hp₂
  obtain ⟨k, rfl⟩ : ∃ k, γ = yoneda.map k := ⟨_, (yoneda_map_yonedaEquiv γ).symm⟩
  refine yonedaEquiv.injective ?_
  refine (hX'' (R.pullback k)
    ((BigFppfOver.topology B S hS).pullback_stable k hR)).isSeparatedFor.ext ?_
  intro W' r hr
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  obtain ⟨h₁, e₁⟩ := comp_eval_restrict_functorInclusion R p₁ r hr s hp₁
  obtain ⟨h₂, e₂⟩ := comp_eval_restrict_functorInclusion R p₂ r hr s hp₂
  rw [e₁, e₂]
  exact RelativeMorphism.eval_eq_of_eq h _ _ h₁ h₂

/-- **A pair over the presheaf of a covering sieve extends uniquely to a pair over the
represented presheaf.** The first component extends because `Q` is a sheaf; the second extends
because `X` is a sheaf and the fibre product over the sieve is the base change of the fibre
product over `V`. This is the sheaf condition of Stacks 05Y3, part (1), read through the pairs
of Stacks 05Y1. -/
theorem existsUnique_restrict_functorInclusion_eq
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hQ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) {V : BigFppfOver B S hS}
    (R : Sieve V) (hR : R ∈ BigFppfOver.topology B S hS V)
    (q : RelativeMorphism B S hS Z X Q z x R.functor) :
    ∃! p : RelativeMorphism B S hS Z X Q z x (yoneda.obj V),
      RelativeMorphism.restrict R.functorInclusion p = q := by
  have hQ'' : Presieve.IsSheaf (BigFppfOver.topology B S hS) Q :=
    (isSheaf_iff_isSheaf_of_type _ Q).mp hQ'
  obtain ⟨a, ha, -⟩ :=
    Presieve.isSheafFor_iff_yonedaSheafCondition.mp (hQ'' R hR) q.base
  have hc : pullback.fst (R.functorInclusion ≫ a) z ≫ q.base =
      pullback.snd (R.functorInclusion ≫ a) z ≫ z := by
    rw [← ha]; exact pullback.condition
  obtain ⟨b, hb, -⟩ := existsUnique_comp_mapFst_functorInclusion_eq hX' R hR a
    (q.eval (pullback.fst (R.functorInclusion ≫ a) z)
      (pullback.snd (R.functorInclusion ≫ a) z) hc)
  have hcommutes : b ≫ x = pullback.snd a z ≫ z := by
    obtain ⟨w, -, hu⟩ := existsUnique_comp_mapFst_functorInclusion_eq hQ' R hR a
      (pullback.snd (R.functorInclusion ≫ a) z ≫ z)
    refine (hu (b ≫ x) ?_).trans (hu (pullback.snd a z ≫ z) ?_).symm
    · show pullback.mapFst R.functorInclusion a z ≫ b ≫ x =
        pullback.snd (R.functorInclusion ≫ a) z ≫ z
      rw [← Category.assoc, hb, RelativeMorphism.eval_comp]
    · show pullback.mapFst R.functorInclusion a z ≫ pullback.snd a z ≫ z =
        pullback.snd (R.functorInclusion ≫ a) z ≫ z
      rw [← Category.assoc, pullback.mapFst_snd]
  have hp : RelativeMorphism.restrict R.functorInclusion
      (⟨a, b, hcommutes⟩ : RelativeMorphism B S hS Z X Q z x (yoneda.obj V)) = q := by
    refine RelativeMorphism.ext_of_eval ha ?_
    intro W γ s hp₀ hq₀
    have h0 : γ ≫ (R.functorInclusion ≫ a) = s ≫ z := hp₀
    have hp₀' : (γ ≫ R.functorInclusion) ≫ a = s ≫ z := by rwa [Category.assoc]
    have h2 : (pullback.lift γ s h0 ≫ pullback.fst (R.functorInclusion ≫ a) z) ≫ q.base =
        (pullback.lift γ s h0 ≫ pullback.snd (R.functorInclusion ≫ a) z) ≫ z := by
      simp only [Category.assoc, hc]
    calc (RelativeMorphism.restrict R.functorInclusion
            (⟨a, b, hcommutes⟩ : RelativeMorphism B S hS Z X Q z x (yoneda.obj V))).eval
            γ s hp₀
        = pullback.lift (γ ≫ R.functorInclusion) s hp₀' ≫ b :=
          RelativeMorphism.eval_restrict _ R.functorInclusion γ s hp₀ hp₀'
      _ = (pullback.lift γ s h0 ≫ pullback.mapFst R.functorInclusion a z) ≫ b := by
          rw [pullback.lift_comp_mapFst R.functorInclusion a z γ s h0 hp₀']
      _ = pullback.lift γ s h0 ≫ q.eval (pullback.fst (R.functorInclusion ≫ a) z)
            (pullback.snd (R.functorInclusion ≫ a) z) hc := by rw [Category.assoc, hb]
      _ = q.eval (pullback.lift γ s h0 ≫ pullback.fst (R.functorInclusion ≫ a) z)
            (pullback.lift γ s h0 ≫ pullback.snd (R.functorInclusion ≫ a) z) h2 :=
          RelativeMorphism.comp_eval q (pullback.lift γ s h0) _ _ hc h2
      _ = q.eval γ s hq₀ :=
          RelativeMorphism.eval_congr q (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
            h2 hq₀
  exact ⟨_, hp, fun p' hp' => RelativeMorphism.ext_of_restrict_functorInclusion hX' hQ' R hR
    (hp'.trans hp.symm)⟩


end AlgebraicGeometry.Space

end
