module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.ChartAction
public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.QuasiAffineAction

/-!
# The isomorphism of fibre products defined by the action on the chart

In the situation of `StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.ChartAction`, let
`Y = U × P` with `g' : T ⟶ Y` the product of `f` with the identity of `P`. Two arrows into `T`
agree after `g'` exactly when they agree over `U` and over `P`, so the action of the chart moves a
point `q` of `Q` along any `t` with `q ≫ π ≫ g' = t ≫ g'`. This file builds from the action the
isomorphism `Q ×_Y T ≅ T ×_Y Q` of fibre products of the site, over `T ×_Y T`.

## Main definitions

* `AlgebraicGeometry.Stack.ChartAction.actY`: the action, indexed by agreement after `g'`.
* `AlgebraicGeometry.Stack.ChartAction.chartIso`: the isomorphism of fibre products.

## Main results

* `AlgebraicGeometry.Stack.ChartAction.exists_descended_chart`: for `g'` an fpqc covering and `π`
  quasi-affine, `Q` descends along `g'` to a scheme over `Y`, with projection invariant under the
  action.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack.ChartAction

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  [𝒳.val.p.IsFibered] {U W P T Y : BigFppfOver B S hS} {R : Sieve U}
  (D : SieveDescentDatum 𝒳.val.p R) {f : W ⟶ U} (hf : R.arrows f)
  {g : Over P ⥤ 𝒳.val.obj} (hg : g ⋙ 𝒳.val.p = Over.forget P) (pr₁ : T ⟶ W) (pr₂ : T ⟶ P)
  {q₁ : Y ⟶ U} {q₂ : Y ⟶ P} {g' : T ⟶ Y}
  (hg₁ : g' ≫ q₁ = pr₁ ≫ f) (hg₂ : g' ≫ q₂ = pr₂)
  {Q : BigFppfOver B S hS} {π : Q ⟶ T}
  (e : yoneda.obj Q ≅ chartPresheaf 𝒳 D hf hg pr₁ pr₂)
  (he : e.hom ≫ OverShriek.presheafToYoneda _ = yoneda.map π)

include hg₁ hg₂ in
/-- Two arrows into `T` that agree after `g'` agree after `pr₁ ≫ f` and after `pr₂`. -/
lemma comp_g'_eq_imp {Z : BigFppfOver B S hS} (a b : Z ⟶ T) (h : a ≫ g' = b ≫ g') :
    a ≫ pr₁ ≫ f = b ≫ pr₁ ≫ f ∧ a ≫ pr₂ = b ≫ pr₂ :=
  ⟨by rw [← hg₁, ← Category.assoc, h, Category.assoc],
    by rw [← hg₂, ← Category.assoc, h, Category.assoc]⟩

/-- The action on the chart, indexed by agreement after `g'`. -/
noncomputable def actY {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t : Z ⟶ T)
    (h : q ≫ π ≫ g' = t ≫ g') : Z ⟶ Q :=
  act 𝒳 D hf hg pr₁ pr₂ e he q t
    ((Category.assoc _ _ _).symm.trans
      (comp_g'_eq_imp pr₁ pr₂ hg₁ hg₂ _ _ ((Category.assoc _ _ _).trans h)).1)
    ((Category.assoc _ _ _).symm.trans
      (comp_g'_eq_imp pr₁ pr₂ hg₁ hg₂ _ _ ((Category.assoc _ _ _).trans h)).2)

/-- The action `actY q t` lies over `t`: its composite with `π` is `t`. -/
lemma actY_comp_π {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t : Z ⟶ T)
    (h : q ≫ π ≫ g' = t ≫ g') : actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t h ≫ π = t :=
  act_comp_π 𝒳 D hf hg pr₁ pr₂ e he q t _ _

/-- Acting by `t` and then by `t'` is acting by `t'`. -/
lemma actY_actY {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (t t' : Z ⟶ T)
    (h : q ≫ π ≫ g' = t ≫ g') (h' : actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t h ≫ π ≫ g' =
      t' ≫ g') (h'' : q ≫ π ≫ g' = t' ≫ g') :
    actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t h) t' h' =
      actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t' h'' :=
  act_act 𝒳 D hf hg pr₁ pr₂ e he q t t' _ _ _ _ _ _

/-- Acting on `q` by `q ≫ π` returns `q`. -/
lemma actY_self {Z : BigFppfOver B S hS} (q : Z ⟶ Q) (h : q ≫ π ≫ g' = (q ≫ π) ≫ g') :
    actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q (q ≫ π) h = q :=
  act_self 𝒳 D hf hg pr₁ pr₂ e he q _ _

/-- The action commutes with precomposition: `k ≫ actY q t = actY (k ≫ q) (k ≫ t)`. -/
lemma comp_actY {Z Z' : BigFppfOver B S hS} (k : Z' ⟶ Z) (q : Z ⟶ Q) (t : Z ⟶ T)
    (h : q ≫ π ≫ g' = t ≫ g') (h' : (k ≫ q) ≫ π ≫ g' = (k ≫ t) ≫ g') :
    k ≫ actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t h =
      actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (k ≫ q) (k ≫ t) h' :=
  comp_act 𝒳 D hf hg pr₁ pr₂ e he k q t _ _ _ _

/-- Acting on equal points `q = q'` by equal arrows `t = t'` gives equal results. -/
lemma actY_congr {Z : BigFppfOver B S hS} {q q' : Z ⟶ Q} {t t' : Z ⟶ T} (hq : q = q')
    (ht : t = t') (h : q ≫ π ≫ g' = t ≫ g') (h' : q' ≫ π ≫ g' = t' ≫ g') :
    actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q t h =
      actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he q' t' h' := by
  subst hq ht
  rfl

/-- The morphism `Q ×_Y T ⟶ T ×_Y Q` of the action: `(q, t) ↦ (q ≫ π, q · t)`. -/
noncomputable def chartIsoHom : pullback (π ≫ g') g' ⟶ pullback g' (π ≫ g') :=
  pullback.lift (pullback.fst _ _ ≫ π)
    (actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc _ π g', actY_comp_π])

/-- The morphism `T ×_Y Q ⟶ Q ×_Y T` of the action: `(t, q) ↦ (q · t, q ≫ π)`. -/
noncomputable def chartIsoInv : pullback g' (π ≫ g') ⟶ pullback (π ≫ g') g' :=
  pullback.lift
    (actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (pullback.snd _ _) (pullback.fst _ _)
      pullback.condition.symm)
    (pullback.snd _ _ ≫ π)
    (by rw [← Category.assoc _ π g', actY_comp_π, pullback.condition, Category.assoc])

/-- **The isomorphism of fibre products defined by the action on the chart.** -/
noncomputable def chartIso : pullback (π ≫ g') g' ≅ pullback g' (π ≫ g') where
  hom := chartIsoHom 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he
  inv := chartIsoInv 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, chartIsoInv, pullback.lift_fst, Category.id_comp,
        comp_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _
          (by rw [Category.assoc, Category.assoc, ← pullback.condition])]
      simp only [chartIsoHom, pullback.lift_fst, pullback.lift_snd]
      rw [actY_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _ _ (by rw [← Category.assoc])]
      exact actY_self 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _
    · rw [Category.assoc, chartIsoInv, pullback.lift_snd, Category.id_comp, chartIsoHom,
        ← Category.assoc, pullback.lift_snd, actY_comp_π]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, chartIsoHom, pullback.lift_fst, Category.id_comp, chartIsoInv,
        ← Category.assoc, pullback.lift_fst, actY_comp_π]
    · rw [Category.assoc, chartIsoHom, pullback.lift_snd, Category.id_comp,
        comp_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _
          (by rw [Category.assoc, Category.assoc, pullback.condition])]
      simp only [chartIsoInv, pullback.lift_fst, pullback.lift_snd]
      rw [actY_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _ _ rfl]
      exact actY_self 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _

/-- The second component of `chartIsoHom` at the point `(a, b)` of `Q ×_Y T` is the action
`actY a b`. -/
lemma lift_chartIsoHom_snd {Z : BigFppfOver B S hS} (a : Z ⟶ Q) (b : Z ⟶ T)
    (h : a ≫ π ≫ g' = b ≫ g') :
    pullback.lift a b h ≫ chartIsoHom 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he ≫ pullback.snd _ _ =
      actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he a b h := by
  rw [chartIsoHom, pullback.lift_snd, comp_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _
    (by rw [Category.assoc, Category.assoc, pullback.condition])]
  exact actY_congr 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) _ _

/-- **The descent of the chart.** Pushed to schemes, the isomorphism of fibre products of the
action is a descent datum on the quasi-affine `π` relative to the fpqc covering `g'`, and it is
effective: there are a scheme `W₀` over `Y`, a Cartesian square exhibiting `Q` as `T ×_Y W₀`, and
the invariance of the projection `Q ⟶ W₀` under the action, read on points of the site. -/
theorem exists_descended_chart
    [Surjective ((BigFppfOver.toScheme B S hS).map g')]
    [Flat ((BigFppfOver.toScheme B S hS).map g')]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map g')]
    (hπ : _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map π)) :
    ∃ (W₀ : Scheme.{u}) (i : W₀ ⟶ (BigFppfOver.toScheme B S hS).obj Y)
      (k : (BigFppfOver.toScheme B S hS).obj Q ⟶ W₀),
      IsPullback ((BigFppfOver.toScheme B S hS).map π) k
        ((BigFppfOver.toScheme B S hS).map g') i ∧
      ∀ ⦃Z : BigFppfOver B S hS⦄ (z₁ z₂ : Z ⟶ Q) (h : z₁ ≫ π ≫ g' = (z₂ ≫ π) ≫ g'),
        actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he z₁ (z₂ ≫ π) h = z₂ →
          (BigFppfOver.toScheme B S hS).map z₁ ≫ k = (BigFppfOver.toScheme B S hS).map z₂ ≫ k := by
  set F := BigFppfOver.toScheme B S hS with hF
  set θ := chartIso 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he with hθ
  have sq1 : IsPullback (F.map (pullback.fst (π ≫ g') g')) (F.map (pullback.snd (π ≫ g') g'))
      (F.map π ≫ F.map g') (F.map g') := by
    have := (IsPullback.of_hasPullback (π ≫ g') g').map F
    rwa [F.map_comp] at this
  have sq2 : IsPullback (F.map (pullback.fst g' (π ≫ g'))) (F.map (pullback.snd g' (π ≫ g')))
      (F.map g') (F.map π ≫ F.map g') := by
    have := (IsPullback.of_hasPullback g' (π ≫ g')).map F
    rwa [F.map_comp] at this
  have hφ1 : (F.mapIso θ).hom ≫ F.map (pullback.fst g' (π ≫ g')) =
      F.map (pullback.fst (π ≫ g') g') ≫ F.map π := by
    simp only [Functor.mapIso_hom, ← F.map_comp, hθ, chartIso, chartIsoHom, pullback.lift_fst]
  have hφ2 : ((F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g'))) ≫ F.map π =
      F.map (pullback.snd (π ≫ g') g') := by
    simp only [Functor.mapIso_hom, ← F.map_comp, hθ, chartIso, chartIsoHom, pullback.lift_snd,
      actY_comp_π]
  have hθs : ∀ {Z : BigFppfOver B S hS} (a : Z ⟶ Q) (b : Z ⟶ T) (h : a ≫ π ≫ g' = b ≫ g'),
      F.map (pullback.lift a b h) ≫ (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g')) =
        F.map (actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he a b h) := by
    intro Z a b h
    simp only [Functor.mapIso_hom, ← F.map_comp, hθ, chartIso]
    rw [lift_chartIsoHom_snd]
  have hsq1lift : ∀ {Z : Scheme.{u}} {Z' : BigFppfOver B S hS} (u : Z ⟶ F.obj Z') (a : Z' ⟶ Q)
      (b : Z' ⟶ T) (h : a ≫ π ≫ g' = b ≫ g') (x : Z ⟶ F.obj Q) (y : Z ⟶ F.obj T)
      (h' : x ≫ F.map π ≫ F.map g' = y ≫ F.map g'), x = u ≫ F.map a → y = u ≫ F.map b →
      sq1.lift x y h' = u ≫ F.map (pullback.lift a b h) := by
    intro Z Z' u a b h x y h' hx hy
    subst hx hy
    refine sq1.hom_ext ?_ ?_
    · rw [sq1.lift_fst, Category.assoc, ← F.map_comp, pullback.lift_fst]
    · rw [sq1.lift_snd, Category.assoc, ← F.map_comp, pullback.lift_snd]
  have hassoc : ∀ ⦃Z : Scheme.{u}⦄ (ξ : Z ⟶ F.obj (pullback (π ≫ g') g'))
      (y : Z ⟶ F.obj T)
      (h₁ : (ξ ≫ (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g'))) ≫ F.map π ≫ F.map g' =
        y ≫ F.map g')
      (h₂ : (ξ ≫ F.map (pullback.fst (π ≫ g') g')) ≫ F.map π ≫ F.map g' = y ≫ F.map g'),
      sq1.lift (ξ ≫ (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g'))) y h₁ ≫
          (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g')) =
        sq1.lift (ξ ≫ F.map (pullback.fst (π ≫ g') g')) y h₂ ≫
          (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g')) := by
    intro Z ξ y h₁ h₂
    have hM := (IsPullback.of_hasPullback (pullback.fst (π ≫ g') g' ≫ π ≫ g') g').map F
    have hu : ξ ≫ F.map (pullback.fst (π ≫ g') g' ≫ π ≫ g') = y ≫ F.map g' := by
      simpa only [F.map_comp, Category.assoc] using h₂
    set m₁ := pullback.fst (pullback.fst (π ≫ g') g' ≫ π ≫ g') g'
    set m₂ := pullback.snd (pullback.fst (π ≫ g') g' ≫ π ≫ g') g'
    set u := hM.lift ξ y hu
    have hξ : ξ = u ≫ F.map m₁ := (hM.lift_fst _ _ _).symm
    have hy : y = u ≫ F.map m₂ := (hM.lift_snd _ _ _).symm
    have hc₁ : (m₁ ≫ pullback.fst _ _) ≫ π ≫ g' = m₂ ≫ g' := by
      rw [Category.assoc]; exact pullback.condition
    have hcm : (m₁ ≫ pullback.fst (π ≫ g') g') ≫ π ≫ g' = (m₁ ≫ pullback.snd (π ≫ g') g') ≫ g' := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (m₁ ≫ ·) pullback.condition
    set a₀ := actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he (m₁ ≫ pullback.fst _ _)
      (m₁ ≫ pullback.snd _ _) hcm with ha₀def
    have hm₁ : pullback.lift (m₁ ≫ pullback.fst _ _) (m₁ ≫ pullback.snd _ _) hcm = m₁ :=
      pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    have ha₀ : m₁ ≫ θ.hom ≫ pullback.snd _ _ = a₀ :=
      (congrArg (· ≫ θ.hom ≫ pullback.snd _ _) hm₁).symm.trans
        (lift_chartIsoHom_snd 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ hcm)
    have hc₀ : a₀ ≫ π ≫ g' = m₂ ≫ g' :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g')
        (actY_comp_π 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ hcm)).trans (hcm.symm.trans hc₁))
    have hL := hsq1lift u a₀ m₂ hc₀ (ξ ≫ (F.mapIso θ).hom ≫ F.map (pullback.snd g' (π ≫ g')))
      y h₁ (by rw [hξ, ← ha₀, Category.assoc]; simp only [Functor.mapIso_hom, F.map_comp]) hy
    have hR := hsq1lift u (m₁ ≫ pullback.fst _ _) m₂ hc₁ (ξ ≫ F.map (pullback.fst (π ≫ g') g'))
      y h₂ (by rw [hξ, F.map_comp, Category.assoc]) hy
    rw [hL, hR, Category.assoc, Category.assoc, hθs, hθs]
    exact congrArg (u ≫ F.map ·) (actY_actY 𝒳 D hf hg pr₁ pr₂ hg₁ hg₂ e he _ _ _ _ _ _)
  obtain ⟨W₀, i, k, hpb, hinv⟩ := exists_descended_of_actionAssoc_of_isQuasiAffineHom
    (F.mapIso θ) sq1 sq2 hφ1 hφ2 hassoc hπ
  refine ⟨W₀, i, k, hpb, fun Z z₁ z₂ h hz => ?_⟩
  have h' : F.map z₁ ≫ F.map π ≫ F.map g' = (F.map z₂ ≫ F.map π) ≫ F.map g' := by
    simpa only [F.map_comp, Category.assoc] using congrArg F.map h
  refine hinv (F.map z₁) (F.map z₂) h' ?_
  rw [hsq1lift (𝟙 _) z₁ (z₂ ≫ π) h _ _ h' (Category.id_comp _).symm
    (by rw [Category.id_comp, F.map_comp]), Category.id_comp, hθs, hz]

end AlgebraicGeometry.Stack.ChartAction

end
