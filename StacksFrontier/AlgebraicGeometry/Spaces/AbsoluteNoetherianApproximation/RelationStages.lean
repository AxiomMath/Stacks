module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Points of the glued relations along the inverse system

In the proof of Stacks 07SU each relation `R_j` is glued from the chart `V_j` and the chart
`P_j = W_j ×_{U_j} W_j` along `W_j`, and the square formed by the transition morphism
`R_k ⟶ R_j` and the source maps is cartesian (Stacks 07SV). This file records the consequence
used when the limit of the system is identified with the given space: a point of `R_j` lying
in one of the two charts is the image of a point of `R_k` lying in the corresponding chart, for
every later `k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] {J : Type*} [Category* J] {Vs Ws P R : J ⥤ C} {ι : Ws ⟶ Vs}
  {p₁ : P ⟶ Ws} {a : Vs ⟶ R} {b : P ⟶ R} {s : R ⟶ Vs}

/-- Naturality of the source map applied to a point `r_k` of `R_k` mapping to `r_j`. -/
private theorem comp_s_comp_map_eq {k j : J} (e : k ⟶ j) {T : C} {rk : T ⟶ R.obj k}
    {rj : T ⟶ R.obj j} (hk : rk ≫ R.map e = rj) : (rk ≫ s.app k) ≫ Vs.map e = rj ≫ s.app j := by
  rw [Category.assoc, ← s.naturality e, ← Category.assoc, hk]

/-- **A point in the chart `V_j` of the glued relation comes from the chart `V_k`.** If the
transition square of the glued relations over the source maps is cartesian and a point `r_j` of
`R_j` lies in the chart `V_j`, then any point `r_k` of `R_k` mapping to it lies in the chart
`V_k`, over its own source. -/
theorem eq_comp_a_of_eq_comp_a {k j : J} (e : k ⟶ j)
    (hcart : IsPullback (R.map e) (s.app k) (s.app j) (Vs.map e))
    (has : ∀ i, a.app i ≫ s.app i = 𝟙 _) {T : C} {rk : T ⟶ R.obj k}
    {rj : T ⟶ R.obj j} (hk : rk ≫ R.map e = rj) {c : T ⟶ Vs.obj j} (hc : rj = c ≫ a.app j) :
    rk = (rk ≫ s.app k) ≫ a.app k := by
  have h1 : (rk ≫ s.app k) ≫ Vs.map e = c := by
    rw [comp_s_comp_map_eq e hk, hc, Category.assoc, has, Category.comp_id]
  refine hcart.hom_ext ?_ ?_
  · rw [hk, hc, Category.assoc, ← a.naturality e, ← Category.assoc, h1]
  · rw [Category.assoc, has, Category.comp_id]

/-- **A point in the chart `P_j` of the glued relation comes from the chart `P_k`.** If, in
addition, `W_k` is the inverse image of `W_j` in `V_k` and `P_k` is the inverse image of `P_j`
along `W_k ⟶ W_j`, then any point of `R_k` mapping to a point of `R_j` in the chart `P_j` lies in
the chart `P_k`. -/
theorem exists_eq_comp_b_of_eq_comp_b {k j : J} (e : k ⟶ j)
    (hcart : IsPullback (R.map e) (s.app k) (s.app j) (Vs.map e))
    (hιcart : IsPullback (Ws.map e) (ι.app k) (ι.app j) (Vs.map e))
    (hPcart : IsPullback (P.map e) (p₁.app k) (p₁.app j) (Ws.map e))
    (hbs : ∀ i, b.app i ≫ s.app i = p₁.app i ≫ ι.app i) {T : C} {rk : T ⟶ R.obj k}
    {rj : T ⟶ R.obj j} (hk : rk ≫ R.map e = rj) {q : T ⟶ P.obj j} (hq : rj = q ≫ b.app j) :
    ∃ q' : T ⟶ P.obj k, rk = q' ≫ b.app k := by
  have hw : (rk ≫ s.app k) ≫ Vs.map e = (q ≫ p₁.app j) ≫ ι.app j := by
    rw [comp_s_comp_map_eq e hk, hq, Category.assoc, hbs, Category.assoc]
  have hw₁ := hιcart.lift_fst _ _ hw.symm
  have hw₂ := hιcart.lift_snd _ _ hw.symm
  have hq'₁ := hPcart.lift_fst q _ hw₁.symm
  have hq'₂ := hPcart.lift_snd q _ hw₁.symm
  refine ⟨hPcart.lift q _ hw₁.symm, hcart.hom_ext ?_ ?_⟩
  · rw [hk, hq, Category.assoc, ← b.naturality e, ← Category.assoc, hq'₁]
  · rw [Category.assoc, hbs, ← Category.assoc, hq'₂, hw₂]

/-- In the situation of `CategoryTheory.eq_comp_a_of_eq_comp_a`, the point `r_k` has equal
target and source as soon as the chart `V_k` is a section of both. -/
theorem comp_t_eq_comp_s_of_eq_comp_a {t : R ⟶ Vs} {k j : J} (e : k ⟶ j)
    (hcart : IsPullback (R.map e) (s.app k) (s.app j) (Vs.map e))
    (has : ∀ i, a.app i ≫ s.app i = 𝟙 _) (hat : ∀ i, a.app i ≫ t.app i = 𝟙 _) {T : C}
    {rk : T ⟶ R.obj k} {rj : T ⟶ R.obj j} (hk : rk ≫ R.map e = rj) {c : T ⟶ Vs.obj j}
    (hc : rj = c ≫ a.app j) : rk ≫ t.app k = rk ≫ s.app k := by
  rw [eq_comp_a_of_eq_comp_a e hcart has hk hc]
  simp only [Category.assoc, hat, has]

end CategoryTheory

end
