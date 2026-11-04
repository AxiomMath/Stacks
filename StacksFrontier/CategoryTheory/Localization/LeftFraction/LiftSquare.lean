module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a commutative square from a left localization (Stacks 05Q3)

Let `W` be a left multiplicative system on a category `C` and let
`Q : C ⥤ LeftFraction.Localization W` be the localization functor built from left
fractions. Given `f : X ⟶ Y` and `f' : X' ⟶ Y'` in `C` and a commutative square
`Q f ≫ b = a ≫ Q f'` in the localization, the square lifts to `C`: there are objects
`X''`, `Y''`, a morphism `f'' : X'' ⟶ Y''`, morphisms `s : X' ⟶ X''` and `t : Y' ⟶ Y''`
in `W` and morphisms `g : X ⟶ X''`, `h : Y ⟶ Y''` with

* `f ≫ h = g ≫ f''` (the left square of the source diagram),
* `s ≫ f'' = f' ≫ t` (the right square),

and `a`, `b` are the left fractions `s⁻¹ g` and `t⁻¹ h`, i.e. the classes of `(g, s)`
and `(h, t)`.

The proof represents `a` as a left fraction `(g₀, s₀)`, applies the left Ore condition
twice — once to `(s₀, f')` and once to the denominator of a representation of `b` — to
reach a common denominator `t₁`, and then corrects by a further `W`-morphism obtained
from left cancellation (`HasLeftCalculusOfFractions.ext`), which is what turns the
square that commutes in the localization into a square that commutes in `C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)
  [W.HasLeftCalculusOfFractions]

/-- Post-composing a left fraction `(i, q, hq)` by `j`, where `q ≫ j = t₀ ≫ r`,
yields the same morphism as the left fraction `(i ≫ j, t₀ ≫ r, ht₁)` in the localisation. -/
private lemma map_eq_of_post_comp
    {X Y Y' Z Y₁'' : C}
    (i : Y ⟶ Z) (q : Y' ⟶ Z) (hq : W q)
    (t₀ : Y' ⟶ X) (r : X ⟶ Y₁'') (j : Z ⟶ Y₁'')
    (ht₁ : W (t₀ ≫ r)) (heq : q ≫ j = t₀ ≫ r) :
    (LeftFraction.mk i q hq).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) =
    (LeftFraction.mk (i ≫ j) (t₀ ≫ r) ht₁).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) := by
  rw [LeftFraction.map_eq_iff]
  exact ⟨Y₁'', j, 𝟙 _, by simpa using heq, by simp, by rwa [heq]⟩

/-- Variant of `map_eq_of_post_comp`: post-composing both numerator and denominator of a
left fraction by the same morphism `d` yields an equal morphism in the localisation. -/
private lemma map_eq_of_post_comp_same
    {X Y Z Z' : C} (h : X ⟶ Z) (t : Y ⟶ Z) (ht : W t) (d : Z ⟶ Z') (ht' : W (t ≫ d)) :
    (LeftFraction.mk h t ht).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) =
    (LeftFraction.mk (h ≫ d) (t ≫ d) ht').map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) :=
  map_eq_of_post_comp W h t ht t d d ht' rfl

/-- Two left fractions differing only by an extra `≫ 𝟙` on the denominator have equal
images in the localisation. -/
private lemma comp_id_leftFraction_map_eq
    {X Y Z : C} (f' : X ⟶ Z) (t : Y ⟶ Z) (ht : W t) (ht' : W (t ≫ 𝟙 Z)) :
    (LeftFraction.mk f' (t ≫ 𝟙 Z) ht').map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) =
    (LeftFraction.mk f' t ht).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) := by
  simp

/-- Composition formula: `Q(f) ≫ (h, t, ht).map Q = (f ≫ h, t, ht).map Q`. -/
private lemma Qmap_comp_leftFraction
    {X Y Y' Z : C} (f : X ⟶ Y) (h : Y ⟶ Z) (t : Y' ⟶ Z) (ht : W t) :
    (LeftFraction.Localization.Q W).map f ≫
        (LeftFraction.mk h t ht).map (LeftFraction.Localization.Q W)
          (Localization.inverts _ _) =
    (LeftFraction.mk (f ≫ h) t ht).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) := by
  set L := LeftFraction.Localization.Q W
  have hinv : W.IsInvertedBy L := Localization.inverts _ _
  set z₁ : W.LeftFraction X Y := LeftFraction.mk f (𝟙 Y) (W.id_mem Y)
  set z₂ : W.LeftFraction Y Y' := LeftFraction.mk h t ht
  set z₃ : W.LeftFraction z₁.Y' z₂.Y' := LeftFraction.mk h (𝟙 Z) (W.id_mem Z)
  have hsq : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f := by simp [z₁, z₂, z₃]
  have hz1_eq : z₁.map L hinv = L.map f := LeftFraction.map_ofHom W f L hinv
  rw [← hz1_eq, LeftFraction.map_comp_map_eq_map z₁ z₂ z₃ hsq L]
  exact comp_id_leftFraction_map_eq W (f ≫ h) t ht _

/-- Composition formula: `(g, s, hs).map Q ≫ Q(f') = (g ≫ f'', t, ht).map Q`,
provided `s ≫ f'' = f' ≫ t`. -/
private lemma leftFraction_comp_Qmap
    {X X' Y' Z₁ Z₂ : C}
    (g : X ⟶ Z₁) (s : X' ⟶ Z₁) (hs : W s)
    (f' : X' ⟶ Y') (t : Y' ⟶ Z₂) (ht : W t) (f'' : Z₁ ⟶ Z₂)
    (hsq : s ≫ f'' = f' ≫ t) :
    (LeftFraction.mk g s hs).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) ≫
      (LeftFraction.Localization.Q W).map f' =
    (LeftFraction.mk (g ≫ f'') t ht).map (LeftFraction.Localization.Q W)
        (Localization.inverts _ _) := by
  set Q := LeftFraction.Localization.Q W
  have hL : W.IsInvertedBy Q := Localization.inverts _ _
  have : IsIso (Q.map t) := hL t ht
  apply (cancel_mono (Q.map t)).mp
  rw [LeftFraction.map_comp_map_s (LeftFraction.mk (g ≫ f'') t ht) Q hL,
    Category.assoc, ← Q.map_comp, ← hsq, Q.map_comp, ← Category.assoc,
    LeftFraction.map_comp_map_s (LeftFraction.mk g s hs) Q hL]
  exact (Q.map_comp g f'').symm

/-- **Stacks 05Q3**.
A commutative square in the left localisation `W⁻¹C` between images of
morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y'` of `C` lifts to a commutative
diagram in `C` involving two morphisms in `W`. -/
@[stacks 05Q3]
lemma exists_leftFraction_lift_of_commSq
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj X')
    (b : (LeftFraction.Localization.Q W).obj Y ⟶ (LeftFraction.Localization.Q W).obj Y')
    (sq : (LeftFraction.Localization.Q W).map f ≫ b =
      a ≫ (LeftFraction.Localization.Q W).map f') :
    ∃ (X'' Y'' : C) (g : X ⟶ X'') (s : X' ⟶ X'') (hs : W s)
      (h : Y ⟶ Y'') (t : Y' ⟶ Y'') (ht : W t) (f'' : X'' ⟶ Y''),
      f ≫ h = g ≫ f'' ∧ s ≫ f'' = f' ≫ t ∧
      a = (LeftFraction.mk g s hs).map (LeftFraction.Localization.Q W)
            (Localization.inverts _ _) ∧
      b = (LeftFraction.mk h t ht).map (LeftFraction.Localization.Q W)
            (Localization.inverts _ _) := by
  -- Step 1: Represent `a` as a left fraction `α = (g₀, s₀)`.
  obtain ⟨α, ha⟩ := Localization.exists_leftFraction (LeftFraction.Localization.Q W) W a
  -- Step 2: Apply the Ore condition to `(s₀, f')` to get `(f₀'', t₀)`.
  obtain ⟨ψ, hψ⟩ := HasLeftCalculusOfFractions.exists_leftFraction (W := W)
    (RightFraction.mk α.s α.hs f')
  -- Step 3: Represent `b` as a left fraction `β = (i, q)`.
  obtain ⟨β, hb⟩ := Localization.exists_leftFraction (LeftFraction.Localization.Q W) W b
  -- Step 4: Apply the Ore condition to `(q, t₀)` to get `(j, r)`.
  obtain ⟨ξ, hξ⟩ := HasLeftCalculusOfFractions.exists_leftFraction (W := W)
    (RightFraction.mk β.s β.hs ψ.s)
  -- Step 5: Common denominator `t₁ = t₀ ≫ r`; verify the right square.
  set t₁ : Y' ⟶ ξ.Y' := ψ.s ≫ ξ.s
  have ht₁ : W t₁ := W.comp_mem _ _ ψ.hs ξ.hs
  set f₁'' : α.Y' ⟶ ξ.Y' := ψ.f ≫ ξ.s
  set h₁ : Y ⟶ ξ.Y' := β.f ≫ ξ.f
  have hsq1 : α.s ≫ f₁'' = f' ≫ t₁ := by
    dsimp only [f₁'', t₁]
    rw [← Category.assoc, ← hψ, Category.assoc]
  have hb' : b = (LeftFraction.mk h₁ t₁ ht₁).map (LeftFraction.Localization.Q W)
                  (Localization.inverts _ _) :=
    hb.trans (map_eq_of_post_comp W β.f β.s β.hs ψ.s ξ.s ξ.f ht₁ hξ.symm)
  -- Step 6: Use `sq` to produce equal left fractions of common denominator `t₁`.
  have heq_in_loc :
      (LeftFraction.mk (f ≫ h₁) t₁ ht₁).map (LeftFraction.Localization.Q W)
          (Localization.inverts _ _) =
      (LeftFraction.mk (α.f ≫ f₁'') t₁ ht₁).map (LeftFraction.Localization.Q W)
          (Localization.inverts _ _) := by
    rw [← Qmap_comp_leftFraction W f h₁ t₁ ht₁, ← hb',
      ← leftFraction_comp_Qmap W α.f α.s α.hs f' t₁ ht₁ f₁'' hsq1, ← ha]
    exact sq
  rw [LeftFraction.map_eq_iff (LeftFraction.Localization.Q W) W] at heq_in_loc
  obtain ⟨Z', u, v, huv, hfuv, hW⟩ := heq_in_loc
  -- Step 7: Apply the `ext` axiom to find `d` with `u ≫ d = v ≫ d`; set `d₂ := u ≫ d`.
  obtain ⟨Y₃, d, hd, huvd⟩ :=
    HasLeftCalculusOfFractions.ext (W := W) u v t₁ ht₁ huv
  set d₂ : ξ.Y' ⟶ Y₃ := u ≫ d
  have ht₁d₂ : W (t₁ ≫ d₂) := by
    rw [show t₁ ≫ d₂ = (t₁ ≫ u) ≫ d by simp [d₂]]
    exact W.comp_mem _ _ hW hd
  refine ⟨α.Y', Y₃, α.f, α.s, α.hs, h₁ ≫ d₂, t₁ ≫ d₂, ht₁d₂, f₁'' ≫ d₂, ?_, ?_, ha, ?_⟩
  · calc f ≫ h₁ ≫ d₂
        = (f ≫ h₁) ≫ u ≫ d := by rw [← Category.assoc]
      _ = (α.f ≫ f₁'') ≫ v ≫ d := by rw [← Category.assoc, hfuv, Category.assoc]
      _ = α.f ≫ f₁'' ≫ d₂ := by rw [Category.assoc, ← huvd]
  · rw [← Category.assoc, hsq1, Category.assoc]
  · exact hb'.trans (map_eq_of_post_comp_same W h₁ t₁ ht₁ d₂ ht₁d₂)

end CategoryTheory.MorphismProperty
