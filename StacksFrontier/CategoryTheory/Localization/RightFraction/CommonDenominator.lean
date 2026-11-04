module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.Fintype.Option
public import StacksCore.Tactic.StacksAttribute

/-!
# A common right denominator for a finite family (Stacks 04VI)

Let `W` be a right multiplicative system on a category `C`. A morphism `X ⟶ Y` of the
localization `W⁻¹C` is a *right fraction* `f s⁻¹`: the class of a pair
`(s : X' ⟶ X, f : X' ⟶ Y)` with `s ∈ W`. Stacks 04VI says that finitely many morphisms
out of a common source can be written with a *common denominator*: given
`g i : X ⟶ Y i` in `W⁻¹C` indexed by a finite type, there is a single `s : X' ⟶ X` in
`W` and morphisms `f i : X' ⟶ Y i` of `C` with `g i = (f i) s⁻¹` for every `i`.

Mathlib has the two smallest cases — one morphism
(`CategoryTheory.Localization.exists_rightFraction`) and two
(`MorphismProperty.RightFraction₂`) — but not the statement for an arbitrary finite
family, which is what this file proves.

The induction is over `Finite.induction_empty_option`, i.e. over the shape of the index
type: for `PEmpty` the identity of `X` will do, and passing from `α` to `Option α` means
merging the denominator obtained for the `α`-part with the denominator of the extra
morphism, which is exactly one application of the right Ore condition. Reindexing along
an equivalence of index types is the third case. The common denominator is what makes
statements about finitely many morphisms of `W⁻¹C` reducible to statements in `C`; it is
used, for instance, to transport an additive structure through the localization.

The work is done for an arbitrary localization functor `L` in
`exists_common_rightFraction_general`, phrased with `(Localization.isoOfHom ..).inv`;
`exists_common_rightFraction` then specialises it to `W.Q` and phrases the conclusion
with `RightFraction.map`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.Localization

universe v u

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

section Helpers
variable {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]

/-- Explicit formula for the image of a right fraction in a localization. -/
private lemma rightFraction_map_eq {X Y : C} (φ : W.RightFraction X Y) :
    φ.map L (Localization.inverts L W) =
      (Localization.isoOfHom L W φ.s φ.hs).inv ≫ L.map φ.f := by
  simp [MorphismProperty.RightFraction.map, Localization.isoOfHom]

/-- Changing the denominator of a right fraction by precomposition:
if `a ≫ s₀ = s`, then `(L.map s)⁻¹ ≫ L.map (a ≫ f₀) = (L.map s₀)⁻¹ ≫ L.map f₀`. -/
private lemma rightFraction_map_comp
    {X₀ X Y Z : C} (f₀ : X₀ ⟶ Y) (s₀ : X₀ ⟶ X) (hs₀ : W s₀)
    (a : Z ⟶ X₀) (s : Z ⟶ X) (hs : W s) (hfac : a ≫ s₀ = s) :
    (Localization.isoOfHom L W s hs).inv ≫ L.map (a ≫ f₀) =
      (Localization.isoOfHom L W s₀ hs₀).inv ≫ L.map f₀ := by
  subst hfac
  simp only [Localization.isoOfHom, asIso_inv, L.map_comp]
  rw [← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq]
  simp

/-- Reindexing a common right-denominator existence statement along an
equivalence of finite index types. -/
private lemma exists_common_rightFraction_equiv_aux
    {α β : Type*} (e : α ≃ β)
    {Y : β → C} {X X' : C} (s : X' ⟶ X) (hs : W s)
    (f' : ∀ i : α, X' ⟶ Y (e i))
    (g : ∀ i, L.obj X ⟶ L.obj (Y i))
    (hf' : ∀ i : α, g (e i) =
      (Localization.isoOfHom L W s hs).inv ≫ L.map (f' i))
    (b : β) :
    g b = (Localization.isoOfHom L W s hs).inv ≫
      L.map (f' (e.symm b) ≫ eqToHom (by simp)) := by
  obtain ⟨a, rfl⟩ : ∃ a, e a = b := ⟨_, e.apply_symm_apply b⟩
  rw [hf' a]
  congr 1
  generalize_proofs h
  have ha : e.symm (e a) = a := e.symm_apply_apply a
  clear hf'
  revert h
  rw [ha]
  intro h
  simp

/-- Equivalence case for `Finite.induction_empty_option`. -/
private lemma exists_common_rightFraction_equiv
    {α β : Type*} (e : α ≃ β)
    (hα : ∀ {Y : α → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)),
      ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
        ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i))
    {Y : β → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i) := by
  obtain ⟨X', s, hs, f', hf'⟩ := hα (Y := Y ∘ e) (fun i => g (e i))
  exact ⟨X', s, hs, fun b => f' (e.symm b) ≫ eqToHom (by simp),
    exists_common_rightFraction_equiv_aux L e s hs f' g hf'⟩

variable [W.HasRightCalculusOfFractions]

/-- Base case for `Finite.induction_empty_option`: the empty index type. -/
private lemma exists_common_rightFraction_pempty
    {Y : PEmpty → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i) :=
  ⟨X, 𝟙 X, W.id_mem X, fun i => i.elim, fun i => i.elim⟩

/-- Inductive step: from the statement for `α` to the statement for
`Option α`. Uses `exists_rightFraction` for the `none` component and the right
Ore condition to merge denominators. -/
private lemma exists_common_rightFraction_option
    {α : Type*}
    (hα : ∀ {Y : α → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)),
      ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
        ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i))
    {Y : Option α → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i) := by
  obtain ⟨X₁, s₁, hs₁, f₁, hf₁⟩ := hα (fun a => g (some a))
  obtain ⟨φ_none, hφ_none⟩ := Localization.exists_rightFraction L W (g none)
  -- Right Ore square from `s₁` and `φ_none.s`.
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.LeftFraction.mk s₁ φ_none.s φ_none.hs).exists_rightFraction
  refine ⟨ψ.X', ψ.s ≫ s₁, W.comp_mem _ _ ψ.hs hs₁,
    fun i => match i with
      | none => ψ.f ≫ φ_none.f
      | some j => ψ.s ≫ f₁ j, ?_⟩
  rintro (_ | j)
  · rw [hφ_none, rightFraction_map_eq L φ_none]
    exact (rightFraction_map_comp L φ_none.f φ_none.s φ_none.hs ψ.f _ _
      (by simp [← hψ])).symm
  · rw [hf₁ j]
    exact (rightFraction_map_comp L (f₁ j) s₁ hs₁ ψ.s _ _ rfl).symm

/-- A common right denominator for a finite family of morphisms out of `L.obj X`, for an
arbitrary localization functor `L : C ⥤ D` of `C` at `W`: the family is `g i =
(L.map s)⁻¹ ≫ L.map (f i)` for a single `s : X' ⟶ X` in `W`. This is the form of
Stacks 04VI that does not mention `W.Q`. -/
lemma exists_common_rightFraction_general
    {ι : Type*} [Finite ι] {Y : ι → C} {X : C}
    (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i) := by
  revert Y X g
  apply Finite.induction_empty_option (P := fun ι =>
    ∀ {Y : ι → C} {X : C} (g : ∀ i, L.obj X ⟶ L.obj (Y i)),
      ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
        ∀ i, g i = (Localization.isoOfHom L W s hs).inv ≫ L.map (f i))
  · exact fun e hα => exists_common_rightFraction_equiv L e @hα
  · exact exists_common_rightFraction_pempty L
  · exact fun hα => exists_common_rightFraction_option L @hα

end Helpers

/-- **Stacks 04VI** (common right denominator).

Let `W : MorphismProperty C` admit a right calculus of fractions. Given a
finite family of morphisms `g i : W.Q.obj X ⟶ W.Q.obj (Y i)` in the
localization with common source `W.Q.obj X`, there exist an object `X'` of
`C`, a morphism `s : X' ⟶ X` in `W`, and a family `f i : X' ⟶ Y i` in `C`
such that each `g i` is represented by the right fraction `(s, f i)`. -/
@[stacks 04VI, sga "4½ Etat_0 2.3.2" "partial"]
theorem exists_common_rightFraction
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    {ι : Type*} [Finite ι] {X : C} {Y : ι → C}
    (g : ∀ i, W.Q.obj X ⟶ W.Q.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (MorphismProperty.RightFraction.mk s hs (f i)).map
        W.Q (Localization.inverts _ W) := by
  obtain ⟨X', s, hs, f, hf⟩ := exists_common_rightFraction_general (W := W) W.Q g
  refine ⟨X', s, hs, f, fun i => ?_⟩
  rw [hf i, rightFraction_map_eq W.Q (MorphismProperty.RightFraction.mk s hs (f i))]

end CategoryTheory.Localization
