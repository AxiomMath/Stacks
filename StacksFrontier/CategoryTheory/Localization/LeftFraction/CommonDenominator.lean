module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Common denominators for a finite family of morphisms of `S⁻¹𝒞`

Stacks 04VE: if `S` is a left multiplicative system on `𝒞` and `L` is a localization functor
for `S`, then any finite family `gᵢ : L(Xᵢ) ⟶ L(Y)` admits a common denominator: there are a
morphism `s : Y ⟶ Y'` in `S` and morphisms `fᵢ : Xᵢ ⟶ Y'` of `𝒞` with `gᵢ = L(fᵢ) ≫ L(s)⁻¹`.
The proof is by induction on finite types (`Finite.induction_empty_option`); the `Option α`
step combines the denominator from the induction hypothesis with the one for the new index
using left calculus of fractions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.Localization

universe v u

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

/-- If `s₀ ≫ a = s`, then composing `f₀` with `a` and inverting `s` agrees with the
original left fraction `(f₀, s₀)` after applying `L`. -/
private lemma leftFraction_map_comp
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]
    {X₀ Y Y₀ Z : C}
    (f₀ : X₀ ⟶ Y₀) (s₀ : Y ⟶ Y₀) (hs₀ : W s₀)
    (a : Y₀ ⟶ Z) (s : Y ⟶ Z) (hs : W s) (hfac : s₀ ≫ a = s) :
    L.map (f₀ ≫ a) ≫ (Localization.isoOfHom L W s hs).inv =
      L.map f₀ ≫ (Localization.isoOfHom L W s₀ hs₀).inv := by
  subst hfac
  simp only [Localization.isoOfHom, asIso_inv, L.map_comp, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq]
  simp

/-- Equivalence transport: from a representation indexed by `α`, build one indexed
by `β` using `e : α ≃ β` and `eqToHom` bookkeeping. -/
private lemma exists_common_leftFraction_equiv_aux
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions]
    {α β : Type*} (e : α ≃ β)
    {X : β → C} {Y Y' : C} (s : Y ⟶ Y') (hs : W s)
    (f' : ∀ i : α, X (e i) ⟶ Y')
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y)
    (hf' : ∀ i : α, g (e i) = L.map (f' i) ≫ (Localization.isoOfHom L W s hs).inv)
    (b : β) :
    g b = L.map (eqToHom (by simp) ≫ f' (e.symm b)) ≫
      (Localization.isoOfHom L W s hs).inv := by
  obtain ⟨a, rfl⟩ := e.surjective b
  have key : ∀ (a' : α) (heq : a' = a),
      f' a' = eqToHom (by rw [heq]) ≫ f' a := by
    rintro a' rfl
    simp
  rw [hf' a, key (e.symm (e a)) (e.symm_apply_apply a), L.map_comp, L.map_comp]
  simp [eqToHom_map]

/-- Equivalence preservation. -/
private lemma exists_common_leftFraction_equiv
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions]
    {α β : Type*} (e : α ≃ β)
    (hα : ∀ {X : α → C} {Y : C} (g : ∀ i, L.obj (X i) ⟶ L.obj Y),
      ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
        ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv)
    {X : β → C} {Y : C} (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv := by
  obtain ⟨Y', s, hs, f', hf'⟩ := hα (X := X ∘ e) (fun i => g (e i))
  exact ⟨Y', s, hs, fun b => eqToHom (by simp) ≫ f' (e.symm b),
    exists_common_leftFraction_equiv_aux L e s hs f' g hf'⟩

/-- Inductive step: if the property holds for `α`, it holds for `Option α`. Apply the
induction hypothesis to the `some`-fibre, represent `g none` by a left fraction, and
combine the two denominators using left calculus. -/
private lemma exists_common_leftFraction_option
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions]
    {α : Type*}
    (hα : ∀ {X : α → C} {Y : C} (g : ∀ i, L.obj (X i) ⟶ L.obj Y),
      ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
        ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv)
    {X : Option α → C} {Y : C} (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv := by
  obtain ⟨Y'', s'', hs'', f'', hf''⟩ := hα (fun i => g (some i))
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W (g none)
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk s'' hs'' φ.s).exists_leftFraction
  refine ⟨ψ.Y', φ.s ≫ ψ.s, W.comp_mem _ _ φ.hs ψ.hs,
    fun | none => φ.f ≫ ψ.s | some j => f'' j ≫ ψ.f, ?_⟩
  rintro (_ | j)
  · rw [hφ, LeftFraction.map_eq]
    exact (leftFraction_map_comp L φ.f φ.s φ.hs ψ.s _ _ rfl).symm
  · rw [hf'' j]
    exact (leftFraction_map_comp L (f'' j) s'' hs'' ψ.f _ _ hψ.symm).symm

/-- **Stacks 04VE**.
Let `W : MorphismProperty C` have left calculus of fractions and let `L` be a
localisation functor for `W`. For any finite family
`g : ∀ i, L.obj (X i) ⟶ L.obj Y`, there exist a common target `Y' : C`, a
morphism `s : Y ⟶ Y'` with `W s`, and a family `f : ∀ i, X i ⟶ Y'` such that
each `g i` equals `L.map (f i) ≫ (Localization.isoOfHom L W s _).inv`. -/
@[stacks 04VE]
theorem exists_common_leftFraction
    {C : Type u} [Category.{v} C] {W : MorphismProperty C}
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions]
    {ι : Type*} [Finite ι]
    {X : ι → C} {Y : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv := by
  apply Finite.induction_empty_option (P := fun ι =>
    ∀ {X : ι → C} {Y : C} (g : ∀ i, L.obj (X i) ⟶ L.obj Y),
      ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
        ∀ i, g i = L.map (f i) ≫ (Localization.isoOfHom L W s hs).inv)
  · intro α β e hα _ _ g
    exact exists_common_leftFraction_equiv L e @hα g
  · intro _ _ g
    exact ⟨_, 𝟙 _, W.id_mem _, fun i => i.elim, fun i => i.elim⟩
  · intro α _ hα _ _ g
    exact exists_common_leftFraction_option L @hα g

end CategoryTheory.Localization
