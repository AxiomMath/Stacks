module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
# When two right fractions define the same morphism of `S⁻¹𝒞`

Let `S` be a right multiplicative system on `𝒞` and let `L : 𝒞 ⥤ D` be a localization functor
for `S`.

* `map_eq_iff_rightFractionRel`: two right fractions `φ, ψ : X ⟶ Y` have the same image in the
  localization if and only if they are `RightFractionRel`-related, the relation by which right
  fractions are identified in the construction of `S⁻¹𝒞`.
* `CategoryTheory.MorphismProperty.RightFraction.map_mk_eq_map_mk_tfae` (Stacks 04VJ): for two
  right fractions `(f : X' ⟶ Y, s : X' ⟶ X)` and `(g : X' ⟶ Y, s : X' ⟶ X)` with the same
  denominator, equality of their images is equivalent to the existence of `t : X'' ⟶ X'` in `S`
  with `t ≫ f = t ≫ g`, and to the existence of `a : X'' ⟶ X'` with `a ≫ f = a ≫ g` and
  `a ≫ s ∈ S`.
-/
@[expose] public section

open CategoryTheory MorphismProperty

/-- For a right multiplicative system `W` on `C` and a localization functor `L : C ⥤ D` at `W`,
two right fractions `φ ψ : X ⟶ Y` have the same image in `D` if and only if
`RightFractionRel φ ψ`, the relation by which right fractions are identified in the construction
of the localization. The common-denominator criterion of Stacks 04VJ is
`CategoryTheory.MorphismProperty.RightFraction.map_mk_eq_map_mk_tfae`. -/
theorem map_eq_iff_rightFractionRel {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {W : MorphismProperty C} [W.HasRightCalculusOfFractions] [L.IsLocalization W]
    {X Y : C} (φ ψ : W.RightFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      RightFractionRel φ ψ := by
  have h_main : φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _
      _) ↔ RightFractionRel φ ψ := by grind only [RightFraction.map_eq_iff]
  grind

namespace CategoryTheory.MorphismProperty.RightFraction

/-- **Stacks 04VJ.** Let `W` be a right multiplicative system on `C` and `L : C ⥤ D` a
localization functor at `W`. For two right fractions `(f : X' ⟶ Y, s : X' ⟶ X)` and
`(g : X' ⟶ Y, s : X' ⟶ X)` with the same denominator `s`, the following are equivalent:
1. their images in `D` are equal;
2. there is a morphism `t : X'' ⟶ X'` in `W` with `t ≫ f = t ≫ g`;
3. there is a morphism `a : X'' ⟶ X'` with `a ≫ f = a ≫ g` and `a ≫ s` in `W`. -/
@[stacks 04VJ]
theorem map_mk_eq_map_mk_tfae {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {W : MorphismProperty C} [W.HasRightCalculusOfFractions] [L.IsLocalization W]
    {X Y X' : C} (s : X' ⟶ X) (hs : W s) (f g : X' ⟶ Y) :
    List.TFAE
      [(RightFraction.mk s hs f).map L (Localization.inverts _ _) =
          (RightFraction.mk s hs g).map L (Localization.inverts _ _),
        ∃ (X'' : C) (t : X'' ⟶ X'), W t ∧ t ≫ f = t ≫ g,
        ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ W (a ≫ s)] := by
  have : IsIso (L.map s) := Localization.inverts L W s hs
  have h₁ : (RightFraction.mk s hs f).map L (Localization.inverts _ _) =
      (RightFraction.mk s hs g).map L (Localization.inverts _ _) ↔ L.map f = L.map g :=
    cancel_epi (inv (L.map s))
  tfae_have 1 ↔ 2 := by
    rw [h₁, MorphismProperty.map_eq_iff_precomp L W]
    exact ⟨fun ⟨X'', t, ht, h⟩ => ⟨X'', t, ht, h⟩, fun ⟨X'', t, ht, h⟩ => ⟨X'', t, ht, h⟩⟩
  tfae_have 2 → 3 := fun ⟨X'', t, ht, h⟩ => ⟨X'', t, h, W.comp_mem _ _ ht hs⟩
  tfae_have 3 → 1 := by
    rintro ⟨X'', a, h, ha⟩
    rw [h₁]
    have : IsIso (L.map a ≫ L.map s) := by
      rw [← L.map_comp]
      exact Localization.inverts L W _ ha
    have : IsIso (L.map a) := IsIso.of_isIso_comp_right (L.map a) (L.map s)
    rw [← cancel_epi (L.map a), ← L.map_comp, ← L.map_comp, h]
  tfae_finish

end CategoryTheory.MorphismProperty.RightFraction
