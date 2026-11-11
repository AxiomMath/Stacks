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
# When two left fractions define the same morphism of `S⁻¹𝒞`

Stacks 04VF: let `S` be a left multiplicative system on `𝒞` and let `L : 𝒞 ⥤ D` be a
localization functor for `S`. Two left fractions `(f, s)` and `(g, s)` from `X` to `Y` with the
same denominator `s : Y ⟶ Y'` have the same image in the localization if and only if
`f ≫ t = g ≫ t` for some `t : Y' ⟶ Y''` in `S`, if and only if `f ≫ a = g ≫ a` for some
`a : Y' ⟶ Y''` with `s ≫ a ∈ S`. This is `leftFraction_map_eq_tfae_of_same_denominator`.

We also record `map_eq_iff_leftFractionRel`, the general criterion for two arbitrary left
fractions (Mathlib's `LeftFraction.map_eq_iff`).
-/

@[expose] public section

open CategoryTheory MorphismProperty

/-- For a left multiplicative system `W` on `C` and a localization functor `L : C ⥤ D` at `W`,
two left fractions `φ ψ : X ⟶ Y` have the same image in `D` if and only if
`LeftFractionRel φ ψ`, i.e. if and only if there are `t₁ : φ.Y' ⟶ Z` and `t₂ : ψ.Y' ⟶ Z` with
`φ.s ≫ t₁ = ψ.s ≫ t₂`, `φ.f ≫ t₁ = ψ.f ≫ t₂` and `φ.s ≫ t₁ ∈ W`. This is a restatement of
Mathlib's `LeftFraction.map_eq_iff`; the same-denominator statement of Stacks 04VF is
`leftFraction_map_eq_tfae_of_same_denominator`. -/
theorem map_eq_iff_leftFractionRel {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {W : MorphismProperty C} [W.HasLeftCalculusOfFractions] [L.IsLocalization W]
    {X Y : C} (φ ψ : W.LeftFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      LeftFractionRel φ ψ := by
  have h_main : φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _
      _) ↔ LeftFractionRel φ ψ := by grind only [LeftFraction.map_eq_iff]
  grind

/-- **Stacks 04VF.** Let `W` be a left multiplicative system on `C` and `L : C ⥤ D` a
localization functor at `W`. For `f g : X ⟶ Y'` and `s : Y ⟶ Y'` in `W`, the following are
equivalent:
1. the left fractions `(f, s)` and `(g, s)` define the same morphism `L.obj X ⟶ L.obj Y`;
2. there is `t : Y' ⟶ Y''` in `W` with `f ≫ t = g ≫ t`;
3. there is `a : Y' ⟶ Y''` with `s ≫ a ∈ W` and `f ≫ a = g ≫ a`. -/
@[stacks 04VF "Mathlib's `LeftFraction` `(f, s)` is the Stacks fraction `s⁻¹f`; the
localization `S⁻¹𝒞` is represented by any localization functor `L` at `W`."]
theorem leftFraction_map_eq_tfae_of_same_denominator {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) {W : MorphismProperty C} [W.HasLeftCalculusOfFractions] [L.IsLocalization W]
    {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    List.TFAE
      [(LeftFraction.mk f s hs).map L (Localization.inverts _ _) =
          (LeftFraction.mk g s hs).map L (Localization.inverts _ _),
        ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t,
        ∃ (Y'' : C) (a : Y' ⟶ Y''), W (s ≫ a) ∧ f ≫ a = g ≫ a] := by
  tfae_have 1 → 2 := by
    intro h
    have hfg : L.map f = L.map g := by
      rw [← LeftFraction.map_comp_map_s (LeftFraction.mk f s hs) L (Localization.inverts _ _),
        h, LeftFraction.map_comp_map_s]
    obtain ⟨Z, t, ht, e⟩ := (MorphismProperty.map_eq_iff_postcomp L W f g).mp hfg
    exact ⟨Z, t, ht, e⟩
  tfae_have 2 → 3 := by
    rintro ⟨Y'', t, ht, e⟩
    exact ⟨Y'', t, W.comp_mem _ _ hs ht, e⟩
  tfae_have 3 → 1 := by
    rintro ⟨Y'', a, ha, e⟩
    have : IsIso (L.map s) := Localization.inverts L W s hs
    have : IsIso (L.map s ≫ L.map a) := by
      rw [← L.map_comp]
      exact Localization.inverts L W _ ha
    have : IsIso (L.map a) := IsIso.of_isIso_comp_left (L.map s) (L.map a)
    have hfg : L.map f = L.map g := by
      rw [← cancel_mono (L.map a), ← L.map_comp, ← L.map_comp, e]
    simp only [LeftFraction.map, hfg]
  tfae_finish
