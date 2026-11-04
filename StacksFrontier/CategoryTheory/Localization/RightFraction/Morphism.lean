module
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism `f s⁻¹` of `S⁻¹C`

Stacks 0BM3: for a right multiplicative system `W` on `C`, a morphism `f : X' ⟶ Y` of `C`
together with a morphism `s : X' ⟶ X` of `W` names the morphism `f s⁻¹ : X ⟶ Y` of the
localization `S⁻¹C = W.Localization`, the `RightFractionRel`-class of the pair `(f, s)`. It is
characterised by `W.Q.map s ≫ f s⁻¹ = W.Q.map f`, and two such pairs name the same morphism
exactly when they are `RightFractionRel`-related.
-/

@[expose] public section


open CategoryTheory

namespace RightLocalizationAsFraction

variable {C : Type*} [Category C] (W : MorphismProperty C)

/-- The pair `(f, s)` with `f : X' ⟶ Y`, `s : X' ⟶ X`, and `s ∈ W`, packaged as a
`RightFraction`. This is the underlying data of the equivalence class `f s⁻¹`. -/
def fracPair {X Y X' : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    W.RightFraction X Y :=
  { X' := X', s := s, hs := hs, f := f }

/-- Given a morphism `f : X' ⟶ Y` and a morphism `s : X' ⟶ X` with `s ∈ W` (where
`W` is a right multiplicative system, i.e. has a right calculus of fractions),
the morphism `f s⁻¹ : X ⟶ Y` in the localized category `S⁻¹C = W.Localization`.

Concretely, this is the image under `W.Q` of the pair `(f, s)`, which represents
the equivalence class of `(f, s)` under `RightFractionRel`. -/
@[stacks 0BM3]
noncomputable def fInvS [W.HasRightCalculusOfFractions]
    {X Y X' : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    W.Q.obj X ⟶ W.Q.obj Y :=
  (fracPair W f s hs).map W.Q (MorphismProperty.Q_inverts W)

/-- The morphism `f s⁻¹ : X ⟶ Y` in `S⁻¹C` is well-defined as the equivalence
class of the pair `(f, s)`: two right fractions `(f₁, s₁)` and `(f₂, s₂)` give
the same morphism in the localized category iff they are related by the
equivalence relation `RightFractionRel`. -/
@[sga "4½ Etat_0 2.3.2" "partial"]
theorem fInvS_eq_iff_rightFractionRel [W.HasRightCalculusOfFractions]
    {X Y X' X'' : C}
    (f₁ : X' ⟶ Y) (s₁ : X' ⟶ X) (hs₁ : W s₁)
    (f₂ : X'' ⟶ Y) (s₂ : X'' ⟶ X) (hs₂ : W s₂) :
    fInvS W f₁ s₁ hs₁ = fInvS W f₂ s₂ hs₂ ↔
      MorphismProperty.RightFractionRel (fracPair W f₁ s₁ hs₁) (fracPair W f₂ s₂ hs₂) :=
  MorphismProperty.RightFraction.map_eq_iff W.Q W _ _

/-- Characterization: the morphism `f s⁻¹` in `S⁻¹C` satisfies
`W.Q.map s ≫ (f s⁻¹) = W.Q.map f`. In other words, in the localized category,
`f s⁻¹` represents the "fraction" by being the unique morphism such that
precomposition with `W.Q.map s` gives back `W.Q.map f`. -/
theorem Q_map_s_comp_fInvS [W.HasRightCalculusOfFractions]
    {X Y X' : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : W s) :
    W.Q.map s ≫ fInvS W f s hs = W.Q.map f :=
  MorphismProperty.RightFraction.map_s_comp_map _ W.Q (MorphismProperty.Q_inverts W)

end RightLocalizationAsFraction

