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
# Universal property of the localization at a left multiplicative system

The left-handed lemma, Stacks 04VG: for a left multiplicative system `S`, the localization
`S⁻¹𝓒 = LeftFraction.Localization S` (left fractions, Stacks 04VD) carries a functor
`Q : 𝓒 ⥤ S⁻¹𝓒` that is the identity on objects and sends `f` to the left fraction `(f, 𝟙)`;
`Q s` is an isomorphism for every `s ∈ S`; and every functor `G : 𝓒 ⥤ 𝓓` inverting `S`
factors as `G = Q ⋙ H` for a unique `H : S⁻¹𝓒 ⥤ 𝓓`. Stacks 04VG itself is registered on the
Mathlib declarations (`StacksFrontier.MathlibRegistrations.Ch04`); this file packages them.

The right-handed lemma, Stacks 04VK, for a right multiplicative system and the category of
right fractions, is in `StacksFrontier.CategoryTheory.Localization.RightFraction.UniversalProperty`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty
  LeftFraction.Localization.StrictUniversalPropertyFixedTarget


universe v u v' u'

variable {𝓒 : Type u} [Category.{v} 𝓒]
variable (S : MorphismProperty 𝓒) [S.HasLeftCalculusOfFractions]
variable {𝓓 : Type u'} [Category.{v'} 𝓓]

/-- The canonical localization functor `Q04VK : 𝓒 ⥤ S⁻¹𝓒` for a left multiplicative system
(the left form, Stacks 04VG (1); the right form 04VK (1) is `RightLocalization.Q`).
This is the Mathlib functor `LeftFraction.Localization.Q`. -/
@[sga "5 V 2.3" "functor p : E → E(S⁻¹)", sga "4½ Etat_0 2.3.1"]
noncomputable def Q04VK : 𝓒 ⥤ LeftFraction.Localization S := LeftFraction.Localization.Q S

/-- Stacks 04VG (1), object part: the functor `Q04VK` acts as the identity on
objects. -/
theorem Q_obj (X : 𝓒) : (Q04VK S).obj X = X := rfl

/-- Stacks 04VG (1), morphism part: the functor `Q04VK` sends `f : X ⟶ Y` to the
canonical morphism in `S⁻¹𝓒` induced by the left fraction `(f, 𝟙 _)`. -/
theorem Q_map {X Y : 𝓒} (f : X ⟶ Y) :
    (Q04VK S).map f =
      (LeftFraction.ofHom S f).map (LeftFraction.Localization.Q S)
        (Localization.inverts _ S) := by
  simp [Q04VK, LeftFraction.map_ofHom]

/-- Stacks 04VG (2), the left form of 04VK (2): For any `s ∈ S` the morphism `Q04VK(s)` is
an isomorphism in `S⁻¹𝓒`. -/
theorem Q_isIso_of_mem {X Y : 𝓒} (s : X ⟶ Y) (hs : S s) :
    IsIso ((Q04VK S).map s) :=
  inferInstanceAs (IsIso (LeftFraction.Localization.Qiso s hs).hom)

/-- Stacks 04VG (3), the left form of 04VK (3) — combined statement: for any functor
`G : 𝓒 ⥤ 𝓓` inverting `S`, there exists a *unique* functor `H : S⁻¹𝓒 ⥤ 𝓓` such that
`H ∘ Q04VK = G`. -/
@[sga "5 V 2.3" "left calc. of fractions",
  sga "4½ Etat_0 2.3.1" "partial",
  sga "4½ Etat_0 Problem2" "partial"]
theorem exists_unique_lift (G : 𝓒 ⥤ 𝓓) (hG : S.IsInvertedBy G) :
    ∃! H : LeftFraction.Localization S ⥤ 𝓓, (Q04VK S) ⋙ H = G :=
  ⟨lift G hG, fac G hG, fun H' hH' => uniq H' _ (hH'.trans (fac G hG).symm)⟩

