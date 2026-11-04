module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ClosedCoverChernBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.PicardTrivialOpenUFD.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnitBranchGlobalEquation

/-!
# The Gysin map on fundamental classes and on classes supported in the divisor

Two consequences of [Stacks, Tag 02TB] and [Stacks, Tag 02T9] used for [Stacks, Tag 0FEB]:

* `Stacks.Chow.gysinChowOfInvertible_fundamentalChowClass`: if the zero scheme `D` of a section
  of an invertible module on `T` is an effective Cartier divisor and `T` has δ-dimension at most
  `k + 1`, then `i^*[T]_{k+1} = [D]_k`;
* `Stacks.Chow.gysinChowOfInvertible_pushforward_eq_zero`: if the module is trivial, the Gysin map
  kills every class pushed forward from the zero scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The fundamental cycle of a scheme is the cycle of the whole scheme as the closed subscheme cut
out by the zero ideal. -/
theorem fundamentalCycle_eq_bot {S : Scheme.{u}} (q : S ⟶ C.S) [LocallyOfFiniteType q] (d : ℤ) :
    fundamentalCycle C q d =
      cycleAssociatedToClosedSubscheme C q (⊥ : S.IdealSheafData).subschemeι d := by
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C q (𝟙 S) _
    (asIso (⊥ : S.IdealSheafData).subschemeι).symm (by simp) d

/-- **`i^*[T]_{k+1} = [D]_k`** for the zero scheme `D` of a section of an invertible module, when
`D` is an effective Cartier divisor and `T` has δ-dimension at most `k + 1`. -/
theorem gysinChowOfInvertible_fundamentalChowClass
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt))
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme T L s)) :
    gysinChowOfInvertible C p k L s (fundamentalChowClass C p (k + 1)) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) k := by
  have hs : (Stacks.Divisors.sectionsOfTop L s).eval (op ⊤) = s :=
    Stacks.Divisors.sectionsOfTop_eval_top L s
  have hbot : schemeDeltaDimension C ((⊥ : T.IdealSheafData).subschemeι ≫ p) ≤
      ((k + 1 : ℤ) : EInt) := schemeDeltaDimension_le_of_isClosedImmersion C p _ hdim
  have key := gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme C p k L
    (Stacks.Divisors.sectionsOfTop L s) ⊥ hbot (by
      rw [hs]
      exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _ hC _)
  rw [hs] at key
  rw [fundamentalChowClass, fundamentalCycle_eq_bot, gysinChowOfInvertible_mk, key,
    fundamentalChowClass, fundamentalCycle_eq_bot, Scheme.IdealSheafData.comap_bot]
  rfl

/-- **The Gysin map of a section of a trivial invertible module kills the classes pushed forward
from its zero scheme**: on the zero scheme the restricted section vanishes identically, so the
Gysin map there is capping with the first Chern class of a trivial module (Stacks 02T9). -/
theorem gysinChowOfInvertible_pushforward_eq_zero
    (φ : L ≅ Scheme.unitModule T)
    (δ : chowGroup C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) (k + 1)) :
    gysinChowOfInvertible C p k L s
      (chowPushforwardOfIsClosedImmersion C _ p (Stacks.Divisors.zeroScheme T L s).subschemeι rfl
        (k + 1) δ) = 0 := by
  let D := Stacks.Divisors.zeroScheme T L s
  have hTA := gysinChowOfInvertible_properChowPushforward C p (D.subschemeι ≫ p) D.subschemeι rfl
    k L s (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      D.subschemeι C (D.subschemeι ≫ p) p rfl (k + 1)) δ
  refine hTA.trans ?_
  -- on `D` the restricted section vanishes
  let L' := (Scheme.Modules.pullback D.subschemeι).obj L
  let s' := AlgebraicGeometry.pullbackGlobalSections D.subschemeι L s
  have hD' : Stacks.Divisors.zeroScheme D.subscheme L' s' = ⊥ := by
    rw [Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.comap_eq_bot_iff_le]
  have : IsIso (Stacks.Divisors.zeroScheme D.subscheme L' s').subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 hD'
  have hφ' : L' ≅ Scheme.unitModule D.subscheme :=
    (Scheme.Modules.pullback D.subschemeι).mapIso φ ≪≫ Scheme.Modules.pullbackUnitIso _
  have hzero : gysinChowOfInvertible C (D.subschemeι ≫ p) k L' s' δ = 0 := by
    refine chowPushforwardOfIso_injective C _ (D.subschemeι ≫ p)
      (Stacks.Divisors.zeroScheme D.subscheme L' s').subschemeι rfl k ?_
    refine (properChowPushforward_gysinChowOfInvertible C (D.subschemeι ≫ p) k L' s' δ).trans ?_
    rw [map_zero, firstChernClassCapChow_congr C (D.subschemeι ≫ p) k hφ' δ]
    induction δ using QuotientAddGroup.induction_on with
    | H β =>
      exact (firstChernClassCapChow_mk C k (D.subschemeι ≫ p) _ β).trans
        (firstChernClassCapOfInvertible_unit C (D.subschemeι ≫ p) k β)
  rw [hzero, map_zero]

end Stacks.Chow

end
