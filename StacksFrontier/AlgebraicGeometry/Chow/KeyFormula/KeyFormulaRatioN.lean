module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.KeyFormulaOnDivisor

/-!
# The second ratio of the key formula, and a two-sided carrier

Let `X` be integral and locally Noetherian, let `L` and `N` be invertible `𝒪_X`-modules with
nonzero meromorphic sections `s` and `t`, and let `ℱ` be a situation of Stacks 0AYB for them. A
member `Z_i` of the family with `g_i = 1` contributes nothing to the right hand side of the key
formula Stacks 0AYC, since the tame symbol `∂_{B_i}(f_i, 1)` is trivial. Consequently the left
hand side of the key formula is rationally equivalent to zero with witnesses inside the union of
the members where both `f_i` and `g_i` differ from `1`.

## Main results

* `Stacks.Chow.KeyFormulaSituation.ratioN_eq_one_iff` — `g_i = 1` exactly when the generic value
  of the chosen generator `t_i` is the section `t`.
* `Stacks.Chow.KeyFormulaSituation.tameSymbol_eq_one_of_ratioN_eq_one` — `∂_{B_i}(f_i, 1) = 1`.
* `Stacks.Chow.KeyFormulaSituation.principalDivisorPushforward_tameSymbol_eq_zero_of_ratioN_eq_one`
  — the `i`-th summand of the right hand side vanishes where `g_i = 1`.
* `Stacks.Chow.KeyFormulaSituation.tameSymbolCoeff_eq_finsum_subtype_of_ratio_eq_one` — the right
  hand side of the key formula is carried by the members where neither ratio is `1`.
* `Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_of_ratio_eq_one` —
  the left hand side is rationally equivalent to zero, witnessed inside those members.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-! ### The members along which the second section is the chosen generator -/

omit [IsLocallyNoetherian X] in
/-- `g_i = 1` exactly when the generic value of the chosen generator `t_i` is the section
`t`. -/
theorem ratioN_eq_one_iff (i : ℱ.Index) :
    ℱ.ratioN i = 1 ↔
      toGenericStalk N (ℱ.componentPoint i) (ℱ.localGeneratorN i) = ℱ.sectionN := by
  have := isInvertible_presheaf N
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [h, one_smul] using ℱ.ratioN_smul_localGeneratorN i
  · refine ((ℱ.isStalkBasis_localGeneratorN i).toGenericStalk
      (isTrivializedNear_of_isInvertible N (ℱ.componentPoint i))).injective ?_
    change ℱ.ratioN i • _ = (1 : X.functionField) • _
    rw [one_smul, ℱ.ratioN_smul_localGeneratorN i, h]

/-- `∂_{B_i}(f_i, 1) = 1`: the tame symbol is trivial in its second argument (Stacks 0EAI). -/
theorem tameSymbol_eq_one_of_ratioN_eq_one {i : ℱ.Index} (h : ℱ.ratioN i = 1) :
    ℱ.tameSymbol i = 1 := by
  have h1 : Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i) = 1 := Units.val_eq_one.mp h
  change tameSymbolAtCoheightOne (ℱ.coheight_componentPoint i)
      (Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i))
      (Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i)) = 1
  rw [h1]
  exact TameSymbol.one_right _ _

/-! ### The carrier of the rational equivalence, cut down on both sides -/

section Cycles

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The tame symbol of the cycle-level data is trivial where `g_i = 1`. -/
theorem toKeyFormulaData_tameSymbol_eq_one_of_ratioN_eq_one {i : ℱ.Index}
    (h : ℱ.ratioN i = 1) : (ℱ.toKeyFormulaData C p).tameSymbol i = 1 := by
  rw [ℱ.toKeyFormulaData_tameSymbol C p i, ℱ.tameSymbol_eq_one_of_ratioN_eq_one h, map_one]
  rfl

/-- The `i`-th summand of the right hand side of the key formula vanishes where `g_i = 1`. -/
theorem principalDivisorPushforward_tameSymbol_eq_zero_of_ratioN_eq_one {i : ℱ.Index}
    (h : ℱ.ratioN i = 1) :
    principalDivisorPushforward C p ((ℱ.toKeyFormulaData C p).component i)
        ((ℱ.toKeyFormulaData C p).isIntegral_component i)
        ((ℱ.toKeyFormulaData C p).tameSymbol i) = 0 := by
  rw [ℱ.toKeyFormulaData_tameSymbol_eq_one_of_ratioN_eq_one C p h]
  exact principalDivisorPushforward_one C p _ _

/-- The right hand side of the key formula is the locally finite sum over the members satisfying
`P`, provided every member outside `P` has `f_i = 1` or `g_i = 1`. -/
theorem tameSymbolCoeff_eq_finsum_subtype_of_ratio_eq_one (P : ℱ.Index → Prop)
    (hP : ∀ i, ¬ P i → ℱ.ratioL i = 1 ∨ ℱ.ratioN i = 1) (x : X) :
    (ℱ.toKeyFormulaData C p).tameSymbolCoeff C p x =
      ∑ᶠ j : {i : ℱ.Index // P i},
        principalDivisorPushforward C p ((ℱ.toKeyFormulaData C p).component j.1)
          ((ℱ.toKeyFormulaData C p).isIntegral_component j.1)
          ((ℱ.toKeyFormulaData C p).tameSymbol j.1) x := by
  refine finsum_eq_finsum_subtype _ fun i hi ↦ ?_
  rw [(hP i hi).elim (ℱ.principalDivisorPushforward_tameSymbol_eq_zero_of_ratioL_eq_one C p)
    (ℱ.principalDivisorPushforward_tameSymbol_eq_zero_of_ratioN_eq_one C p)]
  rfl

/-- If every member outside `P` has `f_i = 1` or `g_i = 1`, the left hand side of the key formula
is rationally equivalent to zero within the union of the supports of the members satisfying
`P`. -/
theorem isRationallyEquivalentToZeroWithin_leftCoeff_of_ratio_eq_one {k : ℤ}
    (P : ℱ.Index → Prop)
    (hP : ∀ i, ¬ P i → ℱ.ratioL i = 1 ∨ ℱ.ratioN i = 1)
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C (((ℱ.toKeyFormulaData C p).component i).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C p k)
    (hα : ∀ x : X, α.1 x = (ℱ.toKeyFormulaData C p).leftCoeff C p x) :
    IsRationallyEquivalentToZeroWithin C p k α
      (⋃ j : {i : ℱ.Index // P i},
        (((ℱ.toKeyFormulaData C p).component j.1).support : Set X)) := by
  have hlocal : LocallyFinite fun j : {i : ℱ.Index // P i} ↦
      (((ℱ.toKeyFormulaData C p).component j.1).support : Set X) :=
    (ℱ.toKeyFormulaData C p).locallyFinite_support_component.comp_injective
      Subtype.val_injective
  refine ⟨{i : ℱ.Index // P i}, fun j ↦ (ℱ.toKeyFormulaData C p).component j.1,
    fun j ↦ (ℱ.toKeyFormulaData C p).isIntegral_component j.1, fun j ↦ hdim j.1, hlocal,
    fun j ↦ Set.subset_iUnion_of_subset j subset_rfl,
    fun j ↦ (ℱ.toKeyFormulaData C p).tameSymbol j.1, fun x ↦ ?_⟩
  rw [hα x, ((ℱ.toKeyFormulaData C p).keyFormula_iff_forall C p).1
    (ℱ.keyFormula_toKeyFormulaData C p) x]
  exact ℱ.tameSymbolCoeff_eq_finsum_subtype_of_ratio_eq_one C p P hP x

end Cycles

end KeyFormulaSituation

end Stacks.Chow

end
