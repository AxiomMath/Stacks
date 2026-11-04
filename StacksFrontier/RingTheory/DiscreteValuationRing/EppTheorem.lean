module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectCoreReduction
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseLayer

/-!
# Epp's theorem

This file assembles the complete perfect-core reduction and the two completion-descent routes into
the unconditional provider for Tag 09F9.  The theorem is first proved with all four rings and
fields in one universe; `eppTheorem_of_monomorphic` supplies the independent-universe form used by
downstream statements.
-/

@[expose] public section

namespace Stacks.EppTheorem

open IsLocalRing IsDiscreteValuationRing

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Epp's theorem when all input types lie in one universe. -/
@[stacks 09F9]
theorem exists_finite_extension_isWeakSolution
    (A B K L : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    (hEpp : ∀ p : ℕ, p.Prime → CharP (ResidueField A) p →
      ∀ [ExpChar (ResidueField B) p], EppCondition A B p) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁,
        D.IsWeakSolution := by
  classical
  by_cases hchar : ringChar (ResidueField A) = 0
  · obtain ⟨K₁, _, _, _, _, _, _, D, hD⟩ :=
      exists_finite_extension_isWeakSolution_of_tame_or_charZero_of_isDVR
        A B K L (Or.inl hchar)
    exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, D, hD⟩
  · let p := ringChar (ResidueField A)
    have hp : p.Prime :=
      (CharP.char_is_prime_or_zero (ResidueField A) p).resolve_right hchar
    let : Fact p.Prime := ⟨hp⟩
    let : CharP (ResidueField A) p := ringChar.charP _
    let : CharP (ResidueField B) p := CharP.of_ringHom_of_ne_zero
      (algebraMap (ResidueField A) (ResidueField B)) p hp.ne_zero
    have hepp : EppCondition A B p := hEpp p hp inferInstance
    let := algebraAdicCompletion A B
    let := isExtension_adicCompletionMap A B
    let := algebraAdicCompletionFractionFieldMap A B
    let := isScalarTower_adicCompletionFractionFieldMap A B
    let := isScalarTower_adicCompletion A B
    let := isScalarTower_algebraMap_adicCompletion A B
    let : IsLocalHom
        (algebraMap A (AdicCompletion (maximalIdeal B) B)) := by
      rw [IsScalarTower.algebraMap_eq A B (AdicCompletion (maximalIdeal B) B)]
      infer_instance
    let := charP_residueField_adicCompletion A p
    let := expChar_residueField_adicCompletion B p
    have heppc : EppCondition
        (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) p :=
      EppCondition.of_residueField_surjective
        (A := A) (A' := AdicCompletion (maximalIdeal A) A)
        (B := B) (B' := AdicCompletion (maximalIdeal B) B)
        (AdicCompletion.residueField_map_bijective B).surjective hepp
    by_cases hpA : (p : A) = 0
    · -- Equal characteristic: retain condition (b), then use the Kummer completion descent.
      let := algebraAdicCompletionFractionField A K
      let := isScalarTower_adicCompletionFractionField A K
      obtain ⟨π, hπprime⟩ := exists_prime A
      have hπ : Irreducible π := hπprime.irreducible
      let πc : AdicCompletion (maximalIdeal A) A :=
        algebraMap A (AdicCompletion (maximalIdeal A) A) π
      have hπc : Irreducible πc := irreducible_algebraMap_adicCompletion A hπ
      have hpAc : (p : AdicCompletion (maximalIdeal A) A) = 0 := by
        simpa only [map_natCast, map_zero] using
          congrArg (algebraMap A (AdicCompletion (maximalIdeal A) A)) hpA
      obtain ⟨M, _, _, _, _, _, D, hD, n, ρ, hρpow, hρmin, hρsep⟩ :=
        exists_finite_extension_isWeakSolution_of_complete_equalCharacteristic_proved
          p (AdicCompletion (maximalIdeal A) A)
            (AdicCompletion (maximalIdeal B) B)
            (AdicCompletionFractionField A) (AdicCompletionFractionField B)
            hpAc πc hπc heppc
      have hρpow' : ρ ^ p ^ n =
          algebraMap (AdicCompletionFractionField A) M
            (algebraMap A (AdicCompletionFractionField A) π) := by
        simpa only [πc, ← IsScalarTower.algebraMap_apply A
          (AdicCompletion (maximalIdeal A) A) (AdicCompletionFractionField A)] using hρpow
      have hρmin' : minpoly (AdicCompletionFractionField A) ρ =
          Polynomial.X ^ p ^ n -
            Polynomial.C (algebraMap A (AdicCompletionFractionField A) π) := by
        simpa only [πc, ← IsScalarTower.algebraMap_apply A
          (AdicCompletion (maximalIdeal A) A) (AdicCompletionFractionField A)] using hρmin
      obtain ⟨K₁, _, _, _, _, _, ⟨e⟩⟩ :=
        exists_finite_extension_nonempty_tensorProduct_algEquiv_of_conditionB
          A K M p π hπ (fun _ ↦ ⟨n, ρ, hρpow', hρmin', hρsep⟩)
      exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, canonicalBaseChange A B K L K₁,
        isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv A B K L K₁ M
          ⟨D, hD⟩ e⟩
    · -- Mixed characteristic: the complete solution is separable, so ordinary descent applies.
      obtain ⟨K₁, _, _, _, _, _, _, D, hD⟩ :=
        exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion.{u, u, u, u,
          u, u, u} A B K L (by
          have hpAc : (p : AdicCompletion (maximalIdeal A) A) ≠ 0 := fun h ↦
            hpA (AdicCompletion.of_injective (maximalIdeal A) A h)
          obtain ⟨M, _, _, _, _, _, D, hD⟩ :=
            exists_finite_extension_isWeakSolution_of_complete_mixedCharacteristic_proved
              p (AdicCompletion (maximalIdeal A) A)
                (AdicCompletion (maximalIdeal B) B)
                (AdicCompletionFractionField A) (AdicCompletionFractionField B)
                hpAc heppc
          have : CharZero A := charZero_of_ne_zero_of_charP_residueField A p hpA
          let := charZero_adicCompletionFractionField A
          exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
            inferInstance, inferInstance, D, hD⟩)
      exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, D, hD⟩

/-- The monomorphic provider consumed by the universe layer. -/
theorem eppTheorem_monomorphic : Stacks.EliminateRamification.EppTheorem.{u, u, u, u} :=
  exists_finite_extension_isWeakSolution

end Stacks.EppTheorem

end
