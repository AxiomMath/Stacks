module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingExtensionModel

/-!
# The integers of a finite extension `E''` of `E` as a subring, with an integral model of `τ`

Packages the integers `O = integralClosure ℤ_ℓ E''` of a finite extension `E''` of a finite
extension `E` of `ℚ_ℓ`, viewed as a subring of `E''`, with what the level dichotomy in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) needs of them: `O` is a valuation ring with
fraction field `E''`, `ℓ` is a nonzero nonunit of `O` and every nonzero element of `O` divides a
power of `ℓ`, the levels `O / ℓᴺ⁺¹` are finite, and a representation `τ : G → GL_m(E)` of a compact
group with continuous restriction of scalars has a model `τ_O` over `O`, conjugate to `τ` in
`GL_m(E'')`, whose reductions modulo every `ℓⁿ` have open kernels
(`Stacks.EtaleCohomology.exists_padicIntegerSubring_model`).

## Main results

* `Stacks.EtaleCohomology.exists_padicIntegerSubring_model`.
-/

@[expose] public noncomputable section

open Module Matrix

namespace Stacks.EtaleCohomology

attribute [local instance] padicIntAlgebraOfRat

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}

/-- **The integers of a finite extension `E''` of `E`, as a subring of `E''`, with an integral
model of `τ ⊗_E E''` whose reductions modulo every `ℓⁿ` have open kernels.** -/
theorem exists_padicIntegerSubring_model (b : Basis (Fin d) ℚ_[ℓ] E)
    (E'' : IntermediateField E (AlgebraicClosure E)) [FiniteDimensional E E''] {m : ℕ}
    (τ : G →* GL (Fin m) E) (hτ : Continuous (restrictScalarsRep b τ)) :
    ∃ (O : Subring E'') (_ : ValuationRing O) (_ : IsFractionRing O E''),
      ((ℓ : O) ≠ 0) ∧ ¬IsUnit (ℓ : O) ∧ (∀ o : O, o ≠ 0 → ∃ c : ℕ, o ∣ (ℓ : O) ^ c) ∧
      (∀ n : ℕ, Finite (O ⧸ Ideal.span {(ℓ : O) ^ n})) ∧
      ∃ (τO : G →* GL (Fin m) O) (T : GL (Fin m) E''),
        (∀ g, (τO g).val.map (algebraMap O E'') =
          (T⁻¹ : GL (Fin m) E'').val * (τ g).val.map (algebraMap E E'') * T.val) ∧
        ∀ n : ℕ, IsOpen (((GeneralLinearGroup.map
          (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ n}))).comp τO).ker : Set G) := by
  obtain ⟨τO, T, hT, hker⟩ := exists_padicIntegerRing_model b E'' τ hτ
  exact ⟨(integralClosure ℤ_[ℓ] E'').toSubring,
    inferInstanceAs (ValuationRing (integralClosure ℤ_[ℓ] E'')),
    inferInstanceAs (IsFractionRing (integralClosure ℤ_[ℓ] E'') E''),
    natCast_ne_zero_padicIntegerRing ℓ, not_isUnit_natCast_padicIntegerRing ℓ,
    fun o ho => exists_dvd_natCast_pow_padicIntegerRing ℓ ho,
    fun n => inferInstanceAs (Finite (integralClosure ℤ_[ℓ] E'' ⧸
      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ n})),
    τO, T, hT, hker⟩

end Stacks.EtaleCohomology

end
