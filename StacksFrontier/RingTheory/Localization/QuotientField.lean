module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import StacksCore.Tactic.StacksAttribute

/-!
# The quotient field of a domain

For a domain `A`, the fraction field `FractionRing A` is a field into which `A` embeds, every
element of it is a fraction `a / b` with `b ≠ 0`, two fractions `a / b` and `a' / b'` agree
exactly when `a * b' = b * a'`, and every injective ring map `φ : A →+* K` into a field factors
uniquely through it, the factorization sending `a / b` to `φ a * (φ b)⁻¹` (Stacks tag 09FJ).
-/

@[expose] public section

universe u v

/-- **Stacks 09FJ** (quotient fields). For a domain `A`, the fraction field `F = FractionRing A`
is a field, the map `A → F` is injective, every element of `F` is a fraction `a / b` with
`b ≠ 0`, and `a / b = a' / b'` if and only if `a * b' = b * a'` (for `b, b' ≠ 0`). Moreover,
for every injective ring map `φ : A →+* K` into a field `K` there is a unique ring map
`ψ : F →+* K` with `ψ ∘ (A → F) = φ`, and any such `ψ` sends `a / b` to `φ a * (φ b)⁻¹`. -/
@[stacks 09FJ "the fraction field FractionRing A, the injective map A → FractionRing A, the
description of its elements as fractions a / b with b ≠ 0 up to cross-multiplication, and the
universal property for injective ring maps into fields with ψ(a / b) = φ(a) φ(b)⁻¹"]
theorem fractionRing_isField_and_lift_unique (A : Type u) [CommRing A] [IsDomain A] :
    IsField (FractionRing A) ∧
    Function.Injective (algebraMap A (FractionRing A)) ∧
    (∀ x : FractionRing A, ∃ a b : A, b ≠ 0 ∧
      x = algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) ∧
    (∀ a b a' b' : A, b ≠ 0 → b' ≠ 0 →
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b =
          algebraMap A (FractionRing A) a' / algebraMap A (FractionRing A) b' ↔
        a * b' = b * a')) ∧
    ∀ (K : Type v) [Field K] (φ : A →+* K), Function.Injective φ →
      (∃! ψ : FractionRing A →+* K, ψ.comp (algebraMap A (FractionRing A)) = φ) ∧
      ∀ ψ : FractionRing A →+* K, ψ.comp (algebraMap A (FractionRing A)) = φ →
        ∀ a b : A, ψ (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) =
          φ a * (φ b)⁻¹ := by
  have hinj := IsFractionRing.injective A (FractionRing A)
  refine ⟨Field.toIsField _, hinj, fun x => ?_, fun a b a' b' hb hb' => ?_,
    fun K _ φ hφ => ?_⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, rfl⟩
  · rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).2 hb) ((map_ne_zero_iff _ hinj).2 hb'),
      ← map_mul, ← map_mul, hinj.eq_iff, mul_comm b a']
  have hlift : (IsFractionRing.lift hφ : FractionRing A →+* K).comp
      (algebraMap A (FractionRing A)) = φ := RingHom.ext (IsFractionRing.lift_algebraMap hφ)
  refine ⟨⟨IsFractionRing.lift hφ, hlift, fun ψ hψ => ?_⟩, fun ψ hψ a b => ?_⟩
  · exact IsLocalization.ringHom_ext (nonZeroDivisors A) (hψ.trans hlift.symm)
  · rw [map_div₀, ← RingHom.comp_apply, ← RingHom.comp_apply, hψ, div_eq_mul_inv]
