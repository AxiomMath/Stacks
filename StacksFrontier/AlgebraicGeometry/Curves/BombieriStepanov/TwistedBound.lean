module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.TwistedModel
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.CurveModel

/-!
# The twisted Bombieri–Stepanov bound for a Dedekind ring with a rational point

Let `A` be a Dedekind domain of finite type over a finite field `F`, whose fraction field `L`
has transcendence degree one over `F`, and let `A` have a maximal ideal `P₀` with residue field
`F`. For a ring automorphism `σ` of `A` of finite order fixing `F`, the `σ`-twisted points
`φ : A → Ω` (`φ(σ a) = φ(a) ^ Q`) number at most `Q + (2γ + 1) √Q`, for `Q` an even power of the
characteristic beyond a bound.

This is `Stacks.BombieriStepanov.ncard_twisted_le` on the proper model of `L`
(`Stacks.BombieriStepanov.exists_curve_model`), the place of `P₀` being rational.

## Main results

* `Stacks.BombieriStepanov.exists_ncard_twisted_le`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

/-- **The twisted Bombieri–Stepanov bound for a Dedekind ring with a rational point.** -/
theorem exists_ncard_twisted_le {F : Type u} [Field F] [Finite F] (pr : ℕ) [Fact pr.Prime]
    [CharP F pr] {L : Type u} [Field L] [Algebra F L] [Algebra.EssFiniteType F L]
    (htr : Algebra.trdeg F L = 1) {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra F A]
    [Algebra.FiniteType F A] [Algebra A L] [IsScalarTower F A L] [IsFractionRing A L]
    (P₀ : Ideal A) [P₀.IsMaximal] (hP₀ne : P₀ ≠ ⊥)
    (hP₀ : ∀ a : A, ∃ c : F, a - algebraMap F A c ∈ P₀)
    (σ : A ≃+* A) (hσF : ∀ c, σ (algebraMap F A c) = algebraMap F A c) {N : ℕ} (hN0 : N ≠ 0)
    (hN : ∀ a, (⇑σ)^[N] a = a) {Ω : Type*} [Field Ω] (ι : F →+* Ω) :
    ∃ γ : ℕ, ∀ e : ℕ, γ ^ 2 + 3 * γ + 1 < pr ^ e →
      {φ : PointsOver A ι | ∀ a, φ.1 (σ a) = φ.1 a ^ (pr ^ e * pr ^ e)}.Finite ∧
      {φ : PointsOver A ι | ∀ a, φ.1 (σ a) = φ.1 a ^ (pr ^ e * pr ^ e)}.ncard ≤
        pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  have := Fintype.ofFinite F
  obtain ⟨M, p, _, _, _, _, hdvr, eL, heL⟩ := exists_curve_model F L htr
  let : Algebra A M.functionField := (eL.toRingHom.comp (algebraMap A L)).toAlgebra
  have : IsFractionRing A M.functionField :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors A)
      { eL with commutes' := fun a => rfl }
  have hFA : ∀ c : F, algebraMap A M.functionField (algebraMap F A c) =
      (fieldToStalk p (genericPoint M)).hom c := by
    intro c
    change eL (algebraMap A L (algebraMap F A c)) = _
    rw [← IsScalarTower.algebraMap_apply, heL]
  have hF : ∀ c : F, ∃ a : A, algebraMap A M.functionField a =
      (fieldToStalk p (genericPoint M)).hom c := fun c => ⟨_, hFA c⟩
  obtain ⟨x₀, hx₀⟩ := exists_curvePlace_eq_localization p hdvr hF P₀ hP₀ne
  have hsurj : Function.Surjective fun c : F =>
      IsLocalRing.residue (M.presheaf.stalk x₀.1) ((fieldToStalk p x₀.1).hom c) := by
    intro z
    obtain ⟨a, rfl⟩ := surjective_residue_comp_toStalk hx₀ z
    obtain ⟨c, hc⟩ := hP₀ a
    refine ⟨c, ?_⟩
    have hker := ker_residue_comp_toStalk hx₀
    have h1 : a - algebraMap F A c ∈ RingHom.ker ((IsLocalRing.residue (M.presheaf.stalk x₀.1)).comp
        (toStalk x₀.1 (forall_exists_algebraMap_eq hx₀))) := by
      rw [hker]
      exact hc
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
    rw [h1, RingHom.comp_apply, toStalk_algebraMap p hFA]
  exact ncard_twisted_le p hdvr hFA pr x₀ hsurj σ hσF hN0 hN ι

end Stacks.BombieriStepanov

end
