module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PoleOrders
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Residue
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme

/-!
# The Bombieri–Stepanov bound on a proper curve over a finite field

Let `X` be a proper curve over a finite field `k` with `q` elements, with a discrete valuation
ring as local ring at every closed point. Let `P₀` be a closed point with residue field `k`. Then
there is a constant `γ`, depending on `X` and `P₀` only, with the following property. Let
`q ^ ν = r²` with `r` a power of the characteristic and `r > γ² + 3γ + 1`. Then every finite set
`S` of closed points other than `P₀`, of degrees dividing `ν`, satisfies

`∑_{x ∈ S} deg x + 1 ≤ q ^ ν + (2γ + 1) q ^ {ν/2}`.

Taking for `S` all closed points other than `P₀` of degree dividing `ν`, the left side is the
number of points of `X` with values in the extension of degree `ν` of `k`.

The constant `γ` is `e²`, with `e` and `e + 1` the pole orders at `P₀` of two functions regular
away from `P₀` (`Stacks.BombieriStepanov.exists_consecutive_poleOrders`). The places of `X` satisfy
the degree formula (`Stacks.BombieriStepanov.hasDegreeFormula_curveVal`). At a place of degree
dividing `ν` the residue field has `q ^ deg x` elements, so `c ^ {q^ν} = c` there, and every
regular function is congruent to its `q^ν`-th power (`one_le_schemeVal_sub_pow`).

## Main results

* `Stacks.BombieriStepanov.pow_card_pow_residueField`: `c ^ {q ^ ν} = c` in the residue field of
  a point of degree dividing `ν`.
* `Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le`: the Bombieri–Stepanov bound.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- In the residue field of a point whose degree over the finite field `k` divides `ν`, every
element satisfies `c ^ {q ^ ν} = c`. -/
theorem pow_card_pow_residueField [Fintype k] (x : X) {ν : ℕ} (hν : p.residueDegree x ∣ ν)
    (c : IsLocalRing.ResidueField (X.presheaf.stalk x)) : c ^ (Fintype.card k ^ ν) = c := by
  rcases Nat.eq_zero_or_pos (p.residueDegree x) with h0 | hpos
  · rw [h0, zero_dvd_iff] at hν
    rw [hν, pow_zero, pow_one]
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom).toAlgebra
  have hdeg := Stacks.Chow.residueDegree_eq_finrank_residueField k p x
  have : Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Module.finite_of_finrank_pos (by rw [← hdeg]; exact hpos)
  let : Fintype (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Module.fintypeOfFintype (Module.finBasis k (IsLocalRing.ResidueField (X.presheaf.stalk x)))
  have hcard := Module.card_eq_pow_finrank (K := k)
    (V := IsLocalRing.ResidueField (X.presheaf.stalk x))
  obtain ⟨m, rfl⟩ := hν
  rw [pow_mul, hdeg, ← hcard]
  exact FiniteField.pow_card_pow m c

variable [IsIntegral X] [IsLocallyNoetherian X]
  (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
  [IsProper p] [IsCurve k p]

include hdvr in
/-- **The Bombieri–Stepanov bound on a proper curve over a finite field.** Let `P₀` be a closed
point of `X` with residue field `k`. There is a constant `γ` such that, whenever
`q ^ ν = r²` with `r = p ^ e` and `r > γ² + 3γ + 1`, every finite set `S` of closed points other
than `P₀` whose degrees divide `ν` has `∑_{x ∈ S} deg x + 1 ≤ q ^ ν + (2γ + 1) r`. -/
theorem exists_sum_curveDeg_add_one_le [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    (P₀ : CurvePlace X) (hcl : IsClosed ({P₀.1} : Set X)) (hP₀ : curveDeg k p P₀ = 1)
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c)) :
    ∃ γ : ℕ, ∀ e ν : ℕ, Fintype.card k ^ ν = pr ^ e * pr ^ e → γ ^ 2 + 3 * γ + 1 < pr ^ e →
      ∀ S : Finset (CurvePlace X), P₀ ∉ S → (∀ P ∈ S, curveDeg k p P ∣ ν) →
        ∑ P ∈ S, curveDeg k p P + 1 ≤ pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  let := functionFieldAlgebra p
  have : CharP X.functionField pr :=
    charP_of_injective_algebraMap (algebraMap k X.functionField).injective pr
  have hD := hasDegreeFormula_curveVal hdvr k p
  have hres : IsResidueRational (k := k) (curveVal hdvr P₀) := by
    have := hdvr P₀.1 P₀.2
    exact isResidueRational_schemeVal p P₀.2 hsurj
  obtain ⟨e₀, a, b, ha, ha0, hae, hb, hb0, hbe⟩ :=
    exists_consecutive_poleOrders hdvr k p P₀ hP₀ hcl
  have hRR := pow_le_natCard_poleSpace hD hP₀ hres e₀ ha ha0 hae hb hb0 hbe
  refine ⟨e₀ * e₀, fun e ν hq hr S hS₀ hSdeg => ?_⟩
  refine sum_deg_add_one_le pr e hD hP₀ hP₀ hres (e₀ * e₀) hRR hr id (fun n y hy => hy) S hS₀
    fun P hP n y hy => ?_
  have := hdvr P.1 P.2
  have hPP₀ : P ≠ P₀ := fun h => hS₀ (h ▸ hP)
  have h := one_le_schemeVal_sub_pow P.2 (pr ^ e * pr ^ e)
    (fun c => by rw [← hq]; exact pow_card_pow_residueField p P.1 (hSdeg P hP) c)
    (hy.2 P hPP₀)
  exact h

end Stacks.BombieriStepanov

end
