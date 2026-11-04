module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.CurveUpperBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.NumberTheory.TraceFormula.RiemannHypothesisBound
public import Mathlib.FieldTheory.Finite.Extension

/-!
# The Bombieri–Stepanov bound for the number of points of a curve

Let `X` be a proper curve over a finite field `k` with `q` elements, with a discrete valuation
ring as local ring at every closed point, and with a closed point of residue field `k`. Then there
is a constant `γ` such that, for every extension `K` of `k` of degree `ν` with
`q ^ ν = r²`, `r` a power of the characteristic, and `r > γ² + 3γ + 1`,

`#X(K) ≤ q ^ ν + (2γ + 1) r`.

Here `#X(K) = ∑_{deg x ∣ ν} deg x` (`Stacks.EtaleCohomology.natCard_fieldValuedPoints`). The sum
over the closed points other than the rational point `P₀` is bounded by
`Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le`.

## Main results

* `Stacks.BombieriStepanov.residueDegree_eq_residueDegree`: the two spellings of the degree of a
  point of a scheme over a field agree.
* `Stacks.BombieriStepanov.exists_natCard_fieldValuedPoints_le`: the bound on `#X(K)`.
* `Stacks.BombieriStepanov.exists_upper_bound_even`: `N m ≤ q^m + C √q^m` for large even `m`.
* `Stacks.BombieriStepanov.norm_eq_sqrt_of_lower_bound`: the Riemann hypothesis from this upper
  bound, a lower bound of the same shape and the pairing `α_i α_j = q`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The degree `[κ(x) : k]` of a point, read through `fieldToResidue`, is the residue degree of
the structure morphism at `x`. -/
theorem residueDegree_eq_residueDegree (x : X) :
    Stacks.EtaleCohomology.residueDegree p x = p.residueDegree x := by
  rw [Stacks.Chow.residueDegree_eq_finrank_residueField k p x]
  rfl

variable [IsIntegral X] [IsLocallyNoetherian X]
  (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
  [IsProper p] [IsCurve k p]

include hdvr in
/-- **The Bombieri–Stepanov bound for the number of points of a curve.** Let `X` be a proper curve
over the finite field `k`, regular at its closed points, with a closed point `P₀` of residue field
`k`. There is a constant `γ` such that for every finite extension `K` of `k` with
`q ^ [K : k] = r²`, `r = p ^ e > γ² + 3γ + 1`, the number of `K`-points satisfies
`#X(K) ≤ q ^ [K : k] + (2γ + 1) r`. -/
theorem exists_natCard_fieldValuedPoints_le [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    (P₀ : CurvePlace X) (hcl : IsClosed ({P₀.1} : Set X)) (hP₀ : curveDeg k p P₀ = 1)
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c)) :
    ∃ γ : ℕ, ∀ (e : ℕ) (K : Type u) [Field K] [Algebra k K] [Finite K],
      Fintype.card k ^ Module.finrank k K = pr ^ e * pr ^ e → γ ^ 2 + 3 * γ + 1 < pr ^ e →
        Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) ≤
          pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  classical
  obtain ⟨γ, H⟩ := exists_sum_curveDeg_add_one_le p hdvr pr P₀ hcl hP₀ hsurj
  refine ⟨γ, fun e K _ _ _ hq hr => ?_⟩
  rw [Stacks.EtaleCohomology.natCard_fieldValuedPoints p K]
  set ν := Module.finrank k K
  set T := (Stacks.EtaleCohomology.closedPointsDegreeLE p ν).filter
    (fun x => Stacks.EtaleCohomology.residueDegree p x.1 ∣ ν)
  let φ : closedPoints X ↪ CurvePlace X :=
    ⟨fun x => ⟨x.1, coheight_eq_one_of_isCurve k p x.2⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun P : CurvePlace X => P.1) h)⟩
  have hsum : ∑ x ∈ T, Stacks.EtaleCohomology.residueDegree p x.1 =
      ∑ P ∈ T.map φ, curveDeg k p P := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun x _ => residueDegree_eq_residueDegree p x.1
  rw [hsum]
  set S := (T.map φ).erase P₀ with hS
  have hSdeg : ∀ P ∈ S, curveDeg k p P ∣ ν := by
    intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 (Finset.mem_of_mem_erase hP)
    have h := (Finset.mem_filter.1 hx).2
    rwa [residueDegree_eq_residueDegree] at h
  have hsplit : ∑ P ∈ T.map φ, curveDeg k p P ≤ ∑ P ∈ S, curveDeg k p P + 1 := by
    by_cases hmem : P₀ ∈ T.map φ
    · rw [← Finset.add_sum_erase _ _ hmem, hP₀, add_comm]
    · rw [hS, Finset.erase_eq_of_notMem hmem]
      exact Nat.le_succ _
  exact hsplit.trans (H e ν hq hr S (Finset.notMem_erase P₀ _) hSdeg)

include hdvr in
/-- **The upper bound in the form the Riemann hypothesis consumes.** Let `N m` be the number of
points of `X` over the extensions of degree `m` of `k`. Under the hypotheses of
`exists_natCard_fieldValuedPoints_le`, there are `C` and `m₀` with `N m ≤ q^m + C · √q^m` for
every even `m ≥ m₀`. -/
theorem exists_upper_bound_even [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    (P₀ : CurvePlace X) (hcl : IsClosed ({P₀.1} : Set X)) (hP₀ : curveDeg k p P₀ = 1)
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c))
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m) :
    ∃ (C : ℝ) (m₀ : ℕ), ∀ m : ℕ, m₀ ≤ m → 2 ∣ m →
      (N m : ℝ) ≤ (Fintype.card k : ℝ) ^ m + C * Real.sqrt (Fintype.card k) ^ m := by
  obtain ⟨γ, H⟩ := exists_natCard_fieldValuedPoints_le p hdvr pr P₀ hcl hP₀ hsurj
  obtain ⟨a, -, ha⟩ := FiniteField.card k pr
  refine ⟨2 * γ + 1, 2 * (γ ^ 2 + 3 * γ + 1) + 1, fun m hm hdm => ?_⟩
  obtain ⟨t, rfl⟩ := hdm
  have hm0 : 2 * t ≠ 0 := by omega
  have : NeZero (2 * t) := ⟨hm0⟩
  set K := ULift.{u} (FiniteField.Extension k pr (2 * t))
  have hfin : Module.finrank k K = 2 * t := by
    rw [finrank_ulift]
    exact FiniteField.finrank_extension k pr (2 * t)
  have : Finite K := Finite.of_equiv _ Equiv.ulift.symm
  set e := (a : ℕ) * t with he
  have hq' : Fintype.card k ^ (2 * t) = pr ^ e * pr ^ e := by
    rw [ha, ← pow_mul, ← pow_add, he]
    ring_nf
  have hq : Fintype.card k ^ Module.finrank k K = pr ^ e * pr ^ e := by rwa [hfin]
  have hpr : 2 ≤ pr := (Fact.out : pr.Prime).two_le
  have ht : γ ^ 2 + 3 * γ + 1 < t := by omega
  have hte : t ≤ e := Nat.le_mul_of_pos_left t a.pos
  have hbound := H e K hq (ht.trans_le (hte.trans (Nat.lt_pow_self (by omega)).le))
  rw [hNcard (2 * t) hm0 K hfin] at hbound
  -- `√q ^ (2t) = p ^ e`
  have hsq : Real.sqrt (Fintype.card k) ^ (2 * t) = (pr : ℝ) ^ e := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), ha, he]
    push_cast
    rw [← pow_mul]
  rw [hsq]
  rw [← hq'] at hbound
  exact_mod_cast hbound

include hdvr in
/-- **The Riemann hypothesis for a proper curve with a rational point, from the lower bound and
the pairing.** Let `X` be a proper curve over `𝔽_q`, regular at its closed points, with a closed
point of residue field `k`. Let `N m = #X(k_m) = 1 - ∑_i α_i^m + q^m` (Tag 03V8, part (3)).
Assume a lower bound `q^m ≤ N m + C · √q^m` for large `m` in an arithmetic progression `d ℕ`, and
the pairing `α_i α_j = q`. Then `‖α_i‖ = √q`. The upper bound comes from Bombieri–Stepanov,
`exists_upper_bound_even`. -/
theorem norm_eq_sqrt_of_lower_bound [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    (P₀ : CurvePlace X) (hcl : IsClosed ({P₀.1} : Set X)) (hP₀ : curveDeg k p P₀ = 1)
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c))
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m)
    {ι : Type*} [Fintype ι] (α : ι → ℂ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (Fintype.card k : ℂ) ^ m)
    (C : ℝ) (m₀ d : ℕ) (hd : d ≠ 0)
    (hlower : ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      (Fintype.card k : ℝ) ^ m ≤ N m + C * Real.sqrt (Fintype.card k) ^ m)
    (hpair : ∀ i, ∃ j, α i * α j = Fintype.card k) (i : ι) :
    ‖α i‖ = Real.sqrt (Fintype.card k) := by
  obtain ⟨C', m₁, hup⟩ := exists_upper_bound_even p hdvr pr P₀ hcl hP₀ hsurj N hNcard
  have hs : ∀ m : ℕ, 0 ≤ Real.sqrt (Fintype.card k) ^ m := fun m => by positivity
  refine Stacks.TraceFormula.norm_eq_sqrt_of_upper_lower α Fintype.card_pos N hN
    (C := max C C') (d := 2 * d) (by omega) (max m₀ m₁) (fun m hm hdm => ?_)
    (fun m hm hdm => ?_) hpair i
  · have := hup m (le_of_max_le_right hm) (dvd_trans (dvd_mul_right 2 d) hdm)
    nlinarith [hs m, le_max_right C C']
  · have := hlower m (le_of_max_le_left hm) (dvd_trans (dvd_mul_left d 2) hdm)
    nlinarith [hs m, le_max_left C C']

end Stacks.BombieriStepanov

end
