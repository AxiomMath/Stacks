module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.NumberTheory.BombieriStepanov.TwistedIdentities

/-!
# Extending the constants of a function field

Let `E` be algebraically closed in a field `L` (every element of `L` integral over `E` lies in
`E`). An irreducible monic polynomial over `E` stays irreducible over `L`: a monic factor over
`L` of a monic polynomial over `E` has coefficients integral over `E`
(`integralClosure.mem_lifts_of_monic_of_dvd_map`), hence in `E`, so it is a factor over `E`.
Consequently `L ⊗_E E₁ = L[X] / (g)` is a field for a finite extension `E₁ = E[X]/(g)`, the
constant field extension of `L` by `E₁`.

## Main results

* `Stacks.BombieriStepanov.irreducible_map_of_forall_isIntegral`
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.BombieriStepanov

/-- **Irreducible polynomials stay irreducible over a field in which the constants are
algebraically closed.** -/
theorem irreducible_map_of_forall_isIntegral {E L : Type*} [Field E] [Field L] [Algebra E L]
    (hE : ∀ c : L, IsIntegral E c → c ∈ (algebraMap E L).range) {g : E[X]} (hg : g.Monic)
    (hirr : Irreducible g) : Irreducible (g.map (algebraMap E L)) := by
  rw [(hg.map _).irreducible_iff_natDegree]
  refine ⟨fun h => hirr.not_isUnit ?_, fun f h hf hh hfh => ?_⟩
  · have h1 : g = 1 := Polynomial.map_injective _ (algebraMap E L).injective (by simpa using h)
    rw [h1]
    exact isUnit_one
  -- the factor `f` comes from `E`
  have hdvd : f ∣ g.map (algebraMap E L) := ⟨h, hfh.symm⟩
  have hlift := integralClosure.mem_lifts_of_monic_of_dvd_map L hg hf hdvd
  have hliftE : f ∈ lifts (algebraMap E L) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨c, hc⟩ := hlift n
    exact hE _ (hc ▸ c.2)
  obtain ⟨f₀, hf₀, hdeg, hf₀m⟩ := lifts_and_natDegree_eq_and_monic hliftE hf
  have hdvd₀ : f₀ ∣ g := by
    rw [← map_dvd_map' (algebraMap E L), hf₀]
    exact hdvd
  obtain ⟨h₀, hh₀⟩ := hdvd₀
  rcases hirr.isUnit_or_isUnit hh₀ with hu | hu
  · left
    rw [← hdeg]
    exact natDegree_eq_zero_of_isUnit hu
  · right
    have hdeg₀ : f₀.natDegree = g.natDegree := by
      rw [hh₀, natDegree_mul hf₀m.ne_zero (fun h => by simp [h] at hu),
        natDegree_eq_zero_of_isUnit hu, add_zero]
    have hdegg : (g.map (algebraMap E L)).natDegree = f.natDegree + h.natDegree := by
      rw [← hfh, hf.natDegree_mul hh]
    rw [natDegree_map, ← hdeg, hdeg₀] at hdegg
    omega

/-- In a domain, the solutions of `b ^ q = b` are the constants, when a field of constants has
`q` elements. -/
theorem exists_algebraMap_eq_of_pow_eq {E S : Type*} [Field E] [Fintype E] [CommRing S] [IsDomain S]
    [Algebra E S] (b : S) (hb : b ^ Fintype.card E = b) : ∃ c : E, algebraMap E S c = b := by
  classical
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  set R := {z : S | z ^ Fintype.card E = z}
  have hsub : Set.range (algebraMap E S) ⊆ R := by
    rintro _ ⟨c, rfl⟩
    simp [R, ← map_pow, FiniteField.pow_card]
  -- at most `#E` solutions in a domain
  have hfin : R.Finite ∧ R.ncard ≤ Fintype.card E := by
    have h0 : (X ^ Fintype.card E - X : S[X]) ≠ 0 := by
      intro h
      have := congrArg (fun P : S[X] => P.coeff 1) h
      have hq1 : (1 : ℕ) ≠ Fintype.card E := hq.ne
      simp [coeff_X, coeff_X_pow, hq1] at this
    have hset : R = ((X ^ Fintype.card E - X : S[X]).roots.toFinset : Set S) := by
      ext z
      simp [R, Multiset.mem_toFinset, mem_roots h0, sub_eq_zero]
    rw [hset]
    refine ⟨Finset.finite_toSet _, ?_⟩
    rw [Set.ncard_coe_finset]
    refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), natDegree_X_pow]
  have heq : Set.range (algebraMap E S) = R := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin.1
    rw [Set.ncard_range_of_injective (algebraMap E S).injective, Nat.card_eq_fintype_card]
    exact hfin.2
  have : b ∈ R := hb
  rw [← heq] at this
  exact this

section Uniqueness

variable {B B₁ E₁ Ω : Type*} [CommRing B] [CommRing B₁] [IsDomain B₁] [Algebra B B₁] [Field E₁]
  [Fintype E₁] [Algebra E₁ B₁] [Field Ω] (ι₁ : E₁ →+* Ω)
  (Γ : Type*) [Group Γ] [Finite Γ] [MulSemiringAction Γ B₁] [SMulCommClass Γ B B₁]
  [Algebra.IsInvariant B B₁ Γ]

/-- **Lifts over a constant extension are unique.** If the group `Γ` of `B₁` over `B` acts
faithfully on the constants `E₁`, two points of `B₁` over `ι₁` with the same restriction to `B`
and finite residue ring are equal. -/
theorem eq_of_comp_algebraMap_eq
    (hfaith : ∀ g : Γ, (∀ c : E₁, g • algebraMap E₁ B₁ c = algebraMap E₁ B₁ c) → g = 1)
    (ψ ψ' : PointsOver B₁ ι₁) (h : ψ.1.comp (algebraMap B B₁) = ψ'.1.comp (algebraMap B B₁))
    [Finite (B₁ ⧸ RingHom.ker ψ.1)] : ψ = ψ' := by
  let : Algebra B Ω := (ψ.1.comp (algebraMap B B₁)).toAlgebra
  let a : B₁ →ₐ[B] Ω := { ψ.1 with commutes' := fun _ => rfl }
  let a' : B₁ →ₐ[B] Ω :=
    { ψ'.1 with commutes' := fun r => (congrArg (fun f : B →+* Ω => f r) h).symm }
  have : Finite (B₁ ⧸ RingHom.ker a) := ‹Finite (B₁ ⧸ RingHom.ker ψ.1)›
  obtain ⟨g, hg⟩ := exists_smul_eq_of_algHom Γ a a'
  have hgE : g ∈ constantFixing B₁ E₁ Γ :=
    mem_constantFixing_of_comp (φ := ψ) (φ' := ψ') (qE := Fintype.card E₁)
      FiniteField.pow_card (fun b hb => exists_algebraMap_eq_of_pow_eq b hb) hg
  have hg1 := hfaith g hgE
  subst hg1
  exact Subtype.ext (RingHom.ext fun b => by
    have := (hg b).symm
    rw [one_smul] at this
    exact this)

end Uniqueness

end Stacks.BombieriStepanov

end
