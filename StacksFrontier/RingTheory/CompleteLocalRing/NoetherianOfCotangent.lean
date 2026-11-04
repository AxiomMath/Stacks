module

public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Complete local rings with finite cotangent space

Let `(R, 𝔪)` be a complete local ring. If finitely many elements of `𝔪` generate `𝔪` modulo
`𝔪²`, then they generate `𝔪`: this is Stacks 031D applied to the module `𝔪`, which is
`𝔪`-adically separated and whose reduction `𝔪/𝔪²` is finite over `R/𝔪`. A complete local ring
with finitely generated maximal ideal and residue field a quotient of `ℤ_[ℓ]` is then a quotient
of a power series ring over `ℤ_[ℓ]` (Stacks 0315), hence Noetherian.

## Main results

* `IsLocalRing.fg_maximalIdeal_of_le_span_sup_sq`.
* `IsLocalRing.isNoetherianRing_of_fg_maximalIdeal`.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a complete local ring, a finite subset of the maximal ideal generating it modulo its
square generates a finitely generated ideal: the maximal ideal is finitely generated. -/
theorem fg_maximalIdeal_of_le_span_sup_sq [IsAdicComplete (maximalIdeal R) R] (T : Set R)
    (hT : T.Finite) (hTm : T ⊆ maximalIdeal R)
    (h : maximalIdeal R ≤ Ideal.span T ⊔ maximalIdeal R ^ 2) : (maximalIdeal R).FG := by
  set m := maximalIdeal R
  have hfinM : Module.Finite R m := by
    refine Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top m ?_ ?_
    · refine eq_bot_iff.2 fun x hx => ?_
      rw [Submodule.mem_bot]
      have hx' : ∀ k, (x : R) ∈ m ^ k := fun k => by
        have h1 : x ∈ m ^ k • (⊤ : Submodule R m) := (Submodule.mem_iInf _).1 hx k
        have h2 : (x : R) ∈ m ^ k • m := (Submodule.mem_smul_top_iff (m ^ k) m x).1 h1
        exact Ideal.mul_le_left (I := m ^ k) (J := m) (Ideal.smul_eq_mul (m ^ k) m ▸ h2)
      have : (x : R) = 0 := IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := m)) (x : R)
        fun k => by
          rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
          exact hx' k
      exact Subtype.ext this
    · let T' : Set m := Subtype.val ⁻¹' T
      have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
      have hspan : Submodule.span R T' ⊔ m • (⊤ : Submodule R m) = ⊤ := by
        refine eq_top_iff.2 fun x _ => ?_
        have hmap : Submodule.map m.subtype (Submodule.span R T' ⊔ m • ⊤) =
            Ideal.span T ⊔ m ^ 2 := by
          rw [Submodule.map_sup, Submodule.map_span, Submodule.map_smul'', Submodule.map_top,
            Submodule.range_subtype, pow_two, Ideal.span, Ideal.smul_eq_mul]
          congr 2
          ext y
          simp only [Set.mem_image, Set.mem_preimage, Submodule.coe_subtype, T']
          exact ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, hTm hy⟩, hy, rfl⟩⟩
        have : (x : R) ∈ Submodule.map m.subtype (Submodule.span R T' ⊔ m • ⊤) :=
          hmap ▸ h x.2
        obtain ⟨y, hy, hyx⟩ := this
        rwa [Subtype.val_injective hyx] at hy
      have : Module.Finite R (m ⧸ m • (⊤ : Submodule R m)) := by
        set K := m • (⊤ : Submodule R m)
        have e : (⊤ : Submodule R (m ⧸ K)) = Submodule.span R (K.mkQ '' T') := by
          rw [← Submodule.map_span, ← sup_bot_eq (Submodule.map K.mkQ _),
            ← Submodule.mkQ_map_self K, ← Submodule.map_sup, hspan, Submodule.map_top,
            Submodule.range_mkQ]
        exact ⟨e ▸ Submodule.fg_span (hT'.image _)⟩
      exact Module.Finite.of_restrictScalars_finite R (R ⧸ m) _
  exact (Submodule.fg_top m).1 (Module.Finite.fg_top)

/-- A complete local `ℤ_[ℓ]`-algebra whose residue field is the image of `ℤ_[ℓ]` and whose maximal
ideal is finitely generated is Noetherian: it is a quotient of a power series ring over `ℤ_[ℓ]`
(Stacks 0315), which is Noetherian (Stacks 0306). -/
theorem isNoetherianRing_of_fg_maximalIdeal [IsAdicComplete (maximalIdeal R) R] {ℓ : ℕ}
    [Fact ℓ.Prime] [Algebra ℤ_[ℓ] R]
    (hres : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R)).comp
      (algebraMap ℤ_[ℓ] R))) (hfg : (maximalIdeal R).FG) : IsNoetherianRing R := by
  obtain ⟨k, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  obtain ⟨F, hF, -, -⟩ := Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
    (maximalIdeal R) y hy (algebraMap ℤ_[ℓ] R) hres
  have := mvPowerSeries_fin_isNoetherianRing ℤ_[ℓ] k
  exact isNoetherianRing_of_surjective _ _ F hF

end IsLocalRing
