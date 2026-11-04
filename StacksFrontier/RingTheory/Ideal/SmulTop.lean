module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.Module.IdealSmulTop

/-!
# `I • ⊤` under a surjection and in a quotient

Two facts about the submodule `I • (⊤ : Submodule R M)`: it is preserved by a surjection, so
`I • ⊤ ≠ ⊤` passes from a quotient back to the module; and in `R ⧸ I` it is the image of the
ideal, so `J • ⊤ = ⊤` says exactly `J ⊔ I = ⊤`.
-/

@[expose] public section

/-- An ideal acting on the top submodule of its own ring is itself: `I • ⊤ = I`. -/
alias ideal_smul_top := Ideal.smul_top_eq_self

/-- If `f : M → N` is a surjective `R`-linear map and `I • N ≠ N`, then `I • M ≠ M`. -/
theorem smul_top_ne_top_of_surjective {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R)
    {f : M →ₗ[R] N} (hf : Function.Surjective f) (h : I • (⊤ : Submodule R N) ≠ ⊤) :
    I • (⊤ : Submodule R M) ≠ ⊤ := fun hM => h <| by
  have htop : Submodule.map f ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  calc I • (⊤ : Submodule R N) = I • Submodule.map f ⊤ := by rw [htop]
    _ = Submodule.map f (I • ⊤) := (Submodule.map_smul'' I ⊤ f).symm
    _ = ⊤ := by rw [hM, htop]

/-- An ideal `J` of `R` satisfies `J • (R/I) = R/I` if and only if `J + I = R`. -/
theorem smul_top_quotient_eq_top_iff {R : Type*} [CommRing R] (I J : Ideal R) :
    J • (⊤ : Submodule R (R ⧸ I)) = ⊤ ↔ J ⊔ I = ⊤ := by
  have hmap : Submodule.map I.mkQ J = J • (⊤ : Submodule R (R ⧸ I)) := by
    conv_lhs => rw [← ideal_smul_top J]
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [← hmap]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [sup_comm, ← Submodule.comap_map_mkQ I J, h, Submodule.comap_top]
  · rw [← sup_bot_eq (Submodule.map I.mkQ J), ← Submodule.mkQ_map_self I, ← Submodule.map_sup, h,
      Submodule.map_top, Submodule.range_mkQ]
