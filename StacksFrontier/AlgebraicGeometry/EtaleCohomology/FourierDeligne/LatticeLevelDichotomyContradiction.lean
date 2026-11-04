module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LatticeLevelSaturation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSubsheafMonodromyDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MatrixContinuousModule

/-!
# A stable proper subspace contradicts the level dichotomy

Let `O` be a domain with fraction field `E`, `ℓ ∈ O` nonzero and not a unit, with every nonzero
`d ∈ O` dividing a power of `ℓ`, and let `S₀` be a set of matrices over `O`. If an `S₀`-stable
subspace `0 ≠ W ≠ E^ι` exists, then its saturated lattice reduced modulo `ℓ^{N+1}`
(`Stacks.EtaleCohomology.latticeLevel`) is an `S₀`-stable submodule which is not killed by
`ℓ^N` and does not contain `ℓ^b (O/ℓ^{N+1})^ι` for any `b ≤ N`. Hence the level dichotomy at
`(N, b)` with `b ≤ N` forces `W = 0` or `W = E^ι`.

## Main results

* `Stacks.EtaleCohomology.eq_bot_or_eq_top_of_levelDichotomy`: the level dichotomy at `(N, b)`,
  `b ≤ N`, for the `S₀`-stable submodules of `(O/ℓ^{N+1})^ι` rules out `S₀`-stable proper
  nonzero subspaces of `E^ι`.
* `Stacks.EtaleCohomology.eq_bot_or_eq_top_of_continuousModuleLevelDichotomy`: the same for the
  finite continuous module `(O/ℓ^{N+1})^m` given by `σ : G → GL_m(O)`.
-/

@[expose] public noncomputable section

open Matrix

universe v w

namespace Stacks.EtaleCohomology

variable {O : Type} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The level dichotomy at `(N, b)`, `b ≤ N`, rules out stable proper subspaces.** -/
theorem eq_bot_or_eq_top_of_levelDichotomy {ℓ : O} (hℓ0 : ℓ ≠ 0) (hℓu : ¬IsUnit ℓ)
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) (S₀ : Set (Matrix ι ι O))
    (W : Submodule E (ι → E)) (hW : ∀ a ∈ S₀, ∀ v ∈ W, a.map (algebraMap O E) *ᵥ v ∈ W)
    {N b : ℕ} (hb : b ≤ N)
    (hD : ∀ S : Submodule (O ⧸ Ideal.span {ℓ ^ (N + 1)}) (ι → O ⧸ Ideal.span {ℓ ^ (N + 1)}),
      (∀ a ∈ S₀, ∀ v ∈ S, a.map (algebraMap O (O ⧸ Ideal.span {ℓ ^ (N + 1)})) *ᵥ v ∈ S) →
      (∃ v ∈ S, ℓ ^ N • v ≠ 0) → ∀ w, ℓ ^ b • w ∈ S) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra! h
  obtain ⟨w, hw⟩ := exists_pow_smul_not_mem_latticeLevel E hℓ0 hℓu hℓ h.2 hb
  exact hw (hD _ (fun a ha _ hv ↦ mulVec_mem_latticeLevel E W _ a (hW a ha) hv)
    (exists_pow_smul_ne_zero_mem_latticeLevel E hℓ0 hℓu hℓ h.1 N) w)

/-- **The level dichotomy of a matrix module rules out stable proper subspaces.** Let
`σ : G → GL_m(O)` and suppose the finite continuous module `(O/ℓ^{N+1})^m` with `G` acting through
`σ` modulo `ℓ^{N+1}` satisfies the level dichotomy at `(N, b)` with `b ≤ N`. Then every
`σ(G)`-stable subspace of `E^m` is `0` or `E^m`. -/
theorem eq_bot_or_eq_top_of_continuousModuleLevelDichotomy {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {m : ℕ} (ℓ : ℕ) (hℓ0 : (ℓ : O) ≠ 0)
    (hℓu : ¬IsUnit (ℓ : O)) (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ (ℓ : O) ^ c) {N b : ℕ}
    [Finite (O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)})] (hb : b ≤ N) (σ : G →* GL (Fin m) O)
    (hσ : IsOpen (((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N + 1)}))).comp σ).ker : Set G))
    (hD : ContinuousModuleLevelDichotomy (matrixContinuousModule.{v, w}
      (O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)}) ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N + 1)}))).comp σ) hσ) ℓ N b)
    (W : Submodule E (Fin m → E)) (hW : ∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap O E) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  refine eq_bot_or_eq_top_of_levelDichotomy E hℓ0 hℓu hℓ (Set.range fun g ↦ (σ g).val) W
    (Set.forall_mem_range.2 hW) hb fun S hS hSN w ↦ ?_
  let e : ULift.{w} (Fin m → O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)})
      ≃ₗ[O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)}]
      (Fin m → O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)}) := ULift.moduleEquiv
  have hsmul : ∀ (k : ℕ) (v : Fin m → O ⧸ Ideal.span {(ℓ : O) ^ (N + 1)}),
      (ℓ : O) ^ k • v = ℓ ^ k • v := fun k v ↦ by
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  have := hD (S.comap e.toLinearMap) (fun g x hx ↦ by
      change e (ULift.up ((((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N + 1)}))).comp σ) g).val *ᵥ (e x))) ∈ S
      exact hS _ ⟨g, rfl⟩ _ hx)
    (by
      obtain ⟨v, hv, hv0⟩ := hSN
      refine ⟨e.symm v, Submodule.mem_comap.2 ?_, fun h0 ↦ hv0 ?_⟩
      · exact (congrArg (· ∈ S) (e.apply_symm_apply v)).mpr hv
      · rw [hsmul, ← e.apply_symm_apply v, ← map_nsmul]
        exact (congrArg e h0).trans (map_zero e)) (e.symm w)
  rwa [hsmul, ← e.apply_symm_apply w, ← map_nsmul]

end Stacks.EtaleCohomology

end
