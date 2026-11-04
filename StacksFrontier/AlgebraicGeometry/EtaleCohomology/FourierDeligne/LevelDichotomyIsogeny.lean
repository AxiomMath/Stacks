module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LatticeLevelSaturation

/-!
# The level dichotomy through an isogeny, and at shifted levels

Let `R` be a commutative ring with an `O`-algebra structure and `ℓ ∈ O`. Say a module `M` with an
action of a type `G` by `R`-linear maps satisfies the level dichotomy at `N, c₀` if every
`G`-stable submodule `S ⊆ M` with `ℓᴺ S ≠ 0` contains `ℓ^{c₀} M`.

* **Isogeny** (`Stacks.EtaleCohomology.levelDichotomy_of_isogeny`): if `f : L ⟶ M` and
  `g : M ⟶ L` are `G`-equivariant with `g ∘ f = ℓᶜ` and `f ∘ g = ℓᶜ`, the dichotomy for `M` at
  `N, c₀` gives the dichotomy for `L` at `N + c, c₀ + c`: the image `f(S)` of a stable `S ⊆ L`
  with `ℓ^{N+c} S ≠ 0` has `ℓᴺ f(S) ≠ 0`, so contains `ℓ^{c₀} M`, and
  `ℓ^{c₀+c} L = g(ℓ^{c₀} f(L)) ⊆ g(f(S)) = ℓᶜ S`.
* **Shifted levels** (`Stacks.EtaleCohomology.exists_shifted_levelDichotomy_of_absIrr`): for an
  absolutely irreducible family of integral matrices over a discrete valuation ring `O` with `ℓ`
  in the maximal ideal, there is `c₀` such that for all `c ≤ N` every stable submodule of
  `(O/ℓᴺ⁺¹)^ι` not killed by `ℓ^{N-c}` contains `ℓ^{c₀+c} (O/ℓᴺ⁺¹)^ι`
  (`Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr_pow` with the divisibility
  `Stacks.EtaleCohomology.exists_pow_succ_eq_mul_of_pow_smul_ne_zero`).

These carry the level dichotomy of the Fourier transform, through the uniform isogenies between
the levels of the sheaves of Laumon's argument, to the levels of a lattice of the representation
`τ` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece L6).

## Main results

* `Stacks.EtaleCohomology.levelDichotomy_of_isogeny`.
* `Stacks.EtaleCohomology.exists_shifted_levelDichotomy_of_absIrr`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

/-- **The level dichotomy through an isogeny.** Let `f : L → M`, `g : M → L` be `R`-linear,
equivariant for actions `ρL`, `ρM` of `G`, with `g ∘ f = ℓᶜ` and `f ∘ g = ℓᶜ`. If every
`G`-stable submodule of `M` not killed by `ℓᴺ` contains `ℓ^{c₀} M`, then every `G`-stable
submodule of `L` not killed by `ℓ^{N+c}` contains `ℓ^{c₀+c} L`. -/
theorem levelDichotomy_of_isogeny {O R G L M : Type*} [CommRing O] [CommRing R] [Algebra O R]
    [AddCommGroup L] [Module R L] [Module O L] [IsScalarTower O R L]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M]
    (ℓ : O) (ρL : G → L →ₗ[R] L) (ρM : G → M →ₗ[R] M) (f : L →ₗ[R] M) (g : M →ₗ[R] L)
    (hf : ∀ h x, f (ρL h x) = ρM h (f x)) (_hg : ∀ h y, g (ρM h y) = ρL h (g y)) (c : ℕ)
    (hgf : ∀ x, g (f x) = ℓ ^ c • x) (_hfg : ∀ y, f (g y) = ℓ ^ c • y) {N c₀ : ℕ}
    (hM : ∀ S : Submodule R M, (∀ h, ∀ y ∈ S, ρM h y ∈ S) → (∃ y ∈ S, ℓ ^ N • y ≠ 0) →
      ∀ y, ℓ ^ c₀ • y ∈ S)
    (S : Submodule R L) (hS : ∀ h, ∀ x ∈ S, ρL h x ∈ S) (hSN : ∃ x ∈ S, ℓ ^ (N + c) • x ≠ 0)
    (x : L) : ℓ ^ (c₀ + c) • x ∈ S := by
  have hsmul_f : ∀ (o : O) (x : L), f (o • x) = o • f x := fun o x => by
    rw [← algebraMap_smul R o x, map_smul, algebraMap_smul]
  have key : ∀ (m : ℕ) (x : L), ℓ ^ (m + c) • x = g (ℓ ^ m • f x) := fun m x => by
    rw [pow_add, mul_comm, mul_smul, ← hgf, hsmul_f]
  have hmapS : ∀ h, ∀ y ∈ S.map f, ρM h y ∈ S.map f := by
    rintro h _ ⟨x, hx, rfl⟩
    exact ⟨ρL h x, hS h x hx, hf h x⟩
  obtain ⟨x₀, hx₀, hx₀N⟩ := hSN
  have hne : ∃ y ∈ S.map f, ℓ ^ N • y ≠ 0 := by
    refine ⟨f x₀, ⟨x₀, hx₀, rfl⟩, fun h0 => hx₀N ?_⟩
    rw [key, h0, map_zero]
  obtain ⟨s, hs, hsx⟩ := hM _ hmapS hne (f x)
  have : ℓ ^ (c₀ + c) • x = ℓ ^ c • s := by
    rw [key, ← hsx, hgf]
  rw [this]
  exact S.smul_of_tower_mem _ hs

/-- **The level dichotomy of an absolutely irreducible integral representation at shifted
levels**, over a discrete valuation ring `O` with fraction field `E` and `ℓ` a nonzero element of
the maximal ideal: there is `c₀` such that for all `c ≤ N` every `S₀`-stable submodule
`S ⊆ (O/ℓᴺ⁺¹)^ι` with `ℓ^{N-c} S ≠ 0` contains `ℓ^{c₀+c} (O/ℓᴺ⁺¹)^ι`. -/
theorem exists_shifted_levelDichotomy_of_absIrr {O : Type} (E : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K : Type*) [Field K] [IsAlgClosed K] [Algebra E K] {ℓ : O}
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) (S₀ : Set (Matrix ι ι O))
    (hmul : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b ∈ S₀) (hone : (1 : Matrix ι ι O) ∈ S₀)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ a ∈ S₀, ∀ v ∈ W, (a.map (algebraMap O E)).map (algebraMap E K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ c₀ : ℕ, ∀ N c : ℕ, c ≤ N →
      ∀ S : Submodule (O ⧸ Ideal.span {ℓ ^ (N + 1)}) (ι → O ⧸ Ideal.span {ℓ ^ (N + 1)}),
        (∀ M ∈ S₀, ∀ v ∈ S, M.map (algebraMap O (O ⧸ Ideal.span {ℓ ^ (N + 1)})) *ᵥ v ∈ S) →
        (∃ x ∈ S, ℓ ^ (N - c) • x ≠ 0) →
          ∀ w : ι → O ⧸ Ideal.span {ℓ ^ (N + 1)}, ℓ ^ (c₀ + c) • w ∈ S := by
  obtain ⟨c₀, hc₀⟩ := exists_levelDichotomy_of_absIrr_pow E K hℓ S₀ hmul hone hirr
  exact ⟨c₀, fun N c hcN S hS hSN w =>
    hc₀ (O ⧸ Ideal.span {ℓ ^ (N + 1)}) (N - c) c
      (fun r hr => exists_pow_succ_eq_mul_of_pow_smul_ne_zero ℓ hcN r hr) S hS hSN w⟩

end Stacks.EtaleCohomology

end
