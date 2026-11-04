module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# Twisting by a character preserves absolute irreducibility

For a representation `σ : G → GL_m(E)` and a character `χ : G → Eˣ`, a subspace over an
`E`-algebra `K` is stable under the twist `g ↦ χ(g) σ(g)`
(`Stacks.EtaleCohomology.characterTwist`) iff it is stable under `σ`: the twist only rescales
each `σ(g)` by the unit `χ(g)`. So the twist is absolutely irreducible (no nonzero proper stable
subspace over any `K`) iff `σ` is
(`Stacks.EtaleCohomology.forall_eq_bot_or_eq_top_characterTwist_iff`). In Laumon's argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) this is how the absolute irreducibility of
`σ` over `k'` passes to `σ ⊗ χ_{a xⁿ}`, the input of the Fourier transform at fixed `a`.

## Main results

* `Stacks.EtaleCohomology.mulVec_mem_characterTwist_iff`.
* `Stacks.EtaleCohomology.forall_eq_bot_or_eq_top_characterTwist_iff`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {G : Type*} [Group G] {E : Type} [Field E] {m : ℕ} (σ : G →* GL (Fin m) E)
  (χ : G →* Eˣ) (K : Type*) [Field K] [Algebra E K]

/-- **A subspace is stable under the twist by a character iff it is stable under `σ`.** -/
public theorem mulVec_mem_characterTwist_iff (W : Submodule K (Fin m → K)) :
    (∀ g, ∀ v ∈ W, (characterTwist σ χ g).val.map (algebraMap E K) *ᵥ v ∈ W) ↔
      ∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W := by
  have hmap : ∀ g, (characterTwist σ χ g).val.map (algebraMap E K) =
      algebraMap E K (χ g : E) • (σ g).val.map (algebraMap E K) := fun g => by
    rw [characterTwist_val]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine forall_congr' fun g => forall₂_congr fun v _ => ?_
  rw [hmap, Matrix.smul_mulVec,
    W.smul_mem_iff ((map_ne_zero (algebraMap E K)).2 (χ g).ne_zero)]

/-- **The twist of `σ` by a character is absolutely irreducible iff `σ` is.** -/
public theorem forall_eq_bot_or_eq_top_characterTwist_iff :
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (characterTwist σ χ g).val.map (algebraMap E K) *ᵥ v ∈ W) →
        W = ⊥ ∨ W = ⊤) ↔
    ∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  simp only [mulVec_mem_characterTwist_iff]

end Stacks.EtaleCohomology

end
