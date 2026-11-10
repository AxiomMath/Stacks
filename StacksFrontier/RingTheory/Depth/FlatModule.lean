module

public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The depth of a flat module is at least the depth of the ring

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` a flat `R`-module. Then

`depth_I(R) ≤ depth_I(M)`.

The reason is that a regular sequence on `R` with its terms in `I` stays regular on `M`: weak
regularity is preserved by tensoring with a flat module
(`RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_lTensor`, read at `M ⊗_R R ≅ M`), and the
nondegeneracy clause `Ideal.ofList rs • M ≠ M` follows from `I • M ≠ M`, which is exactly the
branch of `Module.depth` in which the supremum over regular sequences is the depth.

In the degenerate branch there is nothing to prove: if `I • M = M` then `depth_I(M) = ⊤` by the
convention of Stacks 00LI. Conversely `I • R = I`, so `I • R = R` forces `I = R` and hence
`I • M = M`; the two degenerate branches therefore cannot separate the two sides.

This is the input that lets Faltings' annihilator theorem (Stacks 0EFC) be applied to a module
whose localizations are flat once it is known for the ring itself.

## Main results

* `Module.depth_le_depth_of_flat` — the inequality above.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

open RingTheory.Sequence

universe u

namespace Module

/-- An ideal acting on the ring itself is itself. -/
private lemma ideal_smul_top_self {R : Type u} [CommRing R] (J : Ideal R) :
    J • (⊤ : Submodule R R) = J := by
  simp only [smul_eq_mul, Ideal.mul_top]

/-- **The depth of a flat module is at least the depth of the ring.** A regular sequence on `R`
whose terms lie in `I` remains regular on a flat `R`-module `M`, so every length contributing to
`depth_I(R)` contributes to `depth_I(M)`. -/
@[sga "2 X 2.1" "inequality depth O_{U"]
public theorem depth_le_depth_of_flat {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.depth R I R ≤ Module.depth R I M := by
  classical
  unfold Module.depth
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [ite_eq_left hM]
    exact le_top
  have hR : ¬ (I • (⊤ : Submodule R R) = ⊤) := by
    intro h
    refine hM ?_
    have hI : I = ⊤ := by rw [← ideal_smul_top_self I, h]
    rw [hI, Submodule.top_smul]
  rw [ite_eq_right hR, ite_eq_right hM]
  refine iSup₂_le fun rs hrs => ?_
  obtain ⟨hmem, hreg⟩ := hrs
  have hwr : IsWeaklyRegular M rs :=
    ((TensorProduct.rid R M).isWeaklyRegular_congr rs).mp
      (hreg.toIsWeaklyRegular.isWeaklyRegular_lTensor (M₂ := M))
  have hle : Ideal.ofList rs ≤ I := by
    rw [Ideal.ofList, Ideal.span_le]
    intro x hx
    exact hmem x hx
  have hreg' : IsRegular M rs := by
    refine (isRegular_iff M rs).mpr ⟨hwr, fun htop => hM (le_antisymm le_top ?_)⟩
    exact htop.le.trans (Submodule.smul_mono hle le_rfl)
  exact le_biSup (fun rs : List R => ((rs.length : ℕ) : ℕ∞))
    (show rs ∈ {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs} from ⟨hmem, hreg'⟩)

end Module

end
