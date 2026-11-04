module

public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Maximal Cohen-Macaulay modules via regular sequences and depth

Let `M` be a finite nonzero module over a Noetherian local ring `R`. The predicate `IsMaxCM R M`
asks for an `M`-regular sequence in the maximal ideal of length `dim R`; this is equivalent to
`depth M = dim R`, the condition defining `IsMaximalCohenMacaulayModule`.

## Main results

* `isMaxCM_iff_depth_eq_ringKrullDim` : `IsMaxCM R M ↔ depth M = dim R`.

## References

Stacks project, tags `00LE`, `00LK`, `00NF`.
-/

@[expose] public section

open IsLocalRing

section Maximal

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/-- The depth of a finite nonzero module over a Noetherian local ring is at most the Krull
dimension of the ring. -/
@[ega "IV 5.7.3" "special case"]
private theorem depth_le_ringKrullDim :
    (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) ≤ ringKrullDim R := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
  refine (depth_le_krullDim_zeroLocus_of_mem_associatedPrimes p hp).trans ?_
  rw [ringKrullDim]
  exact Order.krullDim_le_of_strictMono (fun q => q.val) (Subtype.strictMono_coe _)

/-- A finite nonzero module `M` over a Noetherian local ring `R` has an `M`-regular sequence in
the maximal ideal of length `dim R` if and only if `depth M = dim R`. -/
@[ega "0 16.5.7" "special case"]
theorem isMaxCM_iff_depth_eq_ringKrullDim :
    IsMaxCM R M ↔ (Module.depthSup R (maximalIdeal R) M : WithBot ℕ∞) = ringKrullDim R := by
  constructor
  · rintro ⟨rs, hmem, hreg, hlen⟩
    refine le_antisymm depth_le_ringKrullDim ?_
    rw [← hlen]
    exact_mod_cast (le_sSup ⟨rs, rfl, hmem, hreg⟩ :
      (rs.length : ℕ∞) ≤ Module.depthSup R (maximalIdeal R) M)
  · intro h
    obtain ⟨ms, hmem, hreg, hlen⟩ :=
      exists_isRegular_length_eq_depth_of_depth_ne_top (depth_ne_top (R := R) (M := M))
    refine ⟨ms, hmem, hreg, ?_⟩
    rw [← h]
    exact_mod_cast hlen

end Maximal

end
