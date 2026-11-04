module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Freeness of a fixed finite rank descends along a faithfully flat extension of a local ring

Let `R` be a local ring, let `S` be a faithfully flat `R`-algebra and let `M` be a finite
`R`-module. If `S ⊗[R] M` is free of rank `p` over `S`, then `M` is free of rank `p` over `R`.

Both halves of the conclusion come for free from the general theory once they are put together:
flatness descends along a faithfully flat ring map (`Module.Flat.of_flat_tensorProduct`), a
finite flat module over a local ring is free (Stacks 00NZ,
`Module.free_of_flat_of_isLocalRing`), and the rank is read off the base change
(`Module.finrank_baseChange`).

Locality of `R` is needed and not only convenient: over a Dedekind domain a nonprincipal ideal
is finite, flat and of rank one, and becomes free after a faithfully flat extension, without
being free.

## Main results

* `Module.nonempty_linearEquiv_finsupp_of_faithfullyFlat`: the descent of freeness of rank `p`.

## References

* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module

/-- **Freeness of a fixed finite rank descends along a faithfully flat extension of a local
ring.** If `M` is a finite module over a local ring `R` and `S ⊗[R] M` is free of rank `p` over a
faithfully flat `R`-algebra `S`, then `M` is free of rank `p` over `R`. -/
@[sga "1 VIII 1.11" "special case", sga "4½ Arcata 1.4.2" "(ii), special case"]
public theorem nonempty_linearEquiv_finsupp_of_faithfullyFlat
    (R : Type u) [CommRing R] [IsLocalRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (p : ℕ)
    (h : Nonempty ((S ⊗[R] M) ≃ₗ[S] (Fin p →₀ S))) :
    Nonempty (M ≃ₗ[R] (Fin p →₀ R)) := by
  obtain ⟨e⟩ := h
  have hnt : Nontrivial S := (TensorProduct.lid R S).symm.toEquiv.nontrivial
  have hflatS : Module.Flat S (S ⊗[R] M) := Module.Flat.of_linearEquiv e
  have hflat : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  have hfree : Module.Free R M := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank R M = p := by
    rw [← Module.finrank_baseChange (R := S), e.finrank_eq, Module.finrank_finsupp_self,
      Fintype.card_fin]
  exact ⟨(Module.finBasisOfFinrankEq R M hrank).repr⟩

end Module

end
