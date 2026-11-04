module

public import StacksFrontier.RingTheory.AdicCompletion.ShortExact

/-!
# Adic completeness of the middle term of a short exact sequence

Let `R` be a commutative ring, `I ⊆ R` an ideal and `0 → M → N → Q → 0` a short exact sequence of
`R`-modules in which `Q` is annihilated by `I ^ c`. Stacks 0BNG — available here as
`AdicCompletion.map_shortExact_and_isAdicComplete_of_pow_smul_top_eq_bot` — says that `I`-adic
completion keeps this sequence short exact and that `Q` is already `I`-adically complete. Putting
that sequence next to the original one gives a ladder whose outer vertical maps are the canonical
maps `M → M^∧` and `Q → Q^∧`, and if the first of them is bijective then so is the middle one: the
middle term is `I`-adically complete as soon as the submodule is.

## Main results

* `AdicCompletion.isAdicComplete_of_shortExact_of_pow_smul_top_eq_bot` — in a short exact sequence
  whose third term is annihilated by a power of `I`, the middle term is `I`-adically complete as
  soon as the first term is.

## References

* [Stacks Project, Tag 0BNG](https://stacks.math.columbia.edu/tag/0BNG)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public section

namespace AdicCompletion

/-- **Completeness of the middle term.** Let `0 → M → N → Q → 0` be a short exact sequence of
`R`-modules with `I ^ c • (⊤ : Submodule R Q) = ⊥`. If `M` is `I`-adically complete, then so is
`N`. -/
public theorem isAdicComplete_of_shortExact_of_pow_smul_top_eq_bot
    {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {c : ℕ} (hQ : I ^ c • (⊤ : Submodule R Q) = ⊥) [IsAdicComplete I M] :
    IsAdicComplete I N := by
  obtain ⟨hmf, hmfg, -, hQc⟩ :=
    map_shortExact_and_isAdicComplete_of_pow_smul_top_eq_bot I hf hfg hg hQ
  have hMb : Function.Bijective (of I M) := of_bijective_iff.mpr ‹_›
  have hQb : Function.Bijective (of I Q) := of_bijective_iff.mpr hQc
  refine of_bijective_iff.mp ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · have h0 : of I N (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hgQ : of I Q (g (x - y)) = 0 := by
      rw [← map_of I g, h0, _root_.map_zero]
    obtain ⟨m, hm⟩ := (hfg (x - y)).mp (hQb.injective (by simpa using hgQ))
    have hm1 : of I M m = 0 := hmf (by rw [map_of, hm, h0, _root_.map_zero])
    obtain rfl : m = 0 := hMb.injective (by simpa using hm1)
    exact sub_eq_zero.mp (by simpa using hm.symm)
  · obtain ⟨q, hq⟩ := hQb.surjective (map I g z)
    obtain ⟨n, hn⟩ := hg q
    have hz0 : map I g (z - of I N n) = 0 := by
      rw [map_sub, ← hq, map_of, hn, sub_self]
    obtain ⟨w, hw⟩ := (hmfg (z - of I N n)).mp hz0
    obtain ⟨m, hm⟩ := hMb.surjective w
    exact ⟨n + f m, by rw [map_add, ← map_of I f, hm, hw, add_sub_cancel]⟩

end AdicCompletion

end
