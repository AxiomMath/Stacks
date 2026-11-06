module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquare
public import StacksFrontier.CategoryTheory.Sites.Torsion.TorsionColimitOfKernels
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# `𝓕 = colim 𝓕[n]` over the integers invertible in a field

Let `K` be a field and `𝓕` an abelian sheaf on the small étale site of a scheme `U` whose stalks
are torsion of orders invertible in `K`. This file proves the first step of the proofs of
[Stacks, Tag 0F1H] and [Stacks, Tag 0F1I]: *"Write `𝓕 = colim 𝓕[n]` where the colimit is over
the multiplicative system of integers invertible in `K`."*

## Main definitions

* `Stacks.EtaleCohomology.invertibleIn K` — the multiplicative system of the natural numbers
  invertible in `K`.

## Main results

* `Stacks.EtaleCohomology.isUnit_natCast_of_coprime_ringExpChar` — a positive integer prime to
  the exponential characteristic of `K` is invertible in `K`.
* `Stacks.EtaleCohomology.isColimit_torsionKernelsCocone_of_hasTorsionStalksInvertibleIn` —
  **the inclusions `𝓕[n] ⟶ 𝓕`, `n` invertible in `K`, exhibit `𝓕` as the colimit of the
  `𝓕[n]`**.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (K : Type u) [Field K]

/-- **The multiplicative system of the integers invertible in `K`**: the natural numbers whose
image in `K` is a unit. -/
def invertibleIn : Submonoid ℕ where
  carrier := {n | IsUnit (n : K)}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change IsUnit ((a * b : ℕ) : K)
    rw [Nat.cast_mul]
    exact ha.mul hb

/-- A positive integer prime to the exponential characteristic of `K` is invertible in `K`. -/
theorem isUnit_natCast_of_coprime_ringExpChar {n : ℕ} (hn : 0 < n)
    (h : n.Coprime (ringExpChar K)) : IsUnit (n : K) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd : ringChar K ∣ n := (CharP.cast_eq_zero_iff K (ringChar K) n).1 h0
  rcases Nat.eq_zero_or_pos (ringChar K) with hz | hpos
  · rw [hz, zero_dvd_iff] at hd
    omega
  · have : NeZero (ringChar K) := ⟨hpos.ne'⟩
    have hp := (CharP.char_is_prime_of_pos K (ringChar K)).out
    have he : ringExpChar K = ringChar K := max_eq_left hpos
    rw [he] at h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h) hd)

/-- **`𝓕 = colim 𝓕[n]` over the integers `n` invertible in `K`** ([Stacks, Tag 0F1H], first step
of the proof): for an abelian sheaf `𝓕` on the small étale site of `U` whose stalks are torsion
of orders invertible in `K`, the inclusions `𝓕[n] ⟶ 𝓕` of the kernels of multiplication by the
integers `n` invertible in `K` exhibit `𝓕` as the colimit of the `𝓕[n]`, over these integers
ordered by divisibility. -/
theorem isColimit_torsionKernelsCocone_of_hasTorsionStalksInvertibleIn {U : Scheme.{u}}
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : OpenImmersionProductSquare.HasTorsionStalksInvertibleIn K 𝓕) :
    Nonempty (IsColimit (Stacks.Torsion.torsionKernelsCocone 𝓕 (invertibleIn K))) := by
  let : EssentiallySmall.{u + 1} U.Etale := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology U) Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology U) Ab.{u + 1}
  have : HasFilteredColimitsOfSize.{0, 0} (Sheaf (smallEtaleTopology U) Ab.{u + 1}) :=
    hasFilteredColimitsOfSize_shrink.{0, 0, u + 1, u + 1}
  have : AB5OfSize.{u + 1, u + 1} (Sheaf (smallEtaleTopology U) Ab.{u + 1}) := inferInstance
  have : AB5OfSize.{0, 0} (Sheaf (smallEtaleTopology U) Ab.{u + 1}) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  refine Stacks.Torsion.isColimitTorsionKernelsCocone 𝓕 (invertibleIn K) (fun V x => ?_)
  obtain ⟨R, hR, hRx⟩ := h𝓕 V x
  refine ⟨R, hR, fun W f hf => ?_⟩
  obtain ⟨n, hn, hcop, hx⟩ := hRx W f hf
  exact ⟨n, isUnit_natCast_of_coprime_ringExpChar K hn hcop, hx⟩

end Stacks.EtaleCohomology

end
