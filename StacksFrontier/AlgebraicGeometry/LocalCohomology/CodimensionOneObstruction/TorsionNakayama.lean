module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# A finite module divisible by an element of a prime is killed outside that prime

Let `R` be a commutative ring, `q` a prime ideal and `s ∈ q`. If a finite `R`-module `N` is
"divisible by `s` away from `q`" — every `w : N` is of the form `s • w' = g • w` for some `w' : N`
and some `g ∉ q` — then every element of `N` is annihilated by some element outside `q`; that is,
`N` becomes zero after localizing at `q`.

This is Nakayama's lemma read at the prime `q`. The localization `N_q` is a finite module over the
local ring `R_q`, and the divisibility hypothesis says exactly that multiplication by the image of
`s` is surjective on `N_q`; since that image lies in the maximal ideal, the maximal ideal does not
shrink `N_q`, so `N_q = 0`.

## Main results

* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero`: the statement
  above, for a finite module.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero_of_mem`: the same
  for a submodule of a finite module over a Noetherian ring, which is the form the geometry uses —
  the submodule is cut out of the sections of a sheaf by an annihilation condition, so it is not
  given with generators of its own.

## Implementation notes

This is the final contradiction of the first paragraph of [Stacks, Tag 0AWC] at a general
associated point, in the only form in which no scheme appears. There `R` is the ring of an affine
chart `V₀`, `q` the prime of the point `z` of the complement, `s` an element of `q` outside the
prime `p` of the associated point `x`, and `N` the sections over `V₀ ⊓ U` of the coherent module
that are annihilated by `p`. The divisibility hypothesis is
`exists_section_smul_eq_smul_of_notMem_primeIdealOf`, in the same namespace as the results below,
and the conclusion contradicts the existence of a section with nonzero germ at `x`, because a
function outside `q` does not vanish at `x`.

The cited remark closes instead by exhibiting the residue field `κ(x)` as a finite module over
`𝒪_{\overline{\{x\}}, z}` and concluding that the latter is a field — the statement
`AlgebraicGeometry.isField_of_finite_fractionRing`. Nakayama at `q` reaches the contradiction
without constructing that residue field: the element `s ∈ q \ p` acts both invertibly (by
divisibility) and topologically nilpotently (by Nakayama) on the localized module, which is
already absurd.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

universe u v

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- **Nakayama at a prime.** Let `q` be a prime of `R` and `s ∈ q`, and let `N` be a finite
`R`-module in which every element is, up to a factor outside `q`, divisible by `s`. Then every
element of `N` is annihilated by some element outside `q`.

The localization `N_q` is a finite module over the local ring `R_q`; the hypothesis says that the
image of `s` acts surjectively on it, and that image lies in the maximal ideal, so `N_q` is not
shrunk by the maximal ideal and Nakayama's lemma gives `N_q = 0`. -/
theorem exists_notMem_smul_eq_zero {R : Type u} [CommRing R] {q : Ideal R} [q.IsPrime]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] {s : R} (hs : s ∈ q)
    (hdiv : ∀ w : N, ∃ w' : N, ∃ g : R, g ∉ q ∧ s • w' = g • w) (w : N) :
    ∃ g : R, g ∉ q ∧ g • w = 0 := by
  classical
  have hle : (⊤ : Submodule (Localization.AtPrime q) (LocalizedModule q.primeCompl N))
      ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) • ⊤ := by
    intro t _
    induction t using LocalizedModule.induction_on with
    | _ v c =>
      obtain ⟨v', g, hg, hgv⟩ := hdiv v
      have key : LocalizedModule.mk v c
          = algebraMap R (Localization.AtPrime q) s
            • LocalizedModule.mk v' ((⟨g, hg⟩ : q.primeCompl) * c) := by
        rw [algebraMap_smul, LocalizedModule.smul'_mk, hgv]
        exact (LocalizedModule.mk_cancel_common_left ⟨g, hg⟩ c v).symm
      rw [key]
      exact Submodule.smul_mem_smul
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ q s).mpr hs) trivial
  have htop : (⊤ : Submodule (Localization.AtPrime q) (LocalizedModule q.primeCompl N)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (Module.finite_def.mp inferInstance) hle
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have h0 : LocalizedModule.mk w (1 : q.primeCompl) = 0 := by
    have hmem : LocalizedModule.mk w (1 : q.primeCompl) ∈
        (⊤ : Submodule (Localization.AtPrime q) (LocalizedModule q.primeCompl N)) := trivial
    rw [htop] at hmem
    simpa using hmem
  rw [show (0 : LocalizedModule q.primeCompl N) = LocalizedModule.mk 0 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  exact ⟨u, u.2, by simpa [Submonoid.smul_def] using hu⟩

/-- **Nakayama at a prime, for a submodule.** The form of
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero` used by the
geometry: `P` is a submodule of a finite module over a Noetherian ring, so it is finite without
being presented by generators, and the divisibility hypothesis and the conclusion are stated by
membership in `P` rather than on a type of its own. -/
theorem exists_notMem_smul_eq_zero_of_mem {R : Type u} [CommRing R] [IsNoetherianRing R]
    {q : Ideal R} [q.IsPrime] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (P : Submodule R M) {s : R} (hs : s ∈ q)
    (hdiv : ∀ w ∈ P, ∃ w' ∈ P, ∃ g : R, g ∉ q ∧ s • w' = g • w)
    {m : M} (hm : m ∈ P) : ∃ g : R, g ∉ q ∧ g • m = 0 := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  have : Module.Finite R P := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian P)
  have hdiv' : ∀ w : P, ∃ w' : P, ∃ g : R, g ∉ q ∧ s • w' = g • w := by
    intro w
    obtain ⟨w', hw', g, hg, he⟩ := hdiv w.1 w.2
    exact ⟨⟨w', hw'⟩, g, hg, Subtype.ext he⟩
  obtain ⟨g, hg, he⟩ := exists_notMem_smul_eq_zero hs hdiv' ⟨m, hm⟩
  exact ⟨g, hg, by simpa using congrArg Subtype.val he⟩

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
