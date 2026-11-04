module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# A nonempty open of `𝔸^n_k` under a nonempty open of `𝔸^n_K`

Let `K/k` be an algebraic field extension and let `π : 𝔸^n_K ⟶ 𝔸^n_k` be the induced morphism of
affine spaces (`AlgebraicGeometry.AffineSpace.map`). Given a nonempty open `U ⊂ 𝔸^n_K`, this file
produces a nonempty open `U₀ ⊂ 𝔸^n_k` with `π⁻¹(U₀) ⊂ U`.

## Main results

* `AlgebraicGeometry.AffineSpace.exists_nonempty_preimage_map_le`: the statement above.

## Implementation notes

The argument is ideal-theoretic, read through
`AlgebraicGeometry.AffineSpace.SpecIso : 𝔸(n; Spec R) ≅ Spec (MvPolynomial n R)` and the
identification `AlgebraicGeometry.AffineSpace.map_SpecMap` of `π` with the spectrum of
`MvPolynomial.map`. Write the complement of `U` as a zero locus `V(I)`; since `MvPolynomial n K`
is a domain and `U` is nonempty, `I ≠ 0`. The ring `MvPolynomial n K` is integral over
`MvPolynomial n k` — the instance is Mathlib's, the extension being a pushout of `K/k` — so the
contraction `J = I ∩ MvPolynomial n k` is again nonzero (`Ideal.IsIntegral.comap_ne_bot`). Any
nonzero `h ∈ J` then does: the basic open `D(h) ⊂ 𝔸^n_k` is nonempty because `MvPolynomial n k`
is a domain, and its preimage `D(h_K)` misses `V(I)` because `h_K ∈ I`.

Taking `U₀` to be the complement of the image of `Uᶜ` would give the largest such open, at the
price of needing `π` to be a closed map; the weaker statement proved here needs no topology
beyond the basic opens, and it is all that the descent of a "for general `v`" assertion consumes,
such an assertion being monotone in the open.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineSpace

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A nonzero ideal of `MvPolynomial n K` meets `MvPolynomial n k` in a nonzero element, for
`K/k` an algebraic extension of fields: the extension `MvPolynomial n K / MvPolynomial n k` is
integral and both rings are domains. -/
theorem exists_ne_zero_mem_of_isAlgebraic {n : Type u} (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] {I : Ideal (MvPolynomial n K)} (hI : I ≠ ⊥) :
    ∃ h : MvPolynomial n k, h ≠ 0 ∧ MvPolynomial.map (algebraMap k K) h ∈ I := by
  have : Algebra.IsIntegral k K := Algebra.IsAlgebraic.isIntegral
  have hJ : I.comap (algebraMap (MvPolynomial n k) (MvPolynomial n K)) ≠ ⊥ :=
    Ideal.IsIntegral.comap_ne_bot (MvPolynomial n k) hI
  obtain ⟨h, hmem, hne⟩ := (Submodule.ne_bot_iff _).mp hJ
  exact ⟨h, hne, by simpa using hmem⟩

/-- **A polynomial over `k` cutting a nonempty open of `Spec (MvPolynomial n K)` from below.**
For `K/k` an algebraic extension of fields and `W` a nonempty open subset of
`Spec (MvPolynomial n K)`, there is a nonzero `h ∈ MvPolynomial n k` such that every prime not
containing the image of `h` lies in `W`.

This is the ideal-theoretic core of
`AlgebraicGeometry.AffineSpace.exists_nonempty_preimage_map_le`. -/
theorem exists_ne_zero_forall_mem_of_isAlgebraic {n : Type u} (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] {W : Set (PrimeSpectrum (MvPolynomial n K))}
    (hWopen : IsOpen W) (hW : W.Nonempty) :
    ∃ h : MvPolynomial n k, h ≠ 0 ∧ ∀ p : PrimeSpectrum (MvPolynomial n K),
      MvPolynomial.map (algebraMap k K) h ∉ p.asIdeal → p ∈ W := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff W).mp hWopen
  -- a prime misses `W` iff it contains `s`
  have hz (x : PrimeSpectrum (MvPolynomial n K)) : x ∉ W ↔ (s : Set _) ⊆ x.asIdeal :=
    (Set.ext_iff.mp hs x).trans (PrimeSpectrum.mem_zeroLocus _ _)
  have hIne : (Ideal.span s : Ideal (MvPolynomial n K)) ≠ ⊥ := fun hbot =>
    (hz hW.some).mpr (fun f hf => by simp [Ideal.span_eq_bot.mp hbot f hf]) hW.some_mem
  obtain ⟨h, hh0, hhI⟩ := exists_ne_zero_mem_of_isAlgebraic k K hIne
  refine ⟨h, hh0, fun p hp => ?_⟩
  by_contra hpW
  exact hp (Ideal.span_le.mpr ((hz p).mp hpW) hhI)

/-- **A nonempty open of `𝔸^n_k` whose points lift into a given nonempty open of `𝔸^n_K`.**
For `K/k` an algebraic extension of fields and `U ⊂ 𝔸^n_K` a nonempty open, there is a nonempty
open `U₀ ⊂ 𝔸^n_k` whose preimage under `π : 𝔸^n_K ⟶ 𝔸^n_k` is contained in `U`.

This is the missing input to the descent of a "for general `v`" assertion from `𝔸^n_K` back to
`𝔸^n_k`. -/
theorem exists_nonempty_preimage_map_le {n : Type u} (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (U : (𝔸(n; Spec (.of K))).Opens)
    (hU : U.1.Nonempty) :
    ∃ U₀ : (𝔸(n; Spec (.of k))).Opens, U₀.1.Nonempty ∧
      map n (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U₀ ≤ U := by
  classical
  set eK := SpecIso n (CommRingCat.of K) with heK
  set ek := SpecIso n (CommRingCat.of k) with hek
  have hKid : ∀ y, eK.inv.base (eK.hom.base y) = y := fun y =>
    (Scheme.homeoOfIso eK).symm_apply_apply y
  -- `U` read as an open subset of `Spec (MvPolynomial n K)`, which is nonempty.
  have hWne : (eK.inv ⁻¹ᵁ U).1.Nonempty := by
    obtain ⟨x, hx⟩ := hU
    refine ⟨eK.hom.base x, ?_⟩
    show eK.inv.base (eK.hom.base x) ∈ U
    rw [hKid]
    exact hx
  obtain ⟨h, hh0, hsub⟩ :=
    exists_ne_zero_forall_mem_of_isAlgebraic k K (W := (eK.inv ⁻¹ᵁ U).1) (eK.inv ⁻¹ᵁ U).2 hWne
  -- `π` is the spectrum of `MvPolynomial.map`, conjugated by the two identifications.
  have hcomp : map n (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ ek.hom =
      eK.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k K))) := by
    rw [heK, hek, map_SpecMap]
    simp
  refine ⟨ek.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h, ?_, ?_⟩
  · -- `D(h)` is nonempty because `MvPolynomial n k` is a domain, and `ek.hom` is a homeomorphism.
    have hbot : PrimeSpectrum.basicOpen h ≠ ⊥ := by
      rw [Ne, PrimeSpectrum.basicOpen_eq_bot_iff]
      simpa using hh0
    exact Set.Nonempty.preimage ((Opens.ne_bot_iff_nonempty _).mp hbot)
      (Scheme.homeoOfIso ek).surjective
  · -- `π⁻¹ D(h) = D(h_K)`, and `h_K` lies in the ideal cutting out the complement of `U`.
    intro p hp
    have hpt : ek.hom ((map n (Spec.map (CommRingCat.ofHom (algebraMap k K)))) p) =
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k K)))) (eK.hom p) := by
      rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
    replace hp : ek.hom ((map n (Spec.map (CommRingCat.ofHom (algebraMap k K)))) p) ∈
      PrimeSpectrum.basicOpen h := hp
    rw [hpt] at hp
    have hnot : MvPolynomial.map (algebraMap k K) h ∉ (eK.hom p).asIdeal := by
      have := (PrimeSpectrum.mem_basicOpen _ _).mp hp
      exact fun hc => this hc
    have hmemW : eK.hom.base p ∈ (eK.inv ⁻¹ᵁ U).1 := hsub _ hnot
    have : eK.inv.base (eK.hom.base p) ∈ U := hmemW
    rwa [hKid] at this

end AlgebraicGeometry.AffineSpace

end
