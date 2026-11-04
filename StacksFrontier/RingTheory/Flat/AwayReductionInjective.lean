module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.RingTheory.Flat.MittagLeffler

/-!
# One localization kills the prime-complement torsion of a reduction

Let `C` be a commutative ring, `M` a `C`-module, `J` an ideal of `C` and `Q` a prime of `C`.
Write `M/JM` for the reduction `M ⧸ J • ⊤`. This file proves that if the reduction is a
Noetherian `C`-module then there is a single `g ∉ Q` such that, in the away-localization
`M_g`, **every** `r ∉ Q` acts injectively modulo `J`:

`r • ζ ∈ J • ⊤ → ζ ∈ J • ⊤`  for all `ζ : M_g`.

This is the algebraic form of the step in the proof of Stacks 05U7 which the source argues
geometrically: there `X` is shrunk so that every point of `Ass_{X_s}(𝓕_s)` specializes to `x`,
and the transition maps `Γ(U_i, 𝓕)/𝔪_A → Γ(U_{i'}, 𝓕)/𝔪_A` are then injective because a
section of the kernel would be supported in a closed subset of `X_s` missing `x`. Taking
`J = 𝔪_A · C` and `Q` the prime of `x`, the shrinking is the choice of `g` below and the
injectivity is the conclusion.

The argument needs no associated primes. The obstruction to `r` acting injectively modulo `J`
is the submodule of `M/JM` annihilated by some element outside `Q`; it is finitely generated,
so a product of annihilators of its generators is one element `g ∉ Q` killing all of it, and
after localizing at `g` the obstruction has become zero.

## Main definitions

* `Stacks.AwayReduction.primeComplTorsion`: the elements annihilated by some element outside
  the prime.

## Main results

* `Stacks.AwayReduction.exists_mem_primeCompl_smul_eq_zero`: one element outside the prime
  annihilates the whole prime-complement torsion, as soon as the latter is finitely generated.
* `Stacks.AwayReduction.exists_mem_primeCompl_forall_mem_smul_top_localized`: the conclusion
  above — one localization after which every denominator is injective modulo `J`.
* `Stacks.AwayReduction.exists_mem_primeCompl_forall_injective_mapQ`: the same conclusion in
  the `Submodule.mapQ` form in which Stacks 05U7 and 0AT0 phrase reduction modulo an ideal.

## Implementation notes

Reduction modulo `J` is the quotient by `J • (⊤ : Submodule C M)`, matching the spelling used
throughout the flatness development. The localization is the concrete `LocalizedModule` at
`Submonoid.powers g`, so that the transition maps of the Stacks 05U7 colimit diagram — which
are multiplication by a denominator — are literally the maps appearing here.

The Noetherian hypothesis is placed on the reduction `M ⧸ J • ⊤` rather than on `M`: that is
all the argument uses, and in the intended application `M` is a finite module over a finite
type algebra over a local ring, whose reduction modulo the maximal ideal of the base is finite
over a Noetherian ring while `M` itself need not be Noetherian.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
-/

@[expose] public section

universe u v

namespace Stacks.AwayReduction

open Submonoid (powers)

variable {C : Type u} [CommRing C]

/-! ### The prime-complement torsion -/

/-- The submodule of elements of `M` annihilated by some element outside the prime `Q`; it is
the kernel of the localization map `M → M_Q`. -/
def primeComplTorsion (Q : Ideal C) [Q.IsPrime] (M : Type v) [AddCommGroup M] [Module C M] :
    Submodule C M where
  carrier := {m | ∃ s : C, s ∈ Q.primeCompl ∧ s • m = 0}
  zero_mem' := ⟨1, Q.primeCompl.one_mem, smul_zero 1⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, Q.primeCompl.mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = 0 := by rw [mul_comm, mul_smul, hx, smul_zero]
    have h2 : (s * t) • y = 0 := by rw [mul_smul, hy, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [smul_comm, hx, smul_zero]⟩

variable {M : Type v} [AddCommGroup M] [Module C M]

/-- An element `m` lies in `primeComplTorsion Q M` if and only if `s • m = 0` for some `s`
outside `Q`. -/
theorem mem_primeComplTorsion_iff (Q : Ideal C) [Q.IsPrime] {m : M} :
    m ∈ primeComplTorsion Q M ↔ ∃ s : C, s ∈ Q.primeCompl ∧ s • m = 0 := Iff.rfl

/-- If `primeComplTorsion Q M` is finitely generated, then it is annihilated by a single element
outside `Q`. -/
theorem exists_mem_primeCompl_smul_eq_zero (Q : Ideal C) [Q.IsPrime]
    (h : (primeComplTorsion Q M).FG) :
    ∃ g ∈ Q.primeCompl, ∀ m ∈ primeComplTorsion Q M, g • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := h
  have hwit : ∀ x ∈ s, ∃ t : C, t ∈ Q.primeCompl ∧ t • x = 0 := by
    intro x hx
    have hmem : x ∈ primeComplTorsion Q M := by
      rw [← hs]; exact Submodule.subset_span hx
    exact (mem_primeComplTorsion_iff Q).mp hmem
  choose! t ht htz using hwit
  refine ⟨∏ x ∈ s, t x, Q.primeCompl.prod_mem fun x hx => ht x hx, ?_⟩
  have hgen : ∀ x ∈ s, (∏ y ∈ s, t y) • x = 0 := by
    intro x hx
    rw [← Finset.mul_prod_erase s t hx, mul_comm, mul_smul, htz x hx, smul_zero]
  rw [← hs]
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_comm, hx, smul_zero]

/-! ### Reduction of an away-localization -/

variable {g : C}

/-- Scalar multiplication on an away-localization multiplies the numerator. -/
private lemma smul_mk (r : C) (m : M) (t : powers g) :
    r • LocalizedModule.mk m t = LocalizedModule.mk (r • m) t := by
  simp [LocalizedModule.smul'_mk]

/-- Fractions with a fixed denominator add numerator-wise. -/
private lemma mk_add_same (x y : M) (t : powers g) :
    LocalizedModule.mk (x + y) t
      = LocalizedModule.mk x t + LocalizedModule.mk y t := by
  rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [smul_add, mul_smul]

/-- A fraction whose numerator is in `J • ⊤` lies in `J • ⊤`. -/
theorem mk_mem_smul_top (J : Ideal C) {m : M} (t : powers g)
    (hm : m ∈ J • (⊤ : Submodule C M)) :
    LocalizedModule.mk m t
      ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M)) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha x _
    rw [← smul_mk]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro x y hx hy
    rw [mk_add_same]
    exact Submodule.add_mem _ hx hy

/-- Conversely, every element of `J • ⊤` in an away-localization is a fraction whose numerator
can be taken in `J • ⊤`. -/
theorem exists_mk_of_mem_smul_top (J : Ideal C)
    {ζ : LocalizedModule (powers g) M}
    (hζ : ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M))) :
    ∃ (m : M) (t : powers g), ζ = LocalizedModule.mk m t
      ∧ m ∈ J • (⊤ : Submodule C M) := by
  refine Submodule.smul_induction_on hζ ?_ ?_
  · intro a ha ξ _
    induction ξ using LocalizedModule.induction_on with
    | _ m t =>
      exact ⟨a • m, t, smul_mk a m t, Submodule.smul_mem_smul ha Submodule.mem_top⟩
  · rintro x y ⟨m₁, t₁, e₁, h₁⟩ ⟨m₂, t₂, e₂, h₂⟩
    refine ⟨(t₂ : C) • m₁ + (t₁ : C) • m₂, t₁ * t₂, ?_, ?_⟩
    · rw [e₁, e₂, LocalizedModule.mk_add_mk]
      rfl
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

/-! ### Killing the torsion by one localization -/

/-- If `r • (m / t)` lies in `J • ⊤` in an away-localization at `g ∉ Q` and `r ∉ Q`, then some
element outside `Q` carries `m` into `J • ⊤`. -/
private lemma exists_mem_primeCompl_smul_mem_of_smul_mk_mem (J : Ideal C) (Q : Ideal C)
    [Q.IsPrime] (hg : g ∈ Q.primeCompl) {r : C} (hr : r ∈ Q.primeCompl) {m : M} {t : powers g}
    (hζ : r • LocalizedModule.mk m t
      ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M))) :
    ∃ s ∈ Q.primeCompl, s • m ∈ J • (⊤ : Submodule C M) := by
  have hpow : ∀ {c : C}, c ∈ powers g → c ∈ Q.primeCompl :=
    fun hc => Submonoid.powers_le.mpr hg hc
  obtain ⟨n, t', he, hn⟩ := exists_mk_of_mem_smul_top (g := g) J hζ
  rw [smul_mk] at he
  obtain ⟨u, hueq⟩ := LocalizedModule.mk_eq.mp he
  refine ⟨(u : C) * (t' : C) * r,
    Q.primeCompl.mul_mem (Q.primeCompl.mul_mem (hpow u.2) (hpow t'.2)) hr, ?_⟩
  have h2 : ((u : C) * (t' : C)) • (r • m) = ((u : C) * (t : C)) • n := by
    rw [mul_smul, mul_smul]
    simpa only [Submonoid.smul_def] using hueq
  rw [mul_smul, h2]
  exact Submodule.smul_mem _ _ hn

/-- **One localization makes every denominator injective modulo `J`.** If the reduction
`M ⧸ J • ⊤` is a Noetherian `C`-module and `Q` is a prime of `C`, there is `g ∉ Q` such that
in `M_g` every `r ∉ Q` acts injectively modulo `J`.

This is the shrinking step of the proof of Stacks 05U7, in algebraic form. -/
theorem exists_mem_primeCompl_forall_mem_smul_top_localized
    (J : Ideal C) (Q : Ideal C) [Q.IsPrime]
    [IsNoetherian C (M ⧸ J • (⊤ : Submodule C M))] :
    ∃ g ∈ Q.primeCompl, ∀ r ∈ Q.primeCompl,
      ∀ ζ : LocalizedModule (powers g) M,
        r • ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M)) →
          ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M)) := by
  classical
  set N := J • (⊤ : Submodule C M) with hNdef
  obtain ⟨g, hg, hkill⟩ :=
    exists_mem_primeCompl_smul_eq_zero (M := M ⧸ N) Q (IsNoetherian.noetherian _)
  refine ⟨g, hg, ?_⟩
  intro r hr ζ hζ
  induction ζ using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨s, hs, hsm⟩ :=
      exists_mem_primeCompl_smul_mem_of_smul_mk_mem J Q hg hr hζ
    have htor : N.mkQ m ∈ primeComplTorsion Q (M ⧸ N) := by
      refine ⟨s, hs, ?_⟩
      rw [← map_smul]
      exact (Submodule.ker_mkQ N ▸ LinearMap.mem_ker).mp hsm
    have hgm : g • m ∈ N := by
      have hker : g • m ∈ LinearMap.ker N.mkQ :=
        LinearMap.mem_ker.mpr (by rw [map_smul]; exact hkill _ htor)
      rwa [Submodule.ker_mkQ] at hker
    -- `mk m t = mk (g • m) (g * t)`, whose numerator is in `N`
    have hgpow : g ∈ powers g := ⟨1, pow_one g⟩
    have hrw : LocalizedModule.mk m t
        = LocalizedModule.mk (g • m) ((⟨g, hgpow⟩ : powers g) * t) := by
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [mul_comm (⟨g, hgpow⟩ : powers g) t]
      rw [mul_smul]
      rfl
    rw [hrw]
    exact mk_mem_smul_top J _ hgm

/-- **Injectivity of every denominator modulo `J` survives a further localization.** The
shrinking of `exists_mem_primeCompl_forall_mem_smul_top_localized` therefore does not have to
be redone after passing to a smaller basic open, which is what lets it be composed with the
freeness input of Stacks 05MF. -/
theorem forall_mem_smul_top_localized_of_forall_mem_smul_top
    (J : Ideal C) (Q : Ideal C) [Q.IsPrime]
    (h : ∀ r ∈ Q.primeCompl, ∀ m : M,
      r • m ∈ J • (⊤ : Submodule C M) → m ∈ J • (⊤ : Submodule C M))
    {g : C} (hg : g ∈ Q.primeCompl) :
    ∀ r ∈ Q.primeCompl, ∀ ζ : LocalizedModule (powers g) M,
      r • ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M)) →
        ζ ∈ J • (⊤ : Submodule C (LocalizedModule (powers g) M)) := by
  intro r hr ζ hζ
  induction ζ using LocalizedModule.induction_on with
  | _ m t =>
    obtain ⟨s, hs, hsm⟩ := exists_mem_primeCompl_smul_mem_of_smul_mk_mem J Q hg hr hζ
    exact mk_mem_smul_top J t (h s hs m hsm)

/-- **The same conclusion in the `Submodule.mapQ` form.** This is the shape in which Stacks
05U7 and Situation 0AT0 phrase injectivity modulo an ideal: the reduction of multiplication by
`r` is `Submodule.mapQ` along it. -/
theorem exists_mem_primeCompl_forall_injective_mapQ
    (J : Ideal C) (Q : Ideal C) [Q.IsPrime]
    [IsNoetherian C (M ⧸ J • (⊤ : Submodule C M))] :
    ∃ g ∈ Q.primeCompl, ∀ r ∈ Q.primeCompl,
      Function.Injective
        (Submodule.mapQ
          (J • (⊤ : Submodule C (LocalizedModule (powers g) M)))
          (J • (⊤ : Submodule C (LocalizedModule (powers g) M)))
          (LinearMap.lsmul C (LocalizedModule (powers g) M) r)
          (Submodule.smul_top_le_comap_smul_top J
            (LinearMap.lsmul C (LocalizedModule (powers g) M) r))) := by
  obtain ⟨g, hg, hinj⟩ :=
    exists_mem_primeCompl_forall_mem_smul_top_localized (M := M) J Q
  refine ⟨g, hg, fun r hr => ?_⟩
  rw [Submodule.injective_mapQ_smul_top_iff]
  exact fun ζ hζ => hinj r hr ζ hζ

end Stacks.AwayReduction

end
