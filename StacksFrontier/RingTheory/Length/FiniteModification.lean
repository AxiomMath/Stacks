module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Distance
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# A finite modification of a one-dimensional Noetherian local ring

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring and let `A ⊆ B` be a finite ring
extension with `B / A` annihilated by a power of `𝔪` and with `𝔪` not an associated prime of
`B` — the hypotheses of Stacks 0EAT. This file records the consequences a length computation
over such an extension needs:

* a nonzerodivisor of `A` stays a nonzerodivisor on `B`;
* `B / A` has finite length;
* `length_A(A / aA) = length_A(B / aB)` for such a nonzerodivisor,

and combines the last with `StacksFrontier.RingTheory.Length.SemilocalDecomposition` into

`ord_A(a) = ∑_𝔮 [κ(𝔮) : κ(𝔪)] ord_{B_𝔮}(a)`,

the length identity underlying the norm compatibility of tame symbols, Stacks 0EAT.

## Main results

* `Stacks.Length.height_maximalIdeal_eq_one` — the maximal ideal has height one.
* `Stacks.Length.isSMulRegular_of_not_isAssociatedPrime` — a nonzerodivisor of `A` acts
  injectively on a module with `𝔪` not an associated prime.
* `Stacks.Length.length_ne_top_of_isTorsionBy_nonZeroDivisor` — a finite module killed by a
  nonzerodivisor has finite length.
* `Stacks.Length.length_quotient_span_eq` — `length_A(A / aA) = length_A(B / aB)`.
* `Stacks.Length.length_localizedModule_quotient_span_eq` — the localization of `B / aB` at a
  prime `𝔮` is `B_𝔮 / aB_𝔮`.
* `Stacks.Length.ord_eq_sum_finrank_mul_ord` — the length identity.

## Implementation notes

**Already in the library, and not reused.** `StacksFrontier.RingTheory.Length.Finiteness`
proves `stacks_00J0`, that a finite module killed by a power of a finitely generated maximal
ideal has finite length, which is exactly
`Stacks.Length.length_ne_top_of_isTorsionBy_nonZeroDivisor` would need to be replaced by here —
and in a form that would also remove the unit/non-unit split in
`Stacks.Length.ord_eq_sum_finrank_mul_ord`. It is not imported because that module's own imports
include `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`,
`Mathlib.Combinatorics.Enumerative.DyckWord` and a dozen more unrelated files, so importing it
from a commutative-algebra module would put all of analysis on the critical path of the tame
symbol. `StacksFrontier.RingTheory.Length.Comparison` proves `length_le_length_restrictScalars`
(Stacks 00IX (1)), which is `Stacks.Length.length_le_length_restrictScalars` here, but with the
`R`-module structure supplied as `Module.compHom M φ` rather than as an ambient
`[Module A M] [IsScalarTower A R M]`, so it does not apply to a module that already carries both
structures. Both are dedup debt for a repo-tier pass, recorded rather than silently duplicated.

The identity `length_A(A / aA) = length_A(B / aB)` is usually read off the snake lemma applied to
multiplication by `a` on `0 → A → B → B/A → 0`. It is obtained here without a snake lemma, from
`Module.length_quotient_map_of_injective` applied twice: once along `A → B`, which computes
`length_A(B / a·A·B)` as `length_A(A / aA) + length_A(B/A)`, and once along multiplication by `a`
on `B`, which computes the same length as `length_A(B/A) + length_A(B / aB)`. Cancelling the
finite length of `B / A` gives the identity.

## References

* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Stacks.Length

section Regular

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]

/-- The maximal ideal of a one-dimensional local ring has height at most one. -/
private theorem height_maximalIdeal_le_one (R : Type u) [CommRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] : (maximalIdeal R).height ≤ 1 := by
  have h := (Ideal.height_le_ringKrullDim_of_isPrime (I := maximalIdeal R)).trans
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R))
  exact_mod_cast h

/-- An ideal containing a nonzerodivisor has height at least one. -/
private theorem one_le_height_of_mem_nonZeroDivisors {R : Type u} [CommRing R] {p : Ideal R}
    {a : R} (ha : a ∈ nonZeroDivisors R) (hap : a ∈ p) : (1 : ℕ∞) ≤ p.height :=
  le_trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha)
    (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).mpr hap))

omit [IsNoetherianRing A] in
/-- **In a one-dimensional Noetherian local ring every prime containing a nonzerodivisor is the
maximal ideal.** Such a prime has height at least one, and the maximal ideal has height at most
the Krull dimension, namely one. -/
theorem eq_maximalIdeal_of_mem_of_isPrime (p : Ideal A) [hp : p.IsPrime] {a : A}
    (ha : a ∈ nonZeroDivisors A) (hap : a ∈ p) : p = maximalIdeal A := by
  have hmle : (maximalIdeal A).height ≤ 1 := height_maximalIdeal_le_one A
  have hple : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  have hpfin : p.FiniteHeight :=
    ⟨Or.inr (ne_top_of_le_ne_top (show (1 : ℕ∞) ≠ ⊤ by simp)
      ((Ideal.height_mono hple).trans hmle))⟩
  exact Ideal.eq_of_le_of_height_le (I := p) hple
    (hmle.trans (one_le_height_of_mem_nonZeroDivisors ha hap))

omit [IsNoetherianRing A] in
/-- **The maximal ideal of a one-dimensional Noetherian local ring containing a nonzerodivisor
has height one.** It has height at most the Krull dimension, and at least one because it
contains a nonzerodivisor. -/
theorem height_maximalIdeal_eq_one {a : A} (ha : a ∈ nonZeroDivisors A)
    (ham : a ∈ maximalIdeal A) : (maximalIdeal A).height = 1 :=
  le_antisymm (height_maximalIdeal_le_one A) (one_le_height_of_mem_nonZeroDivisors ha ham)

/-- **A nonzerodivisor of `A` acts injectively on a module without `𝔪` as an associated
prime.** If it did not, it would lie in an associated prime of the module, and in a
one-dimensional ring a prime containing a nonzerodivisor is the maximal ideal. -/
theorem isSMulRegular_of_not_isAssociatedPrime {M : Type v} [AddCommGroup M] [Module A M]
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) M) {a : A} (ha : a ∈ nonZeroDivisors A) :
    IsSMulRegular M a := by
  have key : ∀ x : M, a • x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have hmem : a ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors A M]
      exact ⟨x, hx0, hx⟩
    obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp hmem
    have : p.IsPrime := hp.isPrime
    exact hass (eq_maximalIdeal_of_mem_of_isPrime p ha hap ▸ hp)
  intro x y hxy
  refine sub_eq_zero.mp (key _ ?_)
  rw [smul_sub]
  exact sub_eq_zero.mpr hxy

end Regular

section FiniteLength

/-- **A finite module killed by a nonzerodivisor of a one-dimensional Noetherian ring has finite
length.** The module is finite over `A / aA`, which is Artinian because `A / aA` has finite
length over `A`. -/
@[ega "IV 21.10.13" "more general"]
theorem length_ne_top_of_isTorsionBy_nonZeroDivisor
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {Q : Type v} [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    {a : A} (ha : a ∈ nonZeroDivisors A) (haQ : ∀ x : Q, a • x = 0) :
    Module.length A Q ≠ ⊤ := by
  have hfl : IsFiniteLength A (A ⧸ Ideal.span {a}) := isFiniteLength_quotient_span_singleton A ha
  obtain ⟨-, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  have hartring : IsArtinianRing (A ⧸ Ideal.span {a}) := isArtinian_of_tower A hart
  have htors : Module.IsTorsionBySet A Q ((Ideal.span {a} : Ideal A) : Set A) := by
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    intro r hr
    rw [SetLike.mem_coe, Module.mem_annihilator]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    intro x
    rw [mul_smul, haQ x, smul_zero]
  let : Module (A ⧸ Ideal.span {a}) Q := htors.module
  let : IsScalarTower A (A ⧸ Ideal.span {a}) Q := htors.isScalarTower
  have : Module.Finite (A ⧸ Ideal.span {a}) Q := Module.Finite.of_restrictScalars_finite A _ Q
  have : IsArtinian A Q := isArtinian_of_surjective_algebraMap (S := A)
    (R := A ⧸ Ideal.span {a}) (by rw [Ideal.Quotient.algebraMap_eq]
                                  exact Ideal.Quotient.mk_surjective)
  exact Module.length_ne_top

end FiniteLength

section Modification

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The image of `aA` in `B` is the image of `A` multiplied by `a`. -/
private theorem map_span_eq_map_lsmul (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    [Algebra A B] (a : A) :
    Submodule.map (Algebra.linearMap A B) (Ideal.span {a} : Ideal A) =
      Submodule.map (LinearMap.lsmul A B a) (LinearMap.range (Algebra.linearMap A B)) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine Submodule.mem_map.mpr ⟨algebraMap A B c, ⟨c, rfl⟩, ?_⟩
    simp only [LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def, map_mul]
    ring
  · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨c, rfl⟩ := hy
    refine Submodule.mem_map.mpr ⟨c * a, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, ?_⟩
    simp only [LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def, map_mul]
    ring

/-- Multiplication by `a : A` on `B` has range the ideal generated by the image of `a`. -/
private theorem range_lsmul_eq_restrictScalars_span (A : Type u) [CommRing A] (B : Type v)
    [CommRing B] [Algebra A B] (a : A) :
    LinearMap.range (LinearMap.lsmul A B a) =
      (Ideal.span {algebraMap A B a} : Ideal B).restrictScalars A := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, rfl⟩ := hx
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    simp only [LinearMap.lsmul_apply, Algebra.smul_def]
    ring
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    refine ⟨c, ?_⟩
    simp only [LinearMap.lsmul_apply, Algebra.smul_def]
    rw [mul_comm]
    exact hc

/-- **The length of `A / aA` is unchanged by a finite modification with cokernel of finite
length.** Computing the length of `B / a·A·B` along the inclusion `A ⊆ B` gives
`length_A(A / aA) + length_A(B/A)`, and computing it along multiplication by `a` on `B` gives
`length_A(B/A) + length_A(B / aB)`. -/
theorem length_quotient_span_eq {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    (hQ : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≠ ⊤)
    {a : A} (haB : IsSMulRegular B a) :
    Module.length A (A ⧸ (Ideal.span {a} : Ideal A)) =
      Module.length A (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) := by
  have hinj' : Function.Injective (Algebra.linearMap A B) := hinj
  have h1 := Module.length_quotient_map_of_injective hinj' (Ideal.span {a} : Ideal A)
  have h2 := Module.length_quotient_map_of_injective (f := LinearMap.lsmul A B a) haB
    (LinearMap.range (Algebra.linearMap A B))
  rw [map_span_eq_map_lsmul A B a] at h1
  have h4 : Module.length A (B ⧸ LinearMap.range (LinearMap.lsmul A B a)) =
      Module.length A (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) := by
    rw [range_lsmul_eq_restrictScalars_span A B a,
      (Submodule.Quotient.restrictScalarsEquiv A
        (Ideal.span {algebraMap A B a} : Ideal B)).length_eq]
  rw [h4] at h2
  exact WithTop.add_left_cancel hQ ((add_comm _ _).trans (h1.symm.trans h2))

end Modification

section Localized

/-- **The localization of `B / aB` at a prime is `B_𝔮 / aB_𝔮`.** Localization is exact, so it
carries the presentation of `B / aB` to the presentation of `B_𝔮 / aB_𝔮`. -/
theorem length_localizedModule_quotient_span_eq {B : Type v} [CommRing B] (q : Ideal B)
    [q.IsPrime] (b : B) :
    Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (B ⧸ (Ideal.span {b} : Ideal B))) =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸
          (Ideal.span {algebraMap B (Localization.AtPrime q) b} :
            Ideal (Localization.AtPrime q))) := by
  set p := q.primeCompl with hp
  set Bq := Localization.AtPrime q with hBq
  have hsub : Submodule.localized' Bq p (Algebra.linearMap B Bq) (Ideal.span {b})
      = Ideal.span {algebraMap B Bq b} := by
    rw [Submodule.localized'_span]
    simp [Algebra.linearMap_apply, Ideal.span]
  have e : LocalizedModule p (B ⧸ (Ideal.span {b} : Ideal B)) ≃ₗ[B]
      (Bq ⧸ Submodule.localized' Bq p (Algebra.linearMap B Bq) (Ideal.span {b})) :=
    IsLocalizedModule.iso p
      (Submodule.toLocalizedQuotient' Bq p (Algebra.linearMap B Bq) (Ideal.span {b}))
  have e' : LocalizedModule p (B ⧸ (Ideal.span {b} : Ideal B)) ≃ₗ[Bq]
      (Bq ⧸ Submodule.localized' Bq p (Algebra.linearMap B Bq) (Ideal.span {b})) :=
    LinearEquiv.extendScalarsOfIsLocalization p Bq e
  rw [LinearEquiv.length_eq e', hsub]

end Localized

section Formula

open IsLocalRing

/-- **The length over a larger ring is at most the length over a smaller one**: the lattice of
submodules over the larger ring embeds in the lattice over the smaller. -/
theorem length_le_length_restrictScalars (A : Type*) [Ring A] (R : Type*) [Ring R] [SMul A R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] :
    Module.length R M ≤ Module.length A M := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (Submodule.restrictScalarsEmbedding A R M)

/-- A unit has order of vanishing zero: the quotient by the unit ideal is trivial. Kept private
because `Stacks.Chow.ord_eq_zero_of_isUnit`
(`StacksFrontier/AlgebraicGeometry/Chow/KeyLemma/TameSymbolOrder.lean`) is the same statement, one
`omit` away from this generality; a second public copy would be dedup debt, and importing a
`Chow` module into `RingTheory` to reuse it would invert the layering. -/
private theorem ord_eq_zero_of_isUnit {R : Type u} [CommRing R] {x : R} (hx : IsUnit x) :
    Ring.ord R x = 0 := by
  rw [Ring.ord, Ideal.span_singleton_eq_top.mpr hx]
  simp [Module.length_eq_zero]

/-- **The length identity behind Stacks 0EAT.** For a one-dimensional Noetherian local ring `A`
and a finite ring extension `A ⊆ B` with `B / A` annihilated by a power of `𝔪` and `𝔪` not an
associated prime of `B`, the order of vanishing of a nonzerodivisor `a` of `A` is the sum over
the maximal ideals of `B` of the residue degree times the order of vanishing of `a` in `B_𝔮`.

Both sides are `0` when `a` is a unit. Otherwise `a ^ n` is a nonzerodivisor in `𝔪 ^ n`, so
`B / A` has finite length, so `length_A(A / aA) = length_A(B / aB)`; the semilocal
decomposition of `B / aB` turns the latter into the sum. -/
theorem ord_eq_sum_finrank_mul_ord
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    {a : A} (ha : a ∈ nonZeroDivisors A) :
    Ring.ord A a =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (ResidueField A)
            (ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
          Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap A (Localization.AtPrime q.asIdeal) a) := by
  classical
  by_cases hu : IsUnit a
  · rw [ord_eq_zero_of_isUnit hu]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    rw [ord_eq_zero_of_isUnit (hu.map (algebraMap A (Localization.AtPrime q.asIdeal))), mul_zero]
  have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr hu
  obtain ⟨n, hn⟩ := hquot
  have haB : IsSMulRegular B a := isSMulRegular_of_not_isAssociatedPrime hass ha
  have hfiniteQ : Module.Finite A (B ⧸ LinearMap.range (Algebra.linearMap A B)) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have hQ : Module.length A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ≠ ⊤ := by
    refine length_ne_top_of_isTorsionBy_nonZeroDivisor (a := a ^ n) (pow_mem ha n) fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (Algebra.linearMap A B)) x
    rw [← LinearMap.map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (hn (Submodule.smul_mem_smul (Ideal.pow_mem_pow ham n) Submodule.mem_top))
  have hlen : Ring.ord A a =
      Module.length A (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) :=
    length_quotient_span_eq hinj hQ haB
  have hMne : Module.length A (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) ≠ ⊤ := by
    rw [← hlen]; exact Ring.ord_ne_top ha
  have hartA : IsArtinian A (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hMne)).2
  have hartB : IsArtinian B (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B)) :=
    isArtinian_of_tower A hartA
  have hsum := length_eq_sum_length_localizedModule (A := A) (B := B)
    (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B))
  have hfin : ∀ q : MaximalSpectrum B,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B))) ≠ ⊤ := by
    intro q
    have hA : Module.length A (LocalizedModule q.asIdeal.primeCompl
        (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hMne ?_
      rw [hsum]
      exact Finset.single_le_sum
        (f := fun q' : MaximalSpectrum B => Module.length A (LocalizedModule q'.asIdeal.primeCompl
          (B ⧸ (Ideal.span {algebraMap A B a} : Ideal B))))
        (fun _ _ => zero_le) (Finset.mem_univ q)
    exact ne_top_of_le_ne_top hA (length_le_length_restrictScalars A _ _)
  rw [hlen, length_eq_sum_finrank_mul_length_localizedModule _ hfin]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [length_localizedModule_quotient_span_eq q.asIdeal (algebraMap A B a),
    ← IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal) a,
    show Ring.ord (Localization.AtPrime q.asIdeal)
        (algebraMap A (Localization.AtPrime q.asIdeal) a) =
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⧸
          (Ideal.span {algebraMap A (Localization.AtPrime q.asIdeal) a} :
            Ideal (Localization.AtPrime q.asIdeal))) from rfl]

end Formula

end Stacks.Length

end
