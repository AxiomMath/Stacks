module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.PicardGroup

/-!
# Inverting an element of the maximal ideal of a Noetherian local ring of dimension one

Let `R` be a Noetherian local ring of Krull dimension at most one and let `f` be an element of
its maximal ideal. The primes of `R` are then the maximal ideal together with an antichain of
minimal primes, so after inverting `f` — which lies in the maximal ideal and therefore kills
exactly that top prime — no containment between primes survives: every localization of `R` at a
submonoid containing `f` has Krull dimension zero, hence is Artinian, hence has trivial Picard
group.

The consequence drawn here is a spreading-out statement. Let `p` be a prime of a ring `A` whose
local ring `A_p` is Noetherian of dimension at most one, and let `f ∈ p`. An invertible module
over `A_f` becomes free over the ring obtained by further inverting the image of `p`, because
that ring is one of the Artinian localizations above; an invertible module is finitely presented,
so by `Module.FinitePresentation.exists_free_localizedModule_powers` it is already free over
`A_{fg}` for a single `g ∉ p`.

This is the commutative algebra behind clause (2) of
[Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA): an invertible module on a
retrocompact open `U` of a scheme becomes trivial on `V ⊓ U` for a small enough neighbourhood `V`
of a point of the complement, which is what lets it be glued to the structure sheaf of `V`.

## Main results

* `Stacks.PuncturedSpectrum.krullDimLE_zero_of_isLocalization` and
  `Stacks.PuncturedSpectrum.isArtinianRing_of_isLocalization`: a localization of a Noetherian
  local ring of Krull dimension at most one at a submonoid meeting the maximal ideal has
  dimension zero, and is Artinian.
* `Stacks.PuncturedSpectrum.free_of_invertible_of_isLocalization`: an invertible module over such
  a localization is free.
* `Stacks.PuncturedSpectrum.exists_notMem_free_localizedModule_away` and
  `Stacks.PuncturedSpectrum.exists_notMem_free_of_isLocalizedModule`: the spreading-out
  statement above, for the canonical localization and for an arbitrary model of it.

## Implementation notes

No hypothesis beyond `f ∈ maximalIdeal R` is needed for the dimension-zero conclusion. In
particular `f` is not required to cut out the closed point: a prime of `R` not containing `f` is
automatically minimal, because it is not the maximal ideal, the maximal ideal is the only maximal
ideal, and `Ring.krullDimLE_one_iff` leaves no third possibility.

The two localizations `A_f → (A_f)_{p}` and `A_p → (A_p)_f` of the spreading-out statement are
realized as a single localization of `A`, at
`IsLocalization.localizationLocalizationSubmodule (Submonoid.powers f)
(p.primeCompl.map (algebraMap A A_f))`, so that `IsLocalization.isLocalization_of_submonoid_le`
presents it over `A_p` and `IsLocalization.localization_localization_isLocalization` presents it
over `A_f`. The `A_p`-algebra structure is the lift of `A → (A_f)_p` along `A → A_p`, which
exists because every element of `p.primeCompl` is already invertible there.

The degenerate case is real and is handled separately: if some `g ∉ p` has zero image in `A_f`
then `(A_f)_p` is the zero ring, `Module.FinitePresentation.exists_free_localizedModule_powers`
does not apply, and that `g` is returned directly — every module over the zero ring is free.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.PuncturedSpectrum

section Artinian

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  (L : Submonoid R) {f : R} (hfL : f ∈ L) (hf : f ∈ maximalIdeal R)
  (T : Type u) [CommRing T] [Algebra R T] [IsLocalization L T]

omit [IsNoetherianRing R] in
include hfL hf in
/-- **Inverting an element of the maximal ideal of a Noetherian local ring of dimension at most
one leaves no containments between primes.** A prime of the localization contracts to a prime of
`R` not containing `f`, hence not the maximal ideal, hence — `R` being local of dimension at most
one — a minimal prime of `R`; so it cannot be strictly contained in another such prime. -/
theorem krullDimLE_zero_of_isLocalization : Ring.KrullDimLE 0 T := by
  refine Ring.KrullDimLE.mk₀ fun Q hQ => ?_
  obtain ⟨M, hM, hQM⟩ := Q.exists_le_maximal hQ.ne_top
  have hunit : IsUnit (algebraMap R T f) := IsLocalization.map_units T ⟨f, hfL⟩
  have hnotMem : f ∉ M.under R := fun hfM =>
    hM.ne_top (M.eq_top_of_isUnit_mem hfM hunit)
  have hmne : M.under R ≠ maximalIdeal R := fun h => hnotMem (h ▸ hf)
  have hMp : (M.under R).IsPrime := Ideal.IsPrime.under R M
  have hmmin : M.under R ∈ minimalPrimes R := by
    rcases Ring.krullDimLE_one_iff.mp ‹Ring.KrullDimLE 1 R› (M.under R) hMp with h | h
    · exact h
    · exact absurd (eq_maximalIdeal h) hmne
  have hle : Q.under R ≤ M.under R := Ideal.comap_mono hQM
  have heq : Q.under R = M.under R :=
    le_antisymm hle (hmmin.2 ⟨Ideal.IsPrime.under R Q, bot_le⟩ hle)
  have : Q = M := by
    rw [← IsLocalization.map_under L T Q, ← IsLocalization.map_under L T M, heq]
  exact this ▸ hM

include hfL hf in
/-- **Such a localization is Artinian**: it is Noetherian, being a localization of a Noetherian
ring, and of dimension zero by `krullDimLE_zero_of_isLocalization`. -/
theorem isArtinianRing_of_isLocalization : IsArtinianRing T := by
  have : IsNoetherianRing T := IsLocalization.isNoetherianRing L T ‹_›
  have := krullDimLE_zero_of_isLocalization R L hfL hf T
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

include hfL hf in
/-- **An invertible module over such a localization is free.** An Artinian ring has finitely many
maximal ideals, and the Picard group of a ring with finitely many maximal ideals is trivial. -/
theorem free_of_invertible_of_isLocalization (M : Type u) [AddCommGroup M] [Module T M]
    [Module.Invertible T M] : Module.Free T M := by
  have := isArtinianRing_of_isLocalization R L hfL hf T
  infer_instance

end Artinian

section SpreadingOut

variable (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime] {f : A} (hf : f ∈ p)
  (Ap : Type u) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p]
  [IsNoetherianRing Ap] [Ring.KrullDimLE 1 Ap]
  (Af : Type u) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]

/-- The submonoid of `A_f` generated by the image of the complement of `p`: inverting it produces
the local ring of `A_f` "at `p`", which is the punctured spectrum of `A_p` when `f` cuts out the
closed point. -/
private def awaySubmonoid : Submonoid Af := p.primeCompl.map (algebraMap A Af)

private lemma mem_awaySubmonoid {g : A} (hg : g ∉ p) :
    algebraMap A Af g ∈ awaySubmonoid A p Af :=
  ⟨g, hg, rfl⟩

include hf Ap in
/-- **The spreading-out statement.** Let `p` be a prime of `A` with `A_p` Noetherian of Krull
dimension at most one and let `f ∈ p`. Then an invertible `A_f`-module is free after inverting a
single element outside `p`.

Inverting the image of `p.primeCompl` in `A_f` gives an Artinian ring by
`isArtinianRing_of_isLocalization`, over which the module becomes free; an invertible module is
finite and projective, hence finitely presented, so freeness descends to a finite stage by
`Module.FinitePresentation.exists_free_localizedModule_powers`. -/
theorem exists_notMem_free_localizedModule_away
    (M : Type u) [AddCommGroup M] [Module Af M] [Module.Invertible Af M] :
    ∃ g ∉ p, Module.Free (Localization.Away (algebraMap A Af g))
      (LocalizedModule.Away (algebraMap A Af g) M) := by
  classical
  have : IsLocalRing Ap := IsLocalization.AtPrime.isLocalRing Ap p
  set S : Submonoid Af := awaySubmonoid A p Af with hS
  by_cases hzero : (0 : Af) ∈ S
  · obtain ⟨g, hg, hg0⟩ := hzero
    refine ⟨g, hg, ?_⟩
    have : Subsingleton (Localization.Away (algebraMap A Af g)) := by
      rw [hg0]
      exact IsLocalization.subsingleton (M := Submonoid.powers (0 : Af)) ⟨1, pow_one 0⟩
    exact Module.Free.of_subsingleton' _ _
  -- The further localization of `A_f`, presented over `A`, over `A_f` and over `A_p`.
  let T : Type u := Localization S
  have : IsScalarTower A Af T := IsScalarTower.of_algebraMap_eq' rfl
  have hTA : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule (Submonoid.powers f) S) T :=
    IsLocalization.localization_localization_isLocalization (Submonoid.powers f) S T
  set N : Submonoid A :=
    IsLocalization.localizationLocalizationSubmodule (Submonoid.powers f) S with hN
  have hprimeCompl : p.primeCompl ≤ N := by
    intro x hx
    exact IsLocalization.mem_localizationLocalizationSubmodule.mpr
      ⟨⟨algebraMap A Af x, mem_awaySubmonoid A p Af hx⟩, 1, by simp⟩
  have hfN : f ∈ N :=
    IsLocalization.mem_localizationLocalizationSubmodule.mpr
      ⟨1, ⟨f, Submonoid.mem_powers f⟩, by simp⟩
  -- `T` is an `A_p`-algebra: the elements of `p.primeCompl` are already units in `T`.
  have hlift : ∀ y : p.primeCompl, IsUnit (algebraMap A T (y : A)) :=
    fun y => IsLocalization.map_units T ⟨(y : A), hprimeCompl y.2⟩
  let : Algebra Ap T := (IsLocalization.lift (M := p.primeCompl) hlift).toAlgebra
  have : IsScalarTower A Ap T := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := p.primeCompl) hlift x).symm
  have hTAp : IsLocalization (N.map (algebraMap A Ap)) T :=
    IsLocalization.isLocalization_of_submonoid_le Ap T p.primeCompl N hprimeCompl
  -- Hence `T` is Artinian, and the localized module is free over it.
  have : Nontrivial T := by
    refine ⟨⟨1, 0, fun h => hzero ?_⟩⟩
    have h' : algebraMap Af T 1 = algebraMap Af T 0 := by simpa using h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S T).mp h'
    have hc0 : (c : Af) = 0 := by simpa using hc
    exact hc0 ▸ c.2
  have : IsArtinianRing T :=
    isArtinianRing_of_isLocalization Ap (N.map (algebraMap A Ap))
      (Submonoid.mem_map_of_mem _ hfN)
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p f).mpr hf) T
  have : Module.FinitePresentation Af M := Module.finitePresentation_of_projective _ _
  obtain ⟨r, hrS, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers S
      (LocalizedModule.mkLinearMap S M) T
  obtain ⟨g, hg, rfl⟩ := hrS
  exact ⟨g, hg, hfree⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness of the localization of a module away from an element is independent of the model of
that localization. This is the `Away` companion of Mathlib's
`Module.mem_freeLocus_of_isLocalization`, proved the same way: the two localized rings are
identified by `IsLocalization.algEquiv` and the two localized modules by
`IsLocalizedModule.iso`, and `Module.Free.iff_of_equiv` transports freeness along the pair. -/
theorem free_iff_of_isLocalizedModule {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (r : R) (Rr Mr : Type u) [CommRing Rr] [Algebra R Rr]
    [IsLocalization.Away r Rr] [AddCommGroup Mr] [Module R Mr]
    (l : M →ₗ[R] Mr) [IsLocalizedModule (Submonoid.powers r) l]
    [Module Rr Mr] [IsScalarTower R Rr Mr] :
    Module.Free (Localization.Away r) (LocalizedModule.Away r M) ↔ Module.Free Rr Mr := by
  set e := (IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) Rr).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso (Submonoid.powers r) l, map_smul' := ?_ }
  intro a x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) a
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units l s)).1
  simp [e, ← map_smul, ← smul_assoc]

include hf Ap in
/-- **The spreading-out statement, for an arbitrary model of the localization.** The content is
`exists_notMem_free_localizedModule_away`; the conclusion is stated for any ring and module
presented as the localization away from the image of `g`, which is the form a scheme-theoretic
consumer holds, where that ring is the sections over a basic open. -/
theorem exists_notMem_free_of_isLocalizedModule
    (M : Type u) [AddCommGroup M] [Module Af M] [Module.Invertible Af M] :
    ∃ g ∉ p, ∀ (B Mg : Type u) [CommRing B] [Algebra Af B]
      [IsLocalization.Away (algebraMap A Af g) B]
      [AddCommGroup Mg] [Module Af Mg] [Module B Mg] [IsScalarTower Af B Mg]
      (l : M →ₗ[Af] Mg)
      [IsLocalizedModule (Submonoid.powers (algebraMap A Af g)) l],
      Module.Free B Mg := by
  obtain ⟨g, hg, hfree⟩ := exists_notMem_free_localizedModule_away A p hf Ap Af M
  refine ⟨g, hg, fun B Mg _ _ _ _ _ _ _ l _ => ?_⟩
  exact (free_iff_of_isLocalizedModule _ B Mg l).mp hfree

end SpreadingOut

end Stacks.PuncturedSpectrum

end
