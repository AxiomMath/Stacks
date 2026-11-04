module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.StacksAttribute

/-! ## Prime Spectrum Topology -/

add_to_stacks 00DZ PrimeSpectrum.basicOpen
add_to_stacks 00E0 "11" PrimeSpectrum.basicOpen_eq_zeroLocus_compl
add_to_stacks 00E0 "12" PrimeSpectrum.basicOpen_eq_bot_iff
add_to_stacks 00E0 "15" PrimeSpectrum.basicOpen_mul
add_to_stacks 00E1 PrimeSpectrum.zariskiTopology
add_to_stacks 00E2 PrimeSpectrum.comap
add_to_stacks 00E2 PrimeSpectrum.comap_basicOpen
add_to_stacks 00E3 PrimeSpectrum.localization_comap_isInducing
add_to_stacks 00E4 PrimeSpectrum.localization_away_isOpenEmbedding
add_to_stacks 00E5 PrimeSpectrum.isClosedEmbedding_comap_of_surjective
add_to_stacks 00E8 PrimeSpectrum.compactSpace
add_to_stacks 00ED PrimeSpectrum.primeSpectrumProdHomeo
add_to_stacks 00ED "for an arbitrary finite product" PrimeSpectrum.sigmaToPiHomeo
add_to_stacks 04PM PrimeSpectrum.instSpectralSpace

@[expose] public section

variable {R : Type*} [CommSemiring R]

namespace PrimeSpectrum

open TopologicalSpace

@[stacks 00E0 "17"]
theorem basicOpen_eq_top_iff_isUnit {f : R} :
    basicOpen f = ⊤ ↔ IsUnit f := by
  rw [← Ideal.span_singleton_eq_top, ← zeroLocus_empty_iff_eq_top, zeroLocus_span,
    ← TopologicalSpace.Opens.coe_eq_univ, basicOpen_eq_zeroLocus_compl, Set.compl_univ_iff]

@[stacks 00E0 "13", ega "I 1.1.9" "last clause"]
theorem basicOpen_eq_of_unit_mul {f f' u : R} (hu : IsUnit u) (h : f = u * f') :
    basicOpen f = basicOpen f' := by
  rw [h, basicOpen_mul, basicOpen_eq_top_iff_isUnit.mpr hu, top_inf_eq]

@[stacks 00E0 "14"]
theorem exists_basicOpen_disjoint_zeroLocus {I : Ideal R} {p : PrimeSpectrum R}
    (hp : p ∉ zeroLocus (I : Set R)) : ∃ f : R, p ∈ basicOpen f ∧
      (basicOpen f : Set (PrimeSpectrum R)) ∩ zeroLocus (I : Set R) = ∅ := by
  rw [mem_zeroLocus] at hp
  obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hp
  refine ⟨f, (mem_basicOpen f p).mpr hfp, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro q ⟨hqf, hqI⟩
  rw [mem_zeroLocus] at hqI
  exact (mem_basicOpen f q).mp hqf (hqI hfI)

@[stacks 00E0 "16"]
theorem iUnion_basicOpen_eq_compl_zeroLocus {ι : Type*} (f : ι → R) :
    (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))) = (zeroLocus (Set.range f))ᶜ := by
  simp [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter, ← zeroLocus_iUnion]

attribute [local grind =] mul_zero add_zero basicOpen_zero basicOpen_one Opens.coe_bot
  Opens.coe_top Opens.coe_eq_empty in
attribute [local grind .] Set.univ_eq_empty_iff basicOpen_eq_zeroLocus_compl isClopen_compl_iff in
/-- **Stacks 00EF**, in its most general form. Over a semiring the statement must be phrased with
*complementary pairs* rather than idempotents: an idempotent need not have a complement, so
"every idempotent is `0` or `1`" is strictly stronger than preconnectedness there. Mathlib's own
example, on `PrimeSpectrum.mulZeroAddOneEquivClopens`, is the semiring `{0, 0.5, 1}` with `⊔ = +`
and `⊓ = *`, in which `0.5` is idempotent and uncomplemented.

Pairs `e * f = 0`, `e + f = 1` are exactly what index the clopens of `Spec R`, which is why this
is the level at which the equivalence is true. -/
@[stacks 00EF "for a semiring, phrased with complementary pairs"]
theorem preconnectedSpace_iff_mul_eq_zero_add_eq_one :
    PreconnectedSpace (PrimeSpectrum R) ↔
      ∀ e f : R, e * f = 0 → e + f = 1 → e = 0 ∨ f = 0 := by
  rw [preconnectedSpace_iff_clopen]
  refine ⟨fun h e f mul add ↦ ?_, fun h s hs ↦ ?_⟩
  · obtain ⟨he, hf⟩ := IsIdempotentElem.of_mul_add mul add
    refine (h _ (isClopen_basicOpen_of_mul_add e f mul add)).casesOn
      (fun hs ↦ Or.inl ?_) (fun hs ↦ Or.inr ?_)
    <;> exact IsIdempotentElem.eq_zero_of_isNilpotent (by assumption) <|
      basicOpen_eq_bot_iff _|>.1 <| by grind [zeroLocus_eq_basicOpen_of_mul_add, Set.compl_univ]
  · obtain ⟨e, f, mul, add, rfl⟩ := isClopen_iff_mul_add.1 hs
    grind

section CommRing

variable {R : Type*} [CommRing R]

/-- **Stacks 00EF** without the nonzero hypothesis. Over a ring every idempotent `e` has the
complement `1 - e`, so the pair formulation collapses to the familiar one.

This form needs no `Nontrivial R`: for the zero ring `Spec R` is empty, hence preconnected, and
the right-hand side holds vacuously. It is `ConnectedSpace` — which bundles nonemptiness — that
forces the hypothesis, see `connectedSpace_iff_isIdempotentElem`. -/
@[stacks 00EF "without the nonzero hypothesis, for `PreconnectedSpace`"]
theorem preconnectedSpace_iff_isIdempotentElem :
    PreconnectedSpace (PrimeSpectrum R) ↔ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [preconnectedSpace_iff_mul_eq_zero_add_eq_one]
  refine ⟨fun h e he ↦ (h e (1 - e) ?_ ?_).casesOn ?_ ?_, fun h e f mul add ↦
    (h e (IsIdempotentElem.of_mul_add mul add).1).casesOn ?_ ?_⟩
  <;> grind [isIdempotentElem_iff]

/-- **Stacks 00EF**: for a nonzero ring, `Spec R` is connected if and only if `R` has no
nontrivial idempotents.

The `Nontrivial R` hypothesis is load-bearing and not merely inherited from the tag's wording:
for the zero ring the right-hand side holds vacuously while `Spec R` is empty, so `ConnectedSpace`
fails. Dropping it would make the statement false, not weaker. -/
@[stacks 00EF]
theorem connectedSpace_iff_isIdempotentElem [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [← preconnectedSpace_iff_isIdempotentElem]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

/-- **Stacks 00EH**, clause (3): the vanishing locus of a finitely generated idempotent ideal is
open as well as closed.

Only one implication holds. `I.FG` cannot be dropped — in a rank-one non-discrete valuation ring
the maximal ideal satisfies `m * m = m` without being finitely generated, and `V(m)` is closed but
not open — and there is no converse: for `I = (x)` in `k[x]/(x²)` the set `V(I)` is all of
`Spec R`, hence clopen, while `I * I = 0 ≠ I`. -/
@[stacks 00EH "(3)"]
theorem isClopen_zeroLocus_of_isIdempotentElem_of_fg {I : Ideal R} (hfg : I.FG)
    (h : IsIdempotentElem I) : IsClopen (zeroLocus (I : Set R)) := by
  obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg hfg).mp h
  rw [Ideal.submodule_span_eq, zeroLocus_span]
  exact isClopen_iff_zeroLocus.mpr ⟨e, he, rfl⟩

end CommRing

end PrimeSpectrum

open PrimeSpectrum IsLocalRing
/-- **Stacks 00E9**, clause (1) ⇔ (2): a ring is local if and only if its spectrum has exactly
one closed point.

The clause is genuinely topological, so it is stated that way rather than as uniqueness of a
maximal ideal. `PrimeSpectrum.isClosed_singleton_iff_isMaximal` is what converts between the
two, in both directions; the rest is transport between `PrimeSpectrum R` and `Ideal R` along
`PrimeSpectrum.ext`.

No nontriviality hypothesis is needed: for the zero ring the spectrum is empty, so it has no
closed point at all and clause (2) fails on its own. -/
@[stacks 00E9 "(1) ⇔ (2)"]
theorem isLocalRing_iff_existsUnique_isClosed_singleton {R : Type*} [CommSemiring R] :
    IsLocalRing R ↔ ∃! p : PrimeSpectrum R, IsClosed ({p} : Set (PrimeSpectrum R)) := by
  simp only [isClosed_singleton_iff_isMaximal]
  refine ⟨fun _ ↦ ?_, fun ⟨p, hp, huniq⟩ ↦ of_unique_max_ideal ⟨_, hp, fun m hm ↦
    congr(PrimeSpectrum.asIdeal $(huniq ⟨m, hm.isPrime⟩ hm))⟩⟩
  have hm := maximalIdeal.isMaximal R
  exact ⟨⟨maximalIdeal R, hm.isPrime⟩, hm, fun q hq =>
    PrimeSpectrum.ext ((maximal_ideal_unique R).unique hq hm)⟩
