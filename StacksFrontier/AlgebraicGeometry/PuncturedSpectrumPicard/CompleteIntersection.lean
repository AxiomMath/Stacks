module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.PuncturedSpectrumCompletion
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PuncturedSpectrumRegular
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.ExtensionAcrossPoint
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatLocalHomomorphism
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.Defs

/-!
# The Picard group of the punctured spectrum of a complete intersection

Let `(A, 𝔪)` be a Noetherian local ring which is a complete intersection of dimension at least
four.  Then the Picard group of the punctured spectrum `U = Spec A ∖ {𝔪}` is trivial.  This is
[Stacks, Tag 0F2I].

The source argues as follows.  By [Stacks, Tag 0F2G] one may replace `A` by its completion, so
`A = B/(f₁, …, f_r)` with `B` a complete regular local ring and `f₁, …, f_r` a regular sequence,
and then induct on `r`.  The base case `r = 0` is [Stacks, Tag 0F2H], the triviality of the
Picard group of the punctured spectrum of a regular local ring.  For the inductive step one sets
`A' = B/(f₁, …, f_{r-1})` and applies [Stacks, Tag 0F2F] to `f_r ∈ A'`.

## Main results

* `subsingleton_picardGroup_puncturedSpectrum_of_isCompleteIntersectionRing` (in
  `Stacks.PuncturedSpectrumPicard`): the argument of [Stacks, Tag 0F2I], with the conclusion of
  [Stacks, Tag 0F2D] taken as an input.  The library proves [Stacks, Tag 0F2D] as
  `Stacks.PuncturedSpectrumPicard.picardColimitSurjective`, and
  `subsingleton_picardGroup_puncturedSpectrum_of_completeIntersection` (in
  `CompleteIntersectionPicardTrivial`) supplies it, giving [Stacks, Tag 0F2I] outright.
* `Stacks.PuncturedSpectrumPicard.isMaximalCohenMacaulay_of_isCompleteIntersectionRing`: a
  Noetherian local complete intersection is Cohen-Macaulay, so its depth is its dimension.  This
  is what feeds the depth hypothesis of [Stacks, Tag 0F2G].
* `Stacks.PuncturedSpectrumPicard.four_le_ringKrullDim_localization_of_maximal_notMem`: the
  dimension estimate behind hypothesis (2) of [Stacks, Tag 0F2F], namely that a prime maximal
  among those avoiding `f` has `dim A_𝔭 ≥ dim A - 1`.

## Implementation notes

**The carried hypothesis.**  The conclusion of [Stacks, Tag 0F2D] — surjectivity of
`colim_{U₀ ⊆ U' ⊆ U} Pic(U') → Pic(U₀)`, written
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` — is consumed by [Stacks, Tag 0F2F].
Its proof, `Stacks.PuncturedSpectrumPicard.picardColimitSurjective`, lives in a module that is
not imported here, so it is carried in this file as a hypothesis, universally quantified over the
rings and elements the induction applies it to, and guarded by the conditions of [Stacks, Tag
0F2D] that the induction can discharge: the ring is Noetherian local and complete for its
maximal-ideal-adic topology (condition (1) of [Stacks, Tag 0F2D], `f`-adic completeness following
from `𝔪`-adic completeness since `(f) ≤ 𝔪` is finitely generated), and the element lies in the
maximal ideal and is a nonzerodivisor (condition (2)), and the ring has depth at least five.  That
last bound is the source's own footnote to [Stacks, Tag 0F2D], "(3) and (4) hold if
`depth(A/fA) ≥ 4`, or equivalently `depth(A) ≥ 5`", so conditions (3) and (4) — the finiteness of
`H¹_𝔪(A/fA)`, `H²_𝔪(A/fA)` and the vanishing of `H³_𝔪(A/fA)` — are covered too.  The carried
hypothesis is therefore an *instance* of [Stacks, Tag 0F2D] and nothing more: a proof of that tag
discharges it directly, rather than leaving a residue behind.

**The induction.**  `TrivialPicardOfCompletePresentation` is the statement proved by induction;
it is an ordinary internal abbreviation, proved outright in
`forall_trivialPicardOfCompletePresentation`, not an assumption.  The presenting ring is required
to be complete, which is what makes every intermediate quotient `B/(f₁, …, f_i)` complete and so
eligible for the carried hypothesis.  The induction is a *strong* induction on the length, because
hypothesis (2) of [Stacks, Tag 0F2F] re-enters the induction at a localization `B_𝔮` of the
presenting ring, which is regular local but no longer complete; the completion of that
localization is restored by `subsingleton_picard_puncturedSpectrum_of_regularPresentation`.

**The punctured closed fibre.**  [Stacks, Tag 0F2F] concludes about
`Stacks.Algebraization.puncturedClosedFibre A f`, the inverse image of the punctured spectrum of
`A` in `Spec(A/fA)`, whereas [Stacks, Tag 0F2G] and [Stacks, Tag 0F2H] speak of
`Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f})`.  The two opens are *equal*, by
`AlgebraicGeometry.LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen`, so the transfer is a
rewrite and no isomorphism of schemes is needed; see
`puncturedClosedFibre_eq_puncturedSpectrum_quotient`.

## References

* [Stacks Project, Tag 0F2I](https://stacks.math.columbia.edu/tag/0F2I)
* [Stacks Project, Tag 0F2F](https://stacks.math.columbia.edu/tag/0F2F)
* [Stacks Project, Tag 0F2G](https://stacks.math.columbia.edu/tag/0F2G)
* [Stacks Project, Tag 0F2H](https://stacks.math.columbia.edu/tag/0F2H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing RingTheory.Sequence

universe u

namespace Stacks.PuncturedSpectrumPicard

open Stacks.AlgebraicGeometry.PicardBaseChange
  (injective_schemePullbackClass_puncturedSpectrumCompletionMap)

/-! ### Transport along a ring isomorphism -/

/-- **An isomorphism of local rings induces an isomorphism of their punctured spectra**, the
induced map of spectra carrying the closed point to the closed point. -/
def puncturedSpectrumIsoOfRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (Stacks.Divisors.puncturedSpectrum S).toScheme ≅
      (Stacks.Divisors.puncturedSpectrum R).toScheme := by
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map e.toCommRingCatIso.hom
  have hf : IsIso f := by dsimp only [f]; infer_instance
  have heq : Stacks.Divisors.puncturedSpectrum S =
      f ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum R := by
    ext x
    change (x ∉ ({closedPoint S} : Set (PrimeSpectrum S))) ↔
      (f x ∉ ({closedPoint R} : Set (PrimeSpectrum R)))
    apply not_congr
    constructor
    · rintro rfl
      exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap (e : R →+* S))
    · intro hx
      refine PrimeSpectrum.ext ?_
      have he : x.asIdeal.comap (e : R →+* S) = maximalIdeal R :=
        congrArg PrimeSpectrum.asIdeal hx
      rw [← IsLocalRing.maximalIdeal_comap (e : R →+* S)] at he
      exact Ideal.comap_injective_of_surjective (e : R →+* S) e.surjective he
  exact (Spec (.of S)).isoOfEq heq ≪≫ f.preimageIso _

/-- **Triviality of the Picard group of a punctured spectrum only depends on the isomorphism
class of the local ring.** -/
theorem subsingleton_picard_puncturedSpectrum_of_ringEquiv {R S : Type u} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (hR : Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum R).toScheme)) :
    Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum S).toScheme) :=
  subsingleton_picard_of_schemeIso (puncturedSpectrumIsoOfRingEquiv e) hR

/-! ### Cohen-Macaulayness of a complete intersection -/

/-- An ideal generated by a regular sequence is proper. -/
theorem ofList_ne_top_of_isRegular {R : Type*} [CommRing R] {rs : List R}
    (h : IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro heq
  exact h.top_ne_smul (by simp [heq])

/-- Every member of a regular sequence in a local ring lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_isRegular {R : Type*} [CommRing R] [IsLocalRing R] {rs : List R}
    (h : IsRegular R rs) : ∀ r ∈ rs, r ∈ maximalIdeal R :=
  fun _ hr => le_maximalIdeal (ofList_ne_top_of_isRegular h) (Ideal.subset_span hr)

/-- **A regular local ring stays Cohen-Macaulay after quotienting by a regular sequence**, with
the dimension dropping by the length of the sequence.  This is [Stacks, Tag 00NQ] — a regular
local ring is Cohen-Macaulay — fed into [Stacks, Tag 02JN], which carries Cohen-Macaulayness
through a quotient by a regular sequence. -/
theorem isMaximalCohenMacaulay_quotient_ofList {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hrs : IsRegular R rs) [IsLocalRing (R ⧸ Ideal.ofList rs)] :
    Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList rs) (R ⧸ Ideal.ofList rs) ∧
      ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length = ringKrullDim R := by
  have hR : Module.IsMaximalCohenMacaulay R R :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2
  obtain ⟨hiff, hstep⟩ := hR.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim rs
    (mem_maximalIdeal_of_isRegular hrs)
  obtain ⟨-, hall⟩ := hstep hrs
  refine ⟨?_, hiff.mp hrs⟩
  have hall' := hall rs.length le_rfl
  revert hall'
  rw [List.take_length]
  rintro ⟨hloc, hcm, -⟩
  exact hcm

/-- **Cohen-Macaulayness of a local ring only depends on its isomorphism class.** -/
theorem isMaximalCohenMacaulay_self_congr {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Module.IsMaximalCohenMacaulay A A ↔ Module.IsMaximalCohenMacaulay B B := by
  rw [Module.IsMaximalCohenMacaulay, Module.IsMaximalCohenMacaulay,
    Module.depth_self_eq_of_ringEquiv e, ringKrullDim_eq_of_ringEquiv e]

/-- The quotient of a local ring by a proper ideal is local. -/
private theorem isLocalRing_quotient_of_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} (h : I ≠ ⊤) : IsLocalRing (R ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr h
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- In a Cohen-Macaulay local ring the depth is at least any lower bound on the dimension. -/
private theorem le_depth_of_isMaximalCohenMacaulay {A : Type*} [CommRing A] [IsLocalRing A]
    (hCM : Module.IsMaximalCohenMacaulay A A) {m : ℕ∞} (h : (m : WithBot ℕ∞) ≤ ringKrullDim A) :
    m ≤ Module.depth A (maximalIdeal A) A := by
  refine WithBot.coe_le_coe.mp ?_
  rwa [hCM]

/-- **A Noetherian local complete intersection is Cohen-Macaulay**: its depth along the maximal
ideal equals its Krull dimension.

The library has no lemma to this effect, so it is composed here out of the two that do exist:
the completion of a complete intersection is a quotient of a regular local ring by a regular
sequence, a regular local ring is Cohen-Macaulay by [Stacks, Tag 00NQ] and stays so after such a
quotient by [Stacks, Tag 02JN], and Cohen-Macaulayness descends from the completion by
[Stacks, Tag 07NX]. -/
theorem isMaximalCohenMacaulay_of_isCompleteIntersectionRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hA : LocalCompleteIntersection.IsCompleteIntersectionRing A) :
    Module.IsMaximalCohenMacaulay A A := by
  obtain ⟨R, hRring, hRreg, φ, hφ, -, rs, hrs, hker⟩ := hA
  have := isLocalRing_quotient_of_ne_top (ofList_ne_top_of_isRegular hrs)
  have e : (R ⧸ Ideal.ofList rs) ≃+* AdicCompletion (maximalIdeal A) A :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hφ)
  exact isMaximalCohenMacaulay_iff_adicCompletion_maximalIdeal.mpr
    ((isMaximalCohenMacaulay_self_congr e).mp (isMaximalCohenMacaulay_quotient_ofList rs hrs).1)

/-! ### The dimension estimate at a prime maximal away from `f` -/

/-- An ideal not contained in any of finitely many primes contains an element outside all of
them, by prime avoidance. -/
theorem exists_mem_forall_notMem_of_finite {R : Type u} [CommRing R] {s : Set (Ideal R)}
    (hs : s.Finite) (hp : ∀ q ∈ s, q.IsPrime) {I : Ideal R} (hnotle : ∀ q ∈ s, ¬ I ≤ q) :
    ∃ x ∈ I, ∀ q ∈ s, x ∉ q := by
  have hnot : ¬(I : Set R) ⊆ ⋃ q ∈ s, (q : Set R) := by
    intro hsub
    obtain ⟨q, hq, hle⟩ :=
      (Ideal.subset_union_prime_finite hs (f := fun q : Ideal R => q) I I
        (fun q hq _ _ => hp q hq)).mp hsub
    exact hnotle q hq hle
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hnot
  exact ⟨x, hxI, fun q hq hxq => hx (Set.mem_iUnion.mpr ⟨q,
    Set.mem_iUnion.mpr ⟨hq, hxq⟩⟩)⟩

/-- **A Noetherian local domain in which a single nonzero element lies in every nonzero prime has
dimension at most one.**

Were the dimension at least two, prime avoidance would produce `y` in the maximal ideal lying
outside every minimal prime of `(g)` and outside `(0)`; a minimal prime `𝔮` over `(y)` then has
height one by Krull's principal ideal theorem, hence is nonzero, hence contains `g`, hence is a
minimal prime of `(g)` — which `y ∈ 𝔮` contradicts. -/
theorem ringKrullDim_le_one_of_forall_mem_of_ne_bot (D : Type u) [CommRing D]
    [IsNoetherianRing D] [IsLocalRing D] [IsDomain D] (g : D) (hg : g ≠ 0)
    (hall : ∀ q : Ideal D, q.IsPrime → q ≠ ⊥ → g ∈ q) :
    ringKrullDim D ≤ (1 : WithBot ℕ∞) := by
  classical
  by_contra hdim
  have hdim' : 2 ≤ ringKrullDim D := by
    by_contra h
    refine hdim ?_
    have hlt : ringKrullDim D < (1 : WithBot ℕ∞) + 1 := by
      have := not_le.mp h
      rwa [show (2 : WithBot ℕ∞) = (1 : WithBot ℕ∞) + 1 by norm_num] at this
    exact ENat.WithBot.lt_add_one_iff.mp hlt
  have hmheight : 2 ≤ (maximalIdeal D).height := by
    refine WithBot.coe_le_coe.mp ?_
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact hdim'
  let s : Set (Ideal D) := Ideal.minimalPrimes (Ideal.span {g}) ∪ {⊥}
  have hs : s.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing D (Ideal.span {g})).union
      (Set.finite_singleton ⊥)
  have hp : ∀ q ∈ s, q.IsPrime := by
    intro q hq
    rcases hq with hq | hq
    · exact hq.isPrime
    · rw [Set.mem_singleton_iff.mp hq]; exact Ideal.isPrime_bot
  have hnotle : ∀ q ∈ s, ¬ maximalIdeal D ≤ q := by
    intro q hq hle
    rcases hq with hq | hq
    · have h1 : q.height ≤ 1 :=
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) q hq
      have h2 : (2 : ℕ∞) ≤ q.height := hmheight.trans (Ideal.height_mono hle)
      exact absurd (h2.trans h1) (by norm_num)
    · have hq' : q = ⊥ := Set.mem_singleton_iff.mp hq
      have hb : (maximalIdeal D).height ≤ (⊥ : Ideal D).height := by
        rw [hq'] at hle; exact Ideal.height_mono hle
      rw [Ideal.height_bot] at hb
      exact absurd (hmheight.trans hb) (by norm_num)
  obtain ⟨y, hyM, hyavoid⟩ :=
    exists_mem_forall_notMem_of_finite hs hp hnotle (I := maximalIdeal D)
  have hy0 : y ≠ 0 := fun hy =>
    (hyavoid ⊥ (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl))) (hy ▸ Ideal.zero_mem ⊥)
  obtain ⟨⟨q, hq⟩⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {y}) fun htop =>
    (maximalIdeal.isMaximal D).ne_top
      (top_le_iff.mp (htop ▸ (Ideal.span_singleton_le_iff_mem _).mpr hyM))
  have hqp : q.IsPrime := hq.1.1
  have hyq : y ∈ q := hq.1.2 (Ideal.mem_span_singleton_self y)
  have hqle : q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {y}) q hq
  have hqge : (1 : ℕ∞) ≤ q.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hy0)).trans
      (Ideal.height_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyq)))
  have hqne : q ≠ ⊥ := by
    intro hqbot
    rw [hqbot, Ideal.height_bot] at hqge
    exact absurd hqge (by norm_num)
  have hgq : g ∈ q := hall q hqp hqne
  have hspan : Ideal.span {g} ≤ q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgq)
  have hgheight : (1 : ℕ∞) ≤ (Ideal.span {g}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg)
  have hqmin : q ∈ Ideal.minimalPrimes (Ideal.span {g}) :=
    Ideal.mem_minimalPrimes_of_height_le hspan (hqle.trans hgheight)
  exact hyavoid q (Set.mem_union_left _ hqmin) hyq

/-- **If `𝔭` is maximal among the primes avoiding `f`, then `A/𝔭` has dimension at most one**:
every nonzero prime of `A/𝔭` is a prime of `A` strictly above `𝔭`, hence contains `f`. -/
theorem ringKrullDim_quotient_le_one_of_maximal_notMem (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (P : Ideal A) [P.IsPrime] (hfP : f ∉ P)
    (hmax : ∀ Q : Ideal A, Q.IsPrime → P < Q → f ∈ Q) :
    ringKrullDim (A ⧸ P) ≤ (1 : WithBot ℕ∞) := by
  have : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  refine ringKrullDim_le_one_of_forall_mem_of_ne_bot (A ⧸ P) (Ideal.Quotient.mk P f)
    (fun hz => hfP (Ideal.Quotient.eq_zero_iff_mem.mp hz)) ?_
  intro q hq hqne
  have hQ : (q.comap (Ideal.Quotient.mk P)).IsPrime := hq.comap _
  have hPle : P ≤ q.comap (Ideal.Quotient.mk P) := by
    intro x hx
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hPlt : P < q.comap (Ideal.Quotient.mk P) := by
    refine lt_of_le_of_ne hPle ?_
    intro heq
    refine hqne ?_
    have := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
    rw [← this, ← heq, Ideal.map_quotient_self]
  exact Ideal.mem_comap.mp (hmax _ hQ hPlt)

/-- **The dimension estimate behind hypothesis (2) of [Stacks, Tag 0F2F]**: if `A` is a
Cohen-Macaulay local ring of dimension at least five and `𝔭` is maximal among the primes of `A`
avoiding `f`, then `A_𝔭` has dimension at least four.

This is the source's "`dim((A'_{f_r})_𝔭) ≥ 4` for a maximal prime `𝔭` of `A'_{f_r}`".  The
Cohen-Macaulay dimension formula `dim A = ht(𝔭) + dim(A/𝔭)` together with `dim(A/𝔭) ≤ 1` gives
`ht(𝔭) ≥ dim A - 1`, and `ht(𝔭) = dim A_𝔭`. -/
theorem four_le_ringKrullDim_localization_of_maximal_notMem (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hCM : Module.IsMaximalCohenMacaulay A A)
    (hdim : 5 ≤ ringKrullDim A) (f : A) (P : Ideal A) [P.IsPrime] (hfP : f ∉ P)
    (hmax : ∀ Q : Ideal A, Q.IsPrime → P < Q → f ∈ Q) :
    4 ≤ ringKrullDim (Localization.AtPrime P) := by
  have hquot : ringKrullDim (A ⧸ P) ≤ (1 : WithBot ℕ∞) :=
    ringKrullDim_quotient_le_one_of_maximal_notMem A f P hfP hmax
  have hformula := hCM.ringKrullDim_eq_height_add_ringKrullDim_quotient P
  have hupper : ringKrullDim A ≤ (P.height : WithBot ℕ∞) + 1 := by
    rw [hformula]; exact add_le_add le_rfl hquot
  have hfive : (4 : WithBot ℕ∞) + 1 ≤ (P.height : WithBot ℕ∞) + 1 :=
    le_trans (by rw [show (4 : WithBot ℕ∞) + 1 = 5 by norm_num]; exact hdim) hupper
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
  cases hP : P.height with
  | top => simp
  | coe n =>
    have hn : (5 : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) + 1 := by
      rw [show (5 : WithBot ℕ∞) = (4 : WithBot ℕ∞) + 1 by norm_num]
      simpa [hP] using hfive
    have hn' : 5 ≤ n + 1 := by exact_mod_cast hn
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : 4 ≤ n))

/-! ### The punctured closed fibre is the punctured spectrum of the quotient -/

/-- **The punctured closed fibre of `(A, f)` is the punctured spectrum of `A/fA`.**  Both are
opens of `Spec(A/fA)`, and they are *equal*: the quotient map is local, so it matches up the two
closed points.  This is
`AlgebraicGeometry.LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen` read in the spellings
of [Stacks, Tag 0F2F]. -/
theorem puncturedClosedFibre_eq_puncturedSpectrum_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hf : f ∈ maximalIdeal A)
    [IsLocalRing (A ⧸ Ideal.span {f})] :
    Stacks.Algebraization.puncturedClosedFibre A f =
      Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) :=
  LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen ⟨A, f, hf⟩

/-! ### The induction -/

/-- The statement proved by induction on the length of the regular sequence: for a *complete*
regular local presenting ring `R` and a regular sequence of length `n` in it, the punctured
spectrum of `R/(rs)` has trivial Picard group as soon as its dimension is at least four.

This is an internal abbreviation for the induction hypothesis; it is proved outright in
`forall_trivialPicardOfCompletePresentation`. -/
def TrivialPicardOfCompletePresentation (n : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (rs : List R), rs.length = n → IsRegular R rs →
      ∀ [IsLocalRing (R ⧸ Ideal.ofList rs)],
        4 ≤ ringKrullDim (R ⧸ Ideal.ofList rs) →
        Subsingleton (Stacks.Picard.ofScheme
          (Stacks.Divisors.puncturedSpectrum (R ⧸ Ideal.ofList rs)).toScheme)

/-- An ideal generated by a list maps to the ideal generated by the mapped list. -/
theorem ofList_map_eq_map_ofList {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (rs : List R) : Ideal.ofList (rs.map φ) = (Ideal.ofList rs).map φ :=
  (Ideal.map_ofList φ rs).symm

/-- `R/(rs)` for `rs` a list, split off the last entry: quotienting by the final element of the
list afterwards gives the same ring. -/
def quotientOfListSnocEquiv {R : Type*} [CommRing R] (rs : List R) (f : R) :
    ((R ⧸ Ideal.ofList rs) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f}) ≃+*
      R ⧸ Ideal.ofList (rs ++ [f]) := by
  have hmap : Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f} =
      (Ideal.span {f}).map (Ideal.Quotient.mk (Ideal.ofList rs)) := by
    rw [Ideal.map_span]; simp
  have hsup : Ideal.ofList rs ⊔ Ideal.span {f} = Ideal.ofList (rs ++ [f]) := by
    have hset : {r : R | r ∈ rs ++ [f]} = {r : R | r ∈ rs} ∪ {f} := by
      ext x; simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
        Set.mem_union, Set.mem_singleton_iff]
    change Ideal.span {r : R | r ∈ rs} ⊔ Ideal.span {f} =
      Ideal.span {r : R | r ∈ rs ++ [f]}
    rw [hset, Ideal.span_union]
  exact (Ideal.quotEquivOfEq hmap).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList rs) (Ideal.span {f})).trans
      (Ideal.quotEquivOfEq hsup))

/-- **The punctured spectrum of a quotient of an arbitrary regular local ring by a regular
sequence has trivial Picard group**, granted the statement of the induction at the same length
for *complete* presenting rings.

The presenting ring `R` is replaced by its completion `R^`, which is again regular local and is
complete; the image of the regular sequence stays regular because `R → R^` is faithfully flat,
and the completion of `R/(rs)` is `R^/(rs)` by
`nonempty_ringEquiv_adicCompletion_quotient`.  [Stacks, Tag 0F2G] then
descends triviality from the completion, its depth hypothesis coming from Cohen-Macaulayness. -/
theorem subsingleton_picard_puncturedSpectrum_of_regularPresentation {n : ℕ}
    (hQ : TrivialPicardOfCompletePresentation.{u} n)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (φ : R →+* A) (hφ : Function.Surjective φ)
    (rs : List R) (hrs : IsRegular R rs) (hlen : rs.length = n)
    (hker : Ideal.ofList rs = RingHom.ker φ) (hdim : 4 ≤ ringKrullDim A) :
    Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum A).toScheme) := by
  have hne : Ideal.ofList rs ≠ ⊤ := ofList_ne_top_of_isRegular hrs
  have := isLocalRing_quotient_of_ne_top hne
  have e : (R ⧸ Ideal.ofList rs) ≃+* A :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hφ)
  -- It suffices to treat `Q = R/(rs)` itself.
  refine subsingleton_picard_puncturedSpectrum_of_ringEquiv e ?_
  have hdimQ : 4 ≤ ringKrullDim (R ⧸ Ideal.ofList rs) := by
    rwa [ringKrullDim_eq_of_ringEquiv e]
  have hCMQ : Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList rs) (R ⧸ Ideal.ofList rs) :=
    (isMaximalCohenMacaulay_quotient_ofList rs hrs).1
  -- The completion of the presenting ring.
  have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  have hTreg : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  have hTcomplete : IsAdicComplete
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := AdicCompletion.isAdicComplete_of_fg hfg
  have hff : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (maximalIdeal R)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hts : IsRegular (AdicCompletion (maximalIdeal R) R)
      (rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := hrs.of_faithfullyFlat
  have htsne : Ideal.ofList (rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ≠ ⊤ :=
    ofList_ne_top_of_isRegular hts
  have := isLocalRing_quotient_of_ne_top htsne
  -- The completion of `Q` is `R^/(rs)`.
  obtain ⟨ec⟩ := nonempty_ringEquiv_adicCompletion_quotient
    (R := R) (Ideal.ofList rs)
  have ec' : AdicCompletion (maximalIdeal (R ⧸ Ideal.ofList rs)) (R ⧸ Ideal.ofList rs) ≃+*
      (AdicCompletion (maximalIdeal R) R ⧸
        Ideal.ofList (rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))) :=
    ec.trans (Ideal.quotEquivOfEq
      (ofList_map_eq_map_ofList (algebraMap R (AdicCompletion (maximalIdeal R) R)) rs).symm)
  have hdimT : 4 ≤ ringKrullDim (AdicCompletion (maximalIdeal R) R ⧸
      Ideal.ofList (rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))) := by
    rw [← ringKrullDim_eq_of_ringEquiv ec', ← ringKrullDim_adicCompletion_maximalIdeal]
    exact hdimQ
  have hcomp : Subsingleton (Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum
      (AdicCompletion (maximalIdeal (R ⧸ Ideal.ofList rs)) (R ⧸ Ideal.ofList rs))).toScheme) :=
    subsingleton_picard_puncturedSpectrum_of_ringEquiv ec'.symm
      (hQ (AdicCompletion (maximalIdeal R) R)
        (rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
        (by simpa using hlen) hts hdimT)
  -- Descend along the completion by Stacks 0F2G.
  have hdepth : 2 ≤ Module.depth (R ⧸ Ideal.ofList rs)
      (maximalIdeal (R ⧸ Ideal.ofList rs)) (R ⧸ Ideal.ofList rs) :=
    le_depth_of_isMaximalCohenMacaulay hCMQ (le_trans (by norm_num) hdimQ)
  have hinj := injective_schemePullbackClass_puncturedSpectrumCompletionMap
    (R ⧸ Ideal.ofList rs) hdepth
  exact ⟨fun x y => hinj (hcomp.allEq _ _)⟩

/-- **The localization of `R/(rs)` at a prime `𝔭` is presented by the localization of `R` at the
preimage of `𝔭`**, modulo the image there of the same list.  This is the presentation hypothesis
(2) of [Stacks, Tag 0F2F] needs: the source's "`(A'_{f_r})_𝔭 = B_𝔮/(f₁, …, f_{r-1})` for some
prime `𝔮` of `B`". -/
theorem exists_surjective_ker_eq_ofList_localizationAtPrime {R : Type u} [CommRing R]
    (I : Ideal R) (rs : List R) (hI : Ideal.ofList rs = I)
    (P : Ideal (R ⧸ I)) [P.IsPrime] :
    ∃ φ : Localization.AtPrime (P.comap (Ideal.Quotient.mk I)) →+* Localization.AtPrime P,
      Function.Surjective φ ∧
        Ideal.ofList (rs.map (algebraMap R
            (Localization.AtPrime (P.comap (Ideal.Quotient.mk I))))) = RingHom.ker φ := by
  have hM : Submonoid.map (Ideal.Quotient.mk I)
      (P.comap (Ideal.Quotient.mk I)).primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨y, hx, rfl⟩
  have hy : (P.comap (Ideal.Quotient.mk I)).primeCompl ≤
      Submonoid.comap (Ideal.Quotient.mk I) P.primeCompl := fun _ hx => hx
  have hloc : IsLocalization (Submonoid.map (Ideal.Quotient.mk I)
      (P.comap (Ideal.Quotient.mk I)).primeCompl) (Localization.AtPrime P) := by
    rw [hM]; infer_instance
  refine ⟨IsLocalization.map (Localization.AtPrime P) (Ideal.Quotient.mk I) hy, ?_, ?_⟩
  · exact IsLocalization.map_surjective_of_surjective _ _ _ Ideal.Quotient.mk_surjective
  · have hker : RingHom.ker (IsLocalization.map (Localization.AtPrime P)
        (Ideal.Quotient.mk I) hy :
          Localization.AtPrime (P.comap (Ideal.Quotient.mk I)) →+* Localization.AtPrime P) =
        (RingHom.ker (Ideal.Quotient.mk I)).map
          (algebraMap R (Localization.AtPrime (P.comap (Ideal.Quotient.mk I)))) :=
      IsLocalization.ker_map _ _ hM
    rw [Ideal.mk_ker] at hker
    rw [ofList_map_eq_map_ofList, hI]
    exact hker.symm

/-- **The induction of [Stacks, Tag 0F2I]**, on the length of the regular sequence.

The base case is [Stacks, Tag 0F2H].  In the inductive step the last member `f` of the sequence
is split off, giving `A' = R/(rs)` complete Noetherian local and Cohen-Macaulay of dimension at
least five with `A = A'/fA'`; [Stacks, Tag 0F2F] then makes `Pic(U') → Pic(U₀)` surjective, its
hypothesis (2) being the induction hypothesis at the localizations `A'_𝔭`, which are presented by
localizations of `R` through `subsingleton_picard_puncturedSpectrum_of_regularPresentation`. -/
theorem forall_trivialPicardOfCompletePresentation
    (h0F2D : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsAdicComplete (maximalIdeal B) B] (g : B), g ∈ maximalIdeal B →
      g ∈ nonZeroDivisors B → 5 ≤ Module.depth B (maximalIdeal B) B →
      PicardColimitSurjective B g)
    (n : ℕ) : TrivialPicardOfCompletePresentation.{u} n := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ _ rs
    induction rs using List.reverseRecOn with
    | nil =>
      intro _ _ _ _
      have e : R ≃+* (R ⧸ Ideal.ofList ([] : List R)) :=
        ((Ideal.quotEquivOfEq (show Ideal.ofList ([] : List R) = ⊥ by simp)).trans
          (RingEquiv.quotientBot R)).symm
      exact subsingleton_picard_puncturedSpectrum_of_ringEquiv e
        (Stacks.PicardUFD.subsingleton_picardGroup_puncturedSpectrum R)
    | append_singleton rs f _ =>
      intro hlen hrs _ hdim
      -- The shorter sequence and the ring `A'` it cuts out.
      have hpre : IsRegular R rs := ((isRegular_snoc_iff rs f).mp hrs).1
      have hlen' : rs.length < n := by
        simp only [List.length_append, List.length_singleton] at hlen; omega
      have hpne : Ideal.ofList rs ≠ ⊤ := ofList_ne_top_of_isRegular hpre
      have hA'loc := isLocalRing_quotient_of_ne_top hpne
      have hA'complete : IsAdicComplete (maximalIdeal (R ⧸ Ideal.ofList rs))
          (R ⧸ Ideal.ofList rs) :=
        (quotient_isNoetherianCompleteLocalRing
          ⟨inferInstance, inferInstance, inferInstance⟩ _ hpne).isComplete
      have hmk : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList rs)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      -- The last element of the sequence, pushed to `A'`.
      have hfmem : Ideal.Quotient.mk (Ideal.ofList rs) f ∈
          maximalIdeal (R ⧸ Ideal.ofList rs) :=
        map_nonunit (Ideal.Quotient.mk (Ideal.ofList rs)) f
          (mem_maximalIdeal_of_isRegular hrs f (by simp))
      -- `f` acts as a nonzerodivisor on `A'`, by the snoc form of regularity.
      have hsmR : IsSMulRegular (R ⧸ Ideal.ofList rs) f := by
        have hreg := ((isRegular_snoc_iff rs f).mp hrs).2
        have e2 : (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R))) ≃ₗ[R]
            R ⧸ Ideal.ofList rs := Submodule.quotEquivOfEq _ _ (by simp)
        exact (e2.isSMulRegular_congr f).mp ((isRegular_cons_iff _ f []).mp hreg).1
      have hsmg : IsSMulRegular (R ⧸ Ideal.ofList rs)
          (Ideal.Quotient.mk (Ideal.ofList rs) f) := by
        intro x y hxy
        refine hsmR ?_
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        simpa only [smul_eq_mul] using hxy
      have hfreg : (Ideal.Quotient.mk (Ideal.ofList rs) f) ∈
          nonZeroDivisors (R ⧸ Ideal.ofList rs) := by
        refine mem_nonZeroDivisors_iff_right.mpr fun x hx => hsmg ?_
        simp only [smul_eq_mul, mul_zero]
        rw [mul_comm]
        exact hx
      have hspanne : Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f} ≠ ⊤ :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hfmem)
      have := isLocalRing_quotient_of_ne_top hspanne
      -- Dimensions: `dim A' = dim A + 1 ≥ 5`.
      have esnoc := quotientOfListSnocEquiv rs f
      have hdimQ : 4 ≤ ringKrullDim ((R ⧸ Ideal.ofList rs) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f}) := by
        rw [ringKrullDim_eq_of_ringEquiv esnoc]; exact hdim
      have hsmultop : (Ideal.ofList [Ideal.Quotient.mk (Ideal.ofList rs) f] •
          (⊤ : Submodule (R ⧸ Ideal.ofList rs) (R ⧸ Ideal.ofList rs))) =
          Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f} := by
        simp [Ideal.mul_top]
      have hone : IsRegular (R ⧸ Ideal.ofList rs)
          [Ideal.Quotient.mk (Ideal.ofList rs) f] :=
        { toIsWeaklyRegular := (isWeaklyRegular_singleton_iff _ _).mpr hsmg
          top_ne_smul := by rw [hsmultop]; exact fun h => hspanne h.symm }
      have hdrop : ringKrullDim ((R ⧸ Ideal.ofList rs) ⧸
            Ideal.span {Ideal.Quotient.mk (Ideal.ofList rs) f}) + 1 =
          ringKrullDim (R ⧸ Ideal.ofList rs) := by
        have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
          [Ideal.Quotient.mk (Ideal.ofList rs) f] hone
        rw [Ideal.ofList_singleton] at h
        simpa using h
      have hdimA' : 5 ≤ ringKrullDim (R ⧸ Ideal.ofList rs) := by
        rw [← hdrop, show (5 : WithBot ℕ∞) = 4 + 1 by norm_num]
        exact add_le_add hdimQ le_rfl
      have hCMA' : Module.IsMaximalCohenMacaulay (R ⧸ Ideal.ofList rs)
          (R ⧸ Ideal.ofList rs) := (isMaximalCohenMacaulay_quotient_ofList rs hpre).1
      -- Hypothesis (2) of Stacks 0F2F.
      have h2 : ∀ p : PrimeSpectrum (R ⧸ Ideal.ofList rs),
          Ideal.Quotient.mk (Ideal.ofList rs) f ∉ p.asIdeal →
          (∀ q : PrimeSpectrum (R ⧸ Ideal.ofList rs), p.asIdeal < q.asIdeal →
            Ideal.Quotient.mk (Ideal.ofList rs) f ∈ q.asIdeal) →
          Subsingleton (Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum
            (Localization.AtPrime p.asIdeal)).toScheme) := by
        intro p hfp hpmax
        have hPprime : p.asIdeal.IsPrime := p.isPrime
        have hdimB : 4 ≤ ringKrullDim (Localization.AtPrime p.asIdeal) :=
          four_le_ringKrullDim_localization_of_maximal_notMem (R ⧸ Ideal.ofList rs) hCMA'
            hdimA' (Ideal.Quotient.mk (Ideal.ofList rs) f) p.asIdeal hfp
            (fun Q hQ hlt => hpmax ⟨Q, hQ⟩ hlt)
        -- Present `A'_𝔭` by a localization of `R`.
        have hg : Function.Surjective (Ideal.Quotient.mk (Ideal.ofList rs)) :=
          Ideal.Quotient.mk_surjective
        have hqprime : (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs))).IsPrime := by
          have := p.isPrime
          infer_instance
        have hRring : IsRegularRing R :=
          ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp
            (inferInstance : IsRegularLocalRing R)
        have hTreg : IsRegularLocalRing
            (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs)))) :=
          IsRegularRing.isRegularLocalRing_of_isLocalization
            (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs))) _
        have hmem : ∀ x ∈ rs, x ∈ p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs)) := by
          intro x hx
          have hx0 : Ideal.Quotient.mk (Ideal.ofList rs) x = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hx)
          simp [hx0]
        have htreg := hpre.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem
          (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs))))
          (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs))) hmem
        obtain ⟨φ, hφ, hkφ⟩ := exists_surjective_ker_eq_ofList_localizationAtPrime
          (Ideal.ofList rs) rs rfl p.asIdeal
        exact subsingleton_picard_puncturedSpectrum_of_regularPresentation
          (ih rs.length hlen')
          (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.ofList rs))))
          φ hφ _ htreg (by simp) hkφ hdimB
      -- Stacks 0F2F.
      have hsource : Subsingleton (Stacks.Picard.ofScheme
          (Stacks.Divisors.puncturedSpectrum (R ⧸ Ideal.ofList rs)).toScheme) :=
        ih rs.length hlen' R rs rfl hpre (le_trans (by norm_num) hdimA')
      -- The footnote's depth bound, condition (3)/(4) of Stacks 0F2D: `A'` is Cohen-Macaulay
      -- of dimension at least five, so `depth(A') = dim(A') ≥ 5`.
      have hdepthA' : 5 ≤ Module.depth (R ⧸ Ideal.ofList rs)
          (maximalIdeal (R ⧸ Ideal.ofList rs)) (R ⧸ Ideal.ofList rs) :=
        le_depth_of_isMaximalCohenMacaulay hCMA' (le_trans (by norm_num) hdimA')
      have hsurj := surjective_schemePullbackClass_puncturedClosedFibre_of_isNoetherianRing
        hfmem (h0F2D (R ⧸ Ideal.ofList rs) _ hfmem hfreg hdepthA') h2
      have hfibre : Subsingleton (Stacks.Picard.ofScheme
          (Stacks.Algebraization.puncturedClosedFibre (R ⧸ Ideal.ofList rs)
            (Ideal.Quotient.mk (Ideal.ofList rs) f)).toScheme) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := hsurj x
        obtain ⟨b, rfl⟩ := hsurj y
        exact congrArg _ (hsource.allEq a b)
      rw [puncturedClosedFibre_eq_puncturedSpectrum_quotient (R ⧸ Ideal.ofList rs) _ hfmem]
        at hfibre
      exact subsingleton_picard_puncturedSpectrum_of_ringEquiv esnoc hfibre

/-! ### The argument of Stacks 0F2I, with the conclusion of Stacks 0F2D as input -/

/-- **The argument of [Stacks, Tag 0F2I]**, with the conclusion of [Stacks, Tag 0F2D] taken as
the input `h0F2D`.  Let `(A, 𝔪)` be a Noetherian local ring.  If `A` is a complete intersection
of dimension at least four, then the Picard group of the punctured spectrum `U = Spec A ∖ {𝔪}`
of `A` is trivial.

The input `h0F2D` is phrased with `Stacks.PuncturedSpectrumPicard.PicardColimitSurjective` and
quantified over the Noetherian local rings `B` that are `𝔪`-adically complete, the elements
`g ∈ 𝔪_B` that are nonzerodivisors, and the bound `5 ≤ depth(B)`.  Completeness and the
nonzerodivisor clause are conditions (1) and (2) of [Stacks, Tag 0F2D], and the depth bound is
that tag's own footnote, "(3) and (4) hold if `depth(A/fA) ≥ 4`, or equivalently
`depth(A) ≥ 5`", which covers its remaining conditions (3) and (4).  So `h0F2D` asserts no more
than [Stacks, Tag 0F2D] does.  The library proves that tag as
`Stacks.PuncturedSpectrumPicard.picardColimitSurjective`, and
`Stacks.PuncturedSpectrumPicard.subsingleton_picardGroup_puncturedSpectrum_of_completeIntersection`
discharges `h0F2D` with it; that theorem is [Stacks, Tag 0F2I].

The induction applies `h0F2D` exactly to the intermediate quotients `A' = B/(f₁, …, f_{r-1})` of
the source's presentation: all are complete because the presenting ring is, and all have
`depth(A') = dim(A') = dim(A) + 1 ≥ 5` because a quotient of a regular local ring by a regular
sequence is Cohen-Macaulay. -/
theorem subsingleton_picardGroup_puncturedSpectrum_of_isCompleteIntersectionRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (h0F2D : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsAdicComplete (maximalIdeal B) B] (g : B), g ∈ maximalIdeal B →
      g ∈ nonZeroDivisors B → 5 ≤ Module.depth B (maximalIdeal B) B →
      PicardColimitSurjective B g)
    (hA : LocalCompleteIntersection.IsCompleteIntersectionRing A)
    (hdim : 4 ≤ ringKrullDim A) :
    Subsingleton (Stacks.Divisors.puncturedSpectrum A).toScheme.picardGroup := by
  obtain ⟨R, hRring, hRreg, φ, hφ, hlocalhom, rs, hrs, hker⟩ := hA
  have hdimhat : 4 ≤ ringKrullDim (AdicCompletion (maximalIdeal A) A) := by
    rwa [← ringKrullDim_adicCompletion_maximalIdeal]
  have hhat : Subsingleton (Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum
      (AdicCompletion (maximalIdeal A) A)).toScheme) :=
    subsingleton_picard_puncturedSpectrum_of_regularPresentation
      (forall_trivialPicardOfCompletePresentation h0F2D rs.length)
      (AdicCompletion (maximalIdeal A) A) R φ hφ rs hrs rfl hker hdimhat
  have hCM : Module.IsMaximalCohenMacaulay A A :=
    isMaximalCohenMacaulay_of_isCompleteIntersectionRing A
      ⟨R, hRring, hRreg, φ, hφ, hlocalhom, rs, hrs, hker⟩
  have hdepth : 2 ≤ Module.depth A (maximalIdeal A) A :=
    le_depth_of_isMaximalCohenMacaulay hCM (le_trans (by norm_num) hdim)
  have hinj := injective_schemePullbackClass_puncturedSpectrumCompletionMap A hdepth
  exact ⟨fun x y => hinj (hhat.allEq _ _)⟩

end Stacks.PuncturedSpectrumPicard

end
