module

public import Mathlib
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import StacksFrontier.FieldTheory.PurelyInseparable.BaseChange
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.Smooth.Field
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.Topology.Noetherian.OpenViaIrreducibleClosed
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

open Stacks.Smooth.FlatFibreCriterion

@[expose] public section

/-!
# The singular locus and the J-conditions

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07P7, 07P8, 07P9, 07PA, 07PB, 07PC.

## Tag 07P7 — The J-0, J-1, and J-2 properties

The regular locus of the spectrum of a commutative ring consists of the prime ideals at which
the corresponding local rings are regular. The J-0 and J-1 properties describe the size and
openness of this locus, while J-2 requires J-1 for every finite type algebra.

### Main definitions

* `IsJ0`: the regular locus contains a nonempty open subset.
* `IsJ1`: the regular locus is open.
* `IsJ2`: every finite type algebra is J-1.

### Implementation notes

Although the source introduces these properties for Noetherian rings, their defining conditions
make sense for every commutative ring, so no Noetherian hypothesis is imposed. In `IsJ2`, the
finite type algebras are taken in the same ambient universe as the base ring.

### References

* [H. Matsumura, *Commutative Algebra*, (32.B)][MatCA]
* [Stacks Project, Tag 07P7](https://stacks.math.columbia.edu/tag/07P7)

## Tag 07P8 — A characterization of J-1 rings

For a Noetherian ring, the regular locus is open exactly when its intersection with the
vanishing locus of every regular prime contains a nonempty open subset of that vanishing locus.

### Main results

* `isJ1_iff_zeroLocus_inter_regularLocus_contains_nonempty_open`: the
  characterization of the J-1 property by the regular locus on each `V(p)`.

### Implementation notes

An open subset of `V(p)` is represented as the intersection of `V(p)` with an open subset of
the ambient prime spectrum.

### References

* [Stacks Project, Tag 07P8](https://stacks.math.columbia.edu/tag/07P8)

## Tag 07P9 — J-1 from J-0 prime quotients

A Noetherian ring is J-1 if each of its quotients by a prime ideal is J-0.

### Main results

* `isJ1_of_forall_quotient_isJ0`: a Noetherian ring whose prime quotients are
  J-0 is J-1.

### Implementation notes

Prime ideals are represented by points of the prime spectrum. The quotient attached to a point
is taken by its underlying prime ideal.

### References

* [Stacks Project, Tag 07P9](https://stacks.math.columbia.edu/tag/07P9)

## Tag 07PA — Descent of the J-0 property

The J-0 property descends along an injective finite type map from a Noetherian domain to a
J-0 domain.

### Main results

* `isJ0_of_injective_finiteType`: a Noetherian domain admitting an injective finite
  type map to a J-0 domain is J-0.

### Implementation notes

Ring maps are represented by algebra structures, and finite type is expressed by
`Algebra.FiniteType`.

### References

* [Stacks Project, Tag 07PA](https://stacks.math.columbia.edu/tag/07PA)

## Tag 07PB — The J-0 property ascends along separable finite type extensions

An injective finite type map from a Noetherian J-0 domain to a domain with separable induced
extension of fraction fields has J-0 target.

### Main results

* `isJ0_of_finiteType_injective_of_isSeparable_fractionRing`: the J-0 property ascends
  along an injective finite type map of domains when the induced fraction-field extension is
  separable.

### Implementation notes

The induced map of fraction fields is represented using the canonical fraction rings. Injectivity
of the original algebra map supplies the faithful scalar action needed to construct this map.
Separability is understood for arbitrary field extensions, rather than only algebraic extensions.

### References

* [Stacks Project, Tag 07PB](https://stacks.math.columbia.edu/tag/07PB)

## Tag 07PC — Equivalent characterizations of J-2 rings

For a Noetherian ring, the J-2 property can be tested on finite type domain algebras, on
finite algebras, or by realizing finite purely inseparable extensions of residue fields as
fraction fields of finite J-0 domain algebras.

### Main results

* `isJ2_tfae`: four equivalent characterizations of a Noetherian J-2 ring.

### Implementation notes

The finite domain algebra in the fourth condition is represented as an `R`-subalgebra of the
given field. Thus its inclusion into that field is canonical, and being a domain follows from
the ambient field. The algebra structure on the field over `R` is the composite through the
residue field.

### References

* [Stacks Project, Tag 07PC](https://stacks.math.columbia.edu/tag/07PC)

-/

/-! ### Stacks Tag 07P7 -/

section

universe u

@[expose] public section

/-- **Stacks 07P7 (1).** A commutative ring is J-0 if its regular locus contains a nonempty
open subset. -/
@[stacks 07P7 "(1)"]
public def IsJ0 (R : Type u) [CommRing R] : Prop :=
  ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧
    U ⊆ {x | IsRegularLocalRing (Localization.AtPrime x.asIdeal)}

/-- **Stacks 07P7 (2).** A commutative ring is J-1 if its regular locus is open. -/
@[stacks 07P7 "(2)"]
public def IsJ1 (R : Type u) [CommRing R] : Prop :=
  IsOpen {x : PrimeSpectrum R | IsRegularLocalRing (Localization.AtPrime x.asIdeal)}

/-- **Stacks 07P7 (3).** A commutative ring is J-2 if every finite type algebra over it is
J-1. -/
@[stacks 07P7 "(3)"]
public def IsJ2 (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], IsJ1 S

end

end

/-! ### Stacks Tag 07P8 -/

section

section

universe u

open Set

/-- **Stacks 07P8.** A Noetherian ring is J-1 if and only if, for every point `p` of
its regular locus, `V(p)` intersected with the regular locus contains a nonempty open subset
of `V(p)`. -/
@[stacks 07P8]
public theorem isJ1_iff_zeroLocus_inter_regularLocus_contains_nonempty_open
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsJ1 R ↔
      ∀ p : PrimeSpectrum R,
        IsRegularLocalRing (Localization.AtPrime p.asIdeal) →
          ∃ U : Set (PrimeSpectrum R), IsOpen U ∧
            (U ∩ PrimeSpectrum.zeroLocus p.asIdeal).Nonempty ∧
            U ∩ PrimeSpectrum.zeroLocus p.asIdeal ⊆
              PrimeSpectrum.zeroLocus p.asIdeal ∩
                {x | IsRegularLocalRing (Localization.AtPrime x.asIdeal)} := by
  let E : Set (PrimeSpectrum R) :=
    {x | IsRegularLocalRing (Localization.AtPrime x.asIdeal)}
  show IsOpen E ↔ _
  constructor
  · intro hE p hp
    exact ⟨E, hE, ⟨p, hp, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩,
      fun _ hx => ⟨hx.2, hx.1⟩⟩
  · intro h
    rw [Topology.isOpen_iff_inter_irreducible_closed]
    intro Y hYclosed hYirr
    rcases eq_empty_or_nonempty (E ∩ Y) with hEY | hEY
    · exact Or.inl hEY
    · right
      let p : PrimeSpectrum R := ⟨PrimeSpectrum.vanishingIdeal Y,
        PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hYirr⟩
      let : p.asIdeal.IsPrime := p.2
      have hY : Y = PrimeSpectrum.zeroLocus p.asIdeal := by
        show Y = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Y)
        rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hYclosed.closure_eq]
      obtain ⟨q, hqE, hqY⟩ := hEY
      have hpq : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 (hY ▸ hqY)
      obtain ⟨U, hUopen, hUne, hUsub⟩ :=
        h p (AlgebraicGeometry.regular_atPrime_of_le p.asIdeal q.asIdeal hpq hqE)
      exact ⟨U, hUopen, hY ▸ hUne, fun x hx => (hUsub (hY ▸ hx)).2⟩

end

end

/-! ### Stacks Tag 07P9 -/

section

section

universe u

private theorem height_map_quotient_add_height_le' {B : Type*} [CommRing B]
    (n : Ideal B) [n.IsPrime] (Qt : Ideal B) [Qt.IsPrime] (hnle : n ≤ Qt) :
    (Ideal.map (Ideal.Quotient.mk n) Qt).height + n.height ≤ Qt.height := by
  have hFp : (Ideal.map (Ideal.Quotient.mk n) Qt).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hnle
  set F := Ideal.map (Ideal.Quotient.mk n) Qt with hF
  rw [PrimeSpectrum.height_eq_orderHeight ⟨F, hFp⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨n, inferInstance⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨Qt, inferInstance⟩]
  show Order.height (⟨F, hFp⟩ : PrimeSpectrum (B ⧸ n))
      + Order.height (⟨n, inferInstance⟩ : PrimeSpectrum B)
      ≤ Order.height (⟨Qt, inferInstance⟩ : PrimeSpectrum B)
  set Qpt : PrimeSpectrum B := ⟨Qt, inferInstance⟩ with hQpt
  set npt : PrimeSpectrum B := ⟨n, inferInstance⟩ with hnpt
  set Fpt : PrimeSpectrum (B ⧸ n) := ⟨F, hFp⟩ with hFpt
  set g := Ideal.primeSpectrumQuotientOrderIsoZeroLocus n with hg
  set φ : PrimeSpectrum (B ⧸ n) → PrimeSpectrum B := fun x => (g x : PrimeSpectrum B) with hφ
  have hφmono : StrictMono φ := fun a b hab => g.lt_iff_lt.mpr hab
  have hφF : φ Fpt = Qpt := by
    apply PrimeSpectrum.ext
    show (Ideal.comap (Ideal.Quotient.mk n) F) = Qt
    rw [hF, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact sup_eq_left.mpr hnle
  have : Nonempty (LTSeries (PrimeSpectrum (B ⧸ n))) := ⟨RelSeries.singleton _ Fpt⟩
  have : Nonempty (LTSeries (PrimeSpectrum B)) := ⟨RelSeries.singleton _ npt⟩
  have mapchain : ∀ (p : LTSeries (PrimeSpectrum (B ⧸ n))), RelSeries.last p = Fpt →
      ∃ p' : LTSeries (PrimeSpectrum B), p'.last = Qpt ∧ p'.length = p.length ∧ npt ≤ p'.head := by
    intro p hpF
    refine ⟨p.map φ hφmono, ?_, by rw [LTSeries.map_length], ?_⟩
    · rw [LTSeries.last_map, hpF, hφF]
    · rw [LTSeries.head_map]
      exact (g p.head).property
  have hcbound : ∀ (c : LTSeries (PrimeSpectrum B)), RelSeries.last c = npt →
      (c.length : ℕ∞) ≤ Order.height Qpt := by
    intro c hc
    have h1 : (c.length : ℕ∞) ≤ Order.height c.last := Order.length_le_height_last
    rw [hc] at h1
    exact h1.trans (Order.height_mono (by exact hnle))
  have hpbound : ∀ (p : LTSeries (PrimeSpectrum (B ⧸ n))), RelSeries.last p = Fpt →
      (p.length : ℕ∞) ≤ Order.height Qpt := by
    intro p hpF
    obtain ⟨p', hl, hlen, _⟩ := mapchain p hpF
    rw [← hlen, ← hl]
    exact Order.length_le_height_last
  rw [Order.height_eq_iSup_last_eq Fpt, Order.height_eq_iSup_last_eq npt]
  apply ENat.iSup_add_iSup_le
  intro p c
  rcases Classical.em (RelSeries.last p = Fpt) with hpF | hpF
  · rcases Classical.em (RelSeries.last c = npt) with hcn | hcn
    · rw [ciSup_pos hpF, ciSup_pos hcn]
      obtain ⟨p', hp'last, hp'len, hp'head⟩ := mapchain p hpF
      by_cases heq : c.last = p'.head
      · have hslen := RelSeries.smash_length c p' heq
        have hle := Order.length_le_height_last (p := c.smash p' heq)
        rw [RelSeries.last_smash, hp'last] at hle
        calc (p.length : ℕ∞) + (c.length : ℕ∞)
            = (((c.smash p' heq).length : ℕ) : ℕ∞) := by rw [hslen, hp'len]; push_cast; ring
          _ ≤ Order.height Qpt := hle
      · have hlt : c.last < p'.head := lt_of_le_of_ne (hcn ▸ hp'head) heq
        have hslen := RelSeries.append_length c p' hlt
        have hle := Order.length_le_height_last (p := c.append p' hlt)
        rw [RelSeries.last_append, hp'last] at hle
        calc (p.length : ℕ∞) + (c.length : ℕ∞)
            ≤ (((c.append p' hlt).length : ℕ) : ℕ∞) := by
              rw [hslen, hp'len]; exact_mod_cast by omega
          _ ≤ Order.height Qpt := hle
    · rw [ciSup_pos hpF, (iSup_neg hcn : (⨆ (_ : RelSeries.last c = npt), (c.length:ℕ∞)) = ⊥)]
      simpa using hpbound p hpF
  · rw [(iSup_neg hpF : (⨆ (_ : RelSeries.last p = Fpt), (p.length:ℕ∞)) = ⊥)]
    rcases Classical.em (RelSeries.last c = npt) with hcn | hcn
    · rw [ciSup_pos hcn]; simpa using hcbound c hcn
    · rw [(iSup_neg hcn : (⨆ (_ : RelSeries.last c = npt), (c.length:ℕ∞)) = ⊥)]; simp

private theorem pointwise_ascent {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (hgen : ((Submodule.spanFinrank (p.map (algebraMap R (Localization.AtPrime q))) : ℕ) : ℕ∞)
      ≤ p.height)
    (hreg : IsRegularLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let A := Localization.AtPrime q
  let I := p.map (algebraMap R A)
  let S := A ⧸ I
  have hnoeth : IsNoetherianRing A := inferInstance
  have hloc : IsLocalRing S := inferInstance
  have hgen' := key_generator_bound A S (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hgen'
  have hdim : ringKrullDim S = (Ideal.map (Ideal.Quotient.mk p) q).height := by
    let : (Ideal.map (Ideal.Quotient.mk p) q).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    let : IsLocalization.AtPrime A
        (Ideal.comap (Ideal.Quotient.mk p) (Ideal.map (Ideal.Quotient.mk p) q)) := by
      simpa only [Ideal.comap_map_mk hpq] using
        (inferInstance : IsLocalization.AtPrime A q)
    have h := ringKrullDim_quotient_map_ker_eq_height (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective (Ideal.map (Ideal.Quotient.mk p) q) A
    rwa [Ideal.mk_ker] at h
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    (↑(Submodule.spanFinrank (IsLocalRing.maximalIdeal A)) : WithBot ℕ∞)
      ≤ ↑(Submodule.spanFinrank I + Submodule.spanFinrank (IsLocalRing.maximalIdeal S)) := by
          exact_mod_cast hgen'
    _ = (↑(Submodule.spanFinrank I) : WithBot ℕ∞) +
          ↑(Submodule.spanFinrank (IsLocalRing.maximalIdeal S)) := by push_cast; rfl
    _ ≤ (↑p.height : WithBot ℕ∞) + ↑(Submodule.spanFinrank (IsLocalRing.maximalIdeal S)) :=
          add_le_add_left (WithBot.coe_le_coe.mpr hgen) _
    _ = ↑p.height + ringKrullDim S := by
          rw [hreg.spanFinrank_maximalIdeal]
    _ = ↑(p.height + (Ideal.map (Ideal.Quotient.mk p) q).height) := by
          rw [hdim]; push_cast; rfl
    _ ≤ (↑q.height : WithBot ℕ∞) := by
          exact_mod_cast (by simpa [add_comm] using height_map_quotient_add_height_le' p q hpq)
    _ = ringKrullDim A := (IsLocalization.AtPrime.ringKrullDim_eq_height q A).symm

private theorem regular_quotient_localization {R : Type*} [CommRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (qbar : Ideal (R ⧸ p)) [qbar.IsPrime]
    (hcomap : qbar.comap (Ideal.Quotient.mk p) = q)
    (hreg : IsRegularLocalRing (Localization.AtPrime qbar)) :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) := by
  let A := Localization.AtPrime q
  let I := p.map (algebraMap R A)
  have hmem : ∀ x : R, Ideal.Quotient.mk p x ∈ qbar ↔ x ∈ q := by
    intro x
    rw [← Ideal.mem_comap, hcomap]
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ p) q.primeCompl = qbar.primeCompl := by
    rw [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq]
    ext y
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mt (hmem x).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, fun hx ↦ hy ((hmem x).2 hx), rfl⟩
  have hloc : IsLocalization.AtPrime (A ⧸ I) qbar := by
    rw [IsLocalization.AtPrime, ← hsub]
    infer_instance
  let e := IsLocalization.algEquiv qbar.primeCompl
      (Localization.AtPrime qbar) (A ⧸ I)
  let : IsRegularLocalRing (Localization.AtPrime qbar) := hreg
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

private lemma exists_principal_generator_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (I : Ideal R)
    {z : S} (hz : z ∈ I.map (algebraMap R S)) :
    ∃ x ∈ I, z ∈ Ideal.span {algebraMap R S x} := by
  obtain ⟨⟨⟨x, hx⟩, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hz
  refine ⟨x, hx, (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units S t)).mp ?_⟩
  rw [ht]
  exact Ideal.mem_span_singleton_self _

private lemma exists_finset_generators_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (I : Ideal R)
    (hfg : (I.map (algebraMap R S)).FG) :
    ∃ t : Finset R, (↑t : Set R) ⊆ I ∧
      t.card ≤ (I.map (algebraMap R S)).spanFinrank ∧
      (Ideal.span (↑t : Set R)).map (algebraMap R S) = I.map (algebraMap R S) := by
  classical
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hx : ∀ y : {y : S // y ∈ s}, ∃ x ∈ I, (y : S) ∈ Ideal.span {algebraMap R S x} :=
    fun y => exists_principal_generator_of_mem_map M I (hspan ▸ Submodule.subset_span y.property)
  choose x hxmem hxspan using hx
  let t : Finset R := s.attach.image x
  have htI : (↑t : Set R) ⊆ I := by
    intro a ha
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ha
    exact hxmem y
  refine ⟨t, htI, ?_, ?_⟩
  · calc
      t.card ≤ s.attach.card := Finset.card_image_le
      _ = s.card := Finset.card_attach
      _ = _ := hcard
  · refine le_antisymm (Ideal.map_mono (Ideal.span_le.mpr htI)) ?_
    rw [← hspan]
    refine Submodule.span_le.mpr fun y hy => (Ideal.span_le.mpr ?_) (hxspan ⟨y, hy⟩)
    rintro _ rfl
    exact Ideal.mem_map_of_mem _
      (Ideal.subset_span (Finset.mem_image_of_mem _ (Finset.mem_attach _ _)))

private lemma exists_away_map_eq_of_map_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J p : Ideal R) [p.IsPrime] (hJI : J ≤ I)
    (hmap : J.map (algebraMap R (Localization.AtPrime p)) =
      I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ g ∉ p, ∀ q : Ideal R, ∀ [q.IsPrime], g ∉ q →
      J.map (algebraMap R (Localization.AtPrime q)) =
        I.map (algebraMap R (Localization.AtPrime q)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  have hx : ∀ y : {y : R // y ∈ s}, ∃ m : p.primeCompl, (m : R) * (y : R) ∈ J := by
    intro y
    have hy : (algebraMap R (Localization.AtPrime p)) y ∈
        J.map (algebraMap R (Localization.AtPrime p)) := by
      rw [hmap, ← hs]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span y.property)
    obtain ⟨m, hm, hmy⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
        (Localization.AtPrime p) J y).mp hy
    exact ⟨⟨m, hm⟩, hmy⟩
  choose m hm using hx
  let g : p.primeCompl := s.attach.prod m
  refine ⟨g, g.property, ?_⟩
  intro q _ hg
  apply le_antisymm (Ideal.map_mono hJI)
  rw [← hs, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro z ⟨y, hy, rfl⟩
  let yy : {y : R // y ∈ s} := ⟨y, hy⟩
  have hdvd : (m yy : R) ∣ (g : R) := by
    simpa [g, Submonoid.coe_prod] using
      (Finset.dvd_prod_of_mem (fun x : {y : R // y ∈ s} => (m x : R))
        (Finset.mem_attach _ yy))
  obtain ⟨d, hd⟩ := hdvd
  have hgy : (g : R) * y ∈ J := by
    rw [hd]
    convert J.mul_mem_left d (hm yy) using 1; ring
  have hgy' : (algebraMap R (Localization.AtPrime q)) ((g : R) * y) ∈
      J.map (algebraMap R (Localization.AtPrime q)) := Ideal.mem_map_of_mem _ hgy
  have hunit : IsUnit ((algebraMap R (Localization.AtPrime q)) (g : R)) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨(g : R), hg⟩ : q.primeCompl)
  apply (Ideal.mul_unit_mem_iff_mem _ hunit).mp
  simpa only [map_mul, mul_comm] using hgy'

private lemma exists_generator_bound_near_regular_prime {R : Type*} [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g ∉ p, ∀ q : Ideal R, ∀ [q.IsPrime], g ∉ q →
      ((Submodule.spanFinrank (p.map (algebraMap R (Localization.AtPrime q))) : ℕ) : ℕ∞)
        ≤ p.height := by
  classical
  let A := Localization.AtPrime p
  have hfg : (p.map (algebraMap R A)).FG := by
    have : IsNoetherianRing A := inferInstance
    exact IsNoetherian.noetherian _
  obtain ⟨t, htmem, htcard, htmap⟩ :=
    exists_finset_generators_map p.primeCompl p hfg
  let J : Ideal R := Ideal.span (t : Set R)
  have hJ : J ≤ p := Ideal.span_le.mpr htmem
  obtain ⟨g, hg, hspread⟩ := exists_away_map_eq_of_map_eq p J p hJ htmap
  refine ⟨g, hg, ?_⟩
  intro q _ hgq
  have hmin : ((Submodule.spanFinrank (p.map (algebraMap R A)) : ℕ) : ℕ∞) =
      p.height := by
    have hh := hreg.spanFinrank_maximalIdeal
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p),
      IsLocalization.AtPrime.ringKrullDim_eq_height p A] at hh
    exact WithBot.coe_injective hh
  have hmapq := hspread q hgq
  have hcardq : Submodule.spanFinrank (p.map (algebraMap R (Localization.AtPrime q)))
      ≤ t.card := by
    rw [← hmapq, show J = Ideal.span (t : Set R) from rfl, Ideal.map_span,
      ← Finset.coe_image]
    calc
      (Ideal.span (↑(t.image (algebraMap R (Localization.AtPrime q))) :
        Set (Localization.AtPrime q))).spanFinrank
        ≤ (t.image (algebraMap R (Localization.AtPrime q))).card := by
          simpa only [Set.ncard_coe_finset] using
            (Submodule.spanFinrank_span_le_ncard_of_finite
              (Finset.finite_toSet (t.image (algebraMap R (Localization.AtPrime q)))))
      _ ≤ t.card := Finset.card_image_le
  exact (Nat.cast_le.mpr hcardq).trans ((Nat.cast_le.mpr htcard).trans_eq hmin)

/-- **Stacks 07P9.** A Noetherian ring is J-1 if its quotient by every prime ideal is J-0. -/
@[stacks 07P9]
public theorem isJ1_of_forall_quotient_isJ0 (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ p : PrimeSpectrum R, IsJ0 (R ⧸ p.asIdeal)) :
    IsJ1 R := by
  apply (isJ1_iff_zeroLocus_inter_regularLocus_contains_nonempty_open R).2
  intro p hpreg
  obtain ⟨g, hg, hgen⟩ := exists_generator_bound_near_regular_prime p.asIdeal hpreg
  obtain ⟨W, hWopen, hWne, hWreg⟩ := h p
  let f : R →+* (R ⧸ p.asIdeal) := Ideal.Quotient.mk p.asIdeal
  obtain ⟨U, hUopen, hUeq⟩ :=
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ f Ideal.Quotient.mk_surjective).isInducing
      |>.image_eq_isOpen_inter_range hWopen
  have hbotW : (⊥ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈ W := by
    obtain ⟨w, hw⟩ := hWne
    exact hWopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le) hw
  have hcomapbot : PrimeSpectrum.comap f (⊥ : PrimeSpectrum (R ⧸ p.asIdeal)) = p :=
    PrimeSpectrum.ext Ideal.mk_ker
  have hpU : p ∈ U := by
    have himage : p ∈ PrimeSpectrum.comap f '' W := ⟨⊥, hbotW, hcomapbot⟩
    rw [hUeq] at himage
    exact himage.1
  let U' : Set (PrimeSpectrum R) := U ∩ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R))
  refine ⟨U', hUopen.inter PrimeSpectrum.isOpen_basicOpen, ?_, ?_⟩
  · refine ⟨p, ⟨hpU, (PrimeSpectrum.mem_basicOpen g p).2 hg⟩, ?_⟩
    exact (PrimeSpectrum.mem_zeroLocus p _).2 (fun _ hx => hx)
  · intro q hq
    obtain ⟨⟨hqU, hqD⟩, hqV⟩ := hq
    have hpq : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus q _).1 hqV
    have hqrange : q ∈ Set.range (PrimeSpectrum.comap f) := by
      rw [range_comap_of_surjective _ f Ideal.Quotient.mk_surjective]
      have hker : RingHom.ker f = p.asIdeal := Ideal.mk_ker
      rw [hker]
      exact hqV
    have hqimage : q ∈ PrimeSpectrum.comap f '' W := by
      rw [hUeq]
      exact ⟨hqU, hqrange⟩
    obtain ⟨qbar, hqbarW, hqbarEq⟩ := hqimage
    have hcomap : qbar.asIdeal.comap f = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hqbarEq
    have hquot := regular_quotient_localization p.asIdeal q.asIdeal qbar.asIdeal
      hcomap (hWreg hqbarW)
    have hbound := hgen q.asIdeal ((PrimeSpectrum.mem_basicOpen g q).1 hqD)
    exact ⟨hqV, pointwise_ascent p.asIdeal q.asIdeal hpq hbound hquot⟩

end

end

/-! ### Stacks Tag 07PA -/

section

section

universe u v

private lemma exists_basicOpen_subset_of_isOpen {A : Type*} [CommRing A]
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U) {q : PrimeSpectrum A} (hq : q ∈ U) :
    ∃ g : A, g ∉ q.asIdeal ∧ ↑(PrimeSpectrum.basicOpen g) ⊆ U := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff U).mp hU
  have hns : ¬s ⊆ q.asIdeal := by
    intro h
    exact ((show q ∈ Uᶜ by rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr h) hq)
  obtain ⟨g, hgs, hgq⟩ := Set.not_subset.mp hns
  refine ⟨g, hgq, fun q' hq' => ?_⟩
  by_contra hq'U
  have hmem : q' ∈ PrimeSpectrum.zeroLocus s := hs ▸ hq'U
  exact (PrimeSpectrum.mem_basicOpen g q').mp hq'
    ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem hgs)

/-- Regularity of the local ring at a prime of a localization can be checked at its comap. -/
private lemma isRegularLocalRing_atPrime_comap_iff {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B))) ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime q) q
  let e := (IsLocalization.algEquiv (q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (q.comap (algebraMap A B))) (Localization.AtPrime q)).toRingEquiv
  exact ⟨fun h => have := h; IsRegularLocalRing.of_ringEquiv e,
    fun h => have := h; IsRegularLocalRing.of_ringEquiv e.symm⟩

private lemma isRegularRing_localization_of_subset_regularLocus
    {A B : Type*} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (h : ∀ q : PrimeSpectrum B,
      IsRegularLocalRing (Localization.AtPrime ((q.asIdeal).comap (algebraMap A B)))) :
    IsRegularRing B := by
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing M B inferInstance
  rw [isRegularRing_iff]
  intro q hq
  exact (isRegularLocalRing_atPrime_comap_iff M q).1 (h ⟨q, hq⟩)

/-- If an injective finite type map sends a Noetherian domain into a J-0 domain, then the
source is J-0. -/
@[stacks 07PA]
public theorem isJ0_of_injective_finiteType
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (hS : IsJ0 S) :
    IsJ0 R := by
  obtain ⟨U, hU, ⟨q, hqU⟩, hUreg⟩ := hS
  obtain ⟨g, hgq, hgU⟩ := exists_basicOpen_subset_of_isOpen hU hqU
  have hg0 : g ≠ 0 := fun e => hgq (e ▸ q.asIdeal.zero_mem)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let Sg := Localization.Away g
  let : IsRegularRing Sg :=
    isRegularRing_localization_of_subset_regularLocus (Submonoid.powers g) fun Q =>
      hUreg (hgU (show (⟨Q.asIdeal.comap (algebraMap S Sg), inferInstance⟩ :
          PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen g by
        intro hmem
        exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
          (IsLocalization.map_units Sg
            (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)))))
  have hRinj : Function.Injective (algebraMap R Sg) := by
    rw [IsScalarTower.algebraMap_eq R S Sg]
    exact (IsLocalization.injective Sg (powers_le_nonZeroDivisors_of_noZeroDivisors hg0))
      |>.comp hinj
  let : Nontrivial Sg := hRinj.nontrivial
  let : Algebra.FiniteType R Sg := inferInstance
  obtain ⟨f, hf0, hfree⟩ :=
    Module.exists_ne_zero_free_localizedModule_away (R := R) (S := Sg) (M := Sg)
  let Rf := Localization.Away f
  let T := Localization (Algebra.algebraMapSubmonoid Sg (Submonoid.powers f))
  let hloc : IsLocalizedModule (Algebra.algebraMapSubmonoid Sg (Submonoid.powers f))
      (Algebra.linearMap Sg T) := inferInstance
  have hloc' : IsLocalizedModule (Submonoid.powers (algebraMap R Sg f))
      (Algebra.linearMap Sg T) := by
    change IsLocalizedModule (Submonoid.map (algebraMap R Sg) (Submonoid.powers f)) _ at hloc
    simpa only [Submonoid.map_powers] using hloc
  let := hloc'
  let : IsLocalizedModule (Submonoid.powers f)
      ((Algebra.linearMap Sg T).restrictScalars R) :=
    IsLocalizedModule.restrictScalars_powers f (Algebra.linearMap Sg T)
  let : Module.Free Rf T := hfree Rf T ((Algebra.linearMap Sg T).restrictScalars R)
  let : IsRegularRing T :=
    isRegularRing_localization_of_subset_regularLocus
      (Algebra.algebraMapSubmonoid Sg (Submonoid.powers f))
      fun _ => IsRegularRing.isRegularLocalRing_localization _
  let : Nontrivial T := (IsLocalization.injective T (M :=
      Algebra.algebraMapSubmonoid Sg (Submonoid.powers f)) (by
    show Submonoid.map (algebraMap R Sg) (Submonoid.powers f) ≤ nonZeroDivisors Sg
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ hRinj).mpr
      (nonZeroDivisors.ne_zero (powers_le_nonZeroDivisors_of_noZeroDivisors hf0 hx)))).nontrivial
  let : Module.FaithfullyFlat Rf T := inferInstance
  let : IsRegularRing Rf := IsRegularRing.of_faithfullyFlat T
  refine ⟨↑(PrimeSpectrum.basicOpen f), PrimeSpectrum.isOpen_basicOpen, ?_, ?_⟩
  · exact ⟨⟨⊥, inferInstance⟩, hf0⟩
  · intro p hp
    have hp' : (p.asIdeal.map (algebraMap R Rf)).IsPrime :=
      isPrime_map_algebraMap_of_notMem p.asIdeal hp
    let : Algebra Rf (Localization.AtPrime p.asIdeal) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
        p.asIdeal.primeCompl (Submonoid.powers_le.mpr hp)
    let : IsScalarTower R Rf (Localization.AtPrime p.asIdeal) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le ..
    have hi : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
        (p.asIdeal.map (algebraMap R Rf)) :=
      isLocalization_atPrime_map_of_notMem (B := Rf) (C := Localization.AtPrime p.asIdeal) hp
    exact IsRegularRing.isRegularLocalRing_of_isLocalization
      (p.asIdeal.map (algebraMap R Rf)) (Localization.AtPrime p.asIdeal)

end

end

/-! ### Stacks Tag 07PB -/

section

section

/-- The J-0 property descends from an away localization: its regular open set maps to an open set
of the source spectrum, and the local rings at corresponding primes are isomorphic. -/
public theorem isJ0_of_isLocalizationAway (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] (f : A) [IsLocalization.Away f B] (hB : IsJ0 B) :
    IsJ0 A := by
  obtain ⟨U, hU, hUne, hreg⟩ := hB
  let j : PrimeSpectrum B → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A B)
  have hj : Topology.IsOpenEmbedding j := PrimeSpectrum.localization_away_isOpenEmbedding B f
  refine ⟨j '' U, hj.isOpenMap U hU, hUne.image j, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  exact (isRegularLocalRing_atPrime_comap_iff (Submonoid.powers f) y.asIdeal).2 (hreg hy)

/-- A nontrivial regular ring is J-0, with the whole spectrum as regular open set. -/
public theorem isJ0_of_isRegularRing (A : Type*) [CommRing A] [IsRegularRing A]
    [Nontrivial A] : IsJ0 A :=
  ⟨Set.univ, isOpen_univ, Set.univ_nonempty,
    fun x _ => IsRegularRing.isRegularLocalRing_localization x.asIdeal⟩

/-- A Noetherian J-0 domain has a nonzero element whose away localization is regular. -/
public theorem exists_regular_localizationAway (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : IsJ0 A) :
    ∃ f : A, f ≠ 0 ∧ IsRegularRing (Localization.Away f) := by
  obtain ⟨U, hU, ⟨x, hx⟩, hreg⟩ := hA
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx hU
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hxf
  refine ⟨f, hf, ?_⟩
  refine isRegularRing_localization_of_subset_regularLocus (Submonoid.powers f) fun q => ?_
  have hmem : (⟨q.asIdeal.comap (algebraMap A (Localization.Away f)), inferInstance⟩ :
      PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact ⟨q, rfl⟩
  exact hreg (hfU hmem)

/-- **Stacks 07PB.** Let `R → S` be an injective finite type map of domains. If `R` is
Noetherian and J-0 and the induced extension of fraction fields is separable, then `S` is J-0. -/
@[stacks 07PB, ega "IV 6.12.4.1"]
public theorem isJ0_of_finiteType_injective_of_isSeparable_fractionRing
    (R S : Type*) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (hR : IsJ0 R) (hRS : Function.Injective (algebraMap R S))
    (hsep :
      letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
      letI : Algebra (FractionRing R) (FractionRing S) :=
        FractionRing.liftAlgebra R (FractionRing S)
      Algebra.IsSeparableExtension (FractionRing R) (FractionRing S)) :
    IsJ0 S := by
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  let : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have hsm : Algebra.IsSmoothAt R (⊥ : Ideal S) :=
    (Algebra.isSmoothAt_bot_iff_isSeparableExtension R S (FractionRing R)
      (FractionRing S)).mpr hsep
  obtain ⟨f, hf, hRf⟩ := exists_regular_localizationAway R hR
  have : Algebra.FinitePresentation R S :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  obtain ⟨g, hg, hSg⟩ := hsm.exists_notMem_smooth R (⊥ : Ideal S)
  have hg0 : g ≠ 0 := by simpa using hg
  let Rf := Localization.Away f
  let Sg := Localization.Away g
  let T := Localization.Away ((algebraMap R Sg) f)
  let : IsDomain Sg := IsLocalization.Away.isDomain Sg hg0
  have hSgMap : Function.Injective (algebraMap S Sg) :=
    IsLocalization.injective Sg (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  have hSf : (algebraMap R S) f ≠ 0 := fun h => hf (hRS (by simpa using h))
  have hfSg : (algebraMap R Sg) f ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R S Sg]
    exact fun h ↦ hSf (hSgMap (by simpa using h))
  let : IsDomain T := IsLocalization.Away.isDomain T hfSg
  let : IsRegularRing Rf := hRf
  let : Algebra Rf T :=
    (IsLocalization.Away.map Rf T (algebraMap R Sg) f).toAlgebra
  have : IsScalarTower R Rf T := IsScalarTower.of_algebraMap_eq' (by
    show (algebraMap Sg T).comp (algebraMap R Sg) =
      (IsLocalization.Away.map Rf T (algebraMap R Sg) f).comp (algebraMap R Rf)
    exact (IsLocalization.map_comp _).symm)
  have : Algebra.FormallySmooth R T := Algebra.FormallySmooth.comp R Sg T
  have : Algebra.FinitePresentation R T := Algebra.FinitePresentation.trans R Sg T
  have : Algebra.FiniteType R Rf :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) Rf
  have hTsm : Algebra.Smooth Rf T :=
    ⟨Algebra.FormallySmooth.localization_base (Submonoid.powers f),
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R Rf T⟩
  let : Algebra.Smooth Rf T := hTsm
  let : IsRegularRing T := Algebra.isRegularRing_of_smooth Rf T
  exact isJ0_of_isLocalizationAway S Sg g
    (isJ0_of_isLocalizationAway Sg T ((algebraMap R Sg) f)
      (isJ0_of_isRegularRing T))

end

end

/-! ### Stacks Tag 07PC -/

section

section

universe u

open scoped TensorProduct

/-- A finite extension of a fraction field has a finite algebra model with the same
fraction field. -/
@[ega "IV 12.1.1.3" "partial"]
public theorem Algebra.exists_finite_subalgebra_isFractionRing
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra A L] [IsScalarTower A K L] :
    ∃ B : Subalgebra A L, Module.Finite A B ∧ IsFractionRing B L := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let B : Subalgebra A L := Algebra.adjoin A (Set.range b)
  have hfin : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range b) (Set.forall_mem_range.2 hb)
  have hinj : Function.Injective (algebraMap B L) := Subtype.val_injective
  let : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr hinj
  have hfrac : IsFractionRing B L := by
    refine IsFractionRing.of_field B L fun z => ?_
    have hz : z ∈ Submodule.span K (Set.range b) := by
      rw [b.span_eq]
      trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors A) K (Set.range b) z hz
    have hmem : (t : A) • z ∈ B := Algebra.span_le_adjoin A _ ht
    refine ⟨⟨(t : A) • z, hmem⟩, algebraMap A B t, ?_⟩
    have ht0 : algebraMap A L (t : A) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K L]
      exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
          (nonZeroDivisors.ne_zero t.2))
    show z = ((t : A) • z) / algebraMap A L t
    rw [Algebra.smul_def]
    exact (mul_div_cancel_left₀ z ht0).symm
  exact ⟨B, hfin, hfrac⟩

/-- A finite extension of a residue field admits a finite algebra model over the
original ring. -/
private theorem exists_finite_subalgebra_residueField
    (R : Type*) [CommRing R] (p : PrimeSpectrum R)
    (L : Type*) [Field L] [Algebra p.asIdeal.ResidueField L]
    [Module.Finite p.asIdeal.ResidueField L]
    [Algebra R L]
    (hRL : algebraMap R L =
      (algebraMap p.asIdeal.ResidueField L).comp
        (algebraMap R p.asIdeal.ResidueField)) :
    ∃ B : Subalgebra R L, Module.Finite R B ∧ IsFractionRing B L := by
  let A := R ⧸ p.asIdeal
  let K := p.asIdeal.ResidueField
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have hAKL : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRAL : IsScalarTower R A L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [hRL, RingHom.comp_apply, IsScalarTower.algebraMap_apply R A K]
    rfl
  obtain ⟨B, hBfin, hBfrac⟩ :=
    Algebra.exists_finite_subalgebra_isFractionRing A K L
  refine ⟨B.restrictScalars R, ?_, hBfrac⟩
  show Module.Finite R B
  exact Module.Finite.trans A B

/-- The tensor-product image of two domain models has the compositum as its
fraction field when the tensor product of their fraction fields maps onto it. -/
private theorem isFractionRing_range_productMap
    (R : Type*) [CommRing R]
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra R A] [Algebra R B]
    (k K L E : Type*) [Field k] [Field K] [Field L] [Field E]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra R E]
    (fA : A →ₐ[R] E) (fB : B →ₐ[R] E)
    [Algebra k K] [Algebra k L] [Algebra k E]
    (gK : K →ₐ[k] E) (gL : L →ₐ[k] E)
    (hA : ∀ a, fA a = gK (algebraMap A K a))
    (hB : ∀ b, fB b = gL (algebraMap B L b))
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap gL gK)) :
    IsFractionRing (Algebra.TensorProduct.productMap fB fA).range E := by
  let f := Algebra.TensorProduct.productMap fB fA
  let T := f.range
  let iA : A →ₐ[R] T := f.rangeRestrict.comp Algebra.TensorProduct.includeRight
  let iB : B →ₐ[R] T := f.rangeRestrict.comp Algebra.TensorProduct.includeLeft
  have hiA (a : A) : algebraMap T E (iA a) = fA a :=
    Algebra.TensorProduct.productMap_right_apply fB fA a
  have hiB (b : B) : algebraMap T E (iB b) = fB b :=
    Algebra.TensorProduct.productMap_left_apply fB fA b
  let : FaithfulSMul T E :=
    (faithfulSMul_iff_algebraMap_injective T E).mpr Subtype.val_injective
  have hrepr : ∀ t : L ⊗[k] K,
      ∃ a b : T, algebraMap T E b ≠ 0 ∧
        Algebra.TensorProduct.productMap gL gK t =
          algebraMap T E a / algebraMap T E b := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        exact ⟨0, 1, by simp, by simp⟩
    | tmul l x =>
        obtain ⟨bn, bd, hbd, hl⟩ := IsFractionRing.div_surjective B l
        obtain ⟨an, ad, had, hx⟩ := IsFractionRing.div_surjective A x
        refine ⟨iB bn * iA an, iB bd * iA ad, ?_, ?_⟩
        · rw [map_mul, hiB, hiA, hB, hA]
          exact mul_ne_zero
            (by simpa using gL.injective.ne ((IsFractionRing.injective B L).ne
              (nonZeroDivisors.ne_zero hbd)))
            (by simpa using gK.injective.ne ((IsFractionRing.injective A K).ne
              (nonZeroDivisors.ne_zero had)))
        · rw [Algebra.TensorProduct.productMap_apply_tmul, ← hl, ← hx]
          simp only [map_mul, hiB, hiA, hB, hA]
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    | add t₁ t₂ ih₁ ih₂ =>
        obtain ⟨a₁, b₁, hb₁, ht₁⟩ := ih₁
        obtain ⟨a₂, b₂, hb₂, ht₂⟩ := ih₂
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
        · simpa only [map_mul] using mul_ne_zero hb₁ hb₂
        · rw [map_add, ht₁, ht₂, map_add, map_mul, map_mul, map_mul]
          field_simp
  refine IsFractionRing.of_field T E fun x => ?_
  obtain ⟨t, rfl⟩ := hsurj x
  obtain ⟨a, b, _, h⟩ := hrepr t
  exact ⟨a, b, h⟩

/-- Separability of the induced fraction-field extension can be checked in any
compatible models of the two fraction fields. -/
private theorem isSeparableExtension_fractionRing_of_isFractionRing
    (A B : Type u) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] (hAB : Function.Injective (algebraMap A B))
    (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra.IsSeparableExtension K L]
    (hcomm : ∀ a : A,
      algebraMap K L (algebraMap A K a) =
        algebraMap B L (algebraMap A B a)) :
    letI : FaithfulSMul A B :=
      (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
    letI : Algebra (FractionRing A) (FractionRing B) :=
      FractionRing.liftAlgebra A (FractionRing B)
    Algebra.IsSeparableExtension (FractionRing A) (FractionRing B) := by
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
  let : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  let eA : FractionRing A ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) K
  let eB : FractionRing B ≃ₐ[B] L :=
    IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) L
  have hcompat : (algebraMap K L).comp eA.toRingHom =
      eB.toRingHom.comp (algebraMap (FractionRing A) (FractionRing B)) := by
    apply IsFractionRing.ringHom_ext (A := A) (K := FractionRing A)
    intro a
    show algebraMap K L (eA (algebraMap A (FractionRing A) a)) =
      eB (algebraMap (FractionRing A) (FractionRing B)
        (algebraMap A (FractionRing A) a))
    rw [eA.commutes a, hcomm a, ← eB.commutes (algebraMap A B a)]
    congr 1
    rw [FractionRing.algebraMap_liftAlgebra, IsFractionRing.lift_algebraMap]
    exact (IsScalarTower.algebraMap_apply A B (FractionRing B) a).symm
  have hform : (algebraMap K L).FormallySmooth :=
    RingHom.formallySmooth_algebraMap.mpr
      ((Algebra.FormallySmooth.iff_isSeparableExtension K L).mpr inferInstance)
  have hform' :
      (algebraMap (FractionRing A) (FractionRing B)).FormallySmooth := by
    have h₁ := RingHom.FormallySmooth.respectsIso.2
      (algebraMap K L) eA.toRingEquiv hform
    have h₂ := RingHom.FormallySmooth.respectsIso.1
      ((algebraMap K L).comp eA.toRingHom) eB.symm.toRingEquiv h₁
    have heq : eB.symm.toRingHom.comp ((algebraMap K L).comp eA.toRingHom) =
        algebraMap (FractionRing A) (FractionRing B) := by
      rw [hcompat]
      ext x
      simp
    exact heq ▸ h₂
  exact (Algebra.FormallySmooth.iff_isSeparableExtension
    (FractionRing A) (FractionRing B)).mp
    (RingHom.formallySmooth_algebraMap.mp hform')

/-- A domain which is J-1 is J-0. -/
private lemma isJ0_of_isJ1 (A : Type u) [CommRing A] [IsDomain A]
    (h : IsJ1 A) : IsJ0 A := by
  refine ⟨{x | IsRegularLocalRing (Localization.AtPrime x.asIdeal)}, h, ?_, fun _ hx => hx⟩
  refine ⟨⟨⊥, inferInstance⟩, ?_⟩
  show IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A))
  have : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl
        (Localization.AtPrime (⊥ : Ideal A)))
  let : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  infer_instance

/-- Condition (2) of `isJ2_tfae` implies condition (1). -/
private lemma isJ2_of_domain_isJ0 (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S],
      IsJ0 S) : IsJ2 R := by
  intro S _ _ _
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isJ1_of_forall_quotient_isJ0
  intro q
  let : Algebra R (S ⧸ q.asIdeal) :=
    ((Ideal.Quotient.mk q.asIdeal).comp (algebraMap R S)).toAlgebra
  have : Algebra.FiniteType R (S ⧸ q.asIdeal) := by
    let f : S →ₐ[R] (S ⧸ q.asIdeal) :=
      { toRingHom := Ideal.Quotient.mk q.asIdeal
        commutes' := fun _ => rfl }
    exact Algebra.FiniteType.of_surjective f Ideal.Quotient.mk_surjective
  exact h (S ⧸ q.asIdeal)

set_option maxHeartbeats 2000000 in
-- The tensor-image construction and its induced algebra structures require deeper elaboration.
set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 07PC.** For a Noetherian ring `R`, the following are equivalent: `R` is J-2;
every finite type domain algebra over `R` is J-0; every finite algebra over `R` is J-1; and
every finite purely inseparable extension of a residue field of `R` is the fraction field of a
finite J-0 domain algebra over `R`. -/
@[stacks 07PC, ega "IV 6.12.4"]
public theorem isJ2_tfae (R : Type u) [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsJ2 R,
        ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S],
          IsJ0 S,
        ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
          IsJ1 S,
        ∀ (p : PrimeSpectrum R) (L : Type u) [Field L]
          [Algebra p.asIdeal.ResidueField L] [Module.Finite p.asIdeal.ResidueField L]
          [IsPurelyInseparable p.asIdeal.ResidueField L],
          letI : Algebra R L :=
            ((algebraMap p.asIdeal.ResidueField L).comp
              (algebraMap R p.asIdeal.ResidueField)).toAlgebra
          ∃ R' : Subalgebra R L,
            Module.Finite R R' ∧ IsJ0 R' ∧ IsFractionRing R' L ] := by
  tfae_have 1 → 2 := by
    intro h S _ _ _ _
    exact isJ0_of_isJ1 S (h S)
  tfae_have 2 → 1 := isJ2_of_domain_isJ0 R
  tfae_have 1 → 3 := by
    intro h S _ _ _
    have : Algebra.FiniteType R S := Module.Finite.finiteType S
    exact h S
  tfae_have 3 → 4 := by
    intro h p L _ _ _ _
    let : Algebra R L :=
      ((algebraMap p.asIdeal.ResidueField L).comp
        (algebraMap R p.asIdeal.ResidueField)).toAlgebra
    obtain ⟨B, hBfin, hBfrac⟩ :=
      exists_finite_subalgebra_residueField R p L rfl
    exact ⟨B, hBfin, isJ0_of_isJ1 B (h B), hBfrac⟩
  tfae_have 4 → 2 := by
    intro h S _ _ _ _
    let q : PrimeSpectrum S := ⟨⊥, inferInstance⟩
    let p : PrimeSpectrum R := q.comap (algebraMap R S)
    let k := p.asIdeal.ResidueField
    let K := q.asIdeal.ResidueField
    let : Algebra k K :=
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl).toAlgebra
    have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R S) rfl r).symm
    have : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R S K
    have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.of_comp R k K
    let Ω := AlgebraicClosure K
    obtain ⟨K', k', hKfin, hKpi, hkfin, hkpi, hksep,
        hcompositum, hsurj, hker⟩ :=
      exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType k K Ω
    let : Module.Finite k k' := hkfin
    let : IsPurelyInseparable k k' := hkpi
    let : Algebra R k' :=
      ((algebraMap k k').comp (algebraMap R k)).toAlgebra
    obtain ⟨B, hBfin, hBJ0, hBfrac⟩ := h p k'
    let : Algebra R K' :=
      ((algebraMap k' K').comp (algebraMap R k')).toAlgebra
    let fS : S →ₐ[R] K' :=
      { toRingHom := (algebraMap K K').comp (algebraMap S K)
        commutes' := by
          intro r
          show algebraMap K K' (algebraMap S K (algebraMap R S r)) =
            algebraMap k' K' (algebraMap k k' (algebraMap R k r))
          rw [← IsScalarTower.algebraMap_apply R S K,
            IsScalarTower.algebraMap_apply R k K,
            ← IsScalarTower.algebraMap_apply k K K',
            ← IsScalarTower.algebraMap_apply k k' K'] }
    let fB : B →ₐ[R] K' :=
      { toRingHom := (algebraMap k' K').comp (algebraMap B k')
        commutes' := fun _ => rfl }
    let T : Subalgebra R K' := (Algebra.TensorProduct.productMap fB fS).range
    have hTfrac : IsFractionRing T K' := by
      let : IsFractionRing B k' := hBfrac
      exact isFractionRing_range_productMap R S B k K k' K' fS fB
        (IsScalarTower.toAlgHom k K K') (IsScalarTower.toAlgHom k k' K')
        (fun _ => rfl) (fun _ => rfl) hsurj
    let f : B ⊗[R] S →ₐ[R] K' := Algebra.TensorProduct.productMap fB fS
    let iS : S →ₐ[R] T := f.rangeRestrict.comp Algebra.TensorProduct.includeRight
    let iB : B →ₐ[R] T := f.rangeRestrict.comp Algebra.TensorProduct.includeLeft
    have hiS (s : S) : algebraMap T K' (iS s) = fS s :=
      Algebra.TensorProduct.productMap_right_apply fB fS s
    have hiB (b : B) : algebraMap T K' (iB b) = fB b :=
      Algebra.TensorProduct.productMap_left_apply fB fS b
    have : Algebra.FiniteType R B := Module.Finite.finiteType B
    have : Algebra.FiniteType R T := by
      let : Algebra B (B ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
      have : IsScalarTower R B (B ⊗[R] S) := inferInstance
      have : Algebra.FiniteType R (B ⊗[R] S) :=
        Algebra.FiniteType.trans (R := R) (S := B) (A := B ⊗[R] S)
          inferInstance inferInstance
      exact Algebra.FiniteType.of_surjective f.rangeRestrict
        (AlgHom.rangeRestrict_surjective f)
    let : Algebra B T := iB.toAlgebra
    have : IsScalarTower R B T :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := B) (A := T)
        (fun r => (iB.commutes r).symm)
    let : Algebra S T := iS.toAlgebra
    have : IsScalarTower R S T :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := T)
        (fun r => (iS.commutes r).symm)
    have : Algebra.FiniteType B T :=
      Algebra.FiniteType.of_restrictScalars_finiteType R B T
    have : Algebra.FiniteType S T :=
      Algebra.FiniteType.of_restrictScalars_finiteType R S T
    have hBTinj : Function.Injective (algebraMap B T) := by
      intro x y hxy
      change iB x = iB y at hxy
      have hxy' : fB x = fB y := by
        simpa only [hiB] using congrArg (algebraMap T K') hxy
      exact IsFractionRing.injective B k' ((algebraMap k' K').injective hxy')
    have hSTinj : Function.Injective (algebraMap S T) := by
      intro x y hxy
      change iS x = iS y at hxy
      have hxy' : fS x = fS y := by
        simpa only [hiS] using congrArg (algebraMap T K') hxy
      exact IsFractionRing.injective S K ((algebraMap K K').injective hxy')
    have : Algebra.IsSeparableExtension k' K' := hksep
    let : IsFractionRing B k' := hBfrac
    let : IsFractionRing T K' := hTfrac
    have hcommB (b : B) :
        algebraMap k' K' (algebraMap B k' b) = algebraMap T K' (algebraMap B T b) :=
      (hiB b).symm
    have hsep := isSeparableExtension_fractionRing_of_isFractionRing
      B T hBTinj k' K' hcommB
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
    have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
    have hTJ0 : IsJ0 T :=
      isJ0_of_finiteType_injective_of_isSeparable_fractionRing
        B T hBJ0 hBTinj hsep
    exact isJ0_of_injective_finiteType S T hSTinj hTJ0
  tfae_finish

end

end

end
