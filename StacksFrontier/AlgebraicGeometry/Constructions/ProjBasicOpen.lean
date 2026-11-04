module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksCore.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs

/-!
# Standard opens of the homogeneous spectrum

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring. For a homogeneous element `f` of positive degree the
standard open `D₊(f) ⊆ Proj 𝒜` is the set of relevant homogeneous primes not containing `f`, and
these sets form a basis of the topology. This file collects the elementary facts about
containments between standard opens that the construction of `Proj` as a scheme rests on.

An inclusion `D₊(g) ⊆ D₊(f)` of standard opens of positive-degree homogeneous elements has three
equivalent algebraic readings, recorded here: a positive power of `g` is a homogeneous multiple
of `f`; `f` becomes invertible in the localization `A_g`; and the degree-zero fraction
`f ^ deg g / g ^ deg f` is invertible in the degree-zero localization `A₍g₎`. Dually, a family of
standard opens covers `D₊(f)` exactly when the corresponding degree-zero fractions generate the
unit ideal of `A₍f₎`, and every open covering of `D₊(f)` is refined by a *finite* family of
standard opens of positive-degree homogeneous elements — the quasi-compactness of `D₊(f)` in the
form in which the structure sheaf uses it.

## Main results

* `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le`: a containment `D₊(g) ⊆ D₊(f)` gives an
  equality `g ^ e = a * f` with `e` positive and `a` homogeneous.
* `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`: the same equality with the
  degree of `a` in the conclusion, namely `deg a = e * deg g - deg f`, the power `e` being chosen
  large enough that this subtraction does not truncate.
* `ProjectiveSpectrum.exists_finite_basicOpen_refinement`: every open covering of `D₊(f)` admits a
  finite refinement by standard opens of positive-degree homogeneous elements.
* `ProjectiveSpectrum.isUnit_algebraMap_away_of_basicOpen_le`: `f` is a unit in `A_g`.
* `ProjectiveSpectrum.isUnit_isLocalizationElem_of_basicOpen_le`: the degree-zero fraction
  `f ^ deg g / g ^ deg f` is a unit in `A₍g₎`.
* `AlgebraicGeometry.Proj.basicOpen_le_iSup_iff_span_isLocalizationElem_eq_top`: the unit-ideal
  criterion for a family of standard opens to cover `D₊(f)`.
* `AlgebraicGeometry.Proj.exists_homogeneous_awayι_preimage_basicOpen_eq`: every standard open
  `D(g) ⊆ Spec A₍f₎` is the standard open `D₊(h) ⊆ D₊(f)` of a homogeneous `h` of positive
  degree, and `h` can be chosen so that `g = h / f ^ n`.

## Implementation notes

The degrees of `f` and `g` are supplied explicitly as hypotheses `f ∈ 𝒜 d` with `0 < d`, rather
than extracted from a bundled homogeneous element, so that the degree appearing in the conclusion
is the one the caller chose. Where the degree of the coefficient produced is not part of the
conclusion, homogeneity is expressed by the unbundled `SetLike.IsHomogeneousElem`.

The two hypotheses `AddSubmonoidClass σ A` and `AddSubgroupClass σ A` are kept apart: the
divisibility and refinement statements need only a monoid grading, whereas the invertibility
statements and the unit-ideal criterion go through the degree-zero localization `A₍f₎` and the
identification `D₊(f) ≅ Spec A₍f₎`, which need subtraction of degrees.

The finite refining family is indexed by `Fin n`; its members are required both to cover exactly
`D₊(f)` and individually to lie in members of the given covering. The covering members
themselves need not lie in `D₊(f)`. In the unit-ideal criterion the covering family is an
arbitrary indexed family, since the criterion needs no finiteness.

The identification of `D₊(f)` with `Spec A₍f₎` is used through the open immersion
`AlgebraicGeometry.Proj.awayι`, and a correspondence between an open of `Spec A₍f₎` and an open of
`D₊(f)` is recorded as the pair of equations `awayι ⁻¹ᵁ D₊(h) = D(g)` and `awayι ''ᵁ D(g) = D₊(h)`,
following the preimage spelling of `AlgebraicGeometry.Proj.awayι_preimage_basicOpen`. The degree of
the homogeneous element produced from a fraction `g = h / f ^ n` is `n • deg f`, written as a
scalar multiple because that is the form in which `HomogeneousLocalization.Away.mk` records it.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01MA](https://stacks.math.columbia.edu/tag/01MA)
-/

@[expose] public section

namespace ProjectiveSpectrum

universe u v w

section AddSubmonoidClass

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If `f` and `g` are homogeneous elements of positive degree and `D₊(g) ⊆ D₊(f)`, then
a positive power of `g` is a homogeneous multiple of `f`. -/
public theorem exists_pow_eq_mul_of_basicOpen_le {f g : A} {m n : ℕ}
    (hf : f ∈ 𝒜 m) (_hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ a : A, SetLike.IsHomogeneousElem 𝒜 a ∧ g ^ e = a * f := by
  have hopen : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f := by
    intro p hp
    rw [PrimeSpectrum.mem_basicOpen] at hp ⊢
    let q : ProjectiveSpectrum 𝒜 :=
      { asHomogeneousIdeal := p.asIdeal.homogeneousCore 𝒜
        isPrime := p.isPrime.homogeneousCore
        not_irrelevant_le := fun h => hp (Ideal.toIdeal_homogeneousCore_le 𝒜 p.asIdeal
          (h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hg))) }
    exact fun hfp => (hfg (show q ∈ ProjectiveSpectrum.basicOpen 𝒜 g from
      fun h => hp (Ideal.toIdeal_homogeneousCore_le 𝒜 p.asIdeal h)))
        (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨m, hf⟩ hfp)
  obtain ⟨r, hr⟩ := Ideal.mem_radical_iff.mp
    ((PrimeSpectrum.basicOpen_le_basicOpen_iff g f).mp hopen)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (show
    g ^ (r + 1) ∈ Ideal.span ({f} : Set A) by
      simpa only [pow_succ] using (Ideal.span ({f} : Set A)).mul_mem_right g hr)
  let e := r + 1
  have ha : g ^ e = a * f := by simpa only [e, mul_comm] using ha
  have hpw : g ^ e ∈ 𝒜 (e * n) := by
    simpa [mul_comm] using SetLike.pow_mem_graded e hg
  have hproj := congrArg (fun x => (DirectSum.decompose 𝒜 x (e * n) : A)) ha
  rw [DirectSum.decompose_of_mem_same 𝒜 hpw] at hproj
  by_cases hmf : m ≤ e * n
  · refine ⟨e, by simp [e], DirectSum.decompose 𝒜 a (e * n - m),
      ⟨e * n - m, (DirectSum.decompose 𝒜 a (e * n - m)).property⟩, ?_⟩
    rwa [DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hf hmf] at hproj
  · refine ⟨e, by simp [e], 0, ⟨0, zero_mem _⟩, ?_⟩
    simpa only [DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 hf hmf,
      zero_mul] using hproj

/-- The same containment `D₊(g) ⊆ D₊(f)`, with the **degree of the coefficient** in the
conclusion: the power `e` can be chosen with `m ≤ e * n`, and then the coefficient is
homogeneous of the degree `e * n - m` forced by counting degrees in `g ^ e = a * f`.

The degree is forced whenever `g ^ e ≠ 0`, since `g ^ e` then lies in a single homogeneous piece;
and when `g ^ e = 0` the power can be enlarged until `m ≤ e * n` and the coefficient taken to be
`0`, which is homogeneous of every degree. So no hypothesis beyond the containment is needed. -/
@[ega "II 2.3.15" "partial"]
public theorem exists_pow_eq_mul_of_basicOpen_le_degree {f g : A} {m n : ℕ}
    (hf : f ∈ 𝒜 m) (hm : 0 < m) (hg : g ∈ 𝒜 n) (hn : 0 < n)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    ∃ e : ℕ, 1 ≤ e ∧ m ≤ e * n ∧ ∃ a : A, a ∈ 𝒜 (e * n - m) ∧ g ^ e = a * f := by
  obtain ⟨e, he, a, ⟨t, hat⟩, hga⟩ := exists_pow_eq_mul_of_basicOpen_le 𝒜 hf hm hg hn hfg
  by_cases hz : g ^ e = 0
  · refine ⟨e + m, by omega, ?_, 0, zero_mem _, ?_⟩
    · calc m ≤ (e + m) * 1 := by omega
        _ ≤ (e + m) * n := Nat.mul_le_mul_left _ hn
    · rw [pow_add, hz, zero_mul, zero_mul]
  · have hpw : g ^ e ∈ 𝒜 (e * n) := by
      simpa [mul_comm] using SetLike.pow_mem_graded e hg
    have haf : g ^ e ∈ 𝒜 (t + m) := hga ▸ SetLike.mul_mem_graded hat hf
    have hdeg : e * n = t + m := DirectSum.degree_eq_of_mem_mem 𝒜 hpw haf hz
    exact ⟨e, he, by omega, a, by rwa [show e * n - m = t by omega], hga⟩

/-- A family of homogeneous elements whose standard opens cover `D₊(f)` has a finite subfamily
whose standard opens already cover it: the elements `f * (gᵢ)` span an ideal whose radical
contains `f`, so a power of `f` lies in the span of finitely many of them. -/
private theorem finite_homogeneous_subcover {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) {Q : Type*} (g : Q → A) (e : Q → ℕ)
    (hg : ∀ q, g q ∈ 𝒜 (e q))
    (hcover : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⨆ q, ProjectiveSpectrum.basicOpen 𝒜 (g q)) :
    ∃ t : Finset Q, ∀ x, x ∈ ProjectiveSpectrum.basicOpen 𝒜 f →
      ∃ q ∈ t, x ∈ ProjectiveSpectrum.basicOpen 𝒜 (g q) := by
  classical
  let I : Ideal A := Ideal.span (Set.range g)
  have hI : I.IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro x ⟨q, rfl⟩
    exact ⟨e q, hg q⟩
  have hrad : f ∈ I.radical := by
    rw [hI.radical_eq, Ideal.mem_sInf]
    rintro J ⟨hJhom, hIJ, hJprime⟩
    by_contra hfJ
    by_cases hirr : HomogeneousIdeal.irrelevant 𝒜 ≤ (⟨J, hJhom⟩ : HomogeneousIdeal 𝒜)
    · exact hfJ (hirr (HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) hd hf))
    · let x : ProjectiveSpectrum 𝒜 := ⟨⟨J, hJhom⟩, hJprime, hirr⟩
      have hxf : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f := hfJ
      obtain ⟨q, hxq⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge hxf)
      have hgq : g q ∉ J := (ProjectiveSpectrum.mem_basicOpen 𝒜 (g q) x).mp hxq
      exact hgq (hIJ (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff.mp hrad)
  obtain ⟨T, hT, hpow⟩ := Submodule.mem_span_finite_of_mem_span hn
  let qOf : T → Q := fun a => Classical.choose (Set.mem_range.mp (hT a.2))
  have hqOf (a : T) : g (qOf a) = a.1 :=
    Classical.choose_spec (Set.mem_range.mp (hT a.2))
  let t : Finset Q := Finset.univ.image qOf
  have hTsub : (T : Set A) ⊆ g '' (t : Set Q) := by
    intro a ha
    let a' : T := ⟨a, ha⟩
    exact ⟨qOf a',
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, rfl⟩), hqOf a'⟩
  have hpow' : f ^ n ∈ Ideal.span (g '' (t : Set Q)) :=
    (Ideal.span_mono hTsub) hpow
  refine ⟨t, fun x hx => ?_⟩
  by_contra hxnot
  have hgmem : ∀ q ∈ t, g q ∈ x.asHomogeneousIdeal := by
    intro q hqt
    have hxq : x ∉ ProjectiveSpectrum.basicOpen 𝒜 (g q) := fun hxq => hxnot ⟨q, hqt, hxq⟩
    simpa [ProjectiveSpectrum.mem_basicOpen] using hxq
  have hpowx : f ^ n ∈ x.asHomogeneousIdeal :=
    (Ideal.span_le.mpr (by
      rintro y ⟨q, hqt, rfl⟩
      exact hgmem q hqt)) hpow'
  exact (ProjectiveSpectrum.mem_basicOpen 𝒜 f x).mp hx
    (x.isPrime.mem_of_pow_mem n hpowx)

/-- Let `f` be a homogeneous element of positive degree in a graded ring. Every open covering of
the projective standard open `D₊(f)` admits a finite refinement by projective standard opens
`D₊(gᵢ)`, where each `gᵢ` is again homogeneous of positive degree. -/
public theorem exists_finite_basicOpen_refinement {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {ι : Type v} (U : ι → TopologicalSpace.Opens (ProjectiveSpectrum 𝒜))
    (hU : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⨆ i, U i) :
    ∃ (n : ℕ) (g : Fin n → A) (e : Fin n → ℕ),
      (∀ i, 0 < e i ∧ g i ∈ 𝒜 (e i)) ∧
      ProjectiveSpectrum.basicOpen 𝒜 f = ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (g i) ∧
      ∀ i, ∃ j, ProjectiveSpectrum.basicOpen 𝒜 (g i) ≤ U j := by
  classical
  let Q := {q : ι × A × ℕ //
    ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 q.2.2 q.2.1) ≤ U q.1}
  have hGcover : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ q : Q, ProjectiveSpectrum.basicOpen 𝒜
        (f * GradedRing.proj 𝒜 q.1.2.2 q.1.2.1) := by
    intro x hx
    obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge hx)
    obtain ⟨_, ⟨a, rfl⟩, hxa, haU⟩ :=
      (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open
        hxj (U j).isOpen
    change x ∈ ProjectiveSpectrum.basicOpen 𝒜 a at hxa
    rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a] at hxa
    obtain ⟨k, hxk⟩ := TopologicalSpace.Opens.mem_iSup.mp hxa
    change ProjectiveSpectrum.basicOpen 𝒜 a ≤ U j at haU
    have hka0 : ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 k a) ≤
        ProjectiveSpectrum.basicOpen 𝒜 a :=
      (le_iSup (fun n : ℕ => ProjectiveSpectrum.basicOpen 𝒜
        (GradedRing.proj 𝒜 n a)) k).trans_eq
        (ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a).symm
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨(j, a, k), hka0.trans haU⟩, ?_⟩
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact ⟨hx, hxk⟩
  have hgQ : ∀ q : Q, f * GradedRing.proj 𝒜 q.1.2.2 q.1.2.1 ∈
      𝒜 (d + q.1.2.2) := fun q =>
    SetLike.mul_mem_graded hf
      ((GradedRing.proj_apply 𝒜 q.1.2.2 q.1.2.1).symm ▸
        (DirectSum.decompose 𝒜 q.1.2.1 q.1.2.2).property)
  obtain ⟨t, ht⟩ := finite_homogeneous_subcover 𝒜 hf hd
    (fun q : Q => f * GradedRing.proj 𝒜 q.1.2.2 q.1.2.1)
    (fun q => d + q.1.2.2) hgQ hGcover
  let eFin : Fin t.card ≃ t := (Finset.equivFin t).symm
  let g : Fin t.card → A := fun i =>
    f * GradedRing.proj 𝒜 (eFin i).1.1.2.2 (eFin i).1.1.2.1
  let e : Fin t.card → ℕ := fun i => d + (eFin i).1.1.2.2
  refine ⟨t.card, g, e, ?_, ?_, ?_⟩
  · exact fun i => ⟨Nat.add_pos_left hd _, hgQ (eFin i).1⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨q, hqt, hxq⟩ := ht x hx
      let i : Fin t.card := (Finset.equivFin t) ⟨q, hqt⟩
      have hi : eFin i = ⟨q, hqt⟩ := (Finset.equivFin t).symm_apply_apply ⟨q, hqt⟩
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa only [g, hi] using hxq⟩
    · exact iSup_le fun i => (ProjectiveSpectrum.basicOpen_mul 𝒜 f _).le.trans inf_le_left
  · exact fun i => ⟨(eFin i).1.1.1,
      (ProjectiveSpectrum.basicOpen_mul 𝒜 f _).le.trans (inf_le_right.trans (eFin i).1.2)⟩

end AddSubmonoidClass

section AddSubgroupClass

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {f g : A} {d e : ℕ}

/-- If the projective basic open of a positive-degree homogeneous element `g` is contained in
that of `f`, then `f` is invertible in the localization of the graded ring away from `g`. -/
public theorem isUnit_algebraMap_away_of_basicOpen_le
    (hf : f ∈ 𝒜 d) (_hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (h : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    IsUnit (algebraMap A (Localization.Away g) f) := by
  obtain ⟨n, -, a, -, hga⟩ := exists_pow_eq_mul_of_basicOpen_le 𝒜 hf _hd hg he h
  rw [IsLocalization.Away.algebraMap_isUnit_iff g]
  exact ⟨n, a, hga.trans (mul_comm a f)⟩

/-- The chart `Spec A₍f₎ ⟶ Proj 𝒜` maps every point into the standard open `D₊(f)`. -/
private theorem base_awayι_mem_basicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) (x) :
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).toLRSHom.base x ∈
      AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  rw [← AlgebraicGeometry.Proj.opensRange_awayι 𝒜 f hf hd]
  exact ⟨x, rfl⟩

/-- If the projective basic open of a positive-degree homogeneous element `g` is contained in
that of `f`, then the degree-zero fraction `f ^ deg(g) / g ^ deg(f)` is invertible in the
homogeneous localization `A_(g)`. -/
public theorem isUnit_isLocalizationElem_of_basicOpen_le
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (h : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    IsUnit (HomogeneousLocalization.Away.isLocalizationElem hg hf) := by
  rw [← PrimeSpectrum.basicOpen_eq_top_iff_isUnit,
    ← AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hg he hf hd]
  apply top_unique
  intro x _
  exact (show AlgebraicGeometry.Proj.basicOpen 𝒜 g ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f from h)
    (base_awayι_mem_basicOpen 𝒜 hg he x)

end AddSubgroupClass

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Let `f` and `g i` be homogeneous elements of positive degree. Then `D₊(f)` is
contained in the union of the `D₊(g i)` if and only if the fractions
`g i ^ deg(f) / f ^ deg(g i)` generate the unit ideal in `A_(f)`. -/
public theorem basicOpen_le_iSup_iff_span_isLocalizationElem_eq_top
    {ι : Type*} {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (g : ι → A) (e : ι → ℕ) (hg : ∀ i, g i ∈ 𝒜 (e i)) (he : ∀ i, 0 < e i) :
      AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤
        ⨆ i, AlgebraicGeometry.Proj.basicOpen 𝒜 (g i) ↔
      Ideal.span (Set.range fun i => Away.isLocalizationElem hf (hg i)) = ⊤ := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (h (ProjectiveSpectrum.base_awayι_mem_basicOpen 𝒜 hf hd x))
    apply TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rwa [← AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hf hd (hg i) (he i)]
  · intro x hx
    rw [← AlgebraicGeometry.Proj.opensRange_awayι 𝒜 f hf hd] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr h).ge (Set.mem_univ y))
    apply TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rwa [← AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hf hd (hg i) (he i)] at hi

/-- For `f` homogeneous of degree `d` and `h` homogeneous of degree `n • d`, the degree-zero
fraction `h ^ d / f ^ (n • d)` is the `d`-th power of the degree-zero fraction `h / f ^ n`. -/
private theorem isLocalizationElem_eq_mk_pow {f h : A} {d n : ℕ} (hf : f ∈ 𝒜 d)
    (hh : h ∈ 𝒜 (n • d)) :
    Away.isLocalizationElem hf hh = Away.mk 𝒜 hf n h hh ^ d := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow, Away.val_mk, Away.val_mk, Localization.mk_pow,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [← pow_mul, smul_eq_mul, mul_comm]⟩

/-- Multiplying the numerator and the denominator of a degree-zero fraction by `f` does not
change it. -/
private theorem mk_succ_mul_eq_mk {f a : A} {d n : ℕ} (hf : f ∈ 𝒜 d) (ha : a ∈ 𝒜 (n • d))
    (haf : a * f ∈ 𝒜 ((n + 1) • d)) :
    Away.mk 𝒜 hf (n + 1) (a * f) haf = Away.mk 𝒜 hf n a ha := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [pow_succ]; ring⟩

/-- **Stacks Project, Tag 01MA.** Let `f` be a homogeneous element of positive degree `m` in a
graded ring `A`, and let `g` be an element of the degree-zero localization `A₍f₎`, so that `D(g)`
is a standard open of `Spec A₍f₎`. Then there is a homogeneous element `h` of positive degree
`n • m` such that `g = h / f ^ n`, such that `D₊(h) ⊆ D₊(f)`, and such that `D(g)` and `D₊(h)`
correspond under the open immersion `Spec A₍f₎ ⟶ Proj A` identifying `Spec A₍f₎` with `D₊(f)`:
`D(g)` is the preimage of `D₊(h)`, and `D₊(h)` is the image of `D(g)`. -/
@[stacks 01MA]
public theorem exists_homogeneous_awayι_preimage_basicOpen_eq {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (hm : 0 < m) (g : Away 𝒜 f) :
    ∃ (n : ℕ) (h : A) (hh : h ∈ 𝒜 (n • m)), 0 < n • m ∧
      Away.mk 𝒜 hf n h hh = g ∧
      AlgebraicGeometry.Proj.basicOpen 𝒜 h ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f ∧
      AlgebraicGeometry.Proj.awayι 𝒜 f hf hm ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 h =
        PrimeSpectrum.basicOpen g ∧
      AlgebraicGeometry.Proj.awayι 𝒜 f hf hm ''ᵁ PrimeSpectrum.basicOpen g =
        AlgebraicGeometry.Proj.basicOpen 𝒜 h := by
  obtain ⟨n, a, ha, hga⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf g
  have hdeg : a * f ∈ 𝒜 ((n + 1) • m) := by
    rw [succ_nsmul]
    exact SetLike.mul_mem_graded ha hf
  have hpos : 0 < (n + 1) • m := by
    simpa only [smul_eq_mul] using Nat.mul_pos n.succ_pos hm
  have hmk : Away.mk 𝒜 hf (n + 1) (a * f) hdeg = g :=
    (mk_succ_mul_eq_mk 𝒜 hf ha hdeg).trans hga
  have hle : AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
    AlgebraicGeometry.Proj.basicOpen_mono 𝒜 f (a * f) ⟨a, mul_comm a f⟩
  have hpre : AlgebraicGeometry.Proj.awayι 𝒜 f hf hm ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒜 (a * f) = PrimeSpectrum.basicOpen g := by
    rw [AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hf hm hdeg hpos,
      isLocalizationElem_eq_mk_pow 𝒜 hf hdeg, hmk, PrimeSpectrum.basicOpen_pow _ m hm]
  refine ⟨n + 1, a * f, hdeg, hpos, hmk, hle, hpre, ?_⟩
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Proj.opensRange_awayι 𝒜 f hf hm]
  exact inf_eq_right.mpr hle

end AlgebraicGeometry.Proj
