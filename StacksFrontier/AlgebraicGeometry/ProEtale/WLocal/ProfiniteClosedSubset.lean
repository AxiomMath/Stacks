module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Quotient
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrumLocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitBijection
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Profinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The w-local ind-Zariski extension along a profinite closed subset

Let `A` be a commutative ring and `I` an ideal whose closed subset `V(I) ⊆ Spec A` is a
profinite topological space. The ring `A` then admits an ind-Zariski extension `A → B` whose
spectrum is w-local, whose closed points are exactly `V(I·B)`, and which does not change the
quotient by `I`.

The extension is constructed, not merely asserted to exist: it is the canonical localization of
the stratification colimit `A_w` of `A` along the closed subset `V(I·A_w)`.

## Main definitions

* `AlgebraicGeometry.ProEtale.wLocalExtension`: the ring `B` of the construction, the canonical
  localization of `A_w` along `V(I·A_w)`.

## Main results

* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_quotient_iff`: the closed subset
  `V(I)` and the spectrum of `A ⧸ I` are profinite together, being homeomorphic.
* `AlgebraicGeometry.ProEtale.wLocalSpace_localizationRing` and
  `AlgebraicGeometry.ProEtale.closedPoints_localizationRing`: for a w-local `Spec R` and an
  ideal `J` with `Spec (R ⧸ J)` profinite, the canonical localization of `R` along `V(J)` has
  w-local spectrum, with closed points the zero locus of the extended ideal.
* `AlgebraicGeometry.ProEtale.bijective_of_identifiesLocalRings_of_comap_bijective`: an algebra
  identifying local rings whose map of spectra is bijective is an isomorphism, provided the
  source spectrum is Hausdorff.
* `AlgebraicGeometry.ProEtale.isIndZariski_wLocalExtension`,
  `AlgebraicGeometry.ProEtale.wLocalSpace_wLocalExtension`,
  `AlgebraicGeometry.ProEtale.closedPoints_wLocalExtension` and
  `AlgebraicGeometry.ProEtale.bijective_algebraMap_quotient_wLocalExtension`: the four properties
  of the construction.
* `AlgebraicGeometry.ProEtale.exists_isIndZariski_wLocal_of_isProfiniteStacks_zeroLocus`:
  **Stacks 0979**, the existence statement of the source.

## Implementation notes

The closed subset `V(I)` is the subtype of `Spec A` on the zero locus of `I`; it is
homeomorphic to `Spec (A ⧸ I)`, and the proofs work with the latter, where profiniteness is the
property form of `spec_profinite_tfae`.

The source says only that "it is clear that `B` is w-local with closed points `V(IB)`". The
content is that the points of `V(J)` in a w-local `Spec R` are closed as soon as `Spec (R ⧸ J)`
is profinite — profiniteness forbids specializations inside `V(J)`, so the unique closed
specialization of a point of `V(J)` is the point itself — together with the description of the
points of the localization lying over them.

The bijection `V(I·B) → V(I)` is assembled out of `zeroLocusContraction`, the contraction of
one closed subset into another along a ring map, which composes along a composite of ring maps.
Over `A_w` it is the restriction of the bijection on closed points of Stacks 0975, available
because profiniteness makes every point of `V(I·A_w)` closed; over the localization it is
bijective because the spectrum of a localization is embedded in the spectrum of its source.

The source obtains the final isomorphism `A/I ≅ B/IB` from Lemma 096L, which is how it is done
here: the quotient map identifies local rings, being ind-Zariski, and induces a homeomorphism of
spectra, so `096L` produces a two-sided inverse. That step is carried out in the generality in
which it is used, for an arbitrary algebra, in
`bijective_of_identifiesLocalRings_of_comap_bijective`.

The quotient isomorphism is recorded as bijectivity of the canonical map `A ⧸ I → B ⧸ I·B`,
which is stronger than the bare existence of an isomorphism since it identifies the map.

## References

* [Stacks Project, Tag 0979](https://stacks.math.columbia.edu/tag/0979)
* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
* [Stacks Project, Tag 096L](https://stacks.math.columbia.edu/tag/096L)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory TopologicalSpace

universe u

/-! ### The closed subset cut out by an ideal -/

section ZeroLocus

variable {R : Type u} [CommRing R]

/-- The spectrum of `R ⧸ I` is homeomorphic to the closed subset `V(I) ⊆ Spec R`. -/
def zeroLocusHomeomorph (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set R) :=
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).toHomeomorph.trans (Homeomorph.setCongr hrange)

/-- The closed subset `V(I) ⊆ Spec R` is profinite exactly when `Spec (R ⧸ I)` is. -/
theorem isProfiniteStacks_primeSpectrum_quotient_iff (I : Ideal R) :
    IsProfiniteStacks (PrimeSpectrum (R ⧸ I)) ↔
      IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set R)) := by
  rw [isProfiniteStacks_iff_compact_t2_totallyDisconnected,
    isProfiniteStacks_iff_compact_t2_totallyDisconnected]
  have e := zeroLocusHomeomorph I
  refine ⟨fun ⟨_, _, _⟩ => ⟨e.compactSpace, e.t2Space, e.totallyDisconnectedSpace⟩,
    fun ⟨_, _, _⟩ => ⟨e.symm.compactSpace, e.symm.t2Space, e.symm.totallyDisconnectedSpace⟩⟩

/-- A point of `Spec S` lies in `V(I·S)` exactly when its contraction to `Spec R` lies in `V(I)`. -/
private theorem mem_zeroLocus_map_iff {S : Type*} [CommRing S] (f : R →+* S) (I : Ideal R)
    (b : PrimeSpectrum S) :
    b ∈ PrimeSpectrum.zeroLocus (I.map f : Set S) ↔
      PrimeSpectrum.comap f b ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap]
  rfl

/-- Inside a closed subset whose quotient spectrum is profinite there are no specializations
between distinct points. -/
private theorem eq_of_specializes_of_mem_zeroLocus (J : Ideal R)
    (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J)))
    {p q : PrimeSpectrum R} (hp : p ∈ PrimeSpectrum.zeroLocus (J : Set R))
    (hq : q ∈ PrimeSpectrum.zeroLocus (J : Set R)) (h : p ⤳ q) : p = q := by
  have hT2 : T2Space (PrimeSpectrum (R ⧸ J)) :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mp hprof).2.1
  have e := J.primeSpectrumQuotientOrderIsoZeroLocus
  have hpq : e.symm ⟨p, hp⟩ ≤ e.symm ⟨q, hq⟩ :=
    e.symm.monotone ((PrimeSpectrum.le_iff_specializes p q).mpr h)
  have heq : e.symm ⟨p, hp⟩ = e.symm ⟨q, hq⟩ :=
    specializes_iff_eq.mp ((PrimeSpectrum.le_iff_specializes _ _).mp hpq)
  exact congrArg Subtype.val (e.symm.injective heq)

/-- In a w-local spectrum, a point of a closed subset whose quotient spectrum is profinite is a
closed point. -/
private theorem isClosed_singleton_of_mem_zeroLocus [WLocalSpace (PrimeSpectrum R)]
    (J : Ideal R) (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J)))
    {p : PrimeSpectrum R} (hp : p ∈ PrimeSpectrum.zeroLocus (J : Set R)) :
    IsClosed ({p} : Set (PrimeSpectrum R)) := by
  obtain ⟨c, ⟨hc, hpc⟩, _⟩ := WLocalSpace.existsUnique_closedPoint_specializes p
  have hEq := eq_of_specializes_of_mem_zeroLocus J hprof hp
    (hpc.mem_closed (PrimeSpectrum.isClosed_zeroLocus _) hp) hpc
  simpa [hEq] using mem_closedPoints_iff.mp hc

end ZeroLocus

/-! ### The canonical localization along a profinite closed subset -/

section LocalizationAlong

variable {R : Type u} [CommRing R]

/-- Every point of `V(J)` is in the image of the spectrum of the canonical localization of `R`
along `V(J)`. -/
private theorem exists_comap_eq_of_mem_zeroLocus (J : Ideal R)
    {q : PrimeSpectrum R} (hq : q ∈ PrimeSpectrum.zeroLocus (J : Set R)) :
    q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R)))) := by
  rw [localization_comap_range J (1 : R)]
  exact ⟨q, ⟨(PrimeSpectrum.mem_zeroLocus q (J : Set R)).mp hq, Ideal.one_notMem q.asIdeal⟩,
    specializes_rfl⟩

/-- The spectrum of the canonical localization of `R` along `V(J)` is embedded in `Spec R`. -/
private theorem localizationRing_comap_isEmbedding (J : Ideal R) :
    Topology.IsEmbedding
      (PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R)))) :=
  PrimeSpectrum.localization_comap_isEmbedding _ (localizationSubmonoid J 1)

/-- A point of the canonical localization of `R` along `V(J)` lying over a point of `V(J)` is a
closed point, when `Spec (R ⧸ J)` is profinite. -/
private theorem isClosed_singleton_of_comap_eq (J : Ideal R)
    (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J)))
    {q : PrimeSpectrum R} (hq : q ∈ PrimeSpectrum.zeroLocus (J : Set R))
    {b : PrimeSpectrum (localizationRing J (1 : R))}
    (hb : PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R))) b = q) :
    IsClosed ({b} : Set (PrimeSpectrum (localizationRing J (1 : R)))) := by
  have hf := localizationRing_comap_isEmbedding J
  apply closure_eq_iff_isClosed.mp
  ext x
  constructor
  · intro hx
    have hqx : q ⤳ PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R))) x := by
      simpa [hb] using hf.isInducing.specializes_iff.mpr (specializes_iff_mem_closure.mpr hx)
    have hxV := hqx.mem_closed (PrimeSpectrum.isClosed_zeroLocus _) hq
    have hxb : x = b :=
      hf.injective ((eq_of_specializes_of_mem_zeroLocus J hprof hq hxV hqx).symm.trans hb.symm)
    simp [hxb]
  · rintro rfl
    exact subset_closure (by simp)

/-- The closed points of the canonical localization of `R` along `V(J)` are exactly the points of
the zero locus of the extended ideal, when `Spec R` is w-local and `Spec (R ⧸ J)` is profinite. -/
theorem localizationRing_isClosed_singleton_iff [WLocalSpace (PrimeSpectrum R)]
    (J : Ideal R) (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J)))
    (b : PrimeSpectrum (localizationRing J (1 : R))) :
    IsClosed ({b} : Set (PrimeSpectrum (localizationRing J (1 : R)))) ↔
      J.map (algebraMap R (localizationRing J (1 : R))) ≤ b.asIdeal := by
  have hf := localizationRing_comap_isEmbedding J
  have hmem : PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R))) b ∈
      {p : PrimeSpectrum R | ∃ q ∈ locallyClosedPoints J (1 : R), p ⤳ q} := by
    rw [← localization_comap_range J (1 : R)]
    exact ⟨b, rfl⟩
  obtain ⟨q, hq, hspec⟩ := hmem
  have hqV : q ∈ PrimeSpectrum.zeroLocus (J : Set R) := hq.1
  obtain ⟨c, hc⟩ := exists_comap_eq_of_mem_zeroLocus J hqV
  constructor
  · intro hb
    have hspecB : b ⤳ c := by
      apply hf.isInducing.specializes_iff.mp
      simpa [hc] using hspec
    have hcb : c = b := by simpa [hb.closure_eq] using specializes_iff_mem_closure.mp hspecB
    refine (mem_zeroLocus_map_iff _ J b).mpr ?_
    rwa [← hcb, hc]
  · intro hb
    have hV := (mem_zeroLocus_map_iff _ J b).mp hb
    have hEq := eq_of_specializes_of_mem_zeroLocus J hprof hV hqV hspec
    obtain rfl : b = c := hf.injective (hEq.trans hc.symm)
    exact isClosed_singleton_of_comap_eq J hprof hqV hc

/-- The closed points of the canonical localization of `R` along `V(J)` form the zero locus of
the extended ideal. -/
theorem closedPoints_localizationRing [WLocalSpace (PrimeSpectrum R)]
    (J : Ideal R) (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J))) :
    closedPoints (PrimeSpectrum (localizationRing J (1 : R))) =
      PrimeSpectrum.zeroLocus
        (J.map (algebraMap R (localizationRing J (1 : R))) :
          Set (localizationRing J (1 : R))) := by
  ext b
  rw [mem_closedPoints_iff]
  exact localizationRing_isClosed_singleton_iff J hprof b

/-- **The canonical localization of a w-local ring along a profinite closed subset is w-local.**
If `Spec R` is w-local and `Spec (R ⧸ J)` is profinite, the canonical localization of `R` along
`V(J)` has w-local spectrum. -/
theorem wLocalSpace_localizationRing [WLocalSpace (PrimeSpectrum R)]
    (J : Ideal R) (hprof : IsProfiniteStacks (PrimeSpectrum (R ⧸ J))) :
    WLocalSpace (PrimeSpectrum (localizationRing J (1 : R))) := by
  have hf := localizationRing_comap_isEmbedding J
  have hmem {d : PrimeSpectrum (localizationRing J (1 : R))}
      (hd : IsClosed ({d} : Set (PrimeSpectrum (localizationRing J (1 : R))))) :
      PrimeSpectrum.comap (algebraMap R (localizationRing J (1 : R))) d ∈
        PrimeSpectrum.zeroLocus (J : Set R) := by
    exact (mem_zeroLocus_map_iff _ J d).mp
      ((localizationRing_isClosed_singleton_iff J hprof d).mp hd)
  refine
    { toSpectralSpace := inferInstance
      eq_of_specializes := ?_
      isClosed_closedPoints := ?_ }
  · intro x c c' hc hc' hxc hxc'
    exact hf.injective (WLocalSpace.eq_of_specializes
      (isClosed_singleton_of_mem_zeroLocus J hprof (hmem hc))
      (isClosed_singleton_of_mem_zeroLocus J hprof (hmem hc'))
      (hf.isInducing.specializes_iff.mpr hxc) (hf.isInducing.specializes_iff.mpr hxc'))
  · rw [closedPoints_localizationRing J hprof]
    exact PrimeSpectrum.isClosed_zeroLocus _

end LocalizationAlong

/-! ### Contracting one closed subset into another -/

section Contraction

/-- The contraction of the closed subset `V(J) ⊆ Spec S` into the closed subset
`V(I) ⊆ Spec A` along a ring map `f : A → S` carrying `I` into `J`. -/
private def zeroLocusContraction {A S : Type u} [CommRing A] [CommRing S]
    (f : A →+* S) (I : Ideal A) (J : Ideal S) (hJ : I ≤ J.comap f) :
    PrimeSpectrum.zeroLocus (J : Set S) → PrimeSpectrum.zeroLocus (I : Set A) := fun q =>
  ⟨PrimeSpectrum.comap f q.1, by
    change I ≤ (PrimeSpectrum.comap f q.1).asIdeal
    rw [PrimeSpectrum.comap_asIdeal]
    exact hJ.trans (Ideal.comap_mono ((PrimeSpectrum.mem_zeroLocus q.1 (J : Set S)).mp q.2))⟩

/-- Contraction of closed subsets composes along a composite of ring maps. -/
private theorem zeroLocusContraction_bijective_of_comp
    {A S S' : Type u} [CommRing A] [CommRing S] [CommRing S']
    (f : A →+* S) (g : S →+* S') (I : Ideal A) (J : Ideal S) (K : Ideal S')
    (hJ : I ≤ J.comap f) (hK : J ≤ K.comap g) (hIK : I ≤ K.comap (g.comp f))
    (hfb : Function.Bijective (zeroLocusContraction f I J hJ))
    (hgb : Function.Bijective (zeroLocusContraction g J K hK)) :
    Function.Bijective (zeroLocusContraction (g.comp f) I K hIK) := by
  have hEq : zeroLocusContraction (g.comp f) I K hIK =
      zeroLocusContraction f I J hJ ∘ zeroLocusContraction g J K hK := by
    funext q
    exact Subtype.ext (PrimeSpectrum.comap_comp_apply f g q.1)
  rw [hEq]
  exact hfb.comp hgb

/-- A bijection `V(I·S) → V(I)` becomes a bijection of the spectra of the quotients. -/
private theorem comap_quotientMap_bijective_of_zeroLocusContraction_bijective
    {A S : Type u} [CommRing A] [CommRing S] (f : A →+* S) (I : Ideal A)
    (hbij : Function.Bijective (zeroLocusContraction f I (I.map f) Ideal.le_comap_map)) :
    Function.Bijective
      (PrimeSpectrum.comap (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) := by
  let eA := zeroLocusHomeomorph I
  let eS := zeroLocusHomeomorph (I.map f)
  have hFormula (x : PrimeSpectrum (S ⧸ I.map f)) :
      eA (PrimeSpectrum.comap (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) x) =
        zeroLocusContraction f I (I.map f) Ideal.le_comap_map (eS x) := by
    refine Subtype.ext ?_
    show PrimeSpectrum.comap (Ideal.Quotient.mk I)
        (PrimeSpectrum.comap (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) x) =
      PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map f)) x)
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      Ideal.quotientMap_comp_mk Ideal.le_comap_map]
  constructor
  · intro x y hxy
    refine eS.injective (hbij.1 ?_)
    rw [← hFormula x, ← hFormula y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hbij.2 (eA y)
    refine ⟨eS.symm x, eA.injective ?_⟩
    rw [hFormula]
    simpa using hx

/-- The closed points of `Spec A_w` contract bijectively onto `Spec A`. -/
private theorem comap_closedPoints_stratificationColimit_bijective (A : Type u) [CommRing A] :
    Function.Bijective
      (fun q : closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) =>
        PrimeSpectrum.comap (algebraMap A (stratificationColimitRing (A := A))) q.1) := by
  have L := stratificationLimit (A := A)
  let H : L.closedScheme → PrimeSpectrum A :=
    (L.inclusion ≫
      Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A)))).base
  have hH : Function.Bijective H := stratificationLimit_closedScheme_bijective L
  have hRange : Set.range L.inclusion.base =
      closedPoints (stratificationLimitScheme (A := A)) :=
    range_inclusion_eq_closedPoints L
  have hcomp (z : L.closedScheme) :
      H z = PrimeSpectrum.comap (algebraMap A (stratificationColimitRing (A := A)))
        (L.inclusion.base z) := rfl
  constructor
  · intro q q' h
    obtain ⟨z, hz⟩ : q.1 ∈ Set.range L.inclusion.base := by
      rw [hRange]
      exact q.2
    obtain ⟨z', hz'⟩ : q'.1 ∈ Set.range L.inclusion.base := by
      rw [hRange]
      exact q'.2
    obtain rfl : z = z' := hH.1 (by
      rw [hcomp, hcomp, hz, hz']
      exact h)
    exact Subtype.ext (hz.symm.trans hz')
  · intro p
    obtain ⟨z, hz⟩ := hH.2 p
    exact ⟨⟨L.inclusion.base z, hRange ▸ Set.mem_range_self z⟩, (hcomp z).symm.trans hz⟩

/-- `Spec A_w` is w-local. -/
private theorem wLocalSpace_stratificationColimit {A : Type u} [CommRing A] :
    WLocalSpace (PrimeSpectrum (stratificationColimitRing (A := A))) := by
  show WLocalSpace (stratificationLimitScheme (A := A))
  infer_instance

/-- `V(I·A_w)` contracts bijectively onto `V(I)`, when the latter is profinite: profiniteness
makes every point of `V(I·A_w)` a closed point of the w-local space `Spec A_w`, and the closed
points of `Spec A_w` contract bijectively onto `Spec A`. -/
private theorem zeroLocusContraction_stratificationColimit_bijective
    (A : Type u) [CommRing A] (I : Ideal A)
    (hprof : IsProfiniteStacks (PrimeSpectrum (stratificationColimitRing (A := A) ⧸
      I.map (algebraMap A (stratificationColimitRing (A := A)))))) :
    Function.Bijective (zeroLocusContraction
      (algebraMap A (stratificationColimitRing (A := A))) I
      (I.map (algebraMap A (stratificationColimitRing (A := A)))) Ideal.le_comap_map) := by
  have := wLocalSpace_stratificationColimit (A := A)
  have hclosed := comap_closedPoints_stratificationColimit_bijective A
  constructor
  · intro q q' h
    have hqc : q.1 ∈ closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) :=
      mem_closedPoints_iff.mpr (isClosed_singleton_of_mem_zeroLocus _ hprof q.2)
    have hq'c : q'.1 ∈ closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) :=
      mem_closedPoints_iff.mpr (isClosed_singleton_of_mem_zeroLocus _ hprof q'.2)
    have hcc : (⟨q.1, hqc⟩ : closedPoints (PrimeSpectrum (stratificationColimitRing (A := A)))) =
        ⟨q'.1, hq'c⟩ := hclosed.1 (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun x : closedPoints
      (PrimeSpectrum (stratificationColimitRing (A := A))) => x.1) hcc)
  · intro p
    obtain ⟨c, hc⟩ := hclosed.2 p.1
    have hc' : PrimeSpectrum.comap
        (algebraMap A (stratificationColimitRing (A := A))) c.1 = p.1 := hc
    exact ⟨⟨c.1, (mem_zeroLocus_map_iff _ I c.1).mpr (hc' ▸ p.2)⟩, Subtype.ext hc'⟩

/-- `V(J·R^~)` contracts bijectively onto `V(J)` for the canonical localization `R^~` of `R`
along `V(J)`: injectivity because the spectrum of a localization is embedded in `Spec R`, and
surjectivity because every point of `V(J)` is in the image. -/
private theorem zeroLocusContraction_localizationRing_bijective
    {R : Type u} [CommRing R] (J : Ideal R) (K : Ideal (localizationRing J (1 : R)))
    (hK : J.map (algebraMap R (localizationRing J (1 : R))) = K)
    (hJK : J ≤ K.comap (algebraMap R (localizationRing J (1 : R)))) :
    Function.Bijective (zeroLocusContraction
      (algebraMap R (localizationRing J (1 : R))) J K hJK) := by
  subst hK
  have hf := localizationRing_comap_isEmbedding J
  constructor
  · exact fun b b' h => Subtype.ext (hf.injective (congrArg Subtype.val h))
  · intro q
    obtain ⟨b, hb⟩ := exists_comap_eq_of_mem_zeroLocus J q.2
    exact ⟨⟨b, (mem_zeroLocus_map_iff _ J b).mpr (hb ▸ q.2)⟩, Subtype.ext hb⟩

end Contraction

/-! ### From a homeomorphism of spectra to an isomorphism of rings -/

/-- **An algebra identifying local rings whose map of spectra is bijective is an isomorphism.**
This is Stacks 096L applied twice: the inverse homeomorphism is induced by a unique algebra map,
which is a two-sided inverse again by uniqueness. The target spectrum is automatically
quasi-compact, so Hausdorffness of the source spectrum makes the continuous bijection a
homeomorphism. -/
theorem bijective_of_identifiesLocalRings_of_comap_bijective
    {Q T : Type u} [CommRing Q] [CommRing T] [Algebra Q T] [T2Space (PrimeSpectrum Q)]
    (hlocal : Algebra.IdentifiesLocalRings Q T)
    (hSpec : Function.Bijective (PrimeSpectrum.comap (algebraMap Q T))) :
    Function.Bijective (algebraMap Q T) := by
  let e : PrimeSpectrum T ≃ₜ PrimeSpectrum Q :=
    IsHomeomorph.homeomorph _ (isHomeomorph_iff_continuous_bijective.mpr
      ⟨PrimeSpectrum.continuous_comap _, hSpec⟩)
  let gQ : Spec.topObj (CommRingCat.of Q) ⟶ Spec.topObj (CommRingCat.of T) :=
    TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hgQ : gQ ≫ Spec.topMap (CommRingCat.ofHom (algebraMap Q T)) =
      Spec.topMap (CommRingCat.ofHom (algebraMap Q Q)) := by
    ext x
    rw [ConcreteCategory.comp_apply]
    exact e.apply_symm_apply x
  obtain ⟨ψ, hψ, -⟩ := existsUnique_algHom_of_specTopMap_over Q T Q hlocal gQ hgQ
  have hψφ : ψ.toRingHom.comp (algebraMap Q T) = RingHom.id Q := by
    ext x
    simp
  have hψApply (x : PrimeSpectrum Q) : PrimeSpectrum.comap ψ.toRingHom x = e.symm x :=
    congrArg (fun m : Spec.topObj (CommRingCat.of Q) ⟶ Spec.topObj (CommRingCat.of T) => m x) hψ
  obtain ⟨_u, _hu, huniq⟩ := existsUnique_algHom_of_specTopMap_over Q T T hlocal
    (𝟙 (Spec.topObj (CommRingCat.of T))) (by simp)
  have hφψ : (algebraMap Q T).comp ψ.toRingHom = RingHom.id T := by
    refine congrArg AlgHom.toRingHom
      ((huniq ((Algebra.ofId Q T).comp ψ) ?_).trans
        (huniq (AlgHom.id Q T) (by simp)).symm)
    ext x
    show PrimeSpectrum.comap ψ.toRingHom (PrimeSpectrum.comap (algebraMap Q T) x) = x
    rw [hψApply]
    exact e.symm_apply_apply x
  exact ⟨Function.LeftInverse.injective (g := ψ.toRingHom) (RingHom.congr_fun hψφ),
    Function.RightInverse.surjective (g := ψ.toRingHom) (RingHom.congr_fun hφψ)⟩

/-! ### The construction -/

section Construction

variable {A : Type u} [CommRing A]

/-- The extension of an ideal `I ⊆ A` to the stratification colimit `A_w`. -/
abbrev colimitExtendedIdeal (I : Ideal A) : Ideal (stratificationColimitRing (A := A)) :=
  I.map (algebraMap A (stratificationColimitRing (A := A)))

/-- **The w-local ind-Zariski extension of `A` along `V(I)`**: the canonical localization of the
stratification colimit `A_w` of `A` along the closed subset `V(I·A_w)`. -/
abbrev wLocalExtension (I : Ideal A) : Type u :=
  localizationRing (colimitExtendedIdeal I) (1 : stratificationColimitRing (A := A))

/-- The structure map of the extension factors through `A_w`. -/
theorem algebraMap_wLocalExtension_eq (I : Ideal A) :
    algebraMap A (wLocalExtension I) =
      (algebraMap (stratificationColimitRing (A := A)) (wLocalExtension I)).comp
        (algebraMap A (stratificationColimitRing (A := A))) := by
  ext a
  exact IsScalarTower.algebraMap_apply A (stratificationColimitRing (A := A))
    (wLocalExtension I) a

/-- The extension of `I` to the w-local extension equals the extension of `I·A_w` along
`A_w → wLocalExtension I`. -/
theorem map_algebraMap_wLocalExtension (I : Ideal A) :
    I.map (algebraMap A (wLocalExtension I)) =
      (colimitExtendedIdeal I).map
        (algebraMap (stratificationColimitRing (A := A)) (wLocalExtension I)) := by
  rw [algebraMap_wLocalExtension_eq, ← Ideal.map_map]

/-- `A → A_w` is ind-Zariski. -/
private theorem isIndZariski_stratificationColimit :
    Algebra.IsIndZariski A (stratificationColimitRing (A := A)) :=
  stratificationColimit_isIndZariski (A := A)

/-- The spectrum of the quotient of an ind-Zariski extension by the extension of an ideal is
profinite as soon as the spectrum of the quotient of the base is. -/
private theorem isProfiniteStacks_quotient_of_isIndZariski (B : Type u) [CommRing B]
    [Algebra A B] (I : Ideal A) (hI : IsProfiniteStacks (PrimeSpectrum (A ⧸ I)))
    (hAB : Algebra.IsIndZariski A B) :
    IsProfiniteStacks (PrimeSpectrum (B ⧸ I.map (algebraMap A B))) :=
  isProfiniteStacks_primeSpectrum_of_identifiesLocalRings (A ⧸ I) (B ⧸ I.map (algebraMap A B))
    (identifiesLocalRings_of_isIndZariski (A ⧸ I) (B ⧸ I.map (algebraMap A B))
      (isIndZariski_quotient A B I hAB)) hI

variable (A) in
/-- **The extension of `A` along `V(I)` is ind-Zariski**: it is the composite of the ind-Zariski
map `A → A_w` with a localization. -/
theorem isIndZariski_wLocalExtension (I : Ideal A) :
    Algebra.IsIndZariski A (wLocalExtension I) :=
  Algebra.IsIndZariski.comp A (stratificationColimitRing (A := A)) (wLocalExtension I)
    isIndZariski_stratificationColimit (isIndZariski_localization _)

/-- `Spec (A_w ⧸ I·A_w)` is profinite when `V(I)` is. -/
private theorem isProfiniteStacks_quotient_colimitExtendedIdeal (I : Ideal A)
    (hI : IsProfiniteStacks (PrimeSpectrum (A ⧸ I))) :
    IsProfiniteStacks (PrimeSpectrum
      (stratificationColimitRing (A := A) ⧸ colimitExtendedIdeal I)) :=
  isProfiniteStacks_quotient_of_isIndZariski _ I hI isIndZariski_stratificationColimit

variable (A) in
/-- **The spectrum of the extension of `A` along a profinite `V(I)` is w-local.** -/
theorem wLocalSpace_wLocalExtension (I : Ideal A)
    (hI : IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set A))) :
    WLocalSpace (PrimeSpectrum (wLocalExtension I)) :=
  have := wLocalSpace_stratificationColimit (A := A)
  wLocalSpace_localizationRing _ (isProfiniteStacks_quotient_colimitExtendedIdeal I
    ((isProfiniteStacks_primeSpectrum_quotient_iff I).mpr hI))

variable (A) in
/-- **The closed points of the extension of `A` along a profinite `V(I)` are `V(I·B)`.** -/
theorem closedPoints_wLocalExtension (I : Ideal A)
    (hI : IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set A))) :
    closedPoints (PrimeSpectrum (wLocalExtension I)) =
      PrimeSpectrum.zeroLocus
        (I.map (algebraMap A (wLocalExtension I)) : Set (wLocalExtension I)) := by
  have := wLocalSpace_stratificationColimit (A := A)
  rw [map_algebraMap_wLocalExtension]
  exact closedPoints_localizationRing _ (isProfiniteStacks_quotient_colimitExtendedIdeal I
    ((isProfiniteStacks_primeSpectrum_quotient_iff I).mpr hI))

variable (A) in
/-- **The extension of `A` along a profinite `V(I)` does not change the quotient by `I`**: the
canonical map `A ⧸ I → B ⧸ I·B` is bijective. -/
theorem bijective_algebraMap_quotient_wLocalExtension (I : Ideal A)
    (hI : IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set A))) :
    Function.Bijective (algebraMap (A ⧸ I)
      (wLocalExtension I ⧸ I.map (algebraMap A (wLocalExtension I)))) := by
  have hIquot : IsProfiniteStacks (PrimeSpectrum (A ⧸ I)) :=
    (isProfiniteStacks_primeSpectrum_quotient_iff I).mpr hI
  have hT2 : T2Space (PrimeSpectrum (A ⧸ I)) :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected _).mp hIquot).2.1
  have hK : colimitExtendedIdeal I ≤
      (I.map (algebraMap A (wLocalExtension I))).comap
        (algebraMap (stratificationColimitRing (A := A)) (wLocalExtension I)) := by
    rw [map_algebraMap_wLocalExtension]
    exact Ideal.le_comap_map
  have hbij := zeroLocusContraction_bijective_of_comp
    (algebraMap A (stratificationColimitRing (A := A)))
    (algebraMap (stratificationColimitRing (A := A)) (wLocalExtension I)) I
    (colimitExtendedIdeal I) (I.map (algebraMap A (wLocalExtension I)))
    Ideal.le_comap_map hK Ideal.le_comap_map
    (zeroLocusContraction_stratificationColimit_bijective A I
      (isProfiniteStacks_quotient_colimitExtendedIdeal I hIquot))
    (zeroLocusContraction_localizationRing_bijective _ _
      (map_algebraMap_wLocalExtension I).symm hK)
  exact bijective_of_identifiesLocalRings_of_comap_bijective
    (identifiesLocalRings_of_isIndZariski _ _
      (isIndZariski_quotient A (wLocalExtension I) I (isIndZariski_wLocalExtension A I)))
    (comap_quotientMap_bijective_of_zeroLocusContraction_bijective
      (algebraMap A (wLocalExtension I)) I hbij)

variable (A) in
/-- **Stacks 0979.** Let `A` be a ring and `I` an ideal whose closed subset `V(I) ⊆ Spec A` is a
profinite topological space. Then there is an ind-Zariski ring map `A → B` such that `Spec B` is
w-local, the set of its closed points is `V(I·B)`, and `A ⧸ I → B ⧸ I·B` is an isomorphism. -/
@[stacks 0979]
theorem exists_isIndZariski_wLocal_of_isProfiniteStacks_zeroLocus (I : Ideal A)
    (hI : IsProfiniteStacks (PrimeSpectrum.zeroLocus (I : Set A))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.IsIndZariski A B ∧ WLocalSpace (PrimeSpectrum B) ∧
        closedPoints (PrimeSpectrum B) =
          PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B) ∧
        Function.Bijective (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) :=
  ⟨wLocalExtension I, inferInstance, inferInstance, isIndZariski_wLocalExtension A I,
    wLocalSpace_wLocalExtension A I hI, closedPoints_wLocalExtension A I hI,
    bijective_algebraMap_quotient_wLocalExtension A I hI⟩

end Construction

end AlgebraicGeometry.ProEtale

end
