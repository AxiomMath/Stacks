module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Filtration
public import StacksCore.Tactic.StacksAttribute

/-!
# Reducedness of a proper scheme over a discrete valuation ring

Let `f : X ⟶ Spec R` be proper over a discrete valuation ring and assume that every irreducible
component of `X` dominates the base. If the special fibre of `f` is reduced, then `X` itself is
reduced, and so is the generic fibre.

Reducedness of `X` is checked on stalks. A point over the generic point of `Spec R` specializes
to a point over the closed point, and reducedness of stalks propagates along specialization, so
only points of the special fibre have to be treated. At such a point `x`, choose an affine chart
`U` and a uniformizer `ϖ`; the local ring `O_{X,x}` is Noetherian, the image of `ϖ` lies in its
maximal ideal and in no minimal prime (this is where domination of the base is used), and the
quotient by `ϖ` is the local ring of the special fibre, hence reduced. Krull's intersection
theorem then upgrades reducedness of the quotient to reducedness of `O_{X,x}`.

For the generic fibre, the residue field of the generic point of `Spec R` is a localization of
`R` away from a uniformizer, so the generic fibre is an open subscheme of `X` and inherits
reducedness.

## Main results

* `AlgebraicGeometry.isReduced_of_isProper_over_dvr_of_isReduced_specialFiber`: the total space
  is reduced.
* `AlgebraicGeometry.isReduced_genericFiber_of_isProper_over_dvr_of_isReduced_specialFiber`: the
  generic fibre is reduced.

## Implementation notes

An irreducible component dominates the base precisely when its image is dense. In
`PrimeSpectrum R`, the generic point is the ideal `⊥` and the closed point is the maximal ideal;
on the scheme `Spec R` the latter is `IsLocalRing.closedPoint`, and the special fibre is the
fibre of `f` over it.

## References

* [Stacks Project, Tag 0C0D](https://stacks.math.columbia.edu/tag/0C0D)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

section

open CategoryTheory CategoryTheory.Limits

/-- A Noetherian local ring is reduced as soon as the quotient by a single element of the
maximal ideal that avoids every minimal prime is reduced. -/
private theorem isReduced_of_reduced_quotient_of_not_mem_minimalPrimes
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A)
    (hmin : ∀ P ∈ Ideal.minimalPrimes (⊥ : Ideal A), π ∉ P)
    (hquot : _root_.IsReduced (A ⧸ Ideal.span ({π} : Set A))) : _root_.IsReduced A := by
  let I : Ideal A := Ideal.span ({π} : Set A)
  have hI : I ≠ ⊤ := by
    intro h
    have hle : I ≤ IsLocalRing.maximalIdeal A :=
      Ideal.span_le.mpr fun z hz => by simpa using hz ▸ hπ
    have htop : (⊤ : Ideal A) ≤ IsLocalRing.maximalIdeal A := by
      simpa [h] using hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp htop)
  have hK : (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A A)) = ⊥ :=
    I.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) hI
  constructor
  intro a ha
  have factor : ∀ n : ℕ, ∃ b : A, a = π ^ n * b ∧ IsNilpotent b := by
    intro n
    induction n with
    | zero => exact ⟨a, by simp, ha⟩
    | succ n ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      have hmap : IsNilpotent (Ideal.Quotient.mk I b) := by
        obtain ⟨m, hm⟩ := hb
        exact ⟨m, by simpa using congrArg (Ideal.Quotient.mk I) hm⟩
      have : _root_.IsReduced (A ⧸ I) := hquot
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp (isNilpotent_iff_eq_zero.mp hmap))
      have hcnil : IsNilpotent c := by
        obtain ⟨m, hm⟩ := hb
        have hminc : c ∈ sInf (Ideal.minimalPrimes (⊥ : Ideal A)) := by
          rw [Ideal.mem_sInf]
          intro P hP
          have hPm : P.IsPrime := hP.isPrime
          have hbm : b ∈ P := hPm.mem_of_pow_mem m (hm ▸ P.zero_mem)
          rcases hPm.mem_or_mem (hc ▸ hbm) with hcP | hπP
          · exact hcP
          · exact (hmin P hP hπP).elim
        have hrad : c ∈ (⊥ : Ideal A).radical := by
          rwa [← Ideal.sInf_minimalPrimes]
        obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff.mp hrad)
        exact ⟨m, (Ideal.mem_bot.mp hm)⟩
      refine ⟨c, ?_, hcnil⟩
      rw [← hc, pow_succ]
      ring
  have hall : ∀ n : ℕ, a ∈ (I ^ n) • (⊤ : Submodule A A) := by
    intro n
    obtain ⟨b, hab, _⟩ := factor n
    rw [hab, Ideal.smul_top_eq_map]
    simpa using Ideal.mul_mem_right b (I ^ n)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) n)
  have hmem : a ∈ (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A A)) := (Submodule.mem_iInf _).mpr hall
  rw [hK] at hmem
  simpa using hmem

/-- Reducedness of localizations propagates along specialization of primes. -/
private theorem isReduced_localized_of_specializes
    {A : Type*} [CommRing A] {x y : PrimeSpectrum A} (h : x ⤳ y)
    [_root_.IsReduced (Localization.AtPrime y.asIdeal)] :
    _root_.IsReduced (Localization.AtPrime x.asIdeal) := by
  let S := Localization.AtPrime y.asIdeal
  let : Algebra A S := inferInstance
  let : IsLocalization.AtPrime S y.asIdeal := Localization.isLocalization
  have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr h
  let P : Ideal S := x.asIdeal.map (algebraMap A S)
  have : P.IsPrime := by
    dsimp [P]
    exact Ideal.isPrime_map_of_isLocalizationAtPrime
      (q := y.asIdeal) (p := x.asIdeal) (S := S) hle
  let T := Localization.AtPrime P
  let : Algebra S T := inferInstance
  let : IsLocalization.AtPrime T P := Localization.isLocalization
  let : Algebra A T := inferInstance
  let : IsScalarTower A S T := inferInstance
  have hunder : P.comap (algebraMap A S) = x.asIdeal := by
    dsimp [P]
    simpa [Ideal.under_def] using
      (Ideal.under_map_of_isLocalizationAtPrime
        (q := y.asIdeal) (p := x.asIdeal) (S := S) hle)
  have : IsLocalization.AtPrime T x.asIdeal := by
    simpa [hunder] using IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      y.asIdeal.primeCompl T P
  have : _root_.IsReduced T := isReduced_localizationPreserves P.primeCompl T inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime x.asIdeal :=
    IsLocalization.algEquiv x.asIdeal.primeCompl T (Localization.AtPrime x.asIdeal)
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- On an affine chart, reducedness of the local ring at a point can be read on the stalk. -/
private theorem isReduced_localization_iff_isReduced_stalk {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    _root_.IsReduced (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) ↔
      _root_.IsReduced (X.presheaf.stalk x) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let e : X.presheaf.stalk x ≃ₐ[Γ(X, U)] Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  constructor
  · intro h
    exact isReduced_of_injective e e.injective
  · intro h
    exact isReduced_of_injective e.symm e.symm.injective

/-- Reducedness of stalks propagates along specialization of points of a scheme. -/
private theorem isReduced_stalk_of_specializes
    {X : Scheme} {x y : X} (hxy : x ⤳ y)
    [_root_.IsReduced (X.presheaf.stalk y)] :
    _root_.IsReduced (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hxU : x ∈ U := hxy.mem_open U.2 hyU
  let px := hU.primeIdealOf ⟨x, hxU⟩
  let py := hU.primeIdealOf ⟨y, hyU⟩
  have hmapped : hU.fromSpec px ⤳ hU.fromSpec py := by
    simpa [px, py, hU.fromSpec_primeIdealOf] using hxy
  have hxy' : px ⤳ py :=
    (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hmapped
  have : _root_.IsReduced (Localization.AtPrime py.asIdeal) :=
    (isReduced_localization_iff_isReduced_stalk hU hyU).mpr ‹_›
  have : _root_.IsReduced (Localization.AtPrime px.asIdeal) :=
    isReduced_localized_of_specializes hxy'
  exact (isReduced_localization_iff_isReduced_stalk hU hxU).mp ‹_›

/-- A point of a proper scheme over a discrete valuation ring lying over the generic point of
the base specializes to a point lying over the closed point. -/
private theorem exists_specializes_closedPoint_of_generic
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (x : X)
    (hfx : f x = (⟨⊥, inferInstance⟩ : Spec (.of R))) :
    ∃ y : X, f y = IsLocalRing.closedPoint (CommRingCat.of R) ∧ x ⤳ y := by
  have hclosed : IsClosed (f '' closure ({x} : Set X)) := f.isClosedMap _ isClosed_closure
  have hgeneric : (⟨⊥, inferInstance⟩ : Spec (.of R)) ∈ f '' closure ({x} : Set X) := by
    rw [← hfx]
    exact ⟨x, subset_closure (by simp), rfl⟩
  have hspec : (⟨⊥, inferInstance⟩ : Spec (.of R)) ⤳
      IsLocalRing.closedPoint (CommRingCat.of R) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hyC, hyf⟩ := hspec.mem_closed hclosed hgeneric
  exact ⟨y, hyf, specializes_iff_mem_closure.mpr hyC⟩

/-- The spectrum of a discrete valuation ring has exactly two points: the generic point `⊥` and
the closed point. -/
private theorem base_point_bot_or_top
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (y : Spec (.of R)) :
    y = (⟨⊥, inferInstance⟩ : Spec (.of R)) ∨
      y = IsLocalRing.closedPoint (CommRingCat.of R) := by
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (y : PrimeSpectrum R) with h | h
  · exact Or.inl (congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) h)
  · right
    have htop : (⊤ : PrimeSpectrum R) = IsLocalRing.closedPoint (CommRingCat.of R) := rfl
    exact congrArg (fun z : PrimeSpectrum R => (z : Spec (.of R))) (h.trans htop)

/-- On an affine chart of a scheme all of whose irreducible components dominate the base, the
image of a uniformizer of the base lies in no minimal prime of the chart. -/
private theorem uniformizer_avoids_minimalPrime_chart
    {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (hcomponents : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z))
    (e : Spec (.of A) ⟶ X) [IsOpenImmersion e] (φ : R →+* A)
    (he : e ≫ f = Spec.map (CommRingCat.ofHom φ))
    (ϖ : R) (hϖ : Irreducible ϖ) {q : Ideal A}
    (hq : q ∈ Ideal.minimalPrimes (⊥ : Ideal A)) : φ ϖ ∉ q := by
  intro hϖq
  let ηp : PrimeSpectrum A := ⟨q, hq.isPrime⟩
  let η : Spec (.of A) := ηp
  have hqcompP : closure ({ηp} : Set (PrimeSpectrum A)) ∈
      irreducibleComponents (PrimeSpectrum A) := by
    apply (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes (s := {ηp})).mp
    simpa only [PrimeSpectrum.vanishingIdeal_singleton] using hq
  have hqcomp : closure ({η} : Set (Spec (.of A))) ∈
      irreducibleComponents (Spec (.of A)) := hqcompP
  have hbaseπ : ϖ ∈ (PrimeSpectrum.comap φ η).asIdeal := hϖq
  have hbaseTop : PrimeSpectrum.comap φ η = (⊤ : PrimeSpectrum R) := by
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (PrimeSpectrum.comap φ η) with
      hbot | htop
    · have hzero : ϖ ∈ (⊥ : Ideal R) := by simpa [hbot] using hbaseπ
      exact (hϖ.ne_zero (Ideal.mem_bot.mp hzero)).elim
    · exact htop
  have hηClosed : f (e η) = IsLocalRing.closedPoint (CommRingCat.of R) := by
    have heval : f (e η) = PrimeSpectrum.comap φ η := by
      show (e ≫ f) η = _
      rw [he]
      rfl
    rw [heval, hbaseTop]
    rfl
  let W : Set X := closure ({e η} : Set X)
  have hWirr : IsIrreducible W := isIrreducible_singleton.closure
  obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible W hWirr
  have hηZ : e η ∈ Z := hWZ (subset_closure (by simp))
  have hZpre : e ⁻¹' Z ∈ irreducibleComponents (Spec (.of A)) :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding ⟨e η, hηZ, ⟨η, rfl⟩⟩
  have hηpreClosed : IsClosed (e ⁻¹' Z) :=
    (isClosed_of_mem_irreducibleComponents Z hZ).preimage e.continuous
  have hηpre : η ∈ e ⁻¹' Z := hηZ
  have hclosurePre : closure ({η} : Set (Spec (.of A))) ⊆ e ⁻¹' Z :=
    closure_minimal (by simpa using hηpre) hηpreClosed
  have hpreEq : e ⁻¹' Z = closure ({η} : Set (Spec (.of A))) :=
    Set.Subset.antisymm (hqcomp.2 hZpre.1 hclosurePre) hclosurePre
  let F : Set X := f ⁻¹' {IsLocalRing.closedPoint (CommRingCat.of R)}
  have hFclosed : IsClosed F :=
    (IsLocalRing.isClosed_singleton_closedPoint (CommRingCat.of R)).preimage f.continuous
  have hpreFclosed : IsClosed (e ⁻¹' F) := hFclosed.preimage e.continuous
  have hηpreF : η ∈ e ⁻¹' F := hηClosed
  have hclosurePreF : closure ({η} : Set (Spec (.of A))) ⊆ e ⁻¹' F :=
    closure_minimal (by simpa using hηpreF) hpreFclosed
  let V : Set X := Z ∩ Set.range e
  have hVnon : V.Nonempty := ⟨e η, hηZ, ⟨η, rfl⟩⟩
  have hVsubF : V ⊆ F := by
    rintro z ⟨hzZ, ⟨z', rfl⟩⟩
    have hzpre : z' ∈ e ⁻¹' Z := hzZ
    rw [hpreEq] at hzpre
    exact hclosurePreF hzpre
  have hVclosure : closure V = Z := by
    refine Set.Subset.antisymm
      (closure_minimal (fun _ hz => hz.1) (isClosed_of_mem_irreducibleComponents Z hZ))
      fun z hzZ => ?_
    by_contra hzcl
    obtain ⟨w, hwZ, hwE, hwN⟩ := hZ.1.2 (Set.range e) (closure V)ᶜ
      e.isOpenEmbedding.isOpen_range (isClosed_closure.isOpen_compl) hVnon ⟨z, hzZ, hzcl⟩
    exact hwN (subset_closure ⟨hwZ, hwE⟩)
  have hZsubF : Z ⊆ F := hVclosure ▸ closure_minimal hVsubF hFclosed
  have himage : f '' Z ⊆ {IsLocalRing.closedPoint (CommRingCat.of R)} :=
    Set.image_subset_iff.mpr hZsubF
  have hclosureImage : closure (f '' Z) ⊆ {IsLocalRing.closedPoint (CommRingCat.of R)} :=
    closure_minimal himage (IsLocalRing.isClosed_singleton_closedPoint (CommRingCat.of R))
  have hdense := hcomponents Z hZ
  have hgenericClosed : (⟨⊥, inferInstance⟩ : Spec (.of R)) =
      IsLocalRing.closedPoint (CommRingCat.of R) := by
    have hg : (⟨⊥, inferInstance⟩ : Spec (.of R)) ∈ closure (f '' Z) := by
      rw [hdense.closure_eq]
      exact Set.mem_univ _
    exact Set.mem_singleton_iff.mp (hclosureImage hg)
  have hIdealEq : (⊥ : Ideal R) = IsLocalRing.maximalIdeal R :=
    congrArg (fun z : Spec (.of R) => z.asIdeal) hgenericClosed
  have hπmax : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have hπzero : ϖ ∈ (⊥ : Ideal R) := hIdealEq ▸ hπmax
  exact hϖ.ne_zero (Ideal.mem_bot.mp hπzero)

/-- Minimal primes of a localization contract to minimal primes. -/
private theorem minimalPrime_comap_of_localization
    {A L : Type u} [CommRing A] [CommRing L] (S : Submonoid A)
    [Algebra A L] [IsLocalization S L] {P : Ideal L}
    (hP : P ∈ Ideal.minimalPrimes (⊥ : Ideal L)) :
    P.comap (algebraMap A L) ∈ Ideal.minimalPrimes (⊥ : Ideal A) := by
  have hP' : P ∈ ((⊥ : Ideal A).map (algebraMap A L)).minimalPrimes := by
    simpa using hP
  rw [IsLocalization.minimalPrimes_map S L (⊥ : Ideal A)] at hP'
  simpa [Ideal.under_def] using hP'

/-- The image of a point of an affine chart in the base is the pullback of its prime of the
chart. -/
private theorem image_eq_comap_primeIdealOf
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    f x = PrimeSpectrum.comap (Spec.preimage (hU.fromSpec ≫ f)).hom (hU.primeIdealOf ⟨x, hx⟩) := by
  have he : hU.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ f)).hom) := by
    simp
  have hpx : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x := by
    simpa using hU.fromSpec_primeIdealOf ⟨x, hx⟩
  calc f x = (hU.fromSpec ≫ f) (hU.primeIdealOf ⟨x, hx⟩) := congrArg f hpx.symm
    _ = _ := congrArg (fun g => g (hU.primeIdealOf ⟨x, hx⟩)) he

/-- At a point of the special fibre, the image of a uniformizer lies in the prime of the chart
corresponding to that point. -/
private theorem uniformizer_mem_chartPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X) (U : X.Opens)
    (hU : IsAffineOpen U) (hx : x ∈ U)
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfx : f x = IsLocalRing.closedPoint (CommRingCat.of R)) :
    ((Spec.preimage (hU.fromSpec ≫ f)).hom ϖ) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hπ : ϖ ∈ (f x).asIdeal := by
    rw [hfx]
    change ϖ ∈ IsLocalRing.maximalIdeal R
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  rw [image_eq_comap_primeIdealOf f hU hx] at hπ
  exact hπ

/-- Reducedness of a fibre is inherited by the fibre of a restriction to an open subscheme:
for an open immersion `e : Y ⟶ X` and a factorization `e ≫ f = g`, the fibre of `g` over `y`
is an open subscheme of the fibre of `f` over `y`. -/
theorem isReduced_fiber_of_isOpenImmersion_comp
    {X Y B : Scheme.{u}} (e : Y ⟶ X) [IsOpenImmersion e]
    (f : X ⟶ B) (g : Y ⟶ B) (he : e ≫ f = g) (y : B)
    [IsReduced (f.fiber y)] : IsReduced (g.fiber y) := by
  let i : g.fiber y ≅ pullback e (f.fiberι y) :=
    (pullback.congrHom he rfl).symm ≪≫
      (pullbackRightPullbackFstIso f (B.fromSpecResidueField y) e).symm
  let j : g.fiber y ⟶ f.fiber y := i.hom ≫ pullback.snd e (f.fiberι y)
  have : IsOpenImmersion (pullback.snd e (f.fiberι y)) :=
    MorphismProperty.pullback_snd e (f.fiberι y) inferInstance
  have : IsOpenImmersion i.hom := inferInstance
  have : IsOpenImmersion j := inferInstance
  exact isReduced_of_isOpenImmersion j

/-- Reducedness of a fibre is inherited by the fibre of a restriction to an open subscheme. -/
private alias isReduced_fiber_of_isOpenImmersion := isReduced_fiber_of_isOpenImmersion_comp

/-- At a point of the special fibre of an affine chart, the quotient of the local ring by the
uniformizer is the local ring of the special fibre, hence reduced.  Equivalently: for a ring map
`φ : R → A` with `R` a discrete valuation ring and `q` a prime of `A` over the closed point of
`Spec R`, reducedness of the special fibre of `Spec φ` says exactly that the local ring of `A`
at `q` is reduced modulo the image of a uniformizer. -/
theorem isReduced_quotient_localization_of_isReduced_fiber
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R]
    [IsDiscreteValuationRing R] (φ : R →+* A)
    (y : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap φ q = y)
    (hy : y = IsLocalRing.closedPoint (CommRingCat.of R))
    (ϖ : R) (hϖ : Irreducible ϖ)
    [IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber y)] :
    _root_.IsReduced (Localization.AtPrime q.asIdeal ⧸
      Ideal.span ({algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ)} : Set _)) := by
  let : Algebra R A := RingHom.toAlgebra φ
  have hq' : PrimeSpectrum.comap (algebraMap R A) q = y := hq
  let α := PrimeSpectrum.preimageEquivFiber R A y
  let qbar : PrimeSpectrum (y.asIdeal.Fiber A) := α ⟨q, hq'⟩
  have hunder : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal =
      q.asIdeal := by
    show (α.invFun qbar).1.asIdeal = q.asIdeal
    simpa [qbar, α, PrimeSpectrum.preimageEquivFiber] using
      congrArg (fun z : {r // PrimeSpectrum.comap (algebraMap R A) r = y} => z.1.asIdeal)
        (α.left_inv ⟨q, hq'⟩)
  let eArrow := Spec.fiberToSpecResidueFieldIso R A y
  have : IsReduced (Spec (.of (y.asIdeal.Fiber A))) := by
    have : IsReduced (Arrow.mk (Scheme.Hom.fiberToSpecResidueField
        (Spec.map (CommRingCat.ofHom φ)) y)).left := ‹_›
    exact isReduced_of_isOpenImmersion eArrow.inv.left
  have : _root_.IsReduced ((Spec (.of (y.asIdeal.Fiber A))).presheaf.stalk qbar) :=
    isReduced_stalk_of_isReduced (Spec (.of (y.asIdeal.Fiber A))) qbar
  let eStalk := Spec.stalkIso (.of (y.asIdeal.Fiber A)) qbar
  have hStalkInj : Function.Injective eStalk.inv.hom := fun a b hab => by
    simpa using congrArg (fun z => eStalk.hom.hom z) hab
  have hredFiberLoc : _root_.IsReduced (Localization.AtPrime qbar.asIdeal) :=
    isReduced_of_injective eStalk.inv.hom hStalkInj
  let eFiber := Ideal.Fiber.algEquivAux₂ y.asIdeal qbar.asIdeal
  let r : Ideal A := Ideal.comap Algebra.TensorProduct.includeRight qbar.asIdeal
  let Jbar : Ideal (Localization.AtPrime r) :=
    Ideal.map (algebraMap A (Localization.AtPrime r)) (Ideal.map (algebraMap R A) y.asIdeal)
  have hJbar : Jbar = Ideal.span
      ({algebraMap A (Localization.AtPrime r) (φ ϖ)} : Set _) := by
    have hyIdeal : y.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal hy
    have hmax : y.asIdeal = Ideal.span ({ϖ} : Set R) := by
      rw [hyIdeal, hϖ.maximalIdeal_eq]
    dsimp [Jbar, r]
    calc
      Ideal.map (algebraMap A (Localization.AtPrime
          (Ideal.comap Algebra.TensorProduct.includeRight qbar.asIdeal)))
          (Ideal.map (algebraMap R A) y.asIdeal) =
        Ideal.map (algebraMap A (Localization.AtPrime
          (Ideal.comap Algebra.TensorProduct.includeRight qbar.asIdeal)))
          (Ideal.map (algebraMap R A) (Ideal.span ({ϖ} : Set R))) :=
            congrArg (fun I : Ideal R => Ideal.map (algebraMap A
              (Localization.AtPrime
                (Ideal.comap Algebra.TensorProduct.includeRight qbar.asIdeal)))
              (Ideal.map (algebraMap R A) I)) hmax
      _ = Ideal.span ({algebraMap A (Localization.AtPrime
          (Ideal.comap Algebra.TensorProduct.includeRight qbar.asIdeal)) (φ ϖ)} : Set _) := by
            rw [Ideal.map_span, Ideal.map_span]
            simp only [Set.image_singleton]
            congr 1
  have hredJbar : _root_.IsReduced (Localization.AtPrime r ⧸ Jbar) := by
    let : _root_.IsReduced (Localization.AtPrime qbar.asIdeal) := hredFiberLoc
    exact isReduced_of_injective eFiber.symm.toRingHom eFiber.symm.injective
  have hEq : r = q.asIdeal.comap (RingEquiv.refl A).toRingHom := hunder
  let eLoc := Localization.localRingEquiv r q.asIdeal (RingEquiv.refl A) hEq
  let Iq : Ideal (Localization.AtPrime q.asIdeal) :=
    Ideal.span ({algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ)} : Set _)
  have hmapI : Ideal.map (eLoc.toRingHom)
      (Ideal.span ({algebraMap A (Localization.AtPrime r) (φ ϖ)} : Set _)) = Iq := by
    dsimp [Iq]
    have hmap : eLoc (algebraMap A (Localization.AtPrime r) (φ ϖ)) =
        algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ) := by
      simp [eLoc, Localization.localRingEquiv]
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : Localization.AtPrime q.asIdeal => Ideal.span ({z} : Set _)) hmap
  let eQuot := Ideal.quotientEquiv
    (Ideal.span ({algebraMap A (Localization.AtPrime r) (φ ϖ)} : Set _))
    Iq eLoc hmapI.symm
  let : _root_.IsReduced (Localization.AtPrime r ⧸
      Ideal.span ({algebraMap A (Localization.AtPrime r) (φ ϖ)} : Set _)) := by
    rwa [← hJbar]
  exact isReduced_of_injective eQuot.symm.toRingHom eQuot.symm.injective

/-- The stalk at a point of the special fibre is reduced. -/
private theorem isReduced_stalk_of_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hcomponents : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z))
    [IsReduced (f.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))] (x : X)
    (hfx : f x = IsLocalRing.closedPoint (CommRingCat.of R)) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let A := Γ(X, U)
  let q := hU.primeIdealOf ⟨x, hxU⟩
  let φ : R →+* A := (Spec.preimage (hU.fromSpec ≫ f)).hom
  have he : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    simp [φ]
  have heval : f x = PrimeSpectrum.comap φ q := image_eq_comap_primeIdealOf f hU hxU
  let y : PrimeSpectrum R := f x
  have hq : PrimeSpectrum.comap φ q = y :=
    PrimeSpectrum.ext (congrArg (fun z : Spec (.of R) => z.asIdeal) heval).symm
  have hy : y = IsLocalRing.closedPoint (CommRingCat.of R) :=
    congrArg (fun z : Spec (.of R) => (z : PrimeSpectrum R)) hfx
  have : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsReduced (f.fiber y) := by
    rw [hy]
    infer_instance
  have : IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber y) :=
    isReduced_fiber_of_isOpenImmersion_comp hU.fromSpec f _ he y
  have : Algebra R A := RingHom.toAlgebra φ
  have hredQuot := isReduced_quotient_localization_of_isReduced_fiber φ y q hq hy ϖ hϖ
  let : Algebra A (Localization.AtPrime q.asIdeal) := inferInstance
  let : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) q.asIdeal :=
    Localization.isLocalization
  have hπmax : algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime q.asIdeal))
      (uniformizer_mem_chartPoint f x U hU hxU ϖ hϖ hfx)
  have hmin : ∀ P ∈ Ideal.minimalPrimes (⊥ : Ideal (Localization.AtPrime q.asIdeal)),
      algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ) ∉ P := fun P hP =>
    uniformizer_avoids_minimalPrime_chart f hcomponents hU.fromSpec φ he ϖ hϖ
      (minimalPrime_comap_of_localization q.asIdeal.primeCompl hP)
  have : _root_.IsReduced (Localization.AtPrime q.asIdeal) :=
    isReduced_of_reduced_quotient_of_not_mem_minimalPrimes
      (algebraMap A (Localization.AtPrime q.asIdeal) (φ ϖ)) hπmax hmin hredQuot
  exact (isReduced_localization_iff_isReduced_stalk hU hxU).mp ‹_›

/-- The residue field at the generic point of the spectrum of a discrete valuation ring is a
localization away from a uniformizer, so the generic point has an open fibre. -/
@[ega "IV 5.2.5" "partial"]
private theorem isOpenImmersion_genericPoint_residueField
    {R : CommRingCat.{u}} [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    IsOpenImmersion ((Spec R).fromSpecResidueField (⟨⊥, inferInstance⟩ : Spec R)) := by
  let ηs : Spec R := ⟨⊥, inferInstance⟩
  let K := ηs.asIdeal.ResidueField
  let alg : Algebra (↑R) K := IsLocalRing.ResidueField.algebra (Localization.AtPrime ηs.asIdeal)
  let : Algebra (↑R) K := alg
  let algMapη : (↑R) →+* K := @algebraMap (↑R) K _ _ alg
  have : IsFractionRing (↑R) K := by
    show IsFractionRing (↑R) ((⊥ : Ideal (↑R)).ResidueField)
    infer_instance
  have : IsLocalization.Away π (Localization.Away π) := inferInstance
  have hN : ∀ z : nonZeroDivisors (↑R), ∃ m : (↑R), m * z.1 ∈ Submonoid.powers π := by
    intro z
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp z.2) hπ
    obtain ⟨v, hv⟩ := hn.symm
    refine ⟨↑v⁻¹, ?_⟩
    rw [← hv]
    refine ⟨n, ?_⟩
    calc
      π ^ n = (↑v⁻¹ * ↑v) * π ^ n := by simp
      _ = (↑v⁻¹ : (↑R)) * (π ^ n * ↑v) := by ac_rfl
  have : IsLocalization (nonZeroDivisors (↑R)) (Localization.Away π) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (Localization.Away π)
      (Submonoid.powers π) (nonZeroDivisors (↑R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) hN
  let e : Localization.Away π ≃ₐ[↑R] K :=
    IsLocalization.algEquiv (nonZeroDivisors (↑R)) (Localization.Away π) K
  have : IsLocalization.Away π K := IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers π) e
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom algMapη)) :=
    IsOpenImmersion.of_isLocalization π
  have : IsOpenImmersion
      (Spec.map (Scheme.Spec.residueFieldIso R ηs).inv ≫
        Spec.map (CommRingCat.ofHom algMapη)) := inferInstance
  have hfactor :
      Spec.map (Scheme.Spec.residueFieldIso R ηs).inv ≫
        Spec.map (CommRingCat.ofHom algMapη) = (Spec R).fromSpecResidueField ηs :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R ηs
  rw [← hfactor]
  infer_instance

/-- **Reducedness of local rings passes to generalizations.** If `x ⤳ y` in a scheme and the
local ring at `y` is reduced, then so is the local ring at `x`, being a localization of it. -/
theorem isReduced_stalk_of_specializes_of_isReduced {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y)
    (hy : _root_.IsReduced (X.presheaf.stalk y)) : _root_.IsReduced (X.presheaf.stalk x) :=
  @isReduced_stalk_of_specializes X x y hxy hy

/-- **The generic point of the spectrum of a discrete valuation ring has an open fibre.** The
morphism from the spectrum of the residue field at the generic point is an open immersion, the
residue field there being the localization away from a uniformizer. -/
theorem isOpenImmersion_fromSpecResidueField_genericPoint
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion ((Spec (.of R)).fromSpecResidueField (⟨⊥, inferInstance⟩ : Spec (.of R))) :=
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  isOpenImmersion_genericPoint_residueField (R := CommRingCat.of R) ϖ hϖ

end

/-- **Stacks Project, Tag 0C0D (total space).** A proper scheme over a discrete valuation
ring is reduced if every irreducible component dominates the base and the special fibre is
reduced. -/
@[stacks 0C0D "total space"]
theorem isReduced_of_isProper_over_dvr_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hcomponents : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z))
    [IsReduced (f.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    rcases base_point_bot_or_top (f x) with hgeneric | hclosed
    · obtain ⟨y, hyf, hxy⟩ := exists_specializes_closedPoint_of_generic f x hgeneric
      have : _root_.IsReduced (X.presheaf.stalk y) :=
        isReduced_stalk_of_closedPoint f hcomponents y hyf
      exact isReduced_stalk_of_specializes hxy
    · exact isReduced_stalk_of_closedPoint f hcomponents x hclosed
  exact isReduced_of_isReduced_stalk X

/-- **Stacks Project, Tag 0C0D (generic fibre).** A proper scheme over a discrete valuation
ring has reduced generic fibre if every irreducible component dominates the base and the
special fibre is reduced. -/
@[stacks 0C0D "generic fibre"]
theorem isReduced_genericFiber_of_isProper_over_dvr_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hcomponents : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z))
    [IsReduced (f.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))] :
    IsReduced (f.fiber (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsReduced X := isReduced_of_isProper_over_dvr_of_isReduced_specialFiber f hcomponents
  let η : Spec (.of R) := ⟨⊥, inferInstance⟩
  have : IsOpenImmersion ((Spec (.of R)).fromSpecResidueField η) :=
    isOpenImmersion_genericPoint_residueField (R := CommRingCat.of R) ϖ hϖ
  have : IsOpenImmersion (f.fiberι η) :=
    CategoryTheory.MorphismProperty.pullback_fst f
      ((Spec (.of R)).fromSpecResidueField η) inferInstance
  exact isReduced_of_isOpenImmersion (f.fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R))

end AlgebraicGeometry
