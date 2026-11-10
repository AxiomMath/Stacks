module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.RingTheory.Localization.Idempotent
public import StacksFrontier.RingTheory.TraceElement.Independence

/-!
# Trace elements and localization of the target

Let `A → B` be a flat quasi-finite map of Noetherian rings and `g` an element of `B`. A trace
element of the relative dualizing module of `B` over `A` stays a trace element in the relative
dualizing module of `B_g` over `A`, under the identification of Tag 0BT2, part (2).

The trace-element condition over `B_g` tests decompositions `A₁ ⊗_A B_g ≃ C × D` with `C` finite
over `A₁`. Such a decomposition is already visible on `A₁ ⊗_A B` itself: the image of `Spec C` in
`Spec (A₁ ⊗_A B)` is open, because it is open in the localization, and closed, because
`A₁ ⊗_A B → C` is integral, so the clopen subset it defines is the basic open of an idempotent
`q` and `A₁ ⊗_A B ≃ C × (A₁ ⊗_A B)/(1 - q)`. Testing the original trace element against that
decomposition gives the same functional on `C`, because the two intermediate algebras are the
same ring acting on `C` by the same scalars.

## Main results

* `Stacks.Discriminant.exists_idempotent_prodEquiv_of_isLocalizationAway`: a finite direct
  factor of an away localization is a direct factor of the ring, cut out by an idempotent.
* `Stacks.Discriminant.isLocalization_away_one_tmul`: `A₁ ⊗_A B_g` is the away localization of
  `A₁ ⊗_A B` at `1 ⊗ g`.
* `Stacks.Discriminant.isTraceElement_localization`: Tag 0BT9, localizing the target carries
  trace elements to trace elements.

## Implementation notes

The factorization used for `B_g` is `Stacks.Discriminant.locFact`, which keeps the intermediate
algebra of the given factorization of `B` unchanged. Its intermediate algebra is therefore the
same ring as that of the original factorization, but the two carry different — definitionally
equal — algebra structures on the finite factor `C`. Instance search distinguishes them, since
`locFact` does not unfold at reducible transparency, while `exact` identifies them; the trace of
multiplication is transported between them by
`Stacks.Discriminant.finiteProjectiveTrace_congr_ringEquiv` at the identity equivalence.

## References

* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
-/
@[expose] public section

universe u v w x y z s t r

open AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- A finite direct factor of an away localization `R_s` descends to a direct factor of `R`:
there is an idempotent `q` with `R ≃ C × R/(1 - q)` inducing the given projection to `C`.

The map `R → C` is integral because `C` is finite over the base, so its image on spectra is
closed; it is also open, being the composite of an away localization with a projection. A clopen
subset of a spectrum is a basic open of an idempotent. -/
theorem exists_idempotent_prodEquiv_of_isLocalizationAway
    {A : Type u} {R : Type v} {Rg : Type w} {C : Type x} {D : Type y}
    [CommRing A] [CommRing R] [CommRing Rg] [CommRing C] [CommRing D]
    [Algebra A R] [Algebra R Rg] [Algebra A Rg] [IsScalarTower A R Rg]
    [Algebra A C] [Algebra A D]
    (s : R) [IsLocalization.Away s Rg] (e : Rg ≃ₐ[A] C × D) [Module.Finite A C] :
    ∃ q : R, IsIdempotentElem q ∧ ∃ e₁ : R ≃ₐ[A] C × (R ⧸ Ideal.span {1 - q}),
      ∀ x : R, (e₁ x).1 = (e (algebraMap R Rg x)).1 := by
  classical
  let f : R →ₐ[A] C :=
    (AlgHom.fst A C D).comp (e.toAlgHom.comp (IsScalarTower.toAlgHom A R Rg))
  let : Algebra R C := f.toRingHom.toAlgebra
  have : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  have hfgA : (⊤ : Submodule A C).FG := Module.finite_def.mp ‹Module.Finite A C›
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hfgA
  have hASpanLe : Submodule.span A (S : Set C) ≤
      (Submodule.span R (S : Set C)).restrictScalars A :=
    Submodule.span_le.2 fun c hc => Submodule.subset_span hc
  have hRSpan : Submodule.span R (S : Set C) = ⊤ :=
    top_unique fun c _ => hASpanLe (by simp [hSspan])
  have : Module.Finite R C := Module.finite_def.mpr (Submodule.fg_def.mpr ⟨S, hSfinite, hRSpan⟩)
  have hIntegral : f.toRingHom.IsIntegral :=
    RingHom.IsIntegral.of_finite (show Module.Finite R C from inferInstance)
  let ι : R →+* Rg := algebraMap R Rg
  let ε : Rg ≃+* C × D := e.toRingEquiv
  let π : C × D →+* C := RingHom.fst C D
  have hcomp : PrimeSpectrum.comap f.toRingHom =
      (PrimeSpectrum.comap ι) ∘ (PrimeSpectrum.comap ε.toRingHom) ∘ (PrimeSpectrum.comap π) := by
    funext p
    change PrimeSpectrum.comap (π.comp (ε.toRingHom.comp ι)) p = _
    simp [PrimeSpectrum.comap_comp_apply, Function.comp_def]
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap f.toRingHom)) := by
    let : Algebra (C × D) C := π.toAlgebra
    have hι : IsOpenEmbedding (PrimeSpectrum.comap ι) :=
      PrimeSpectrum.localization_away_isOpenEmbedding Rg s
    have hπ : IsOpenEmbedding (PrimeSpectrum.comap π) :=
      PrimeSpectrum.localization_away_isOpenEmbedding C (1, 0)
    let eSpec : PrimeSpectrum Rg ≃ₜ PrimeSpectrum (C × D) :=
      { (PrimeSpectrum.comapEquiv ε).toEquiv with
        continuous_toFun := PrimeSpectrum.continuous_comap _
        continuous_invFun := PrimeSpectrum.continuous_comap _ }
    have hε : IsOpenEmbedding (PrimeSpectrum.comap ε.toRingHom) := eSpec.symm.isOpenEmbedding
    rw [hcomp]
    exact (hι.comp (hε.comp hπ)).isOpen_range
  have hrangeClosed : IsClosed (Set.range (PrimeSpectrum.comap f.toRingHom)) := by
    simpa using PrimeSpectrum.isClosedMap_comap_of_isIntegral f.toRingHom hIntegral _
      (isClosed_univ : IsClosed (Set.univ : Set (PrimeSpectrum C)))
  obtain ⟨qC, hqC, hqCRange⟩ :=
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen ⟨hrangeClosed, hopen⟩
  let mid : Rg →+* C := π.comp ε.toRingHom
  let qRg : Rg := ε.symm (1, 0)
  let : Algebra Rg C := mid.toAlgebra
  have hqRg : IsIdempotentElem qRg := by
    refine ε.injective ?_
    simp [qRg]
  have hmidKer : RingHom.ker mid = Ideal.span {1 - qRg} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    refine ⟨fun hx => ⟨ε.symm (0, (ε x).2), ?_⟩, ?_⟩
    · change (ε x).1 = 0 at hx
      refine ε.injective ?_
      ext <;> simp [qRg, hx]
    · rintro ⟨y, hy⟩
      rw [← hy]
      simp [mid, qRg, π]
  have hmidSurj : Function.Surjective mid := fun c => ⟨ε.symm (c, 0), by simp [mid, π]⟩
  have : IsLocalization.Away qRg C :=
    IsLocalization.away_of_isIdempotentElem hqRg hmidKer hmidSurj
  have hqPull : (PrimeSpectrum.comap ι) ⁻¹' PrimeSpectrum.basicOpen qC =
      PrimeSpectrum.basicOpen qRg := by
    calc
      (PrimeSpectrum.comap ι) ⁻¹' PrimeSpectrum.basicOpen qC =
          (PrimeSpectrum.comap ι) ⁻¹' Set.range (PrimeSpectrum.comap f.toRingHom) := by
            rw [hqCRange]
      _ = Set.range (PrimeSpectrum.comap mid) := by
            rw [hcomp, Set.range_comp, Set.preimage_image_eq _
              (PrimeSpectrum.localization_away_isOpenEmbedding Rg s).injective]
            rfl
      _ = PrimeSpectrum.basicOpen qRg := PrimeSpectrum.localization_away_comap_range C qRg
  have hqLocal : algebraMap R Rg qC = qRg := by
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ?_ hqRg ?_
    · exact hqC.map (algebraMap R Rg)
    · refine TopologicalSpace.Opens.ext ?_
      simpa [PrimeSpectrum.comap_basicOpen] using hqPull
  have hqf : f qC = 1 := by
    have hunit : IsUnit (f qC) := by
      by_contra hnot
      obtain ⟨m, hmmax, hmspan⟩ :=
        Ideal.exists_le_maximal (Ideal.span {f qC}) (Ideal.span_singleton_ne_top hnot)
      let p : PrimeSpectrum C := ⟨m, hmmax.isPrime⟩
      have hmem : f qC ∈ p.asIdeal := hmspan (Ideal.subset_span (Set.mem_singleton _))
      have hp : PrimeSpectrum.comap f.toRingHom p ∈ PrimeSpectrum.basicOpen qC := by
        have hp' : PrimeSpectrum.comap f.toRingHom p ∈
          Set.range (PrimeSpectrum.comap f.toRingHom) := ⟨p, rfl⟩
        rw [hqCRange] at hp'
        exact hp'
      exact ((PrimeSpectrum.mem_basicOpen qC _).mp hp) hmem
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (hqC.map f)
  have hqmem : qC ∈ Ideal.span {s} := by
    have hrangeSubset : PrimeSpectrum.basicOpen qC ≤ PrimeSpectrum.basicOpen s := by
      change (PrimeSpectrum.basicOpen qC : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.basicOpen s
      rw [← hqCRange, ← PrimeSpectrum.localization_away_comap_range Rg s]
      rintro p ⟨x, rfl⟩
      refine ⟨PrimeSpectrum.comap mid x, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply]
      rfl
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp
      ((PrimeSpectrum.basicOpen_le_basicOpen_iff qC s).mp hrangeSubset)
    cases n with
    | zero =>
        have htop : Ideal.span {s} = ⊤ := by
          rw [Ideal.eq_top_iff_one]
          simpa using hn
        simp [htop]
    | succ n => simpa [hqC.pow_succ_eq n] using hn
  obtain ⟨t, hqst⟩ := Ideal.mem_span_singleton'.mp hqmem
  have hqst' : s * t = qC := by simpa [mul_comm] using hqst
  have hfsft : f s * f t = 1 := by rw [← map_mul, hqst', hqf]
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨⟨x, m⟩, hrep⟩ := IsLocalization.surj (Submonoid.powers s) (e.symm (c, 0))
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m.1 s).mp m.2
    rw [← hn] at hrep
    have hcfspow : c * (f s) ^ n = f x := by simpa [f] using congrArg Prod.fst (congrArg e hrep)
    refine ⟨x * t ^ n, ?_⟩
    calc
      f (x * t ^ n) = f x * (f t) ^ n := by rw [map_mul, map_pow]
      _ = (c * (f s) ^ n) * (f t) ^ n := by rw [hcfspow]
      _ = c * ((f s) * (f t)) ^ n := by ring
      _ = c := by rw [hfsft, one_pow, mul_one]
  have hker : RingHom.ker f = Ideal.span {1 - qC} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    refine ⟨fun hr => ?_, ?_⟩
    · have hzero : algebraMap R Rg (qC * x) = 0 := by
        refine ε.injective ?_
        rw [map_mul, hqLocal]
        have hr' : (ε (algebraMap R Rg x)).1 = 0 := by
          simpa [f, ε, π] using (show f x = 0 from hr)
        have hqpair : ε qRg = (1, 0) := by simp [qRg]
        exact Prod.ext (by simp [hqpair, hr']) (by simp [hqpair])
      obtain ⟨m, hm⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers s) Rg (qC * x)).mp hzero
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m.1 s).mp m.2
      rw [← hn] at hm
      have hqrmul : qC * x = 0 := by
        cases n with
        | zero => simpa using hm
        | succ n =>
          calc
            qC * x = qC * (qC * x) := by rw [← mul_assoc, hqC.eq]
            _ = (s ^ (n + 1) * t ^ (n + 1)) * (qC * x) := by
              rw [← mul_pow, hqst', hqC.pow_succ_eq n]
            _ = t ^ (n + 1) * (s ^ (n + 1) * (qC * x)) := by ac_rfl
            _ = 0 := by rw [hm, mul_zero]
      exact ⟨x, by linear_combination -hqrmul⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      simp [hqf]
  have hq : IsIdempotentElem (1 - qC) := hqC.one_sub
  let eprod : R ≃ₐ[A] (R ⧸ Ideal.span {1 - qC}) × (R ⧸ Ideal.span {qC}) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem A hq (by simpa using hqC) (by simp)
      (by rw [sub_mul, one_mul, hqC.eq, sub_self])
  let eqv := (Ideal.quotientEquivAlgOfEq A (show Ideal.span {1 - qC} = RingHom.ker f from
      hker.symm)).trans (Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj)
  have hJ : Ideal.span ({qC} : Set R) = Ideal.span ({1 - (1 - qC)} : Set R) := by
    rw [show (1 : R) - (1 - qC) = qC by ring]
  refine ⟨1 - qC, hq, (eprod.trans (AlgEquiv.prodCongr eqv AlgEquiv.refl)).trans
    (AlgEquiv.prodCongr AlgEquiv.refl (Ideal.quotientEquivAlgOfEq A hJ)), fun x => ?_⟩
  change eqv (Ideal.Quotient.mk (Ideal.span {1 - qC}) x) = (e (algebraMap R Rg x)).1
  simp [eqv, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk, f]

/-- Scalar extension of an away localization is the away localization at the extended element,
for the extension of the ring in which the element lives. -/
theorem isLocalization_away_one_tmul
    {A : Type u} {A₁ : Type s} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing Bg]
    [Algebra A A₁] [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [Algebra (A₁ ⊗[A] B) (A₁ ⊗[A] Bg)] [IsScalarTower A₁ (A₁ ⊗[A] B) (A₁ ⊗[A] Bg)]
    (hmap : (algebraMap (A₁ ⊗[A] B) (A₁ ⊗[A] Bg)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B Bg))
    (g : B) [IsLocalization.Away g Bg] :
    IsLocalization.Away ((1 : A₁) ⊗ₜ[A] g) (A₁ ⊗[A] Bg) := by
  have h := IsLocalization.tensorProduct_tensorProduct_right A A₁ (Submonoid.powers g) Bg hmap
  change IsLocalization (Submonoid.powers ((1 : A₁) ⊗ₜ[A] g)) (A₁ ⊗[A] Bg)
  simpa [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using h

/-- **Stacks Project, Tag 0BT9.** A trace element of the relative dualizing module of a flat
quasi-finite map of Noetherian rings remains a trace element after an away localization of the
target, under the identification of Tag 0BT2, part (2). -/
@[stacks 0BT9 "trace_algebra_localization"]
theorem isTraceElement_localization
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers g) localizationMap)
    {τ : dualizingModule F} (hτ : IsTraceElement.{u, v, y, s, t, max s v} F τ) :
    letI : IsNoetherianRing Bg :=
      IsLocalization.isNoetherianRing (Submonoid.powers g) Bg inferInstance
    letI : Module.Flat B Bg := IsLocalization.flat Bg (Submonoid.powers g)
    letI : Module.Flat A Bg := Module.Flat.trans A B Bg
    letI : Algebra.QuasiFinite A Bg :=
      Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g)
    IsTraceElement.{u, w, z, s, t, r} G
      (localizedModule_dualizingModule_equiv g F G localizationMap hM
        (localizationMap τ)) := by
  let : IsNoetherianRing Bg :=
    IsLocalization.isNoetherianRing (Submonoid.powers g) Bg inferInstance
  let : Module.Flat B Bg := IsLocalization.flat Bg (Submonoid.powers g)
  let : Module.Flat A Bg := Module.Flat.trans A B Bg
  let : Algebra.QuasiFinite A Bg :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g)
  let H : FiniteOpenFactorization.{u, w, y} A Bg := locFact (Bg := Bg) g F
  have hH : IsTraceElement.{u, w, y, s, t, r} H
      (localizedModule_dualizingModule_equiv g F H localizationMap hM
        (localizationMap τ)) := by
    intro A₁ _ _ _ C D _ _ _ _ e hfinite
    have : Module.Finite A₁ C := hfinite
    let loc : (A₁ ⊗[A] B) →+* (A₁ ⊗[A] Bg) :=
      (Algebra.TensorProduct.map (AlgHom.id A A₁) (IsScalarTower.toAlgHom A B Bg)).toRingHom
    let : Algebra (A₁ ⊗[A] B) (A₁ ⊗[A] Bg) := loc.toAlgebra
    have : IsScalarTower A₁ (A₁ ⊗[A] B) (A₁ ⊗[A] Bg) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change ((a ⊗ₜ[A] (1 : Bg)) : A₁ ⊗[A] Bg) = loc (a ⊗ₜ[A] (1 : B))
        simp [loc]
    have hloc : ∀ b : B, loc ((1 : A₁) ⊗ₜ[A] b) = (1 : A₁) ⊗ₜ[A] algebraMap B Bg b := fun b => by
      simp [loc]
    have hincludeRight : (algebraMap (A₁ ⊗[A] B) (A₁ ⊗[A] Bg)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B Bg) := by
      ext b
      exact hloc b
    have : IsLocalization.Away ((1 : A₁) ⊗ₜ[A] g) (A₁ ⊗[A] Bg) :=
      isLocalization_away_one_tmul hincludeRight g
    obtain ⟨idem, hidem, e₁, he₁⟩ :=
      exists_idempotent_prodEquiv_of_isLocalizationAway ((1 : A₁) ⊗ₜ[A] g) e
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let H₁ := FiniteOpenFactorization.baseChange H A₁
    let algLoc : Algebra H₁.middle C :=
      ((RingHom.fst C D).comp
        (e.toRingEquiv.toRingHom.comp H₁.algebraTarget.algebraMap)).toAlgebra
    let algBase : Algebra F₁.middle C :=
      ((RingHom.fst C ((A₁ ⊗[A] B) ⧸ Ideal.span {1 - idem})).comp
        (e₁.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
    obtain ⟨hp, hmfS, hmpS, hsource⟩ :=
      hτ A₁ C ((A₁ ⊗[A] B) ⧸ Ideal.span {1 - idem}) e₁ hfinite
    have : Module.Projective A₁ C := hp
    have : Module.Finite F₁.middle C := hmfS
    have : Module.Projective F₁.middle C := hmpS
    obtain ⟨hmfT, hmpT⟩ :=
      finite_and_projective_of_prodEquiv_middle H₁ e (fun _ => rfl) hfinite
    have : Module.Finite H₁.middle C := hmfT
    have : Module.Projective H₁.middle C := hmpT
    have hmapFactors : (algebraMap (A₁ ⊗[A] B) (A₁ ⊗[A] Bg)).comp
          F₁.algebraTarget.algebraMap = H₁.algebraTarget.algebraMap := by
      change (Algebra.TensorProduct.map (AlgHom.id A A₁)
            (IsScalarTower.toAlgHom A B Bg)).toRingHom.comp
          (Algebra.TensorProduct.map (AlgHom.id A A₁)
            (IsScalarTower.toAlgHom A F.middle B)).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id A A₁)
          ((IsScalarTower.toAlgHom A B Bg).comp
            (IsScalarTower.toAlgHom A F.middle B))).toRingHom
      have hcomp := Algebra.TensorProduct.map_comp (AlgHom.id A A₁) (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A B Bg) (IsScalarTower.toAlgHom A F.middle B)
      exact RingHom.ext fun u => congrArg (fun k => k u) hcomp.symm
    have hmiddleMap : ∀ a : F₁.middle,
        algebraMap H₁.middle C a = algebraMap F₁.middle C a := fun a => by
      change (e (H₁.algebraTarget.algebraMap a)).1 = (e₁ (F₁.algebraTarget.algebraMap a)).1
      rw [he₁ (F₁.algebraTarget.algebraMap a)]
      exact (congrArg (fun u => (e u).1) (DFunLike.congr_fun hmapFactors a)).symm
    have htrace (value : C) :
        @finiteProjectiveTrace F₁.middle _ C _ algBase.toModule hmfS hmpS
            (@Algebra.lmul F₁.middle C _ _ algBase value) =
          @finiteProjectiveTrace H₁.middle _ C _ algLoc.toModule hmfT hmpT
            (@Algebra.lmul H₁.middle C _ _ algLoc value) :=
      @finiteProjectiveTrace_congr_ringEquiv F₁.middle H₁.middle _ _
        (RingEquiv.refl F₁.middle) C _ algBase algLoc hmfS hmpS hmfT hmpT hmiddleMap
        (@Algebra.lmul F₁.middle C _ _ algBase value)
        (@Algebra.lmul H₁.middle C _ _ algLoc value) (fun _ => rfl)
    let restrictLoc := finiteFactorRestriction H A₁ C D e (fun _ => rfl) hfinite hp hmfT hmpT
    let restrictBase := finiteFactorRestriction F A₁ C
      ((A₁ ⊗[A] B) ⧸ Ideal.span {1 - idem}) e₁ (fun _ => rfl) hfinite hp hmfS hmpS
    have hbridge : ∀ ω : dualizingModule F,
        restrictLoc.1 (dualizingModule.baseChange H A₁
            (localizedModule_dualizingModule_equiv g F H localizationMap hM
              (localizationMap ω))) =
          restrictBase.1 (dualizingModule.baseChange F A₁ ω) := by
      intro ω
      refine dualizingModule.induction_on F (motive := fun ω =>
        restrictLoc.1 (dualizingModule.baseChange H A₁
            (localizedModule_dualizingModule_equiv g F H localizationMap hM
              (localizationMap ω))) =
          restrictBase.1 (dualizingModule.baseChange F A₁ ω)) ω ?_ ?_
      · intro φ b
        have hcoeff : (e₁ ((1 : A₁) ⊗ₜ[A] b)).1 =
            (e ((1 : A₁) ⊗ₜ[A] algebraMap B Bg b)).1 := by
          rw [he₁ ((1 : A₁) ⊗ₜ[A] b)]
          exact congrArg (fun u => (e u).1) (hloc b)
        have hloc := localizedModule_dualizingModule_equiv_tmul g F H localizationMap hM
          (AlgEquiv.refl : H.middle ≃ₐ[A] F.middle) (fun _ => rfl) φ b
        refine LinearMap.ext fun value => ?_
        have hstep : (Module.Dual.baseChange A₁ φ)
              (finiteProjectiveTrace H₁.middle C (Algebra.lmul H₁.middle C
                ((e ((1 : A₁) ⊗ₜ[A] algebraMap B Bg b)).1 * value))) =
            (Module.Dual.baseChange A₁ φ)
              (finiteProjectiveTrace F₁.middle C (Algebra.lmul F₁.middle C
                ((e₁ ((1 : A₁) ⊗ₜ[A] b)).1 * value))) := by
          rw [hcoeff]
          exact (congrArg (Module.Dual.baseChange A₁ φ) (htrace _)).symm
        rw [hloc]
        exact (restrictLoc.2 (Module.Dual.baseChange A₁ φ)
            ((1 : A₁) ⊗ₜ[A] algebraMap B Bg b) value).trans
          (hstep.trans (restrictBase.2 (Module.Dual.baseChange A₁ φ)
            ((1 : A₁) ⊗ₜ[A] b) value).symm)
      · intro ω₁ ω₂ h₁ h₂
        simp only [map_add, h₁, h₂]
    exact ⟨hp, hmfT, hmpT, (hbridge τ).trans hsource⟩
  have key := (isTraceElement_congr H G _).mp hH
  rwa [localizedModule_dualizingModule_equiv_natural g F H G localizationMap hM
    (localizationMap τ)] at key

end Stacks.Discriminant

end
