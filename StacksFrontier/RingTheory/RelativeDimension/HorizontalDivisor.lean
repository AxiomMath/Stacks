module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineGeneralCase
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension

/-!
# A horizontal divisor over a local base dominates the base

Let `A ⊆ B` be an injective local homomorphism of local domains with `B` essentially of finite
type over `A`, and let `g ∈ 𝔪_B`. If `g` lies in no minimal prime over `𝔪_A B` and the closed
fibre satisfies `dim (B/𝔪_A B) + trdeg_{κ(𝔪_A)} κ(𝔪_B) = trdeg_A B`, then `A → B/gB` is again
injective, so the generic point of `Spec A` lies in the image of `Spec (B/gB) → Spec A`.

## Main results

* `IsLocalRing.injective_quotient_of_dimension_add_trdeg_eq`: `A` embeds in `B/gB`.

## Implementation notes

The conclusion is stated as injectivity of the composite `A → B → B/gB` rather than as a
statement about the image of `Spec (B/gB) → Spec A`; the two are equivalent.

The dimension of the closed fibre is `ringKrullDim (B ⧸ (𝔪_A).map (algebraMap A B))` and
transcendence degrees are compared in `WithBot ℕ∞` through `Cardinal.toENat`, matching
`IsLocalRing.ringKrullDim_closedFiber_add_trdeg_eq_trdeg`, which supplies the dimension
hypothesis in the flat case.

The argument of the source descends `B` to an `A`-algebra `C` of finite type containing `g`,
where `Spec C ⟶ Spec A` is a dominant morphism locally of finite type, and applies Stacks 053R
to the locally principal closed subscheme cut out by `g`. No Noetherian hypothesis is needed:
Stacks 053R is used through
`Stacks.Divisors.fiber_zeroLocus_specMap_eq_sUnion_irreducibleComponents`, the affine form of
the general case. The replacement of `C` by a principal localization, which the source performs
to arrange that the minimal primes of the two closed fibres correspond, is carried out here by
choosing the localization that computes the *local* dimension of `Spec (C/𝔪_A C)` at the point
of `B`: `exists_notMem_ringKrullDim_localization_le` produces it, and
`IsLocalization.minimalPrimes_map` transports the minimal primes back.

`Algebra.EssFiniteType` of an essentially-of-finite-type extension and the local-dimension
formula `IsLocalRing.localKrullDim_eq_ringKrullDim_add_trdeg` are taken from
`StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension`.

## References

* [Stacks Project, Tag 053S](https://stacks.math.columbia.edu/tag/053S)
* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
* [Stacks Project, Tag 053T](https://stacks.math.columbia.edu/tag/053T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace IsLocalRing

universe u

/-- An essentially finite type algebra over a local ring is a localization at a prime of a
finite type subalgebra, which may be taken to contain any prescribed finite set. -/
private theorem exists_finiteType_subalgebra_localization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] [Algebra.EssFiniteType A B] (s : Finset B) :
    ∃ C : Subalgebra A B, (↑s : Set B) ⊆ C ∧ Algebra.FiniteType A C ∧
      IsLocalization.AtPrime B ((maximalIdeal B).comap C.val) := by
  classical
  obtain ⟨t, ht⟩ := (Algebra.essFiniteType_iff A B).mp inferInstance
  let C := Algebra.adjoin A (↑(t ∪ s) : Set B)
  have hle : Algebra.adjoin A (↑t : Set B) ≤ C :=
    Algebra.adjoin_mono (Finset.coe_subset.mpr Finset.subset_union_left)
  have hloc : IsLocalization ((IsUnit.submonoid B).comap (algebraMap C B)) B :=
    (Algebra.essFiniteType_cond_iff A B (t ∪ s)).mpr fun b ↦ by
      obtain ⟨d, hd, hunit, hbd⟩ := ht b
      exact ⟨d, hle hd, hunit, hle hbd⟩
  refine ⟨C, fun b hb ↦ Algebra.subset_adjoin (Finset.mem_union_right t hb),
    (Subalgebra.fg_iff_finiteType C).mp (Subalgebra.fg_adjoin_finset (t ∪ s)), ?_⟩
  have heq : ((maximalIdeal B).comap C.val).primeCompl =
      (IsUnit.submonoid B).comap (algebraMap C B) := by
    ext b
    exact notMem_maximalIdeal
  change IsLocalization _ B
  rwa [heq]

/-- A localization of a domain at a submonoid of nonzerodivisors is algebraic over it. -/
private theorem isAlgebraic_of_isLocalization
    {R T : Type u} [CommRing R] [CommRing T] [IsDomain R] [Algebra R T]
    (M : Submonoid R) [IsLocalization M T] (hM : M ≤ nonZeroDivisors R) :
    Algebra.IsAlgebraic R T := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M x
  apply IsAlgebraic.of_smul (hM b.property)
  rw [Algebra.smul_def, mul_comm, hab]
  exact isAlgebraic_algebraMap a

/-- Inverting nonzerodivisors does not change the transcendence degree over a smaller domain. -/
private theorem trdeg_eq_of_isLocalization
    {A C T : Type u} [CommRing A] [CommRing C] [CommRing T]
    [IsDomain A] [IsDomain C] [IsDomain T]
    [Algebra A C] [Algebra A T] [Algebra C T] [IsScalarTower A C T]
    (M : Submonoid C) [IsLocalization M T]
    (hinj : Function.Injective (algebraMap A C)) (hM : M ≤ nonZeroDivisors C) :
    Algebra.trdeg A C = Algebra.trdeg A T := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hinj
  have : FaithfulSMul C T := (faithfulSMul_iff_algebraMap_injective C T).mpr
    (IsLocalization.injective T hM)
  have : Algebra.IsAlgebraic C T := isAlgebraic_of_isLocalization M hM
  simpa only [trdeg_eq_zero, add_zero] using trdeg_add_eq A C (A := T)

/-- The generic fibre of a finite type extension of domains has dimension equal to the
transcendence degree of the extension. -/
private theorem genericFiber_dimension_eq_trdeg
    {A C : Type u} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [Algebra A C] [Algebra.FiniteType A C]
    (hinj : Function.Injective (algebraMap A C)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap A C))).fiber
      (genericPoint (Spec (CommRingCat.of A)))) =
        (Cardinal.toENat (Algebra.trdeg A C) : WithBot ℕ∞) := by
  let K := (⊥ : Ideal A).ResidueField
  let T := (⊥ : Ideal A).Fiber C
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid C (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors C :=
    map_le_nonZeroDivisors_of_injective (algebraMap A C) hinj le_rfl
  have : IsLocalization M T := inferInstance
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    (IsFractionRing.injective A K)
  have : Algebra.IsAlgebraic A K :=
    isAlgebraic_of_isLocalization (nonZeroDivisors A) le_rfl
  have : FaithfulSMul K T := (faithfulSMul_iff_algebraMap_injective K T).mpr
    (algebraMap K T).injective
  have hAKT : Algebra.trdeg K T = Algebra.trdeg A T := by
    simpa only [trdeg_eq_zero, zero_add] using trdeg_add_eq A K (A := T)
  have hACT := trdeg_eq_of_isLocalization (T := T) M hinj hM
  have hTFrac := trdeg_eq_of_isLocalization
    (A := K) (C := T) (T := FractionRing T) (nonZeroDivisors T)
    (algebraMap K T).injective le_rfl
  have hd := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, 0}
    K T (FractionRing T)).1
  rw [← hTFrac, hAKT, ← hACT] at hd
  rw [genericPoint_eq_bot_of_affine]
  let e := Scheme.homeoOfIso (CategoryTheory.Arrow.leftFunc.mapIso
    (Spec.fiberToSpecResidueFieldIso A C (⊥ : PrimeSpectrum A)))
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans
    ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim T).trans hd)

/-- A basic open neighbourhood of a point of a spectrum whose dimension computes the local
dimension there. -/
private theorem exists_notMem_ringKrullDim_localization_le
    {R : Type u} [CommRing R] (x : PrimeSpectrum R) :
    ∃ h ∉ x.asIdeal, ringKrullDim (Localization.Away h) ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum R) x := by
  obtain ⟨U, hxU, hU, hdim⟩ := (topologicalKrullDimAt_isLeast (PrimeSpectrum R) x).1
  obtain ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hx, hhU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU hU
  refine ⟨h, hx, ?_⟩
  let e := (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away h) h).isEmbedding
    |>.toHomeomorph |>.trans
      (Homeomorph.setCongr (PrimeSpectrum.localization_away_comap_range (Localization.Away h) h))
  calc ringKrullDim (Localization.Away h)
      = topologicalKrullDim (PrimeSpectrum (Localization.Away h)) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) :=
      IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph
    _ ≤ topologicalKrullDim U :=
      (Topology.IsEmbedding.inclusion hhU).isInducing.topologicalKrullDim_le
    _ = TopologicalSpace.localKrullDim (PrimeSpectrum R) x :=
      hdim.symm.trans (TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim _ _)

/-- The primes of the closed fibre of `Spec C ⟶ Spec A` are exactly the primes of `C` lying over
the closed point of the local ring `A`. -/
private theorem range_comap_quotient_closedFiber
    {A C : Type u} [CommRing A] [CommRing C] [IsLocalRing A] [Algebra A C] :
    Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A C)))) =
        (PrimeSpectrum.comap (algebraMap A C)) ⁻¹' {closedPoint A} := by
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext q
  change (maximalIdeal A).map (algebraMap A C) ≤ q.asIdeal ↔
    PrimeSpectrum.comap (algebraMap A C) q = closedPoint A
  rw [Ideal.map_le_iff_le_comap]
  exact ⟨fun h ↦ PrimeSpectrum.ext
    ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) h).symm,
    fun h ↦ (congrArg PrimeSpectrum.asIdeal h).ge⟩

/-- A prime of `C` is the contraction of a prime of the closed fibre ring `C/𝔪_A C` exactly when
it lies over the closed point of `A`. -/
private theorem exists_comap_quotient_eq_iff
    {A C : Type u} [CommRing A] [CommRing C] [IsLocalRing A] [Algebra A C]
    (q : Ideal C) [q.IsPrime] :
    (∃ x : PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C)),
      x.asIdeal.comap (Ideal.Quotient.mk _) = q) ↔ q.comap (algebraMap A C) = maximalIdeal A := by
  simpa [PrimeSpectrum.ext_iff, closedPoint] using
    Set.ext_iff.mp (range_comap_quotient_closedFiber (A := A) (C := C)) ⟨q, inferInstance⟩

/-- The spectrum of the closed fibre ring of `Spec C ⟶ Spec A` is the closed fibre. -/
private noncomputable def closedFiberHomeomorph
    (A C : Type u) [CommRing A] [CommRing C] [IsLocalRing A] [Algebra A C] :
    PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C)) ≃ₜ
      (Spec.map (CommRingCat.ofHom (algebraMap A C))).fiber (closedPoint A) :=
  ((PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_comap_quotient_closedFiber)).trans
    (Scheme.Hom.fiberHomeo (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (closedPoint A)).symm

/-- `closedFiberHomeomorph` is the contraction map along `C → C/𝔪_A C`. -/
private theorem closedFiberHomeomorph_apply
    {A C : Type u} [CommRing A] [CommRing C] [IsLocalRing A] [Algebra A C]
    (x : PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C))) :
    (Spec.map (CommRingCat.ofHom (algebraMap A C))).fiberι (closedPoint A)
      (closedFiberHomeomorph A C x) =
        PrimeSpectrum.comap (Ideal.Quotient.mk _) x :=
  Scheme.Hom.fiberι_fiberHomeo_symm
    (Spec.map (CommRingCat.ofHom (algebraMap A C))) (closedPoint A) _

/-- **Stacks 053R** at `Spec C ⟶ Spec A` for the locally principal closed subscheme cut out by a
factor `c` of a nonzero element of `A`: the zero locus of `c` in the fibre over `s` is a union of
irreducible components of that fibre. -/
private theorem fiber_zeroLocus_eq_union_irreducibleComponents
    {A C : Type u} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [Algebra A C] [Algebra.FiniteType A C]
    (hinj : Function.Injective (algebraMap A C))
    (c d : C) (a : A) (ha : a ≠ 0) (heq : algebraMap A C a = c * d)
    (s : PrimeSpectrum A)
    (hdim : let f := Spec.map (CommRingCat.ofHom (algebraMap A C));
      topologicalKrullDim (f.fiber s) ≤
        topologicalKrullDim (f.fiber (genericPoint (Spec (CommRingCat.of A))))) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let Z := (f.fiberι s) ⁻¹' PrimeSpectrum.zeroLocus {c}
    Z = ⋃₀ {D | D ∈ irreducibleComponents (f.fiber s) ∧ D ⊆ Z} := by
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hinj
  have h3 : ringKrullDim (s.asIdeal.Fiber C) ≤ ringKrullDim ((⊥ : Ideal A).Fiber C) := by
    rw [← topologicalKrullDim_fiber_specMap_eq A C s,
      ← topologicalKrullDim_fiber_specMap_genericPoint_eq A C]
    exact hdim
  exact Stacks.Divisors.fiber_zeroLocus_specMap_eq_sUnion_irreducibleComponents c s
    (Stacks.Divisors.isUnit_fiber_bot_of_mul_eq_algebraMap c d a ha heq.symm) h3

/-- A prime of `C` over the closed point of `A` which contains a factor `c` of a nonzero element
of `A` contains a minimal prime over `𝔪_A C` containing `c`. -/
private theorem exists_minimalPrime_of_vertical
    {A C : Type u} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsLocalRing A] [Algebra A C] [Algebra.FiniteType A C]
    (hinj : Function.Injective (algebraMap A C))
    (c d : C) (a : A) (ha : a ≠ 0) (heq : algebraMap A C a = c * d)
    (q : Ideal C) [q.IsPrime] (hq : q.comap (algebraMap A C) = maximalIdeal A)
    (hc : c ∈ q)
    (hdim : let f := Spec.map (CommRingCat.ofHom (algebraMap A C));
      topologicalKrullDim (f.fiber (closedPoint A)) ≤
        topologicalKrullDim (f.fiber (genericPoint (Spec (CommRingCat.of A))))) :
    ∃ p ∈ ((maximalIdeal A).map (algebraMap A C)).minimalPrimes, p ≤ q ∧ c ∈ p := by
  let J := (maximalIdeal A).map (algebraMap A C)
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let e := closedFiberHomeomorph A C
  obtain ⟨x, hx⟩ := (exists_comap_quotient_eq_iff q).mpr hq
  have hex : f.fiberι (closedPoint A) (e x) = (⟨q, ‹_›⟩ : PrimeSpectrum C) :=
    (closedFiberHomeomorph_apply x).trans (PrimeSpectrum.ext hx)
  have hxc : e x ∈ (f.fiberι (closedPoint A)) ⁻¹' PrimeSpectrum.zeroLocus {c} := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact (congrArg PrimeSpectrum.asIdeal hex).symm ▸ hc
  rw [fiber_zeroLocus_eq_union_irreducibleComponents hinj c d a ha heq
    (closedPoint A) hdim] at hxc
  obtain ⟨D, ⟨hD, hDc⟩, hxD⟩ := hxc
  have hpre : e ⁻¹' D ∈ irreducibleComponents (PrimeSpectrum (C ⧸ J)) :=
    preimage_mem_irreducibleComponents hD e.isOpenEmbedding ⟨e x, hxD, x, rfl⟩
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hpre
  obtain ⟨r, hr, hDr⟩ := hpre
  change PrimeSpectrum.zeroLocus (r : Set (C ⧸ J)) = e ⁻¹' D at hDr
  let p := r.comap (Ideal.Quotient.mk J)
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨r, hr, rfl⟩
  · have hrx : r ≤ x.asIdeal := by
      change x ∈ PrimeSpectrum.zeroLocus (r : Set (C ⧸ J))
      rw [hDr]
      exact hxD
    exact (Ideal.comap_mono hrx).trans_eq hx
  · have hrD : e (⟨r, hr.1.1⟩ : PrimeSpectrum (C ⧸ J)) ∈ D := by
      change (⟨r, hr.1.1⟩ : PrimeSpectrum (C ⧸ J)) ∈ e ⁻¹' D
      rw [← hDr]
      exact fun _ hz ↦ hz
    have := (hDc hrD) (Set.mem_singleton c)
    rwa [closedFiberHomeomorph_apply] at this

/-- The same conclusion from a bound on the *local* dimension of the closed fibre at the prime,
obtained by replacing `C` by the principal localization that computes that local dimension. -/
private theorem exists_minimalPrime_of_vertical_of_local_dimension
    {A C : Type u} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsLocalRing A] [Algebra A C] [Algebra.FiniteType A C]
    (hinj : Function.Injective (algebraMap A C))
    (c d : C) (a : A) (ha : a ≠ 0) (heq : algebraMap A C a = c * d)
    (x : PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C)))
    (hc : Ideal.Quotient.mk _ c ∈ x.asIdeal)
    (hdim : TopologicalSpace.localKrullDim
      (PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C))) x ≤
        (Cardinal.toENat (Algebra.trdeg A C) : WithBot ℕ∞)) :
    ∃ p ∈ ((maximalIdeal A).map (algebraMap A C)).minimalPrimes,
      p ≤ x.asIdeal.comap (Ideal.Quotient.mk _) ∧ c ∈ p := by
  let J := (maximalIdeal A).map (algebraMap A C)
  obtain ⟨hbar, hhbar, hbound⟩ := exists_notMem_ringKrullDim_localization_le x
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective hbar
  let D := Localization.Away h
  let q := x.asIdeal.comap (Ideal.Quotient.mk J)
  have hne : h ≠ 0 := fun hz ↦ hhbar (by simp [hz])
  have hM : Submonoid.powers h ≤ nonZeroDivisors C :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hne)
  have : IsDomain D := IsLocalization.isDomain_of_le_nonZeroDivisors D hM
  have hCD : Function.Injective (algebraMap C D) := IsLocalization.injective D hM
  have hAD : Function.Injective (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A C D]
    exact hCD.comp hinj
  obtain ⟨y, hy⟩ : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈
      Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
    rw [PrimeSpectrum.localization_away_comap_range D h]
    exact hhbar
  have hqy : q = y.asIdeal.comap (algebraMap C D) :=
    (congrArg PrimeSpectrum.asIdeal hy).symm
  have hqA : q.comap (algebraMap A C) = maximalIdeal A :=
    (exists_comap_quotient_eq_iff q).mp ⟨x, rfl⟩
  let E := D ⧸ J.map (algebraMap C D)
  have hJD : J.map (algebraMap C D) = (maximalIdeal A).map (algebraMap A D) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization.Away (Ideal.Quotient.mk J h) E := by
    have := (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (C ⧸ J) (Submonoid.powers h)) E)
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
      Ideal.Quotient.algebraMap_eq] using this
  have hE : ringKrullDim E = ringKrullDim (Localization.Away (Ideal.Quotient.mk J h)) :=
    (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk J h))
      E (Localization.Away (Ideal.Quotient.mk J h))).toRingEquiv.ringKrullDim
  have htr : Algebra.trdeg A C = Algebra.trdeg A D :=
    trdeg_eq_of_isLocalization (Submonoid.powers h) hinj hM
  have hdimD : topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap A D))).fiber (closedPoint A)) ≤
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap A D))).fiber
          (genericPoint (Spec (CommRingCat.of A)))) := by
    rw [genericFiber_dimension_eq_trdeg hAD, ← htr,
      ← IsHomeomorph.topologicalKrullDim_eq _ (closedFiberHomeomorph A D).isHomeomorph,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hJD]
    exact hE.le.trans (hbound.trans hdim)
  obtain ⟨p, hp, hpy, hcp⟩ := exists_minimalPrime_of_vertical hAD
    (algebraMap C D c) (algebraMap C D d) a ha (by
      rw [IsScalarTower.algebraMap_apply A C D, heq, map_mul]) y.asIdeal (by
        rw [IsScalarTower.algebraMap_eq A C D, ← Ideal.comap_comap, ← hqy, hqA])
    (by
      have : c ∈ q := hc
      rw [hqy] at this
      exact this) hdimD
  refine ⟨p.comap (algebraMap C D), ?_, ?_, hcp⟩
  · rwa [← hJD, IsLocalization.minimalPrimes_map (Submonoid.powers h) D] at hp
  · exact (Ideal.comap_mono hpy).trans_eq hqy.symm

/-- A minimal prime over `𝔪_A C` contained in the prime `q` presenting a localization `B` of `C`
maps to a minimal prime over `𝔪_A B`, so an element avoiding the latter avoids the former. -/
private theorem notMem_minimalPrime_of_localization
    {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
    (q : Ideal C) [q.IsPrime] [IsLocalization.AtPrime B q]
    (I : Ideal A) (c : C)
    (hnot : ∀ p ∈ (I.map (algebraMap A B)).minimalPrimes, algebraMap C B c ∉ p)
    {p : Ideal C} (hp : p ∈ (I.map (algebraMap A C)).minimalPrimes) (hpq : p ≤ q) :
    c ∉ p := by
  have : p.IsPrime := hp.1.1
  have hpc : (p.map (algebraMap C B)).comap (algebraMap C B) = p :=
    Ideal.under_map_of_isLocalizationAtPrime (S := B) q hpq
  apply fun hc ↦ hnot (p.map (algebraMap C B)) ?_ (Ideal.mem_map_of_mem _ hc)
  rw [IsScalarTower.algebraMap_eq A C B, ← Ideal.map_map,
    IsLocalization.minimalPrimes_map q.primeCompl B]
  change (p.map (algebraMap C B)).comap (algebraMap C B) ∈
    (I.map (algebraMap A C)).minimalPrimes
  rwa [hpc]

/-- The local dimension of the closed fibre of `Spec C ⟶ Spec A` at the prime presenting a local
localization `B` is the dimension of the closed fibre of `B` plus the residue-field
transcendence degree. -/
private theorem closedFiber_localKrullDim_eq
    {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]
    [IsLocalHom (algebraMap A B)] [Algebra.FiniteType A C]
    (q : Ideal C) [q.IsPrime] [IsLocalization.AtPrime B q]
    (x : PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C)))
    (hx : x.asIdeal.comap (Ideal.Quotient.mk _) = q) :
    let := (ResidueField.map (algebraMap A B)).toAlgebra
    TopologicalSpace.localKrullDim
      (PrimeSpectrum (C ⧸ (maximalIdeal A).map (algebraMap A C))) x =
      ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) +
        (Cardinal.toENat (Algebra.trdeg (ResidueField A) (ResidueField B)) :
          WithBot ℕ∞) := by
  let := (ResidueField.map (algebraMap A B)).toAlgebra
  let J := (maximalIdeal A).map (algebraMap A C)
  let D := C ⧸ J
  let E := B ⧸ J.map (algebraMap C B)
  let k := ResidueField A
  have hJB : J.map (algebraMap C B) = (maximalIdeal A).map (algebraMap A B) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hle : J.map (algebraMap C B) ≤ maximalIdeal B := by
    rw [hJB, Ideal.map_le_iff_le_comap, maximalIdeal_comap]
  have : Nontrivial E := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hle)
  have : IsLocalRing E := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (J.map (algebraMap C B))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : Algebra k D := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : maximalIdeal A ≤ J.comap (algebraMap A C))
  have : IsScalarTower A k D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType k D := Algebra.FiniteType.of_restrictScalars_finiteType A k D
  let : Algebra k E := ((algebraMap D E).comp (algebraMap k D)).toAlgebra
  have : IsScalarTower k D E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsub : Algebra.algebraMapSubmonoid D q.primeCompl = x.asIdeal.primeCompl := by
    subst hx
    ext z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    constructor
    · rintro ⟨y, hy, hyz⟩ hz
      apply hy
      change Ideal.Quotient.mk J y ∈ x.asIdeal
      change Ideal.Quotient.mk J y = Ideal.Quotient.mk J z at hyz
      rwa [hyz]
    · intro hz
      exact ⟨z, hz, rfl⟩
  have : IsLocalization.AtPrime E x.asIdeal := by
    have h := (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid D q.primeCompl) E)
    rwa [hsub] at h
  let f : ResidueField B →ₐ[k] ResidueField E :=
    { ResidueField.map (Ideal.Quotient.mk (J.map (algebraMap C B))) with
      commutes' z := by
        obtain ⟨a, rfl⟩ := residue_surjective (R := A) z
        change ResidueField.map _ (ResidueField.map (algebraMap A B) (residue A a)) = _
        rw [ResidueField.map_residue, ResidueField.map_residue]
        change residue E (Ideal.Quotient.mk _ (algebraMap A B a)) =
          residue E (Ideal.Quotient.mk _ (algebraMap C B (algebraMap A C a)))
        rw [← IsScalarTower.algebraMap_apply] }
  have hf : Function.Bijective f := by
    refine ⟨f.injective, fun z ↦ ?_⟩
    obtain ⟨bbar, rfl⟩ := residue_surjective (R := E) z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
    exact ⟨residue B b, rfl⟩
  have ht := (AlgEquiv.ofBijective f hf).trdeg_eq
  have hd := IsLocalRing.localKrullDim_eq_ringKrullDim_add_trdeg k D E x.asIdeal
  rw [← ht] at hd
  change TopologicalSpace.localKrullDim (PrimeSpectrum D) x =
    ringKrullDim (B ⧸ J.map (algebraMap C B)) +
      (Cardinal.toENat (Algebra.trdeg k (ResidueField B)) : WithBot ℕ∞) at hd
  rwa [hJB] at hd

/-- **Stacks 053S.** Let `A ⊆ B` be an injective local homomorphism of local domains with `B`
essentially of finite type over `A`, and let `g ∈ 𝔪_B` lie in no minimal prime over `𝔪_A B`. If
`dim (B/𝔪_A B) + trdeg_{κ(𝔪_A)} κ(𝔪_B) = trdeg_A B`, then `A → B/gB` is injective, i.e. the
generic point of `Spec A` is in the image of `Spec (B/gB) → Spec A`. -/
@[stacks 053S]
public theorem injective_quotient_of_dimension_add_trdeg_eq
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (hB : IsEssentiallyOfFiniteType A B (algebraMap A B))
    (g : B) (hg : g ∈ maximalIdeal B)
    (hnot : ∀ q ∈ (Ideal.map (algebraMap A B) (maximalIdeal A)).minimalPrimes, g ∉ q)
    (hdim : letI := (ResidueField.map (algebraMap A B)).toAlgebra;
      ringKrullDim (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) +
        (Cardinal.toENat (Algebra.trdeg (ResidueField A) (ResidueField B)) :
          WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg A B) : WithBot ℕ∞)) :
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {g})).comp (algebraMap A B)) := by
  classical
  have : Algebra.EssFiniteType A B := essFiniteType_of_isEssentiallyOfFiniteType A B hB
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  by_contra ha0
  change Ideal.Quotient.mk (Ideal.span {g}) (algebraMap A B a) = 0 at ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  obtain ⟨C, hC, hft, hloc⟩ := exists_finiteType_subalgebra_localization
    (A := A) (B := B) {g, b}
  have : Algebra.FiniteType A C := hft
  let q := (maximalIdeal B).comap C.val
  have : IsLocalization.AtPrime B q := hloc
  let c : C := ⟨g, hC (by simp)⟩
  let d : C := ⟨b, hC (by simp)⟩
  have hAC : Function.Injective (algebraMap A C) := fun x y hxy ↦
    hinj (congrArg Subtype.val hxy)
  let J := (maximalIdeal A).map (algebraMap A C)
  obtain ⟨x, hxq⟩ := (exists_comap_quotient_eq_iff q).mpr (maximalIdeal_comap (algebraMap A B))
  have hM : q.primeCompl ≤ nonZeroDivisors C := fun z hz ↦
    mem_nonZeroDivisors_of_ne_zero (fun h ↦ hz (h ▸ q.zero_mem))
  have htr : Algebra.trdeg A C = Algebra.trdeg A B :=
    trdeg_eq_of_isLocalization q.primeCompl hAC hM
  have hlocal : TopologicalSpace.localKrullDim (PrimeSpectrum (C ⧸ J)) x ≤
      (Cardinal.toENat (Algebra.trdeg A C) : WithBot ℕ∞) := by
    rw [closedFiber_localKrullDim_eq (B := B) q x hxq, hdim, ← htr]
  obtain ⟨p, hp, hpq, hcp⟩ := exists_minimalPrime_of_vertical_of_local_dimension
    hAC c d a ha0 (Subtype.ext hb) x
    (show c ∈ x.asIdeal.comap (Ideal.Quotient.mk J) by rw [hxq]; exact hg) hlocal
  exact notMem_minimalPrime_of_localization q (maximalIdeal A) c hnot hp (hpq.trans_eq hxq) hcp

end IsLocalRing

end
