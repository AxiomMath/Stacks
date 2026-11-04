module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.Basic
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Reverse
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The nonvanishing locus of a homogeneous section on the invertible locus of `Proj`

Let `S` be a graded ring, `X = Proj(S)` and `d ≥ 1`. On the open `W_d ⊆ X` of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible`, where the twists `𝒪(nd)` are
invertible, a homogeneous element `f ∈ S_{nd}` gives a global section `s` of `𝒪(nd)`, and the
locus where `s` does not vanish is the standard open `D₊(f)`:

`X_s ∩ W_d = D₊(f) ∩ W_d`.

## The route

The equality is proved on `Proj(S)` itself rather than on the open subscheme `W_d`, which
removes every transport along the open immersion `W_d ↪ X`; the form of the source's statement,
on `W_d`, follows from this one and
`Stacks.SheafOfModules.preimage_nonvanishingLocus`. Since `W_d` is the union of the standard
opens `D₊(pq)` with `deg p = deg q + d`
(`Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_iSup_basicOpen_mul`), only one such
chart has to be treated, and the whole argument becomes algebra in the localization of `S` at
the homogeneous prime of the point.

Write `R = S₍x₎` for the degree-zero part of that localization. The two steps are:

* **The chart is free of rank one.** The degree-zero part of the localization of the shifted
  module `S(nd)` is the free `R`-module on the single fraction `(p/q)^n = p^{2n} / (pq)^n`
  (`degreeZeroModuleAt_eq_span_ratioFiber`). This is the stalk form of the trivialization of
  `𝒪(nd)` over `D₊(pq)` that `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioOverIsoUnit`
  produces at the level of sections.
* **The coefficient of `f`.** In that basis `f/1 = (f q^n / p^n) · (p/q)^n`, and the coefficient
  lies in the maximal ideal of the local ring `R` exactly when `f` lies in the homogeneous
  prime, because `p` and `q` do not (`degreeSectionRatio_mem_maximalIdeal_iff`). Over a local
  ring a free rank-one module has `r · v ∈ 𝔪 · M` exactly when `r ∈ 𝔪`.

The passage from the stalk of the twisting sheaf to the degree-zero localization is the
identification `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv`
of Stacks Tag 01M7, which is semilinear over `AlgebraicGeometry.Proj.stalkIso'`; membership in
`𝔪 · M` transports along any semilinear equivalence, and the germ of the section is `f/1` by
`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_stalk`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioFiber`: the value `(p/q)^n` of the
  trivializing section of `𝒪(nd)` at a point of `D₊(pq)`, as a single fraction.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.degreeSectionRatio`: the coefficient of `f/1`
  in that basis.

## Main results

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.degreeZeroModuleAt_eq_span_ratioFiber`: the
  degree-zero localization of `S(nd)` at a point of `D₊(pq)` is free of rank one on
  `ratioFiber`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.mk_mem_maximalIdeal_smul_degreeZeroModuleAt_iff`:
  `f/1` lies in `𝔪 · M₍x₎` exactly when `f` lies in the homogeneous prime of `x`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.mem_nonvanishingLocus_degreeSection_iff` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.nonvanishingLocus_degreeSection_inter`:
  **Stacks Tag 01MV**, pointwise and as an equality of subsets of `Proj(S)`.
* `nonvanishingLocus_degreeSection_inter_of_commonDegreeCover`: **Stacks Tag 01MW, clause (5)**,
  the same statement for an open of `Proj(S)` admitting a cover by standard opens of one common
  degree.

## Implementation notes

Neither `0 < d` nor `0 < n` is assumed: the argument never uses positivity.

The canonical module structure of Stacks Tag 01CB on the stalk of the twisting sheaf is supplied
with a `letI` rather than left to instance search. `AlgebraicGeometry.Proj` is not reducible, so
the sheaf of rings of the ringed space `Proj 𝒮` and the sheaf of rings over which the twisting
sheaves are modules — definitionally equal, and unified without trouble when they occur as
explicit arguments — are not seen to be equal at `instances` transparency, and the scalar action
on the stalk is therefore not found by instance search.

`left_notMem_of_mul_notMem` and `right_notMem_of_mul_notMem` are the same two facts as
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.left_mem_primeCompl` and `…right_mem_primeCompl`
of `StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Trivialization.lean`, stated with the
hypothesis `p * q ∉ 𝔭` rather than `x ∈ D₊(pq)`, which is the form every statement below needs;
the two pairs should be merged onto one hypothesis shape in a cleanup pass.

The module structure of the degree-zero homogeneous localization on the fibre
`ProjectiveSpectrum.Proj.ModuleFiber` is likewise not an instance: it is the one written into the
type of `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt`, and is repeated
as a `letI` wherever a statement needs it, exactly as in
`StacksFrontier/AlgebraicGeometry/ProjStalkGlobalSections/Stalk.lean`.

## References

* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Two pieces of commutative algebra -/

/-- Membership in `𝔪 · M` transports along an additive equivalence that is semilinear over an
isomorphism of the two local base rings. -/
private theorem mem_maximalIdeal_smul_top_iff_of_semilinear
    {A B M N : Type*} [CommRing A] [CommRing B] [instA : IsLocalRing A] [IsLocalRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (φ : A ≃+* B) (ε : M ≃+ N) (hε : ∀ (a : A) (m : M), ε (a • m) = φ a • ε m) (m : M) :
    m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      ε m ∈ IsLocalRing.maximalIdeal B • (⊤ : Submodule B N) := by
  have hmem : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ φ a ∈ IsLocalRing.maximalIdeal B := by
    intro a
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr ⟨fun h => h.map φ, fun h => by simpa using h.map φ.symm⟩
  have hsymm : ∀ (b : B) (n : N), ε.symm (b • n) = φ.symm b • ε.symm n := fun b n =>
    ε.injective (by rw [hε, ε.apply_symm_apply, ε.apply_symm_apply, φ.apply_symm_apply])
  refine ⟨fun hm => ?_, fun hn => ?_⟩
  · refine Submodule.smul_induction_on hm (fun a ha y _ => ?_) fun y z hy hz => ?_
    · rw [hε]
      exact Submodule.smul_mem_smul ((hmem a).mp ha) Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hy hz
  · have h : ε.symm (ε m) ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
      refine Submodule.smul_induction_on hn (fun b hb y _ => ?_) fun y z hy hz => ?_
      · rw [hsymm]
        exact Submodule.smul_mem_smul ((hmem (φ.symm b)).mpr (by simpa using hb))
          Submodule.mem_top
      · rw [map_add]
        exact Submodule.add_mem _ hy hz
    simpa using h

/-- In the free rank-one module `R · v` spanned by a unit `v` of a faithful `R`-algebra `K`, the
multiple `r · v` lies in `I · (R · v)` exactly when `r` lies in `I`. -/
private theorem mem_ideal_smul_span_singleton_iff
    {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (v : K) (hv : IsUnit v)
    (I : Ideal R) (r : R) :
    algebraMap R K r * v ∈ I • Submodule.span R ({v} : Set K) ↔ r ∈ I := by
  rw [Submodule.mem_smul_span_singleton]
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun hr => ⟨r, hr, Algebra.smul_def r v⟩⟩
  rw [Algebra.smul_def] at h
  obtain rfl := hinj (hv.mul_left_inj.mp h)
  exact hy

/-! ### The degree-zero localization on a chart of the invertible locus -/

section Chart

variable {p q : S} {e d : ℕ}

/-- `p` does not lie in a homogeneous prime that misses `pq`. -/
theorem left_notMem_of_mul_notMem {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) : p ∉ x.asHomogeneousIdeal.toIdeal :=
  fun hp => hx (Ideal.mul_mem_right q _ hp)

/-- `q` does not lie in a homogeneous prime that misses `pq`. -/
theorem right_notMem_of_mul_notMem {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) : q ∉ x.asHomogeneousIdeal.toIdeal :=
  fun hq => hx (Ideal.mul_mem_left _ p hq)

/-- The value at a point `x` of `D₊(pq)` of the trivializing section `(p/q)^n` of `𝒪(nd)`, for
`p` homogeneous of degree `e + d` and `q` homogeneous of degree `e`, written as the single
fraction `p^{2n} / (pq)^n` of the localization of `S` at the homogeneous prime of `x`. -/
noncomputable def ratioFiber (n : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x :=
  LocalizedModule.mk (p ^ (2 * n))
    ⟨(p * q) ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx n⟩

/-- The trivializing value is a unit of the localization: that is what the standard open
`D₊(pq)` is for. -/
theorem isUnit_ratioFiber (n : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    IsUnit (ratioFiber 𝒮 n hx :
      Localization x.asHomogeneousIdeal.toIdeal.primeCompl) := by
  show IsUnit (Localization.mk (p ^ (2 * n))
    ⟨(p * q) ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx n⟩)
  rw [Localization.mk_eq_mk']
  exact (IsLocalization.AtPrime.isUnit_mk'_iff
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) x.asHomogeneousIdeal.toIdeal _ _).2
    (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (left_notMem_of_mul_notMem 𝒮 hx) (2 * n))

/-- The fraction `m / s` of the localization is `(m q^n / (s p^n)) · (p/q)^n`. -/
private theorem mk_eq_mk_smul_ratioFiber (n : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) (m : S)
    (s : x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hden : s.1 * p ^ n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (LocalizedModule.mk m s : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      (Localization.mk (m * q ^ n) ⟨s.1 * p ^ n, hden⟩ :
        Localization x.asHomogeneousIdeal.toIdeal.primeCompl) • ratioFiber 𝒮 n hx := by
  have hc : p ^ (2 * n) * q ^ n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.mul_mem _
      (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (left_notMem_of_mul_notMem 𝒮 hx) (2 * n))
      (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (right_notMem_of_mul_notMem 𝒮 hx) n)
  rw [ratioFiber, LocalizedModule.mk_smul_mk]
  have hnum : (p ^ (2 * n) * q ^ n) • m = (m * q ^ n) • p ^ (2 * n) := by
    simp only [smul_eq_mul]
    ring
  have hden : s * ⟨_, hc⟩ = (⟨s.1 * p ^ n, hden⟩ :
      x.asHomogeneousIdeal.toIdeal.primeCompl) *
        ⟨(p * q) ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx n⟩ :=
    Subtype.ext (by simp only [Submonoid.coe_mul]; ring)
  calc (LocalizedModule.mk m s : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x)
      = LocalizedModule.mk ((p ^ (2 * n) * q ^ n) • m) (s * ⟨_, hc⟩) :=
        (LocalizedModule.mk_cancel_common_right s ⟨_, hc⟩ m).symm
    _ = _ := by rw [hnum, hden]

/-- **The degree-zero localization of `S(nd)` at a point of `D₊(pq)` is free of rank one**, on
the trivializing value `(p/q)^n`. For `p` of degree `e + d` and `q` of degree `e` this is the
stalk form of the trivialization of `𝒪(nd)` over `D₊(pq)` of Stacks Tag 01MU. -/
theorem degreeZeroModuleAt_eq_span_ratioFiber (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) (n : ℕ)
    {x : ProjectiveSpectrum.top 𝒮} (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x =
      Submodule.span (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        {ratioFiber 𝒮 n hx} := by
  let _ : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  have ha := left_notMem_of_mul_notMem 𝒮 hx
  have hb := right_notMem_of_mul_notMem 𝒮 hx
  have hqpow : (p * q) ^ n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
    x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx n
  have hv : ratioFiber 𝒮 n hx ∈
      degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x := by
    refine Submodule.subset_span ⟨n * (2 * e + d), p ^ (2 * n), ⟨(p * q) ^ n, hqpow⟩, ?_, ?_, rfl⟩
    · have hpow : p ^ (2 * n) ∈ 𝒮 (2 * n * (e + d)) := by
        simpa [nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          SetLike.pow_mem_graded (A := 𝒮) (2 * n) hp
      show p ^ (2 * n) ∈
        integerGrading 𝒮 (((n * (2 * e + d) : ℕ) : ℤ) + ((n * d : ℕ) : ℤ))
      rw [show (((n * (2 * e + d) : ℕ) : ℤ) + ((n * d : ℕ) : ℤ)) = ((2 * n * (e + d) : ℕ) : ℤ)
        by push_cast; ring, integerGrading_natCast]
      simpa only [mem_homogeneousSubmodule] using hpow
    · have hpq : p * q ∈ 𝒮 (2 * e + d) := by
        have h := SetLike.mul_mem_graded hp hq
        rwa [show e + d + e = 2 * e + d by omega] at h
      simpa [nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        SetLike.pow_mem_graded n hpq
  refine le_antisymm (fun z hz => ?_)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv))
  change z ∈ Submodule.span (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    {z | ∃ (j : ℕ) (m : S) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
      m ∈ twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ) (j : ℤ) ∧
        (s : S) ∈ 𝒮 j ∧ z = LocalizedModule.mk m s} at hz
  refine Submodule.span_induction
    (p := fun y _ => y ∈ Submodule.span
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      {ratioFiber 𝒮 n hx})
    ?_ (Submodule.zero_mem _) (fun _ _ _ _ iy iz => Submodule.add_mem _ iy iz)
    (fun r _ _ iy => Submodule.smul_mem _ r iy) hz
  rintro y ⟨j, m, s, hm, hs, rfl⟩
  have hmS : m ∈ 𝒮 (j + n * d) := by
    change m ∈ integerGrading 𝒮 ((j : ℤ) + ((n * d : ℕ) : ℤ)) at hm
    rw [show ((j : ℤ) + ((n * d : ℕ) : ℤ)) = ((j + n * d : ℕ) : ℤ) by push_cast; ring,
      integerGrading_natCast] at hm
    simpa only [mem_homogeneousSubmodule] using hm
  have hnum : m * q ^ n ∈ 𝒮 (j + n * (e + d)) := by
    have h := SetLike.mul_mem_graded hmS (SetLike.pow_mem_graded n hq)
    rwa [smul_eq_mul, show j + n * d + n * e = j + n * (e + d) by ring] at h
  have hdenG : s.1 * p ^ n ∈ 𝒮 (j + n * (e + d)) := by
    have hppow : p ^ n ∈ 𝒮 (n * (e + d)) := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded n hp
    simpa only [Nat.add_assoc] using SetLike.mul_mem_graded hs hppow
  have hdenMem : s.1 * p ^ n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.mul_mem _ s.2 (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha n)
  set rr : HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal :=
    HomogeneousLocalization.mk
      ⟨j + n * (e + d), ⟨m * q ^ n, hnum⟩, ⟨s.1 * p ^ n, hdenG⟩, hdenMem⟩ with hrr
  have hgen : LocalizedModule.mk m s = rr • ratioFiber 𝒮 n hx := by
    change _ = HomogeneousLocalization.val rr • ratioFiber 𝒮 n hx
    rw [hrr, HomogeneousLocalization.val_mk]
    exact mk_eq_mk_smul_ratioFiber 𝒮 n hx m s hdenMem
  rw [hgen]
  exact Submodule.smul_mem _ rr (Submodule.subset_span (Set.mem_singleton _))

/-- The coefficient of `f/1` in the basis `(p/q)^n` of the degree-zero localization of `S(nd)`:
the degree-zero fraction `f q^n / p^n`. -/
noncomputable def degreeSectionRatio (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n : ℕ}
    (f : 𝒮 (n * d)) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    ⟨n * (e + d),
      ⟨(f : S) * q ^ n, by
        have h := SetLike.mul_mem_graded f.2 (SetLike.pow_mem_graded n hq)
        rwa [smul_eq_mul, show n * d + n * e = n * (e + d) by ring] at h⟩,
      ⟨p ^ n, by
        have h := SetLike.pow_mem_graded (A := 𝒮) n hp
        rwa [smul_eq_mul] at h⟩,
      x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
        (left_notMem_of_mul_notMem 𝒮 hx) n⟩

/-- The coefficient of `f/1` is a nonunit of the local ring `S₍x₎` exactly when `f` lies in the
homogeneous prime of `x`: its denominator `p^n` and the factor `q^n` of its numerator do not. -/
theorem degreeSectionRatio_mem_maximalIdeal_iff (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n : ℕ}
    (f : 𝒮 (n * d)) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    degreeSectionRatio 𝒮 hp hq f hx ∈ IsLocalRing.maximalIdeal
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal) ↔
      (f : S) ∈ x.asHomogeneousIdeal.toIdeal := by
  have ha := left_notMem_of_mul_notMem 𝒮 hx
  have hb := right_notMem_of_mul_notMem 𝒮 hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine (not_congr (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒮
    x.asHomogeneousIdeal.toIdeal (degreeSectionRatio 𝒮 hp hq f hx))).symm.trans ?_
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  show (Localization.mk ((f : S) * q ^ n)
      ⟨p ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha n⟩ :
        Localization x.asHomogeneousIdeal.toIdeal.primeCompl) ∈
    IsLocalRing.maximalIdeal (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) ↔ _
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.mk'_mem_maximal_iff
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) x.asHomogeneousIdeal.toIdeal
    ((f : S) * q ^ n) ⟨p ^ n, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha n⟩]
  exact ⟨fun h => (x.isPrime.mem_or_mem h).resolve_right
    (x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hb n), Ideal.mul_mem_right (q ^ n) _⟩

/-- The expansion of `f/1` in the basis `(p/q)^n`. -/
theorem mk_eq_degreeSectionRatio_smul_ratioFiber (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) {n : ℕ}
    (f : 𝒮 (n * d)) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    (LocalizedModule.mk (f : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      HomogeneousLocalization.val (degreeSectionRatio 𝒮 hp hq f hx) •
        ratioFiber 𝒮 n hx := by
  have ha := left_notMem_of_mul_notMem 𝒮 hx
  have hb := right_notMem_of_mul_notMem 𝒮 hx
  have hppow : (1 : x.asHomogeneousIdeal.toIdeal.primeCompl).1 * p ^ n ∈
      x.asHomogeneousIdeal.toIdeal.primeCompl := by
    simpa using x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ha n
  change _ = HomogeneousLocalization.val (degreeSectionRatio 𝒮 hp hq f hx) • ratioFiber 𝒮 n hx
  rw [degreeSectionRatio, HomogeneousLocalization.val_mk]
  simpa using mk_eq_mk_smul_ratioFiber 𝒮 n hx (f : S) 1 hppow

/-- **`f/1` lies in `𝔪 · M₍x₎` exactly when `f` lies in the homogeneous prime of `x`**, for `x`
in a chart `D₊(pq)` of the invertible locus. This is the algebraic heart of Stacks Tag 01MV. -/
theorem mk_mem_maximalIdeal_smul_degreeZeroModuleAt_iff (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e)
    {n : ℕ} (f : 𝒮 (n * d)) {x : ProjectiveSpectrum.top 𝒮}
    (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    (LocalizedModule.mk (f : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) ∈
      IsLocalRing.maximalIdeal
          (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal) •
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x ↔
      (f : S) ∈ x.asHomogeneousIdeal.toIdeal := by
  let _ : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  have hinj : Function.Injective (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)) := fun z z' hz =>
    HomogeneousLocalization.val_injective (𝒜 := 𝒮)
      (x := x.asHomogeneousIdeal.toIdeal.primeCompl) hz
  rw [degreeZeroModuleAt_eq_span_ratioFiber 𝒮 hp hq n hx,
    mk_eq_degreeSectionRatio_smul_ratioFiber 𝒮 hp hq f hx,
    show HomogeneousLocalization.val (degreeSectionRatio 𝒮 hp hq f hx) • ratioFiber 𝒮 n hx =
      algebraMap (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
          (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
          (degreeSectionRatio 𝒮 hp hq f hx) * ratioFiber 𝒮 n hx from rfl,
    mem_ideal_smul_span_singleton_iff hinj _ (isUnit_ratioFiber 𝒮 n hx) _ _]
  exact degreeSectionRatio_mem_maximalIdeal_iff 𝒮 hp hq f hx

end Chart

/-! ### Stacks Tag 01MV -/

section Locus

variable {p q : S} {e d : ℕ}

/-- **Stacks Tag 01MV on a chart.** At a point of a standard open `D₊(pq)` with
`deg p = deg q + d`, the global section of `𝒪(nd)` attached to `f ∈ S_{nd}` is nonvanishing
exactly on `D₊(f)`. -/
theorem mem_nonvanishingLocus_degreeSection_iff_of_mem_basicOpen_mul
    (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e) (n : ℕ) (f : 𝒮 (n * d))
    {x : ProjectiveSpectrum.top 𝒮} (hx : p * q ∉ x.asHomogeneousIdeal.toIdeal) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
        (sectionsOfTop _ (degreeSection 𝒮 (n * d) f)) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) := by
  let _ : Module
      (ringStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace x)
      (grpStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x) :=
    stalkModule (AlgebraicGeometry.Proj 𝒮).toRingedSpace _ x
  have hsemi : ∀ (a : ringStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace x)
      (z : grpStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x),
      associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x (a • z) =
        AlgebraicGeometry.Proj.stalkIso' 𝒮 x a •
          associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x z := by
    intro a z
    obtain ⟨U, hxU, s, rfl⟩ := exists_grpGerm_eq (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x z
    obtain ⟨V, hxV, r, hr⟩ :=
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.exists_germ_eq a
    have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    have h1 : ringGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace x (U ⊓ V) hxW
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.map
          (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r) = a :=
      (TopCat.Presheaf.germ_res_apply (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hxW r).trans hr
    have h2 := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
      (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val.presheaf
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hxW s
    have hcombine :
        a • grpGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x U hxU s =
          grpGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace
            (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x (U ⊓ V) hxW
            (((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.map
                (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r) •
              ((twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val.map
                (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)) :=
      ((congrArg (fun uu : ringStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace x =>
            uu • grpGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace
              (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x (U ⊓ V) hxW
              ((twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val.map
                (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)) h1).trans
        (congrArg (fun vv : grpStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace
            (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x => a • vv) h2)).symm.trans
        (stalkModule_germ_smul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x (U ⊓ V) hxW _ _).symm
    refine ((congrArg (fun ww => associatedModuleSheafStalkEquiv 𝒮
        (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x ww) hcombine).trans
      (associatedModuleSheafStalkEquiv_germ_smul 𝒮
        (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x (U ⊓ V) hxW _ _)).trans ?_
    exact (congrArg (fun uu : HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal =>
        uu • associatedModuleSheafStalkEquiv 𝒮
          (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x
          (grpGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace
            (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x (U ⊓ V) hxW
            ((twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val.map
              (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)))
      (congrArg (AlgebraicGeometry.Proj.stalkIso' 𝒮 x) h1)).trans
      (congrArg (fun ww => AlgebraicGeometry.Proj.stalkIso' 𝒮 x a •
        associatedModuleSheafStalkEquiv 𝒮
          (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x ww) h2)
  have hvalue : ((associatedModuleSheafStalkEquiv 𝒮
        (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x
        (grpGerm (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x ⊤ (Opens.mem_top x)
          (degreeSection 𝒮 (n * d) f)) :
          degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      LocalizedModule.mk (f : S) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_stalk 𝒮 (n * d) f x
  refine Iff.trans (mem_nonvanishingLocus_sectionsOfTop_iff
    (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace) (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
    (degreeSection 𝒮 (n * d) f) x) ?_
  refine Iff.trans ?_ (AlgebraicGeometry.Proj.mem_basicOpen 𝒮 (f : S) x).symm
  refine not_congr (Iff.trans (mem_maximalIdeal_smul_top_iff_of_semilinear
    (A := ringStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace x)
    (instA := (AlgebraicGeometry.Proj 𝒮).isLocalRing x)
    (B := HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    (M := grpStalk (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)).val x)
    (N := degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x)
    (AlgebraicGeometry.Proj.stalkIso' 𝒮 x)
    (associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x)
    hsemi _) ?_)
  refine Iff.trans (Submodule.mem_smul_top_iff _ _ _) (Iff.trans (Iff.of_eq (congrArg
    (fun ww : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x => ww ∈
      IsLocalRing.maximalIdeal (HomogeneousLocalization.AtPrime 𝒮
          x.asHomogeneousIdeal.toIdeal) •
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 ((n * d : ℕ) : ℤ)) x) hvalue))
    (mk_mem_maximalIdeal_smul_degreeZeroModuleAt_iff 𝒮 hp hq f hx))

/-- **Stacks Tag 01MV, pointwise.** At a point of the invertible locus `W_d`, the global section
of `𝒪(nd)` attached to a homogeneous element `f` of degree `nd` is nonvanishing exactly on the
standard open `D₊(f)`. -/
theorem mem_nonvanishingLocus_degreeSection_iff (d n : ℕ) (f : 𝒮 (n * d))
    {x : ProjectiveSpectrum.top 𝒮} (hx : x ∈ whereInvertible 𝒮 d) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
        (sectionsOfTop _ (degreeSection 𝒮 (n * d) f)) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) := by
  rw [GoodOpenClose.whereInvertible_eq_iSup_basicOpen_mul 𝒮 d] at hx
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hk
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ha
  exact mem_nonvanishingLocus_degreeSection_iff_of_mem_basicOpen_mul 𝒮 a.2 b.2 n f
    ((AlgebraicGeometry.Proj.mem_basicOpen 𝒮 ((a : S) * (b : S)) x).mp hb)

/-- **Stacks Tag 01MV.** Let `S` be a graded ring, `X = Proj(S)`, `d ≥ 1`, `n ≥ 1` and
`f ∈ S_{nd}`. Let `s` be the global section of `𝒪(nd)` attached to `f`. Then, on the open `W_d`
where the `d`-divisible twists are invertible, the nonvanishing locus of `s` is the standard
open `D₊(f)`:

`X_s ∩ W_d = D₊(f) ∩ W_d`.

This is stated on `Proj(S)` rather than on the open subscheme `W_d`, which is strictly stronger
than the form of the source: the statement there is the image of this one under
`Stacks.SheafOfModules.preimage_nonvanishingLocus`. No positivity of `d` or `n` is needed. -/
@[stacks 01MV]
theorem nonvanishingLocus_degreeSection_inter (d n : ℕ) (f : 𝒮 (n * d)) :
    Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
          (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
          (sectionsOfTop _ (degreeSection 𝒮 (n * d) f)) ∩
        (whereInvertible 𝒮 d : Set ↥(AlgebraicGeometry.Proj 𝒮)) =
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) : Set ↥(AlgebraicGeometry.Proj 𝒮)) ∩
        (whereInvertible 𝒮 d : Set ↥(AlgebraicGeometry.Proj 𝒮)) := by
  ext x
  exact and_congr_left fun hx => mem_nonvanishingLocus_degreeSection_iff 𝒮 d n f hx

/-- **Stacks Tag 01MW (5).** Let `Y` be an open of `Proj(S)` covered by standard opens
`D₊(f_i)` with the `f_i` homogeneous of one common degree `d`, let `n ≥ 1` and let
`f ∈ S_{nd}`. Then the global section of `𝒪(nd)` attached to `f` is nonvanishing on `Y`
exactly on `D₊(f) ∩ Y`.

As for Stacks Tag 01MV, the nonvanishing locus is taken on `Proj(S)` and intersected with `Y`,
rather than taken on the open subscheme `Y` after restricting the section; the two agree by
`Stacks.SheafOfModules.preimage_nonvanishingLocus`. -/
theorem nonvanishingLocus_degreeSection_inter_of_commonDegreeCover
    (Y : (AlgebraicGeometry.Proj 𝒮).Opens)
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒮 Y) (n : ℕ) (f : 𝒮 (n * C.degree)) :
    Stacks.SheafOfModules.nonvanishingLocus
          (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
          (twistingSheaf 𝒮 ((n * C.degree : ℕ) : ℤ))
          (sectionsOfTop _ (degreeSection 𝒮 (n * C.degree) f)) ∩
        (Y : Set ↥(AlgebraicGeometry.Proj 𝒮)) =
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S) : Set ↥(AlgebraicGeometry.Proj 𝒮)) ∩
        (Y : Set ↥(AlgebraicGeometry.Proj 𝒮)) := by
  ext z
  exact and_congr_left fun hz => mem_nonvanishingLocus_degreeSection_iff 𝒮 C.degree n f
    (CommonDegreeTwist.le_whereInvertible 𝒮 Y C hz)

end Locus

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

end
