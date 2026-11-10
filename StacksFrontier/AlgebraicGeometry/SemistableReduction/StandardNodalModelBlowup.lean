module

public import StacksFrontier.AlgebraicGeometry.Blowup.DerivedPullbackAnnihilation
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalOnSource
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModel
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.RingTheory.NodalChart.Blowup
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The blowup of the standard nodal model in its singular point

Let `R` be a commutative ring, `π : R` nonzero, `n ≥ 2`, and let `X = Spec A` be the standard
nodal model `A = R[x, y]/(xy - πⁿ)` over `S = Spec R` of
`StacksFrontier/AlgebraicGeometry/SemistableReduction/StandardNodalModel.lean`. Its singular point
is cut out by `𝔪 = (π, x, y)`. This file builds the blowup `b : X' ⟶ X` of `X` in `𝔪` *as a
morphism of schemes*, covers `X'` by the three affine charts whose algebras
`A[𝔪/π]`, `A[𝔪/x]`, `A[𝔪/y]` are identified in `StacksFrontier/RingTheory/NodalChart/Blowup.lean`,
and records the two facts of [Stacks, Tag 0CDC] about the result:

* `X' ⟶ S` is again at-worst-nodal of relative dimension one;
* the central chart is an affine open of `X'` which is, over `S`, the standard nodal model with
  the exponent lowered by two — the neighbourhood of the one point at which `X'` can fail to be
  regular, the two outer charts being regular by
  `Stacks.isRegular_spec_nodalXChart` and `Stacks.isRegular_spec_nodalYChart`.

## Main definitions

* `Stacks.nodalCenterGen` — the three generators `π`, `x`, `y` of `𝔪`, indexed by `Fin 3`.
* `Stacks.nodalModelBlowup` — the blowup `X'` of `X` in `𝔪`.
* `Stacks.nodalModelBlowupHom` — the blowup morphism `b : X' ⟶ X`.
* `Stacks.nodalModelBlowupToBase` — the composite `X' ⟶ S`.
* `Stacks.nodalModelBlowupChart` — the three affine charts
  `Spec A[𝔪/π]`, `Spec A[𝔪/x]`, `Spec A[𝔪/y]` of `X'`.

## Main results

* `Stacks.iSup_opensRange_nodalModelBlowupChart` — the three charts cover `X'`.
* `Stacks.nodalModelBlowupChart_comp_toBase` — the chart at a generator lies over `S` by `Spec`
  of the structure map of its blowup algebra.
* `Stacks.isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupToBase` — `X' ⟶ S` is
  at-worst-nodal of relative dimension one.
* `Stacks.exists_isOpenImmersion_nodalModel_sub_two` — the central chart is an affine open of
  `X'` which over `S` is the standard nodal model of exponent `n - 2`.
* `Stacks.isRegularRing_nodalChartRing_one` and `Stacks.isRegular_nodalModel_zero` — the
  exponent zero model is regular over a regular base.
* `Stacks.isRegular_nodalModelBlowup` — `X'` is regular as soon as the nodal chart rings of
  parameters `π^(n-2)` and `π` are.
* `Stacks.isRegular_nodalModelBlowup_of_le_three` — for `2 ≤ n ≤ 3`, where `⌊n/2⌋ = 1`, the
  single blowup already resolves the singularity.

## Implementation notes

The blowup is `Stacks.Blowup.blowUpSpec 𝔪`, the `Proj` of the Rees algebra of `𝔪`, with its
structure morphism `Stacks.Blowup.toSpec 𝔪`; that this agrees with the blowup of the ideal
sheaf `𝔪` defines on `Spec A` is `Stacks.Blowup.nonempty_over_iso_blowUpToBase` (Tag 0804). The
charts are `Stacks.Blowup.blowUpSpecChart`, whose source is `affineBlowup 𝔪 a`, and they already
cover once `a` ranges over a generating family
(`Stacks.Blowup.iSup_opensRange_specAffineBlowupι_of_eq_span`); the generating family here is the
three elements `π`, `x`, `y` of the definition of `Stacks.nodalCenter`.

The chart algebras of `StacksFrontier/RingTheory/NodalChart/Blowup.lean` are stated for an abstract
localization `S` away from the denominator, as `affineBlowupAlgebra 𝔪 a S`; the realization the
scheme charts use is `affineBlowup 𝔪 a` inside `Localization.Away a`, and the two are the same
subalgebra by `affineBlowup_eq_affineBlowupAlgebra`. Everything in this file is therefore the
transport of a chart identification along `Subalgebra.equivOfEq`, followed by `Spec`.

Being at-worst-nodal of relative dimension one is étale local on the source
(`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering`, Tag 0C5D), and
an open immersion is étale, so the three charts suffice: each of them lies over `S` by `Spec` of
the structure map of a nodal chart ring, which is at-worst-nodal of relative dimension one for
every parameter by `Stacks.isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing`. For the
central chart the parameter is `π^(n-2)` and for the two outer ones it is `π`.

Regularity of `X'` is read off the same three-chart cover through the fourth item of
`AlgebraicGeometry.isRegular_tfae_cover`, each chart being the spectrum of a chart algebra
transported along `AlgebraicGeometry.IsRegular.of_iso`. For `n = 2` the central chart has
parameter `π⁰ = 1`, where regularity is new: the chart ring is a smooth `R`-algebra
(`Stacks.smooth_nodalChartRing_one`) and a smooth algebra over a regular ring is regular
(`Algebra.isRegularRing_of_smooth`, Tag 07NF).

The chain of blowups `X_{⌊n/2⌋} → … → X₀ = X` is therefore complete for `n ≤ 3`, where it has
length `⌊n/2⌋ ≤ 1`. For `n ≥ 4` it is *not* treated here: the second blowup is taken at a closed
point of the non-affine scheme `X'`, which needs the blowup of a scheme in an ideal sheaf
supported in one affine chart to be glued from the blowup of that chart and an isomorphism off
the centre. The two halves exist separately — `Stacks.Blowup.isPullback_blowUpChart` identifies
the part of a blowup over an affine open of the base, and
`Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData` says the blowup is
an isomorphism over any open disjoint from the centre — but they are not yet joined into a
statement about a blowup at a closed point of a scheme covered by nodal charts.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 0C5D](https://stacks.math.columbia.edu/tag/0C5D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-! ### The generators of the centre -/

/-- The three generators `π`, `x`, `y` of the centre `𝔪 = (π, x, y)` of the blowup resolving the
standard nodal model, indexed by `Fin 3`. -/
public def nodalCenterGen (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Fin 3 → nodalChartRing R (π ^ n) :=
  ![algebraMap R (nodalChartRing R (π ^ n)) π, nodalGen R (π ^ n) 0, nodalGen R (π ^ n) 1]

@[simp] public theorem nodalCenterGen_zero (π : R) (n : ℕ) :
    nodalCenterGen R π n 0 = algebraMap R (nodalChartRing R (π ^ n)) π := rfl

@[simp] public theorem nodalCenterGen_one (π : R) (n : ℕ) :
    nodalCenterGen R π n 1 = nodalGen R (π ^ n) 0 := rfl

@[simp] public theorem nodalCenterGen_two (π : R) (n : ℕ) :
    nodalCenterGen R π n 2 = nodalGen R (π ^ n) 1 := rfl

/-- Each of the three generators `π`, `x`, `y` lies in the centre `𝔪 = (π, x, y)`. -/
public theorem nodalCenterGen_mem (π : R) (n : ℕ) (i : Fin 3) :
    nodalCenterGen R π n i ∈ nodalCenter R π (π ^ n) := by
  fin_cases i
  · exact algebraMap_mem_nodalCenter π (π ^ n)
  · exact nodalGen_mem_nodalCenter π (π ^ n) 0
  · exact nodalGen_mem_nodalCenter π (π ^ n) 1

/-- The centre is spanned by the three generators `π`, `x`, `y`. -/
public theorem nodalCenter_eq_span_range_nodalCenterGen (π : R) (n : ℕ) :
    nodalCenter R π (π ^ n) = Ideal.span (Set.range (nodalCenterGen R π n)) := by
  refine congrArg Ideal.span ?_
  ext z
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-! ### The blowup and its charts -/

/-- **The blowup `X'` of the standard nodal model `X = Spec R[x, y]/(xy - πⁿ)` in the ideal
`𝔪 = (π, x, y)` of its singular point.** It is the `Proj` of the Rees algebra of `𝔪`; that this
is the blowup of the scheme `X` in the ideal sheaf attached to `𝔪` is
`Stacks.Blowup.nonempty_over_iso_blowUpToBase`. -/
@[stacks 0CDC "to ameliorate the situation in case n > 1 we consider the blowup b : X' → X of X \
in 𝔪: the scheme X'"]
public def nodalModelBlowup (R : Type u) [CommRing R] (π : R) (n : ℕ) : Scheme.{u} :=
  Blowup.blowUpSpec (nodalCenter R π (π ^ n))

/-- **The blowup morphism `b : X' ⟶ X` of the standard nodal model in `𝔪 = (π, x, y)`.** -/
@[stacks 0CDC "to ameliorate the situation in case n > 1 we consider the blowup b : X' → X of X \
in 𝔪: the morphism b"]
public def nodalModelBlowupHom (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    nodalModelBlowup R π n ⟶ nodalModel R π n :=
  Blowup.toSpec (nodalCenter R π (π ^ n))

/-- The structure morphism `X' ⟶ S = Spec R` of the blowup, the blowup morphism followed by the
structure morphism of the standard nodal model. -/
public def nodalModelBlowupToBase (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    nodalModelBlowup R π n ⟶ Spec (CommRingCat.of R) :=
  nodalModelBlowupHom R π n ≫ nodalModelHom R π n

/-- The affine chart of the blowup attached to one of the three generators of `𝔪`: the spectrum
of the affine blowup algebra `A[𝔪/π]`, `A[𝔪/x]` or `A[𝔪/y]`. -/
public def nodalModelBlowupChart (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 3) :
    Spec (CommRingCat.of (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i))) ⟶
      nodalModelBlowup R π n :=
  Blowup.blowUpSpecChart _ (nodalCenterGen R π n i) (nodalCenterGen_mem π n i)

/-- Each of the three charts of the blowup is an open immersion into `X'`. -/
public instance (π : R) (n : ℕ) (i : Fin 3) :
    IsOpenImmersion (nodalModelBlowupChart R π n i) :=
  inferInstanceAs (IsOpenImmersion
    (Blowup.blowUpSpecChart _ (nodalCenterGen R π n i) (nodalCenterGen_mem π n i)))

/-- **By construction `X'` is covered by three affine pieces, the spectra of the blowup algebras
`A[𝔪/π]`, `A[𝔪/x]` and `A[𝔪/y]`.** -/
@[stacks 0CDC "by construction X' is covered by three affine pieces corresponding to the blowup \
algebras A[𝔪/π], A[𝔪/x] and A[𝔪/y]"]
public theorem iSup_opensRange_nodalModelBlowupChart (π : R) (n : ℕ) :
    ⨆ i, (nodalModelBlowupChart R π n i).opensRange = ⊤ :=
  Blowup.iSup_opensRange_specAffineBlowupι_of_eq_span _ (nodalCenterGen_mem π n)
    (nodalCenter_eq_span_range_nodalCenterGen π n)

/-- Every point of `X'` lies in one of the three charts. -/
public theorem exists_mem_range_nodalModelBlowupChart (π : R) (n : ℕ)
    (z : nodalModelBlowup R π n) :
    ∃ i : Fin 3, z ∈ Set.range (nodalModelBlowupChart R π n i).base := by
  have hz : z ∈ ⨆ i, (nodalModelBlowupChart R π n i).opensRange := by
    rw [iSup_opensRange_nodalModelBlowupChart]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hz

/-- The structure morphism of the standard nodal model, with the scheme spelled out. -/
public theorem nodalModelHom_eq (π : R) (n : ℕ) :
    nodalModelHom R π n =
      Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R (π ^ n)))) := rfl

/-- **The chart `Spec A[𝔪/a]` lies over `X` by `Spec` of the structure map of its blowup
algebra.** -/
public theorem nodalModelBlowupChart_comp_hom (π : R) (n : ℕ) (i : Fin 3) :
    nodalModelBlowupChart R π n i ≫ nodalModelBlowupHom R π n =
      Spec.map (CommRingCat.ofHom (algebraMap (nodalChartRing R (π ^ n))
        (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)))) :=
  Blowup.blowUpSpecChart_toSpec _ (nodalCenterGen R π n i) (nodalCenterGen_mem π n i)

/-- **The chart `Spec A[𝔪/a]` lies over `S = Spec R` by `Spec` of the structure map of its
blowup algebra.** -/
public theorem nodalModelBlowupChart_comp_toBase (π : R) (n : ℕ) (i : Fin 3) :
    nodalModelBlowupChart R π n i ≫ nodalModelBlowupToBase R π n =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)))) := by
  have h : (algebraMap R
      (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)) : R →+* _) =
      (algebraMap (nodalChartRing R (π ^ n))
        (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i))).comp
        (algebraMap R (nodalChartRing R (π ^ n))) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [nodalModelBlowupToBase, ← Category.assoc, nodalModelBlowupChart_comp_hom, h,
    CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

/-! ### The chart algebras, in the realization the charts use -/

/-- The chart algebra `A[𝔪/x]` of the blowup scheme is the one identified in
`Stacks.nodalXChart_equiv`. -/
public theorem affineBlowup_nodalCenterGen_one_eq (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 1) =
      nodalXChart π n (Localization.Away (nodalGen R (π ^ n) 0)) :=
  affineBlowup_eq_affineBlowupAlgebra _ _

/-- The chart algebra `A[𝔪/y]` of the blowup scheme is the one identified in
`Stacks.nodalYChart_equiv`. -/
public theorem affineBlowup_nodalCenterGen_two_eq (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 2) =
      nodalYChart π n (Localization.Away (nodalGen R (π ^ n) 1)) :=
  affineBlowup_eq_affineBlowupAlgebra _ _

/-- The chart algebra `A[𝔪/π]` of the blowup scheme is the one identified in
`Stacks.nodalCentralChart_equiv`. -/
public theorem affineBlowup_nodalCenterGen_zero_eq (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 0) =
      nodalCentralChart π n
        (Localization.Away (algebraMap R (nodalChartRing R (π ^ n)) π)) :=
  affineBlowup_eq_affineBlowupAlgebra _ _

section Identifications

/-- An algebra isomorphism over an intermediate ring commutes with the structure map of the
bottom ring. -/
private theorem algEquiv_algebraMap_base {A' M N : Type u} [CommRing A'] [Algebra R A']
    [CommRing M] [CommRing N] [Algebra A' M] [Algebra A' N] [Algebra R M] [Algebra R N]
    [IsScalarTower R A' M] [IsScalarTower R A' N] (φ : M ≃ₐ[A'] N) (r : R) :
    φ (algebraMap R M r) = algebraMap R N r := by
  rw [IsScalarTower.algebraMap_apply R A' M, IsScalarTower.algebraMap_apply R A' N, φ.commutes]

/-- Transporting a chart identification along an isomorphism of chart algebras over the chart
ring preserves its compatibility with the structure map of the base. -/
private theorem ringEquiv_trans_algebraMap {A' M N T : Type u} [CommRing A'] [Algebra R A']
    [CommRing M] [CommRing N] [CommRing T] [Algebra A' M] [Algebra A' N] [Algebra R M]
    [Algebra R N] [Algebra R T] [IsScalarTower R A' M] [IsScalarTower R A' N]
    (φ : M ≃ₐ[A'] N) (e : N ≃+* T)
    (he : ∀ r : R, e (algebraMap A' N (algebraMap R A' r)) = algebraMap R T r) (r : R) :
    (φ.toRingEquiv.trans e) (algebraMap R M r) = algebraMap R T r := by
  change e (φ (algebraMap R M r)) = algebraMap R T r
  rw [algEquiv_algebraMap_base φ r, IsScalarTower.algebraMap_apply R A' N r]
  exact he r

/-- `Spec` of an `R`-algebra isomorphism onto a nodal chart ring turns the structure morphism of
the source into the structure morphism of the nodal chart ring, up to an isomorphism of the
source. -/
private theorem specMap_algebraMap_eq_of_ringEquiv {T B : Type u} [CommRing T] [CommRing B]
    [Algebra R T] [Algebra R B] (e : T ≃+* B)
    (he : ∀ r : R, e (algebraMap R T r) = algebraMap R B r) :
    Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  have h : (algebraMap R T : R →+* T) = e.symm.toRingHom.comp (algebraMap R B) :=
    RingHom.ext fun r ↦ (e.symm_apply_eq.2 (he r).symm).symm
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp]

/-- The chart algebra `A[𝔪/π]` of the blowup scheme, transported onto the realization of
`Stacks.nodalCentralChart_equiv`. -/
private def nodalCentralChartTransport (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 0)
      ≃ₐ[nodalChartRing R (π ^ n)]
      nodalCentralChart π n (Localization.Away (algebraMap R (nodalChartRing R (π ^ n)) π)) :=
  Subalgebra.equivOfEq _ _ (affineBlowup_nodalCenterGen_zero_eq π n)

/-- The chart algebra `A[𝔪/x]` of the blowup scheme, transported onto the realization of
`Stacks.nodalXChart_equiv`. -/
private def nodalXChartTransport (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 1)
      ≃ₐ[nodalChartRing R (π ^ n)]
      nodalXChart π n (Localization.Away (nodalGen R (π ^ n) 0)) :=
  Subalgebra.equivOfEq _ _ (affineBlowup_nodalCenterGen_one_eq π n)

/-- The chart algebra `A[𝔪/y]` of the blowup scheme, transported onto the realization of
`Stacks.nodalYChart_equiv`. -/
private def nodalYChartTransport (π : R) (n : ℕ) :
    affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 2)
      ≃ₐ[nodalChartRing R (π ^ n)]
      nodalYChart π n (Localization.Away (nodalGen R (π ^ n) 1)) :=
  Subalgebra.equivOfEq _ _ (affineBlowup_nodalCenterGen_two_eq π n)

variable [IsDomain R] [UniqueFactorizationMonoid R] {π : R} {n : ℕ}

/-- The central chart algebra `A[𝔪/π]` of the blowup scheme is `R[x', y']/(x'y' - π^(n-2))`, as
an `R`-algebra. -/
public theorem exists_ringEquiv_affineBlowup_nodalCenterGen_zero (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 0)
        ≃+* nodalChartRing R (π ^ (n - 2)),
      ∀ r : R, e (algebraMap R _ r) = algebraMap R (nodalChartRing R (π ^ (n - 2))) r := by
  obtain ⟨e, he, -⟩ := nodalCentralChart_equiv π n
    (Localization.Away (algebraMap R (nodalChartRing R (π ^ n)) π)) hπ hn
  exact ⟨(nodalCentralChartTransport π n).toRingEquiv.trans e,
    ringEquiv_trans_algebraMap (nodalCentralChartTransport π n) e he⟩

/-- The chart algebra `A[𝔪/x]` of the blowup scheme is `R[x, u]/(xu - π)`, as an
`R`-algebra. -/
public theorem exists_ringEquiv_affineBlowup_nodalCenterGen_one (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 1)
        ≃+* nodalChartRing R π,
      ∀ r : R, e (algebraMap R _ r) = algebraMap R (nodalChartRing R π) r := by
  obtain ⟨e, he, -, -⟩ := nodalXChart_equiv π n
    (Localization.Away (nodalGen R (π ^ n) 0)) hπ hn
  exact ⟨(nodalXChartTransport π n).toRingEquiv.trans e,
    ringEquiv_trans_algebraMap (nodalXChartTransport π n) e he⟩

/-- The chart algebra `A[𝔪/y]` of the blowup scheme is `R[y, v]/(yv - π)`, as an
`R`-algebra. -/
public theorem exists_ringEquiv_affineBlowup_nodalCenterGen_two (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n 2)
        ≃+* nodalChartRing R π,
      ∀ r : R, e (algebraMap R _ r) = algebraMap R (nodalChartRing R π) r := by
  obtain ⟨e, he, -, -⟩ := nodalYChart_equiv π n
    (Localization.Away (nodalGen R (π ^ n) 1)) hπ hn
  exact ⟨(nodalYChartTransport π n).toRingEquiv.trans e,
    ringEquiv_trans_algebraMap (nodalYChartTransport π n) e he⟩

/-- Each of the three charts of `X'` is, over `S`, a standard nodal model: the central chart with
parameter `π^(n-2)` and the two outer ones with parameter `π`. -/
public theorem exists_param_nodalModelBlowupChart (hπ : π ≠ 0) (hn : 2 ≤ n) (i : Fin 3) :
    ∃ (h : R) (e : affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)
        ≃+* nodalChartRing R h),
      ∀ r : R, e (algebraMap R _ r) = algebraMap R (nodalChartRing R h) r := by
  fin_cases i
  · exact ⟨_, exists_ringEquiv_affineBlowup_nodalCenterGen_zero hπ hn⟩
  · exact ⟨_, exists_ringEquiv_affineBlowup_nodalCenterGen_one hπ hn⟩
  · exact ⟨_, exists_ringEquiv_affineBlowup_nodalCenterGen_two hπ hn⟩

end Identifications

/-! ### `X' ⟶ S` is at-worst-nodal of relative dimension one -/

section AtWorstNodal

variable [IsDomain R] [UniqueFactorizationMonoid R] {π : R} {n : ℕ}

/-- Each chart of `X'` is at-worst-nodal of relative dimension one over `S`. -/
public theorem isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupChart_comp
    (hπ : π ≠ 0) (hn : 2 ≤ n) (i : Fin 3) :
    IsAtWorstNodalOfRelativeDimensionOne
      (nodalModelBlowupChart R π n i ≫ nodalModelBlowupToBase R π n) := by
  obtain ⟨h, e, he⟩ := exists_param_nodalModelBlowupChart hπ hn i
  have hresp : MorphismProperty.RespectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hiso : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map e.symm.toCommRingCatIso.hom))
  rw [nodalModelBlowupChart_comp_toBase, specMap_algebraMap_eq_of_ringEquiv e he,
    MorphismProperty.cancel_left_of_respectsIso
      (P := @IsAtWorstNodalOfRelativeDimensionOne.{u})]
  exact isAtWorstNodalOfRelativeDimensionOne_specMap_nodalChartRing h

/-- **`X' ⟶ S` is at-worst-nodal of relative dimension one.** The three charts cover `X'`, an
open immersion is étale, and over `S` each chart is a standard nodal model: the central one with
parameter `π^(n-2)`, the two outer ones with parameter `π`. -/
@[stacks 0CDC "thus we see that X' → S is at-worst-nodal of relative dimension 1"]
public theorem isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupToBase
    (hπ : π ≠ 0) (hn : 2 ≤ n) :
    IsAtWorstNodalOfRelativeDimensionOne (nodalModelBlowupToBase R π n) := by
  have hcov : Presieve.ofArrows
      (fun i : Fin 3 => Spec (CommRingCat.of
        (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i))))
      (fun i => nodalModelBlowupChart R π n i) ∈ Scheme.etalePrecoverage
        (nodalModelBlowup R π n) := by
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
      ⟨fun z => exists_mem_range_nodalModelBlowupChart π n z, fun i => ?_⟩
    infer_instance
  exact (isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering _ _ hcov).mpr
    (isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupChart_comp hπ hn)

end AtWorstNodal

/-! ### The central chart is the model with the exponent lowered by two -/

section CentralChart

variable [IsDomain R] [UniqueFactorizationMonoid R] {π : R} {n : ℕ}

/-- The central chart of `X'`, in the `Spec` spelling: an open immersion of
`Spec R[x', y']/(x'y' - π^(n-2))` into `X'` over `S`. -/
private theorem exists_isOpenImmersion_spec_sub_two (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ j : Spec (CommRingCat.of (nodalChartRing R (π ^ (n - 2)))) ⟶ nodalModelBlowup R π n,
      IsOpenImmersion j ∧ j ≫ nodalModelBlowupToBase R π n =
        Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R (π ^ (n - 2))))) ∧
        Set.range j.base = Set.range (nodalModelBlowupChart R π n 0).base := by
  obtain ⟨e, he⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_zero hπ hn
  have hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have key := specMap_algebraMap_eq_of_ringEquiv e.symm fun r ↦
    e.symm_apply_eq.2 (he r).symm
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ nodalModelBlowupChart R π n 0,
    IsOpenImmersion.comp _ _, ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    rw [nodalModelBlowupChart_comp_toBase]
    exact key.symm
  · have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom e.toRingHom)).base := by
      have : Surjective (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
      exact (Spec.map (CommRingCat.ofHom e.toRingHom)).surjective
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [hsurj.range_eq, Set.image_univ]

/-- **The one point at which `X'` can fail to be regular has an affine open neighbourhood
exactly as the original situation, with `n` replaced by `n - 2`.** The central chart `A[𝔪/π]` is
an affine open of `X'` which, over `S`, is the standard nodal model of exponent `n - 2`; the two
outer charts are regular by `Stacks.isRegular_spec_nodalXChart` and
`Stacks.isRegular_spec_nodalYChart`. -/
@[stacks 0CDC "X' is regular, except for one point which has an affine open neighbourhood \
exactly as above but with n replaced by n - 2: that neighbourhood, as the standard nodal model \
of exponent n - 2 over S"]
public theorem exists_isOpenImmersion_nodalModel_sub_two (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ j : nodalModel R π (n - 2) ⟶ nodalModelBlowup R π n,
      IsOpenImmersion j ∧ j ≫ nodalModelBlowupToBase R π n = nodalModelHom R π (n - 2) ∧
        Set.range j.base = Set.range (nodalModelBlowupChart R π n 0).base :=
  exists_isOpenImmersion_spec_sub_two hπ hn

end CentralChart

/-! ### Regularity of the blowup -/

/-- **The exponent zero nodal chart ring `R[x, y]/(xy - 1)` is regular over a regular base.** It
is a smooth `R`-algebra, and a smooth algebra over a regular ring is regular. -/
public theorem isRegularRing_nodalChartRing_one (R : Type u) [CommRing R] [IsRegularRing R] :
    IsRegularRing (nodalChartRing R 1) :=
  let := smooth_nodalChartRing_one R
  Algebra.isRegularRing_of_smooth R (nodalChartRing R 1)

/-- **The exponent zero standard nodal model is regular over a regular base.** -/
public theorem isRegular_nodalModel_zero (R : Type u) [CommRing R] [IsRegularRing R] (π : R) :
    IsRegular (nodalModel R π 0) := by
  change IsRegular (Spec (CommRingCat.of (nodalChartRing R (π ^ 0))))
  rw [pow_zero]
  exact @isRegular_spec_of_isRegularRing (nodalChartRing R 1) _
    (isRegularRing_nodalChartRing_one R)

section Regular

variable [IsDomain R] [UniqueFactorizationMonoid R] {π : R} {n : ℕ}

/-- Each of the three chart algebras of `X'` is regular as soon as the nodal chart rings of
parameters `π^(n-2)` and `π` are: the central chart is the first and the two outer charts are
the second. -/
public theorem isRegularRing_affineBlowup_nodalCenterGen (hπ : π ≠ 0) (hn : 2 ≤ n)
    (hc : IsRegularRing (nodalChartRing R (π ^ (n - 2))))
    (ho : IsRegularRing (nodalChartRing R π)) (i : Fin 3) :
    IsRegularRing (affineBlowup (nodalCenter R π (π ^ n)) (nodalCenterGen R π n i)) := by
  fin_cases i
  · obtain ⟨e, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_zero hπ hn
    exact hc.of_ringEquiv e.symm
  · obtain ⟨e, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_one hπ hn
    exact ho.of_ringEquiv e.symm
  · obtain ⟨e, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_two hπ hn
    exact ho.of_ringEquiv e.symm

/-- **The blowup `X'` is regular as soon as its three chart algebras are.** The three charts are
an open cover of `X'` by spectra of those algebras. -/
public theorem isRegular_nodalModelBlowup (hπ : π ≠ 0) (hn : 2 ≤ n)
    (hc : IsRegularRing (nodalChartRing R (π ^ (n - 2))))
    (ho : IsRegularRing (nodalChartRing R π)) :
    IsRegular (nodalModelBlowup R π n) := by
  refine ((isRegular_tfae_cover (nodalModelBlowup R π n)).out 4 1 rfl rfl).mp
    ⟨ULift.{u} (Fin 3), fun i => (nodalModelBlowupChart R π n i.down).opensRange, ?_, fun i => ?_⟩
  · rw [← iSup_opensRange_nodalModelBlowupChart π n]
    exact le_antisymm (iSup_le fun i => le_iSup_of_le i.down le_rfl)
      (iSup_le fun i => le_iSup_of_le (ULift.up i) le_rfl)
  · exact IsRegular.of_iso (Scheme.Hom.isoOpensRange (nodalModelBlowupChart R π n i.down)).symm
      (@isRegular_spec_of_isRegularRing _ _
        (isRegularRing_affineBlowup_nodalCenterGen hπ hn hc ho i.down))

end Regular

section Resolution

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **For `2 ≤ n ≤ 3` the single blowup already resolves the singularity: `X'` is regular.** The
exponent drop `n ↦ n - 2` of the central chart lands on `0` or `1`, where the standard nodal
model is regular, and the two outer charts are regular for every `n ≥ 2`. Since `⌊n/2⌋ = 1` for
these `n`, the chain of blowing ups in closed points of [Stacks, Tag 0CDC] is here the single
blowup `b : X' ⟶ X`, and `X' ⟶ S` is at-worst-nodal of relative dimension one by
`Stacks.isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupToBase`. -/
@[stacks 0CDC "using induction on n: for 2 ≤ n ≤ 3 the sequence of blowing ups in closed points \
X_{⌊n/2⌋} → … → X₁ → X₀ = X is the single blowup b : X' → X, and X_{⌊n/2⌋} = X' is regular"]
public theorem isRegular_nodalModelBlowup_of_le_three {π : R} (hπ : Irreducible π) {n : ℕ}
    (h2 : 2 ≤ n) (h3 : n ≤ 3) : IsRegular (nodalModelBlowup R π n) := by
  refine isRegular_nodalModelBlowup hπ.ne_zero h2 ?_ (isRegularRing_nodalChartRing hπ)
  interval_cases n
  · rw [show (2 : ℕ) - 2 = 0 from rfl, pow_zero]
    exact isRegularRing_nodalChartRing_one R
  · rw [show (3 : ℕ) - 2 = 1 from rfl, pow_one]
    exact isRegularRing_nodalChartRing hπ

end Resolution

end Stacks

end
