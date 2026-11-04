module

public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.FiniteQuotientVanishing
public import StacksFrontier.RingTheory.LocalCohomology.SupportedModulesAcyclic
public import StacksFrontier.RingTheory.Support.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A map out of `M/fM` with a finite-length cokernel is surjective

Let `A` be a Noetherian local ring, `f ∈ 𝔪`, and let `M`, `N` be finite `A`-modules with

* `f` a nonzerodivisor on `M` and `depth_𝔪(M) ≥ 2`,
* `H^2_𝔪(M)` a finite `A`-module,
* `depth_𝔪(N) ≥ 3`.

If `φ : M/fM → N` is injective with a cokernel of finite length, then `φ` is surjective.

This is the module-level heart of the SGA2 injectivity of `Pic(U) → Pic(U₀)`: there `M` is the
module of global sections of an invertible module on the punctured spectrum, `N` is `A/fA`, and
the cokernel of `φ` is the module whose length is the Euler characteristic of the corresponding
coherent triple. Surjectivity of `φ` is the vanishing of that Euler characteristic.

## The argument

Write `Q` for the cokernel, a module of finite length, so supported at the closed point and
therefore acyclic for sections with support there in positive degrees.

* `depth_𝔪(N) ≥ 3` gives `H^i_𝔪(N) = 0` for `i ≤ 2`.
* The long exact sequence of `0 → M/fM → N → Q → 0` then turns `H^1_𝔪(Q) = 0` and
  `H^2_𝔪(N) = 0` into `H^2_𝔪(M/fM) = 0`.
* `H^2_𝔪(M)` is finite and dies on passing to `M/fM`, so it vanishes
  (`Stacks.LocalCohomology.isZero_localCohomology_of_finite_of_isZero_quotSMulTop`).
* `depth_𝔪(M) ≥ 2` gives `H^1_𝔪(M) = 0`, so the long exact sequence of
  `0 → M →^f M → M/fM → 0` gives `H^1_𝔪(M/fM) = 0`.
* The long exact sequence of the first sequence again, one degree down, gives `H^0_𝔪(Q) = 0`;
  since `Q` is supported at the closed point its degree-zero local cohomology is `Q` itself, so
  `Q = 0`.

## Main results

* `Stacks.LocalCohomology.support_subset_closedPoint_of_isFiniteLength`
* `Stacks.LocalCohomology.isZero_of_isZero_localCohomology_zero_of_support_subset`
* `Stacks.LocalCohomology.isZero_localCohomology_maximalIdeal_of_lt_depth`
* `Stacks.LocalCohomology.surjective_of_isFiniteLength_cokernel_of_finite_localCohomology`

## Implementation notes

`Stacks.LocalCohomology.isZero_localCohomology_maximalIdeal_of_lt_depth` is
`Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth` with the hypothesis `𝔪M ≠ M`
removed: that hypothesis says exactly that `M` is nonzero, and for a zero module every local
cohomology module is zero anyway, so the two cases together cover every finite module.

`support_of_isFiniteLength` in `StacksFrontier/RingTheory/Support/Finite.lean` computes the support
of a finite-length module to be the closed point, but needs the module to be nonzero. Here the
module whose support is wanted is the one being shown to vanish, so the inclusion form is
proved instead, by the same induction over `IsFiniteLength`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### Two auxiliary vanishing statements -/

/-- **The support of a finite-length module over a local ring is contained in the closed
point.** Induction over `IsFiniteLength`: a subsingleton has empty support, and in the inductive
step the support of a module is the union of the supports of a submodule and the quotient, the
quotient being simple and so supported at the closed point. -/
theorem support_subset_closedPoint_of_isFiniteLength {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.support R M ⊆ {IsLocalRing.closedPoint R} := by
  induction h with
  | of_subsingleton => simp [Module.support_eq_empty_iff.mpr ‹_›]
  | of_simple_quotient K ih =>
      rename_i P _ _ Q _
      rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ Q) Q.subtype_injective
        Q.mkQ_surjective]
      exact Set.union_subset ih (support_eq_closedPoint_of_isSimpleModule R _).subset

/-- **A module supported in `T` with vanishing degree-zero local cohomology is zero.** For such a
module the sections with support in `T` are everything, and they are the degree-zero local
cohomology by `Stacks.LocalCohomology.sectionsIsoLocalCohomologyZero`. -/
theorem isZero_of_isZero_localCohomology_zero_of_support_subset (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (N : ModuleCat.{u} A) (hN : Module.support A (N : Type u) ⊆ T)
    (h : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 0)) :
    IsZero N := by
  have hsub : Subsingleton (sectionsWithSupportIn A T (N : Type u)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (h.of_iso ((sectionsIsoLocalCohomologyZero.{u, 0} A T).app N))
  have htop : sectionsWithSupportIn A T (N : Type u) = ⊤ :=
    (sectionsWithSupportIn_eq_top_iff A T (N : Type u)).mpr hN
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ ?_⟩
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨a, htop ▸ Submodule.mem_top⟩ : sectionsWithSupportIn A T (N : Type u))
    ⟨b, htop ▸ Submodule.mem_top⟩)

/-- **Local cohomology vanishes below the depth**, with no nonvanishing hypothesis on the module:
for a zero module every local cohomology module is zero, and otherwise Nakayama supplies the
hypothesis `𝔪M ≠ M` of `Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth`. -/
@[sga "2 XII 1.5"]
theorem isZero_localCohomology_maximalIdeal_of_lt_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (n : ℕ) (hd : (n : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) (M : Type u))
    (i : ℤ) (hi : i < n) :
    IsZero (localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) := by
  rcases subsingleton_or_nontrivial (M : Type u) with hs | hnt
  · exact Functor.map_isZero
      (localCohomologyWithSupportInFunctor.{u, 0} A
        (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A)) i)
      (ModuleCat.isZero_of_subsingleton M)
  · exact isZero_localCohomology_of_lt_depth.{u, 0} (IsLocalRing.maximalIdeal A) M
      (Module.maximalIdeal_smul_top_ne_top (M : Type u)) n hd i hi

/-! ### The surjectivity -/

/-- An injective linear map and the projection onto its cokernel form a short exact sequence. -/
theorem shortExact_ofHom_range_mkQ {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (hinj : Function.Injective φ) :
    (ShortComplex.mk (ModuleCat.ofHom φ) (ModuleCat.ofHom (LinearMap.range φ).mkQ)
      (ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self φ x))).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).mpr hinj)
    ((ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _))
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (LinearMap.range φ).mkQ x = 0 := hx
  rwa [← LinearMap.mem_ker, Submodule.ker_mkQ, LinearMap.mem_range] at hx'

/-- **A map out of `M/fM` with a finite-length cokernel is surjective.** Let `A` be a Noetherian
local ring, `f ∈ 𝔪`, and `M`, `N` finite `A`-modules with `f` a nonzerodivisor on `M`,
`depth_𝔪(M) ≥ 2`, `H^2_𝔪(M)` finite and `depth_𝔪(N) ≥ 3`. An injective `A`-linear map
`φ : M/fM → N` whose cokernel has finite length is surjective.

The cokernel is supported at the closed point, so the long exact sequences of
`0 → M/fM → N → coker φ → 0` and `0 → M →^f M → M/fM → 0` propagate the vanishing of
`H^i_𝔪(N)` for `i ≤ 2` down to `H^0_𝔪(coker φ) = 0`, passing through the vanishing of
`H^2_𝔪(M)` that finiteness forces. -/
theorem surjective_of_isFiniteLength_cokernel_of_finite_localCohomology (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    (M N : ModuleCat.{u} A) [Module.Finite A (M : Type u)] [Module.Finite A (N : Type u)]
    (hreg : IsSMulRegular (M : Type u) f)
    (hdM : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (M : Type u))
    (hfin : Module.Finite A (localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 2))
    (hdN : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (N : Type u))
    (φ : QuotSMulTop f (M : Type u) →ₗ[A] (N : Type u)) (hinj : Function.Injective φ)
    (hQ : IsFiniteLength A ((N : Type u) ⧸ LinearMap.range φ)) :
    Function.Surjective φ := by
  set T := PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) with hTdef
  -- the short exact sequence `0 → M/fM → N → Q → 0`
  have hSexact := shortExact_ofHom_range_mkQ φ hinj
  set Mq := ModuleCat.of A (QuotSMulTop f (M : Type u))
  set Q := ModuleCat.of A ((N : Type u) ⧸ LinearMap.range φ)
  -- `Q` is supported at the closed point, hence acyclic in positive degrees
  have hQsupp : Module.support A ((N : Type u) ⧸ LinearMap.range φ) ⊆ T := by
    rw [hTdef, zeroLocus_maximalIdeal]
    exact support_subset_closedPoint_of_isFiniteLength hQ
  have hQone : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Q) 1) :=
    isZero_localCohomologyWithSupportIn_of_support_subset.{u, 0} A T
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization Q hQsupp 1
      (by norm_num)
  -- hence `H^2_𝔪(M/fM) = 0`
  have hMq2 : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Mq) 2) :=
    isZero_localCohomology_X₁.{u, 0} T hSexact 1 2 (by ring) hQone
      (isZero_localCohomology_maximalIdeal_of_lt_depth A N 3 hdN 2 (by norm_num))
  -- so the finite module `H^2_𝔪(M)` vanishes
  have hM2 : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 2) :=
    isZero_localCohomology_of_finite_of_isZero_quotSMulTop (IsLocalRing.maximalIdeal A) hf M
      hreg 2 hfin hMq2
  -- `depth M ≥ 2` kills `H^1_𝔪(M)`, and the sequence of multiplication by `f` gives
  -- `H^1_𝔪(M/fM) = 0`
  have hMq1 : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Mq) 1) :=
    isZero_localCohomology_X₃.{u, 0} T (smulShortComplex_shortExact.{u, 0} hreg) 1 2
      (by ring) (isZero_localCohomology_maximalIdeal_of_lt_depth A M 2 hdM 1 (by norm_num)) hM2
  -- and then `H^0_𝔪(Q) = 0`, so `Q = 0`
  have hQzero : IsZero (localCohomologyWithSupportIn.{u, 0} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Q) 0) :=
    isZero_localCohomology_X₃.{u, 0} T hSexact 0 1 (by ring)
      (isZero_localCohomology_maximalIdeal_of_lt_depth A N 3 hdN 0 (by norm_num)) hMq1
  have hsub : Subsingleton ((N : Type u) ⧸ LinearMap.range φ) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_of_isZero_localCohomology_zero_of_support_subset A T Q hQsupp hQzero)
  rw [← LinearMap.range_eq_top]
  refine top_unique fun x _ ↦ ?_
  have hx : (LinearMap.range φ).mkQ x = 0 := Subsingleton.elim _ _
  rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at hx

end Stacks.LocalCohomology

end
