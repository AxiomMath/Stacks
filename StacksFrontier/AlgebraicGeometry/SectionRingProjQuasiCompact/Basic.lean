module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Annihilator
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.ProjBasis
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiSeparated

/-!
# The canonical morphism to `Proj Γ_*(X, L)` is quasi-compact with dense image: Tag 01Q0

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `S = Γ_*(X, L)` the graded section ring of
Stacks Tag 01CV. **Stacks Tag 01Q0** assumes

* (a) every point of `X` lies in `X_s` for some homogeneous `s ∈ S_+` — the hypothesis of Stacks
  Tag 01PZ, here `Stacks.SectionRingProjMorphism.nvUnion L = ⊤` — and
* (b) `X` is quasi-compact, here `CompactSpace X`,

and concludes that the canonical morphism `f : X ⟶ Proj S` of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfCovers`) is **quasi-compact with dense image**. Both
conclusions are proved here. **`L` is not assumed ample**: ampleness (Stacks Tag 01PS) is (a) and
(b) together with the extra demand that the `X_s` be *affine*, which nothing below uses.

## Quasi-compactness

The Stacks proof checks that `f^{-1}(D₊(s)) = X_s` is quasi-compact, writing `X` as a finite union
of affine opens and intersecting with `X_s` by Stacks Tag 01PV. That is not the route taken here,
because the target is quasi-separated for free:
`Stacks.AlgebraicGeometry.ProjQuasiSeparated.quasiSeparatedSpace_proj` says `Proj 𝒮` is
quasi-separated for *every* graded ring, and `AlgebraicGeometry.quasiCompact_of_compactSpace` —
Stacks Tag 01KO — then makes every morphism out of a quasi-compact scheme into it quasi-compact.
Hypothesis (a) is not needed for this half beyond its role in producing `f`.

## Dense image

This is where (a) and (b) are both spent, and it is the Stacks argument. The basic opens `D₊(s)`
of the homogeneous `s` of positive degree are a basis
(`Stacks.AlgebraicGeometry.ProjBasis.exists_pos_basicOpen_le`), so if the image missed a nonempty
open it would miss a nonempty `D₊(a)`; clause (1) of Stacks Tag 01PZ
(`Stacks.SectionRingProjMorphism.projHomOfCovers_preimage_projBasicOpen`) identifies the preimage
of `D₊(a)` with `X_a`, so `X_a` would be empty, and then a power of `a` is **zero in `S`** —
`Stacks.SectionRingProjQuasiCompact.exists_pow_eq_zero_of_nvOpen_eq_bot` — whence
`D₊(a) = D₊(aᵏ) = D₊(0) = ∅`, a contradiction.

The nilpotence step is the injectivity half of Stacks Tag 01PW in the case `𝓕 = 𝒪_X`, in the form
`Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero_of_cover` already carries it: that
lemma annihilates against a finite **affine** cover whose members sit inside the nonvanishing
opens of finitely many homogeneous elements of one common degree. Under ampleness one takes the
affine `X_{c i}` themselves; under (a) and (b) alone the `X_b` cover `X` but need not be affine,
so `Stacks.SectionRingProjQuasiCompact.exists_common_degree_affine_subcover` shrinks each `X_b` to
an affine open around each of its points and cuts the result down by quasi-compactness. This is
the only place where the two hypotheses are used, and it is why they are exactly the hypotheses of
the tag.

## Main results

* `Stacks.SectionRingProjQuasiCompact.exists_common_degree_affine_subcover`: a finite affine cover
  of `X` subordinate to the nonvanishing opens of homogeneous elements of one common degree.
* `Stacks.SectionRingProjQuasiCompact.exists_pow_eq_zero_of_nvOpen_eq_bot`: **a homogeneous
  element of positive degree with empty nonvanishing open is nilpotent in `Γ_*(X, L)`.**
* `Stacks.SectionRingProjQuasiCompact.projBasicOpen_eq_bot_of_nvOpen_eq_bot`: such an element has
  empty chart `D₊`.
* `Stacks.SectionRingProjQuasiCompact.quasiCompact_projHomOfCovers`: **Stacks Tag 01Q0, the
  quasi-compactness.**
* `Stacks.SectionRingProjQuasiCompact.denseRange_projHomOfCovers`: **Stacks Tag 01Q0, the dense
  image.**

## References

* [Stacks Project, Tag 01Q0](https://stacks.math.columbia.edu/tag/01Q0)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (resTop powSec nvLocus_powSec_of_one_le)

universe u

namespace Stacks.SectionRingProjQuasiCompact

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### Sections over the empty open -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- A section of an `𝒪_X`-module restricts to zero on an empty open, there being only one section
there. -/
theorem resTop_eq_zero_of_eq_bot {M : X.Modules} {U : X.Opens} (hU : U = ⊥) (t : Γ(M, ⊤)) :
    resTop U t = 0 := by
  subst hU
  have : Subsingleton Γ(M, (⊥ : X.Opens)) := ⟨fun p q ↦ by
    refine TopCat.Presheaf.IsSheaf.section_ext M.isSheaf (U := op (⊥ : X.Opens)) ?_
    intro z hz
    exact absurd hz (by simp)⟩
  exact Subsingleton.elim _ _

/-! ### A finite affine cover subordinate to the nonvanishing opens -/

/-- **Clause (a) of Stacks Tag 01PZ plus quasi-compactness give a finite affine cover of `X`
subordinate to the nonvanishing opens of homogeneous elements of one common degree.**

The degree can be prescribed to be a multiple of any given positive `n`, which is what the
annihilator needs in order to produce a power of a *given* element.

`Stacks.SectionExtension.exists_common_degree_affine_cover` is the ample analogue, where the
nonvanishing opens are themselves affine and no shrinking is needed. Here they need not be, so
each `X_b` is shrunk to an affine open around each of its points before quasi-compactness cuts the
family down; the price is that the covering opens are only *contained in* the nonvanishing
opens. -/
theorem exists_common_degree_affine_subcover [CompactSpace X]
    (hcov : Stacks.SectionRingProjMorphism.nvUnion L = ⊤) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (N : ℕ) (F : Finset X) (c : {y : X // y ∈ F} → powSections L N)
      (V : {y : X // y ∈ F} → X.Opens),
      1 ≤ N ∧ n ∣ N ∧ (∀ i, V i ≤ nvOpen L (c i)) ∧ (∀ i, IsAffineOpen (V i)) ∧
        (⊤ : X.Opens) ≤ ⨆ i, V i := by
  classical
  -- clause (a), read pointwise
  have hpt : ∀ x : X, ∃ (e : ℕ) (b : powSections L e), 1 ≤ e ∧ x ∈ nvOpen L b := by
    intro x
    have hx : x ∈ Stacks.SectionRingProjMorphism.nvUnion L := by rw [hcov]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨p.deg, p.val, p.deg_pos, hp⟩
  choose e b he hmem using hpt
  -- an affine open around each point inside its nonvanishing open
  choose W hWaff hxW hWle using fun x : X =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (hmem x)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y : X => (W y : Set X))
    (fun y => (W y).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩
  -- one common degree for the finitely many elements, then one multiple of `n`
  obtain ⟨N₀, b', hN₀, hb'⟩ :=
    Stacks.FinGenFromCover.exists_common_degree_family L (ι := {y : X // y ∈ F})
      (fun i => e i.1) (fun i => he i.1) fun i => b i.1
  have hN : 1 ≤ n * N₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  choose c hc using fun i : {y : X // y ∈ F} =>
    Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L (b' i) (dvd_mul_left N₀ n) hN
  have hcoe : ∀ i : {y : X // y ∈ F}, nvOpen L (c i) = nvOpen L (b i.1) := fun i =>
    TopologicalSpace.Opens.ext (by rw [coe_nvOpen, coe_nvOpen, hc i, hb' i])
  refine ⟨n * N₀, F, c, fun i => W i.1, hN, dvd_mul_right n N₀, fun i => ?_,
    fun i => hWaff i.1, ?_⟩
  · rw [hcoe i]
    exact hWle i.1
  · intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩

/-! ### A homogeneous element vanishing everywhere is nilpotent -/

/-- **A homogeneous element of positive degree whose nonvanishing open is empty is nilpotent in
`Γ_*(X, L)`**, under clauses (a) and (b) of Stacks Tag 01Q0.

The element restricts to zero on its own nonvanishing open for trivial reasons when that open is
empty, so the annihilator of
`Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero_of_cover` — the injectivity half of
Stacks Tag 01PW at the degree of `a`, in the case `𝓕 = 𝒪_X` — applies to `u = a` itself and kills
it against a power of `a`. The covering element is the genuine power
`Stacks.SectionExtension.powSec L a N₀`, so that
`Stacks.SectionRingChartMap.of_powSec_eq_pow` turns the conclusion into a power of `a` in the
ring. -/
theorem exists_pow_eq_zero_of_nvOpen_eq_bot [CompactSpace X]
    (hcov : Stacks.SectionRingProjMorphism.nvUnion L = ⊤) {d : ℕ} (hd : 1 ≤ d)
    (a : powSections L d) (ha : nvOpen L a = ⊥) :
    ∃ k : ℕ, 1 ≤ k ∧ DirectSum.of (powSections L) d a ^ k = 0 := by
  obtain ⟨N, F, c, V, hN1, hdvd, hVmem, hVaff, hcover⟩ :=
    exists_common_degree_affine_subcover L hcov hd
  obtain ⟨N₀, rfl⟩ := hdvd
  have hN₀ : 1 ≤ N₀ := by
    rcases Nat.eq_zero_or_pos N₀ with h | h
    · rw [h, Nat.mul_zero] at hN1; omega
    · exact h
  obtain ⟨k, hk⟩ := Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero_of_cover L
    (powSec L a N₀) c (nvOpen L a)
    (Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L a N₀ hN₀) V hVmem hVaff hcover a
    (resTop_eq_zero_of_eq_bot ha (globalSection X _ a))
  rw [Stacks.SectionRingChartMap.of_powSec_eq_pow L a N₀, ← pow_mul] at hk
  exact ⟨N₀ * k + 1, by omega, by rw [pow_succ']; exact hk⟩

/-- **A homogeneous element of positive degree with empty nonvanishing open has empty chart**,
under clauses (a) and (b) of Stacks Tag 01Q0. `AlgebraicGeometry.Proj.basicOpen_pow` reads `D₊`
off the nilpotence of `Stacks.SectionRingProjQuasiCompact.exists_pow_eq_zero_of_nvOpen_eq_bot`. -/
theorem projBasicOpen_eq_bot_of_nvOpen_eq_bot [CompactSpace X]
    (hcov : Stacks.SectionRingProjMorphism.nvUnion L = ⊤) {d : ℕ} (hd : 1 ≤ d)
    (a : powSections L d) (ha : nvOpen L a = ⊥) :
    Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = ⊥ := by
  obtain ⟨k, hk1, hk⟩ := exists_pow_eq_zero_of_nvOpen_eq_bot L hcov hd a ha
  rw [← Proj.basicOpen_pow (grading L) (DirectSum.of (powSections L) d a) k hk1, hk,
    Proj.basicOpen_zero]

/-! ### Stacks Tag 01Q0 -/

/-- **Stacks Tag 01Q0, the quasi-compactness.** Under clause (a) of Stacks Tag 01PZ — the `X_s`
cover `X` — and `X` quasi-compact, the canonical morphism `f : X ⟶ Proj Γ_*(X, L)` of Stacks Tag
01PZ is quasi-compact.

`Proj` of any graded ring is quasi-separated
(`Stacks.AlgebraicGeometry.ProjQuasiSeparated.quasiSeparatedSpace_proj`), so this is
`AlgebraicGeometry.quasiCompact_of_compactSpace`, which is Stacks Tag 01KO. -/
@[stacks 01Q0 "the canonical morphism of 01PZ is quasi-compact, under (a) the X_s cover X and (b) X quasi-compact"]
theorem quasiCompact_projHomOfCovers [CompactSpace X]
    (hcov : Stacks.SectionRingProjMorphism.nvUnion L = ⊤) :
    QuasiCompact (Stacks.SectionRingProjMorphism.projHomOfCovers L hcov) :=
  AlgebraicGeometry.quasiCompact_of_compactSpace _

/-- **Stacks Tag 01Q0, the dense image.** Under clause (a) of Stacks Tag 01PZ — the `X_s` cover
`X` — and `X` quasi-compact, the canonical morphism `f : X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ
has dense image.

A nonempty open of `Proj Γ_*(X, L)` missing the image would contain a nonempty `D₊(a)` with `a`
homogeneous of positive degree, whose preimage `X_a` would then be empty; but then `a` is
nilpotent and `D₊(a) = ∅`. -/
@[stacks 01Q0 "the canonical morphism of 01PZ has dense image, under (a) the X_s cover X and (b) X quasi-compact"]
theorem denseRange_projHomOfCovers [CompactSpace X]
    (hcov : Stacks.SectionRingProjMorphism.nvUnion L = ⊤) :
    DenseRange (Stacks.SectionRingProjMorphism.projHomOfCovers L hcov).base := by
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  intro y _
  by_contra hy
  obtain ⟨Ω, hΩopen, hyΩ, hΩ⟩ : ∃ Ω : Set ↥(AlgebraicGeometry.Proj (grading L)), IsOpen Ω ∧ y ∈ Ω ∧
      Ω ∩ Set.range (Stacks.SectionRingProjMorphism.projHomOfCovers L hcov).base = ∅ := by
    refine ⟨(closure (Set.range
        (Stacks.SectionRingProjMorphism.projHomOfCovers L hcov).base))ᶜ,
      isClosed_closure.isOpen_compl, hy, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact hz.1 (subset_closure hz.2)
  obtain ⟨j, s, hj, hsmem, hys, hsΩ⟩ :=
    Stacks.AlgebraicGeometry.ProjBasis.exists_pos_basicOpen_le (grading L)
      ⟨Ω, hΩopen⟩ hyΩ
  obtain ⟨a, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hsmem
  have hempty : nvOpen L a = ⊥ := by
    refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_)
    have hz' : z ∈ Stacks.SectionRingProjMorphism.projHomOfCovers L hcov
        ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) j a) := by
      rw [Stacks.SectionRingProjMorphism.projHomOfCovers_preimage_projBasicOpen L hcov a hj]
      exact hz
    have hmem : (Stacks.SectionRingProjMorphism.projHomOfCovers L hcov).base z ∈ Ω := hsΩ hz'
    exact Set.eq_empty_iff_forall_notMem.mp hΩ _ ⟨hmem, ⟨z, rfl⟩⟩
  rw [projBasicOpen_eq_bot_of_nvOpen_eq_bot L hcov hj a hempty] at hys
  exact hys

end Monoidal

end Stacks.SectionRingProjQuasiCompact

end
