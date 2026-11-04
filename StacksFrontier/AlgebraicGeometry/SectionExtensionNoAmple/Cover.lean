module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample

/-!
# The cover the gluing argument of Stacks Tag 01PW needs, without ampleness

`Stacks.SectionExtension.exists_common_degree_affine_cover` produces, **from ampleness of `L`**, a
single degree `N` carrying a finite family `c i` of homogeneous elements whose nonvanishing loci
are *affine* and cover `X`, together with a power of a prescribed element in that same degree.

Ampleness is used there for exactly one thing: that the nonvanishing locus `X_b` through a point
can be chosen affine. This file drops that, and keeps everything else:

> if every point of a quasi-compact `X` lies in *some* `X_b` for `b` homogeneous of positive
> degree, there is one degree `N` carrying a finite family `c i` and a finite family of **affine
> opens `V i ⊆ X_{c i}`** covering `X`, plus a power of a prescribed element in degree `N`.

The affine opens are obtained by refining each `X_{b}` along the basis of affine opens
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`) rather than by asking `X_b` to be affine itself.
That weakening is the whole point: the gluing argument only ever uses an affine open *inside* a
nonvanishing locus, because all it does on a chart is divide by the generator `c i`, and
`Stacks.SectionExtension.exists_resTop_eq_smul` and
`Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` are both stated for an arbitrary open
inside the nonvanishing locus.

## The hypothesis, and why it is strictly weaker than ampleness

`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` is `Stacks.Ample.IsAmple` with the
affineness clause of
`Stacks.AmpleTheory.isAmple_iff_forall_affine_nonvanishingOpen` deleted and quasi-compactness of
`X` separated out. It is satisfied, with no ampleness anywhere, by the pullback `f^* M` of an ample
module along any morphism: the preimages `f⁻¹(S_t)` of the affine nonvanishing opens of `S` are the
nonvanishing opens of the pulled-back sections (Stacks Tag 0H78,
`Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`) and cover `X`, while being in
general not affine. That is precisely the case part (1) of [Stacks, Tag 0892] needs, where
assuming `f^* M` ample would be circular.

## Main definitions and results

* `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`: every point lies in the nonvanishing
  locus of a homogeneous element of positive degree.
* `Stacks.SectionExtensionNoAmple.exists_common_degree_affine_subcover`: the cover described above.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.GradedSections (powSections)

universe u

namespace Stacks.SectionExtensionNoAmple

section Cover

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Every point lies in the nonvanishing locus of a homogeneous element of positive degree.**
This is the clause of ampleness that the gluing argument of Stacks Tag 01PW actually consumes, with
the affineness of the nonvanishing locus deleted — see the module documentation for why that
deletion is the point. -/
def HasPointwiseNonvanishing : Prop :=
  ∀ x : X, ∃ (d : ℕ) (b : powSections L d), 1 ≤ d ∧ x ∈ nvOpen L b

/-- **The cover the gluing argument of Stacks Tag 01PW runs over, with no ampleness.** For `X`
quasi-compact, `L` invertible with enough sections in the sense of
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`, and `a` homogeneous of positive degree
`n`, there is one degree `N` carrying

* a power `a'` of `a`, with the same nonvanishing locus — so `n ∣ N`, which is what lets a
  consumer solve the degree equation of its own power family — and
* a finite family `c i` of homogeneous elements of degree `N`,

together with a finite family of **affine** opens `V i ≤ X_{c i}` covering `X`.

The proof is `Stacks.SectionExtension.exists_common_degree_affine_cover` with one step inserted and
one deleted: each pointwise nonvanishing locus is first refined to an affine open inside it, and
the affineness of the nonvanishing locus is never asked for. The common degree is then produced by
exactly the same two facts, `Stacks.FinGenFromCover.exists_common_degree_family` and
`Stacks.AmpleAffineAvoidance.exists_pow_of_dvd`. -/
theorem exists_common_degree_affine_subcover (hX : CompactSpace X)
    (hpt : HasPointwiseNonvanishing L) {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) :
    ∃ (N : ℕ) (a' : powSections L N) (ι : Type u) (_ : Finite ι)
      (c : ι → powSections L N) (V : ι → X.Opens),
      1 ≤ N ∧ n ∣ N ∧ nvLocus L a' = nvLocus L a ∧ (∀ i, IsAffineOpen (V i)) ∧
        (∀ i, V i ≤ nvOpen L (c i)) ∧ (⊤ : X.Opens) ≤ ⨆ i, V i := by
  classical
  choose d b hd hmem using hpt
  have hrefine : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ V ≤ nvOpen L (b x) := by
    intro x
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hmem x) (nvOpen L (b x)).2
    exact ⟨V, hxV, hV, hVle⟩
  choose V hxV hVaff hVle using hrefine
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y : X => ((V y : X.Opens) : Set X))
    (fun y => (V y).2) fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨N₀, b', hN₀, hb'⟩ :=
    Stacks.FinGenFromCover.exists_common_degree_family L (ι := {y : X // y ∈ T})
      (fun i => d i.1) (fun i => hd i.1) fun i => b i.1
  have hN : 1 ≤ n * N₀ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨a', ha'⟩ := Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L a (dvd_mul_right n N₀) hN
  choose c hc using fun i =>
    Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L (b' i) (dvd_mul_left N₀ n) hN
  have hcoe : ∀ i, nvOpen L (c i) = nvOpen L (b i.1) := fun i =>
    TopologicalSpace.Opens.ext (by rw [coe_nvOpen, coe_nvOpen, hc i, hb' i])
  refine ⟨n * N₀, a', {y : X // y ∈ T}, inferInstance, c, fun i => V i.1, hN,
    dvd_mul_right n N₀, ha', fun i => hVaff i.1, fun i => ?_, fun x _ => ?_⟩
  · rw [hcoe i]; exact hVle i.1
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩

end Cover

end Stacks.SectionExtensionNoAmple

end
