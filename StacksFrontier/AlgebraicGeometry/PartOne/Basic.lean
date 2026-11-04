module

public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Annihilator

/-!
# The trivializing affine cover of [Stacks, Tag 01PW], and the annihilator step of part (1)

The proof of [Stacks, Tag 01PW] opens by choosing a finite affine open cover `X = ⋃ Uⱼ` on which
the invertible module is trivial, and observing that there `X_s ∩ Uⱼ = D(fⱼ)` for the function
`fⱼ` corresponding to `s` under the trivialization. Everything else in the source is a
localization computation over the affine `Uⱼ` and a gluing over the cover.

This file builds that cover, and runs the injectivity step of part (1) over it.

## Why this cover and not a cover by nonvanishing loci

`Stacks.SectionExtensionNoAmple` proves the surjectivity half of Tag 01PW over a cover by affine
opens *contained in nonvanishing loci of global homogeneous elements*, which is what its
hypothesis `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` provides. That hypothesis is
strictly stronger than anything Tag 01PW assumes: an invertible module with
`Γ(X, L ^⊗ n) = 0` for every `n ≥ 1` — an anti-ample module on a projective curve — has empty
nonvanishing loci and so fails it, while Tag 01PW still applies. The covering-set rule therefore
withholds Tag 01PW's labels from every consequence of that hypothesis, and the files in that
directory say so.

The cover built here replaces the global homogeneous elements by **local basis sections**, which
exist for every invertible module with no hypothesis beyond invertibility, by clause 2 of
[Stacks, Tag 0B8M] (`Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible`). That is
the source's own cover.

## Main results

* `Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover`: **the source's cover.** A
  quasi-compact scheme carrying an invertible module is covered by finitely many affine opens on
  each of which that module is sectionwise trivial. No ampleness, and no global section.
* `Stacks.Tag01PWPartOne.exists_finite_affine_basicOpen_cover`: **`X_s ∩ Uⱼ = D(fⱼ)`.** Over that
  cover, the nonvanishing open of a global section meets each member in the basic open of the
  section's trivializing function.
* `Stacks.Tag01PWPartOne.exists_cover_pow_smul_res_eq_zero`: **the annihilator step of part (1)
  of [Stacks, Tag 01PW], at Tag 01PW's own hypotheses.** For `X` quasi-compact, `M` invertible,
  `s` a global section of `M` and `G` quasi-coherent, a global section of `G` vanishing on `X_s`
  is killed, over every member of the cover, by one single power of that member's trivializing
  function. Quasi-compactness is the only hypothesis on `X`; there is no ampleness and no
  `HasPointwiseNonvanishing`.

## What is not done, and no tag is attached

**No `@[stacks]` attribute is attached, and part (1) is not closed.** Part (1) asserts
injectivity of the map `Γ_*(X, 𝓕, L)_{(s)} → Γ(X_s, 𝓕)` of [Stacks, Tag 0B5L]. Neither that map
nor the graded module `Γ_*(X, 𝓕, L)` it is defined on exists in either tree: the graded *ring*
`Γ_*(X, L)` is `Stacks.GradedSections.sectionRing` and the graded module over it is absent, so
part (1) is not yet statable. What is proved here is the geometric content of its proof.

**The one step between this file and the injectivity statement** is the local power law: for `b`
a basis section of `M` over a trivializing open `W` and `s|_W = f • b`, the `k`-th power
`s^k ∈ Γ(M ^⊗ k, ⊤)` of `s` satisfies `s^k|_W = f^k • b^{(k)}` for the induced basis section
`b^{(k)}` of `M ^⊗ k` over `W`. With it, the conclusion below turns into
`Stacks.SectionTensorFormula.tensorSection G (M ^⊗ k) τ (s^k) = 0` by
`tensorSection_smul_right`, `tensorSection_smul_left` and `tensorSection_zero_left`, and the
sheaf condition over the cover. `Stacks.TensorPowerTrivialize.resTop_sectionPow` is that power law
for two *global* sections with one of them nowhere vanishing on `W`; the basis section here is
local, and nothing states it for a local section.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleSectionExtension (res)
open Stacks.SectionExtension (map_res_res_module exists_forall_le)

universe u

namespace Stacks.Tag01PWPartOne

variable {X : Scheme.{u}}

/-- **The cover the proof of [Stacks, Tag 01PW] runs over.** A quasi-compact scheme carrying an
invertible `𝒪_X`-module is covered by finitely many affine opens on each of which the module is
sectionwise trivial.

Clause 2 of [Stacks, Tag 0B8M] gives a trivializing open around every point; refining along
`AlgebraicGeometry.Scheme.isBasis_affineOpens` makes those opens affine, and
`IsCompact.elim_finite_subcover` makes the family finite. The shape is the one of
`Stacks.SectionExtensionNoAmple.exists_finite_affine_cover`, with the trivialization carried
along. -/
theorem exists_finite_affine_trivializing_cover [CompactSpace X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] :
    ∃ (ι : Type u) (_ : Finite ι) (W : ι → X.Opens),
      (∀ i, IsAffineOpen (W i)) ∧ ((⊤ : X.Opens) ≤ ⨆ i, W i) ∧
        ∀ i, Nonempty (Stacks.SheafDescent.Trivialization X.presheaf M.val (W i)) := by
  classical
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  have hcov : (Set.univ : Set X) ⊆
      ⋃ A : {A : X.affineOpens // ∃ z : X, (A.1 : X.Opens) ≤ V z},
        ((A.1.1 : X.Opens) : Set X) := by
    intro x _
    obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
    obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz (V z).2
    exact Set.mem_iUnion.mpr ⟨⟨⟨A, hA⟩, ⟨z, hAV⟩⟩, hxA⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun A : {A : X.affineOpens // ∃ z : X, (A.1 : X.Opens) ≤ V z} =>
      ((A.1.1 : X.Opens) : Set X))
    (fun A => A.1.1.2) hcov
  refine ⟨{i : {A : X.affineOpens // ∃ z : X, (A.1 : X.Opens) ≤ V z} // i ∈ T}, inferInstance,
    fun i => (i.1.1.1 : X.Opens), fun i => i.1.1.2, fun x hx => ?_, fun i => ?_⟩
  · obtain ⟨A, hAT, hxA⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, hAT⟩, hxA⟩
  · obtain ⟨z, hz⟩ := i.1.2
    exact ⟨(htriv z).some.comp (homOfLE hz)⟩

/-- **`X_s ∩ Uⱼ = D(fⱼ)`, the displayed step of the proof of [Stacks, Tag 01PW].** Over the cover
of `Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover`, the nonvanishing open of a
global section `s` meets each member in the basic open of the trivializing function of `s` there.

This is `Stacks.NonvanishingOpen.nonvanishingLocus_inter` — an equality of *subsets* — read as an
equality of opens over each member of a finite affine cover. -/
theorem exists_finite_affine_basicOpen_cover [CompactSpace X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤)) :
    ∃ (ι : Type u) (_ : Finite ι) (W : ι → X.Opens) (f : (i : ι) → Γ(X, W i)),
      (∀ i, IsAffineOpen (W i)) ∧ ((⊤ : X.Opens) ≤ ⨆ i, W i) ∧
        ∀ i, Stacks.NonvanishingOpen.nonvanishingOpen X M s ⊓ W i = X.basicOpen (f i) := by
  obtain ⟨ι, hι, W, hWaff, hcover, htriv⟩ := exists_finite_affine_trivializing_cover M
  refine ⟨ι, hι, W, fun i => Stacks.NonvanishingOpen.trivTop (htriv i).some s, hWaff, hcover,
    fun i => TopologicalSpace.Opens.ext ?_⟩
  rw [TopologicalSpace.Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen]
  exact Stacks.NonvanishingOpen.nonvanishingLocus_inter (htriv i).some s

/-- **The annihilator step of part (1) of [Stacks, Tag 01PW], at Tag 01PW's own hypotheses.**

For `X` quasi-compact, `M` an invertible `𝒪_X`-module, `s` a global section of `M` and `G` a
quasi-coherent `𝒪_X`-module, a global section `τ` of `G` whose restriction to `X_s` vanishes is
killed, over every member of the trivializing affine cover, by one single power `k` of that
member's trivializing function — `k` is uniform over the cover, which is what the sheaf condition
needs in order to conclude anything global.

The only hypothesis on `X` is quasi-compactness. In particular there is **no** ampleness of `M`
and no `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`; see the module documentation
for why those are strictly stronger than Tag 01PW's hypotheses, and for the one local power law
that still separates this from the injectivity statement itself. -/
theorem exists_cover_pow_smul_res_eq_zero [CompactSpace X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤)) (G : X.Modules) [G.IsQuasicoherent]
    (τ : Γ(G, ⊤))
    (hτ : res G (le_top : Stacks.NonvanishingOpen.nonvanishingOpen X M s ≤ ⊤) τ = 0) :
    ∃ (ι : Type u) (_ : Finite ι) (W : ι → X.Opens) (f : (i : ι) → Γ(X, W i)) (k : ℕ),
      (∀ i, IsAffineOpen (W i)) ∧ ((⊤ : X.Opens) ≤ ⨆ i, W i) ∧
        (∀ i, Stacks.NonvanishingOpen.nonvanishingOpen X M s ⊓ W i = X.basicOpen (f i)) ∧
          ∀ i, f i ^ k • res G (le_top : W i ≤ ⊤) τ = 0 := by
  obtain ⟨ι, hι, W, f, hWaff, hcover, hbasic⟩ := exists_finite_affine_basicOpen_cover M s
  have : Finite ι := hι
  have key : ∀ i, ∃ e : ℕ, f i ^ e • res G (le_top : W i ≤ ⊤) τ = 0 := by
    intro i
    have hle : X.basicOpen (f i) ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s := by
      rw [← hbasic i]; exact inf_le_left
    refine Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero G (hWaff i) (f i) _ ?_
    have hchain : res G (X.basicOpen_le (f i)) (res G (le_top : W i ≤ ⊤) τ)
        = res G hle (res G (le_top : Stacks.NonvanishingOpen.nonvanishingOpen X M s ≤ ⊤) τ) := by
      simp only [res, map_res_res_module]
    rw [hchain, hτ]
    simp
  choose e he using key
  obtain ⟨k, hk⟩ := exists_forall_le e
  refine ⟨ι, hι, W, f, k, hWaff, hcover, hbasic, fun i => ?_⟩
  rw [show k = k - e i + e i from (Nat.sub_add_cancel (hk i)).symm, pow_add, mul_smul, he i,
    smul_zero]

end Stacks.Tag01PWPartOne

end
