module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.LinearTopology
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# What continuity of the scalar multiplication means

Stacks Project, Chapter 87 "Formal Spaces", Tag 0AMR.

Let `R` be a linearly topologized ring and let `M` be a linearly topologized `R`-module.
Fix a fundamental system `I` of open ideals of `R` and a fundamental system `N` of open
submodules of `M`, that is, families for which the members form a basis of neighbourhoods of
zero. The source records that in this situation continuity of `+ : M × M → M` is automatic
(see `TopologicalRing.continuous_add_of_hasBasis_addSubgroup`), while continuity of
`R × M → M` is a genuine condition, namely
`∀ f, x, μ, ∃ λ, ν, (f + I λ) • (x + N ν) ⊆ f • x + N μ`, and that this condition simplifies
to the pointwise one `∀ x, μ, ∃ λ, I λ • x ⊆ N μ`.

## Main results

* `TopologicalModule.continuousSMul_iff_forall_exists_smul_mem`: scalar multiplication is
  continuous if and only if for every `x : M` and every index `μ` there is an index `λ` with
  `I λ • x ⊆ N μ`.
* `TopologicalModule.continuousSMul_iff_forall_exists_coset_smul_coset`: scalar multiplication
  is continuous if and only if the displayed condition on cosets holds.

Together the two give the chain of equivalences asserted by the source.

## References

* [Stacks Project, Tag 0AMR](https://stacks.math.columbia.edu/tag/0AMR)
-/

namespace TopologicalModule

open Filter

open scoped Pointwise Topology

variable {R M ι κ : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  (I : ι → Ideal R) (N : κ → Submodule R M)

/-- **Tag 0AMR.** Let `I` be a fundamental system of open ideals of a topological ring `R` and
let `N` be a fundamental system of open submodules of an `R`-module `M`. Then scalar
multiplication `R × M → M` is continuous exactly when `I λ • x ⊆ N μ` for some `λ`, for every
`x : M` and every `μ`. -/
@[stacks 0AMR "scalar_continuity_criterion"]
theorem continuousSMul_iff_forall_exists_smul_mem
    (hI : (𝓝 (0 : R)).HasBasis (fun _ : ι ↦ True) fun l ↦ (I l : Set R))
    (hN : (𝓝 (0 : M)).HasBasis (fun _ : κ ↦ True) fun m ↦ (N m : Set M)) :
    ContinuousSMul R M ↔ ∀ (x : M) (μ : κ), ∃ l : ι, ∀ f ∈ I l, f • x ∈ N μ := by
  constructor
  · intro _ x μ
    have hmem : (fun f : R ↦ f • x) ⁻¹' (N μ : Set M) ∈ 𝓝 (0 : R) := by
      refine ((continuous_id.smul continuous_const).continuousAt (x := (0 : R))) ?_
      simpa using hN.mem_of_mem (i := μ) trivial
    obtain ⟨l, -, hl⟩ := hI.mem_iff.mp hmem
    exact ⟨l, fun f hf ↦ hl hf⟩
  · intro h
    have hsmul : ∀ {μ : κ}, True →
        ∃ V ∈ 𝓝 (0 : R), ∃ ν : κ, True ∧ V • (N ν : Set M) ⊆ (N μ : Set M) := by
      intro μ _
      refine ⟨Set.univ, univ_mem, μ, trivial, ?_⟩
      rintro - ⟨f, -, y, hy, rfl⟩
      exact (N μ).smul_mem f hy
    have hleft : ∀ (f : R) {μ : κ}, True →
        ∃ ν : κ, True ∧ Set.MapsTo (f • ·) (N ν : Set M) (N μ : Set M) :=
      fun f {μ} _ ↦ ⟨μ, trivial, fun y hy ↦ (N μ).smul_mem f hy⟩
    have hright : ∀ (x : M) {μ : κ}, True → ∀ᶠ f in 𝓝 (0 : R), f • x ∈ (N μ : Set M) := by
      intro x μ _
      obtain ⟨l, hl⟩ := h x μ
      exact mem_of_superset (hI.mem_of_mem (i := l) trivial) fun f hf ↦ hl f hf
    exact ContinuousSMul.of_basis_zero hN hsmul hleft hright

/-- **Tag 0AMR.** The displayed form of the continuity of `R × M → M`: for all `f`, `x` and `μ`
there are `λ` and `ν` with `(f + I λ) • (x + N ν) ⊆ f • x + N μ`. The source deduces it from
`TopologicalModule.continuousSMul_iff_forall_exists_smul_mem` using that `f • N ν + I λ • N ν ⊆
N μ` whenever `N ν ⊆ N μ`; here `ν = μ` always works. -/
@[stacks 0AMR "scalar_continuity_criterion"]
theorem continuousSMul_iff_forall_exists_coset_smul_coset
    (hI : (𝓝 (0 : R)).HasBasis (fun _ : ι ↦ True) fun l ↦ (I l : Set R))
    (hN : (𝓝 (0 : M)).HasBasis (fun _ : κ ↦ True) fun m ↦ (N m : Set M)) :
    ContinuousSMul R M ↔ ∀ (f : R) (x : M) (μ : κ), ∃ (l : ι) (ν : κ),
      ∀ g ∈ I l, ∀ y ∈ N ν, (f + g) • (x + y) - f • x ∈ N μ := by
  rw [continuousSMul_iff_forall_exists_smul_mem I N hI hN]
  constructor
  · intro h f x μ
    obtain ⟨l, hl⟩ := h x μ
    refine ⟨l, μ, fun g hg y hy ↦ ?_⟩
    rw [show (f + g) • (x + y) - f • x = f • y + (g • x + g • y) by
      simp only [add_smul, smul_add]
      abel]
    exact (N μ).add_mem ((N μ).smul_mem f hy)
      ((N μ).add_mem (hl g hg) ((N μ).smul_mem g hy))
  · intro h x μ
    obtain ⟨l, ν, hlν⟩ := h 0 x μ
    refine ⟨l, fun g hg ↦ ?_⟩
    simpa using hlν g hg 0 (N ν).zero_mem

end TopologicalModule

end
