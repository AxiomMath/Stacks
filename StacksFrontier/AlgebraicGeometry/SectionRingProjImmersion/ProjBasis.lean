module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The basic opens of positive degree are a basis of `Proj`

For a graded ring `𝒜 = ⨁_{n ≥ 0} 𝒜 n`, Mathlib's `AlgebraicGeometry.Proj.isBasis_basicOpen` says
the opens `D₊(g)` form a basis of `Proj 𝒜` as `g` ranges over **all** of the ring. This file
sharpens that to the homogeneous `g` of **positive degree**, which is the only shape in which the
charts of `Proj` are available: `AlgebraicGeometry.Proj.basicOpenIsoSpec` and
`AlgebraicGeometry.Proj.awayι` both ask for a positive degree.

The sharpening is two of Mathlib's own facts put together. `Proj.basicOpen_eq_iSup_proj` writes
`D₊(g)` as the union of the `D₊` of the homogeneous components of `g`, so a point of `D₊(g)` lies
in `D₊(h)` for some homogeneous `h` — of possibly zero degree. The homogeneous elements of
positive degree generate the irrelevant ideal, so by `Proj.iSup_basicOpen_eq_top` their basic
opens cover `Proj 𝒜`, and the point lies in `D₊(b)` for some `b` of positive degree; then
`D₊(h b) = D₊(h) ⊓ D₊(b)` contains the point, is contained in `D₊(g)`, and `h b` is homogeneous of
positive degree.

## Main results

* `Stacks.AlgebraicGeometry.ProjBasis.iSup_basicOpen_pos_eq_top`: **the basic opens of the
  homogeneous elements of positive degree cover `Proj 𝒜`.**
* `Stacks.AlgebraicGeometry.ProjBasis.exists_pos_basicOpen_le`: **they are a basis**: every point
  of an open `W` lies in a `D₊(s)` inside `W` with `s` homogeneous of positive degree.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjBasis

universe u w

variable {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The basic opens of the homogeneous elements of positive degree cover `Proj 𝒜`.** The
homogeneous elements of positive degree span the irrelevant ideal: a ring element with vanishing
degree-zero component is the sum of its remaining homogeneous components, each of which is one of
them. `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top` then applies. -/
theorem iSup_basicOpen_pos_eq_top :
    ⨆ c : {s : R // ∃ j : ℕ, 0 < j ∧ s ∈ 𝒜 j}, Proj.basicOpen 𝒜 (c : R) = ⊤ := by
  classical
  refine Proj.iSup_basicOpen_eq_top 𝒜 (fun c : {s : R // ∃ j : ℕ, 0 < j ∧ s ∈ 𝒜 j} ↦ (c : R))
    fun x hx ↦ ?_
  have hx0 : GradedRing.proj 𝒜 0 x = 0 := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mp hx
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  by_cases h0 : i = 0
  · subst h0
    have hz : ((DirectSum.decompose 𝒜 x 0 : 𝒜 0) : R) = 0 := by
      rw [← GradedRing.proj_apply]; exact hx0
    rw [hz]
    exact Ideal.zero_mem _
  · exact Ideal.subset_span
      ⟨⟨_, i, Nat.pos_of_ne_zero h0, SetLike.coe_mem (DirectSum.decompose 𝒜 x i)⟩, rfl⟩

/-- **The basic opens of the homogeneous elements of positive degree are a basis of `Proj 𝒜`.**
Every point of an open `W` lies in a basic open `D₊(s)` contained in `W`, with `s` homogeneous of
positive degree. -/
@[ega "II 2.3.4"]
theorem exists_pos_basicOpen_le (W : (Proj 𝒜).Opens) {x : Proj 𝒜} (hx : x ∈ W) :
    ∃ (j : ℕ) (s : R), 0 < j ∧ s ∈ 𝒜 j ∧ x ∈ Proj.basicOpen 𝒜 s ∧
      Proj.basicOpen 𝒜 s ≤ W := by
  classical
  obtain ⟨w, ⟨V, hVB, rfl⟩, hxg, hgW⟩ :=
    (Proj.isBasis_basicOpen 𝒜).exists_subset_of_mem_open hx W.2
  obtain ⟨g, rfl⟩ := hVB
  have hgW' : Proj.basicOpen 𝒜 g ≤ W := hgW
  have hdec : Proj.basicOpen 𝒜 g = ⨆ i : ℕ, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i g) :=
    Proj.basicOpen_eq_iSup_proj 𝒜 g
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hdec ▸ hxg)
  have hple : Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i g) ≤ Proj.basicOpen 𝒜 g := by
    rw [hdec]
    exact le_iSup (fun i : ℕ ↦ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i g)) i
  have hbtop : x ∈ (⨆ c : {s : R // ∃ j : ℕ, 0 < j ∧ s ∈ 𝒜 j}, Proj.basicOpen 𝒜 (c : R)) := by
    rw [iSup_basicOpen_pos_eq_top 𝒜]; trivial
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hbtop
  obtain ⟨jb, hjb, hbmem⟩ := b.2
  have hmem : GradedRing.proj 𝒜 i g ∈ 𝒜 i := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  refine ⟨i + jb, GradedRing.proj 𝒜 i g * b.1, by omega,
    SetLike.mul_mem_graded hmem hbmem, ?_, ?_⟩
  · rw [Proj.basicOpen_mul]; exact ⟨hi, hb⟩
  · rw [Proj.basicOpen_mul]
    exact le_trans inf_le_left (hple.trans hgW')

end Stacks.AlgebraicGeometry.ProjBasis

end
