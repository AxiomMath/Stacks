module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relevant basic opens of `Proj 𝒜`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring. The standard opens `D₊(f) ⊆ Proj 𝒜` that the Stacks
project uses are the ones attached to a *homogeneous element of positive degree*; Mathlib's
`AlgebraicGeometry.Proj.basicOpen 𝒜 f` is defined for an arbitrary `f : A`, and the basis
statement `AlgebraicGeometry.Proj.isBasis_basicOpen` lets `f` range over all of `A`.

This file records the sharp statements, where `f` ranges only over the homogeneous elements of
positive degree. There are three, in increasing strength:

* every point of `Proj 𝒜` lies outside some homogeneous ideal generator of positive degree;
* the `D₊(f)` for such `f` cover `Proj 𝒜`;
* they form a basis of the topology of `Proj 𝒜`, so every open is their union.

## Main results

* `Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem`: a point of `Proj 𝒜`
  omits some homogeneous element of positive degree.
* `Stacks.AlgebraicGeometry.ProjShared.iSup_basicOpen_homogeneous_eq_top`: the relevant
  standard opens cover `Proj 𝒜`, in the `⨆ (n) (_ : 0 < n) (f : 𝒜 n)` shape.
* `Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le`: between a point and
  an open containing it there is a relevant standard open.
* `Stacks.AlgebraicGeometry.ProjShared.isBasis_basicOpen_homogeneous`: the relevant standard
  opens form a basis.
* `Stacks.AlgebraicGeometry.ProjShared.eq_iSup_basicOpen_homogeneous`: consequently every open
  is the union of the relevant standard opens it contains.

## Implementation notes

The first result is exactly the relevance condition `ProjectiveSpectrum.not_irrelevant_le` read
through `HomogeneousIdeal.irrelevant_le`, and the covering statement is the pointwise reading of
it. Both are also consequences of Mathlib's `AlgebraicGeometry.Proj.affineOpenCover`, whose
index type `Σ n : ℕ+, 𝒜 n` is the same data; what is new is the `⨆`-of-`Opens` form, which is
the form in which a locus defined as a supremum of standard opens is compared with `⊤`.

The basis statement is proved by sharpening Mathlib's: an arbitrary `f : A` is replaced by the
homogeneous component of `f` that the given point omits, and that component — which may have
degree zero — is multiplied by a positive-degree homogeneous element the point also omits. The
multiplication both raises the degree above zero and shrinks the standard open, by
`AlgebraicGeometry.Proj.basicOpen_mul`, so no case distinction on the degree of the component
is needed.

The grading is taken as a family `𝒜 : ℕ → σ` of elements of a `SetLike` type with
`AddSubgroupClass σ A`, which is the generality of Mathlib's `Proj` and of the Stacks source; in
particular `A : Type u` and `σ : Type w` live in independent universes.

## References

* [Stacks Project, Tag 01M5](https://stacks.math.columbia.edu/tag/01M5)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public section

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjShared

universe u w

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A point of `Proj 𝒜` is a homogeneous prime that does not contain the irrelevant ideal, hence
omits some homogeneous element of positive degree. -/
public theorem exists_homogeneous_pos_notMem (x : Proj 𝒜) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ f ∉ x.asHomogeneousIdeal := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact x.not_irrelevant_le <| (HomogeneousIdeal.irrelevant_le 𝒜).mpr
    fun i hi f hf => hcon i f hi hf

/-- The standard opens `D₊(f)` of the homogeneous elements `f` of positive degree cover
`Proj 𝒜`. This is the sharp form of `AlgebraicGeometry.Proj.isBasis_basicOpen`'s covering
consequence: `f` ranges only over the relevant homogeneous elements. -/
@[ega "II 3.1.6" "special case"]
public theorem iSup_basicOpen_homogeneous_eq_top :
    (⨆ (n : ℕ) (_ : 0 < n) (f : 𝒜 n), Proj.basicOpen 𝒜 (f : A)) = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨n, f, hn, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  simp only [TopologicalSpace.Opens.mem_iSup, Proj.mem_basicOpen]
  exact ⟨n, hn, ⟨f, hf⟩, hfx⟩

/-- Membership in a supremum of standard opens of positive-degree homogeneous elements. -/
public theorem mem_iSup_basicOpen_homogeneous_iff (x : Proj 𝒜) :
    x ∈ (⨆ (n : ℕ) (_ : 0 < n) (f : 𝒜 n), Proj.basicOpen 𝒜 (f : A)) ↔
      ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ f ∉ x.asHomogeneousIdeal := by
  simp only [TopologicalSpace.Opens.mem_iSup, Proj.mem_basicOpen,
    Subtype.exists]
  exact ⟨fun ⟨n, hn, f, hf, hfx⟩ => ⟨n, f, hn, hf, hfx⟩,
    fun ⟨n, f, hn, hf, hfx⟩ => ⟨n, hn, f, hf, hfx⟩⟩

/-- Between a point of `Proj 𝒜` and an open containing it there is a standard open `D₊(f)` of a
homogeneous `f` of positive degree. -/
public theorem exists_basicOpen_homogeneous_le {U : (Proj 𝒜).Opens} {x : Proj 𝒜} (hx : x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ x ∈ Proj.basicOpen 𝒜 f ∧
      Proj.basicOpen 𝒜 f ≤ U := by
  obtain ⟨V, ⟨r, rfl⟩, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜) hx
  obtain ⟨m, g, hm, hg, hgx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  rw [Proj.basicOpen_eq_iSup_proj 𝒜 r] at hxV hVU
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
  have hri : GradedRing.proj 𝒜 i r ∈ 𝒜 i := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  have hle : Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i r) ≤ U :=
    le_trans (le_iSup (fun j : ℕ => Proj.basicOpen 𝒜
      (GradedRing.proj 𝒜 j r)) i) hVU
  refine ⟨i + m, GradedRing.proj 𝒜 i r * g, by omega, SetLike.mul_mem_graded hri hg, ?_, ?_⟩
  · rw [Proj.basicOpen_mul]
    exact ⟨hxi, hgx⟩
  · exact (Proj.basicOpen_mul 𝒜 _ g).le.trans (inf_le_left.trans hle)

/-- The standard opens `D₊(f)` of the homogeneous elements `f` of positive degree form a basis of
the topology of `Proj 𝒜`. This is the sharp form of
`AlgebraicGeometry.Proj.isBasis_basicOpen`, which lets `f` range over all of `A`. -/
@[ega "II 2.3.4"]
public theorem isBasis_basicOpen_homogeneous :
    TopologicalSpace.Opens.IsBasis
      (Set.range fun f : Σ n : ℕ+, 𝒜 (n : ℕ) =>
        Proj.basicOpen 𝒜 (f.2 : A)) := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hx => ?_
  obtain ⟨n, f, hn, hf, hxf, hfU⟩ := exists_basicOpen_homogeneous_le 𝒜 hx
  exact ⟨_, ⟨⟨⟨n, hn⟩, ⟨f, hf⟩⟩, rfl⟩, hxf, hfU⟩

/-- Every open of `Proj 𝒜` is the union of the standard opens of positive-degree homogeneous
elements that it contains. -/
public theorem eq_iSup_basicOpen_homogeneous (U : (Proj 𝒜).Opens) :
    U = ⨆ (n : ℕ) (_ : 0 < n) (f : 𝒜 n)
      (_ : Proj.basicOpen 𝒜 (f : A) ≤ U),
      Proj.basicOpen 𝒜 (f : A) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨n, f, hn, hf, hxf, hfU⟩ := exists_basicOpen_homogeneous_le 𝒜 hx
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨n, hn, ⟨f, hf⟩, hfU, hxf⟩
  · exact iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun h => h

end Stacks.AlgebraicGeometry.ProjShared

end
