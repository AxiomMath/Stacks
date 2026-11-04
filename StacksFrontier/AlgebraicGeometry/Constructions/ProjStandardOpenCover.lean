module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard open coverings of the homogeneous spectrum

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring. A *standard open covering* of a projective standard
open `D₊(f)` is a finite family of standard opens `D₊(gᵢ)` whose union is `D₊(f)`, where `f` and
all the `gᵢ` are homogeneous of positive degree.

A quasi-compact open of `Proj 𝒜` can always be covered by finitely many standard opens whose
defining elements share one positive degree: the standard opens of all positive-degree
homogeneous elements cover `Proj 𝒜`, so quasi-compactness extracts a finite subfamily, and
raising each member to a suitable power — which does not change its standard open — makes the
degrees equal to their product.

## Main definitions

* `ProjectiveSpectrum.IsStandardOpenCover`: a finite standard open covering of `D₊(f)`.
* `AlgebraicGeometry.Proj.CommonDegreeCover`: a positive degree, a finite family of homogeneous
  elements of that degree, and the resulting cover of a given open.
* `AlgebraicGeometry.Proj.commonDegreeCover`: a chosen such package for a quasi-compact open.

## Main results

* `AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover`: a quasi-compact open of
  `Proj 𝒜` has a finite standard-open cover whose defining homogeneous elements all have the
  same positive degree.

## Implementation notes

In `IsStandardOpenCover` the finite family is indexed by `Fin n`, positive-degree homogeneity is
expressed by the existence of a positive degree, and the covering condition is an equality of
opens of `Proj 𝒜`; the definition is an `abbrev` so that clients see those three clauses
directly.

In `CommonDegreeCover` the finite family is instead a `Finset` of elements of the graded ring,
since the construction produces it as the image of a finite subcover and the indexing is
immaterial. Intersecting each standard open with the given open `Y` records the cover as an
equality of opens of `Proj 𝒜`, which is the form its consumers use. The bundled version exposes
the chosen degree and its positivity, the family and its homogeneity, and the covering equality
as structure projections.

## References

* [Stacks Project, Tag 01M5](https://stacks.math.columbia.edu/tag/01M5)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
-/

@[expose] public section

namespace ProjectiveSpectrum

universe u v

/-- A finite family of positive-degree homogeneous elements `gᵢ` gives a standard open
covering of the projective standard open `D₊(f)` when their standard opens have union
exactly `D₊(f)`. -/
@[stacks 01M5] public abbrev IsStandardOpenCover {A : Type u} {σ : Type v}
    [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : A) {n : ℕ} (g : Fin n → A) : Prop :=
  (∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) ∧ (∀ i, ∃ e : ℕ, 0 < e ∧ g i ∈ 𝒜 e) ∧
    ProjectiveSpectrum.basicOpen 𝒜 f = ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (g i)

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

universe u w

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite standard-open cover of an open `Y ⊆ Proj 𝒜` defined by homogeneous elements of one
common positive degree. -/
public structure CommonDegreeCover (Y : (Proj 𝒜).Opens) where
  /-- The common degree of the defining elements. -/
  degree : ℕ
  /-- The common degree is positive. -/
  degree_pos : 0 < degree
  /-- The finite family of elements defining the standard opens. -/
  sections : Finset A
  /-- Every defining element is homogeneous of the common degree. -/
  sections_mem : ∀ f ∈ sections, f ∈ 𝒜 degree
  /-- The intersections with the standard opens cover `Y`. -/
  iSup_basicOpen_inf_eq :
    (⨆ f ∈ sections, Proj.basicOpen 𝒜 f ⊓ Y) = Y

/-- A quasi-compact open of `Proj 𝒜` has a finite cover by standard opens defined by homogeneous
elements of one common positive degree. -/
@[ega "IV 18.12.17" "partial"]
public theorem exists_common_degree_finite_basicOpen_cover
    (Y : (Proj 𝒜).Opens) (hY : IsCompact (Y : Set (Proj 𝒜))) :
    ∃ d : ℕ, 0 < d ∧ ∃ s : Finset A,
      (∀ f ∈ s, f ∈ 𝒜 d) ∧
        Y = ⨆ f ∈ s, Proj.basicOpen 𝒜 f ⊓ Y := by
  classical
  let I := Σ i : PNat, 𝒜 i
  let U : I → (Proj 𝒜).Opens := fun i ↦ Proj.basicOpen 𝒜 i.2
  have hU : (⨆ i, U i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    intro z hz
    rw [← DirectSum.sum_support_decompose 𝒜 z]
    refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
      Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
    · convert Ideal.zero_mem _
      subst hc0
      exact hz
  have hYU : (Y : Set (Proj 𝒜)) ⊆ ⋃ i, (U i : Set (Proj 𝒜)) := by
    intro x hx
    have hx' : x ∈ ⨆ i, U i := hU.symm ▸ Set.mem_univ x
    exact Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp hx')
  obtain ⟨t, ht⟩ := hY.elim_finite_subcover
    (fun i ↦ (U i : Set (Proj 𝒜))) (fun i ↦ (U i).isOpen) hYU
  let d : ℕ := ∏ i ∈ t, (i.1 : ℕ)
  have hd : 0 < d := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ i.1.ne_zero)
  have hdvd : ∀ i ∈ t, (i.1 : ℕ) ∣ d := fun i hi ↦
    Finset.dvd_prod_of_mem (fun j : I ↦ (j.1 : ℕ)) hi
  let F : I → A := fun i ↦ (i.2 : A) ^ (d / (i.1 : ℕ))
  refine ⟨d, hd, t.image F, ?_, le_antisymm ?_ (iSup_le fun _ ↦ iSup_le fun _ ↦ inf_le_right)⟩
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    simpa [F, Nat.div_mul_cancel (hdvd i hi)] using
      SetLike.pow_mem_graded (A := 𝒜) (d / (i.1 : ℕ)) i.2.property
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hpow : 0 < d / (i.1 : ℕ) := Nat.div_pos (Nat.le_of_dvd hd (hdvd i hi)) i.1.2
    simp only [TopologicalSpace.Opens.mem_iSup]
    refine ⟨F i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_, hx⟩
    simpa [U, F, Proj.basicOpen_pow 𝒜 (i.2 : A) _ hpow] using hxi

/-- A chosen common-degree finite standard-open cover of a quasi-compact open of `Proj 𝒜`. -/
public noncomputable def commonDegreeCover
    (Y : (Proj 𝒜).Opens) (hY : IsCompact (Y : Set (Proj 𝒜))) :
    CommonDegreeCover 𝒜 Y :=
  let h := exists_common_degree_finite_basicOpen_cover 𝒜 Y hY
  { degree := h.choose
    degree_pos := h.choose_spec.1
    sections := h.choose_spec.2.choose
    sections_mem := h.choose_spec.2.choose_spec.1
    iSup_basicOpen_inf_eq := h.choose_spec.2.choose_spec.2.symm }

end AlgebraicGeometry.Proj
