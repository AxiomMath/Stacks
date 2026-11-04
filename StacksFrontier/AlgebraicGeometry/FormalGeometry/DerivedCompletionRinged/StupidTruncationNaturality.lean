module

public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# Naturality of the stupid filtration

Let `K` be a cochain complex indexed by `ℤ` and let `σ^{≥p}K` be its brutal truncations, which
form the stupid filtration `⋯ ⊆ σ^{≥p+1}K ⊆ σ^{≥p}K ⊆ ⋯` with successive quotients the single
complexes `Kᵖ[-p]`. This file records that the whole structure is natural in `K`: a map of
complexes `φ : K ⟶ L` restricts to every truncation, commutes with the inclusions
`σ^{≥b}K ⟶ σ^{≥a}K`, and induces on the quotient `Kᵖ[-p]` the map `(φᵖ)[-p]`. Together with the
short exactness of `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ 0`
(`StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact`), this is what an induction
along the stupid filtration of a tower of complexes consumes.

## Main results

* `StacksDraft.StupidTruncation.stupidTruncMap_comp_stupidTruncGEMapLE`: the restriction of a map
  of complexes to the truncations commutes with the inclusions of the filtration.
* `StacksDraft.StupidTruncation.stupidTruncMap_comp_stupidTruncGEπ`: the projection of `σ^{≥p}K`
  onto `Kᵖ[-p]` is natural in `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

attribute [local instance] mono_ιStupidTrunc

/-- **The restriction of a map of complexes to the stupid truncations commutes with the
inclusions of the stupid filtration.** Both composites become the restriction of the map to
`σ^{≥b}K` after the inclusion into `L`, which is a monomorphism. -/
@[reassoc]
theorem stupidTruncMap_comp_stupidTruncGEMapLE {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    {a b : ℤ} (h : a ≤ b) :
    stupidTruncMap φ (embeddingUpIntGE b) ≫ stupidTruncGEMapLE L h =
      stupidTruncGEMapLE K h ≫ stupidTruncMap φ (embeddingUpIntGE a) := by
  apply (cancel_mono (ιStupidTrunc L (embeddingUpIntGE a))).1
  rw [Category.assoc, Category.assoc, stupidTruncGEMapLE_ι, stupidTruncMap_ιStupidTrunc,
    stupidTruncMap_ιStupidTrunc, ← Category.assoc, stupidTruncGEMapLE_ι]

/-- **The projection of the truncation `σ^{≥p}K` onto its bottom term `Kᵖ[-p]` is natural in
`K`**: a map of complexes `φ` induces `(φᵖ)[-p]` on the quotient. -/
@[reassoc]
theorem stupidTruncMap_comp_stupidTruncGEπ {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    stupidTruncMap φ (embeddingUpIntGE p) ≫ stupidTruncGEπ L p =
      stupidTruncGEπ K p ≫ (single C (.up ℤ) p).map (φ.f p) := by
  apply to_single_hom_ext
  have h := congrArg (fun g => g.f p) (stupidTruncMap_ιStupidTrunc (e := embeddingUpIntGE p) φ)
  simp only [comp_f, ιStupidTruncGE_f _ p p le_rfl] at h
  rw [comp_f, comp_f, stupidTruncGEπ_f, stupidTruncGEπ_f, single_map_f_self, ← Category.assoc, h,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

end StacksDraft.StupidTruncation
