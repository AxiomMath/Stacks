module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLE

/-!
# Degreewise isomorphy of the canonical truncation maps

Let `e : c.Embedding c'` be an embedding of complex shapes and `K : HomologicalComplex C c'`.
The canonical maps `K.πTruncGE e` and `K.ιTruncLE e` are isomorphisms in every degree in the
image of `e` that is not a boundary degree, with no support hypothesis on `K`.

## Main results

* `HomologicalComplex.isIso_πTruncGE_f`: `(K.πTruncGE e).f i'` is an isomorphism when
  `e.f i = i'` and `i` is not an `e.BoundaryGE` degree.
* `HomologicalComplex.isIso_ιTruncLE_f`: `(K.ιTruncLE e).f i'` is an isomorphism when
  `e.f i = i'` and `i` is not an `e.BoundaryLE` degree.
* `CochainComplex.isIso_ιTruncLE_f_of_lt`: for `K : CochainComplex C ℤ`, the map
  `(K.ιTruncLE n).f i` is an isomorphism whenever `i < n`.
* `CochainComplex.epi_ιTruncLE_f_of_lt`: the same map is in particular an epimorphism
  whenever `i < n`.
* `CochainComplex.isIso_πTruncGE_f_of_lt`: for `K : CochainComplex C ℤ`, the map
  `(K.πTruncGE n).f i` is an isomorphism whenever `n < i`.
-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject ComplexShape

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex C c') [∀ i', K.HasHomology i']

/-- The canonical projection `K ⟶ K.truncGE e` is an isomorphism in every degree `i'` of
the form `e.f i` for a non-boundary degree `i`. -/
lemma isIso_πTruncGE_f (e : c.Embedding c') [e.IsTruncGE] {i : ι} {i' : ι'}
    (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.πTruncGE e).f i') := by
  change IsIso ((e.liftExtend (K.restrictionToTruncGE' e)
    (K.restrictionToTruncGE'_hasLift e)).f i')
  rw [e.isIso_liftExtend_f_iff _ _ hi']
  exact K.isIso_restrictionToTruncGE' e i hi

/-- The canonical inclusion `K.truncLE e ⟶ K` is an isomorphism in every degree `i'` of
the form `e.f i` for a non-boundary degree `i`. -/
lemma isIso_ιTruncLE_f (e : c.Embedding c') [e.IsTruncLE] {i : ι} {i' : ι'}
    (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.ιTruncLE e).f i') := by
  have := K.op.isIso_πTruncGE_f e.op hi'
    (by simpa only [Embedding.op_boundaryGE_iff] using hi)
  exact inferInstanceAs (IsIso ((K.op.πTruncGE e.op).f i').unop)

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℤ) [∀ i, K.HasHomology i]

/-- For a cochain complex `K`, the canonical inclusion `K.truncLE n ⟶ K` is an isomorphism in
every degree strictly below `n`. -/
lemma isIso_ιTruncLE_f_of_lt (n i : ℤ) (hi : i < n) : IsIso ((K.ιTruncLE n).f i) := by
  have hf : (embeddingUpIntLE n).f (n - i).natAbs = i := by
    change n - ((n - i).natAbs : ℤ) = i
    lia
  have hb : ¬ (embeddingUpIntLE n).BoundaryLE (n - i).natAbs := by
    rw [boundaryLE_embeddingUpIntLE_iff]
    lia
  exact K.isIso_ιTruncLE_f (embeddingUpIntLE n) hf hb

/-- The canonical inclusion `K.truncLE n ⟶ K` is an epimorphism in every degree strictly
below `n`. -/
lemma epi_ιTruncLE_f_of_lt (n i : ℤ) (hi : i < n) : Epi ((K.ιTruncLE n).f i) :=
  have := K.isIso_ιTruncLE_f_of_lt n i hi
  inferInstance

/-- For a cochain complex, the canonical projection `K ⟶ K.truncGE n` is an isomorphism in every
degree strictly above `n`. -/
lemma isIso_πTruncGE_f_of_lt (n i : ℤ) (hi : n < i) : IsIso ((K.πTruncGE n).f i) := by
  have hf : (embeddingUpIntGE n).f (i - n).natAbs = i := by
    change n + ((i - n).natAbs : ℤ) = i
    lia
  have hb : ¬ (embeddingUpIntGE n).BoundaryGE (i - n).natAbs := by
    rw [boundaryGE_embeddingUpIntGE_iff]
    lia
  exact K.isIso_πTruncGE_f (embeddingUpIntGE n) hf hb

end CochainComplex

end
