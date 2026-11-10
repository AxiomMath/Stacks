module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Morphisms out of an extended complex

Let `e : c.Embedding c'` be an embedding of complex shapes which is truncating from below
(`ComplexShape.Embedding.IsTruncGE`, e.g. `ComplexShape.embeddingUpNat`). For a complex `K`
indexed by `c` and a complex `L` indexed by `c'`, a morphism `φ : K ⟶ L.restriction e` extends
to a morphism `K.extend e ⟶ L`: in the degrees of the image of `e` it is `φ`, and the other
terms of `K.extend e` are zero. Mathlib provides the dual construction,
`ComplexShape.Embedding.liftExtend`, of morphisms *into* an extended complex.

## Main definitions

* `ComplexShape.Embedding.descExtend`: the morphism `K.extend e ⟶ L` induced by
  `φ : K ⟶ L.restriction e`.

## Main results

* `ComplexShape.Embedding.descExtend_f`: in a degree `e.f i`, the component of `descExtend` is
  `φ.f i`, read through the canonical identifications of the terms.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

open HomologicalComplex

variable {K : HomologicalComplex C c} {L : HomologicalComplex C c'}

namespace descExtend

variable [e.IsRelIff] (φ : K ⟶ L.restriction e)

open scoped Classical in
/-- Auxiliary definition for `ComplexShape.Embedding.descExtend`. -/
noncomputable def f (i' : ι') : (K.extend e).X i' ⟶ L.X i' :=
  if hi' : ∃ i, e.f i = i' then
    (K.extendXIso e hi'.choose_spec).hom ≫ φ.f hi'.choose ≫
      (L.restrictionXIso e hi'.choose_spec).hom
  else 0

variable {e} in
/-- In a degree `e.f i`, the map `f e φ` is `φ.f i`, read through the identifications of
`(K.extend e).X (e.f i)` with `K.X i` and of `(L.restriction e).X i` with `L.X (e.f i)`. -/
lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f e φ i' = (K.extendXIso e hi).hom ≫ φ.f i ≫ (L.restrictionXIso e hi).hom := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  obtain rfl : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  exact dite_eq_left hi'

/-- The maps `f e φ` commute with the differentials. -/
lemma comm [e.IsTruncGE] (i' j' : ι') :
    f e φ i' ≫ L.d i' j' = (K.extend e).d i' j' ≫ f e φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      obtain ⟨j, hj⟩ := e.mem_next (hi ▸ hij' : c'.Rel (e.f i) j')
      rw [f_eq φ hi, f_eq φ hj, K.extend_d_eq e hi hj]
      have hc := φ.comm i j
      rw [L.restriction_d_eq e hi hj] at hc
      have hc' : φ.f i ≫ (L.restrictionXIso e hi).hom ≫ L.d i' j' =
          K.d i j ≫ φ.f j ≫ (L.restrictionXIso e hj).hom := by
        rw [← reassoc_of% hc]
        simp
      simp only [assoc, Iso.inv_hom_id_assoc]
      rw [hc']
    · exact (K.isZero_extend_X e i' (by simpa using hi')).eq_of_src _ _
  · rw [L.shape _ _ hij', (K.extend e).shape _ _ hij', comp_zero, zero_comp]

end descExtend

variable [e.IsTruncGE] (φ : K ⟶ L.restriction e)

/-- **The morphism `K.extend e ⟶ L` induced by a morphism `φ : K ⟶ L.restriction e`**, for an
embedding `e` truncating from below: `φ` in the degrees of the image of `e`, and zero on the
other (zero) terms of `K.extend e`. -/
noncomputable def descExtend : K.extend e ⟶ L where
  f i' := descExtend.f e φ i'
  comm' i' j' _ := descExtend.comm e φ i' j'

variable {e} in
/-- In a degree `e.f i`, the component of `descExtend e φ` is `φ.f i`, read through the
identifications of the terms. -/
lemma descExtend_f {i' : ι'} {i : ι} (hi : e.f i = i') :
    (e.descExtend φ).f i' = (K.extendXIso e hi).hom ≫ φ.f i ≫ (L.restrictionXIso e hi).hom :=
  descExtend.f_eq φ hi

end ComplexShape.Embedding

end
