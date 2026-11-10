module

public import StacksFrontier.Algebra.Homology.Embedding.MapExtend07Q9

/-!
# The components of `HomologicalComplex.mapExtendIso` in the image of the embedding

Let `e : c.Embedding c'` be an embedding of complex shapes and let `F : C ⥤ D` be a functor
preserving zero morphisms. The isomorphism `HomologicalComplex.mapExtendIso F e K` identifies
`F(K.extend e)` with `(F(K)).extend e`. In a degree `e.f n` of the image of the embedding both
sides are `F` of the term `K.X n`, and the component of the comparison is the identity read through
the two `extendXIso`.

## Main results

* `HomologicalComplex.mapExtendIso_hom_f`, `HomologicalComplex.mapExtendIso_inv_f`: the
  components of the comparison in a degree of the form `e.f n`.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (e : c.Embedding c') (K : HomologicalComplex C c)

/-- The component of `mapExtendIso` in a degree `e.f n` of the image of the embedding: the
identity, read through the two `extendXIso`. -/
lemma mapExtendIso_hom_f (n : ι) (n' : ι') (h : e.f n = n') :
    (mapExtendIso F e K).hom.f n' =
      F.map ((K.extendXIso e h).hom) ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  have hr := e.r_eq_some h
  change (MapExtend.isoX F K (e.r n')).hom =
    F.map (extend.XIso K hr).hom ≫
      (extend.XIso ((F.mapHomologicalComplex c).obj K) hr).inv
  generalize e.r n' = r at hr ⊢
  subst r
  simp only [MapExtend.isoX, extend.XIso, eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans,
    Iso.refl_hom]
  rfl

/-- The component of the inverse of `mapExtendIso` in a degree `e.f n` of the image of the
embedding. -/
lemma mapExtendIso_inv_f (n : ι) (n' : ι') (h : e.f n = n') :
    (mapExtendIso F e K).inv.f n' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map ((K.extendXIso e h).inv) := by
  rw [← cancel_epi ((mapExtendIso F e K).hom.f n'), ← comp_f, Iso.hom_inv_id, id_f,
    mapExtendIso_hom_f F e K n n' h]
  simp [← Functor.map_comp]

end HomologicalComplex

end
