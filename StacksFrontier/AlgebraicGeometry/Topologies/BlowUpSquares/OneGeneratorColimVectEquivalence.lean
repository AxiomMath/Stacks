module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap

/-!
# The induced functor on the colimit categories carries the stage shift

Let `F : C ⥤ C` and `F' : C' ⥤ C'` be endofunctors and let `Φ : C ⥤ C'` commute with them up to
a natural isomorphism `α : F ⋙ Φ ≅ Φ ⋙ F'`, so that `CategoryTheory.EndoColim.map` is the
induced functor `colim_F C ⥤ colim_{F'} C'` between the colimit categories of Stacks Tag 0EXA.
This file computes that functor on the stage shift `(F^k E, n + k) ≅ (E, n)` of Tag 0EXA.

## Main results

* `CategoryTheory.EndoColim.Pseudococone.desc_map_shiftStepHom`: the functor determined by a
  pseudo-cocone carries the one-step stage shift to the pseudo-cocone's own comparison.
* `CategoryTheory.EndoColim.Pseudococone.desc_map_objShiftIso_hom`: the functor determined by a
  pseudo-cocone carries the iterated stage shift to the comparison of the stage functors along
  iterates.
* `CategoryTheory.EndoColim.map_objShiftIso_hom`: **the induced functor carries the stage shift
  of `colim_F C` to the stage shift of `colim_{F'} C'`**, conjugated by the iterated comparison
  `CategoryTheory.EndoColim.squareIter`.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u u₂

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {F : C ⥤ C} {D : Type*} [Category D]

namespace Pseudococone

/-- **The functor determined by a pseudo-cocone carries the one-step stage shift of `colim_F C`
to the pseudo-cocone's own comparison.** The shift `(F E, n + 1) ≅ (E, n)` of Stacks Tag 0EXA is
presented at level `0` by a transport of objects, and the induced morphism of `D` is the
comparison `F ⋙ S_{n + 1} ≅ S_n` carried by the pseudo-cocone, by the invariance of
`CategoryTheory.EndoColim.Pseudococone.mapAt` under raising the presenting morphism. -/
lemma desc_map_shiftStepHom (P : Pseudococone F D) (m : ℕ) (X : C) :
    P.desc.map (shiftStepHom F m X) = (P.compat m).hom.app X := by
  have key := P.mapAt_endoHomCast_endoRaise (m + 1) m 0 1 (by omega)
    (eqToHom (F.endoIter_obj_obj 0 X)) m (m + 0) (m + 1 + 0) (by omega) (by omega) (by omega)
  rw [endoRaise_eqToHom, endoHomCast_eqToHom] at key
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · have hid : eqToHom (F.endoIter_obj_obj 0 X) = 𝟙 (F.obj X) := rfl
    rw [mapAt, hid]
    simp [iterObjIso, compatIter]

/-- **The functor determined by a pseudo-cocone carries the iterated stage shift of `colim_F C`
to the comparison of the stage functors along iterates of `F`.** Both isomorphisms are the
one-step comparison iterated, so this is
`CategoryTheory.EndoColim.Pseudococone.desc_map_shiftStepHom` at every step. -/
lemma desc_map_objShiftIso_hom (P : Pseudococone F D) (n : ℕ) : ∀ (k : ℕ) (E : C),
    P.desc.map (objShiftIso F n k E).hom = (P.iterObjIso n k E).hom
  | 0, E => P.desc.map_id (⟨E, n⟩ : EndoColim F)
  | k + 1, E => by
      show P.desc.map ((shiftStepIso F (n + k) ((F.endoIter k).obj E)).hom ≫
          (objShiftIso F n k E).hom) = (P.compatIter n k E).hom ≫ (P.iterObjIso n k E).hom
      rw [Functor.map_comp, shiftStepIso_hom, desc_map_shiftStepHom,
        desc_map_objShiftIso_hom P n k E]
      rfl

end Pseudococone

variable {C' : Type u₂} [Category.{v} C']

/-- **The induced functor carries the stage shift of `colim_F C` to the stage shift of
`colim_{F'} C'`**, conjugated by the iterated comparison. The functor
`CategoryTheory.EndoColim.map` is the one determined by
`CategoryTheory.EndoColim.mapPseudococone`, so this is
`CategoryTheory.EndoColim.Pseudococone.desc_map_objShiftIso_hom` for that pseudo-cocone together
with the computation `CategoryTheory.EndoColim.mapPseudococone_iterObjIso_hom` of the comparison
it carries. -/
lemma map_objShiftIso_hom (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')
    (n k : ℕ) (E : C) :
    (map F F' Φ α).map (objShiftIso F n k E).hom =
      stageHomOf F' (n + k) (squareIter F F' Φ α k E).inv ≫
        (objShiftIso F' n k (Φ.obj E)).hom :=
  (Pseudococone.desc_map_objShiftIso_hom (mapPseudococone F F' Φ α) n k E).trans
    (mapPseudococone_iterObjIso_hom F F' Φ α n k E)

end CategoryTheory.EndoColim

end
