module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatMorphisms

/-!
# Representing objects and morphisms of a filtered colimit of categories at one stage

For a filtered diagram `F : I ⥤ Cat`, `CategoryTheory.Cat.exists_stage_obj_of_colimit` and
`CategoryTheory.Cat.exists_stage_map_of_colimit` represent a single object, resp. a single
morphism, of `colimit F` at a stage of the diagram, but the latter produces the source and the
target of the represented morphism along two possibly different transitions. This file collects
the forms in which those two statements are actually used: one transition rather than two, two
objects at one common stage, and a pair of parallel morphisms at one common stage; and it reads
fullness and essential surjectivity of a functor out of `colimit F` back at a stage.

## Main results

* `CategoryTheory.Cat.exists_common_stage_obj_of_colimit`
* `CategoryTheory.Cat.exists_stage_map_of_colimit_of_eq`
* `CategoryTheory.Cat.exists_stage_map_pair_of_colimit`
* `CategoryTheory.Cat.exists_stage_obj_of_essSurj`
* `CategoryTheory.Cat.exists_stage_map_of_full`

## Implementation notes

Filteredness is what collapses the several stages and transitions these statements start from
into one: `CategoryTheory.IsFiltered.max` for two stages and `CategoryTheory.IsFiltered.coeq`
for two transitions out of one stage. Because a morphism of a stage maps to a morphism between
the *images* of its endpoints, which are only equal to the prescribed objects, the conclusions
are heterogeneous equalities; `CategoryTheory.Cat.transport_hom_of_heq` turns one into an
equation between composites with `eqToHom`.

## References

* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe u v w uD vD

section Stages

variable {I : Type v} [Category.{w} I]
  (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
  [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]

/-- **Two objects of a filtered colimit in `Cat` come from one common stage.** -/
lemma exists_common_stage_obj_of_colimit [IsFiltered I] (x y : ↑(colimit F)) :
    ∃ (i : I) (a b : F.obj i),
      (colimit.ι F i).toFunctor.obj a = x ∧ (colimit.ι F i).toFunctor.obj b = y := by
  obtain ⟨i, a, ha⟩ := exists_stage_obj_of_colimit.{u, v, w} F x
  obtain ⟨k, b, hb⟩ := exists_stage_obj_of_colimit.{u, v, w} F y
  refine ⟨IsFiltered.max i k, (F.map (IsFiltered.leftToMax i k)).toFunctor.obj a,
    (F.map (IsFiltered.rightToMax i k)).toFunctor.obj b, ?_, ?_⟩
  · exact (Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (colimit.w F (IsFiltered.leftToMax i k))) a).trans ha
  · exact (Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (colimit.w F (IsFiltered.rightToMax i k))) b).trans hb

/-- **A morphism of a filtered colimit in `Cat` between images of objects of one stage comes
from a single later stage.** This is `CategoryTheory.Cat.exists_stage_map_of_colimit` with the
two transitions it produces equalised, which filteredness allows. -/
lemma exists_stage_map_of_colimit_of_eq [IsFiltered I]
    (j : I) (a b : F.obj j)
    (f : (colimit.ι F j).toFunctor.obj a ⟶ (colimit.ι F j).toFunctor.obj b) :
    ∃ (k : I) (r : j ⟶ k) (g : (F.map r).toFunctor.obj a ⟶ (F.map r).toFunctor.obj b),
      HEq ((colimit.ι F k).toFunctor.map g) f := by
  obtain ⟨l, s, t, g, hg⟩ := exists_stage_map_of_colimit.{u, v, w} F j j a b f
  have hst : s ≫ IsFiltered.coeqHom s t = t ≫ IsFiltered.coeqHom s t :=
    IsFiltered.coeq_condition s t
  have hcs := congrArg Cat.Hom.toFunctor (F.map_comp s (IsFiltered.coeqHom s t))
  have hct := congrArg Cat.Hom.toFunctor (F.map_comp t (IsFiltered.coeqHom s t))
  have e₁ : (F.map (s ≫ IsFiltered.coeqHom s t)).toFunctor.obj a =
      (F.map (IsFiltered.coeqHom s t)).toFunctor.obj ((F.map s).toFunctor.obj a) :=
    Functor.congr_obj hcs a
  have e₂ : (F.map (IsFiltered.coeqHom s t)).toFunctor.obj ((F.map t).toFunctor.obj b) =
      (F.map (s ≫ IsFiltered.coeqHom s t)).toFunctor.obj b := by
    rw [hst]
    exact (Functor.congr_obj hct b).symm
  refine ⟨IsFiltered.coeq s t, s ≫ IsFiltered.coeqHom s t,
    eqToHom e₁ ≫ (F.map (IsFiltered.coeqHom s t)).toFunctor.map g ≫ eqToHom e₂, ?_⟩
  simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact (Functor.hcongr_hom
    (congrArg Cat.Hom.toFunctor (colimit.w F (IsFiltered.coeqHom s t))) g).trans hg

/-- **A pair of parallel morphisms of a filtered colimit in `Cat` between images of objects of
one stage comes from a single later stage.** Both are represented along one and the same
transition, so that they are again parallel. -/
lemma exists_stage_map_pair_of_colimit [IsFiltered I]
    (j : I) (a b : F.obj j)
    (f g : (colimit.ι F j).toFunctor.obj a ⟶ (colimit.ι F j).toFunctor.obj b) :
    ∃ (k : I) (r : j ⟶ k) (f' g' : (F.map r).toFunctor.obj a ⟶ (F.map r).toFunctor.obj b),
      HEq ((colimit.ι F k).toFunctor.map f') f ∧ HEq ((colimit.ι F k).toFunctor.map g') g := by
  obtain ⟨k₁, r₁, f₁, hf₁⟩ := exists_stage_map_of_colimit_of_eq.{u, v, w} F j a b f
  obtain ⟨k₂, r₂, g₁, hg₁⟩ := exists_stage_map_of_colimit_of_eq.{u, v, w} F j a b g
  set u := IsFiltered.leftToMax k₁ k₂ with hu
  set v := IsFiltered.rightToMax k₁ k₂ with hv
  set e := IsFiltered.coeqHom (r₁ ≫ u) (r₂ ≫ v) with he
  have hcoeq : (r₁ ≫ u) ≫ e = (r₂ ≫ v) ≫ e :=
    IsFiltered.coeq_condition (r₁ ≫ u) (r₂ ≫ v)
  have hw₁ : r₁ ≫ u ≫ e = (r₁ ≫ u) ≫ e := (Category.assoc _ _ _).symm
  have hw₂ : r₂ ≫ v ≫ e = (r₁ ≫ u) ≫ e := (Category.assoc _ _ _).symm.trans hcoeq.symm
  -- the two morphisms, pushed forward to the equalising stage
  have c₁ := congrArg Cat.Hom.toFunctor ((F.map_comp r₁ (u ≫ e)).symm.trans (congrArg F.map hw₁))
  have c₂ := congrArg Cat.Hom.toFunctor ((F.map_comp r₂ (v ≫ e)).symm.trans (congrArg F.map hw₂))
  refine ⟨IsFiltered.coeq (r₁ ≫ u) (r₂ ≫ v), (r₁ ≫ u) ≫ e,
    eqToHom (Functor.congr_obj c₁ a).symm ≫ (F.map (u ≫ e)).toFunctor.map f₁ ≫
      eqToHom (Functor.congr_obj c₁ b),
    eqToHom (Functor.congr_obj c₂ a).symm ≫ (F.map (v ≫ e)).toFunctor.map g₁ ≫
      eqToHom (Functor.congr_obj c₂ b), ?_, ?_⟩
  · simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (Functor.hcongr_hom
      (congrArg Cat.Hom.toFunctor (colimit.w F (u ≫ e))) f₁).trans hf₁
  · simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (Functor.hcongr_hom
      (congrArg Cat.Hom.toFunctor (colimit.w F (v ≫ e))) g₁).trans hg₁

/-- **A pair of parallel morphisms of a filtered colimit in `Cat` comes from one stage.** The
two prescribed endpoints are represented at that stage as well. -/
lemma exists_stage_hom_pair_of_colimit [IsFiltered I] {x y : ↑(colimit F)} (f g : x ⟶ y) :
    ∃ (j : I) (a b : F.obj j) (f' g' : a ⟶ b)
      (hx : (colimit.ι F j).toFunctor.obj a = x)
      (hy : (colimit.ι F j).toFunctor.obj b = y),
      (colimit.ι F j).toFunctor.map f' = eqToHom hx ≫ f ≫ eqToHom hy.symm ∧
      (colimit.ι F j).toFunctor.map g' = eqToHom hx ≫ g ≫ eqToHom hy.symm := by
  obtain ⟨i, A, B, hA, hB⟩ := exists_common_stage_obj_of_colimit.{u, v, w} F x y
  obtain ⟨k, r, f', g', hf', hg'⟩ := exists_stage_map_pair_of_colimit.{u, v, w} F i A B
    (eqToHom hA ≫ f ≫ eqToHom hB.symm) (eqToHom hA ≫ g ≫ eqToHom hB.symm)
  have hwa : (colimit.ι F k).toFunctor.obj ((F.map r).toFunctor.obj A) =
      (colimit.ι F i).toFunctor.obj A :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F r)) A
  have hwb : (colimit.ι F k).toFunctor.obj ((F.map r).toFunctor.obj B) =
      (colimit.ι F i).toFunctor.obj B :=
    Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F r)) B
  refine ⟨k, (F.map r).toFunctor.obj A, (F.map r).toFunctor.obj B, f', g',
    hwa.trans hA, hwb.trans hB, ?_, ?_⟩
  · rw [(comp_eqToHom_iff _ _ _).mp (transport_hom_of_heq hwa hwb hf')]
    simp
  · rw [(comp_eqToHom_iff _ _ _).mp (transport_hom_of_heq hwa hwb hg')]
    simp

/-- **Essential surjectivity of a functor out of a colimit in `Cat` is witnessed at a stage.**
Every object of the target is isomorphic to the image of an object of one of the stages. -/
lemma exists_stage_obj_of_essSurj {D : Type uD} [Category.{vD} D]
    (K : (colimit F : Cat) ⥤ D) [K.EssSurj] (x : D) :
    ∃ (j : I) (a : F.obj j), Nonempty (K.obj ((colimit.ι F j).toFunctor.obj a) ≅ x) := by
  obtain ⟨y, ⟨eo⟩⟩ := Functor.EssSurj.mem_essImage K x
  obtain ⟨j, a, ha⟩ := exists_stage_obj_of_colimit.{u, v, w} F y
  exact ⟨j, a, ⟨eqToIso (congrArg K.obj ha) ≪≫ eo⟩⟩

/-- **Fullness of a functor out of a filtered colimit in `Cat` is witnessed at a stage.** A
morphism between the images of two objects of one stage is, at a later stage, the image of a
morphism of that stage. -/
lemma exists_stage_map_of_full [IsFiltered I] {D : Type uD} [Category.{vD} D]
    (K : (colimit F : Cat) ⥤ D) [K.Full] (i : I) (x y : F.obj i)
    (f : K.obj ((colimit.ι F i).toFunctor.obj x) ⟶
      K.obj ((colimit.ι F i).toFunctor.obj y)) :
    ∃ (k : I) (s : i ⟶ k)
      (g : (F.map s).toFunctor.obj x ⟶ (F.map s).toFunctor.obj y),
      HEq (K.map ((colimit.ι F k).toFunctor.map g)) f := by
  obtain ⟨f', hf'⟩ := K.map_surjective f
  obtain ⟨k, s, g, hg⟩ := exists_stage_map_of_colimit_of_eq.{u, v, w} F i x y f'
  exact ⟨k, s, g, (map_heq_of_eq K
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F s)) x)
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F s)) y) hg).trans
      (heq_of_eq hf')⟩

end Stages

end CategoryTheory.Cat

end
