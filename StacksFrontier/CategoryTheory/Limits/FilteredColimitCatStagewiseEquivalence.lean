module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductEquivalence

/-!
# A stagewise equivalence of filtered diagrams of categories is an equivalence of colimits

Let `τ : 𝒳 ⟶ 𝒴` be a morphism of diagrams of categories indexed by a filtered category `J`. This
file proves that each of the three properties "faithful", "full" and "essentially surjective"
passes from every component `τ.app j` to `CategoryTheory.Limits.colimMap τ`, and hence that a
stagewise equivalence induces an equivalence
`colim 𝒳ⱼ ≌ colim 𝒴ⱼ`.

This is what makes an identification of two diagrams of categories that holds only up to
equivalence usable at the level of colimits. The colimit of a diagram of categories is a
*1-categorical* colimit, so it is a functor of the diagram only up to equality: a stagewise
equivalence is not a morphism of diagrams at all, and even a strict morphism of diagrams whose
components happen to be equivalences is not obviously an equivalence after passing to the colimit,
because the colimit is a quotient. For a *filtered* index category it is, and that is the content
here. The application is Stacks 0CMW, where the fibre of a 2-fibre product of categories fibred in
groupoids over an object of the site is identified with the 2-fibre product of the fibres only up
to equivalence once the *split* fibres of Stacks 004A are used, which is what the colimit of fibre
categories is built from.

## Main results

* `CategoryTheory.Cat.faithful_colimMap`
* `CategoryTheory.Cat.full_colimMap`
* `CategoryTheory.Cat.essSurj_colimMap`
* `CategoryTheory.Cat.isEquivalence_colimMap`: a stagewise equivalence of filtered diagrams of
  categories induces an equivalence of colimits.

## Implementation notes

All three proofs represent the datum at a stage of the diagram, apply the hypothesis at a stage,
and push the answer back into the colimit, which is the toolkit of
`StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages`. Filteredness enters to bring two
objects to one common stage and to force an identity holding in the colimit to hold already at a
stage (`CategoryTheory.Cat.exists_common_stage_eq_of_colimit_ι_map_eq`).

The square relating a colimit inclusion to `colimMap`
(`CategoryTheory.Cat.ι_colimMap_toFunctor`) and the naturality square of `τ`
(`CategoryTheory.Cat.naturality_toFunctor`) both commute *strictly*, and the transports they
produce are read off `CategoryTheory.Cat.strictSquare_obj` rather than
`CategoryTheory.Functor.congr_obj`, so that they mention no composite functors and the adjacent
ones cancel syntactically. This file therefore imports the toolkit collected for the 2-fibre
product comparison rather than restating it, although the statements here are about no 2-fibre
product.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe u v w

section Stagewise

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  {X Y : J ⥤ Cat.{max u v w, max u v w}} (τ : X ⟶ Y)
  [HasColimit X] [HasColimit Y]
  [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  [HasColimit (Y ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]

/-- The equality of objects underlying the square relating a colimit inclusion to `colimMap`,
in the form whose transports cancel syntactically. -/
lemma colimMap_ι_obj (j : J) (a : X.obj j) :
    (colimMap τ).toFunctor.obj ((colimit.ι X j).toFunctor.obj a) =
      (colimit.ι Y j).toFunctor.obj ((τ.app j).toFunctor.obj a) :=
  Functor.congr_obj (ι_colimMap_toFunctor τ j) a

/-- The equality of objects underlying the naturality square of `τ`, in the form whose
transports cancel syntactically. -/
lemma map_app_obj {j k : J} (r : j ⟶ k) (a : X.obj j) :
    (Y.map r).toFunctor.obj ((τ.app j).toFunctor.obj a) =
      (τ.app k).toFunctor.obj ((X.map r).toFunctor.obj a) :=
  Functor.congr_obj ((naturality_toFunctor τ r).symm) a

/-- The square relating a colimit inclusion to `colimMap`, on morphisms. -/
private lemma colimMap_ι_map {j : J} {x y : X.obj j} (c : x ⟶ y) :
    (colimMap τ).toFunctor.map ((colimit.ι X j).toFunctor.map c) =
      eqToHom (colimMap_ι_obj.{u, v, w} τ j x) ≫
        (colimit.ι Y j).toFunctor.map ((τ.app j).toFunctor.map c) ≫
          eqToHom (colimMap_ι_obj.{u, v, w} τ j y).symm :=
  strictSquare_map _ _ _ _ (ι_colimMap_toFunctor τ j) c

/-- The naturality square of `τ`, on morphisms. -/
private lemma map_app_map {j k : J} (r : j ⟶ k) {x y : X.obj j} (c : x ⟶ y) :
    (τ.app k).toFunctor.map ((X.map r).toFunctor.map c) =
      eqToHom (map_app_obj.{u, v, w} τ r x).symm ≫
        (Y.map r).toFunctor.map ((τ.app j).toFunctor.map c) ≫
          eqToHom (map_app_obj.{u, v, w} τ r y) :=
  strictSquare_map _ _ _ _ (naturality_toFunctor τ r) c

/-- **A stagewise faithful morphism of filtered diagrams of categories is faithful on
colimits.** -/
theorem faithful_colimMap (h : ∀ j : J, (τ.app j).toFunctor.Faithful) :
    (colimMap τ).toFunctor.Faithful where
  map_injective {P Q} f g hfg := by
    obtain ⟨j, a, b, f', g', hx, hy, hf', hg'⟩ :=
      exists_stage_hom_pair_of_colimit.{u, v, w} X f g
    -- the two stage morphisms already have the same image in `colim 𝒴`
    have eF := colimMap_ι_map.{u, v, w} τ f'
    have eG := colimMap_ι_map.{u, v, w} τ g'
    rw [hf', Functor.map_comp, Functor.map_comp, hfg] at eF
    rw [hg', Functor.map_comp, Functor.map_comp] at eG
    have key : (colimit.ι Y j).toFunctor.map ((τ.app j).toFunctor.map f') =
        (colimit.ι Y j).toFunctor.map ((τ.app j).toFunctor.map g') :=
      (cancel_mono (eqToHom _)).mp ((cancel_epi (eqToHom _)).mp (eF.symm.trans eG))
    -- filteredness forces the identity at a stage, where faithfulness applies
    obtain ⟨k, v, hv⟩ := exists_common_stage_eq_of_colimit_ι_map_eq Y j
      ((τ.app j).toFunctor.map f') ((τ.app j).toFunctor.map g') key
    have hk : (τ.app k).toFunctor.map ((X.map v).toFunctor.map f') =
        (τ.app k).toFunctor.map ((X.map v).toFunctor.map g') := by
      rw [map_app_map.{u, v, w} τ v f', map_app_map.{u, v, w} τ v g', hv]
    have hι : (colimit.ι X j).toFunctor.map f' = (colimit.ι X j).toFunctor.map g' := by
      have e := congrArg (colimit.ι X k).toFunctor.map ((h k).map_injective hk)
      rw [colimit_ι_map_map v f', colimit_ι_map_map v g'] at e
      exact (cancel_mono _).mp ((cancel_epi _).mp e)
    rw [hf', hg'] at hι
    exact (cancel_mono (eqToHom hy.symm)).mp ((cancel_epi (eqToHom hx)).mp hι)

/-- **A stagewise full morphism of filtered diagrams of categories is full on colimits.** -/
theorem full_colimMap (h : ∀ j : J, (τ.app j).toFunctor.Full) :
    (colimMap τ).toFunctor.Full where
  map_surjective {P Q} m := by
    obtain ⟨j, a, b, hx, hy⟩ := exists_common_stage_obj_of_colimit.{u, v, w} X P Q
    -- `m` read as a morphism between the images of two objects of the stage `j`
    have Pa : (colimit.ι Y j).toFunctor.obj ((τ.app j).toFunctor.obj a) =
        (colimMap τ).toFunctor.obj P :=
      (colimMap_ι_obj.{u, v, w} τ j a).symm.trans (congrArg (colimMap τ).toFunctor.obj hx)
    have Pb : (colimMap τ).toFunctor.obj Q =
        (colimit.ι Y j).toFunctor.obj ((τ.app j).toFunctor.obj b) :=
      (congrArg (colimMap τ).toFunctor.obj hy).symm.trans (colimMap_ι_obj.{u, v, w} τ j b)
    obtain ⟨k, r, g, hg⟩ := exists_stage_hom_of_colimit.{u, v, w} Y j
      ((τ.app j).toFunctor.obj a) ((τ.app j).toFunctor.obj b)
      (eqToHom Pa ≫ m ≫ eqToHom Pb)
    -- at the stage `k` fullness produces a preimage
    obtain ⟨c, hc⟩ := (h k).map_surjective
      (eqToHom (map_app_obj.{u, v, w} τ r a).symm ≫ g ≫
        eqToHom (map_app_obj.{u, v, w} τ r b))
    have key : (colimMap τ).toFunctor.map ((colimit.ι X k).toFunctor.map c) =
        eqToHom (congrArg (colimMap τ).toFunctor.obj ((colimit_ι_map_obj X r a).trans hx)) ≫
          m ≫ eqToHom (congrArg (colimMap τ).toFunctor.obj
            ((colimit_ι_map_obj X r b).trans hy)).symm := by
      rw [colimMap_ι_map.{u, v, w} τ c, hc, map_eqToHom_conj, hg]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    refine ⟨eqToHom ((colimit_ι_map_obj X r a).trans hx).symm ≫
      (colimit.ι X k).toFunctor.map c ≫ eqToHom ((colimit_ι_map_obj X r b).trans hy), ?_⟩
    rw [Functor.map_comp, Functor.map_comp, key, eqToHom_map, eqToHom_map]
    exact eqToHom_conj_cancel _ _ _ _ _

/-- **A stagewise essentially surjective morphism of filtered diagrams of categories is
essentially surjective on colimits.** -/
theorem essSurj_colimMap (h : ∀ j : J, (τ.app j).toFunctor.EssSurj) :
    (colimMap τ).toFunctor.EssSurj where
  mem_essImage R := by
    obtain ⟨j, y, hy⟩ := exists_stage_obj_of_colimit.{u, v, w} Y R
    obtain ⟨x, ⟨eo⟩⟩ := (h j).mem_essImage y
    exact ⟨(colimit.ι X j).toFunctor.obj x,
      ⟨eqToIso (colimMap_ι_obj.{u, v, w} τ j x) ≪≫
        (colimit.ι Y j).toFunctor.mapIso eo ≪≫ eqToIso hy⟩⟩

/-- **A stagewise equivalence of filtered diagrams of categories induces an equivalence of
colimits.** -/
theorem isEquivalence_colimMap (h : ∀ j : J, (τ.app j).toFunctor.IsEquivalence) :
    (colimMap τ).toFunctor.IsEquivalence where
  faithful := faithful_colimMap.{u, v, w} τ fun j => (h j).faithful
  full := full_colimMap.{u, v, w} τ fun j => (h j).full
  essSurj := essSurj_colimMap.{u, v, w} τ fun j => (h j).essSurj

end Stagewise

end CategoryTheory.Cat

end
