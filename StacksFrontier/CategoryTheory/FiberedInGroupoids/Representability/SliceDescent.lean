module

public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a representing presheaf to a smaller slice

Let `a : A ⟶ X` be a morphism of a category `C` and let `q : 𝒟 ⥤ C/A` be a category over the
smaller slice. Viewing it over `C/X` along the localization functor `CategoryTheory.Over.map a`
*adds no information*, and this file is the corresponding statement for representing presheaves:
if `q ⋙ Over.map a` is equivalent over `C/X` to the category of elements of a presheaf `G` on
`C/X`, then `q` itself is equivalent over `C/A` to the category of elements of a presheaf `F` on
`C/A`, and `F` is cut out of the restriction of `G` by one equation.

The presheaf `F` is *not* the restriction `G|_{C/A}` of `G`. A section of the restriction over
`W : C/A` is a section of `G` over `(Over.map a).obj W`, and the objects of `𝒟` it classifies are
those lying over *any* object of `C/A` with the same image, not just over `W`; the two agree only
when `a` is a monomorphism. What `F` is, is the *fibre* of the restriction over the tautological
section: the extra datum an object of `𝒟` carries beyond its image in `C/X` is its structure
morphism to `A`, and `F` is the part of `G|_{C/A}` on which the induced morphism to the
representable presheaf of `A/X` is the structure morphism.

## Main definitions

* `CategoryTheory.PresheafOfCategories.sliceDescentStructure`: the 1-morphism from the category of
  elements of `G` to the category of elements of `h_{A/X}` recording the structure morphism to `A`.
* `CategoryTheory.PresheafOfCategories.toSliceBaseChange`: the comparison of the category of
  elements of `G` with the 2-fibre product `C/A ×_{h_{A/X}} El G` that
  `CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` represents.

## Main results

* `CategoryTheory.PresheafOfCategories.isEquivalence_toSliceBaseChange`: that comparison is an
  equivalence.
* `CategoryTheory.PresheafOfCategories.exists_isPullback_nonempty_equivalenceOver_of_comp_overMap`:
  the descent statement above, with the cartesian square exhibiting `F` as the fibre product of
  the restriction of `G` with the final presheaf over the restriction of `h_{A/X}`.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u v₂ u₂

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)

/-- A functor to `C/A` which is strictly over `C/X` of a presheaf is fibred in groupoids. -/
private theorem isFiberedInGroupoids_of_comp_overMap_eq {G : (Over X)ᵒᵖ ⥤ Type v}
    (q : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤ Over A)
    (hq : q ⋙ Over.map a = discreteProjection G) : q.IsFiberedInGroupoids :=
  (Functor.isFiberedInGroupoids_comp_overMap_iff a q).1
    (hq ▸ (isFiberedInSetoids_discreteProjection G).isFiberedInGroupoids)

section Strict

variable {G : (Over X)ᵒᵖ ⥤ Type v}
  (q : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤ Over A)
  (hq : q ⋙ Over.map a = discreteProjection G)

/-- The 1-morphism from the category of elements of `G` to the category of elements of the
presheaf on `C/X` represented by `A/X`, attached to a 1-morphism `q` from that category of
elements to the smaller slice `C/A`: it records the structure morphism to `A` that `q` supplies. -/
abbrev sliceDescentStructure : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
    (presheafOfCategories (yoneda.obj (Over.mk a) ⋙ typeToCat)).obj :=
  q ⋙ overMapToElements a

include hq in
/-- The structure 1-morphism is a 1-morphism over `C/X`. -/
lemma sliceDescentStructure_comp_eq :
    sliceDescentStructure a q ⋙ discreteProjection (yoneda.obj (Over.mk a)) =
      discreteProjection G := hq

/-- The comparison of the category of elements of `G` with the 2-fibre product
`C/A ×_{h_{A/X}} El G`: an object `y` is sent to the triple consisting of its image `q y` in
`C/A`, of `y` itself, and of the identity comparison isomorphism. -/
noncomputable def toSliceBaseChange :
    (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver (Over.map a) (discreteProjection G)
        (discreteProjection (yoneda.obj (Over.mk a))) (overMapToElements a)
        (sliceDescentStructure a q) where
  obj y :=
    { base := (Over.map a).obj (q.obj y)
      x := q.obj y
      y := y
      hx := rfl
      hy := (Functor.congr_obj hq y).symm
      iso := Iso.refl _
      vertical := IsHomLift.id rfl }
  map {y y'} u :=
    { hbase := (Over.map a).map (q.map u)
      a := q.map u
      b := u
      ha := IsHomLift.map (Over.map a) (q.map u)
      hb := by
        have h : (q ⋙ Over.map a).IsHomLift ((Over.map a).map (q.map u)) u := IsHomLift.map _ u
        rwa [hq] at h
      w := by simp }
  map_id y := TwoFibreProductOver.Hom.ext' (q.map_id y) rfl
  map_comp u u' := TwoFibreProductOver.Hom.ext' (q.map_comp u u') rfl

include hq in
/-- The comparison functor is strictly over `C/A`: the first projection of the 2-fibre product
recovers `q`. -/
lemma toSliceBaseChange_comp_fst :
    toSliceBaseChange a q hq ⋙ TwoFibreProductOver.fst (Over.map a) (discreteProjection G)
        (discreteProjection (yoneda.obj (Over.mk a))) (overMapToElements a)
        (sliceDescentStructure a q) = q := rfl

include hq in
/-- The comparison `toSliceBaseChange` of the category of elements of `G` with the 2-fibre
product `C/A ×_{h_{A/X}} El G` is an equivalence. -/
theorem isEquivalence_toSliceBaseChange : (toSliceBaseChange a q hq).IsEquivalence := by
  have hIE : (overMapToElements a).IsEquivalence :=
    (overMapElementsEquivalenceOver a).isEquivalence_hom_functor
  have hfaith : (toSliceBaseChange a q hq).Faithful :=
    ⟨fun h => congrArg TwoFibreProductOver.Hom.b h⟩
  have hfull : (toSliceBaseChange a q hq).Full := by
    constructor
    intro y y' f
    obtain ⟨fa, hfa⟩ : ∃ g : q.obj y ⟶ q.obj y', g = TwoFibreProductOver.Hom.a f := ⟨_, rfl⟩
    obtain ⟨fb, hfb⟩ : ∃ h : y ⟶ y', h = TwoFibreProductOver.Hom.b f := ⟨_, rfl⟩
    have hw : (overMapToElements a).map fa ≫ 𝟙 ((overMapToElements a).obj (q.obj y')) =
        𝟙 ((overMapToElements a).obj (q.obj y)) ≫ (overMapToElements a).map (q.map fb) := by
      rw [hfa, hfb]
      exact f.w
    have hab : fa = q.map fb := (overMapToElements a).map_injective <| by
      simpa only [Category.comp_id, Category.id_comp] using hw
    exact ⟨fb, TwoFibreProductOver.Hom.ext' (hab.symm.trans hfa) hfb⟩
  have hess : (toSliceBaseChange a q hq).EssSurj := by
    constructor
    intro P
    set ff := Functor.FullyFaithful.ofFullyFaithful (overMapToElements a)
    set i : P.x ≅ q.obj P.y := ff.preimageIso P.iso
    have hihom : (overMapToElements a).map i.hom = P.iso.hom := ff.map_preimage P.iso.hom
    have hvert : (Over.map a).IsHomLift (𝟙 P.base) i.hom := by
      refine (Functor.isHomLift_map_iff_of_comp_eq (Over.map a)
        (discreteProjection (yoneda.obj (Over.mk a))) (overMapToElements a) rfl
        (𝟙 P.base) i.hom).1 ?_
      rw [hihom]
      exact P.vertical
    have hvertinv : (Over.map a).IsHomLift (𝟙 P.base) i.inv :=
      IsHomLift.lift_id_inv (Over.map a) P.base i
    refine ⟨P.y, ⟨TwoFibreProductOver.isoMkVertical (U := P.base) i.symm (Iso.refl P.y)
      hvertinv (IsHomLift.id P.hy) ?_⟩⟩
    have hiinv : (overMapToElements a).map i.inv = P.iso.inv :=
      congrArg Iso.inv (Iso.ext hihom : (overMapToElements a).mapIso i = P.iso)
    have hgoal : (overMapToElements a).map i.inv ≫ P.iso.hom =
        𝟙 ((overMapToElements a).obj (q.obj P.y)) ≫
          (overMapToElements a).map (q.map (𝟙 P.y)) := by
      rw [hiinv, Iso.inv_hom_id, q.map_id, Functor.map_id, Category.id_comp]
    exact hgoal
  exact Functor.IsEquivalence.mk

include hq in
/-- A 1-morphism from the category of elements of a
presheaf `G` on `C/X` to the smaller slice `C/A`, strictly over `C/X`, is equivalent over `C/A` to
the category of elements of the subpresheaf of the restriction of `G` cut out by the tautological
section. -/
@[sga "4 I 5.12" "special case"]
theorem nonempty_equivalenceOver_sliceDescentPresheaf :
    Nonempty (StacksRepresentableCFG.EquivalenceOver q
      (discreteProjection (twoFibreProductPresheaf (overMapToElements a)
        (rfl : overMapToElements a ⋙ discreteProjection (yoneda.obj (Over.mk a)) = Over.map a)
        (sliceDescentStructure a q) (sliceDescentStructure_comp_eq a q hq)))) := by
  obtain ⟨e₁⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_of_comp_overMap_eq a q hq)
    (isFiberedInGroupoids_fst_overMap a (sliceDescentStructure a q)
      (sliceDescentStructure_comp_eq a q hq) (overMapToElements a) rfl)
    (toSliceBaseChange a q hq) (toSliceBaseChange_comp_fst a q hq)
    (isEquivalence_toSliceBaseChange a q hq)
  obtain ⟨e₂⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf a (sliceDescentStructure a q)
    (sliceDescentStructure_comp_eq a q hq) (overMapToElements a) rfl
  exact ⟨e₁.trans e₂⟩

end Strict

section General

variable {𝒟 : Type u₂} [Category.{v₂} 𝒟] {G : (Over X)ᵒᵖ ⥤ Type v}

/-- Let `q : 𝒟 ⥤ C/A` be a category fibred in
groupoids over the slice at `A` and let `a : A ⟶ X`. If `q`, viewed over the slice at `X` along
the localization functor `Over.map a`, is equivalent over `C/X` to the category of elements of a
presheaf `G`, then `q` is equivalent over `C/A` to the category of elements of a presheaf `F` on
`C/A` which is the fibre product of the restriction of `G` along `Over.map a` with the presheaf of
points of the final object of `C/A`, taken over the restriction of the presheaf represented by
`A/X`. -/
theorem exists_isPullback_nonempty_equivalenceOver_of_comp_overMap
    (q : 𝒟 ⥤ Over A) (hqf : q.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver (q ⋙ Over.map a) (discreteProjection G)) :
    ∃ (F : (Over A)ᵒᵖ ⥤ Type v)
      (τ : (OverShriek.relocalizeRestrict a).obj G ⟶
        (OverShriek.relocalizeRestrict a).obj (yoneda.obj (Over.mk a)))
      (ι : F ⟶ (OverShriek.relocalizeRestrict a).obj G)
      (π : F ⟶ yoneda.obj (Over.mk (𝟙 A)))
      (ρ : yoneda.obj (Over.mk (𝟙 A)) ⟶
        (OverShriek.relocalizeRestrict a).obj (yoneda.obj (Over.mk a))),
      IsPullback ι π τ ρ ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) := by
  set q' : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤ Over A := e.inv.functor ⋙ q
  have hq' : q' ⋙ Over.map a = discreteProjection G := e.inv.w
  obtain ⟨e₀⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_of_comp_overMap_eq a q' hq') hqf
    e.inv.functor rfl e.isEquivalence_inv_functor
  obtain ⟨e₁⟩ := nonempty_equivalenceOver_sliceDescentPresheaf a q' hq'
  exact ⟨_, _, _, _, _, isPullback_fibrePresheaf
    (Functor.whiskerLeft (Over.map a).op
      (natTransOfBasedFunctor (sliceDescentStructure a q')
        (sliceDescentStructure_comp_eq a q' hq')))
    (sectionOfBasedFunctor (overMapToElements a) rfl)
    (fun f => sectionOfBasedFunctor_map (overMapToElements a) rfl f) Over.mkIdTerminal,
    ⟨e₀.symm.trans e₁⟩⟩

end General

end CategoryTheory.PresheafOfCategories

end
