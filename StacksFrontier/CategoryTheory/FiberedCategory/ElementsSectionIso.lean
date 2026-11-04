module

public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# Two sections of a category of elements naming the same element coincide

Let `F` be a presheaf of sets on a category `C` and let `El F` be its category of elements
(Stacks 02XV, `CategoryTheory.presheafOfCategories` of `F ⋙ typeToCat`). A 1-morphism
`σ : 𝒯 ⥤ El F` over `C` names a family of elements of `F`, one over each `pT τ`
(`CategoryTheory.PresheafOfCategories.sectionOfBasedFunctor`). This file proves that the family
determines the 1-morphism *on the nose*: two 1-morphisms over `C` naming the same family are
equal. For a category over `C` equivalent to `El F` over `C`, two such 1-morphisms are instead
isomorphic by an isomorphism whose components lie over identities.

The file also records the section of `El F` over a slice `𝒞/A` attached to a morphism
`yoneda.obj A ⟶ F`, which is the universal example of such a 1-morphism.

## Main definitions

* `CategoryTheory.PresheafOfCategories.sliceSectionOfHom`: the 1-morphism `𝒞/A ⥤ El F` over `𝒞`
  attached to a morphism of presheaves `yoneda.obj A ⟶ F`.

## Main results

* `CategoryTheory.PresheafOfCategories.eq_of_sections_eq`: two 1-morphisms into `El F` over `C`
  naming the same family of elements are equal.
* `CategoryTheory.PresheafOfCategories.elementOf_congr` and
  `CategoryTheory.PresheafOfCategories.sectionOfBasedFunctor_congr`: the element named depends
  only on the object naming it, not on the identification of its base.
* `CategoryTheory.PresheafOfCategories.faithful_discreteProjection`: the projection of `El F` to
  `C` is faithful.
* `CategoryTheory.PresheafOfCategories.eq_of_vertical_natTrans`: two 1-morphisms into `El F` over
  `C` joined by a vertical 2-morphism are equal.
* `CategoryTheory.PresheafOfCategories.natTrans_ext_of_vertical`: a vertical 2-morphism between
  two 1-morphisms into `El F` over `C` is unique.
* `CategoryTheory.PresheafOfCategories.exists_vertical_iso_of_sections_eq`: two 1-morphisms into
  a category equivalent to `El F` over `C` naming the same family of elements are isomorphic by
  an isomorphism whose components lie over identities.
* `CategoryTheory.PresheafOfCategories.sliceSectionOfHom_map`: relocalizing the slice before
  taking the section restricts the morphism of presheaves.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
-/

@[expose] public section

open CategoryTheory Opposite

namespace StacksRepresentableCFG

universe v u v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u} [Category.{v} C] {D₁ : Type u₁} [Category.{v₁} D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂] {D₃ : Type u₃} [Category.{v₃} D₃]

/-- Postcomposing a 1-morphism over `C` with the forward 1-morphism of an equivalence over `C`
leaves a 1-morphism over `C`. -/
theorem EquivalenceOver.comp_hom_functor_comp_eq {p : D₁ ⥤ C} {q : D₂ ⥤ C}
    (e : EquivalenceOver p q) {r : D₃ ⥤ C} {H : D₃ ⥤ D₁} (hH : H ⋙ p = r) :
    (H ⋙ e.hom.functor) ⋙ q = r := by
  rw [Functor.assoc, e.hom.w, hH]

end StacksRepresentableCFG

namespace CategoryTheory.PresheafOfCategories

universe vC uC uT uS vS

variable {C : Type uC} [Category.{vC} C] {F : Cᵒᵖ ⥤ Type vC}

/-- A morphism of a category of elements is determined by its image under the projection to
`C`. -/
theorem elements_hom_ext_map {Z W : (presheafOfCategories (F ⋙ typeToCat)).obj} (u w : Z ⟶ W)
    (h : (discreteProjection F).map u = (discreteProjection F).map w) : u = w :=
  elements_hom_ext u w h

/-- The components of the canonical 2-morphism between two equal 1-morphisms over `C` lie over
identities: the projection of an `eqToHom` is an `eqToHom`. -/
theorem isHomLift_eqToHom_app {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    {σ τ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj}
    (hσ : σ ⋙ discreteProjection F = pT) (hτ : τ ⋙ discreteProjection F = pT) (h : σ = τ)
    (t : 𝒯) :
    (discreteProjection F).IsHomLift (𝟙 (pT.obj t)) ((eqToHom h).app t) := by
  refine IsHomLift.of_fac' (discreteProjection F) (𝟙 (pT.obj t)) ((eqToHom h).app t)
    (Functor.congr_obj hσ t) (Functor.congr_obj hτ t) ?_
  rw [eqToHom_app, eqToHom_map, Category.id_comp, eqToHom_trans]

/-- Two 1-morphisms over `C` naming the same family of elements of `F` are equal. -/
theorem eq_of_sections_eq {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    (σ τ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hσ : σ ⋙ discreteProjection F = pT) (hτ : τ ⋙ discreteProjection F = pT)
    (h : ∀ t, sectionOfBasedFunctor σ hσ t = sectionOfBasedFunctor τ hτ t) : σ = τ := by
  refine CategoryTheory.Functor.ext (fun t => obj_eq_of_elementOf_eq
    (Functor.congr_obj hσ t) (Functor.congr_obj hτ t) (h t)) (fun a b i => ?_)
  refine elements_hom_ext_map _ _ ?_
  have key : ∀ (ρ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
      (hρ : ρ ⋙ discreteProjection F = pT), (discreteProjection F).map (ρ.map i) =
      eqToHom (Functor.congr_obj hρ a) ≫ pT.map i ≫ eqToHom (Functor.congr_obj hρ b).symm :=
    fun _ hρ => Functor.congr_hom hρ i
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, key σ hσ, key τ hτ]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- Equal objects of a category of elements lying over one object of `C` name the same
element. -/
theorem elementOf_congr {X Y : (presheafOfCategories (F ⋙ typeToCat)).obj} {V : C}
    (hX : X.base = V) (hY : Y.base = V) (h : X = Y) : elementOf F hX = elementOf F hY := by
  subst h
  rfl

/-- Two 1-morphisms over `C` whose images at `t` agree name the same element at `t`. -/
theorem sectionOfBasedFunctor_congr {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    (σ τ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hσ : σ ⋙ discreteProjection F = pT) (hτ : τ ⋙ discreteProjection F = pT) {t : 𝒯}
    (h : σ.obj t = τ.obj t) :
    sectionOfBasedFunctor σ hσ t = sectionOfBasedFunctor τ hτ t :=
  elementOf_congr _ _ h

/-- The projection from a category of elements of a presheaf of sets to the base is
faithful. -/
theorem faithful_discreteProjection : (discreteProjection F).Faithful :=
  ⟨fun {_ _ _ _} h => elements_hom_ext_map _ _ h⟩

/-- Two 1-morphisms over `C` into a category of elements joined by a vertical 2-morphism are
equal. -/
theorem eq_of_vertical_natTrans {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    {σ τ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj}
    (hσ : σ ⋙ discreteProjection F = pT) (hτ : τ ⋙ discreteProjection F = pT) (η : σ ⟶ τ)
    (hη : ∀ t, (discreteProjection F).IsHomLift (𝟙 (pT.obj t)) (η.app t)) : σ = τ := by
  refine eq_of_sections_eq σ τ hσ hτ fun t => ?_
  have h := elementOf_eq_map (P := F) (Functor.congr_obj hσ t) (Functor.congr_obj hτ t)
    (𝟙 (pT.obj t)) (η.app t) (hη t)
  rwa [op_id, F.map_id_apply] at h

/-- A vertical 2-morphism of 1-morphisms over `C` into a category of elements is unique. -/
theorem natTrans_ext_of_vertical {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C}
    {σ τ : 𝒯 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj} (η θ : σ ⟶ τ)
    (hη : ∀ t, (discreteProjection F).IsHomLift (𝟙 (pT.obj t)) (η.app t))
    (hθ : ∀ t, (discreteProjection F).IsHomLift (𝟙 (pT.obj t)) (θ.app t)) : η = θ := by
  refine NatTrans.ext (funext fun t => elements_hom_ext_map _ _ ?_)
  have := hη t
  have := hθ t
  rw [IsHomLift.fac' _ (𝟙 (pT.obj t)) (η.app t),
    IsHomLift.fac' _ (𝟙 (pT.obj t)) (θ.app t)]

/-- Two 1-morphisms over `C` into a category equivalent to a category of elements, naming the
same family of elements, are isomorphic by an isomorphism whose components lie over
identities. -/
theorem exists_vertical_iso_of_sections_eq {𝒮 : Type uS} [Category.{vS} 𝒮] {p : 𝒮 ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    {𝒯 : Type uT} [Category.{vC} 𝒯] {pT : 𝒯 ⥤ C} (H K : 𝒯 ⥤ 𝒮)
    (hH : H ⋙ p = pT) (hK : K ⋙ p = pT)
    (h : ∀ t, sectionOfBasedFunctor (H ⋙ e.hom.functor)
        (e.comp_hom_functor_comp_eq hH) t =
      sectionOfBasedFunctor (K ⋙ e.hom.functor) (e.comp_hom_functor_comp_eq hK) t) :
    ∃ η : H ≅ K, ∀ t, p.IsHomLift (𝟙 (pT.obj t)) (η.hom.app t) := by
  have he : e.hom.functor.IsEquivalence := e.toEquivalence.isEquivalence_functor
  have hcomp : H ⋙ e.hom.functor = K ⋙ e.hom.functor :=
    eq_of_sections_eq _ _ (e.comp_hom_functor_comp_eq hH) (e.comp_hom_functor_comp_eq hK) h
  let W := (Functor.whiskeringRight 𝒯 𝒮 (presheafOfCategories (F ⋙ typeToCat)).obj).obj
    e.hom.functor
  refine ⟨W.preimageIso (eqToIso hcomp), fun t => ?_⟩
  have hmap : e.hom.functor.map ((W.preimageIso (eqToIso hcomp)).hom.app t) =
      (eqToHom hcomp).app t :=
    NatTrans.congr_app (W.map_preimage (eqToIso hcomp).hom) t
  have : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 (pT.obj t))
      (e.hom.functor.map ((W.preimageIso (eqToIso hcomp)).hom.app t)) :=
    hmap ▸ isHomLift_eqToHom_app (e.comp_hom_functor_comp_eq hH)
      (e.comp_hom_functor_comp_eq hK) hcomp t
  exact Functor.isHomLift_of_isHomLift_map e.hom.w _ _

/-- The section of `El F` over the slice `𝒞/A` attached to a morphism of presheaves
`yoneda.obj A ⟶ F`: an object of `𝒞/A` is an element of `yoneda.obj A`, sent to its image under
the morphism of presheaves. -/
def sliceSectionOfHom {A : C} (m : yoneda.obj A ⟶ F) :
    Over A ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj :=
  sliceToElements A ⋙ elementsMap m

/-- `CategoryTheory.PresheafOfCategories.sliceSectionOfHom` is a 1-morphism over `𝒞`: it is
strictly over the forgetful functor of the slice. -/
theorem sliceSectionOfHom_comp_eq {A : C} (m : yoneda.obj A ⟶ F) :
    sliceSectionOfHom m ⋙ discreteProjection F = Over.forget A := rfl

/-- Relocalizing before taking the section restricts the morphism of presheaves: for
`i : G ⟶ A` the section attached to `m` over the slice at `A`, read over the slice at `G`, is the
section attached to the restriction of `m` along `i`. -/
theorem sliceSectionOfHom_map {A G : C} (i : G ⟶ A) (m : yoneda.obj A ⟶ F) :
    Over.map i ⋙ sliceSectionOfHom m = sliceSectionOfHom (yoneda.map i ≫ m) := rfl

end CategoryTheory.PresheafOfCategories

end
