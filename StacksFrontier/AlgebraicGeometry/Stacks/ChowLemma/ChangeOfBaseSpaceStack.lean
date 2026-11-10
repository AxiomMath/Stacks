module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements

/-!
# The algebraic stack of an algebraic space, and a change of base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site and `F` a presheaf on the big fppf site of
`S`. Construction A of Stacks 04X5 views the category of elements of `F` over the big fppf site
of `S'`; this is the category of elements of the lower-shriek extension `Λ_g F`
(`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`). This file packages the
two comparison functors as 1-morphisms over `S'` and records how they interact with the
1-morphisms attached to maps of presheaves and with the structure 1-morphisms to the stack of
`S/S'` that the 2-categorical correspondence of Stacks 04X5 uses.

## Main definitions

* `AlgebraicGeometry.Stack.changeBaseFibredCategoryHom` and
  `AlgebraicGeometry.Stack.changeBaseFibredCategoryInv`: the two comparisons.
* `AlgebraicGeometry.Stack.relocalizeElementsStructureHom`: the 1-morphism from the category of
  elements of `Λ_g F` to the stack represented by `S/S'`.
* `AlgebraicGeometry.Stack.changeBaseHomIso`: Construction A of a 2-isomorphism.

## Main results

* `AlgebraicGeometry.Stack.changeBaseFibredCategoryHom_comp_inv`: one round trip is the identity
  on the nose.
* `AlgebraicGeometry.Stack.changeBaseFunctor_associatedMap_comp` and
  `AlgebraicGeometry.Stack.associatedMap_relocalize_comp_inv`: both comparisons are natural.
* `AlgebraicGeometry.Stack.changeBaseFibredCategoryHom_comp_structureHom` and
  `AlgebraicGeometry.Stack.associatedMap_comp_structureHom`: compatibility with the structure
  1-morphisms to `S/S'`.
* `AlgebraicGeometry.Stack.eq_of_basedNatTrans_schemeFibredCategory`: 1-morphisms to the stack
  represented by an object of the site which are joined by a 2-morphism are equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- Construction A of the category of elements of a presheaf `F` on the big fppf site of `S` is
the category of elements of its lower-shriek extension `Λ_g F`. -/
def changeBaseFibredCategoryHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    changeBase B S S' hS hS' g (fibredCategory B S hS F).val ⥤ᵇ
      (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val where
  toFunctor := PresheafOfCategories.relocalizeToElements g F
  w := PresheafOfCategories.relocalizeToElements_comp_eq g F

/-- The inverse comparison. -/
def changeBaseFibredCategoryInv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val ⥤ᵇ
      changeBase B S S' hS hS' g (fibredCategory B S hS F).val where
  toFunctor := PresheafOfCategories.elementsToRelocalize g F
  w := PresheafOfCategories.elementsToRelocalize_comp_eq g F

/-- The comparison followed by its inverse is the identity, on the nose. -/
theorem changeBaseFibredCategoryHom_comp_inv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    BasedFunctor.comp (changeBaseFibredCategoryHom B S S' hS hS' g F)
      (changeBaseFibredCategoryInv B S S' hS hS' g F) = BasedFunctor.id _ := by
  refine BasedCategory.BasedFunctor.ext' ?_
  fapply CategoryTheory.Functor.ext
  · intro Z
    rfl
  · intro Z W u
    refine PresheafOfCategories.elements_hom_ext _ _ (Over.OverMorphism.ext ?_)
    change u.base.left = 𝟙 _ ≫ u.base.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- The comparison is an equivalence of the underlying categories. -/
instance isEquivalence_changeBaseFibredCategoryHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Functor.IsEquivalence (changeBaseFibredCategoryHom B S S' hS hS' g F).toFunctor :=
  (CategoryTheory.Equivalence.mk
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).hom.functor
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).inv.functor
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).unitIso
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).counitIso).isEquivalence_functor

/-- **The comparison is natural.** Construction A of the 1-morphism attached to `m : F ⟶ G`,
followed by the comparison for `G`, is the comparison for `F` followed by the 1-morphism attached
to `Λ_g m`. -/
theorem changeBaseFunctor_associatedMap_comp {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ⟶ G) :
    BasedFunctor.comp (changeBaseFunctor B S S' hS hS' g (associatedMap B S hS m).1.hom)
        (changeBaseFibredCategoryHom B S S' hS hS' g G) =
      BasedFunctor.comp (changeBaseFibredCategoryHom B S S' hS hS' g F)
        (associatedMap B S' hS' ((OverShriek.relocalizePresheafFunctor g).map m)).1.hom := by
  refine BasedCategory.BasedFunctor.ext' ?_
  fapply CategoryTheory.Functor.ext
  · intro Z
    rfl
  · intro Z W u
    refine PresheafOfCategories.elements_hom_ext _ _ (Over.OverMorphism.ext ?_)
    change u.base.left = 𝟙 _ ≫ u.base.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- The inverse comparison is an equivalence of the underlying categories. -/
instance isEquivalence_changeBaseFibredCategoryInv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Functor.IsEquivalence (changeBaseFibredCategoryInv B S S' hS hS' g F).toFunctor :=
  (CategoryTheory.Equivalence.mk
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).inv.functor
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).hom.functor
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).counitIso.symm
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).unitIso.symm).isEquivalence_functor

/-- **The inverse comparison is natural.** -/
theorem associatedMap_relocalize_comp_inv {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ⟶ G) :
    BasedFunctor.comp
        (associatedMap B S' hS' ((OverShriek.relocalizePresheafFunctor g).map m)).1.hom
        (changeBaseFibredCategoryInv B S S' hS hS' g G) =
      BasedFunctor.comp (changeBaseFibredCategoryInv B S S' hS hS' g F)
        (changeBaseFunctor B S S' hS hS' g (associatedMap B S hS m).1.hom) := by
  refine BasedCategory.BasedFunctor.ext' ?_
  fapply CategoryTheory.Functor.ext
  · intro Z
    rfl
  · intro Z W u
    refine PresheafOfCategories.elements_hom_ext _ _ (Over.OverMorphism.ext ?_)
    change u.base.left = 𝟙 _ ≫ u.base.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- **Construction A of a 2-isomorphism.** A 2-isomorphism between two 1-morphisms of categories
fibred in groupoids over the big fppf site of `S` is a 2-isomorphism between their images under
Construction A: its components lie over identities of the site of `S`, hence over identities of
the site of `S'`. -/
def changeBaseHomIso {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {φ ψ : 𝒜 ⟶ ℬ} (η : φ ≅ ψ) :
    changeBaseHom B S S' hS hS' g φ ≅ changeBaseHom B S S' hS hS' g ψ :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (F := changeBaseFunctor B S S' hS hS' g φ.hom) (G := changeBaseFunctor B S S' hS hS' g ψ.hom)
    (NatIso.ofComponents (fun x =>
      { hom := η.hom.hom.toNatTrans.app x
        inv := η.inv.hom.toNatTrans.app x
        hom_inv_id := congrArg (fun t => t.hom.toNatTrans.app x) η.hom_inv_id
        inv_hom_id := congrArg (fun t => t.hom.toNatTrans.app x) η.inv_hom_id })
      (fun k => η.hom.hom.toNatTrans.naturality k))
    (fun x => (Functor.isHomLift_overMap_iff ℬ.val.p g (𝟙 (𝒜.val.p.obj x))
      (η.hom.hom.toNatTrans.app x) (BasedFunctor.w_obj φ.hom x)
      (BasedFunctor.w_obj ψ.hom x)).2 (η.hom.hom.isHomLift' x)))

/-! ### 1-morphisms to a slice -/

section Slice

/-- Two functors to a slice category which agree on objects and after forgetting to the base are
equal. -/
theorem _root_.CategoryTheory.Over.functor_ext_of_forget {C : Type*} [Category C] {D : Type*}
    [Category D] {W : D} {F₁ F₂ : C ⥤ Over W} (hobj : ∀ x, F₁.obj x = F₂.obj x)
    (hforget : F₁ ⋙ Over.forget W = F₂ ⋙ Over.forget W) : F₁ = F₂ := by
  refine CategoryTheory.Functor.ext hobj (fun x y φ => ?_)
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
  simpa using Functor.congr_hom hforget φ

/-- An object of a slice is determined by a morphism to another object whose underlying morphism
is an `eqToHom`. -/
theorem _root_.CategoryTheory.Over.eq_of_left_eq_eqToHom {D : Type*} [Category D] {W : D}
    {X Y : Over W} (a : X ⟶ Y) (h : X.left = Y.left) (ha : a.left = eqToHom h) : X = Y := by
  obtain ⟨X, ⟨⟨⟩⟩, x⟩ := X
  obtain ⟨Y, ⟨⟨⟩⟩, y⟩ := Y
  change X = Y at h
  subst h
  have hw := Over.w a
  rw [ha] at hw
  change 𝟙 X ≫ y = x at hw
  rw [Category.id_comp] at hw
  subst hw
  rfl

/-- **1-morphisms to the stack represented by an object of the site are determined up to equality
by their 2-isomorphism class.** A 2-morphism between two 1-morphisms to the slice over `W` has
components over identities, and a morphism of the slice over an identity is an identity, so the
two 1-morphisms agree on objects; they agree after forgetting to the site, being 1-morphisms over
it. -/
theorem eq_of_basedNatTrans_schemeFibredCategory {T : Scheme.{u}} {hT : B.Contains T}
    {𝒜 : BasedCategory.{w, w} (BigFppfOver B T hT)} {W : BigFppfOver B T hT}
    {F₁ F₂ : 𝒜 ⥤ᵇ (schemeFibredCategory B T hT W).val} (α : BasedNatTrans F₁ F₂) :
    F₁ = F₂ := by
  refine BasedCategory.BasedFunctor.ext' (Over.functor_ext_of_forget (fun x => ?_)
    (F₁.w.trans F₂.w.symm))
  have := α.isHomLift' x
  have hx := IsHomLift.fac' (schemeFibredCategory B T hT W).val.p (𝟙 (𝒜.p.obj x))
    (α.toNatTrans.app x)
  simp only [Category.id_comp, eqToHom_trans] at hx
  exact Over.eq_of_left_eq_eqToHom (α.toNatTrans.app x)
    ((BasedFunctor.w_obj F₁ x).trans (BasedFunctor.w_obj F₂ x).symm) hx

end Slice

/-- The structural 1-morphism of the category of elements of `Λ_g F` to the stack represented by
`S/S'`: an element of `Λ_g F` over `W` carries a factorization `ψ : W ⟶ S` of the structure
morphism of `W`. -/
def relocalizeElementsStructureHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val ⥤ᵇ
      (schemeFibredCategory B S' hS' (Over.mk g)).val where
  toFunctor :=
    { obj := fun P => Over.mk (Over.homMk P.fiber.as.1.1 P.fiber.as.2 : P.base ⟶ Over.mk g)
      map := fun {P Q} u => Over.homMk u.base (by
        apply Over.OverMorphism.ext
        exact PresheafOfCategories.relocalizeFactorOf_map g F u)
      map_id := fun _ => Over.OverMorphism.ext rfl
      map_comp := fun _ _ => Over.OverMorphism.ext rfl }
  w := rfl

/-- The comparison followed by the structural 1-morphism of `Λ_g F` is the structural 1-morphism
of Construction A, as Stacks 04X5 equips it. -/
theorem changeBaseFibredCategoryHom_comp_structureHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    BasedFunctor.comp (changeBaseFibredCategoryHom B S S' hS hS' g F)
        (relocalizeElementsStructureHom B S S' hS hS' g F) =
      { toFunctor := (fibredCategory B S hS F).val.p ⋙
          Over.iteratedSliceBackward (Over.mk g)
        w := rfl } :=
  BasedCategory.BasedFunctor.ext' (Over.functor_ext_of_forget (fun _ => rfl) rfl)

/-- The structural 1-morphisms of lower-shriek extensions are compatible with a morphism over
`h_{S/S'}`. -/
theorem associatedMap_comp_structureHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : (OverShriek.relocalizePresheafFunctor g).obj F ⟶
      (OverShriek.relocalizePresheafFunctor g).obj G)
    (hm : m ≫ OverShriek.relocalizeToYoneda g G = OverShriek.relocalizeToYoneda g F) :
    BasedFunctor.comp (associatedMap B S' hS' m).1.hom
        (relocalizeElementsStructureHom B S S' hS hS' g G) =
      relocalizeElementsStructureHom B S S' hS hS' g F := by
  refine BasedCategory.BasedFunctor.ext' (Over.functor_ext_of_forget (fun P => ?_) rfl)
  have h := congrArg (fun k => (CommaMorphism.left (k.app (Opposite.op P.base) P.fiber.as)))
    hm
  simp only [NatTrans.comp_app, types_comp_apply] at h
  change Over.mk (Over.homMk (m.app _ P.fiber.as).1.1 (m.app _ P.fiber.as).2 :
      P.base ⟶ Over.mk g) = Over.mk (Over.homMk P.fiber.as.1.1 P.fiber.as.2)
  congr 1
  exact Over.OverMorphism.ext h

end AlgebraicGeometry.Stack
