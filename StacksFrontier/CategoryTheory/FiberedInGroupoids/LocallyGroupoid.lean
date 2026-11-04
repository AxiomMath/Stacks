module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# The 2-category of categories fibred in groupoids is locally groupoidal

Let `𝒞` be a category. A `2`-morphism of the `2`-category of categories fibred in groupoids
over `𝒞` is a morphism of functors over `𝒞` all of whose components lie over an identity of
`𝒞`; since the fibres of a category fibred in groupoids are groupoids, every such component is
an isomorphism, hence so is the `2`-morphism. So that `2`-category is locally groupoidal, i.e. a
`(2,1)`-category.

## Main results

* `CategoryTheory.BasedCategory.isGroupoid_basedFunctor`: for a category `𝒴` fibred in
  groupoids over `𝒞`, the category of functors over `𝒞` from any category over `𝒞` to `𝒴` is a
  groupoid.
* `CategoryTheory.CatFiberedInGroupoids.homGroupoid`: a hom-category of the `2`-category of
  categories fibred in groupoids is a groupoid.
* `CategoryTheory.CatFiberedInGroupoids.isIso_two`: every `2`-morphism of the `2`-category of
  categories fibred in groupoids is invertible.
* `CategoryTheory.CatFiberedInGroupoids.twoIso`: a `2`-morphism, read as a `2`-isomorphism.
* `CategoryTheory.CatFiberedInGroupoids.basedIsoOfHom₂`: the isomorphism of functors over `𝒞`
  underlying a `2`-morphism.
* `CategoryTheory.BasedFunctor.eq_of_toFunctor_eq`: a based functor is determined by its
  underlying functor.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- A functor over `𝒞` is determined by its underlying functor. -/
theorem BasedFunctor.eq_of_toFunctor_eq {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞} {F G : 𝒳 ⥤ᵇ 𝒴}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- For a category `𝒴` fibred in groupoids over `𝒞`, the category of functors over `𝒞` from a
category `𝒳` over `𝒞` to `𝒴` is a groupoid. -/
theorem BasedCategory.isGroupoid_basedFunctor {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞}
    (h𝒴 : 𝒴.p.IsFiberedInGroupoids) : IsGroupoid (𝒳 ⥤ᵇ 𝒴) where
  all_isIso {F _} α := by
    have happ : ∀ a : 𝒳.obj, IsIso (α.toNatTrans.app a) := by
      intro a
      have := h𝒴.isStronglyCartesian_homLift (𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a)
      exact Functor.IsStronglyCartesian.isIso_of_base_isIso
        (p := 𝒴.p) (f := 𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a)
    have : IsIso (X := F.toFunctor) α.toNatTrans :=
      (NatTrans.isIso_iff_isIso_app α.toNatTrans).2 happ
    exact BasedNatIso.isIso_of_toNatTrans_isIso α

/-- A hom-category of the `2`-category of categories fibred in groupoids over `𝒞` is a
groupoid, so that `2`-category is locally groupoidal. -/
instance CatFiberedInGroupoids.homGroupoid
    (𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) : IsGroupoid (𝒳 ⟶ 𝒴) :=
  letI : IsGroupoid (𝒳.based ⥤ᵇ 𝒴.based) :=
    BasedCategory.isGroupoid_basedFunctor 𝒴.isFiberedInGroupoids
  Bicategory.InducedBicategory.homGroupoid 𝒳 𝒴

/-- The isomorphism of functors over `𝒞` underlying a 2-morphism of categories fibred in
groupoids. -/
noncomputable def CatFiberedInGroupoids.basedIsoOfHom₂
    {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞} {F G : 𝒳 ⟶ 𝒴} (t : F ⟶ G) :
    F.hom ≅ G.hom := by
  have := BasedCategory.isGroupoid_basedFunctor (𝒳 := 𝒳.val) 𝒴.isFiberedInGroupoids
  exact asIso t.hom

namespace CatFiberedInGroupoids

variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞} {G H : 𝒳 ⟶ 𝒴}

/-- Every `2`-morphism of the `2`-category of categories fibred in groupoids is invertible. -/
theorem isIso_two (t : G ⟶ H) : IsIso t :=
  IsGroupoid.all_isIso t

/-- A `2`-morphism of the `2`-category of categories fibred in groupoids, read as a
`2`-isomorphism. -/
noncomputable def twoIso (t : G ⟶ H) : G ≅ H :=
  @asIso _ _ _ _ t (isIso_two t)

/-- The forward direction of `CategoryTheory.CatFiberedInGroupoids.twoIso` is the given
`2`-morphism. -/
@[simp]
theorem twoIso_hom (t : G ⟶ H) : (twoIso t).hom = t :=
  rfl

end CatFiberedInGroupoids

end CategoryTheory

end
