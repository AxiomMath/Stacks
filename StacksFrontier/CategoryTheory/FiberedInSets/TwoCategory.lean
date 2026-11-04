module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategoryIsCategory

/-!
# The 2-category of categories fibred in sets

Let `𝒞` be a category. The *2-category of categories fibred in sets over `𝒞`* has as objects the
categories over `𝒞` whose structure functor is fibred in sets, as 1-morphisms the functors `G` over
`𝒞`, i.e. those with `p' ∘ G = p`, and as 2-morphisms the morphisms of functors `t` with
`p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `CategoryTheory.CatFiberedInSets`: the 2-category of categories fibred in sets over `𝒞`;
* `CategoryTheory.CatFiberedInSets.inclusion`: its inclusion into the 2-category of categories
  fibred in groupoids over `𝒞`.

## Main results

* `CategoryTheory.Functor.isFiberedInSets_iff`: a functor is fibred in sets if and only if it is
  fibred in groupoids and all of its fibre categories are discrete; the two halves of the forward
  direction are `Functor.IsFiberedInSets.isFiberedInGroupoids` and
  `Functor.IsFiberedInSets.fiber_isDiscrete`.
* `CategoryTheory.CatFiberedInSets.inclusionTwoHomEquiv`: the inclusion is bijective on
  2-morphisms.

## Implementation notes

`CategoryTheory.Functor.IsFiberedInSets` says that every morphism of the base has a *unique* lift
with a prescribed target, i.e. that `p` is a discrete fibration. `CatFiberedInSets 𝒞` is the full
sub-2-category of Mathlib's `BasedCategory 𝒞` spanned by the categories fibred in sets, built with
`CategoryTheory.Bicategory.InducedBicategory`, so its 1-morphisms and 2-morphisms are described by
`CategoryTheory.CatFiberedInGroupoids.homEquivBasedFunctor`,
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`,
`CategoryTheory.CatFiberedInGroupoids.homEquivBasedNatTrans` and
`CategoryTheory.CatFiberedInGroupoids.map_app`, which hold for every such full sub-2-category.

## References

* [Stacks Project, Tag 0043](https://stacks.math.columbia.edu/tag/0043)
* [Stacks Project, Tag 04S8](https://stacks.math.columbia.edu/tag/04S8)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

namespace Functor.IsFiberedInSets

/-- The data of a lift `φ` of `f` in the form used by the unique lifting property. -/
private theorem domain_eq_and_map_eq (p : 𝒮 ⥤ 𝒞) {V U : 𝒞} (f : V ⟶ U) {x y : 𝒮} (φ : y ⟶ x)
    [p.IsHomLift f φ] (hx : p.obj x = U) :
    ∃ hy : p.obj (⟨y, φ⟩ : Σ y : 𝒮, y ⟶ x).1 = V,
      p.map (⟨y, φ⟩ : Σ y : 𝒮, y ⟶ x).2 = eqToHom hy ≫ f ≫ eqToHom hx.symm :=
  ⟨IsHomLift.domain_eq p f φ, IsHomLift.fac' p f φ⟩

/-- In a category fibred in sets a lift of a morphism of the base is unique together with its
domain: two morphisms into a fixed object of `𝒮` lying over the same morphism of `𝒞` have equal
domains, and are equal modulo that equality. -/
lemma eq_of_isHomLift (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] {V U : 𝒞} (f : V ⟶ U) {x y₁ y₂ : 𝒮}
    (φ₁ : y₁ ⟶ x) (φ₂ : y₂ ⟶ x) [p.IsHomLift f φ₁] [p.IsHomLift f φ₂] :
    ∃ h : y₁ = y₂, φ₁ = eqToHom h ≫ φ₂ := by
  have hx : p.obj x = U := IsHomLift.codomain_eq p f φ₁
  have h₁ := domain_eq_and_map_eq p f φ₁ hx
  have h₂ := domain_eq_and_map_eq p f φ₂ hx
  obtain ⟨rfl, hheq⟩ :=
    Sigma.mk.inj_iff.mp ((IsFiberedInSets.existsUnique_lift f x hx).unique h₁ h₂)
  exact ⟨rfl, (eq_of_heq hheq).trans (Category.id_comp φ₂).symm⟩

/-- The fibre categories of a category fibred in sets are discrete. -/
instance fiber_isDiscrete (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] (U : 𝒞) : IsDiscrete (p.Fiber U) where
  subsingleton a b :=
    ⟨fun φ ψ ↦ by
      obtain ⟨_, hc⟩ :=
        eq_of_isHomLift p (𝟙 U) (Fiber.fiberInclusion.map φ) (Fiber.fiberInclusion.map ψ)
      exact Fiber.hom_ext (hc.trans (Category.id_comp _))⟩
  eq_of_hom {a b} φ := by
    obtain ⟨h, _⟩ := eq_of_isHomLift p (𝟙 U) (Fiber.fiberInclusion.map φ)
      (Fiber.fiberInclusion.map (𝟙 b))
    exact Subtype.ext h

/-- A category fibred in sets is a category fibred in groupoids. -/
lemma isFiberedInGroupoids (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] : p.IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    obtain ⟨⟨y, φ⟩, ⟨hy, hφ⟩, -⟩ := IsFiberedInSets.existsUnique_lift f x hx
    exact ⟨y, φ, IsHomLift.of_fac' p f φ hy hx hφ⟩
  unique_lift {x y z} φ ψ f hf := by
    obtain ⟨⟨w, χ⟩, ⟨hw, hχ⟩, -⟩ := IsFiberedInSets.existsUnique_lift f y rfl
    have hχlift : p.IsHomLift f χ := IsHomLift.of_fac' p f χ hw rfl hχ
    have hcomp : p.IsHomLift (p.map ψ) (χ ≫ φ) := by
      rw [← hf]; infer_instance
    obtain ⟨hwz, hc⟩ := eq_of_isHomLift p (p.map ψ) (χ ≫ φ) ψ
    refine ⟨eqToHom hwz.symm ≫ χ, ⟨?_, ?_⟩, ?_⟩
    · simp [hχ, eqToHom_map]
    · rw [Category.assoc, hc]
      simp
    · rintro χ' ⟨hχ'map, hχ'comp⟩
      have h₁ : p.IsHomLift f χ' := IsHomLift.of_fac' p f χ' rfl rfl (by simpa using hχ'map)
      obtain ⟨_, hc'⟩ := eq_of_isHomLift p f χ' (eqToHom hwz.symm ≫ χ)
      exact hc'.trans (Category.id_comp _)

end Functor.IsFiberedInSets

/-- A functor is fibred in sets, i.e. every morphism of the base has a unique lift with a
prescribed target, if and only if it is fibred in groupoids and all of its fibre categories are
discrete. -/
lemma Functor.isFiberedInSets_iff (p : 𝒮 ⥤ 𝒞) :
    p.IsFiberedInSets ↔ p.IsFiberedInGroupoids ∧ ∀ U : 𝒞, IsDiscrete (p.Fiber U) := by
  refine ⟨fun h ↦ ⟨IsFiberedInSets.isFiberedInGroupoids p, fun U ↦ inferInstance⟩, ?_⟩
  rintro ⟨hg, hd⟩
  refine ⟨fun {U V} f x hx ↦ ?_⟩
  obtain ⟨y, φ, hφ⟩ := hg.exists_lift f x hx
  refine ⟨⟨y, φ⟩, Functor.IsFiberedInSets.domain_eq_and_map_eq p f φ hx, ?_⟩
  rintro ⟨y', φ'⟩ ⟨hy', hφ'⟩
  have h₁ : p.IsHomLift f φ' := IsHomLift.of_fac' p f φ' hy' hx hφ'
  obtain ⟨χ, ⟨hχmap, hχcomp⟩, -⟩ :=
    hg.unique_lift φ φ' (eqToHom (hy'.trans (IsHomLift.domain_eq p f φ).symm)) (by
      rw [IsHomLift.fac' p f φ, IsHomLift.fac' p f φ']
      simp)
  have hχlift : p.IsHomLift (𝟙 V) χ := IsHomLift.of_fac' p (𝟙 V) χ hy'
    (IsHomLift.domain_eq p f φ) (by rw [hχmap]; simp)
  have := hd V
  have h : y' = y :=
    congrArg (fun z : p.Fiber V ↦ z.1) (IsDiscrete.eq_of_hom (Fiber.homMk p V χ))
  subst h
  have hχid : χ = 𝟙 y' :=
    congrArg Fiber.fiberInclusion.map
      (Subsingleton.elim (Fiber.homMk p V χ) (𝟙 (Fiber.mk (p := p) (S := V) hy')))
  rw [← hχcomp, hχid, Category.id_comp]

set_option linter.checkUnivs false in
/-- The 2-category of categories fibred in sets over `𝒞`: the full sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` spanned by the categories fibred in sets.
Explicitly:

1. its objects are the categories `p : 𝒮 ⥤ 𝒞` over `𝒞` that are fibred in sets;
2. its 1-morphisms `(𝒮, p) ⟶ (𝒮', p')` are the functors `G : 𝒮 ⥤ 𝒮'` with `p' ∘ G = p`;
3. its 2-morphisms `t : G ⟶ H` are the morphisms of functors with `p'(t_x) = 𝟙 (p x)` for every
   object `x` of `𝒮`. -/
@[stacks 04S8]
abbrev CatFiberedInSets (𝒞 : Type u₁) [Category.{v₁} 𝒞] :=
  Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞)
    (Subtype.val (p := fun 𝒳 : BasedCategory.{v₂, u₂} 𝒞 ↦ 𝒳.p.IsFiberedInSets))

namespace CatFiberedInSets

open CatFiberedInGroupoids
  (homEquivBasedFunctor homFunctor homFunctor_comp_p homEquivBasedNatTrans map_app)

/-- A category over `𝒞` whose structure functor is fibred in sets, viewed as an object of the
2-category of categories fibred in sets over `𝒞`. -/
abbrev mk (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (h : 𝒳.p.IsFiberedInSets) :
    CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞 :=
  ⟨𝒳, h⟩

/-- The structure functor of an object of the 2-category of categories fibred in sets over `𝒞` is
fibred in sets. -/
instance isFiberedInSets (𝒳 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞) : 𝒳.val.p.IsFiberedInSets :=
  𝒳.2


/-- A category fibred in sets, as an object of the 2-category of categories fibred in groupoids
over `𝒞`. -/
abbrev toCatFiberedInGroupoids (𝒳 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞) :
    CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.mk 𝒳.val (Functor.IsFiberedInSets.isFiberedInGroupoids 𝒳.val.p)

/-- The inclusion of the 2-category of categories fibred in sets over `𝒞` into the 2-category of
categories fibred in groupoids over `𝒞`, as a functor on the underlying 1-categories of the two
strict bicategories. It sends an object `𝒳` to `CatFiberedInSets.toCatFiberedInGroupoids 𝒳`. -/
@[simps!]
def inclusion : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞 ⥤ CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.inclusion fun 𝒳 h ↦
    have := h
    Functor.IsFiberedInSets.isFiberedInGroupoids 𝒳.p

/-- The inclusion of the 2-category of categories fibred in sets into the 2-category of categories
fibred in groupoids is bijective on 2-morphisms. -/
def inclusionTwoHomEquiv {𝒳 𝒴 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞} (G H : 𝒳 ⟶ 𝒴) :
    (G ⟶ H) ≃ (inclusion.map G ⟶ inclusion.map H) where
  toFun t := Bicategory.InducedBicategory.Hom₂.mk t.hom
  invFun t := Bicategory.InducedBicategory.Hom₂.mk t.hom
  left_inv _ := rfl
  right_inv _ := rfl

end CatFiberedInSets

end CategoryTheory
