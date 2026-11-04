module

public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
import StacksCore.Tactic.StacksAttribute

/-!
# Categories fibred in groupoids representable by an algebraic space

A category fibred in groupoids over the big fppf site of a scheme `S` is *representable by an
algebraic space* when it is equivalent, over that site, to the category attached to the sheaf
of points of an algebraic space over `S`.

## Main definitions

* `AlgebraicGeometry.IsRepresentableByAlgebraicSpace`: this representability property.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

universe u v w

/-- A category fibred in groupoids over the big fppf site of `S` is represented by an
algebraic space over `S` if it is equivalent over the site to the category of elements of
that space's sheaf of points. -/
public abbrev AlgebraicGeometry.IsRepresentableByAlgebraicSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    (𝒳 : CategoryTheory.CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)) : Prop :=
  ∃ F : CategoryTheory.Functor (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ (Type u),
    AlgebraicGeometry.IsAlgebraicSpace B S hS F ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
        (CategoryTheory.presheafOfCategories
          (CategoryTheory.Functor.comp F CategoryTheory.typeToCat)).p)


open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Stack

/-! ### Sections of a presheaf of categories, and extensionality for presheaf morphisms -/

/-- Two elements of a family of subsingletons over equal indices are heterogeneously equal. -/
public theorem heq_of_subsingleton_family {α : Sort _} {β : α → Sort _}
    (hβ : ∀ a, Subsingleton (β a)) {a b : α} {x : β a} {y : β b}
    (h : a = b) : HEq x y := by
  cases h
  exact heq_of_eq (Subsingleton.elim _ _)

/-- The section of a set-valued presheaf named by an object of its category of elements, read over
a given object of the site identified with the base of that object. -/
public def elementSection {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*)
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj) (T : C)
    (h : x.base = T) : F.obj (Opposite.op T) :=
  F.map (eqToHom h.symm).op x.fiber.as

/-- `AlgebraicGeometry.Stack.elementSection` is natural: a morphism of the category of elements
lying over `k` restricts the section of its target to the section of its source. -/
public theorem elementSection_naturality {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*)
    {x y : (presheafOfCategories (F ⋙ typeToCat)).obj} (g : x ⟶ y)
    {T T' : C} (hx : x.base = T) (hy : y.base = T') (k : T ⟶ T')
    (hk : g.base = eqToHom hx ≫ k ≫ eqToHom hy.symm) :
    elementSection F x T hx = F.map k.op (elementSection F y T' hy) := by
  subst T
  subst T'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hk
  subst k
  have h : x.fiber.as = F.map g.base.op y.fiber.as := Discrete.eq_of_hom g.fiber
  simpa [elementSection] using h

/-- Two morphisms of the category of elements of a set-valued presheaf with the same base
component are equal: the fibre components live in a subsingleton. -/
public theorem presheaf_hom_ext {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) {x y : (presheafOfCategories (F ⋙ typeToCat)).obj}
    {f g : x ⟶ y} (h : f.base = g.base) : f = g :=
  (PresheafOfCategories.homEquiv (F ⋙ typeToCat) x y).injective <| Sigma.ext h <|
    heq_of_subsingleton_family
      (β := fun k : x.base ⟶ y.base =>
        x.fiber ⟶ ((F ⋙ typeToCat).map k.op).toFunctor.obj y.fiber)
      (fun _ => ⟨fun _ _ => Discrete.hom_eq⟩) h

/-- A based functor between the categories of elements of two set-valued presheaves is a morphism
of presheaves: it moves the section named by an element to the section named by its image. -/
public def presheafMapOfBasedFunctor {C : Type*} [Category C]
    {F G : Cᵒᵖ ⥤ Type u}
    (a : presheafOfCategories (F ⋙ typeToCat) ⥤ᵇ
      presheafOfCategories (G ⋙ typeToCat)) : F ⟶ G where
  app T := ↾fun s => elementSection G (a.obj ⟨T.unop, Discrete.mk s⟩) T.unop
    (congrArg (fun K => K.obj ⟨T.unop, Discrete.mk s⟩) a.w)
  naturality {T T'} k := by
    ext s
    let x : (presheafOfCategories (F ⋙ typeToCat)).obj :=
      ⟨T'.unop, Discrete.mk (F.map k s)⟩
    let y : (presheafOfCategories (F ⋙ typeToCat)).obj :=
      ⟨T.unop, Discrete.mk s⟩
    let j : x ⟶ y := ⟨k.unop, Discrete.eqToHom rfl⟩
    exact elementSection_naturality G (a.map j) (a.w_obj x) (a.w_obj y) k.unop
      (CategoryTheory.Functor.congr_hom a.w j)

end AlgebraicGeometry.Stack

end
