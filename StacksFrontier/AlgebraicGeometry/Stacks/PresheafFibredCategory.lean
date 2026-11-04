module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# The category fibred in groupoids attached to a presheaf

Let `S` be a scheme contained in a big fppf site `B`. A set-valued presheaf on the big fppf
site of `S` becomes a presheaf of groupoids by regarding each of its values as a discrete
groupoid, and hence a category fibred in groupoids over that site, with discrete fibres. A
map of presheaves induces a 1-morphism between the attached categories, given on objects by
applying the map in the fibre.

## Main definitions

* `AlgebraicGeometry.Stack.fibredCategory`: the category fibred in groupoids attached to a
  set-valued presheaf on the big fppf site of `S`.
* `AlgebraicGeometry.Stack.associatedMap`: the 1-morphism induced by a map of presheaves,
  together with the specification of its value in each fibre.

## Main results

* `AlgebraicGeometry.Stack.associatedMap_obj`: the value of the associated 1-morphism on an
  object, as an equality rather than a heterogeneous one.
* `AlgebraicGeometry.Stack.associatedMap_comp`: the associated 1-morphism of a composite of maps
  of presheaves is the composite of the associated 1-morphisms.
* `AlgebraicGeometry.Stack.hom_ext_of_section`, `AlgebraicGeometry.Stack.hom_ext_of_obj`,
  `AlgebraicGeometry.Stack.hom_eq_of_hom₂` and `AlgebraicGeometry.Stack.subsingleton_hom₂`: a
  1-morphism into the attached category is determined by the family of elements it names, hence
  also by its action on objects; two such 1-morphisms joined by a 2-morphism are equal, and a
  2-morphism between two of them is unique.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category fibred in groupoids attached to a set-valued presheaf on the big fppf site
of `S`: the Grothendieck construction of the presheaf of discrete groupoids it defines. -/
def fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (presheafOfGroupoids (F ⋙ typeToGrpd))
    (isFiberedInGroupoids_presheafOfGroupoids (F ⋙ typeToGrpd))

/-- The 1-morphism of categories fibred in groupoids induced by a map `a` of set-valued
presheaves, together with its value on objects: it sends `(U, x)` to `(U, a_U(x))`. -/
@[stacks 0458 "associated morphism"]
def associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    {f : fibredCategory B S hS F ⟶ fibredCategory B S hS G //
      ∀ x : (fibredCategory B S hS F).val.obj,
      HEq ((CatFiberedInGroupoids.homFunctor f).obj x).fiber
          (Discrete.mk (a.app (Opposite.op x.base)
            (Discrete.as (show Discrete (F.obj (Opposite.op x.base)) from x.fiber))))} := by
  let f : (fibredCategory B S hS F).val.obj ⥤ (fibredCategory B S hS G).val.obj :=
    { obj X := ⟨X.base, Discrete.mk (a.app (Opposite.op X.base) X.fiber.as)⟩
      map {X Y} g := {
        base := g.base
        fiber := Discrete.eqToHom (by
          calc
            a.app (Opposite.op X.base) X.fiber.as =
                a.app (Opposite.op X.base)
                  (F.map g.base.op Y.fiber.as) :=
                    congrArg (a.app (Opposite.op X.base)) (Discrete.eq_of_hom g.fiber)
            _ = G.map g.base.op (a.app (Opposite.op Y.base) Y.fiber.as) := by
                    have hn := congrFun
                      (congrArg (fun q => TypeCat.homEquiv q) (a.naturality g.base.op))
                      Y.fiber.as
                    simpa only [TypeCat.homEquiv_apply, ConcreteCategory.comp_apply] using hn) }
      map_id X := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
        apply Discrete.hom_eq
      map_comp f₁ f₂ := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
        apply Discrete.hom_eq }
  let bf : (fibredCategory B S hS F).val ⥤ᵇ (fibredCategory B S hS G).val := ⟨f, rfl⟩
  exact ⟨(CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm bf, fun _ => HEq.rfl⟩

/-- The 1-morphism attached to a map `a : F ⟶ G` of set-valued presheaves sends the pair
`(U, x)` to the pair `(U, a_U(x))`. -/
@[stacks 0458 "the associated morphism on objects"]
theorem associatedMap_obj
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (x : (fibredCategory B S hS F).val.obj) :
    (associatedMap B S hS a).1.hom.obj x =
      ⟨x.base, Discrete.mk (a.app (Opposite.op x.base) x.fiber.as)⟩ := by
  have hb := congrArg (fun H => H.obj x)
    (CatFiberedInGroupoids.homFunctor_comp_p (associatedMap B S hS a).1)
  have hf := (associatedMap B S hS a).2 x
  change ((associatedMap B S hS a).1.hom.obj x).base = x.base at hb
  generalize (associatedMap B S hS a).1.hom.obj x = t at *
  rcases x with ⟨xb, xf⟩
  rcases t with ⟨tb, tf⟩
  change tb = xb at hb
  subst tb
  have ht : tf = Discrete.mk (a.app (Opposite.op xb) xf.as) := eq_of_heq hf
  cases ht
  rfl

/-! ### 1-morphisms into the category attached to a presheaf -/

section Hom

open CategoryTheory.PresheafOfCategories

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A 1-morphism into the category attached to a presheaf of sets is determined by the family
of elements it names: the image of an object `x` of `𝒳` lies over `p x`, so it names an element
of `F` there (`CategoryTheory.PresheafOfCategories.sectionOfBasedFunctor`), and two 1-morphisms
naming the same family are equal. -/
theorem hom_ext_of_section (f g : 𝒳 ⟶ fibredCategory B S hS F)
    (h : ∀ x, sectionOfBasedFunctor f.hom.toFunctor f.hom.w x =
      sectionOfBasedFunctor g.hom.toFunctor g.hom.w x) : f = g :=
  Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' (eq_of_sections_eq _ _ f.hom.w g.hom.w h))

/-- The element named by a 1-morphism at an object depends only on the image of that object. -/
theorem section_eq_of_obj_eq (f g : 𝒳 ⟶ fibredCategory B S hS F) (x : 𝒳.val.obj)
    (h : f.hom.obj x = g.hom.obj x) :
    sectionOfBasedFunctor f.hom.toFunctor f.hom.w x =
      sectionOfBasedFunctor g.hom.toFunctor g.hom.w x :=
  sectionOfBasedFunctor_congr _ _ f.hom.w g.hom.w h

/-- A 1-morphism into the category attached to a presheaf of sets is determined by its action on
objects. -/
theorem hom_ext_of_obj {f g : 𝒳 ⟶ fibredCategory B S hS F}
    (h : ∀ x, f.hom.obj x = g.hom.obj x) : f = g :=
  hom_ext_of_section B S hS f g fun x => section_eq_of_obj_eq B S hS f g x (h x)

/-- The image of an object under a 1-morphism is the pair of its base and the element it
names. -/
theorem obj_eq_mk_section (f : 𝒳 ⟶ fibredCategory B S hS F) (x : 𝒳.val.obj) :
    f.hom.obj x =
      ⟨𝒳.val.p.obj x, Discrete.mk (sectionOfBasedFunctor f.hom.toFunctor f.hom.w x)⟩ :=
  obj_eq_of_elementOf_eq (Functor.congr_obj f.hom.w x) rfl
    (elementOf_mk F (𝒳.val.p.obj x) _).symm

/-- Two 1-morphisms into the category attached to a presheaf of sets joined by a 2-morphism are
equal. -/
theorem hom_eq_of_hom₂ {f g : 𝒳 ⟶ fibredCategory B S hS F} (η : f ⟶ g) : f = g :=
  Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' (eq_of_vertical_natTrans f.hom.w g.hom.w η.hom.toNatTrans
      fun x => η.hom.isHomLift' x))

/-- A 2-morphism between two 1-morphisms into the category attached to a presheaf of sets is
unique. -/
theorem subsingleton_hom₂ (f g : 𝒳 ⟶ fibredCategory B S hS F) : Subsingleton (f ⟶ g) :=
  ⟨fun a b => Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _
    (natTrans_ext_of_vertical a.hom.toNatTrans b.hom.toNatTrans
      (fun x => a.hom.isHomLift' x) fun x => b.hom.isHomLift' x))⟩

/-- The 1-morphism attached to a composite of maps of presheaves is the composite of the two
attached 1-morphisms. -/
@[stacks 0458 "functoriality of the associated morphism"]
theorem associatedMap_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H) :
    (associatedMap B S hS (a ≫ b)).1 =
      (associatedMap B S hS a).1 ≫ (associatedMap B S hS b).1 := by
  refine hom_ext_of_obj B S hS fun x => ?_
  rw [associatedMap_obj]
  show _ = (associatedMap B S hS b).1.hom.obj ((associatedMap B S hS a).1.hom.obj x)
  rw [associatedMap_obj, associatedMap_obj]
  rfl

end Hom

end AlgebraicGeometry.Stack

end
