module

public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence

/-!
# The section named by an object of a category represented by a presheaf

Let `C` be a category, let `F` be a presheaf of sets on `C` and let `p : 𝒮 ⥤ C` be a category
over `C` which is equivalent over `C` to the category of elements of `F` (Stacks 02XV applied to
`F ⋙ typeToCat`). An object `z` of `𝒮` lying over `W` then *names* a section of `F` over `W`:
carry `z` through the equivalence and read off the element its image names. This is the
elementwise form of `CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`.

The section named is unchanged by a vertical morphism and compatible with restriction, every
section is named by some object, two objects naming the same section are vertically isomorphic,
and naming is compatible with composing equivalences.

## Main definitions

* `CategoryTheory.PresheafOfCategories.sectionOfObj`: the section of `F` over `W` named by an
  object of `𝒮` lying over `W`.
* `CategoryTheory.PresheafOfCategories.equivalenceOverOfIso`: isomorphic presheaves have
  equivalent categories of elements.

## Main results

* `CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_hom`: a vertical morphism of `𝒮` does
  not change the section named.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_map`: a morphism of `𝒮` over `f : W' ⟶ W`
  names the restriction along `f`.
* `CategoryTheory.PresheafOfCategories.exists_sectionOfObj`: every section is named by an object.
* `CategoryTheory.PresheafOfCategories.exists_hom_of_sectionOfObj_map`: the converse of
  `sectionOfObj_map`, a section equation is realised by a morphism of objects.
* `CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`: two objects of one fibre
  naming the same section are isomorphic in that fibre.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_trans`: naming through a composite of
  equivalences over `C` is naming through the second one after applying the first.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u a v₁ u₁ v₂ u₂

namespace StacksRepresentableCFG

variable {C : Type u} [Category.{v} C] {D₁ : Type u₁} [Category.{v₁} D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂]

/-- An equivalence over `C` read through an equality of the structure functor of its source. -/
def EquivalenceOver.ofEq {p p' : D₁ ⥤ C} {q : D₂ ⥤ C} (h : p = p') (e : EquivalenceOver p q) :
    EquivalenceOver p' q := by
  subst h; exact e

/-- Reading an equivalence over `C` through an equality of structure functors does not change its
underlying functor. -/
@[simp] lemma EquivalenceOver.ofEq_hom_functor {p p' : D₁ ⥤ C} {q : D₂ ⥤ C} (h : p = p')
    (e : EquivalenceOver p q) : (e.ofEq h).hom.functor = e.hom.functor := by
  subst h; rfl

end StacksRepresentableCFG

namespace CategoryTheory.PresheafOfCategories

variable {C : Type u} [Category.{v} C]

section OfIso

variable {F G : Cᵒᵖ ⥤ Type a}

/-- An isomorphism of presheaves of sets, read as a pointwise family of bijections. -/
def PointwiseEquiv.ofIso (i : F ≅ G) : PointwiseEquiv F G where
  equiv U := (i.app U).toEquiv
  naturality f s := NatTrans.naturality_apply i.hom f s

/-- Isomorphic presheaves of sets have equivalent categories of elements, over the base. -/
def equivalenceOverOfIso (i : F ≅ G) :
    StacksRepresentableCFG.EquivalenceOver (presheafOfCategories (F ⋙ typeToCat)).p
      (presheafOfCategories (G ⋙ typeToCat)).p :=
  equivalenceOverOfPointwiseEquiv (PointwiseEquiv.ofIso i)

end OfIso

section Section

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {p : 𝒮 ⥤ C} {F : Cᵒᵖ ⥤ Type a}
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The section of `F` over `W` named by an object `z` of `𝒮` lying over `W`: carry `z` through
the equivalence and read off the element of `F(W)` that its image names. -/
def sectionOfObj (z : 𝒮) {W : C} (h : p.obj z = W) : F.obj (op W) :=
  elementsFiberEquiv F W ((fiberFunctorOfComp e.hom.w W).obj (Functor.Fiber.mk h))

/-- The canonical object of the category of elements attached to a section names that section. -/
@[simp] lemma sectionOfObj_refl (X : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl
      (presheafOfCategories (F ⋙ typeToCat)).p) X rfl = X.fiber.as :=
  rfl

/-- The section named through an isomorphism of representing presheaves is the image of the
section named. -/
@[simp] lemma sectionOfObj_ofIso {G : Cᵒᵖ ⥤ Type a} (i : F ≅ G)
    (X : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    sectionOfObj (equivalenceOverOfIso i) X rfl = i.hom.app (op X.base) X.fiber.as :=
  rfl

/-- Naming a section through a composite of equivalences over `C` is naming it through the second
one after applying the first. -/
lemma sectionOfObj_trans {𝒯 : Type u₂} [Category.{v₂} 𝒯] {q : 𝒯 ⥤ C}
    (d : StacksRepresentableCFG.EquivalenceOver p q)
    (c : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : 𝒮) {W : C} (h : p.obj z = W) :
    sectionOfObj (d.trans c) z h =
      sectionOfObj c (d.hom.functor.obj z) ((Functor.congr_obj d.hom.w z).trans h) :=
  rfl

/-- A morphism of `𝒮` lying over an identity does not change the section named. -/
lemma sectionOfObj_eq_of_hom {z z' : 𝒮} {W : C} (h : p.obj z = W) (h' : p.obj z' = W)
    (φ : z ⟶ z') (hφ : p.IsHomLift (𝟙 W) φ) :
    sectionOfObj e z h = sectionOfObj e z' h' :=
  elementsFiberEquiv_eq_of_hom F ((fiberFunctorOfComp e.hom.w W).map
    (show Functor.Fiber.mk h ⟶ Functor.Fiber.mk h' from ⟨φ, hφ⟩))

/-- Two objects of one fibre of `p` isomorphic in that fibre name the same section. -/
lemma sectionOfObj_eq_of_fiberIso {z z' : 𝒮} {W : C} (h : p.obj z = W) (h' : p.obj z' = W)
    (i : (Functor.Fiber.mk h : p.Fiber W) ≅ Functor.Fiber.mk h') :
    sectionOfObj e z h = sectionOfObj e z' h' :=
  sectionOfObj_eq_of_hom e h h' (Functor.Fiber.fiberInclusion.map i.hom) i.hom.2

/-- A morphism of `𝒮` lying over `f : W' ⟶ W` names the restriction along `f` of the section
named by its target. -/
lemma sectionOfObj_map {z z' : 𝒮} {W W' : C} (h : p.obj z = W) (h' : p.obj z' = W')
    (f : W' ⟶ W) (φ : z' ⟶ z) (hφ : p.IsHomLift f φ) :
    sectionOfObj e z' h' = F.map f.op (sectionOfObj e z h) :=
  elementsFiberEquiv_map_of_isHomLift F f
    ((fiberFunctorOfComp e.hom.w W).obj (Functor.Fiber.mk h))
    ((fiberFunctorOfComp e.hom.w W').obj (Functor.Fiber.mk h'))
    (e.hom.functor.map φ) (isHomLift_map_of_comp e.hom.w f φ hφ)

/-- The unit of the equivalence, read as an isomorphism of the fibre over `W` between an object
and its round trip. -/
def fiberUnitIso (z : 𝒮) {W : C} (h : p.obj z = W) :
    (Functor.Fiber.mk h : p.Fiber W) ≅
      (fiberFunctorOfComp e.inv.w W).obj
        ((fiberFunctorOfComp e.hom.w W).obj (Functor.Fiber.mk h)) :=
  Functor.Fiber.isoMk (e.unitIso.app z) (by
    have hu := e.isHomLift_unitIso_hom_app z
    rwa [h] at hu)

/-- The image under the backward 1-morphism of the canonical object attached to a section names
that section. -/
lemma sectionOfObj_inv_obj (X : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    sectionOfObj e (e.inv.functor.obj X) (Functor.congr_obj e.inv.w X) = X.fiber.as :=
  elementsFiberEquiv_eq_of_hom F
    (Functor.Fiber.isoMk
      (a := (fiberFunctorOfComp e.hom.w X.base).obj
        (Functor.Fiber.mk (Functor.congr_obj e.inv.w X)))
      (b := Functor.Fiber.mk
        (rfl : (presheafOfCategories (F ⋙ typeToCat)).p.obj X = X.base))
      (e.counitIso.app X) (e.isHomLift_counitIso_hom_app X)).hom

/-- Every section of `F` over `W` is named by an object of `𝒮` lying over `W`. -/
lemma exists_sectionOfObj {W : C} (s : F.obj (op W)) :
    ∃ (z : 𝒮) (h : p.obj z = W), sectionOfObj e z h = s :=
  ⟨e.inv.functor.obj ⟨W, Discrete.mk s⟩,
    Functor.congr_obj e.inv.w (⟨W, Discrete.mk s⟩ :
      (presheafOfCategories (F ⋙ typeToCat)).obj),
    sectionOfObj_inv_obj e ⟨W, Discrete.mk s⟩⟩

/-- The converse of `CategoryTheory.PresheafOfCategories.elementsFiberEquiv_map_of_isHomLift`:
an equation between elements of a presheaf is realised by a morphism of its category of elements
over the morphism of `C` relating them. -/
lemma exists_hom_of_elementsFiberEquiv_map (G : Cᵒᵖ ⥤ Type a) {V U : C} (f : V ⟶ U)
    (x : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber U)
    (y : (presheafOfCategories (G ⋙ typeToCat)).p.Fiber V)
    (hs : elementsFiberEquiv G V y = G.map f.op (elementsFiberEquiv G U x)) :
    ∃ φ : y.1 ⟶ x.1, (presheafOfCategories (G ⋙ typeToCat)).p.IsHomLift f φ := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  change x.base = U at hx
  change y.base = V at hy
  subst hx hy
  change y.fiber.as = G.map f.op x.fiber.as at hs
  refine ⟨⟨f, Discrete.eqToHom hs⟩, ?_⟩
  refine IsHomLift.of_fac' _ f _ rfl rfl ?_
  show f = eqToHom rfl ≫ f ≫ eqToHom rfl
  simp

/-- A section equation is realised by a morphism of objects: if the section named by `z'` is the
restriction along `f` of the section named by `z`, then some morphism `z' ⟶ z` of `𝒮` lies over
`f`. This is the converse of `CategoryTheory.PresheafOfCategories.sectionOfObj_map`. -/
lemma exists_hom_of_sectionOfObj_map {z z' : 𝒮} {W W' : C} (h : p.obj z = W) (h' : p.obj z' = W')
    (f : W' ⟶ W) (hs : sectionOfObj e z' h' = F.map f.op (sectionOfObj e z h)) :
    ∃ φ : z' ⟶ z, p.IsHomLift f φ := by
  obtain ⟨ψ, hψ⟩ := exists_hom_of_elementsFiberEquiv_map F f
    ((fiberFunctorOfComp e.hom.w W).obj (Functor.Fiber.mk h))
    ((fiberFunctorOfComp e.hom.w W').obj (Functor.Fiber.mk h')) hs
  obtain ⟨φ, hφ⟩ : ∃ φ : z' ⟶ z, e.hom.functor.map φ = ψ :=
    have := e.toEquivalence.isEquivalence_functor
    e.toEquivalence.functor.map_surjective ψ
  refine ⟨φ, ?_⟩
  have hmap : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift f (e.hom.functor.map φ) :=
    hφ ▸ hψ
  exact ((⟨e.hom.functor, e.hom.w⟩ : BasedCategory.ofFunctor p ⥤ᵇ
    BasedCategory.ofFunctor (presheafOfCategories (F ⋙ typeToCat)).p).isHomLift_iff f φ).mp hmap

/-- Two objects of one fibre of `p` naming the same section of `F` are isomorphic in that
fibre. -/
def fiberIsoOfSectionOfObj_eq {z z' : 𝒮} {W : C} (h : p.obj z = W)
    (h' : p.obj z' = W) (hs : sectionOfObj e z h = sectionOfObj e z' h') :
    (Functor.Fiber.mk h : p.Fiber W) ≅ Functor.Fiber.mk h' :=
  fiberUnitIso e z h ≪≫
    eqToIso (congrArg (fiberFunctorOfComp e.inv.w W).obj
      ((elementsFiberEquiv F W).injective hs)) ≪≫
    (fiberUnitIso e z' h').symm

end Section

end CategoryTheory.PresheafOfCategories

end
