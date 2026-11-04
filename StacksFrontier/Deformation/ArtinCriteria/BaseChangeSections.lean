module

public import StacksFrontier.Deformation.ArtinCriteria.BaseChangeRetraction
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange

/-!
# Sections of the algebraic space representing a base change, read as arrows of `𝒳`

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `x` be an object over
`U` and `y` the 2-Yoneda functor of an object over `V`, and let `F` be an algebraic space over `V`
representing the 2-fibre product `(Sch/V) ×_{y, 𝒳, x} (Sch/U)`. A section `s` of `F` over an object
`T` of the site over `V` is a triple `(a, a', α)`: here it is read as an arrow `y(T) ⟶ x` of `𝒳`,
the composite of the comparison isomorphism `α` with the chosen cartesian arrow over the first
component.

## Main definitions

* `Deformation.Artin.BaseChange.pointArrow`: the arrow `y(P.x) ⟶ x` of an object `P` of the
  2-fibre product.
* `Deformation.Artin.BaseChange.sectionArrow`: the arrow `y(T) ⟶ x` of a section of `F`.

## Main results

* `Deformation.Artin.BaseChange.pointArrow_comp`: naturality for morphisms of the 2-fibre
  product.
* `Deformation.Artin.BaseChange.sectionArrow_comp`: naturality for restriction of sections.
* `Deformation.Artin.BaseChange.sectionArrow_hom_obj`: the arrow of the section attached to an
  object of the 2-fibre product is the arrow of that object.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.BaseChange

universe u v w

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.BasedCategory.ofFunctor

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
  (U V : AlgebraicGeometry.BigFppfOver B S hS)
  (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
  (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)

/-- The chosen cartesian arrow of the 2-Yoneda functor of `x` at an object of the slice. -/
def cartArrow (a : Over U) :
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩).obj a ⟶ x :=
  (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ a).φ

/-- The chosen cartesian arrow at `a` is strongly cartesian over `a.hom`. -/
instance (a : Over U) : 𝒳.val.p.IsStronglyCartesian a.hom (cartArrow B S hS 𝒳 U x hx a) :=
  (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩ a).isStronglyCartesian

/-- The image of a morphism `g : a ⟶ a'` of the slice under the 2-Yoneda functor of `x`, composed
with the chosen cartesian arrow at `a'`, is the chosen cartesian arrow at `a`. -/
@[reassoc]
theorem map_cartArrow {a a' : Over U} (g : a ⟶ a') :
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩).map g ≫
      cartArrow B S hS 𝒳 U x hx a' = cartArrow B S hS 𝒳 U x hx a := by
  have := (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
    a').isStronglyCartesian
  have := (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
    a).isStronglyCartesian
  exact Functor.IsStronglyCartesian.fac 𝒳.val.p a'.hom _ (Over.w g).symm _

/-- The arrow `y(P.x) ⟶ x` of an object of the 2-fibre product. -/
def pointArrow (P : BaseChangeProduct B S hS 𝒳 U V x hx y) : y.obj P.x ⟶ x :=
  P.iso.hom ≫ cartArrow B S hS 𝒳 U x hx P.y

/-- **Naturality of the arrow of a point.** -/
theorem pointArrow_comp {P Q : BaseChangeProduct B S hS 𝒳 U V x hx y} (m : P ⟶ Q) :
    y.map m.a ≫ pointArrow B S hS 𝒳 U V x hx y Q = pointArrow B S hS 𝒳 U V x hx y P := by
  simp only [pointArrow]
  rw [← Category.assoc, m.w, Category.assoc, map_cartArrow]

variable (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
  (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)

/-- The arrow `y(T) ⟶ x` of a section of `F` over `T`. -/
def sectionArrow (c : (presheafOfCategories (F ⋙ typeToCat)).obj) : y.obj c.base ⟶ x :=
  y.map (eqToHom (inv_obj_x e c).symm) ≫
    pointArrow B S hS 𝒳 U V x hx y (e.inv.functor.obj c)

/-- **Naturality of the arrow of a section.** -/
theorem sectionArrow_comp {c d : (presheafOfCategories (F ⋙ typeToCat)).obj} (f : c ⟶ d) :
    y.map f.base ≫ sectionArrow B S hS 𝒳 U V x hx y F e d =
      sectionArrow B S hS 𝒳 U V x hx y F e c := by
  have hm := Functor.congr_hom e.inv.w f
  change (e.inv.functor.map f).a = _ at hm
  simp only [sectionArrow]
  rw [← pointArrow_comp B S hS 𝒳 U V x hx y (e.inv.functor.map f), ← Category.assoc,
    ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hm,
    show (presheafOfCategories (F ⋙ typeToCat)).p.map f = f.base from rfl]
  simp only [eqToHom_trans_assoc]
  congr 2

/-- **The arrow of the section attached to a point is the arrow of the point.** -/
theorem sectionArrow_hom_obj (Q : BaseChangeProduct B S hS 𝒳 U V x hx y)
    (hQ : (e.hom.functor.obj Q).base = Q.x) :
    sectionArrow B S hS 𝒳 U V x hx y F e (e.hom.functor.obj Q) =
      y.map (eqToHom hQ) ≫ pointArrow B S hS 𝒳 U V x hx y Q := by
  let m : e.inv.functor.obj (e.hom.functor.obj Q) ⟶ Q := e.unitIso.inv.app Q
  have hm : (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget U) 𝒳.val.p y
      (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U
        ⟨x, hx⟩).toFunctor).IsHomLift (𝟙 Q.x) m := by
    have : (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget U) 𝒳.val.p y
        (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U
          ⟨x, hx⟩).toFunctor).IsHomLift (𝟙 Q.x) (e.unitIso.hom.app Q) :=
      e.isHomLift_unitIso_hom_app Q
    rw [show m = inv (e.unitIso.hom.app Q) by simp [m]]
    exact IsHomLift.lift_id_inv_isIso _ _ _
  have hma : m.a = eqToHom (by rw [inv_obj_x e, hQ]) := by
    simpa using IsHomLift.fac' (TwoFibreProductOver.fst (Over.map V.hom) (Over.forget U)
      𝒳.val.p y (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U
        ⟨x, hx⟩).toFunctor) (𝟙 Q.x) m
  simp only [sectionArrow]
  rw [← pointArrow_comp B S hS 𝒳 U V x hx y m, hma, ← Category.assoc, ← Functor.map_comp,
    eqToHom_trans]

/-- **The arrow of a section lies over the projection of the section to `U`.** -/
private theorem sectionArrow_isHomLift (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (c : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    𝒳.val.p.IsHomLift ((baseChangeProjection B S hS 𝒳 U V x hx y F e).app c)
      (sectionArrow B S hS 𝒳 U V x hx y F e c) := by
  let P := e.inv.functor.obj c
  have hP : P.x = c.base := inv_obj_x e c
  rw [baseChangeProjection_app B S hS 𝒳 U V x hx y F e c hP]
  have h1 : 𝒳.val.p.IsHomLift (eqToHom (congrArg (Over.map V.hom).obj hP.symm))
      (y.map (eqToHom hP.symm)) := by
    refine IsHomLift.of_fac' _ _ _ (Functor.congr_obj hy c.base)
      (Functor.congr_obj hy P.x) ?_
    simp only [eqToHom_map, eqToHom_trans]
  have h2 : 𝒳.val.p.IsHomLift (eqToHom (P.hx.trans P.hy.symm)) P.iso.hom := by
    have := P.vertical
    refine IsHomLift.of_fac' _ _ _ (Functor.congr_obj hy P.x) ?_ ?_
    · exact IsHomLift.codomain_eq 𝒳.val.p (𝟙 P.base) P.iso.hom |>.trans P.hy.symm
    · rw [IsHomLift.fac' 𝒳.val.p (𝟙 P.base) P.iso.hom]
      simp
  have h3 : 𝒳.val.p.IsHomLift P.y.hom (cartArrow B S hS 𝒳 U x hx P.y) :=
    inferInstance
  exact @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1
    (@IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 h3)

end Deformation.Artin.BaseChange
