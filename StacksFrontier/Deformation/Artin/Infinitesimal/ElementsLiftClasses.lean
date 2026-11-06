module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory

/-!
# Lifts in the category of elements of a presheaf

Let `F` be a presheaf of sets on the big fppf site of `S` and `𝒢 = fibredCategory F` its category
of elements, the category fibred in groupoids whose objects over `T` are the sections of `F`
over `T`. For a section `e₀` of `F` over `T₀` and an arrow `a : T₀ ⟶ T₁` of the site, a lift of
the object `(T₀, e₀)` along `a` — an object of `𝒢` over `T₁` with an arrow from `(T₀, e₀)` lying
over `a` — is the same thing as a section of `F` over `T₁` restricting to `e₀` along `a`, and two
lifts are isomorphic exactly when their sections agree.

This is the dictionary through which the lift classes of Stacks 07Y9 at a point of an algebraic
space are read as sections of the space.

## Main definitions

* `Deformation.Artin.elemObj`, `Deformation.Artin.elemHom`: the object `(T, g)` of `𝒢` and the
  arrow `(T', F(t) g) ⟶ (T, g)` over `t : T' ⟶ T`.
* `Deformation.Artin.elemSecAt`: the section of `F` named by an object of `𝒢` over `T`.
* `Deformation.Artin.elemLift`: the lift of `(T₀, e₀)` along `a` named by a section over `T₁`.
* `Deformation.Artin.elemLiftClassEquiv`: the isomorphism classes of lifts are the sections over
  `T₁` restricting to `e₀`.

## Main results

* `Deformation.Artin.elemSecAt_hom`: an arrow of `𝒢` over `t` relates the two sections by `F(t)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite AlgebraicGeometry AlgebraicGeometry.Stack

namespace Deformation.Artin

universe u

attribute [local implicit_reducible] Bicategory.InducedBicategory CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion fibredCategory
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget

section ElementsLifts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The object `(T, g)` of the category of elements of `F`. -/
abbrev elemObj (T : BigFppfOver B S hS) (g : F.obj (op T)) :
    (fibredCategory B S hS F).val.obj :=
  ⟨T, Discrete.mk g⟩

/-- The object `(T, g)` of the category of elements lies over `T`. -/
theorem elemObj_p_obj (T : BigFppfOver B S hS) (g : F.obj (op T)) :
    (fibredCategory B S hS F).val.p.obj (elemObj F T g) = T := rfl

/-- The arrow `(T', g') ⟶ (T, g)` of the category of elements over `t : T' ⟶ T`, for
`g' = F(t) g`. -/
def elemHom {T T' : BigFppfOver B S hS} (t : T' ⟶ T) {g : F.obj (op T)} {g' : F.obj (op T')}
    (h : g' = F.map t.op g) : elemObj F T' g' ⟶ elemObj F T g where
  base := t
  fiber := Discrete.eqToHom h

/-- The base of the arrow `elemHom F t h` is `t`. -/
theorem elemHom_base {T T' : BigFppfOver B S hS} (t : T' ⟶ T) {g : F.obj (op T)}
    {g' : F.obj (op T')} (h : g' = F.map t.op g) : (elemHom F t h).base = t := rfl

/-- The arrow `elemHom F t h` lies over `t`. -/
instance elemHom_isHomLift {T T' : BigFppfOver B S hS} (t : T' ⟶ T) {g : F.obj (op T)}
    {g' : F.obj (op T')} (h : g' = F.map t.op g) :
    (fibredCategory B S hS F).val.p.IsHomLift t (elemHom F t h) :=
  Functor.IsHomLift.map (p := (fibredCategory B S hS F).val.p) (elemHom F t h)

/-- An arrow of the category of elements is determined by its base. -/
theorem elem_hom_ext {o o' : (fibredCategory B S hS F).val.obj} (u v : o ⟶ o')
    (h : u.base = v.base) : u = v := by
  obtain ⟨ub, uf⟩ := u
  obtain ⟨vb, vf⟩ := v
  change ub = vb at h
  subst h
  congr 1
  exact Discrete.hom_eq

/-- The fibre component of an arrow of the category of elements. -/
theorem elem_fiber_eq {o o' : (fibredCategory B S hS F).val.obj} (u : o ⟶ o') :
    o.fiber.as = F.map u.base.op o'.fiber.as :=
  Discrete.eq_of_hom u.fiber

/-- The section of `F` over `T` named by an object of the category of elements lying over `T`. -/
def elemSecAt (o : (fibredCategory B S hS F).val.obj) (T : BigFppfOver B S hS)
    (h : o.base = T) : F.obj (op T) :=
  F.map (eqToHom h.symm).op o.fiber.as

/-- The section named by the object `(T, g)` over `T` is `g`. -/
@[simp]
theorem elemSecAt_elemObj (T : BigFppfOver B S hS) (g : F.obj (op T)) (h : T = T) :
    elemSecAt F (elemObj F T g) T h = g := by
  simp [elemSecAt]

/-- **An arrow of the category of elements over `t` relates the two sections by `F(t)`.** -/
theorem elemSecAt_hom {o o' : (fibredCategory B S hS F).val.obj} {T T' : BigFppfOver B S hS}
    (t : T ⟶ T') (u : o ⟶ o') [(fibredCategory B S hS F).val.p.IsHomLift t u]
    (h : o.base = T) (h' : o'.base = T') :
    elemSecAt F o T h = F.map t.op (elemSecAt F o' T' h') := by
  have hu : u.base = eqToHom h ≫ t ≫ eqToHom h'.symm :=
    IsHomLift.fac' (fibredCategory B S hS F).val.p t u
  unfold elemSecAt
  rw [elem_fiber_eq F u, hu, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp]
  congr 2
  simp

/-- Transporting a section of `F` along an equality `T = T'` and back gives the original section. -/
theorem map_eqToHom_op_map_eqToHom_op {T T' : BigFppfOver B S hS} (h : T = T')
    (z : F.obj (op T)) : F.map (eqToHom h).op (F.map (eqToHom h.symm).op z) = z := by
  subst h
  simp

variable {T₀ T₁ : BigFppfOver B S hS} (e₀ : F.obj (op T₀)) (a : T₀ ⟶ T₁)

/-- The lifts of `(T₀, e₀)` along `a`. -/
abbrev ElemLiftFib :=
  (Under.post (fibredCategory B S hS F).val.p).Fiber
    (Under.mk (eqToHom (elemObj_p_obj F T₀ e₀) ≫ a))

/-- The lift of `(T₀, e₀)` along `a` named by a section `g` over `T₁` restricting to `e₀`. -/
def elemLift (g : F.obj (op T₁)) (hg : e₀ = F.map a.op g) : ElemLiftFib F e₀ a :=
  ⟨Under.mk (elemHom F a hg), by
    change Under.mk a = Under.mk (eqToHom (elemObj_p_obj F T₀ e₀) ≫ a)
    exact congrArg Under.mk (Category.id_comp a).symm⟩

/-- The arrow of the lift `elemLift F e₀ a g hg` is `elemHom F a hg`. -/
theorem elemLift_hom (g : F.obj (op T₁)) (hg : e₀ = F.map a.op g) :
    (elemLift F e₀ a g hg).1.hom = elemHom F a hg := rfl

/-- The section over `T₁` named by a lift of `(T₀, e₀)` along `a`. -/
def elemLiftSec (ℓ : ElemLiftFib F e₀ a) : F.obj (op T₁) :=
  elemSecAt F ℓ.1.right T₁ (underFiber_right_obj _ (elemObj_p_obj F T₀ e₀) a ℓ)

/-- The section named by the lift `elemLift F e₀ a g hg` is `g`. -/
@[simp]
theorem elemLiftSec_elemLift (g : F.obj (op T₁)) (hg : e₀ = F.map a.op g) :
    elemLiftSec F e₀ a (elemLift F e₀ a g hg) = g :=
  elemSecAt_elemObj F T₁ g _

/-- The section named by a lift restricts to `e₀`. -/
theorem elemLiftSec_cond (ℓ : ElemLiftFib F e₀ a) : F.map a.op (elemLiftSec F e₀ a ℓ) = e₀ := by
  have := underFiber_isHomLift _ (elemObj_p_obj F T₀ e₀) a ℓ
  have h := elemSecAt_hom F a ℓ.1.hom (rfl : (elemObj F T₀ e₀).base = T₀)
    (underFiber_right_obj _ (elemObj_p_obj F T₀ e₀) a ℓ)
  rw [elemSecAt_elemObj] at h
  exact h.symm

/-- Isomorphic (indeed, related by any arrow of) lifts name the same section. -/
theorem elemLiftSec_eq_of_hom {ℓ ℓ' : ElemLiftFib F e₀ a} (χ : ℓ ⟶ ℓ') :
    elemLiftSec F e₀ a ℓ = elemLiftSec F e₀ a ℓ' := by
  have : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 T₁) χ.1.right :=
    underPost_isHomLift_right _ (𝟙 _) χ.1 χ.2
  have h := elemSecAt_hom F (𝟙 T₁) χ.1.right
    (underFiber_right_obj _ (elemObj_p_obj F T₀ e₀) a ℓ)
    (underFiber_right_obj _ (elemObj_p_obj F T₀ e₀) a ℓ')
  rw [op_id, Functor.map_id_apply] at h
  exact h

/-- Every lift is related to the lift named by its section. -/
def toElemLift (ℓ : ElemLiftFib F e₀ a) :
    ℓ ⟶ elemLift F e₀ a (elemLiftSec F e₀ a ℓ) (elemLiftSec_cond F e₀ a ℓ).symm := by
  have hT : ℓ.1.right.base = T₁ := underFiber_right_obj _ (elemObj_p_obj F T₀ e₀) a ℓ
  have hfib : ℓ.1.right.fiber.as = F.map (eqToHom hT).op (elemLiftSec F e₀ a ℓ) :=
    (map_eqToHom_op_map_eqToHom_op F hT _).symm
  let χ : ℓ.1.right ⟶ (elemLift F e₀ a (elemLiftSec F e₀ a ℓ)
      (elemLiftSec_cond F e₀ a ℓ).symm).1.right :=
    elemHom F (g' := ℓ.1.right.fiber.as) (eqToHom hT) hfib
  have hχ : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 T₁) χ := by
    have : (fibredCategory B S hS F).val.p.IsHomLift (eqToHom hT) χ :=
      elemHom_isHomLift F (eqToHom hT) hfib
    exact IsHomLift.of_fac' _ (𝟙 T₁) χ hT rfl (by
      rw [IsHomLift.fac' (fibredCategory B S hS F).val.p (eqToHom hT) χ]
      simp)
  refine underFiberHomMk _ (elemObj_p_obj F T₀ e₀) a χ hχ ?_
  apply elem_hom_ext
  have := underFiber_isHomLift _ (elemObj_p_obj F T₀ e₀) a ℓ
  have hb : ℓ.1.hom.base = eqToHom rfl ≫ a ≫ eqToHom hT.symm :=
    IsHomLift.fac' (fibredCategory B S hS F).val.p a ℓ.1.hom
  change ℓ.1.hom.base ≫ eqToHom hT = a
  rw [hb]
  simp

/-- **The lift classes of `(T₀, e₀)` along `a` are the sections over `T₁` restricting to `e₀`.** -/
def elemLiftClassEquiv :
    Quotient (isIsomorphicSetoid (ElemLiftFib F e₀ a)) ≃ {g : F.obj (op T₁) // F.map a.op g = e₀}
    where
  toFun := Quotient.lift (fun ℓ ↦ ⟨elemLiftSec F e₀ a ℓ, elemLiftSec_cond F e₀ a ℓ⟩)
    (fun _ _ ⟨i⟩ ↦ Subtype.ext (elemLiftSec_eq_of_hom F e₀ a i.hom))
  invFun g := Quotient.mk _ (elemLift F e₀ a g.1 g.2.symm)
  left_inv := by
    intro c
    induction c using Quotient.ind with
    | _ ℓ =>
      have : IsGroupoid (ElemLiftFib F e₀ a) :=
        (underPost_isFiberedInGroupoids _ (fibredCategory B S hS F).isFiberedInGroupoids
          (elemObj F T₀ e₀)).fiber_isGroupoid _
      exact Quotient.sound ⟨(asIso (toElemLift F e₀ a ℓ)).symm⟩
  right_inv := by
    intro g
    exact Subtype.ext (elemLiftSec_elemLift F e₀ a g.1 g.2.symm)

/-- `elemLiftClassEquiv` sends the class of a lift `ℓ` to the section named by `ℓ`. -/
theorem elemLiftClassEquiv_mk (ℓ : ElemLiftFib F e₀ a) :
    (elemLiftClassEquiv F e₀ a (Quotient.mk _ ℓ)).1 = elemLiftSec F e₀ a ℓ := rfl

/-- The inverse of `elemLiftClassEquiv` sends a section `g` to the class of the lift named by
`g`. -/
theorem elemLiftClassEquiv_symm_apply (g : {g : F.obj (op T₁) // F.map a.op g = e₀}) :
    (elemLiftClassEquiv F e₀ a).symm g = Quotient.mk _ (elemLift F e₀ a g.1 g.2.symm) := rfl

/-- The arrow between the lifts named by `g` and by its restriction along `m : T₂ ⟶ T₁`, for a
second arrow `a₂ : T₀ ⟶ T₂` with `a₂ ≫ m = a`. -/
theorem exists_elemLift_hom {T₂ : BigFppfOver B S hS} (a₂ : T₀ ⟶ T₂) (m : T₂ ⟶ T₁)
    (hm : a₂ ≫ m = a) (g : F.obj (op T₁)) (hg : e₀ = F.map a.op g)
    (hg₂ : e₀ = F.map a₂.op (F.map m.op g)) :
    ∃ φ : (elemLift F e₀ a₂ (F.map m.op g) hg₂).1.right ⟶ (elemLift F e₀ a g hg).1.right,
      (fibredCategory B S hS F).val.p.IsStronglyCartesian m φ ∧
      (elemLift F e₀ a₂ (F.map m.op g) hg₂).1.hom ≫ φ = (elemLift F e₀ a g hg).1.hom :=
  ⟨elemHom F m rfl, (fibredCategory B S hS F).isFiberedInGroupoids.isStronglyCartesian_homLift
    m (elemHom F m (g := g) rfl), elem_hom_ext F _ _ hm⟩

end ElementsLifts

end Deformation.Artin
