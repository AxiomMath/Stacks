module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# Lifts of an object along an arrow out of its base, and their base change

Let `p : X ⥤ C` be a functor, `x` an object of `X` and `a : p(x) ⟶ V` an arrow of the base.
A *lift of `x` along `a`* is an object of `X` over `V` together with an arrow from `x` lying
over `a`; such lifts are the objects of the fibre of `Under.post p` over `Under.mk a`, and
their morphisms are the arrows commuting with the structure arrows, which are vertical.
Isomorphism classes of lifts are the values of the functor of lifts of a deformation
situation.

A commutative square `u ≫ a = a' ≫ g` in the base, together with an arrow `ξ` over its
left edge `u` and a strongly cartesian arrow `χ` over its right edge `g`, carries a lift
along `a` to a lift along `a'`: the structure arrow of the base change is the factorization
of `ξ` followed by the structure arrow through `χ`. A lift along `a'` admitting a cartesian
comparison arrow compatible with a given arrow out of `x'` is determined by that datum up to
isomorphism, so base change is well defined on isomorphism classes.

## Main definitions

* `Deformation.Artin.LiftAlong`, the category of lifts of `x` along `a`, and
  `Deformation.Artin.LiftAlongClasses`, its isomorphism classes.
* `Deformation.Artin.liftAlongMk` and `Deformation.Artin.liftAlongIsoMk`, a lift from an
  arrow over `a` and an isomorphism of lifts from a vertical isomorphism.
* `Deformation.Artin.liftAlongBaseChange`, the base change of a lift along a commutative
  square in the base.

## Main results

* `Deformation.Artin.liftAlongClassMk_eq_of_cartesian`, uniqueness up to isomorphism of a
  lift admitting a prescribed cartesian comparison arrow.
* `Deformation.Artin.liftAlongBaseChange_fac`, the defining factorization of the base change.
* `Deformation.Artin.liftAlongClassMk_baseChange_id` and
  `Deformation.Artin.liftAlongClassMk_baseChange_comp`, the unit and composition laws of base
  change on isomorphism classes.
-/

@[expose] public section

namespace Deformation.Artin

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]

/-- Lifts of `x` along `a : p(x) ⟶ V`: an object of `X` over `V` together with an arrow from
`x` lying over `a`, and the arrows commuting with those. -/
public abbrev LiftAlong (p : X ⥤ C) (x : X) {V : C} (a : p.obj x ⟶ V) :=
  (Under.post (X := x) p).Fiber (Under.mk a)

/-- Isomorphism classes of lifts of `x` along `a`, isomorphism being taken in the category of
lifts, that is by an arrow lying over the identity of `V`. -/
public abbrev LiftAlongClasses (p : X ⥤ C) (x : X) {V : C} (a : p.obj x ⟶ V) :=
  Quotient (isIsomorphicSetoid (LiftAlong p x a))

/-- The isomorphism class of a lift. -/
public def liftAlongClassMk {p : X ⥤ C} {x : X} {V : C} {a : p.obj x ⟶ V}
    (t : LiftAlong p x a) : LiftAlongClasses p x a :=
  Quotient.mk _ t

section

variable (p : X ⥤ C) (x : X) {V : C} (a : p.obj x ⟶ V)

/-- The target of a lift of `x` along `a : p(x) ⟶ V` lies over `V`. -/
public lemma liftAlong_base_obj (t : LiftAlong p x a) : p.obj t.1.right = V := by
  have ht := t.2
  change (Under.post (X := x) p).obj t.1 = Under.mk a at ht
  exact congrArg (fun o : Under (p.obj x) => o.right) ht

/-- The right component of a transport along an equality of objects of `Under` is a transport. -/
private lemma eqToHom_right_eq {Y : C} {o o' : Under Y} (h : o = o') (h' : o.right = o'.right) :
    (eqToHom h).right = eqToHom h' := by
  cases h
  rfl

/-- The structure arrow of a lift of `x` along `a` lies over `a`. -/
public lemma liftAlong_isHomLift (t : LiftAlong p x a) : p.IsHomLift a t.1.hom := by
  apply IsHomLift.of_fac' p a t.1.hom rfl (liftAlong_base_obj p x a t)
  have h := Under.w (eqToHom t.2)
  rw [eqToHom_right_eq _ (liftAlong_base_obj p x a t)] at h
  have h2 : p.map t.1.hom ≫ eqToHom (liftAlong_base_obj p x a t) = a := h
  simp [← h2]

/-- A morphism of lifts of `x` along `a` lies over the identity of `V`. -/
public lemma liftAlong_morphism_isHomLift {s t : LiftAlong p x a} (m : s ⟶ t) :
    p.IsHomLift (𝟙 V) m.1.right := by
  have hm : (Under.post (X := x) p).IsHomLift (𝟙 (Under.mk a)) m.1 := m.2
  have hfac := IsHomLift.fac' (Under.post (X := x) p) (𝟙 (Under.mk a)) m.1
  have hforget := congrArg ((Under.forget (p.obj x)).map) hfac
  apply IsHomLift.of_fac' p (𝟙 V) m.1.right
    (liftAlong_base_obj p x a s) (liftAlong_base_obj p x a t)
  have hforget' : p.map m.1.right =
      (eqToHom s.2).right ≫ 𝟙 V ≫ (eqToHom t.2.symm).right := by
    simpa [← Under.post_forget_eq_forget_comp, Functor.comp_map, Under.post]
      using hforget
  rwa [eqToHom_right_eq s.2 (liftAlong_base_obj p x a s),
    eqToHom_right_eq t.2.symm (liftAlong_base_obj p x a t).symm] at hforget'

/-- An arrow out of `x` lying over `a` is a lift of `x` along `a`. -/
public def liftAlongMk {z : X} (hz : p.obj z = V) (g : x ⟶ z) (hg : p.IsHomLift a g) :
    LiftAlong p x a := by
  refine ⟨Under.mk g, ?_⟩
  cases hz
  change Under.mk (p.map g) = Under.mk a
  congr 1
  simpa using IsHomLift.fac' p a g

/-- The target of the lift attached to an arrow out of `x` is the target of that arrow. -/
@[simp]
public lemma liftAlongMk_right {z : X} (hz : p.obj z = V) (g : x ⟶ z)
    (hg : p.IsHomLift a g) : (liftAlongMk p x a hz g hg).1.right = z := rfl

/-- The structure arrow of the lift attached to an arrow out of `x` is that arrow. -/
@[simp]
public lemma liftAlongMk_hom {z : X} (hz : p.obj z = V) (g : x ⟶ z)
    (hg : p.IsHomLift a g) : (liftAlongMk p x a hz g hg).1.hom = g := rfl

/-- An isomorphism over the identity of `V` commuting with the structure arrows is an
isomorphism of lifts. -/
public def liftAlongIsoMk {s t : LiftAlong p x a} (e : s.1.right ≅ t.1.right)
    (he : p.IsHomLift (𝟙 V) e.hom) (hw : s.1.hom ≫ e.hom = t.1.hom) : s ≅ t := by
  refine Functor.Fiber.isoMk (Under.isoMk e hw) ?_
  apply IsHomLift.of_fac' (Under.post (X := x) p) (𝟙 (Under.mk a))
    (Under.isoMk e hw).hom s.2 t.2
  apply Under.UnderMorphism.ext
  change p.map e.hom = _
  rw [IsHomLift.fac' p (𝟙 V) e.hom]
  simp only [Under.eqToHom_right, Under.comp_right, Under.id_right]
  congr 1

end

section BaseChange

variable {p : X ⥤ C} {x x' : X} {V V' : C} {a : p.obj x ⟶ V} {a' : p.obj x' ⟶ V'}

/-- Two lifts of `x'` along `a'` carrying strongly cartesian arrows over one and the same
`g : V' ⟶ V` into one and the same object of `X`, compatibly with their structure arrows, are
isomorphic as lifts, hence have the same class. -/
public lemma liftAlongClassMk_eq_of_cartesian {g : V' ⟶ V} {w : X}
    (s t : LiftAlong p x' a') (χ : s.1.right ⟶ w) (χ' : t.1.right ⟶ w)
    (hχ : p.IsStronglyCartesian g χ) (hχ' : p.IsStronglyCartesian g χ')
    (h : s.1.hom ≫ χ = t.1.hom ≫ χ') :
    liftAlongClassMk s = liftAlongClassMk t := by
  have hsc : p.IsCartesian g χ := inferInstance
  have hsc' : p.IsCartesian g χ' := inferInstance
  have hs : p.IsHomLift a' s.1.hom := liftAlong_isHomLift p x' a' s
  have ht : p.IsHomLift a' t.1.hom := liftAlong_isHomLift p x' a' t
  let sF : p.Fiber V' := ⟨s.1.right, liftAlong_base_obj p x' a' s⟩
  let tF : p.Fiber V' := ⟨t.1.right, liftAlong_base_obj p x' a' t⟩
  let e : sF ≅ tF := Functor.fiberIsoOfCartesian g χ χ' hsc hsc'
  let E : s.1.right ≅ t.1.right := Functor.Fiber.fiberInclusion.mapIso e
  have hE : p.IsHomLift (𝟙 V') E.hom := e.hom.2
  have hEfac : E.hom ≫ χ' = χ :=
    Functor.fiberIsoOfCartesian_hom_fac (z := sF) (z' := tF) g χ χ' hsc hsc'
  have hcomp : p.IsHomLift a' (s.1.hom ≫ E.hom) :=
    IsHomLift.comp_lift_id_right' p a' s.1.hom V' E.hom
  have hw : s.1.hom ≫ E.hom = t.1.hom := by
    refine Functor.IsStronglyCartesian.ext p g χ' a' ?_
    rw [Category.assoc, hEfac, h]
  exact Quotient.sound ⟨liftAlongIsoMk p x' a' E hE hw⟩

/-- The base change of a lift along a commutative square `u ≫ a = a' ≫ g` of the base: given
a lift `t` of `x` along `a`, an arrow `ξ : x' ⟶ x` lying over `u` and a strongly cartesian
arrow `χ : w ⟶ t.right` lying over `g`, the lift of `x'` along `a'` whose structure arrow is
the factorization of `ξ` followed by the structure arrow of `t` through `χ`. -/
public noncomputable def liftAlongBaseChange {u : p.obj x' ⟶ p.obj x} {g : V' ⟶ V} {w : X}
    (hw : p.obj w = V') (t : LiftAlong p x a) (ξ : x' ⟶ x) (hξ : p.IsHomLift u ξ)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian g χ) (hsq : u ≫ a = a' ≫ g) :
    LiftAlong p x' a' := by
  have ht : p.IsHomLift a t.1.hom := liftAlong_isHomLift p x a t
  have hcomp : p.IsHomLift (u ≫ a) (ξ ≫ t.1.hom) := inferInstance
  exact liftAlongMk p x' a' hw
    (Functor.IsStronglyCartesian.map p g χ hsq (ξ ≫ t.1.hom))
    (Functor.IsStronglyCartesian.map_isHomLift p g χ hsq (ξ ≫ t.1.hom))

/-- The target of the base change of a lift is the source of the cartesian arrow. -/
@[simp]
public lemma liftAlongBaseChange_right {u : p.obj x' ⟶ p.obj x} {g : V' ⟶ V} {w : X}
    (hw : p.obj w = V') (t : LiftAlong p x a) (ξ : x' ⟶ x) (hξ : p.IsHomLift u ξ)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian g χ) (hsq : u ≫ a = a' ≫ g) :
    (liftAlongBaseChange (a' := a') hw t ξ hξ χ hχ hsq).1.right = w := rfl

/-- The structure arrow of the base change of a lift factors `ξ` followed by the structure
arrow of the lift through the cartesian arrow `χ`. -/
public lemma liftAlongBaseChange_fac {u : p.obj x' ⟶ p.obj x} {g : V' ⟶ V} {w : X}
    (hw : p.obj w = V') (t : LiftAlong p x a) (ξ : x' ⟶ x) (hξ : p.IsHomLift u ξ)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian g χ) (hsq : u ≫ a = a' ≫ g) :
    (liftAlongBaseChange (a' := a') hw t ξ hξ χ hχ hsq).1.hom ≫ χ = ξ ≫ t.1.hom := by
  have ht : p.IsHomLift a t.1.hom := liftAlong_isHomLift p x a t
  have hcomp : p.IsHomLift (u ≫ a) (ξ ≫ t.1.hom) := inferInstance
  exact Functor.IsStronglyCartesian.fac p g χ hsq (ξ ≫ t.1.hom)

/-- A lift carrying a strongly cartesian arrow over the identity of `V'` to a second lift,
compatibly with the structure arrows, has the class of that second lift. -/
public lemma liftAlongClassMk_eq_of_cartesian_id (s t : LiftAlong p x' a')
    (χ : s.1.right ⟶ t.1.right) (hχ : p.IsStronglyCartesian (𝟙 V') χ)
    (h : s.1.hom ≫ χ = t.1.hom) : liftAlongClassMk s = liftAlongClassMk t := by
  have hid : p.IsHomLift (𝟙 V') (𝟙 t.1.right) :=
    IsHomLift.id (liftAlong_base_obj p x' a' t)
  refine liftAlongClassMk_eq_of_cartesian s t χ (𝟙 t.1.right) hχ inferInstance ?_
  simpa using h

/-- Base change along an identity square recovers the class of the lift. -/
public lemma liftAlongClassMk_baseChange_id {w : X} (hw : p.obj w = V) (t : LiftAlong p x a)
    (χ : w ⟶ t.1.right) (hχ : p.IsStronglyCartesian (𝟙 V) χ) :
    liftAlongClassMk
        (liftAlongBaseChange (a' := a) hw t (𝟙 x) (IsHomLift.id rfl) χ hχ (by simp)) =
      liftAlongClassMk t := by
  refine liftAlongClassMk_eq_of_cartesian_id _ t χ hχ ?_
  rw [liftAlongBaseChange_fac]
  simp

/-- Base change along two stacked squares of the base is base change along the composite
square: the iterated base change has the class of any lift whose structure arrow factors the
composite arrow out of `x₂` through the composite cartesian arrow. -/
public lemma liftAlongClassMk_baseChange_comp {x₁ x₂ : X} {V₁ V₂ : C}
    {a₁ : p.obj x₁ ⟶ V₁} {a₂ : p.obj x₂ ⟶ V₂}
    {u₁ : p.obj x₁ ⟶ p.obj x} {u₂ : p.obj x₂ ⟶ p.obj x₁}
    {g₁ : V₁ ⟶ V} {g₂ : V₂ ⟶ V₁} {w₁ w₂ : X}
    (hw₁ : p.obj w₁ = V₁) (hw₂ : p.obj w₂ = V₂) (t : LiftAlong p x a)
    (ξ₁ : x₁ ⟶ x) (hξ₁ : p.IsHomLift u₁ ξ₁) (ξ₂ : x₂ ⟶ x₁) (hξ₂ : p.IsHomLift u₂ ξ₂)
    (χ₁ : w₁ ⟶ t.1.right) (hχ₁ : p.IsStronglyCartesian g₁ χ₁) (hsq₁ : u₁ ≫ a = a₁ ≫ g₁)
    (χ₂ : w₂ ⟶ w₁) (hχ₂ : p.IsStronglyCartesian g₂ χ₂) (hsq₂ : u₂ ≫ a₁ = a₂ ≫ g₂)
    (s : LiftAlong p x₂ a₂) (χ : s.1.right ⟶ t.1.right)
    (hχ : p.IsStronglyCartesian (g₂ ≫ g₁) χ)
    (hs : s.1.hom ≫ χ = (ξ₂ ≫ ξ₁) ≫ t.1.hom) :
    liftAlongClassMk
        (liftAlongBaseChange (a' := a₂) hw₂
          (liftAlongBaseChange (a' := a₁) hw₁ t ξ₁ hξ₁ χ₁ hχ₁ hsq₁) ξ₂ hξ₂ χ₂ hχ₂ hsq₂) =
      liftAlongClassMk s := by
  have i₃ : p.IsStronglyCartesian (g₂ ≫ g₁) (χ₂ ≫ χ₁) :=
    Functor.IsStronglyCartesian.comp (p := p) (f := g₂) (g := g₁) (φ := χ₂) (ψ := χ₁)
  have e₁ := liftAlongBaseChange_fac (a' := a₂) hw₂
    (liftAlongBaseChange (a' := a₁) hw₁ t ξ₁ hξ₁ χ₁ hχ₁ hsq₁) ξ₂ hξ₂ χ₂ hχ₂ hsq₂
  have e₂ := liftAlongBaseChange_fac (a' := a₁) hw₁ t ξ₁ hξ₁ χ₁ hχ₁ hsq₁
  have key : ∀ (ζ : x₂ ⟶ w₂) (η : x₁ ⟶ w₁), ζ ≫ χ₂ = ξ₂ ≫ η → η ≫ χ₁ = ξ₁ ≫ t.1.hom →
      ζ ≫ χ₂ ≫ χ₁ = (ξ₂ ≫ ξ₁) ≫ t.1.hom := by
    intro ζ η hζ hη
    rw [← Category.assoc, hζ, Category.assoc, hη, Category.assoc]
  exact liftAlongClassMk_eq_of_cartesian (g := g₂ ≫ g₁) _ s (χ₂ ≫ χ₁) χ i₃ hχ
    ((key _ _ e₁ e₂).trans hs.symm)

end BaseChange

end Deformation.Artin
