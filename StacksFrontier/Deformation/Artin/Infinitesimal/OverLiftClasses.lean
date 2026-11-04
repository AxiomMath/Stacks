module

public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback

/-!
# Lifts in a slice category are arrows

Let `U` be an object of a category `C` and regard the slice `C/U` as a category over `C` through
the forgetful functor `C/U ⥤ C`. This is how a scheme `U` over `S` is a category fibred in
groupoids over the big site of `S` (`AlgebraicGeometry.Stack.schemeFibredCategory`), and in the
deformation theory of Artin's Axioms a *lift* of an object `x : V ⟶ U` of the slice along an
arrow `a : V ⟶ V'` of `C` is an object of the slice over `V'` together with an arrow from `x`
lying over `a`.

For a slice the lifts carry no more information than the arrows they produce: the isomorphism
classes of lifts of `x` along `a` are in bijection with the arrows `g : V' ⟶ U` restricting to
`x` along `a`, i.e. with `a ≫ g = x`. This is the first step in computing the tangent spaces
`T_x(M)` of a scheme, the third paragraph of the proof of Stacks 0DNT, where `a` is the
square-zero immersion `Spec A ⟶ Spec A[M]`.

## Main definitions

* `Deformation.Artin.overLiftHom` — the arrow `V' ⟶ U` of a lift.
* `Deformation.Artin.overLiftOfHom` — the lift attached to an arrow `V' ⟶ U` restricting to `x`.
* `Deformation.Artin.overLiftClassEquiv` — the bijection between isomorphism classes of lifts
  and arrows restricting to `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace Deformation.Artin

section OverLift

universe u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] (U : C) {x : Over U} {V V' : C}
  (hx : (Over.forget U).obj x = V) (aa : V ⟶ V')

/-- The arrow `V' ⟶ U` of a lift of `x : V ⟶ U` along `a : V ⟶ V'`: the structure arrow of the
lifted object of the slice. -/
public def overLiftHom (t : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    V' ⟶ U :=
  eqToHom (underFiber_right_obj (Over.forget U) hx aa t).symm ≫ t.1.right.hom

/-- The structure arrow of a lift, read in `C`. -/
public theorem overLift_hom_left
    (t : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    t.1.hom.left =
      eqToHom hx ≫ aa ≫ eqToHom (underFiber_right_obj (Over.forget U) hx aa t).symm := by
  have hl := underFiber_isHomLift (Over.forget U) hx aa t
  exact IsHomLift.fac' (Over.forget U) aa t.1.hom

/-- The arrow of a lift restricts to `x` along `a`. -/
public theorem overLiftHom_spec
    (t : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    aa ≫ overLiftHom U hx aa t = eqToHom hx.symm ≫ x.hom := by
  have hw := Over.w t.1.hom
  rw [overLift_hom_left U hx aa t] at hw
  rw [overLiftHom, ← hw]
  simp

/-- An arrow of the slice between the objects of two lifts, lying over `D`, composes the arrows. -/
private theorem overLiftHom_eq_comp_aux {y : Over U} {W W' : C}
    (hy : (Over.forget U).obj y = W) {cc : W ⟶ W'} (D : W' ⟶ V')
    (u : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa)))
    (v : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hy ≫ cc)))
    (ρ : v.1.right ⟶ u.1.right) (hρ : (Over.forget U).IsHomLift D ρ) :
    overLiftHom U hy cc v = D ≫ overLiftHom U hx aa u := by
  have hfac := IsHomLift.fac' (Over.forget U) D ρ
  have hw := Over.w ρ
  change ρ.left = _ at hfac
  rw [hfac] at hw
  rw [overLiftHom, overLiftHom, ← hw]
  simp

/-- A morphism of lifts does not change the arrow. -/
public theorem overLiftHom_eq_of_hom
    {t s : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))} (α : t ⟶ s) :
    overLiftHom U hx aa t = overLiftHom U hx aa s := by
  simpa using overLiftHom_eq_comp_aux U hx aa hx (𝟙 V') s t α.1.right
    (underPost_isHomLift_right (Over.forget U) (𝟙 _) α.1 α.2)

/-- The arrow `x ⟶ (V' ⟶ U)` of the slice lying over `a`, for an arrow `g` restricting to `x`. -/
public def overLiftArrow (g : V' ⟶ U) (hg : aa ≫ g = eqToHom hx.symm ≫ x.hom) :
    x ⟶ Over.mk g :=
  Over.homMk (eqToHom hx ≫ aa) (by
    change (eqToHom hx ≫ aa) ≫ g = x.hom
    rw [Category.assoc, hg]
    simp)

/-- The arrow `overLiftArrow` lies over `a`. -/
public theorem overLiftArrow_isHomLift (g : V' ⟶ U) (hg : aa ≫ g = eqToHom hx.symm ≫ x.hom) :
    (Over.forget U).IsHomLift aa (overLiftArrow U hx aa g hg) := by
  apply IsHomLift.of_fac (Over.forget U) aa _ hx rfl
  change aa = eqToHom hx.symm ≫ (eqToHom hx ≫ aa) ≫ eqToHom rfl
  simp

/-- The lift of `x` along `a` attached to an arrow `g : V' ⟶ U` restricting to `x`. -/
public def overLiftOfHom (g : V' ⟶ U) (hg : aa ≫ g = eqToHom hx.symm ≫ x.hom) :
    (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa)) :=
  underFiberObjMk (Over.forget U) hx aa (overLiftArrow U hx aa g hg)
    (overLiftArrow_isHomLift U hx aa g hg)

/-- The arrow of the lift attached to `g` is `g`. -/
public theorem overLiftHom_overLiftOfHom (g : V' ⟶ U)
    (hg : aa ≫ g = eqToHom hx.symm ≫ x.hom) :
    overLiftHom U hx aa (overLiftOfHom U hx aa g hg) = g := by
  change eqToHom (rfl : V' = V') ≫ g = g
  simp

/-- Every lift is isomorphic to the lift attached to its arrow. -/
public def overLiftIso (t : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    t ≅ overLiftOfHom U hx aa (overLiftHom U hx aa t) (overLiftHom_spec U hx aa t) := by
  have ht := underFiber_right_obj (Over.forget U) hx aa t
  let g := overLiftHom U hx aa t
  let χ : t.1.right ⟶ Over.mk g := Over.homMk (eqToHom ht) (by
    change eqToHom ht ≫ (eqToHom ht.symm ≫ t.1.right.hom) = t.1.right.hom
    simp)
  let χ' : Over.mk g ⟶ t.1.right := Over.homMk (eqToHom ht.symm) (by
    change eqToHom ht.symm ≫ t.1.right.hom = eqToHom ht.symm ≫ t.1.right.hom
    rfl)
  have hχ : (Over.forget U).IsHomLift (𝟙 V') χ := by
    apply IsHomLift.of_fac (Over.forget U) (𝟙 V') χ ht rfl
    change 𝟙 V' = eqToHom ht.symm ≫ eqToHom ht ≫ eqToHom rfl
    simp
  have hχ' : (Over.forget U).IsHomLift (𝟙 V') χ' := by
    apply IsHomLift.of_fac (Over.forget U) (𝟙 V') χ' rfl ht
    change 𝟙 V' = eqToHom rfl ≫ eqToHom ht.symm ≫ eqToHom ht
    simp
  have hw : t.1.hom ≫ χ = (overLiftOfHom U hx aa g (overLiftHom_spec U hx aa t)).1.hom := by
    apply Over.OverMorphism.ext
    change t.1.hom.left ≫ eqToHom ht = eqToHom hx ≫ aa
    rw [overLift_hom_left U hx aa t]
    simp
  have hw' : (overLiftOfHom U hx aa g (overLiftHom_spec U hx aa t)).1.hom ≫ χ' = t.1.hom := by
    apply Over.OverMorphism.ext
    change (eqToHom hx ≫ aa) ≫ eqToHom ht.symm = t.1.hom.left
    rw [overLift_hom_left U hx aa t]
    simp
  refine
    { hom := underFiberHomMk (Over.forget U) hx aa χ hχ hw
      inv := underFiberHomMk (Over.forget U) hx aa χ' hχ' hw'
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Functor.Fiber.hom_ext
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    change eqToHom ht ≫ eqToHom ht.symm = 𝟙 _
    simp
  · apply Functor.Fiber.hom_ext
    apply Under.UnderMorphism.ext
    apply Over.OverMorphism.ext
    change eqToHom ht.symm ≫ eqToHom ht = 𝟙 _
    simp

/-- **Lifts in a slice category are arrows.** The isomorphism classes of lifts of
`x : V ⟶ U` along `a : V ⟶ V'` are in bijection with the arrows `g : V' ⟶ U` with
`a ≫ g = x`. -/
public def overLiftClassEquiv :
    Quotient (isIsomorphicSetoid
        ((Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa)))) ≃
      { g : V' ⟶ U // aa ≫ g = eqToHom hx.symm ≫ x.hom } where
  toFun := Quotient.lift (fun t => ⟨overLiftHom U hx aa t, overLiftHom_spec U hx aa t⟩)
    (fun _ _ h => Subtype.ext (overLiftHom_eq_of_hom U hx aa h.some.hom))
  invFun g := Quotient.mk _ (overLiftOfHom U hx aa g.1 g.2)
  left_inv := by
    intro c
    induction c using Quotient.ind with
    | _ t => exact Quotient.sound ⟨(overLiftIso U hx aa t).symm⟩
  right_inv := by
    intro g
    exact Subtype.ext (overLiftHom_overLiftOfHom U hx aa g.1 g.2)

/-- The bijection `overLiftClassEquiv` sends the class of a lift to its arrow. -/
@[simp]
public theorem overLiftClassEquiv_mk
    (t : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    (overLiftClassEquiv U hx aa (Quotient.mk _ t)).1 = overLiftHom U hx aa t := rfl

/-- **An arrow between two lifts lying over `D` composes their arrows.** If `ρ` is an arrow of
the slice from a lift `v` of `y` along `c` to a lift `u` of `x` along `a`, lying over
`D : W' ⟶ V'`, then the arrow of `v` is `D` followed by the arrow of `u`. -/
public theorem overLiftHom_eq_comp_of_isHomLift {y : Over U} {W W' : C}
    (hy : (Over.forget U).obj y = W) {cc : W ⟶ W'} (D : W' ⟶ V')
    (u : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hx ≫ aa)))
    (v : (Under.post (Over.forget U)).Fiber (Under.mk (eqToHom hy ≫ cc)))
    (ρ : v.1.right ⟶ u.1.right) (hρ : (Over.forget U).IsHomLift D ρ) :
    overLiftHom U hy cc v = D ≫ overLiftHom U hx aa u :=
  overLiftHom_eq_comp_aux U hx aa hy D u v ρ hρ

end OverLift

end Deformation.Artin

end
