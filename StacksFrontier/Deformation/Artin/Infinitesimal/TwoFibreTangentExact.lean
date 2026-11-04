module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreLiftGroupoid

/-!
# Exactness of the tangent half of the six-term sequence of a 2-fibre product

Let `P : 𝒳 ⟶ 𝒴` and `Q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S` and let `w = (x, z, φ)` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over
`Spec A`.  This file proves the two exactness assertions of Stacks 0DNN that live in the
tangent half of the sequence

`… ⟶ Inf_y(M) --δ--> T_w(M) ⟶ T_x(M) ⊕ T_z(M) ⟶ T_y(M)`,

namely exactness at `T_w(M)` and at `T_x(M) ⊕ T_z(M)`.  Both are the dictionary between lifts
of `w` and compatible pairs of lifts of `x` and of `z`, read on isomorphism classes: a lift of
`w` whose two components are trivial is, after transporting along those trivialisations, a
boundary deformation; and a pair of lifts of `x` and of `z` whose images in the lifts of `y`
are isomorphic glues to a lift of `w`.

## Main results

* `Deformation.Artin.twoFibreLift_image_class_eq`: the two images in `T_y(M)` of a lift of `w`
  agree — the comparison isomorphism of the lift is an isomorphism of lifts of `y`.
* `Deformation.Artin.exact_tangentProj_tangentLegDiff`: **Stacks 0DNN, exactness at
  `T_x(M) ⊕ T_z(M)`**.
* `Deformation.Artin.exact_boundary_tangentProj`: **Stacks 0DNN, exactness at `T_w(M)`**.

## References

* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### Reducing exactness to the two components -/

section ExactAlgebra
universe z₁ z₂ z₃ z₄

variable {R : Type*} [Ring R] {N : Type z₁} {M₁ : Type z₂} {M₂ : Type z₃} {L : Type z₄}
  [AddCommGroup N] [Module R N] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup L] [Module R L]

/-- Exactness of a `prod` followed by a signed `coprod`, in terms of the components: the
image of the pair map is the set of pairs on which the two legs agree. -/
public theorem exact_prod_coprod_neg (c₁ : N →ₗ[R] M₁) (c₂ : N →ₗ[R] M₂) (d₁ : M₁ →ₗ[R] L)
    (d₂ : M₂ →ₗ[R] L)
    (h : ∀ (u : M₁) (v : M₂), d₁ u = d₂ v ↔ ∃ ζ, c₁ ζ = u ∧ c₂ ζ = v) :
    Function.Exact (LinearMap.prod c₁ c₂) (LinearMap.coprod d₁ (-d₂)) := by
  intro b
  simp only [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero,
    Set.mem_range, LinearMap.prod_apply, Prod.ext_iff]
  exact h b.1 b.2

/-- Exactness of a map followed by a `prod`, in terms of the components. -/
public theorem exact_prod (δ : L →ₗ[R] N) (c₁ : N →ₗ[R] M₁) (c₂ : N →ₗ[R] M₂)
    (h : ∀ ζ : N, (c₁ ζ = 0 ∧ c₂ ζ = 0) ↔ ∃ β, δ β = ζ) :
    Function.Exact δ (LinearMap.prod c₁ c₂) := by
  intro ζ
  constructor
  · intro hz
    exact (h ζ).1 ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  · rintro ⟨β, hβ⟩
    obtain ⟨h1, h2⟩ := (h ζ).2 ⟨β, hβ⟩
    exact Prod.ext h1 h2

/-- Exactness of a signed `coprod` followed by a map, in terms of the components. -/
public theorem exact_coprod_neg (d₁ : M₁ →ₗ[R] L) (d₂ : M₂ →ₗ[R] L) (δ : L →ₗ[R] N)
    (h : ∀ β : L, δ β = 0 ↔ ∃ (u : M₁) (v : M₂), d₁ u - d₂ v = β) :
    Function.Exact (LinearMap.coprod d₁ (-d₂)) δ := by
  intro β
  rw [h β]
  constructor
  · rintro ⟨u, v, huv⟩
    exact ⟨(u, v), by simpa only [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.1, c.2, by
      simpa only [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg] using hc⟩

end ExactAlgebra

/-! ### Morphisms of lifts are isomorphisms -/

section LiftIso
open Functor
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]

/-- A morphism of lifts of `x` is an isomorphism: the lifts form a category fibred in
groupoids. -/
public theorem isIso_liftHom (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {x : X}
    {U : Under (p.obj x)} {s t : (Under.post p).Fiber U} (m : s ⟶ t) : IsIso m := by
  have := (underPost_isFiberedInGroupoids p hp x).fiber_isGroupoid U
  exact IsGroupoid.all_isIso m

/-- A morphism of lifts of `x`, as an isomorphism. -/
public def liftHomIso (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {x : X}
    {U : Under (p.obj x)} {s t : (Under.post p).Fiber U} (m : s ⟶ t) : s ≅ t :=
  have := isIso_liftHom p hp m
  asIso m

/-- The inverse of a vertical isomorphism is vertical. -/
public theorem isHomLift_inv_vertical (p : X ⥤ C) (R : C) {a b : X} (φ : a ≅ b)
    (hφ : p.IsHomLift (𝟙 R) φ.hom) : p.IsHomLift (𝟙 R) φ.inv := by
  have := hφ
  infer_instance

end LiftIso

section TwoFibreTangentExact
open Functor CategoryTheory.TwoFibreProductOver
universe u v₁ w₁ v₂ w₂ v₃ w₃

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒵 : Type v₂} [Category.{w₂} 𝒵]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  {p𝒳 : 𝒳 ⥤ BigFppfOver B S hS} {p𝒵 : 𝒵 ⥤ BigFppfOver B S hS}
  {p𝒴 : 𝒴 ⥤ BigFppfOver B S hS} {P : 𝒳 ⥤ 𝒴} {Q : 𝒵 ⥤ 𝒴}
  (hP : P ⋙ p𝒴 = p𝒳) (hQ : Q ⋙ p𝒴 = p𝒵)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q)
  (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w = algebraOver A B S hS toS hA)

/-- The comparison isomorphism of a lift of `w`, read as a morphism of lifts of `y = P x`
from the image of its `𝒳`-component to the image of its `𝒵`-component. -/
public def twoFibreLiftEta (M : SiteModule A B) (d : TwoFibreLift A B S hS toS hA w hw M) :
    (squareZeroLiftPost A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) M).obj
      ((squareZeroLiftPost A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw M).obj d) ⟶
    (squareZeroLiftTransport A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
        (twoFibreFstImageOver A B S hS toS hA hP w hw)
        (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
        (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) M).obj
      ((squareZeroLiftPost A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
        (twoFibreSndOver A B S hS toS hA w hw) M).obj
        ((squareZeroLiftPost A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw M).obj
          d)) :=
  underFiberHomMk p𝒴 (twoFibreFstImageOver A B S hS toS hA hP w hw)
    (squareZeroArrow A B S hS toS hA M) ((d.1.right).iso).hom
    (twoFibreLiftIso_isHomLift A B S hS toS hA hP hQ w hw M d) (d.1.hom).w

include h𝒴 in
/-- **The two images in the lifts of `y` of a lift of `w` have the same isomorphism class.**
This is the composite `T_w(M) ⟶ T_x(M) ⊕ T_z(M) ⟶ T_y(M)` of the six-term sequence being
zero, read on representatives. -/
public theorem twoFibreLift_image_class_eq (M : SiteModule A B)
    (d : TwoFibreLift A B S hS toS hA w hw M) :
    liftClassOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
        (twoFibreFstOver A B S hS toS hA w hw) M
        (liftClassOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw M
          (Quotient.mk _ d)) =
      liftClassOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
        (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
        (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
        (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) M
        (liftClassOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw M
          (Quotient.mk _ d)) :=
  Quotient.sound ⟨liftHomIso p𝒴 h𝒴
    (twoFibreLiftEta A B S hS toS hA hP hQ w hw M d)⟩

variable (TW : TangentFunctorData A B S hS toS hA
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw)
  (TX : TangentFunctorData A B S hS toS hA p𝒳 w.x (twoFibreFstOver A B S hS toS hA w hw))
  (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (twoFibreSndOver A B S hS toS hA w hw))
  (TY : TangentFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
    (twoFibreFstImageOver A B S hS toS hA hP w hw))

/-- **Stacks 0DNN, exactness at `T_x(M) ⊕ T_z(M)`.**  A pair of lifts of `x` and of `z` whose
images in the lifts of `y` are isomorphic is the pair of components of a lift of `w`, glued
along that isomorphism; and conversely the two images of a lift of `w` are isomorphic through
its comparison isomorphism. -/
public theorem exact_tangentProj_tangentLegDiff (M : SiteModule A B) :
    Function.Exact
      (LinearMap.prod
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX
          h𝒳 M)
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ
          h𝒵 M))
      (LinearMap.coprod
        (tangentLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) TX TY h𝒴 M)
        (-twoFibreTangentSideMap A B S hS toS hA hP hQ h𝒴 w hw TZ TY M)) := by
  refine exact_prod_coprod_neg _ _ _ _ (fun u v => ?_)
  constructor
  · intro huv
    obtain ⟨s, hs⟩ := Quotient.exists_rep (TX.liftEquiv M u)
    obtain ⟨t, ht⟩ := Quotient.exists_rep (TZ.liftEquiv M v)
    have hcls : liftClassOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) M (Quotient.mk _ s) =
        liftClassOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) M (Quotient.mk _ t) := by
      rw [hs, ht]
      exact (liftEquiv_tangentMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) TX TY M u).symm.trans
        ((congrArg (TY.liftEquiv M) huv).trans
          (liftEquiv_tangentMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
            (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
            (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
            (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) TZ TY M v))
    obtain ⟨ψ⟩ := Quotient.exact hcls
    refine ⟨(TW.liftEquiv M).symm (Quotient.mk _
        (twoFibreLiftGlue A B S hS toS hA w hw M s t (fiberEndRightIso p𝒴 h𝒴 ψ.hom)
          (underPost_isHomLift_right p𝒴 (𝟙 _) ψ.hom.1 ψ.hom.2) (Under.w ψ.hom.1))), ?_, ?_⟩
    · apply (TX.liftEquiv M).injective
      refine Eq.trans (liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX M _)
        ?_
      rw [Equiv.apply_symm_apply, ← hs]
      rfl
    · apply (TZ.liftEquiv M).injective
      refine Eq.trans (liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
        (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ M _)
        ?_
      rw [Equiv.apply_symm_apply, ← ht]
      rfl
  · rintro ⟨ζ, h1, h2⟩
    apply (TY.liftEquiv M).injective
    obtain ⟨d, hd⟩ := Quotient.exists_rep (TW.liftEquiv M ζ)
    have e1 := liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX M ζ
    have e2 := liftEquiv_tangentMapOfOneMorphism A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ M ζ
    refine (liftEquiv_tangentMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) TX TY M u).trans (Eq.trans ?_
        (liftEquiv_tangentMapOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
          (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) TZ TY M v).symm)
    rw [← h1, ← h2]
    refine Eq.trans (congrArg (liftClassOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) M) e1) ?_
    refine Eq.trans ?_ (congrArg (liftClassOfOneMorphismTransport A B S hS toS hA p𝒵 p𝒴 Q hQ
      w.y (twoFibreSndOver A B S hS toS hA w hw) (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) M) e2).symm
    rw [← hd]
    exact twoFibreLift_image_class_eq A B S hS toS hA hP hQ h𝒴 w hw M d

/-- If a tangent vector goes to `0` under the map induced by a `1`-morphism, a representative of
its lift class goes to the class of the trivial deformation. -/
private theorem liftClass_eq_trivialDeformation_of_tangentMap_eq_zero {X : Type v₁}
    [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y] (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS) (F : X ⥤ Y) (hF : F ⋙ q = p) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA)
    (T : TangentFunctorData A B S hS toS hA p x hx)
    (T' : TangentFunctorData A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx))
    (hq : q.IsFiberedInGroupoids) (M : SiteModule A B) (ζ : T.functor.obj M)
    (d : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)))
    (hd : Quotient.mk _ d = T.liftEquiv M ζ)
    (h : tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M ζ = 0) :
    liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M (Quotient.mk _ d) =
      Quotient.mk _ (trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M) := by
  rw [hd, ← liftEquiv_tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M ζ, h]
  exact liftEquiv_zero A B S hS toS hA q (F.obj x) _ hq T' M

include h𝒳 h𝒵 in
/-- **Stacks 0DNN, exactness at `T_w(M)`.**  A lift of `w` whose two components are trivial
is, after transporting along those two trivialisations, a lift with components the trivial
deformations of `x` and of `z`; its comparison isomorphism is then the twist by a unique
infinitesimal automorphism of the trivial deformation of `y`, which is the preimage under the
boundary map.  Conversely the two components of a boundary deformation are trivial by
construction. -/
public theorem exact_boundary_tangentProj
    (InfY : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (twoFibreFstImageOver A B S hS toS hA hP w hw) h𝒴)
    (M : SiteModule A B) :
    Function.Exact (boundaryLinearMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M)
      (LinearMap.prod
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX
          h𝒳 M)
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
          (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ
          h𝒵 M)) := by
  refine exact_prod _ _ _ (fun ζ => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨d, hd⟩ := Quotient.exists_rep (TW.liftEquiv M ζ)
    have ha := liftClass_eq_trivialDeformation_of_tangentMap_eq_zero A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.fst_comp_eq w hw TW TX h𝒳 M
      ζ d hd h1
    have hb := liftClass_eq_trivialDeformation_of_tangentMap_eq_zero A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P Q) TwoFibreProductOver.snd_comp_eq w hw TW TZ h𝒵 M
      ζ d hd h2
    obtain ⟨a⟩ := Quotient.exact ha
    obtain ⟨b⟩ := Quotient.exact hb
    obtain ⟨aI, haI⟩ : ∃ e : (d.1.right).x ≅
        (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.right, e.hom = a.hom.1.right :=
      ⟨fiberEndRightIso p𝒳 h𝒳 a.hom, rfl⟩
    obtain ⟨bI, hbI⟩ : ∃ e : (d.1.right).y ≅
        (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.right, e.hom = b.hom.1.right :=
      ⟨fiberEndRightIso p𝒵 h𝒵 b.hom, rfl⟩
    have hav : p𝒳.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) aI.hom := by
      rw [haI]; exact underPost_isHomLift_right p𝒳 (𝟙 _) a.hom.1 a.hom.2
    have hbv : p𝒵.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) bI.hom := by
      rw [hbI]; exact underPost_isHomLift_right p𝒵 (𝟙 _) b.hom.1 b.hom.2
    have havi := isHomLift_inv_vertical p𝒳 (squareZeroOver A B S hS toS M) aI hav
    have hbvi := isHomLift_inv_vertical p𝒵 (squareZeroOver A B S hS toS M) bI hbv
    have hwa : (d.1.hom).a ≫ aI.hom = (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom := by
      rw [haI]; exact Under.w a.hom.1
    have hwb : (d.1.hom).b ≫ bI.hom = (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom := by
      rw [hbI]; exact Under.w b.hom.1
    have hPai := lift_map_isHomLift p𝒳 p𝒴 P hP (𝟙 (squareZeroOver A B S hS toS M))
      (underFiber_right_obj p𝒳 (twoFibreFstOver A B S hS toS hA w hw)
        (squareZeroArrow A B S hS toS hA M) (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M))
      (((d.1.right)).hx.trans (twoFibreLift_base A B S hS toS hA w hw M d)) _ havi
    have hQb := lift_map_isHomLift p𝒵 p𝒴 Q hQ (𝟙 (squareZeroOver A B S hS toS M))
      (((d.1.right)).hy.trans (twoFibreLift_base A B S hS toS hA w hw M d))
      (underFiber_right_obj p𝒵 (twoFibreSndOver A B S hS toS hA w hw)
        (squareZeroArrow A B S hS toS hA M) (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M)) _ hbv
    have hid := P.map_hom_inv' aI
    have hidQ := Q.map_hom_inv' bI
    have hsq : P.map ((twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom) ≫ (P.map aI.inv ≫
        ((d.1.right).iso).hom ≫ Q.map bI.hom) = w.iso.hom ≫
        Q.map ((twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom) := by
      rw [← hwa, ← hwb, P.map_comp_assoc, reassoc_of% hid, reassoc_of% (d.1.hom).w, Q.map_comp]
    have hvψ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) (P.map aI.inv ≫
        ((d.1.right).iso).hom ≫ Q.map bI.hom) :=
      isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hPai
        (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M)
          (twoFibreLiftIso_isHomLift A B S hS toS hA hP hQ w hw M d) hQb)
    have hvβ : p𝒴.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
        ((trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).hom ≫
          (P.map aI.inv ≫ ((d.1.right).iso).hom ≫ Q.map bI.hom) ≫
              (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).inv ≫
              (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).inv) :=
      isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M)
        (trivialComparison_isHomLift A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M)
        (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M) hvψ
          (isHomLift_comp_vertical p𝒴 (squareZeroOver A B S hS toS M)
            (isHomLift_inv_vertical p𝒴 (squareZeroOver A B S hS toS M)
              (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M)
              (trivialComparison_isHomLift A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
                (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M))
            (isHomLift_inv_vertical p𝒴 (squareZeroOver A B S hS toS M)
              (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M)
              (trivialTransportComparison_isHomLift A B S hS toS hA p𝒴 (P.obj w.x)
                (Q.obj w.y) (twoFibreFstImageOver A B S hS toS hA hP w hw)
                (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
                (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M))))
    have e1 := trivialComparisonIso_comp A B S hS toS hA p𝒳 p𝒴 P hP w.x
      (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M
    have e2 := trivialComparisonIso_comp A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
      (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M
    have e3 := trivialTransportComparisonIso_comp A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
      (twoFibreFstImageOver A B S hS toS hA hP w hw)
      (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
      (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M
    have hkey : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.hom ≫
        (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).hom ≫ (P.map aI.inv ≫
              ((d.1.right).iso).hom ≫ Q.map bI.hom) =
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.hom ≫
            (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).hom ≫
              (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).hom := by
      rw [reassoc_of% e1, hsq, reassoc_of% e3, e2]
    have hcomm : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.hom ≫
        ((trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).hom ≫
          (P.map aI.inv ≫ ((d.1.right).iso).hom ≫ Q.map bI.hom) ≫
              (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).inv ≫
              (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).inv) =
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M).1.hom := by
      simp only [Category.assoc, reassoc_of% hkey, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id]
    obtain ⟨βa, hβr⟩ : ∃ χ : (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M) ⟶
        (twoFibreTrivFstImage A B S hS toS hA hP h𝒴 w hw M),
        χ.1.right = (trivialComparisonIso A B S hS toS hA p𝒳 p𝒴 P hP w.x
          (twoFibreFstOver A B S hS toS hA w hw) h𝒳 h𝒴 M).hom ≫
          (P.map aI.inv ≫ ((d.1.right).iso).hom ≫ Q.map bI.hom) ≫
              (trivialComparisonIso A B S hS toS hA p𝒵 p𝒴 Q hQ w.y
          (twoFibreSndOver A B S hS toS hA w hw) h𝒵 h𝒴 M).inv ≫
              (trivialTransportComparisonIso A B S hS toS hA p𝒴 (P.obj w.x) (Q.obj w.y)
          (twoFibreFstImageOver A B S hS toS hA hP w hw)
          (twoFibreSndImageOver A B S hS toS hA hQ w hw) w.iso
          (twoFibreIso_isHomLift A B S hS toS hA hP hQ w hw) h𝒴 M).inv :=
      ⟨underFiberHomMk p𝒴 (twoFibreFstImageOver A B S hS toS hA hP w hw)
        (squareZeroArrow A B S hS toS hA M) _ hvβ hcomm, rfl⟩
    have hbdry : (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M βa).hom = P.map aI.inv ≫
        ((d.1.right).iso).hom ≫ Q.map bI.hom := by
      rw [boundaryIso_hom, hβr]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    have hsqf : P.map aI.inv ≫ ((d.1.right).iso).hom =
        (boundaryIso A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M βa).hom ≫ Q.map bI.inv := by
      rw [hbdry]
      simp only [Category.assoc]
      rw [hidQ, Category.comp_id]
    have hdaf : (twoFibreTrivFst A B S hS toS hA h𝒳 w hw M).1.hom ≫ aI.inv = (d.1.hom).a := by
      rw [← hwa, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hdbf : (twoFibreTrivSnd A B S hS toS hA h𝒵 w hw M).1.hom ≫ bI.inv = (d.1.hom).b := by
      rw [← hwb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ⟨(InfY.autEquiv M).symm βa, ?_⟩
    apply (TW.liftEquiv M).injective
    refine Eq.trans
      (liftEquiv_twoFibreBoundaryMap A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW M _) ?_
    rw [Equiv.apply_symm_apply, ← hd]
    exact Quotient.sound ⟨liftHomIso _ (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q
      h𝒳 h𝒵 h𝒴 hP hQ) (twoFibreLiftHom A B S hS toS hA w hw M
        (boundaryLift A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw M βa) d
        aI.inv bI.inv havi hbvi hsqf hdaf hdbf)⟩
  · rintro ⟨β, hβ⟩
    refine ⟨?_, ?_⟩
    · rw [← hβ]
      exact tangentMap_twoFibreBoundaryMap_fst A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW TX M β
    · rw [← hβ]
      exact tangentMap_twoFibreBoundaryMap_snd A B S hS toS hA hP hQ h𝒳 h𝒵 h𝒴 w hw InfY TW TZ M β

end TwoFibreTangentExact

end Deformation.Artin

end
