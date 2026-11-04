module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.LiftAction
public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.Presentation
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
import all StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.LiftAction
import all StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.Presentation

/-!
# The comparison of `Inf_x(I)` with the infinitesimal automorphisms of a lift

This file continues
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.LiftAction`; it is the last of
the three files re-exported by
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts`. It shows that the module
structure on `Inf_x` is composition of automorphisms, defines the geometric difference of
infinitesimal automorphisms and `Deformation.Artin.InfComparisonData`, and proves
**Stacks 07Y9 part (1)** at a general deformation situation,
`Deformation.Artin.exists_infComparison`.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Deformation.Artin.squareZeroRing
  CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

universe u v w

namespace Deformation.Artin

section Deformations

variable (A : Type u) [CommRing A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-! ### The module structure on `Inf_x` is composition of automorphisms -/

section InfinitesimalAddition

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- Restriction along a module map preserves composition of automorphisms. -/
private theorem infAut_map_comp {M N : SiteModule A B} (f : M ⟶ N)
    (θ θ' : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj M) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f (θ ≫ θ') =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ ≫
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ' := by
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  have h1 := infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f (θ ≫ θ')
  have h2 := infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f θ
  have h3 := infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f θ'
  rw [h2, h3]
  exact h1.trans (fiberEndRestrict_map_comp (Under.post p)
    (underPost_isFiberedInGroupoids p hp x) _ _ θ θ')

include hp in
/-- Restriction along the sum of the two projections of `M × M` is the composite of the
restrictions along the projections. -/
private theorem infAut_map_sum (hRS : SatisfiesRSStar B S hS p hp) (M : SiteModule A B)
    (θ : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj
      (siteModuleProd A B hA M M)) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
        (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) θ =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleFst A B hA M M) θ ≫
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleSnd A B hA M M) θ :=
  map_add_of_interchange A B hA
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp)
    (fun N => 𝟙 (trivialDeformation A B S hS toS hA p x hx hp N))
    (fun _ a b => a ≫ b) (fun _ a => Category.comp_id a) (fun _ a => Category.id_comp a)
    (fun f a b => infAut_map_comp A B S hS toS hA p x hx hp f a b) M
    (fun a => infinitesimalAutomorphismSetFunctor_map_zero A B S hS toS hA p x hx hp M a)
    (infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp hRS M M)
    θ

include hp in
/-- **The module structure on `Inf_x(M)` is composition.** The addition supplied by
Stacks 06I6 on the infinitesimal automorphisms of a trivial deformation is the composition
of automorphisms, so the identification of `Inf_x(M)` with those automorphisms is an
isomorphism of groups. -/
private theorem autEquiv_add (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (M : SiteModule A B) (a b : Inf.functor.obj M) :
    Inf.autEquiv M (a + b) = Inf.autEquiv M a ≫ Inf.autEquiv M b := by
  have hcomp : (Equiv.prodCongr (Inf.autEquiv M) (Inf.autEquiv M)) ∘
      (fun z : Inf.functor.obj (siteModuleProd A B hA M M) =>
        (Inf.functor.map (siteModuleFst A B hA M M) z,
          Inf.functor.map (siteModuleSnd A B hA M M) z)) =
      (fun θ : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj
          (siteModuleProd A B hA M M) =>
        ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
            (siteModuleFst A B hA M M) θ,
          (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
            (siteModuleSnd A B hA M M) θ)) ∘
        (Inf.autEquiv (siteModuleProd A B hA M M)) := by
    funext z
    exact Prod.ext (Inf.autEquiv_natural _ z) (Inf.autEquiv_natural _ z)
  have hbij : Function.Bijective
      (fun z : Inf.functor.obj (siteModuleProd A B hA M M) =>
        (Inf.functor.map (siteModuleFst A B hA M M) z,
          Inf.functor.map (siteModuleSnd A B hA M M) z)) := by
    refine (Function.Bijective.of_comp_iff'
      (Equiv.prodCongr (Inf.autEquiv M) (Inf.autEquiv M)).bijective _).mp ?_
    rw [hcomp]
    exact (infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp
      hRS M M).comp (Inf.autEquiv (siteModuleProd A B hA M M)).bijective
  obtain ⟨z, hz⟩ := hbij.2 (a, b)
  have ha : Inf.functor.map (siteModuleFst A B hA M M) z = a := congrArg Prod.fst hz
  have hb : Inf.functor.map (siteModuleSnd A B hA M M) z = b := congrArg Prod.snd hz
  have hsum : Inf.functor.map
      (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) z = a + b := by
    rw [← ha, ← hb]
    exact ConcreteCategory.congr_hom Inf.functor.map_add z
  have e4 := infAut_map_sum A B S hS toS hA p x hx hp hRS M
    (Inf.autEquiv (siteModuleProd A B hA M M) z)
  rw [← hsum, Inf.autEquiv_natural, e4, ← Inf.autEquiv_natural, ← Inf.autEquiv_natural, ha, hb]
  rfl

end InfinitesimalAddition

/-! ### Infinitesimal automorphisms across a deformation situation -/

section InfinitesimalComparison

variable (hp : p.IsFiberedInGroupoids)

/-- An infinitesimal automorphism `α` of a lift `x'` of `x` over a square-zero deformation
`A' → A` is the *difference transport* of an infinitesimal automorphism `αI` of the trivial
deformation of `x` over `A[I]`, where `I` is the kernel: glueing `x'` with itself over
`A' ×_A A'` and transporting across the canonical isomorphism `A' ×_A A' ≅ A' ×_A A[I]` of
`Deformation.Artin.squareZeroDifferenceEquiv`, there is an automorphism `θ` of the glueing
restricting to the identity along the first projection, to `α` along the second, and to
`αI` on the `A[I]`-factor.

Since `Deformation.Artin.kerDifference` is the second element minus the first, this is the
source's convention for the difference of `α` from the identity. -/
public def IsGeometricInfDifference
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      IsSiteModule A B (ModuleCat.of A (RingHom.ker q)))
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g)))
    (αI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      trivialDeformation A B S hS toS hA p x hx hp
          ⟨ModuleCat.of A (RingHom.ker q), hI⟩ ⟶
        trivialDeformation A B S hS toS hA p x hx hp
          ⟨ModuleCat.of A (RingHom.ker q), hI⟩)
    (α : x' ⟶ x') : Prop :=
  letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let M : SiteModule A B := ⟨ModuleCat.of A (RingHom.ker q), hI⟩
  letI : Module Aᵐᵒᵖ (RingHom.ker q) :=
    oppositeModule A (ModuleCat.of A (RingHom.ker q))
  letI : IsCentralScalar A (RingHom.ker q) :=
    centralScalar A (ModuleCat.of A (RingHom.ker q))
  let Q := q.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom)
  ∃ (hP : B.Contains (Spec (.of (q.pullback q))))
    (hQ : B.Contains (Spec (.of Q)))
    (toSP : B.obj hP ⟶ B.obj hS)
    (toSQ : B.obj hQ ⟶ B.obj hS)
    (r₁ r₂ : (Over.mk toS' : BigFppfOver B S hS) ⟶ Over.mk toSP)
    (s : squareZeroOver A B S hS toS M ⟶ Over.mk toSQ)
    (e : (Over.mk toSQ : BigFppfOver B S hS) ≅ Over.mk toSP)
    (er : (q.pullback q) ≃+* Q),
      B.inclusion.map r₁.left = Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ∧
      B.inclusion.map r₂.left = Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ∧
      B.inclusion.map s.left =
        Spec.map (CommRingCat.ofHom
          (q.pullbackSnd ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom))) ∧
      B.inclusion.map e.hom.left = Spec.map (CommRingCat.ofHom er.toRingHom) ∧
      (∀ y : q.pullback q,
        (er y).1.1 = y.1.1 ∧
        (er y).1.2 =
          ((q y.1.1, kerDifference q y) : TrivSqZeroExt A (RingHom.ker q))) ∧
      ∃ (v w : X) (φ₁ φ₂ : x'.1.right ⟶ v)
        (ψ : (trivialDeformation A B S hS toS hA p x hx hp M).1.right ⟶ w)
        (ε : w ⟶ v) (θ : v ⟶ v),
        p.IsStronglyCartesian r₂ φ₁ ∧ p.IsStronglyCartesian r₁ φ₂ ∧
        p.IsStronglyCartesian s ψ ∧ p.IsStronglyCartesian e.hom ε ∧
        x'.1.hom ≫ φ₁ = x'.1.hom ≫ φ₂ ∧
        (trivialDeformation A B S hS toS hA p x hx hp M).1.hom ≫ ψ ≫ ε =
          x'.1.hom ≫ φ₁ ∧
        p.IsHomLift (𝟙 (Over.mk toSP : BigFppfOver B S hS)) θ ∧
        φ₂ ≫ θ = φ₂ ∧
        α.1.right ≫ φ₁ = φ₁ ≫ θ ∧
        αI.1.right ≫ ψ ≫ ε = ψ ≫ ε ≫ θ

include hp in
/-- Restriction of infinitesimal automorphisms along an arrow of lifts which has an inverse
up to the two identities is a bijection. -/
private theorem end_restrict_bijective {U V : Under (p.obj x)}
    {a : (Under.post p).Fiber U} {b : (Under.post p).Fiber V}
    {u : V ⟶ U} {u' : U ⟶ V} (κ : b.1 ⟶ a.1)
    (hκ : (Under.post p).IsHomLift u κ) (κ' : a.1 ⟶ b.1)
    (hκ' : (Under.post p).IsHomLift u' κ')
    (h1 : κ' ≫ κ = 𝟙 a.1) (h2 : κ ≫ κ' = 𝟙 b.1) :
    Function.Bijective (fun θ : a ⟶ a =>
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) κ hκ θ) := by
  have hq := underPost_isFiberedInGroupoids p hp x
  have key : ∀ {U V : Under (p.obj x)} {a : (Under.post p).Fiber U} {b : (Under.post p).Fiber V}
      {u : V ⟶ U} {u' : U ⟶ V} (κ : b.1 ⟶ a.1) (hκ : (Under.post p).IsHomLift u κ)
      (κ' : a.1 ⟶ b.1) (hκ' : (Under.post p).IsHomLift u' κ') (h : κ' ≫ κ = 𝟙 a.1)
      (θ : a ⟶ a),
      fiberEndRestrict (Under.post p) hq κ' hκ' (fiberEndRestrict (Under.post p) hq κ hκ θ) =
        θ := by
    intro U V a b u u' κ hκ κ' hκ' h θ
    have hc : (Under.post p).IsHomLift (u' ≫ u) (κ' ≫ κ) := inferInstance
    rw [← fiberEndRestrict_comp (Under.post p) hq κ hκ κ' hκ' hc,
      fiberEndRestrict_congr (Under.post p) hq (κ' ≫ κ) (𝟙 a.1) hc (IsHomLift.id a.2) h,
      fiberEndRestrict_id (Under.post p) hq θ]
  exact ⟨Function.LeftInverse.injective (key κ hκ κ' hκ' h1),
    Function.RightInverse.surjective (key κ' hκ' κ hκ h2)⟩

include hp in
/-- **(RS*) for a fibre product of deformation situations.** The comparison functor of the
square presenting `P` as the fibre product of `D` and `E` over `A` is an equivalence. -/
private theorem fiberSquareComparison_isEquivalence (hRS : SatisfiesRSStar B S hS p hp)
    (D E P : AffineDeformation A B S hS toS hA)
    (i : AffineDeformation.Hom P D) (j : AffineDeformation.Hom P E)
    (hpb : IsPullback ((BigFppfOver.toScheme B S hS).map i.right).appTop
      ((BigFppfOver.toScheme B S hS).map j.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop)
    (hsurj : Function.Surjective E.aug) (hsq : RingHom.ker E.aug ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    (fiberSquareComparison p (Functor.chosenPullbacks p) D.arrow E.arrow i.right j.right
      ((Under.w i).trans (Under.w j).symm)).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  have hf : (BigFppfOver.toScheme B S hS).map D.arrow =
      Spec.map (CommRingCat.ofHom D.aug) := D.arrow_eq
  have hg : (BigFppfOver.toScheme B S hS).map E.arrow =
      Spec.map (CommRingCat.ofHom E.aug) := E.arrow_eq
  exact hRS ⟨algebraOver A B S hS toS hA, show IsAffine (Spec (.of A)) from inferInstance⟩
    ⟨D.siteOver, show IsAffine (Spec D.ring) from inferInstance⟩
    ⟨E.siteOver, show IsAffine (Spec E.ring) from inferInstance⟩
    ⟨P.siteOver, show IsAffine (Spec P.ring) from inferInstance⟩
    (ObjectProperty.homMk D.arrow) (ObjectProperty.homMk E.arrow)
    (ObjectProperty.homMk i.right) (ObjectProperty.homMk j.right)
    (ObjectProperty.hom_ext _ ((Under.w i).trans (Under.w j).symm))
    (by
      show IsPullback ((BigFppfOver.toScheme B S hS).map i.right).appTop
        ((BigFppfOver.toScheme B S hS).map j.right).appTop
        ((BigFppfOver.toScheme B S hS).map D.arrow).appTop
        ((BigFppfOver.toScheme B S hS).map E.arrow).appTop
      rw [hf, hg]
      exact hpb)
    (by
      show Function.Surjective
        (((BigFppfOver.toScheme B S hS).map E.arrow).appTop.hom)
      rw [hg]
      exact specMap_appTop_surjective _ hsurj)
    (by
      show RingHom.ker (((BigFppfOver.toScheme B S hS).map E.arrow).appTop.hom) ^ 2 = ⊥
      rw [hg]
      exact specMap_appTop_ker_sq _ hsq)

include hp in
/-- **(RS*) for infinitesimal automorphisms.** Restriction along two cartesian arrows to
lifts over `D` and over `E` is a bijection from the infinitesimal automorphisms of a lift
over the fibre product `P` onto pairs of infinitesimal automorphisms. -/
private theorem end_pair_bijective (hRS : SatisfiesRSStar B S hS p hp)
    (D E P : AffineDeformation A B S hS toS hA)
    (i : AffineDeformation.Hom P D) (j : AffineDeformation.Hom P E)
    (hpb : IsPullback ((BigFppfOver.toScheme B S hS).map i.right).appTop
      ((BigFppfOver.toScheme B S hS).map j.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop)
    (hsurj : Function.Surjective E.aug) (hsq : RingHom.ker E.aug ^ 2 = ⊥)
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ P.arrow)))
    {b₁ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))}
    {b₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.arrow))}
    (φ₁ : b₁.1 ⟶ a.1) (hφ₁ : (Under.post p).IsHomLift (AffineDeformation.underMap p x hx i) φ₁)
    (φ₂ : b₂.1 ⟶ a.1)
    (hφ₂ : (Under.post p).IsHomLift (AffineDeformation.underMap p x hx j) φ₂) :
    Function.Bijective (fun θ : a ⟶ a =>
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) φ₁ hφ₁ θ,
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) φ₂ hφ₂ θ)) := by
  let : p.IsFibered := hp.isFibered
  obtain ⟨t, ht⟩ :=
    isoFiberToUnder_surjective p hp (Functor.chosenPullbacks p) P.arrow ⟨x, hx⟩ a
  have hbij := fiberEndRestrict_underRestrictArrow_bijective p hp (Functor.chosenPullbacks p)
    D.arrow ⟨x, hx⟩ E.arrow i.right j.right ((Under.w i).trans (Under.w j).symm)
    P.arrow (Under.w i)
    (fiberSquareComparison_isEquivalence A B S hS toS hA p hp hRS D E P i j hpb hsurj hsq)
    t
  exact fiberEndRestrict_pair_bijective_of_iso (Under.post p)
    (underPost_isFiberedInGroupoids p hp x) _ _ _ _ φ₁ hφ₁ φ₂ hφ₂ (eqToIso ht) hbij

/-- An arrow of lifts whose underlying arrow lies over the underlying arrow of a morphism
of base thickenings lies over that morphism. -/
private theorem underPost_isHomLift_of_right {U V : Under (p.obj x)}
    {s : (Under.post p).Fiber U} {t : (Under.post p).Fiber V} (g : U ⟶ V)
    (m : s.1 ⟶ t.1) (hm : p.IsHomLift g.right m.right) :
    (Under.post p).IsHomLift g m := by
  refine IsHomLift.of_fac' (Under.post p) _ _ s.2 t.2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Under.homMk_right]
  rw [IsHomLift.fac' p g.right m.right]

/-- The structure arrow of a lift lies over the arrow of its deformation situation. -/
private theorem lift_hom_isHomLift (D : AffineDeformation A B S hS toS hA)
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) :
    p.IsHomLift D.arrow a.1.hom := by
  have hy : p.obj a.1.right = D.siteOver := congrArg Under.right a.2
  apply IsHomLift.of_fac p D.arrow a.1.hom hx hy
  have hw := Under.w (eqToHom a.2)
  simp only [Under.eqToHom_right] at hw
  change p.map a.1.hom ≫ eqToHom hy = eqToHom hx ≫ D.arrow at hw
  rw [hw]
  simp

/-- The trivial thickening of `Spec A`, mapping to the base of a deformation situation. -/
private def liftBaseDeformation (D : AffineDeformation A B S hS toS hA) :
    liftBaseId A B S hS toS hA p x hx ⟶ Under.mk (eqToHom hx ≫ D.arrow) :=
  Under.homMk D.arrow rfl

/-- The structure arrow of a lift, as an arrow of lifts out of `x` itself. -/
private def liftIdArrow (D : AffineDeformation A B S hS toS hA)
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) :
    (liftId A B S hS toS hA p x hx).1 ⟶ a.1 :=
  Under.homMk a.1.hom (Category.id_comp _)

private theorem liftIdArrow_isHomLift (D : AffineDeformation A B S hS toS hA)
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) :
    (Under.post p).IsHomLift (liftBaseDeformation A B S hS toS hA p x hx D)
      (liftIdArrow A B S hS toS hA p x hx D a) :=
  underPost_isHomLift_of_right B S hS p x _ _
    (lift_hom_isHomLift A B S hS toS hA p x hx D a)

/-- The structural arrow of the trivial square-zero extension of a deformation situation
factors the restriction of a lift through `x` itself. -/
private theorem underMap_baseMap (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : RingHom.ker R.aug ^ 2 = ⊥) :
    AffineDeformation.underMap p x hx
        (BasedRing.baseMap R
          (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq))).toHom =
      liftBaseSection A B S hS toS hA p x hx (BasedRing.kernelSite R hq hsq) ≫
        liftBaseDeformation A B S hS toS hA p x hx R := by
  apply Under.UnderMorphism.ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom
      ((TrivSqZeroExt.inlHom A (BasedRing.kernelSite R hq hsq).obj).comp R.aug)) =
    Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom A (BasedRing.kernelSite R hq hsq).obj)) ≫
      B.inclusion.map R.arrow.left
  rw [R.arrow_eq, ← Spec.map_comp]
  rfl

include hp in
/-- **The difference comparison, in abstract form.** Suppose `PP` presents the self-fibre
product of a deformation situation `D` over `A` by two projections `i₁`, `i₂`, that `QQ`
presents the fibre product of `D` with a second situation `E`, that `dg` is a diagonal for
`PP` and that `dm : PP ⟶ QQ` is an isomorphism compatible with the first projections. Let
`x'` be a lift over `D`, let `t` be a lift over `E`, and let `ℓ : t ⟶ x'` lie over the
composite `dg` after `dm` after the second projection of `QQ`.

Then the infinitesimal automorphisms of `x'` and of `t` correspond multiplicatively: an
automorphism of the glueing of `x'` with itself along `dg` which is the identity on the
first factor is matched with its difference on the `E`-factor. -/
private theorem exists_differenceMulEquiv (hRS : SatisfiesRSStar B S hS p hp)
    {R : AffineDeformation A B S hS toS hA} (D E PP QQ : BasedRing A B S hS toS hA R)
    (i₁ i₂ : BasedRing.RingMap PP D) (j₁ : BasedRing.RingMap QQ D)
    (j₂ : BasedRing.RingMap QQ E)
    (hpbP : IsPullback ((BigFppfOver.toScheme B S hS).map i₁.toHom.right).appTop
      ((BigFppfOver.toScheme B S hS).map i₂.toHom.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop)
    (hpbQ : IsPullback ((BigFppfOver.toScheme B S hS).map j₁.toHom.right).appTop
      ((BigFppfOver.toScheme B S hS).map j₂.toHom.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop)
    (dg : BasedRing.RingMap D PP)
    (hdg₁ : i₁.comp dg = BasedRing.RingMap.id R D)
    (hdg₂ : i₂.comp dg = BasedRing.RingMap.id R D)
    (dm : BasedRing.RingMap PP QQ) (eiso : PP.ring ≃+* QQ.ring)
    (heiso : dm.hom = eiso.toRingHom) (hdm : j₁.comp dm = i₁)
    (hsurjD : Function.Surjective D.aug) (hsqD : RingHom.ker D.aug ^ 2 = ⊥)
    (hsurjE : Function.Surjective E.aug) (hsqE : RingHom.ker E.aug ^ 2 = ⊥)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.toAffine.arrow)))
    (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.toAffine.arrow)))
    (ℓ : t.1 ⟶ x'.1)
    (hℓ : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx ((j₂.comp dm).comp dg).toHom) ℓ) :
    ∃ Ψ : (x' ⟶ x') ≃ (t ⟶ t),
      (∀ α β : x' ⟶ x', Ψ (α ≫ β) = Ψ α ≫ Ψ β) ∧
      ∃ (v : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ PP.toAffine.arrow)))
        (w : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ QQ.toAffine.arrow)))
        (φ₁ φ₂ : x'.1 ⟶ v.1) (ψ : t.1 ⟶ w.1) (ε : w.1 ⟶ v.1)
        (_hφ₁ : (Under.post p).IsHomLift
          (AffineDeformation.underMap p x hx i₁.toHom) φ₁)
        (_hφ₂ : (Under.post p).IsHomLift
          (AffineDeformation.underMap p x hx i₂.toHom) φ₂)
        (_hψ : (Under.post p).IsHomLift
          (AffineDeformation.underMap p x hx j₂.toHom) ψ)
        (_hε : (Under.post p).IsHomLift
          (AffineDeformation.underMap p x hx dm.toHom) ε),
        ∀ α : x' ⟶ x', ∃ θ : v ⟶ v,
          φ₁ ≫ Functor.Fiber.fiberInclusion.map θ = φ₁ ∧
          Functor.Fiber.fiberInclusion.map α ≫ φ₂ =
            φ₂ ≫ Functor.Fiber.fiberInclusion.map θ ∧
          Functor.Fiber.fiberInclusion.map (Ψ α) ≫ ψ ≫ ε =
            (ψ ≫ ε) ≫ Functor.Fiber.fiberInclusion.map θ := by
  let : p.IsFibered := hp.isFibered
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  have hqg := underPost_isFiberedInGroupoids p hp x
  have hcomp : ∀ {D' E' F' : BasedRing A B S hS toS hA R} (f : BasedRing.RingMap D' E')
      (g : BasedRing.RingMap E' F'),
      AffineDeformation.underMap p x hx g.toHom ≫ AffineDeformation.underMap p x hx f.toHom =
        AffineDeformation.underMap p x hx (g.comp f).toHom := by
    intro D' E' F' f g
    rw [BasedRing.RingMap.toHom_comp, AffineDeformation.underMap_comp]
  have hinv : ∀ {D' E' : BasedRing A B S hS toS hA R} (f : BasedRing.RingMap D' E')
      (g : BasedRing.RingMap E' D'), g.comp f = BasedRing.RingMap.id R D' →
      𝟙 _ = AffineDeformation.underMap p x hx g.toHom ≫
        AffineDeformation.underMap p x hx f.toHom := by
    intro D' E' f g h
    rw [hcomp, h, BasedRing.RingMap.toHom_id, AffineDeformation.underMap_id]
  let c' := underPostPullbacks p x hp
  -- the glueing of `x'` with itself along the diagonal
  let v := c'.obj (AffineDeformation.underMap p x hx dg.toHom) x'
  let κ := c'.map (AffineDeformation.underMap p x hx dg.toHom) x'
  have : (Under.post p).IsStronglyCartesian
      (AffineDeformation.underMap p x hx dg.toHom) κ := c'.isStronglyCartesian _ _
  have : (Under.post p).IsHomLift
      (𝟙 (Under.mk (eqToHom hx ≫ D.toAffine.arrow))) (𝟙 x'.1) := IsHomLift.id x'.2
  have h₁ := hinv _ _ hdg₁
  have h₂ := hinv _ _ hdg₂
  let φ₁ := Functor.IsStronglyCartesian.map (Under.post p) _ κ h₁ (𝟙 x'.1)
  let φ₂ := Functor.IsStronglyCartesian.map (Under.post p) _ κ h₂ (𝟙 x'.1)
  have hφ₁ : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx i₁.toHom) φ₁ := inferInstance
  have hφ₂ : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx i₂.toHom) φ₂ := inferInstance
  -- the lift over `E`, mapping to the glueing
  have := hℓ
  have h₃ : AffineDeformation.underMap p x hx ((j₂.comp dm).comp dg).toHom =
      AffineDeformation.underMap p x hx (j₂.comp dm).toHom ≫
        AffineDeformation.underMap p x hx dg.toHom := (hcomp dg (j₂.comp dm)).symm
  let φE := Functor.IsStronglyCartesian.map (Under.post p) _ κ h₃ ℓ
  have hφEfac : φE ≫ κ = ℓ := Functor.IsStronglyCartesian.fac (Under.post p) _ κ h₃ ℓ
  -- transport across the isomorphism `dm`
  let vQ := c'.obj (AffineDeformation.underMap p x hx dm.toHom) v
  let lam := c'.map (AffineDeformation.underMap p x hx dm.toHom) v
  have : (Under.post p).IsStronglyCartesian
      (AffineDeformation.underMap p x hx dm.toHom) lam := c'.isStronglyCartesian _ _
  have hlam : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx dm.toHom) lam := inferInstance
  have h₄ : AffineDeformation.underMap p x hx i₁.toHom =
      AffineDeformation.underMap p x hx j₁.toHom ≫
        AffineDeformation.underMap p x hx dm.toHom := by
    rw [hcomp, hdm]
  have h₅ : AffineDeformation.underMap p x hx (j₂.comp dm).toHom =
      AffineDeformation.underMap p x hx j₂.toHom ≫
        AffineDeformation.underMap p x hx dm.toHom := (hcomp dm j₂).symm
  let ψ₁ := Functor.IsStronglyCartesian.map (Under.post p) _ lam h₄ φ₁
  let ψ₂ := Functor.IsStronglyCartesian.map (Under.post p) _ lam h₅ φE
  have hψ₁ : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx j₁.toHom) ψ₁ := inferInstance
  have hψ₂ : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx j₂.toHom) ψ₂ := inferInstance
  have hψ₁fac : ψ₁ ≫ lam = φ₁ := Functor.IsStronglyCartesian.fac (Under.post p) _ lam h₄ φ₁
  -- the inverse of the transport
  have : (Under.post p).IsHomLift
      (𝟙 (Under.mk (eqToHom hx ≫ PP.toAffine.arrow))) (𝟙 v.1) := IsHomLift.id v.2
  have : (Under.post p).IsHomLift
      (𝟙 (Under.mk (eqToHom hx ≫ QQ.toAffine.arrow))) (𝟙 vQ.1) := IsHomLift.id vQ.2
  have hinvc := BasedRing.RingMap.inverse_comp R dm eiso heiso
  have hcinv := BasedRing.RingMap.comp_inverse R dm eiso heiso
  have h₆ := hinv _ _ hinvc
  let lam' := Functor.IsStronglyCartesian.map (Under.post p) _ lam h₆ (𝟙 v.1)
  have hlam' : (Under.post p).IsHomLift
      (AffineDeformation.underMap p x hx (dm.inverse R eiso heiso).toHom) lam' :=
    inferInstance
  have hlam'fac : lam' ≫ lam = 𝟙 v.1 :=
    Functor.IsStronglyCartesian.fac (Under.post p) _ lam h₆ (𝟙 v.1)
  have hu := (hinv _ _ hcinv).symm
  have hlamfac' : lam ≫ lam' = 𝟙 vQ.1 := by
    have : (Under.post p).IsHomLift
        (𝟙 (Under.mk (eqToHom hx ≫ QQ.toAffine.arrow))) (lam ≫ lam') :=
      isHomLift_congr (Under.post p) hu (lam ≫ lam') inferInstance
    have hfid : AffineDeformation.underMap p x hx dm.toHom =
      𝟙 _ ≫ AffineDeformation.underMap p x hx dm.toHom := (Category.id_comp _).symm
    have e1 := Functor.IsStronglyCartesian.map_uniq (Under.post p) _ lam hfid lam
      (lam ≫ lam') (by rw [Category.assoc, hlam'fac, Category.comp_id])
    have e2 := Functor.IsStronglyCartesian.map_uniq (Under.post p) _ lam hfid lam
      (𝟙 vQ.1) (Category.id_comp _)
    exact e1.trans e2.symm
  -- the two (RS*) decompositions and the transport bijection
  have hbijP := end_pair_bijective A B S hS toS hA p x hx hp hRS D.toAffine D.toAffine
    PP.toAffine i₁.toHom i₂.toHom hpbP hsurjD hsqD v φ₁ hφ₁ φ₂ hφ₂
  have hbijQ := end_pair_bijective A B S hS toS hA p x hx hp hRS D.toAffine E.toAffine
    QQ.toAffine j₁.toHom j₂.toHom hpbQ hsurjE hsqE vQ ψ₁ hψ₁ ψ₂ hψ₂
  have hbijTr := end_restrict_bijective B S hS p x hp lam hlam lam' hlam' hlam'fac hlamfac'
  let eP := Equiv.ofBijective _ hbijP
  let fQ := (Equiv.ofBijective _ hbijTr).trans (Equiv.ofBijective _ hbijQ)
  have hfst : ∀ θ : v ⟶ v, (eP θ).1 = (fQ θ).1 := by
    intro θ
    show fiberEndRestrict (Under.post p) hqg φ₁ hφ₁ θ =
      fiberEndRestrict (Under.post p) hqg ψ₁ hψ₁
        (fiberEndRestrict (Under.post p) hqg lam hlam θ)
    rw [← fiberEndRestrict_comp (Under.post p) hqg lam hlam ψ₁ hψ₁ inferInstance]
    exact fiberEndRestrict_congr (Under.post p) hqg φ₁ (ψ₁ ≫ lam) hφ₁ inferInstance
      hψ₁fac.symm θ
  have hePmul : ∀ θ θ' : v ⟶ v,
      eP (θ ≫ θ') = ((eP θ).1 ≫ (eP θ').1, (eP θ).2 ≫ (eP θ').2) :=
    fun θ θ' => Prod.ext (fiberEndRestrict_map_comp (Under.post p) hqg φ₁ hφ₁ θ θ')
      (fiberEndRestrict_map_comp (Under.post p) hqg φ₂ hφ₂ θ θ')
  have hfQmul : ∀ θ θ' : v ⟶ v,
      fQ (θ ≫ θ') = ((fQ θ).1 ≫ (fQ θ').1, (fQ θ).2 ≫ (fQ θ').2) := by
    intro θ θ'
    show (fiberEndRestrict (Under.post p) hqg ψ₁ hψ₁
        (fiberEndRestrict (Under.post p) hqg lam hlam (θ ≫ θ')),
      fiberEndRestrict (Under.post p) hqg ψ₂ hψ₂
        (fiberEndRestrict (Under.post p) hqg lam hlam (θ ≫ θ'))) = _
    rw [fiberEndRestrict_map_comp (Under.post p) hqg lam hlam θ θ']
    exact Prod.ext (fiberEndRestrict_map_comp (Under.post p) hqg ψ₁ hψ₁ _ _)
      (fiberEndRestrict_map_comp (Under.post p) hqg ψ₂ hψ₂ _ _)
  refine ⟨equivFromPairCoordinates eP fQ hfst (𝟙 x'), ?_,
    v, vQ, φ₁, φ₂, ψ₂, lam, hφ₁, hφ₂, hψ₂, hlam, ?_⟩
  · intro α β
    show (fQ (eP.symm (𝟙 x', α ≫ β))).2 =
      (fQ (eP.symm (𝟙 x', α))).2 ≫ (fQ (eP.symm (𝟙 x', β))).2
    have hsym : eP.symm (𝟙 x', α ≫ β) = eP.symm (𝟙 x', α) ≫ eP.symm (𝟙 x', β) := by
      apply eP.injective
      rw [Equiv.apply_symm_apply, hePmul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Prod.ext (Category.id_comp _).symm rfl
    rw [hsym, hfQmul]
  · intro α
    refine ⟨eP.symm (𝟙 x', α), ?_, ?_, ?_⟩
    · have h1 : fiberEndRestrict (Under.post p) hqg φ₁ hφ₁ (eP.symm (𝟙 x', α)) = 𝟙 x' := by
        show (eP (eP.symm (𝟙 x', α))).1 = 𝟙 x'
        rw [eP.apply_symm_apply]
      have hf := fiberEndRestrict_fac (Under.post p) hqg φ₁ hφ₁ (eP.symm (𝟙 x', α))
      rw [h1, CategoryTheory.Functor.map_id, Category.id_comp] at hf
      exact hf.symm
    · have h2 : fiberEndRestrict (Under.post p) hqg φ₂ hφ₂ (eP.symm (𝟙 x', α)) = α := by
        show (eP (eP.symm (𝟙 x', α))).2 = α
        rw [eP.apply_symm_apply]
      have hf := fiberEndRestrict_fac (Under.post p) hqg φ₂ hφ₂ (eP.symm (𝟙 x', α))
      rw [h2] at hf
      exact hf
    · have hψε : (Under.post p).IsHomLift
          (AffineDeformation.underMap p x hx j₂.toHom ≫
            AffineDeformation.underMap p x hx dm.toHom) (ψ₂ ≫ lam) := inferInstance
      have h3 : fiberEndRestrict (Under.post p) hqg (ψ₂ ≫ lam) hψε (eP.symm (𝟙 x', α)) =
          (fQ (eP.symm (𝟙 x', α))).2 := by
        rw [fiberEndRestrict_comp (Under.post p) hqg lam hlam ψ₂ hψ₂ hψε]
        rfl
      have hf := fiberEndRestrict_fac (Under.post p) hqg (ψ₂ ≫ lam) hψε
        (eP.symm (𝟙 x', α))
      rw [h3] at hf
      exact hf

include hp in
/-- The difference comparison at a deformation situation presented by an affine
deformation: the infinitesimal automorphisms of a lift `x'` over `Spec A'` correspond
multiplicatively to those of the trivial deformation of `x` over `A[I]`, where `I` is the
kernel of `A' → A`, and the correspondence is the geometric difference transport. -/
private theorem exists_infDifferenceEquiv (hRS : SatisfiesRSStar B S hS p hp)
    (R : AffineDeformation A B S hS toS hA) (hq : Function.Surjective R.aug)
    (hsq : RingHom.ker R.aug ^ 2 = ⊥)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ R.arrow))) :
    ∃ Ψ : (x' ⟶ x') ≃
        (trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq) ⟶
          trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq)),
      (∀ α β : x' ⟶ x', Ψ (α ≫ β) = Ψ α ≫ Ψ β) ∧
      letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      ∀ α : x' ⟶ x', IsGeometricInfDifference A B S hS toS hA p x hx hp R.ring
        R.contains R.structureMap R.aug hq hsq R.arrow
        (isSiteModule_kernel A B R.contains R.aug hq) x' (Ψ α) α := by
  let : p.IsFibered := hp.isFibered
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  have hwSurj : Function.Surjective
      (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq)).aug :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hwSq : RingHom.ker
      (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq)).aug ^ 2 = ⊥ :=
    squareZeroProjection_ker_sq A (BasedRing.kernelSite R hq hsq).obj
  have : (Under.post p).IsHomLift
      (liftBaseSection A B S hS toS hA p x hx (BasedRing.kernelSite R hq hsq))
      (trivialDeformationMap A B S hS toS hA p x hx hp
        (BasedRing.kernelSite R hq hsq)) :=
    (trivialDeformationMap_isCartesian A B S hS toS hA p x hx hp
      (BasedRing.kernelSite R hq hsq)).toIsHomLift
  have := liftIdArrow_isHomLift A B S hS toS hA p x hx R x'
  have hcomposite : (Under.post p).IsHomLift
      (liftBaseSection A B S hS toS hA p x hx (BasedRing.kernelSite R hq hsq) ≫
        liftBaseDeformation A B S hS toS hA p x hx R)
      (trivialDeformationMap A B S hS toS hA p x hx hp
          (BasedRing.kernelSite R hq hsq) ≫
        liftIdArrow A B S hS toS hA p x hx R x') := inferInstance
  obtain ⟨Ψ, hΨmul, v, w, φ₁, φ₂, ψ, ε, hφ₁, hφ₂, hψ, hε, hwit⟩ :=
    exists_differenceMulEquiv A B S hS toS hA p x hx hp hRS
      (BasedRing.original R) (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq))
      (BasedRing.prod (BasedRing.original R) (BasedRing.original R))
      (BasedRing.prod (BasedRing.original R)
        (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq)))
      (BasedRing.fst _ _) (BasedRing.snd _ _) (BasedRing.fst _ _) (BasedRing.snd _ _)
      (BasedRing.prod_isPullbackSquare _ _) (BasedRing.prod_isPullbackSquare _ _)
      (BasedRing.diag R) (BasedRing.fst_comp_diag R) (BasedRing.snd_comp_diag R)
      (BasedRing.differenceMap R hq hsq) (BasedRing.differenceEquiv R hq hsq) rfl
      (BasedRing.differenceMap_fst R hq hsq) hq hsq hwSurj hwSq x'
      (trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq))
      (trivialDeformationMap A B S hS toS hA p x hx hp
          (BasedRing.kernelSite R hq hsq) ≫
        liftIdArrow A B S hS toS hA p x hx R x')
      (isHomLift_congr (Under.post p)
        ((underMap_baseMap A B S hS toS hA p x hx R hq hsq).symm.trans
          (congrArg (fun k : BasedRing.RingMap (BasedRing.original R)
              (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq)) =>
            AffineDeformation.underMap p x hx k.toHom)
            (BasedRing.delta_comp_diag R hq hsq).symm)) _ hcomposite)
  have := hφ₁
  have := hφ₂
  have := hψ
  have := hε
  refine ⟨Ψ, hΨmul, ?_⟩
  intro α
  obtain ⟨θ, hw₁, hw₂, hw₃⟩ := hwit α
  have hcart : ∀ {U V : Under (p.obj x)} {a : (Under.post p).Fiber U}
      {b : (Under.post p).Fiber V} (f : U ⟶ V) (φ : a.1 ⟶ b.1),
      (Under.post p).IsHomLift f φ → p.IsStronglyCartesian f.right φ.right := by
    intro U V a b f φ h
    have := underPost_isHomLift_right p f φ h
    exact hp.isStronglyCartesian_homLift _ _
  refine ⟨(BasedRing.prod (BasedRing.original R) (BasedRing.original R)).contains,
    (BasedRing.prod (BasedRing.original R)
      (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq))).contains,
    (BasedRing.prod (BasedRing.original R) (BasedRing.original R)).structureMap,
    (BasedRing.prod (BasedRing.original R)
      (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq))).structureMap,
    (BasedRing.fst (BasedRing.original R) (BasedRing.original R)).toHom.right,
    (BasedRing.snd (BasedRing.original R) (BasedRing.original R)).toHom.right,
    (BasedRing.snd (BasedRing.original R)
      (BasedRing.squareZero R (BasedRing.kernelSite R hq hsq))).toHom.right,
    BasedRing.overIso R (BasedRing.differenceMap R hq hsq)
      (BasedRing.differenceEquiv R hq hsq) rfl,
    BasedRing.differenceEquiv R hq hsq, rfl, rfl, rfl, rfl,
    (squareZeroDifferenceEquiv R.aug hq hsq).property,
    v.1.right, w.1.right, φ₂.right, φ₁.right, ψ.right, ε.right, θ.1.right,
    hcart _ _ hφ₂, hcart _ _ hφ₁, hcart _ _ hψ, hcart _ _ hε,
    (Under.w φ₂).trans (Under.w φ₁).symm, ?_,
    underPost_isHomLift_right p (𝟙 _) θ.1 θ.2, ?_, ?_, ?_⟩
  · exact (Under.w (ψ ≫ ε)).trans (Under.w φ₂).symm
  · exact congrArg Under.Hom.right hw₁
  · exact congrArg Under.Hom.right hw₂
  · exact (congrArg Under.Hom.right hw₃).trans (Category.assoc _ _ _)

include hp in
/-- An endomorphism of a lift in the fibre of lifts is an isomorphism: the lifts of `x`
form a category fibred in groupoids. -/
private theorem isIso_liftEnd {U : Under (p.obj x)}
    {a : (Under.post p).Fiber U} (θ : a ⟶ a) : IsIso θ :=
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber U) :=
    (underPost_isFiberedInGroupoids p hp x).fiber_isGroupoid U
  CategoryTheory.IsGroupoid.all_isIso θ

include hp in
/-- A multiplicative bijection of infinitesimal automorphisms carries the identity to the
identity: the image of the identity is idempotent, and every such endomorphism is an
isomorphism. -/
private theorem map_id_of_mul {U V : Under (p.obj x)} {a : (Under.post p).Fiber U}
    {b : (Under.post p).Fiber V} (Ψ : (a ⟶ a) → (b ⟶ b))
    (hΨ : ∀ α β : a ⟶ a, Ψ (α ≫ β) = Ψ α ≫ Ψ β) : Ψ (𝟙 a) = 𝟙 b := by
  have := isIso_liftEnd B S hS p x hp (Ψ (𝟙 a))
  refine ((cancel_epi (Ψ (𝟙 a))).1 ?_).symm
  rw [Category.comp_id, ← hΨ, Category.comp_id]

/-- **Stacks 07Y9 part (1), the comparison at a deformation situation.** For a deformation
situation `(x, A' → A)` with square-zero kernel `I` and a chosen lift `x'` of `x` over
`Spec A'`, the value `Inf_x(I)` of the `A`-linear functor of infinitesimal automorphisms is
the group `Inf(x'/x)` of infinitesimal automorphisms of `x'`. -/
public structure InfComparisonData
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))) where
  /-- The kernel of the deformation situation is a module of the chosen site, so the
  infinitesimal automorphisms of the trivial deformation at it are defined. -/
  kernelIsSiteModule : letI := Stacks.Smooth.kerModule hq hsq
    IsSiteModule A B (ModuleCat.of A (RingHom.ker q))
  /-- The comparison `Inf_x(I) → Inf(x'/x)`. -/
  equiv : letI := Stacks.Smooth.kerModule hq hsq
    (Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type w) ≃
      (x' ⟶ x')
  /-- The comparison carries zero to the identity automorphism. -/
  equiv_zero : letI := Stacks.Smooth.kerModule hq hsq
    equiv 0 = 𝟙 x'
  /-- The comparison carries addition to composition: it is an isomorphism of groups. -/
  equiv_add : letI := Stacks.Smooth.kerModule hq hsq
    ∀ a b, equiv (a + b) = equiv a ≫ equiv b
  /-- The comparison is the geometric difference transport: the automorphism of `x'`
  attached to `a` is the difference, across `A' ×_A A' ≅ A' ×_A A[I]`, of the automorphism
  of the trivial deformation over `A[I]` attached to the same `a`. -/
  equiv_geometric : letI := Stacks.Smooth.kerModule hq hsq
    ∀ a, IsGeometricInfDifference A B S hS toS hA p x hx hp A' hA' toS' q hq hsq g
      kernelIsSiteModule x'
      (Inf.autEquiv ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ a) (equiv a)

include hp in
/-- The comparison of Stacks 07Y9 part (1) exists at every deformation situation with a
lift. -/
private theorem nonempty_infComparisonData (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))) :
    Nonempty (InfComparisonData A B S hS toS hA p x hx hp Inf A' hA' toS' q hq hsq g x') := by
  classical
  let R : AffineDeformation A B S hS toS hA := ⟨.of A', hA', toS', q, g, hg⟩
  obtain ⟨Ψ, hΨ, hgeo⟩ := exists_infDifferenceEquiv A B S hS toS hA p x hx hp hRS R hq hsq x'
  have hΨid : Ψ (𝟙 x') = 𝟙 _ := map_id_of_mul B S hS p x hp Ψ hΨ
  have hΨsymm : ∀ u v, Ψ.symm (u ≫ v) = Ψ.symm u ≫ Ψ.symm v := by
    intro u v
    apply Ψ.injective
    rw [Equiv.apply_symm_apply, hΨ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨{ kernelIsSiteModule :=
              let := Stacks.Smooth.kerModule hq hsq
              isSiteModule_kernel A B hA' q hq
            equiv := (Inf.autEquiv (BasedRing.kernelSite R hq hsq)).trans Ψ.symm
            equiv_zero := ?_
            equiv_add := ?_
            equiv_geometric := ?_ }⟩
  · exact (congrArg Ψ.symm (autEquiv_zero A B S hS toS hA p x hx hp Inf
      (BasedRing.kernelSite R hq hsq))).trans (Ψ.symm_apply_eq.2 hΨid.symm)
  · intro a b
    exact (congrArg Ψ.symm (autEquiv_add A B S hS toS hA p x hx hp hRS Inf
      (BasedRing.kernelSite R hq hsq) a b)).trans (hΨsymm _ _)
  · intro a
    have h := hgeo (Ψ.symm (Inf.autEquiv (BasedRing.kernelSite R hq hsq) a))
    rw [Equiv.apply_symm_apply] at h
    exact h

include hp in
/-- **Stacks 07Y9 part (1).** For `𝒳` satisfying (RS*), a deformation situation `A' → A`
with square-zero kernel `I` whose source lies in the chosen site, and a lift `x'` of `x`
over `Spec A'`, the value of the `A`-linear functor `Inf_x` at `I` is isomorphic, as a
group, to the infinitesimal automorphisms of `x'`. -/
@[stacks 07Y9 "part (1), the comparison of Inf_x(I) with Inf(x'/x)"]
public noncomputable def exists_infComparison (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))) :
    InfComparisonData A B S hS toS hA p x hx hp Inf A' hA' toS' q hq hsq g x' :=
  Classical.choice (by
    exact nonempty_infComparisonData A B S hS toS hA p x hx hp hRS Inf A' hA'
      toS' q hq hsq g hg x')

end InfinitesimalComparison

end Deformations

end Deformation.Artin

end
