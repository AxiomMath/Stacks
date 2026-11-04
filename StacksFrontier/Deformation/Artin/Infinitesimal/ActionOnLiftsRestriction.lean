module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts
import all StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts

/-!
# The difference construction is canonical, and restricts along base change

This file continues `StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts`. There, for a
category `𝒳` fibred in groupoids over the big fppf site of `S` satisfying (RS*), an object `x`
over `Spec A` and a deformation situation `A' → A` with square-zero kernel `I`, the action of
`T_x(I)` on lift classes and the comparison `Inf_x(I) ≅ Inf(x'/x)` of Stacks 07Y9 are
constructed and pinned by the geometric difference construction. Here the pins are shown to
determine these data, which gives Stacks 07YB, and the pins are restricted along a morphism of
deformation situations, which is the input to the two squares of Stacks 07YA.

## Main results

* `Deformation.Artin.IsGeometricInfDifference.conj` — the geometric difference transport is
  natural for isomorphisms of lifts.
* `Deformation.Artin.InfComparisonData.actions_agree` — **Stacks 07YB**: for two lifts `x'`,
  `x''` the precomposition action of `Inf(x'/x)` and the postcomposition action of
  `Inf(x''/x)` on `Mor(x', x'')` are simply transitive and agree via the comparisons
  `Inf(x'/x) = Inf_x(I) = Inf(x''/x)` of Stacks 07Y9, giving a simply transitive action of
  `Inf_x(I)`.
* `Deformation.Artin.isGeometricDifference_unique`,
  `Deformation.Artin.ActionOnLiftsData.action_eq_of_isGeometricDifference`,
  `Deformation.Artin.InfComparisonData.equiv_eq_of_isGeometricInfDifference` — the geometric
  pins determine the difference, the action on lifts and the comparison of `Inf`.
* `Deformation.Artin.IsGeometricInfDifference.restrict`,
  `Deformation.Artin.IsGeometricDifference.restrict` — the two pins restrict along a morphism
  of deformation situations; with the uniqueness above this gives the two squares of
  Stacks 07YA (`StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSituationMorphism`).

## Implementation notes

For Stacks 07YB the comparisons are arbitrary `InfComparisonData`, so the agreement of the two
actions needs that the geometric pin determines the comparison. A witness of the pin has its
base data forced — the structure map of `Spec (A' ×_A A')` over `S` by the pushout property
of `Spec` of a fibre product along a surjection — and two glueings of a lift with itself are
isomorphic by (RS*); conjugation by that isomorphism is invisible because `Inf(x'/x)` and
`Inf_x(I)` are commutative, so by (RS*) the automorphism of the trivial deformation is
determined by that of the lift. Naturality of the pin for isomorphisms of lifts then gives the
agreement.

## References

* [Stacks Project, Tag 07YB](https://stacks.math.columbia.edu/tag/07YB)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
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

/-! ### Deformation situations in the site -/

section Deformations

variable (A : Type u) [CommRing A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-! ### Infinitesimal automorphisms across a deformation situation -/

section InfinitesimalComparison

variable (hp : p.IsFiberedInGroupoids)

/-! ### The comparison is canonical, and the two actions on morphisms of lifts agree -/

/-- An arrow out of `x` lying over the arrow of an affine deformation is a lift of `x` along
that arrow. -/
private def liftOfIsHomLift (D : AffineDeformation A B S hS toS hA) {y : X} (m : x ⟶ y)
    (hm : p.IsHomLift D.arrow m) : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow)) :=
  ⟨Under.mk m, by
    have := hm
    have hy : p.obj y = D.siteOver := IsHomLift.codomain_eq p D.arrow m
    refine StructuredArrow.obj_ext _ _ hy ?_
    change p.map m ≫ eqToHom hy = eqToHom hx ≫ D.arrow
    rw [IsHomLift.fac' p D.arrow m]
    simp⟩

/-- Restricting a conjugate by an isomorphism of targets: if `φ` and `φ'` are arrows over one
base arrow into `a` and `a'`, and `κ : a ≅ a'`, then restricting `κ θ κ⁻¹` along `φ` is
conjugate to restricting `θ` along `φ'`. -/
private theorem fiberEndRestrict_conj_iso {𝒞 : Type*} [Category 𝒞] {𝒴 : Type*} [Category 𝒴]
    (r : 𝒴 ⥤ 𝒞) (hr : r.IsFiberedInGroupoids) {U V : 𝒞} {u : V ⟶ U} {a a' : r.Fiber U}
    {b : r.Fiber V} (κ : a ≅ a') (φ : b.1 ⟶ a.1) (hφ : r.IsHomLift u φ)
    (φ' : b.1 ⟶ a'.1) (hφ' : r.IsHomLift u φ') (θ : a' ⟶ a') :
    ∃ e : b ≅ b, fiberEndRestrict r hr φ hφ (κ.hom ≫ θ ≫ κ.inv) =
      e.hom ≫ fiberEndRestrict r hr φ' hφ' θ ≫ e.inv := by
  have hc : r.IsHomLift u (φ ≫ Functor.Fiber.fiberInclusion.map κ.hom) :=
    isHomLift_comp_fiberIso r φ hφ κ
  have hcart : ∀ {ψ : b.1 ⟶ a'.1}, r.IsHomLift u ψ → r.IsCartesian u ψ := fun hψ =>
    have := hψ
    (hr.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
  refine ⟨Functor.fiberIsoOfCartesian u _ φ' (hcart hc) (hcart hφ'), ?_⟩
  rw [← fiberEndRestrict_comp_iso r hr φ hφ κ hc θ]
  exact fiberEndRestrict_conj r hr _ hc φ' hφ' _
    (Functor.fiberIsoOfCartesian_hom_fac u _ φ' (hcart hc) (hcart hφ')) θ

/-- A bijection from an additive commutative group onto the endomorphisms of an object which
turns addition into composition makes composition of those endomorphisms commutative. -/
private theorem comp_comm_of_addEquiv {G : Type*} [AddCommGroup G] {E : Type*} [Category E]
    {a : E} (e : G ≃ (a ⟶ a)) (he : ∀ u v, e (u + v) = e u ≫ e v) (β γ : a ⟶ a) :
    β ≫ γ = γ ≫ β := by
  obtain ⟨u, rfl⟩ := e.surjective β
  obtain ⟨v, rfl⟩ := e.surjective γ
  rw [← he, ← he, add_comm]

/-- The structure map of `Spec (A' ×_A A')` over `S` is determined by its restrictions along the
two projections, because `Spec (A' ×_A A')` is the pushout of two copies of `Spec A'`. -/
private theorem structureMap_eq_of_projections (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) {hP : B.Contains (Spec (.of (R.aug.pullback R.aug)))}
    {toSP : B.obj hP ⟶ B.obj hS}
    (r₁ r₂ : (Over.mk R.structureMap : BigFppfOver B S hS) ⟶ Over.mk toSP)
    (hr₁ : B.inclusion.map r₁.left = Spec.map (CommRingCat.ofHom (R.aug.pullbackFst R.aug)))
    (hr₂ : B.inclusion.map r₂.left = Spec.map (CommRingCat.ofHom (R.aug.pullbackSnd R.aug))) :
    toSP = (BasedRing.prod (BasedRing.original R) (BasedRing.original R)).structureMap := by
  let O := BasedRing.original R
  apply ObjectProperty.hom_ext
  have hpo := Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
    (CommRingCat.ofHom R.aug) (CommRingCat.ofHom R.aug)
    (CommRingCat.ofHom (R.aug.pullbackFst R.aug)) (CommRingCat.ofHom (R.aug.pullbackSnd R.aug))
    (ringPullbackIsPullback R.aug R.aug) hq
  have w₁ := congrArg B.inclusion.map (Over.w r₁)
  have w₂ := congrArg B.inclusion.map (Over.w r₂)
  have c₁ := congrArg B.inclusion.map (Over.w (BasedRing.fst O O).toHom.right)
  have c₂ := congrArg B.inclusion.map (Over.w (BasedRing.snd O O).toHom.right)
  rw [Functor.map_comp, hr₁] at w₁
  rw [Functor.map_comp, hr₂] at w₂
  rw [Functor.map_comp] at c₁ c₂
  refine hpo.hom_ext ?_ ?_
  · exact w₂.trans c₂.symm
  · exact w₁.trans c₁.symm

/-- The composite of the maps `s` and `e` of a difference witness is the canonical difference
map `A' ×_A A' ⟶ A[I]`, on the underlying schemes. -/
private theorem inclusion_map_comp_eq_delta (R : AffineDeformation A B S hS toS hA)
    (hq : Function.Surjective R.aug) (hsq : RingHom.ker R.aug ^ 2 = ⊥)
    {hP : B.Contains (Spec (.of (R.aug.pullback R.aug)))} {toSP : B.obj hP ⟶ B.obj hS}
    {hQ : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker R.aug) :=
        oppositeModule A (ModuleCat.of A (RingHom.ker R.aug))
      letI : IsCentralScalar A (RingHom.ker R.aug) :=
        centralScalar A (ModuleCat.of A (RingHom.ker R.aug))
      B.Contains (Spec (.of (R.aug.pullback
        ((TrivSqZeroExt.fstHom A A (RingHom.ker R.aug)).toRingHom))))}
    {toSQ : B.obj hQ ⟶ B.obj hS}
    (s : squareZeroOver A B S hS toS (BasedRing.kernelSite R hq hsq) ⟶ Over.mk toSQ)
    (e : (Over.mk toSQ : BigFppfOver B S hS) ≅ Over.mk toSP)
    (er : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker R.aug) :=
        oppositeModule A (ModuleCat.of A (RingHom.ker R.aug))
      letI : IsCentralScalar A (RingHom.ker R.aug) :=
        centralScalar A (ModuleCat.of A (RingHom.ker R.aug))
      (R.aug.pullback R.aug) ≃+*
        R.aug.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker R.aug)).toRingHom))
    (hs : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker R.aug) :=
        oppositeModule A (ModuleCat.of A (RingHom.ker R.aug))
      letI : IsCentralScalar A (RingHom.ker R.aug) :=
        centralScalar A (ModuleCat.of A (RingHom.ker R.aug))
      B.inclusion.map s.left = Spec.map (CommRingCat.ofHom
        (R.aug.pullbackSnd ((TrivSqZeroExt.fstHom A A (RingHom.ker R.aug)).toRingHom))))
    (he : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker R.aug) :=
        oppositeModule A (ModuleCat.of A (RingHom.ker R.aug))
      letI : IsCentralScalar A (RingHom.ker R.aug) :=
        centralScalar A (ModuleCat.of A (RingHom.ker R.aug))
      B.inclusion.map e.hom.left = Spec.map (CommRingCat.ofHom er.toRingHom))
    (her : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker R.aug) :=
        oppositeModule A (ModuleCat.of A (RingHom.ker R.aug))
      letI : IsCentralScalar A (RingHom.ker R.aug) :=
        centralScalar A (ModuleCat.of A (RingHom.ker R.aug))
      ∀ y : R.aug.pullback R.aug, (er y).1.1 = y.1.1 ∧
        (er y).1.2 = ((R.aug y.1.1, kerDifference R.aug y) :
          TrivSqZeroExt A (RingHom.ker R.aug))) :
    B.inclusion.map s.left ≫ B.inclusion.map e.hom.left =
      Spec.map (CommRingCat.ofHom (BasedRing.delta R hq hsq).hom) := by
  rw [hs, he]
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro y
  exact (her y).2.trans (BasedRing.delta_apply R hq hsq y).symm

include hp in
/-- **The geometric difference transport, in normal form.** The base data of a witness of
`Deformation.Artin.IsGeometricInfDifference` are forced: the structure map of `A' ×_A A'` over
`S` is determined by its restrictions along the two projections, because `Spec (A' ×_A A')` is
the pushout of the two copies of `Spec A'` along `Spec A`; the projections and the
difference map are then the canonical ones. Read in the fibre of lifts under `x`, the witness
is a lift over `A' ×_A A'` with arrows from `x'` over the two projections and from the trivial
deformation over the difference map, and an endomorphism restricting to `𝟙`, to `α` and to
`αI` along those three arrows. -/
private theorem isGeometricInfDifference_normalForm
    (R : AffineDeformation A B S hS toS hA) (hq : Function.Surjective R.aug)
    (hsq : RingHom.ker R.aug ^ 2 = ⊥)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ R.arrow)))
    (αI : trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq) ⟶
      trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq))
    (α : x' ⟶ x')
    (h : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      IsGeometricInfDifference A B S hS toS hA p x hx hp R.ring R.contains R.structureMap
        R.aug hq hsq R.arrow (isSiteModule_kernel A B R.contains R.aug hq) x' αI α) :
    ∃ (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫
          (BasedRing.prod (BasedRing.original R) (BasedRing.original R)).toAffine.arrow)))
      (φ₁ φ₂ : x'.1 ⟶ a.1)
      (χ : (trivialDeformation A B S hS toS hA p x hx hp
        (BasedRing.kernelSite R hq hsq)).1 ⟶ a.1)
      (hφ₁ : (Under.post p).IsHomLift (AffineDeformation.underMap p x hx
        (BasedRing.snd (BasedRing.original R) (BasedRing.original R)).toHom) φ₁)
      (hφ₂ : (Under.post p).IsHomLift (AffineDeformation.underMap p x hx
        (BasedRing.fst (BasedRing.original R) (BasedRing.original R)).toHom) φ₂)
      (hχ : (Under.post p).IsHomLift
        (AffineDeformation.underMap p x hx (BasedRing.delta R hq hsq).toHom) χ)
      (θ : a ⟶ a),
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) φ₂ hφ₂ θ =
          𝟙 x' ∧
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) φ₁ hφ₁ θ = α ∧
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) χ hχ θ = αI := by
  let O := BasedRing.original R
  let PP := BasedRing.prod O O
  obtain ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, v, w, φ₁, φ₂, ψ, ε, θ,
    hφ₁, hφ₂, hψ, hε, hc₁, hc₂, hθ, hθ₂, hα, hαI⟩ := h
  have := lift_hom_isHomLift A B S hS toS hA p x hx R x'
  have i₁ : p.IsHomLift r₂ φ₁ := hφ₁.toIsHomLift
  have i₂ : p.IsHomLift r₁ φ₂ := hφ₂.toIsHomLift
  have i₀ : p.IsHomLift (R.arrow ≫ r₂) (x'.1.hom ≫ φ₁) := by
    have := i₁
    infer_instance
  have iχ : p.IsHomLift (s ≫ e.hom) (ψ ≫ ε) := by
    have := hψ.toIsHomLift
    have := hε.toIsHomLift
    infer_instance
  clear hφ₁ hφ₂
  -- the structure map of `A' ×_A A'` over `S` is the canonical one
  have hSP := structureMap_eq_of_projections A B S hS toS hA R hq r₁ r₂ hr₁ hr₂
  subst hSP
  obtain rfl : r₁ = (BasedRing.fst O O).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hr₁)
  obtain rfl : r₂ = (BasedRing.snd O O).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hr₂)
  -- the composite of `s` and `e` is the canonical difference map
  have hse : s ≫ e.hom = (BasedRing.delta R hq hsq).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (inclusion_map_comp_eq_delta A B S hS toS hA R hq hsq s e er hs he her))
  -- the witness, read in the fibre of lifts under `x`
  have hm : p.IsHomLift PP.toAffine.arrow (x'.1.hom ≫ φ₁) :=
    isHomLift_congr p (Under.w (BasedRing.snd O O).toHom) _ i₀
  let a := liftOfIsHomLift A B S hS toS hA p x hx PP.toAffine (x'.1.hom ≫ φ₁) hm
  let φ₁u : x'.1 ⟶ a.1 := Under.homMk φ₁ rfl
  let φ₂u : x'.1 ⟶ a.1 := Under.homMk φ₂ hc₁.symm
  let χ : (trivialDeformation A B S hS toS hA p x hx hp
      (BasedRing.kernelSite R hq hsq)).1 ⟶ a.1 := Under.homMk (ψ ≫ ε) hc₂
  have hχ : p.IsHomLift (BasedRing.delta R hq hsq).toHom.right (ψ ≫ ε) :=
    isHomLift_congr p hse _ iχ
  have hθa : a.1.hom ≫ θ = a.1.hom :=
    (Category.assoc _ _ _).trans ((congrArg (x'.1.hom ≫ ·) hα.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ₁) (Under.w α.1))))
  let θu : a.1 ⟶ a.1 := Under.homMk θ hθa
  let θf : a ⟶ a := ⟨θu, underPost_isHomLift_of_right B S hS p x (𝟙 _) θu hθ⟩
  refine ⟨a, φ₁u, φ₂u, χ,
    underPost_isHomLift_of_right B S hS p x
      (AffineDeformation.underMap p x hx (BasedRing.snd O O).toHom) φ₁u i₁,
    underPost_isHomLift_of_right B S hS p x
      (AffineDeformation.underMap p x hx (BasedRing.fst O O).toHom) φ₂u i₂,
    underPost_isHomLift_of_right B S hS p x
      (AffineDeformation.underMap p x hx (BasedRing.delta R hq hsq).toHom) χ hχ, θf, ?_, ?_, ?_⟩
  · refine (fiberEndRestrict_eq _ _ _ _ _ _ ?_).symm
    exact Under.UnderMorphism.ext ((Category.id_comp φ₂).trans hθ₂.symm)
  · refine (fiberEndRestrict_eq _ _ _ _ _ _ ?_).symm
    exact Under.UnderMorphism.ext hα
  · refine (fiberEndRestrict_eq _ _ _ _ _ _ ?_).symm
    exact Under.UnderMorphism.ext (hαI.trans (Category.assoc _ _ _).symm)

include hp in
/-- **The geometric difference determines the automorphism of the trivial deformation.** If
the same infinitesimal automorphism `α` of a lift `x'` is the difference transport of `αI` and
of `αI'`, then `αI = αI'`. Two glueings of `x'` with itself over `A' ×_A A'` are isomorphic by
(RS*); conjugating along such an isomorphism changes the restrictions to `x'` and to the
trivial deformation only by conjugation, which is trivial because both groups of
infinitesimal automorphisms are commutative; and by (RS*) an endomorphism of the glueing is
determined by its two restrictions to `x'`. -/
private theorem isGeometricInfDifference_left_unique (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (R : AffineDeformation A B S hS toS hA) (hq : Function.Surjective R.aug)
    (hsq : RingHom.ker R.aug ^ 2 = ⊥)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ R.arrow)))
    (αI αI' : trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq) ⟶
      trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq))
    (α : x' ⟶ x')
    (h : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      IsGeometricInfDifference A B S hS toS hA p x hx hp R.ring R.contains R.structureMap
        R.aug hq hsq R.arrow (isSiteModule_kernel A B R.contains R.aug hq) x' αI α)
    (h' : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      IsGeometricInfDifference A B S hS toS hA p x hx hp R.ring R.contains R.structureMap
        R.aug hq hsq R.arrow (isSiteModule_kernel A B R.contains R.aug hq) x' αI' α) :
    αI = αI' := by
  have hq' := underPost_isFiberedInGroupoids p hp x
  let O := BasedRing.original R
  let C := exists_infComparison A B S hS toS hA p x hx hp hRS Inf R.ring R.contains
    R.structureMap R.aug hq hsq R.arrow R.arrow_eq x'
  have hcX : ∀ β γ : x' ⟶ x', β ≫ γ = γ ≫ β := comp_comm_of_addEquiv C.equiv C.equiv_add
  have hcT : ∀ β γ : trivialDeformation A B S hS toS hA p x hx hp
      (BasedRing.kernelSite R hq hsq) ⟶
        trivialDeformation A B S hS toS hA p x hx hp (BasedRing.kernelSite R hq hsq),
      β ≫ γ = γ ≫ β :=
    comp_comm_of_addEquiv (Inf.autEquiv _)
      (autEquiv_add A B S hS toS hA p x hx hp hRS Inf _)
  obtain ⟨a, φ₁, φ₂, χ, hφ₁, hφ₂, hχ, θ, h₂, h₁, h₃⟩ :=
    isGeometricInfDifference_normalForm A B S hS toS hA p x hx hp R hq hsq x' αI α h
  obtain ⟨a', φ₁', φ₂', χ', hφ₁', hφ₂', hχ', θ', h₂', h₁', h₃'⟩ :=
    isGeometricInfDifference_normalForm A B S hS toS hA p x hx hp R hq hsq x' αI' α h'
  -- the two glueings are isomorphic lifts over `A' ×_A A'`
  have key : ∀ (b : (Under.post p).Fiber (Under.mk (eqToHom hx ≫
        (BasedRing.prod O O).toAffine.arrow))) (ψ₁ ψ₂ : x'.1 ⟶ b.1),
      (Under.post p).IsHomLift
        (AffineDeformation.underMap p x hx (BasedRing.snd O O).toHom) ψ₁ →
      (Under.post p).IsHomLift
        (AffineDeformation.underMap p x hx (BasedRing.fst O O).toHom) ψ₂ →
      (AffineDeformation.map p x hx hp (BasedRing.fst O O).toHom (Quotient.mk _ b),
        AffineDeformation.map p x hx hp (BasedRing.snd O O).toHom (Quotient.mk _ b)) =
        (Quotient.mk _ x', Quotient.mk _ x') := by
    intro b ψ₁ ψ₂ hψ₁ hψ₂
    have : p.IsHomLift (BasedRing.fst O O).toHom.right ψ₂.right :=
      underPost_isHomLift_right p
        (AffineDeformation.underMap p x hx (BasedRing.fst O O).toHom) ψ₂ hψ₂
    have : p.IsHomLift (BasedRing.snd O O).toHom.right ψ₁.right :=
      underPost_isHomLift_right p
        (AffineDeformation.underMap p x hx (BasedRing.snd O O).toHom) ψ₁ hψ₁
    have hc₂ : p.IsStronglyCartesian (BasedRing.fst O O).toHom.right ψ₂.right :=
      hp.isStronglyCartesian_homLift _ _
    have hc₁ : p.IsStronglyCartesian (BasedRing.snd O O).toHom.right ψ₁.right :=
      hp.isStronglyCartesian_homLift _ _
    exact Prod.ext
      (AffineDeformation.map_eq_of_lift p x hx hp _ b x' ψ₂.right hc₂ (Under.w ψ₂))
      (AffineDeformation.map_eq_of_lift p x hx hp _ b x' ψ₁.right hc₁ (Under.w ψ₁))
  have hcls : (Quotient.mk _ a : BasedRing.classes p x hx (BasedRing.prod O O)) =
      Quotient.mk _ a' :=
    (BasedRing.pair_bijective p x hx hp hRS O O hq hsq).1
      ((key a φ₁ φ₂ hφ₁ hφ₂).trans (key a' φ₁' φ₂' hφ₁' hφ₂').symm)
  obtain ⟨κ⟩ := Quotient.exact hcls
  -- conjugating the second endomorphism into the first glueing
  have e₂ : fiberEndRestrict (Under.post p) hq' φ₂ hφ₂ (κ.hom ≫ θ' ≫ κ.inv) = 𝟙 x' := by
    obtain ⟨e, he⟩ := fiberEndRestrict_conj_iso (Under.post p) hq' κ φ₂ hφ₂ φ₂' hφ₂' θ'
    rw [he, h₂', Category.id_comp, e.hom_inv_id]
  have e₁ : fiberEndRestrict (Under.post p) hq' φ₁ hφ₁ (κ.hom ≫ θ' ≫ κ.inv) = α := by
    obtain ⟨e, he⟩ := fiberEndRestrict_conj_iso (Under.post p) hq' κ φ₁ hφ₁ φ₁' hφ₁' θ'
    rw [he, h₁', ← Category.assoc, hcX e.hom α, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have e₃ : fiberEndRestrict (Under.post p) hq' χ hχ (κ.hom ≫ θ' ≫ κ.inv) = αI' := by
    obtain ⟨e, he⟩ := fiberEndRestrict_conj_iso (Under.post p) hq' κ χ hχ χ' hχ' θ'
    rw [he, h₃', ← Category.assoc, hcT e.hom αI', Category.assoc, e.hom_inv_id,
      Category.comp_id]
  -- by (RS*) the two endomorphisms of the first glueing agree
  have hθ : κ.hom ≫ θ' ≫ κ.inv = θ :=
    (end_pair_bijective A B S hS toS hA p x hx hp hRS O.toAffine O.toAffine
      (BasedRing.prod O O).toAffine (BasedRing.fst O O).toHom (BasedRing.snd O O).toHom
      (BasedRing.prod_isPullbackSquare O O) hq hsq a φ₂ hφ₂ φ₁ hφ₁).1
      (Prod.ext (e₂.trans h₂.symm) (e₁.trans h₁.symm))
  rw [← h₃, ← e₃, hθ]

include hp in
/-- **The geometric difference is natural in the lift.** Transporting a witness of
`Deformation.Artin.IsGeometricInfDifference` along an isomorphism of lifts `f : x' ≅ x''`
gives a witness for the conjugate automorphism `f⁻¹ α f` of `x''`, with the same automorphism
of the trivial deformation. -/
public theorem IsGeometricInfDifference.conj
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      IsSiteModule A B (ModuleCat.of A (RingHom.ker q)))
    {x' x'' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))} (f : x' ≅ x'')
    (αI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      trivialDeformation A B S hS toS hA p x hx hp
          ⟨ModuleCat.of A (RingHom.ker q), hI⟩ ⟶
        trivialDeformation A B S hS toS hA p x hx hp
          ⟨ModuleCat.of A (RingHom.ker q), hI⟩)
    (α : x' ⟶ x')
    (h : IsGeometricInfDifference A B S hS toS hA p x hx hp A' hA' toS' q hq hsq g hI x' αI α) :
    IsGeometricInfDifference A B S hS toS hA p x hx hp A' hA' toS' q hq hsq g hI x'' αI
      (f.inv ≫ α ≫ f.hom) := by
  obtain ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, v, w, φ₁, φ₂, ψ, ε, θ,
    hφ₁, hφ₂, hψ, hε, hc₁, hc₂, hθ, hθ₂, hα, hαI⟩ := h
  have : p.IsHomLift (𝟙 (Over.mk toS' : BigFppfOver B S hS)) f.inv.1.right :=
    underPost_isHomLift_right p _ _ f.inv.2
  have := hφ₁.toIsHomLift
  have := hφ₂.toIsHomLift
  have hw : x''.1.hom ≫ f.inv.1.right = x'.1.hom := Under.w f.inv.1
  have hhi : f.hom.1.right ≫ f.inv.1.right = 𝟙 _ :=
    congrArg (fun k : x' ⟶ x' => k.1.right) f.hom_inv_id
  refine ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, v, w,
    f.inv.1.right ≫ φ₁, f.inv.1.right ≫ φ₂, ψ, ε, θ,
    hp.isStronglyCartesian_homLift _ _, hp.isStronglyCartesian_homLift _ _, hψ, hε, ?_, ?_, hθ,
    ?_, ?_, hαI⟩
  · rw [← Category.assoc x''.1.hom, hw, ← Category.assoc x''.1.hom, hw]
    exact hc₁
  · rw [← Category.assoc x''.1.hom, hw]
    exact hc₂
  · rw [Category.assoc, hθ₂]
  · have hcomp : (f.inv ≫ α ≫ f.hom).1.right =
        f.inv.1.right ≫ α.1.right ≫ f.hom.1.right := rfl
    rw [hcomp, Category.assoc, Category.assoc, ← Category.assoc f.hom.1.right, hhi,
      Category.id_comp, hα, Category.assoc]

include hp in
/-- **Stacks 07YB.** Let `𝒳` satisfy (RS*), let `(x, A' → A)` be a deformation situation with
kernel `I`, and let `x'`, `x''` be lifts of `x` to `Spec A'`. Composition gives a map
`Inf(x'/x) × Mor(x', x'') × Inf(x''/x) → Mor(x', x'')`, and since the lifts form a groupoid it
defines, at every morphism, simply transitive actions of `Inf(x'/x)` (by precomposition) and of
`Inf(x''/x)` (by postcomposition). Let `C'` and `C''` be the comparisons of Stacks 07Y9,
`Inf_x(I) ≅ Inf(x'/x)` and `Inf_x(I) ≅ Inf(x''/x)`. Then the two actions agree via these
identifications: `C'(a) ≫ f = f ≫ C''(a)` for every `a ∈ Inf_x(I)` and every morphism
`f : x' ⟶ x''`. In particular `Inf_x(I)` acts on `Mor(x', x'')`, and the action is simply
transitive as soon as `Mor(x', x'')` is nonempty: every orbit map is a bijection.

The agreement holds for *every* pair of comparisons in the sense of
`Deformation.Artin.InfComparisonData`, which pins a comparison geometrically. The proof shows
that this pin determines the comparison and is natural for isomorphisms of lifts
(`Deformation.Artin.IsGeometricInfDifference.conj`), using (RS*) and the commutativity of
`Inf(x'/x)` and of `Inf_x(I)`. -/
@[stacks 07YB "actions on Mor(x', x'') agree via Inf(x'/x) = Inf_x(I) = Inf(x''/x)"]
public theorem InfComparisonData.actions_agree (hRS : SatisfiesRSStar B S hS p hp)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    {x' x'' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))}
    (C' : InfComparisonData A B S hS toS hA p x hx hp Inf A' hA' toS' q hq hsq g x')
    (C'' : InfComparisonData A B S hS toS hA p x hx hp Inf A' hA' toS' q hq hsq g x'') :
    letI := Stacks.Smooth.kerModule hq hsq
    (∀ f : x' ⟶ x'', Function.Bijective (fun α : x' ⟶ x' => α ≫ f)) ∧
      (∀ f : x' ⟶ x'', Function.Bijective (fun β : x'' ⟶ x'' => f ≫ β)) ∧
      (∀ (a : Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), C'.kernelIsSiteModule⟩)
        (f : x' ⟶ x''), C'.equiv a ≫ f = f ≫ C''.equiv a) ∧
      (∀ f : x' ⟶ x'', C'.equiv 0 ≫ f = f) ∧
      (∀ (a b : Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), C'.kernelIsSiteModule⟩)
        (f : x' ⟶ x''), C'.equiv (a + b) ≫ f = C'.equiv a ≫ C'.equiv b ≫ f) ∧
      (∀ f : x' ⟶ x'', Function.Bijective
        (fun a : Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), C'.kernelIsSiteModule⟩ =>
          C'.equiv a ≫ f)) := by
  let := Stacks.Smooth.kerModule hq hsq
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))) :=
    (underPost_isFiberedInGroupoids p hp x).fiber_isGroupoid _
  have hpre : ∀ f : x' ⟶ x'', Function.Bijective (fun α : x' ⟶ x' => α ≫ f) := by
    intro f
    have := CategoryTheory.IsGroupoid.all_isIso f
    exact ⟨fun α β hαβ => (cancel_mono f).1 hαβ,
      fun γ => ⟨γ ≫ inv f, by simp⟩⟩
  have hpost : ∀ f : x' ⟶ x'', Function.Bijective (fun β : x'' ⟶ x'' => f ≫ β) := by
    intro f
    have := CategoryTheory.IsGroupoid.all_isIso f
    exact ⟨fun α β hαβ => (cancel_epi f).1 hαβ,
      fun γ => ⟨inv f ≫ γ, by simp⟩⟩
  have hagree : ∀ (a : Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), C'.kernelIsSiteModule⟩)
      (f : x' ⟶ x''), C'.equiv a ≫ f = f ≫ C''.equiv a := by
    intro a f
    have := CategoryTheory.IsGroupoid.all_isIso f
    let R : AffineDeformation A B S hS toS hA := ⟨.of A', hA', toS', q, g, hg⟩
    have hβ := IsGeometricInfDifference.conj A B S hS toS hA p x hx hp A' hA' toS' q hq hsq g
      C'.kernelIsSiteModule (asIso f) _ _ (C'.equiv_geometric a)
    obtain ⟨b, hb⟩ := C''.equiv.surjective ((asIso f).inv ≫ C'.equiv a ≫ (asIso f).hom)
    have hgeo := C''.equiv_geometric b
    rw [hb] at hgeo
    have hab : a = b := (Inf.autEquiv _).injective
      (isGeometricInfDifference_left_unique A B S hS toS hA p x hx hp hRS Inf R hq hsq x''
        _ _ _ hβ hgeo)
    subst hab
    rw [hb]
    simp
  refine ⟨hpre, hpost, hagree, fun f => ?_, fun a b f => ?_, fun f => ?_⟩
  · rw [C'.equiv_zero, Category.id_comp]
  · rw [C'.equiv_add, Category.assoc]
  · exact (hpre f).comp C'.equiv.bijective

end InfinitesimalComparison

/-! ### The geometric pins determine the difference, the action and the comparison -/

section GeometricUniqueness

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- **The geometric difference, read on lift classes.** A witness of
`Deformation.Artin.IsGeometricDifference` produces a class of lifts over `A' ×_A A'` which
restricts to `z₂` and `z₁` along the two projections and to the class attached to the tangent
vector along the difference map `A' ×_A A' ⟶ A[I]`. -/
private theorem isGeometricDifference_classes
    (T : TangentFunctorData A B S hS toS hA p x hx)
    (R : AffineDeformation A B S hS toS hA) (hq : Function.Surjective R.aug)
    (hsq : RingHom.ker R.aug ^ 2 = ⊥) (z₁ z₂ : AffineDeformation.classes p x hx R)
    (a : (T.functor.obj (BasedRing.kernelSite R hq hsq) : Type _))
    (h : letI : Module A (RingHom.ker R.aug) := Stacks.Smooth.kerModule hq hsq
      IsGeometricDifference A B S hS toS hA p x hx T R.ring R.contains R.structureMap
        R.aug hq hsq R.arrow (isSiteModule_kernel A B R.contains R.aug hq) z₁ z₂ a) :
    ∃ c : BasedRing.classes p x hx (BasedRing.prod (BasedRing.original R) (BasedRing.original R)),
      BasedRing.map p x hx hp (BasedRing.fst (BasedRing.original R) (BasedRing.original R)) c =
          z₂ ∧
        BasedRing.map p x hx hp (BasedRing.snd (BasedRing.original R) (BasedRing.original R))
            c = z₁ ∧
        BasedRing.map p x hx hp (BasedRing.delta R hq hsq) c =
          T.liftEquiv (BasedRing.kernelSite R hq hsq) a := by
  let O := BasedRing.original R
  let PP := BasedRing.prod O O
  obtain ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, t₁, t₂, t, v, w,
    φ₁, φ₂, ψ, ε, ht₁, ht₂, ht, hφ₁, hφ₂, hψ, hε, hc₁, hc₂⟩ := h
  have := lift_hom_isHomLift A B S hS toS hA p x hx R t₁
  have i₀ : p.IsHomLift (R.arrow ≫ r₂) (t₁.1.hom ≫ φ₁) := by
    have := hφ₁.toIsHomLift
    infer_instance
  have hSP := structureMap_eq_of_projections A B S hS toS hA R hq r₁ r₂ hr₁ hr₂
  subst hSP
  obtain rfl : r₁ = (BasedRing.fst O O).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hr₁)
  obtain rfl : r₂ = (BasedRing.snd O O).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hr₂)
  have hse : s ≫ e.hom = (BasedRing.delta R hq hsq).toHom.right :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (inclusion_map_comp_eq_delta A B S hS toS hA R hq hsq s e er hs he her))
  have hm : p.IsHomLift PP.toAffine.arrow (t₁.1.hom ≫ φ₁) :=
    isHomLift_congr p (Under.w (BasedRing.snd O O).toHom) _ i₀
  let c := liftOfIsHomLift A B S hS toS hA p x hx PP.toAffine (t₁.1.hom ≫ φ₁) hm
  have iχ : p.IsHomLift (s ≫ e.hom) (ψ ≫ ε) := by
    have := hψ.toIsHomLift
    have := hε.toIsHomLift
    infer_instance
  have hχ : p.IsHomLift (BasedRing.delta R hq hsq).toHom.right (ψ ≫ ε) :=
    isHomLift_congr p hse _ iχ
  refine ⟨Quotient.mk _ c, ?_, ?_, ?_⟩
  · rw [← ht₂]
    exact AffineDeformation.map_eq_of_lift p x hx hp (BasedRing.fst O O).toHom c t₂ φ₂ hφ₂
      hc₁.symm
  · rw [← ht₁]
    exact AffineDeformation.map_eq_of_lift p x hx hp (BasedRing.snd O O).toHom c t₁ φ₁ hφ₁ rfl
  · have := hχ
    exact (AffineDeformation.map_eq_of_lift p x hx hp (BasedRing.delta R hq hsq).toHom c t
      (ψ ≫ ε) (hp.isStronglyCartesian_homLift (BasedRing.delta R hq hsq).toHom.right (ψ ≫ ε))
      hc₂).trans ht

include hp in
/-- **The geometric difference of two lift classes is unique.** If two tangent vectors are
both the difference of `z₁` from `z₂` in the sense of `Deformation.Artin.IsGeometricDifference`,
they are equal: the glueing of the two lifts over `A' ×_A A'` is unique up to isomorphism by
(RS*), and the tangent vector is its restriction along the difference map. -/
public theorem isGeometricDifference_unique (hRS : SatisfiesRSStar B S hS p hp)
    (T : TangentFunctorData A B S hS toS hA p x hx)
    (A' : Type u) [CommRing A'] (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS) (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      IsSiteModule A B (ModuleCat.of A (RingHom.ker q)))
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx g)
    (a a' : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), hI⟩ : Type _))
    (h : IsGeometricDifference A B S hS toS hA p x hx T A' hA' toS' q hq hsq g hI z₁ z₂ a)
    (h' : IsGeometricDifference A B S hS toS hA p x hx T A' hA' toS' q hq hsq g hI z₁ z₂ a') :
    a = a' := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let R : AffineDeformation A B S hS toS hA := ⟨.of A', hA', toS', q, g, hg⟩
  let O := BasedRing.original R
  obtain ⟨c, hc₁, hc₂, hc₃⟩ :=
    isGeometricDifference_classes A B S hS toS hA p x hx hp T R hq hsq z₁ z₂ a h
  obtain ⟨c', hc₁', hc₂', hc₃'⟩ :=
    isGeometricDifference_classes A B S hS toS hA p x hx hp T R hq hsq z₁ z₂ a' h'
  have hcc : c = c' := (BasedRing.pair_bijective p x hx hp hRS O O hq hsq).1
    (Prod.ext (hc₁.trans hc₁'.symm) (hc₂.trans hc₂'.symm))
  subst hcc
  exact (T.liftEquiv (BasedRing.kernelSite R hq hsq)).injective (hc₃.symm.trans hc₃')

include hp in
/-- **The difference map of an action on lifts is the geometric difference.** -/
public theorem ActionOnLiftsData.difference_eq_of_isGeometricDifference
    (hRS : SatisfiesRSStar B S hS p hp)
    {T : TangentFunctorData A B S hS toS hA p x hx}
    {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))}
    {toS' : B.obj hA' ⟶ B.obj hS} {q : A' →+* A} {hq : Function.Surjective q}
    {hsq : RingHom.ker q ^ 2 = ⊥}
    {g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    (D : ActionOnLiftsData A B S hS toS hA p x hx T A' hA' toS' q hq hsq g)
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx g)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), D.kernelIsSiteModule⟩ : Type _))
    (h : IsGeometricDifference A B S hS toS hA p x hx T A' hA' toS' q hq hsq g
      D.kernelIsSiteModule z₁ z₂ a) :
    D.difference z₁ z₂ = a :=
  isGeometricDifference_unique A B S hS toS hA p x hx hp hRS T A' hA' toS' q hq hsq g hg
    D.kernelIsSiteModule z₁ z₂ _ _ (D.difference_geometric z₁ z₂) h

include hp in
/-- **The action on lifts is pinned by the geometric difference**: the tangent vector `a`
moves `z` to `z'` exactly when `a` is the geometric difference of `z'` from `z`. -/
public theorem ActionOnLiftsData.action_eq_of_isGeometricDifference
    (hRS : SatisfiesRSStar B S hS p hp)
    {T : TangentFunctorData A B S hS toS hA p x hx}
    {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))}
    {toS' : B.obj hA' ⟶ B.obj hS} {q : A' →+* A} {hq : Function.Surjective q}
    {hsq : RingHom.ker q ^ 2 = ⊥}
    {g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    (D : ActionOnLiftsData A B S hS toS hA p x hx T A' hA' toS' q hq hsq g)
    (z z' : liftClassesOver A B S hS toS hA p x hx g)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), D.kernelIsSiteModule⟩ : Type _))
    (h : IsGeometricDifference A B S hS toS hA p x hx T A' hA' toS' q hq hsq g
      D.kernelIsSiteModule z' z a) :
    D.action a z = z' := by
  obtain ⟨b, rfl⟩ := (D.orbit_bijective z).2 z'
  have hb := ActionOnLiftsData.difference_eq_of_isGeometricDifference A B S hS toS hA p x hx hp
    hRS hg D _ z a h
  rw [D.action_difference] at hb
  rw [hb]

include hp in
/-- **The comparison of Stacks 07Y9 part (1) is pinned by the geometric difference**: the
infinitesimal automorphism of the lift attached to `a ∈ Inf_x(I)` is the unique one which is
the difference transport of the automorphism of the trivial deformation attached to `a`. -/
public theorem InfComparisonData.equiv_eq_of_isGeometricInfDifference
    (hRS : SatisfiesRSStar B S hS p hp)
    {Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp}
    {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))}
    {toS' : B.obj hA' ⟶ B.obj hS} {q : A' →+* A} {hq : Function.Surjective q}
    {hsq : RingHom.ker q ^ 2 = ⊥}
    {g : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}
    (hg : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom q))
    {x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))}
    (C : InfComparisonData A B S hS toS hA p x hx hp Inf A' hA' toS' q hq hsq g x')
    (a : letI := Stacks.Smooth.kerModule hq hsq
      Inf.functor.obj ⟨ModuleCat.of A (RingHom.ker q), C.kernelIsSiteModule⟩)
    (α : x' ⟶ x')
    (h : letI := Stacks.Smooth.kerModule hq hsq
      IsGeometricInfDifference A B S hS toS hA p x hx hp A' hA' toS' q hq hsq g
        C.kernelIsSiteModule x' (Inf.autEquiv _ a) α) :
    C.equiv a = α := by
  let := Stacks.Smooth.kerModule hq hsq
  let R : AffineDeformation A B S hS toS hA := ⟨.of A', hA', toS', q, g, hg⟩
  obtain ⟨b, hb⟩ := C.equiv.surjective α
  have hgeo := C.equiv_geometric b
  rw [hb] at hgeo
  have hab : a = b := (Inf.autEquiv _).injective
    (isGeometricInfDifference_left_unique A B S hS toS hA p x hx hp hRS Inf R hq hsq x'
      _ _ _ h hgeo)
  rw [hab, hb]

end GeometricUniqueness

end Deformations

/-! ### Restricting lifts along a morphism of thickenings -/

section Restriction

open CategoryTheory.Functor

variable {A C : Type u} [CommRing A] [CommRing C]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC} (φ₀ : y ⟶ x)
  {U V : BigFppfOver B S hS} {gA : algebraOver A B S hS toS hA ⟶ U}
  {gC : algebraOver C B S hS toSC hC ⟶ V} {k : V ⟶ U}

include hp in
/-- Two vertical endomorphisms of a lift which agree after composing with an arrow of `𝒳`
out of the lift are equal: every arrow of a category fibred in groupoids is cartesian. -/
public theorem underFiber_end_ext {z : X} {T : Under (p.obj z)} {b : (Under.post p).Fiber T}
    {a : X} {W : BigFppfOver B S hS} {k' : T.right ⟶ W} (φ : b.1.right ⟶ a)
    (hφ : p.IsHomLift k' φ)
    (χ χ' : b ⟶ b) (h : χ.1.right ≫ φ = χ'.1.right ≫ φ) : χ = χ' := by
  have := hφ
  have := hp.isStronglyCartesian_homLift k' φ
  have : p.IsHomLift (𝟙 T.right) (Fiber.fiberInclusion.map χ).right :=
    underPost_isHomLift_right p (𝟙 T) χ.1 χ.2
  have : p.IsHomLift (𝟙 T.right) (Fiber.fiberInclusion.map χ').right :=
    underPost_isHomLift_right p (𝟙 T) χ'.1 χ'.2
  apply Functor.Fiber.hom_ext
  exact Under.UnderMorphism.ext (IsStronglyCartesian.ext p k' φ (𝟙 T.right) h)

include hp in
/-- **Restriction of an endomorphism of a lift along an arrow of lifts.** Let `b` be a lift
of `y` and `a` a lift of `x`, and let `φ` be an arrow from `b` to `a` lying over `k`,
compatible with `φ₀ : y ⟶ x`. Every vertical endomorphism `θ` of `a` restricts to a unique
vertical endomorphism of `b` compatible with `φ`. -/
public def liftEndRestrict {a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))}
    {b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))}
    (φ : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ)
    (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom) (θ : a ⟶ a) : b ⟶ b := by
  haveI := hφ
  haveI := hp.isStronglyCartesian_homLift k φ
  haveI : p.IsHomLift (𝟙 U) θ.1.right := underPost_isHomLift_right p (𝟙 _) θ.1 θ.2
  have hk : k = 𝟙 V ≫ k := (Category.id_comp k).symm
  refine underFiberHomMk p hy gC (IsStronglyCartesian.map p k φ hk (φ ≫ θ.1.right))
    (IsStronglyCartesian.map_isHomLift p k φ hk _) ?_
  have := underFiber_isHomLift p hy gC b
  refine IsStronglyCartesian.ext p k φ gC ?_
  rw [Category.assoc, IsStronglyCartesian.fac, ← Category.assoc, hc, Category.assoc,
    show a.1.hom ≫ θ.1.right = a.1.hom from Under.w θ.1]

include hp in
/-- The defining square of `Deformation.Artin.liftEndRestrict`. -/
public theorem liftEndRestrict_fac {a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))}
    {b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))}
    (φ : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ)
    (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom) (θ : a ⟶ a) :
    (liftEndRestrict p hp φ₀ φ hφ hc θ).1.right ≫ φ = φ ≫ θ.1.right := by
  have := hφ
  have := hp.isStronglyCartesian_homLift k φ
  have : p.IsHomLift (𝟙 U) θ.1.right := underPost_isHomLift_right p (𝟙 _) θ.1 θ.2
  exact IsStronglyCartesian.fac p k φ (Category.id_comp k).symm (φ ≫ θ.1.right)

include hp in
/-- The defining square determines `Deformation.Artin.liftEndRestrict`. -/
public theorem liftEndRestrict_eq {a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))}
    {b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))}
    (φ : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ)
    (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom) (θ : a ⟶ a) (χ : b ⟶ b)
    (hχ : χ.1.right ≫ φ = φ ≫ θ.1.right) : χ = liftEndRestrict p hp φ₀ φ hφ hc θ :=
  underFiber_end_ext p hp φ hφ _ _ (hχ.trans (liftEndRestrict_fac p hp φ₀ φ hφ hc θ).symm)

include hp in
/-- **Restriction of endomorphisms is single-valued when the endomorphisms of the restricted
lift commute.** Two arrows `φ`, `φ'` from `b` to `a` over the same base arrow and compatible
with `φ₀` differ by a vertical automorphism of `b`, so the endomorphisms of `b` they restrict
`θ` to are conjugate; when the endomorphisms of `b` commute they agree. -/
public theorem liftEnd_eq_of_comm {a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))}
    {b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))}
    (hcomm : ∀ χ χ' : b ⟶ b, χ ≫ χ' = χ' ≫ χ)
    (φ φ' : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ) (hφ' : p.IsHomLift k φ')
    (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom) (hc' : b.1.hom ≫ φ' = φ₀ ≫ a.1.hom)
    (θ : a ⟶ a) (χ χ' : b ⟶ b)
    (hχ : χ.1.right ≫ φ = φ ≫ θ.1.right) (hχ' : χ'.1.right ≫ φ' = φ' ≫ θ.1.right) :
    χ = χ' := by
  have := hφ
  have := hφ'
  have := hp.isStronglyCartesian_homLift k φ'
  have hk : k = 𝟙 V ≫ k := (Category.id_comp k).symm
  let ι := IsStronglyCartesian.map p k φ' hk φ
  have hι : p.IsHomLift (𝟙 V) ι := IsStronglyCartesian.map_isHomLift p k φ' hk φ
  have hιfac : ι ≫ φ' = φ := IsStronglyCartesian.fac p k φ' hk φ
  have := underFiber_isHomLift p hy gC b
  have : p.IsHomLift gC (b.1.hom ≫ ι) := inferInstance
  have hw : b.1.hom ≫ ι = b.1.hom := by
    refine IsStronglyCartesian.ext p k φ' gC ?_
    rw [Category.assoc, hιfac, hc, hc']
  let ιl : b ⟶ b := underFiberHomMk p hy gC ι hι hw
  have hconj : χ ≫ ιl = ιl ≫ χ' := by
    refine underFiber_end_ext p hp φ' hφ' _ _ ?_
    change (χ.1.right ≫ ι) ≫ φ' = (ι ≫ χ'.1.right) ≫ φ'
    rw [Category.assoc, hιfac, hχ, Category.assoc, hχ', ← Category.assoc, hιfac]
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))) :=
    (underPost_isFiberedInGroupoids p hp y).fiber_isGroupoid _
  have : IsIso ιl := CategoryTheory.IsGroupoid.all_isIso ιl
  exact (cancel_mono ιl).1 (hconj.trans (hcomm ιl χ'))

variable (specMap : algebraOver C B S hS toSC hC ⟶ algebraOver A B S hS toS hA)
  (hφ₀ : p.IsHomLift specMap φ₀) (hk : specMap ≫ gA = gC ≫ k)

include hp hφ₀ hk in
/-- **Restriction of lifts.** Every lift `a` of `x` along `gA` restricts along `k` to a lift
of `y` along `gC`, compatibly with `φ₀ : y ⟶ x`. -/
public theorem exists_liftRestriction (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))) :
    ∃ (b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))) (φ : b.1.right ⟶ a.1.right),
      p.IsHomLift k φ ∧ b.1.hom ≫ φ = φ₀ ≫ a.1.hom := by
  let : p.IsFibered := hp.isFibered
  have := underFiber_isHomLift p hx gA a
  have hcomp : p.IsHomLift (specMap ≫ gA) (φ₀ ≫ a.1.hom) := inferInstance
  let xa : p.Fiber U := ⟨a.1.right, underFiber_right_obj p hx gA a⟩
  let ρ := (Functor.chosenPullbacks p).map k xa
  have hρ : p.IsStronglyCartesian k ρ := (Functor.chosenPullbacks p).isStronglyCartesian k xa
  have : p.IsHomLift (specMap ≫ gA) (φ₀ ≫ a.1.hom) := hcomp
  let m := IsStronglyCartesian.map p k ρ hk (φ₀ ≫ a.1.hom)
  have hm : p.IsHomLift gC m := IsStronglyCartesian.map_isHomLift p k ρ hk _
  refine ⟨⟨Under.mk m, StructuredArrow.obj_ext _ _ ((Functor.chosenPullbacks p).obj k xa).2 ?_⟩,
    ρ, hρ.toIsHomLift, IsStronglyCartesian.fac p k ρ hk _⟩
  change p.map m ≫ eqToHom ((Functor.chosenPullbacks p).obj k xa).2 = eqToHom hy ≫ gC
  rw [IsHomLift.fac' p gC m, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

omit specMap hφ₀ hk in
include hp in
/-- **Restriction of lifts is well defined on isomorphism classes.** -/
public theorem liftClass_eq_of_restriction
    {a a' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA))}
    {b b' : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))}
    (φ : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ) (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom)
    (φ' : b'.1.right ⟶ a'.1.right) (hφ' : p.IsHomLift k φ')
    (hc' : b'.1.hom ≫ φ' = φ₀ ≫ a'.1.hom)
    (h : (Quotient.mk _ a : liftClassesOver A B S hS toS hA p x hx gA) = Quotient.mk _ a') :
    (Quotient.mk _ b : liftClassesOver C B S hS toSC hC p y hy gC) = Quotient.mk _ b' := by
  obtain ⟨α⟩ := Quotient.exact h
  have := hφ
  have := hφ'
  have := hp.isStronglyCartesian_homLift k φ'
  have : p.IsHomLift (𝟙 U) α.hom.1.right := underPost_isHomLift_right p (𝟙 _) α.hom.1 α.hom.2
  have hk : k = 𝟙 V ≫ k := (Category.id_comp k).symm
  let ι := IsStronglyCartesian.map p k φ' hk (φ ≫ α.hom.1.right)
  have hι : p.IsHomLift (𝟙 V) ι := IsStronglyCartesian.map_isHomLift p k φ' hk _
  have hιfac : ι ≫ φ' = φ ≫ α.hom.1.right := IsStronglyCartesian.fac p k φ' hk _
  have := underFiber_isHomLift p hy gC b
  have := underFiber_isHomLift p hy gC b'
  have hw : b.1.hom ≫ ι = b'.1.hom := by
    refine IsStronglyCartesian.ext p k φ' gC ?_
    rw [Category.assoc, hιfac, ← Category.assoc, hc, Category.assoc,
      show a.1.hom ≫ α.hom.1.right = a'.1.hom from Under.w α.hom.1, hc']
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))) :=
    (underPost_isFiberedInGroupoids p hp y).fiber_isGroupoid _
  exact Quotient.sound ⟨asIso (underFiberHomMk p hy gC ι hι hw)⟩

include hp hφ₀ hk in
/-- **The pullback map on isomorphism classes of lifts** along a morphism of thickenings. -/
public def liftClassesRestrict :
    liftClassesOver A B S hS toS hA p x hx gA → liftClassesOver C B S hS toSC hC p y hy gC :=
  Quotient.lift (fun a => Quotient.mk _
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose)
    (fun a a' h => liftClass_eq_of_restriction p hp φ₀
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose_spec.1
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose_spec.2
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a').choose_spec.choose
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a').choose_spec.choose_spec.1
      (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a').choose_spec.choose_spec.2
      (Quotient.sound h))

include hp hφ₀ hk in
/-- The pullback map on classes of lifts sends the class of a lift to the class of any
restriction of it. -/
public theorem liftClassesRestrict_mk
    (a : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
    (b : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC)))
    (φ : b.1.right ⟶ a.1.right) (hφ : p.IsHomLift k φ) (hc : b.1.hom ≫ φ = φ₀ ≫ a.1.hom) :
    liftClassesRestrict p hp φ₀ specMap hφ₀ hk (Quotient.mk _ a) = Quotient.mk _ b :=
  liftClass_eq_of_restriction p hp φ₀
    (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose
    (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose_spec.1
    (exists_liftRestriction p hp φ₀ specMap hφ₀ hk a).choose_spec.choose_spec.2
    φ hφ hc rfl

end Restriction

/-! ### Restricting the geometric pins along a morphism of deformation situations -/

/-- Composing the spectra of two ring maps is taking the spectrum of their composite. -/
private theorem specMap_comp {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (a : R₁ →+* R₂) (b : R₂ →+* R₃) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (b.comp a)) :=
  (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.ofHom_comp a b).symm)

/-- A commutative square of ring maps gives a commutative square of spectra. -/
private theorem specMap_comp_eq {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] [CommRing R₄] (a : R₁ →+* R₂) (b : R₂ →+* R₃) (c : R₁ →+* R₄)
    (d : R₄ →+* R₃) (h : ∀ z, b (a z) = d (c z)) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom c) := by
  rw [specMap_comp, specMap_comp]
  congr 2
  exact RingHom.ext h

section RestrictedBase

variable {A C : Type u} [CommRing A] [CommRing C]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}

/-- Two morphisms of the site over `S` with the same underlying morphism of schemes agree. -/
private theorem bigFppfOver_hom_ext {U V : BigFppfOver B S hS} (a b : U ⟶ V)
    (h : B.inclusion.map a.left = B.inclusion.map b.left) : a = b :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)

/-- **The base of the restriction of a difference witness.** A morphism of deformation
situations `(C' → C) ⟶ (A' → A)`, given by `f' : A' → C'` over `f : A → C`, induces
morphisms `Spec (C' ×_C C') ⟶ Spec (A' ×_A A')` and `Spec (C' ×_C C[J]) ⟶ Spec (A' ×_A A[I])`
over `S`, compatible with the projections, with the difference isomorphisms and with the
maps out of the square-zero extensions. On the `C`-side the fibre products are the canonical
ones; on the `A`-side they are those of an arbitrary difference witness, whose structure maps
over `S` are pinned by its projections. -/
private theorem exists_restrictedDifferenceBase {f : A →+* C}
    {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))}
    {toS' : B.obj hA' ⟶ B.obj hS}
    {q : A' →+* A} (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
    (RC : AffineDeformation C B S hS toSC hC) (hqC : Function.Surjective RC.aug)
    (hsqC : RingHom.ker RC.aug ^ 2 = ⊥)
    {f' : A' →+* RC.ring} (hff : RC.aug.comp f' = f.comp q)
    {k : RC.siteOver ⟶ (Over.mk toS' : BigFppfOver B S hS)}
    (hk : B.inclusion.map k.left = Spec.map (CommRingCat.ofHom f'))
    (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      IsSiteModule A B (ModuleCat.of A (RingHom.ker q)))
    (eI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      squareZeroRing A (ModuleCat.of A (RingHom.ker q)) ⟶
        squareZeroRing C (BasedRing.kernelSite RC hqC hsqC).obj)
    (heI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module C (RingHom.ker RC.aug) := Stacks.Smooth.kerModule hqC hsqC
      ∀ z, (eI.hom z).fst = f z.fst ∧
        ((eI.hom z).snd : RingHom.ker RC.aug).1 = f' (z.snd : RingHom.ker q).1)
    (kI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      squareZeroOver C B S hS toSC (BasedRing.kernelSite RC hqC hsqC) ⟶
        squareZeroOver A B S hS toS ⟨ModuleCat.of A (RingHom.ker q), hI⟩)
    (hkI : B.inclusion.map kI.left = Spec.map eI)
    (hP : B.Contains (Spec (.of (q.pullback q))))
    (hQ : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
      letI : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
      B.Contains (Spec (.of (q.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom)))))
    (toSP : B.obj hP ⟶ B.obj hS) (toSQ : B.obj hQ ⟶ B.obj hS)
    (r₁ r₂ : (Over.mk toS' : BigFppfOver B S hS) ⟶ Over.mk toSP)
    (s : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      squareZeroOver A B S hS toS ⟨ModuleCat.of A (RingHom.ker q), hI⟩ ⟶ Over.mk toSQ)
    (e : (Over.mk toSQ : BigFppfOver B S hS) ≅ Over.mk toSP)
    (er : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
      letI : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
      (q.pullback q) ≃+* q.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom))
    (hr₁ : B.inclusion.map r₁.left = Spec.map (CommRingCat.ofHom (q.pullbackFst q)))
    (hr₂ : B.inclusion.map r₂.left = Spec.map (CommRingCat.ofHom (q.pullbackSnd q)))
    (hs : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
      letI : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
      B.inclusion.map s.left = Spec.map (CommRingCat.ofHom
        (q.pullbackSnd ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom))))
    (he : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
      letI : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
      B.inclusion.map e.hom.left = Spec.map (CommRingCat.ofHom er.toRingHom))
    (her : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      letI : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
      letI : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
      ∀ y : q.pullback q, (er y).1.1 = y.1.1 ∧
        (er y).1.2 = ((q y.1.1, kerDifference q y) : TrivSqZeroExt A (RingHom.ker q))) :
    ∃ (kP : (BasedRing.prod (BasedRing.original RC) (BasedRing.original RC)).toAffine.siteOver ⟶
        Over.mk toSP)
      (kQ : (BasedRing.prod (BasedRing.original RC)
          (BasedRing.squareZero RC (BasedRing.kernelSite RC hqC hsqC))).toAffine.siteOver ⟶
        Over.mk toSQ),
      k ≫ r₁ = (BasedRing.fst (BasedRing.original RC) (BasedRing.original RC)).toHom.right ≫ kP ∧
      k ≫ r₂ = (BasedRing.snd (BasedRing.original RC) (BasedRing.original RC)).toHom.right ≫ kP ∧
      kI ≫ s = (BasedRing.snd (BasedRing.original RC)
        (BasedRing.squareZero RC (BasedRing.kernelSite RC hqC hsqC))).toHom.right ≫ kQ ∧
      kQ ≫ e.hom = (BasedRing.overIso RC (BasedRing.differenceMap RC hqC hsqC)
        (BasedRing.differenceEquiv RC hqC hsqC) rfl).hom ≫ kP := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
  let : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
  let : Module C (RingHom.ker RC.aug) := Stacks.Smooth.kerModule hqC hsqC
  let OC := BasedRing.original RC
  let PC := BasedRing.prod OC OC
  let WC := BasedRing.squareZero RC (BasedRing.kernelSite RC hqC hsqC)
  let QC := BasedRing.prod OC WC
  let erC := BasedRing.differenceEquiv RC hqC hsqC
  have hff' : ∀ a, RC.aug (f' a) = f (q a) := fun a => RingHom.congr_fun hff a
  let Pm : q.pullback q →+* RC.aug.pullback RC.aug :=
    ((f'.comp (q.pullbackFst q)).prod (f'.comp (q.pullbackSnd q))).codRestrict _ (fun y => by
      change RC.aug (f' y.1.1) = RC.aug (f' y.1.2)
      rw [hff', hff']
      exact congrArg f y.2)
  let Qm : q.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom) →+*
      OC.aug.pullback WC.aug :=
    ((f'.comp (q.pullbackFst _)).prod (eI.hom.comp (q.pullbackSnd _))).codRestrict _
      (fun y => by
        change RC.aug (f' y.1.1) = (eI.hom y.1.2).fst
        rw [hff', (heI y.1.2).1]
        exact congrArg f y.2)
  have hPQ : ∀ y, erC (Pm y) = Qm (er y) := by
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact ((squareZeroDifferenceEquiv RC.aug hqC hsqC).property (Pm y)).1.trans
        (congrArg f' (her y).1).symm
    · refine ((squareZeroDifferenceEquiv RC.aug hqC hsqC).property (Pm y)).2.trans
        (Eq.trans ?_ (congrArg eI.hom (her y).2).symm)
      apply TrivSqZeroExt.ext
      · exact (hff' _).trans (heI (q y.1.1, kerDifference q y)).1.symm
      · apply Subtype.ext
        exact (map_sub f' _ _).symm.trans (heI (q y.1.1, kerDifference q y)).2.symm
  have w₂ : B.inclusion.map r₂.left ≫ B.inclusion.map toSP = B.inclusion.map toS' :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w r₂))
  have w₁ : B.inclusion.map r₁.left ≫ B.inclusion.map toSP = B.inclusion.map toS' :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w r₁))
  have wk : B.inclusion.map k.left ≫ B.inclusion.map toS' =
      B.inclusion.map RC.structureMap :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w k))
  have we : B.inclusion.map e.hom.left ≫ B.inclusion.map toSP = B.inclusion.map toSQ :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w e.hom))
  have c₁ : B.inclusion.map (BasedRing.fst OC OC).toHom.right.left ≫
      B.inclusion.map PC.structureMap = B.inclusion.map RC.structureMap :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg B.inclusion.map (Over.w (BasedRing.fst OC OC).toHom.right))
  have c₂ : B.inclusion.map (BasedRing.snd OC OC).toHom.right.left ≫
      B.inclusion.map PC.structureMap = B.inclusion.map RC.structureMap :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg B.inclusion.map (Over.w (BasedRing.snd OC OC).toHom.right))
  have cQ : B.inclusion.map (BasedRing.overIso RC (BasedRing.differenceMap RC hqC hsqC)
        (BasedRing.differenceEquiv RC hqC hsqC) rfl).hom.left ≫
      B.inclusion.map PC.structureMap = B.inclusion.map QC.structureMap :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg B.inclusion.map (Over.w (BasedRing.overIso RC (BasedRing.differenceMap RC hqC hsqC)
        (BasedRing.differenceEquiv RC hqC hsqC) rfl).hom))
  have hpo := Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
    (CommRingCat.ofHom RC.aug) (CommRingCat.ofHom RC.aug)
    (CommRingCat.ofHom (RC.aug.pullbackFst RC.aug))
    (CommRingCat.ofHom (RC.aug.pullbackSnd RC.aug))
    (ringPullbackIsPullback RC.aug RC.aug) hqC
  have hkP : Spec.map (CommRingCat.ofHom Pm) ≫ B.inclusion.map toSP =
      B.inclusion.map PC.structureMap := by
    refine hpo.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ B.inclusion.map toSP)
        ((specMap_comp_eq Pm (RC.aug.pullbackSnd RC.aug) (q.pullbackSnd q) f'
          (fun _ => rfl)).trans (congrArg₂ (· ≫ ·) hk.symm hr₂.symm))).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (B.inclusion.map k.left ≫ ·) w₂).trans (wk.trans c₂.symm)
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ B.inclusion.map toSP)
        ((specMap_comp_eq Pm (RC.aug.pullbackFst RC.aug) (q.pullbackFst q) f'
          (fun _ => rfl)).trans (congrArg₂ (· ≫ ·) hk.symm hr₁.symm))).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (B.inclusion.map k.left ≫ ·) w₁).trans (wk.trans c₁.symm)
  have hkQ : Spec.map (CommRingCat.ofHom Qm) ≫ B.inclusion.map toSQ =
      B.inclusion.map QC.structureMap := by
    refine (congrArg (Spec.map (CommRingCat.ofHom Qm) ≫ ·) we.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ B.inclusion.map toSP) ((congrArg (Spec.map (CommRingCat.ofHom Qm) ≫ ·)
      he).trans (specMap_comp_eq er.toRingHom Qm Pm erC.toRingHom
        (fun z => (hPQ z).symm)))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (Spec.map (CommRingCat.ofHom erC.toRingHom) ≫ ·) hkP).trans cQ
  have hkI' : B.inclusion.map kI.left = Spec.map (CommRingCat.ofHom eI.hom) := hkI
  refine ⟨Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom Pm)))
      (ObjectProperty.hom_ext _ hkP),
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom Qm)))
      (ObjectProperty.hom_ext _ hkQ), ?_, ?_, ?_, ?_⟩
  · exact bigFppfOver_hom_ext _ _ ((congrArg₂ (· ≫ ·) hk hr₁).trans
      (specMap_comp_eq (q.pullbackFst q) f' Pm (RC.aug.pullbackFst RC.aug) (fun _ => rfl)))
  · exact bigFppfOver_hom_ext _ _ ((congrArg₂ (· ≫ ·) hk hr₂).trans
      (specMap_comp_eq (q.pullbackSnd q) f' Pm (RC.aug.pullbackSnd RC.aug) (fun _ => rfl)))
  · exact bigFppfOver_hom_ext _ _ ((congrArg₂ (· ≫ ·) hkI' hs).trans
      (specMap_comp_eq (q.pullbackSnd ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom))
        eI.hom Qm (OC.aug.pullbackSnd WC.aug) (fun _ => rfl)))
  · exact bigFppfOver_hom_ext _ _ ((congrArg (Spec.map (CommRingCat.ofHom Qm) ≫ ·) he).trans
      (specMap_comp_eq er.toRingHom Qm Pm erC.toRingHom (fun z => (hPQ z).symm)))

end RestrictedBase

section DeformationSituationMorphism

open CategoryTheory.Functor

variable {A C : Type u} [CommRing A] [CommRing C]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC} (φ₀ : y ⟶ x) {f : A →+* C}
  {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))} {toS' : B.obj hA' ⟶ B.obj hS}
  {q : A' →+* A} (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
  {gA : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)}
  {C' : Type u} [CommRing C'] {hC' : B.Contains (Spec (.of C'))}
  {toSC' : B.obj hC' ⟶ B.obj hS}
  {qC : C' →+* C} (hqC : Function.Surjective qC) (hsqC : RingHom.ker qC ^ 2 = ⊥)
  {gC : algebraOver C B S hS toSC hC ⟶ (Over.mk toSC' : BigFppfOver B S hS)}
  (hgC : B.inclusion.map gC.left = Spec.map (CommRingCat.ofHom qC))
  {f' : A' →+* C'} (hff : qC.comp f' = f.comp q)
  {k : (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk toS'}
  (hk : B.inclusion.map k.left = Spec.map (CommRingCat.ofHom f'))
  (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    IsSiteModule A B (ModuleCat.of A (RingHom.ker q)))
  (hJ : letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    IsSiteModule C B (ModuleCat.of C (RingHom.ker qC)))
  (eI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    squareZeroRing A (ModuleCat.of A (RingHom.ker q)) ⟶
      squareZeroRing C (ModuleCat.of C (RingHom.ker qC)))
  (heI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    ∀ z, (eI.hom z).fst = f z.fst ∧
      ((eI.hom z).snd : RingHom.ker qC).1 = f' (z.snd : RingHom.ker q).1)
  (kI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    squareZeroOver C B S hS toSC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ⟶
      squareZeroOver A B S hS toS ⟨ModuleCat.of A (RingHom.ker q), hI⟩)
  (hkI : B.inclusion.map kI.left = Spec.map eI)

include hp hgC hff hk heI hkI in
/-- **The infinitesimal difference transport restricts along a morphism of deformation
situations.** Let `(y, C' → C) ⟶ (x, A' → A)` be a morphism of deformation situations, let
`x'` be a lift of `x` over `A'` and `y'` a lift of `y` over `C'` with an arrow `y' ⟶ x'` over
`Spec C' ⟶ Spec A'`, and let `ρ` be an arrow from the trivial deformation of `y` over
`C[J]` to that of `x` over `A[I]`, over the morphism induced by `I ⟶ J`. If `α ∈ Inf(x'/x)` is
the difference transport of `αI ∈ Inf_x(I)`, then the restriction `α'` of `α` to `y'` is the
difference transport of the restriction `αI'` of `αI`. -/
public theorem IsGeometricInfDifference.restrict
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
    (y' : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC)))
    (φ : y'.1.right ⟶ x'.1.right) (hφ : p.IsHomLift k φ)
    (hφc : y'.1.hom ≫ φ = φ₀ ≫ x'.1.hom)
    (ρ : (letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      trivialDeformation C B S hS toSC hC p y hy hp
        ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩).1.right ⟶
      (letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      trivialDeformation A B S hS toS hA p x hx hp
        ⟨ModuleCat.of A (RingHom.ker q), hI⟩).1.right)
    (hρ : p.IsHomLift kI ρ)
    (hρc : (letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      trivialDeformation C B S hS toSC hC p y hy hp
        ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩).1.hom ≫ ρ =
      φ₀ ≫ (letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      trivialDeformation A B S hS toS hA p x hx hp
        ⟨ModuleCat.of A (RingHom.ker q), hI⟩).1.hom)
    (αI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      trivialDeformation A B S hS toS hA p x hx hp ⟨ModuleCat.of A (RingHom.ker q), hI⟩ ⟶
        trivialDeformation A B S hS toS hA p x hx hp ⟨ModuleCat.of A (RingHom.ker q), hI⟩)
    (αI' : letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      trivialDeformation C B S hS toSC hC p y hy hp
          ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ⟶
        trivialDeformation C B S hS toSC hC p y hy hp ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩)
    (hαI : αI'.1.right ≫ ρ = ρ ≫ αI.1.right)
    (α : x' ⟶ x') (α' : y' ⟶ y') (hα : α'.1.right ≫ φ = φ ≫ α.1.right)
    (h : IsGeometricInfDifference A B S hS toS hA p x hx hp A' hA' toS' q hq hsq gA hI x' αI α) :
    IsGeometricInfDifference C B S hS toSC hC p y hy hp C' hC' toSC' qC hqC hsqC gC hJ y' αI'
      α' := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
  obtain ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, v, w, φ₁, φ₂, ψ, ε, θ,
    hφ₁, hφ₂, hψ, hε, hc₁, hc₂, hθ, hθ₂, hα₁, hαI₁⟩ := h
  let RC : AffineDeformation C B S hS toSC hC := ⟨.of C', hC', toSC', qC, gC, hgC⟩
  let OC := BasedRing.original RC
  let PC := BasedRing.prod OC OC
  let WC := BasedRing.squareZero RC (BasedRing.kernelSite RC hqC hsqC)
  let QC := BasedRing.prod OC WC
  let eC := BasedRing.overIso RC (BasedRing.differenceMap RC hqC hsqC)
    (BasedRing.differenceEquiv RC hqC hsqC) rfl
  obtain ⟨kP₀, kQ₀, hkr₁₀, hkr₂₀, hks₀, hke₀⟩ := exists_restrictedDifferenceBase hq hsq RC hqC
    hsqC hff hk hI eI heI kI hkI hP hQ toSP toSQ r₁ r₂ s e er hr₁ hr₂ hs he her
  let r₁C : (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk PC.structureMap :=
    (BasedRing.fst OC OC).toHom.right
  let r₂C : (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk PC.structureMap :=
    (BasedRing.snd OC OC).toHom.right
  let sC : squareZeroOver C B S hS toSC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ⟶
      Over.mk QC.structureMap := (BasedRing.snd OC WC).toHom.right
  let eC' : (Over.mk QC.structureMap : BigFppfOver B S hS) ≅ Over.mk PC.structureMap := eC
  let kP : (Over.mk PC.structureMap : BigFppfOver B S hS) ⟶ Over.mk toSP := kP₀
  let kQ : (Over.mk QC.structureMap : BigFppfOver B S hS) ⟶ Over.mk toSQ := kQ₀
  have hkr₁ : k ≫ r₁ = r₁C ≫ kP := hkr₁₀
  have hkr₂ : k ≫ r₂ = r₂C ≫ kP := hkr₂₀
  have hks : kI ≫ s = sC ≫ kQ := hks₀
  have hke : kQ ≫ e.hom = eC'.hom ≫ kP := hke₀
  have hb₁ : gC ≫ r₂C = gC ≫ r₁C :=
    (Under.w (BasedRing.snd OC OC).toHom).trans (Under.w (BasedRing.fst OC OC).toHom).symm
  have hb₂ : squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ≫
      sC ≫ eC'.hom = gC ≫ r₂C :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eC.hom)
      (Under.w (BasedRing.snd OC WC).toHom)).trans
      ((Under.w (BasedRing.differenceMap RC hqC hsqC).toHom).trans
        (Under.w (BasedRing.snd OC OC).toHom).symm))
  let : p.IsFibered := hp.isFibered
  have := hφ
  have := hρ
  have := hφ₁.toIsHomLift
  have := hφ₂.toIsHomLift
  have := hψ.toIsHomLift
  have := hε.toIsHomLift
  have := hθ
  obtain ⟨vC, ρv, hρv⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.codomain_eq p r₂ φ₁) kP
  obtain ⟨wC, ρw, hρw⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.codomain_eq p s ψ) kQ
  have := hρv.toIsHomLift
  have := hρw.toIsHomLift
  have := hp.isStronglyCartesian_homLift kP ρv
  have := hp.isStronglyCartesian_homLift kQ ρw
  let φ₁C := IsStronglyCartesian.map p kP ρv hkr₂ (φ ≫ φ₁)
  let φ₂C := IsStronglyCartesian.map p kP ρv hkr₁ (φ ≫ φ₂)
  let εC := IsStronglyCartesian.map p kP ρv hke (ρw ≫ ε)
  have hρψ : p.IsHomLift (kI ≫ s) (ρ ≫ ψ) := IsHomLift.comp (p := p) kI s ρ ψ
  let ψC := IsStronglyCartesian.map p kQ ρw (f' := kI ≫ s) hks (ρ ≫ ψ)
  let θC := IsStronglyCartesian.map p kP ρv (Category.id_comp kP).symm (ρv ≫ θ)
  have f₁ : φ₁C ≫ ρv = φ ≫ φ₁ := IsStronglyCartesian.fac p kP ρv hkr₂ (φ ≫ φ₁)
  have f₂ : φ₂C ≫ ρv = φ ≫ φ₂ := IsStronglyCartesian.fac p kP ρv hkr₁ (φ ≫ φ₂)
  have fε : εC ≫ ρv = ρw ≫ ε := IsStronglyCartesian.fac p kP ρv hke (ρw ≫ ε)
  have fψ : ψC ≫ ρw = ρ ≫ ψ := IsStronglyCartesian.fac p kQ ρw (f' := kI ≫ s) hks (ρ ≫ ψ)
  have fθ : θC ≫ ρv = ρv ≫ θ :=
    IsStronglyCartesian.fac p kP ρv (Category.id_comp kP).symm (ρv ≫ θ)
  have f₁' : ∀ {Z : X} (m : v ⟶ Z), φ₁C ≫ ρv ≫ m = φ ≫ φ₁ ≫ m := fun m => by
    rw [← Category.assoc, f₁, Category.assoc]
  have f₂' : ∀ {Z : X} (m : v ⟶ Z), φ₂C ≫ ρv ≫ m = φ ≫ φ₂ ≫ m := fun m => by
    rw [← Category.assoc, f₂, Category.assoc]
  have fε' : ∀ {Z : X} (m : v ⟶ Z), εC ≫ ρv ≫ m = ρw ≫ ε ≫ m := fun m => by
    rw [← Category.assoc, fε, Category.assoc]
  have fψ' : ∀ {Z : X} (m : w ⟶ Z), ψC ≫ ρw ≫ m = ρ ≫ ψ ≫ m := fun m => by
    rw [← Category.assoc, fψ, Category.assoc]
  have hφc' : ∀ {Z : X} (m : x'.1.right ⟶ Z), y'.1.hom ≫ φ ≫ m = φ₀ ≫ x'.1.hom ≫ m :=
    fun m => by rw [← Category.assoc, hφc, Category.assoc]
  have hρc' : ∀ {Z : X} (m : (trivialDeformation A B S hS toS hA p x hx hp
      ⟨ModuleCat.of A (RingHom.ker q), hI⟩).1.right ⟶ Z),
      (trivialDeformation C B S hS toSC hC p y hy hp
        ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩).1.hom ≫ ρ ≫ m =
      φ₀ ≫ (trivialDeformation A B S hS toS hA p x hx hp
        ⟨ModuleCat.of A (RingHom.ker q), hI⟩).1.hom ≫ m :=
    fun m => by rw [← Category.assoc, hρc, Category.assoc]
  have : p.IsHomLift r₂C φ₁C :=
    IsStronglyCartesian.map_isHomLift p kP ρv hkr₂ (φ ≫ φ₁)
  have : p.IsHomLift r₁C φ₂C :=
    IsStronglyCartesian.map_isHomLift p kP ρv hkr₁ (φ ≫ φ₂)
  have : p.IsHomLift eC'.hom εC := IsStronglyCartesian.map_isHomLift p kP ρv hke (ρw ≫ ε)
  have : p.IsHomLift sC ψC :=
    IsStronglyCartesian.map_isHomLift p kQ ρw (f' := kI ≫ s) hks (ρ ≫ ψ)
  have : p.IsHomLift (𝟙 (Over.mk PC.structureMap : BigFppfOver B S hS)) θC :=
    IsStronglyCartesian.map_isHomLift p kP ρv (Category.id_comp kP).symm (ρv ≫ θ)
  have := underFiber_isHomLift p hy gC y'
  have := underFiber_isHomLift p hy
    (squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩)
    (trivialDeformation C B S hS toSC hC p y hy hp ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩)
  have : p.IsHomLift (𝟙 (Over.mk toSC' : BigFppfOver B S hS)) α'.1.right :=
    underPost_isHomLift_right p (𝟙 _) α'.1 α'.2
  have : p.IsHomLift
      (𝟙 (squareZeroOver C B S hS toSC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩)) αI'.1.right :=
    underPost_isHomLift_right p (𝟙 _) αI'.1 αI'.2
  have sc₁ : p.IsStronglyCartesian r₂C φ₁C := hp.isStronglyCartesian_homLift r₂C φ₁C
  have sc₂ : p.IsStronglyCartesian r₁C φ₂C := hp.isStronglyCartesian_homLift r₁C φ₂C
  have scψ : p.IsStronglyCartesian sC ψC := hp.isStronglyCartesian_homLift sC ψC
  have scε : p.IsStronglyCartesian eC'.hom εC := hp.isStronglyCartesian_homLift eC'.hom εC
  have hθC : p.IsHomLift (𝟙 (Over.mk PC.structureMap : BigFppfOver B S hS)) θC := inferInstance
  refine ⟨PC.contains, QC.contains, PC.structureMap, QC.structureMap,
    r₁C, r₂C, sC, eC', BasedRing.differenceEquiv RC hqC hsqC,
    rfl, rfl, rfl, rfl, (squareZeroDifferenceEquiv qC hqC hsqC).property,
    vC, wC, φ₁C, φ₂C, ψC, εC, θC, sc₁, sc₂, scψ, scε, ?_, ?_, hθC, ?_, ?_, ?_⟩
  · have : p.IsHomLift (gC ≫ r₂C) (y'.1.hom ≫ φ₂C) :=
      isHomLift_congr p hb₁.symm _ inferInstance
    refine IsStronglyCartesian.ext p kP ρv (gC ≫ r₂C) ?_
    rw [Category.assoc, Category.assoc, f₁, f₂, hφc', hφc', hc₁]
  · have : p.IsHomLift (gC ≫ r₂C)
        ((trivialDeformation C B S hS toSC hC p y hy hp
          ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩).1.hom ≫ ψC ≫ εC) :=
      isHomLift_congr p hb₂ _ inferInstance
    refine IsStronglyCartesian.ext p kP ρv (gC ≫ r₂C) ?_
    simp only [Category.assoc]
    rw [fε, fψ', hρc', hc₂, f₁, hφc']
  · refine IsStronglyCartesian.ext p kP ρv r₁C ?_
    simp only [Category.assoc]
    rw [fθ, f₂', hθ₂, f₂]
  · refine IsStronglyCartesian.ext p kP ρv r₂C ?_
    simp only [Category.assoc]
    rw [f₁, fθ, f₁', ← Category.assoc α'.1.right, hα, Category.assoc, hα₁]
  · refine IsStronglyCartesian.ext p kP ρv
      (sC ≫ eC'.hom) ?_
    simp only [Category.assoc]
    rw [fε, fθ, fε', fψ', fψ', ← Category.assoc αI'.1.right, hαI, Category.assoc, hαI₁]


variable (specMap : algebraOver C B S hS toSC hC ⟶ algebraOver A B S hS toS hA)
  (hφ₀ : p.IsHomLift specMap φ₀) (hkA : specMap ≫ gA = gC ≫ k)
  (hkM : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    specMap ≫ squareZeroArrow A B S hS toS hA ⟨ModuleCat.of A (RingHom.ker q), hI⟩ =
      squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ≫ kI)

include hp hgC hff hk heI hkI hφ₀ hkM in
/-- **The difference of two lifts restricts along a morphism of deformation situations.** Let
`(y, C' → C) ⟶ (x, A' → A)` be a morphism of deformation situations, and let `a ∈ T_x(I)` and
`b ∈ T_y(J)` be such that `b` is the restriction of `a`: every restriction to `C[J]` of a lift
in the class `a` lies in the class `b`. If `a` is the difference of two classes `z₁`, `z₂` of
lifts of `x` over `A'`, then `b` is the difference of their restrictions to `C'`. -/
public theorem IsGeometricDifference.restrict
    (Tx : TangentFunctorData A B S hS toS hA p x hx)
    (Ty : TangentFunctorData C B S hS toSC hC p y hy)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (Tx.functor.obj ⟨ModuleCat.of A (RingHom.ker q), hI⟩ : Type _))
    (b : letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      (Ty.functor.obj ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ : Type _))
    (hab : ∀ (t : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (Under.post p).Fiber (Under.mk (eqToHom hx ≫
          squareZeroArrow A B S hS toS hA ⟨ModuleCat.of A (RingHom.ker q), hI⟩)))
      (t' : letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
      (Under.post p).Fiber (Under.mk (eqToHom hy ≫
          squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩)))
      (ρ : t'.1.right ⟶ t.1.right), p.IsHomLift kI ρ → t'.1.hom ≫ ρ = φ₀ ≫ t.1.hom →
      Quotient.mk _ t = Tx.liftEquiv _ a → Quotient.mk _ t' = Ty.liftEquiv _ b)
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx gA)
    (h : IsGeometricDifference A B S hS toS hA p x hx Tx A' hA' toS' q hq hsq gA hI z₁ z₂ a) :
    IsGeometricDifference C B S hS toSC hC p y hy Ty C' hC' toSC' qC hqC hsqC gC hJ
      (liftClassesRestrict p hp φ₀ specMap hφ₀ hkA z₁)
      (liftClassesRestrict p hp φ₀ specMap hφ₀ hkA z₂) b := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
  obtain ⟨hP, hQ, toSP, toSQ, r₁, r₂, s, e, er, hr₁, hr₂, hs, he, her, t₁, t₂, t, v, w,
    φ₁, φ₂, ψ, ε, ht₁, ht₂, ht, hφ₁, hφ₂, hψ, hε, hc₁, hc₂⟩ := h
  obtain ⟨t₁', φt₁, hφt₁, hct₁⟩ := exists_liftRestriction p hp φ₀ specMap hφ₀ hkA t₁
  obtain ⟨t₂', φt₂, hφt₂, hct₂⟩ := exists_liftRestriction p hp φ₀ specMap hφ₀ hkA t₂
  obtain ⟨t', ρt, hρt, hct⟩ := exists_liftRestriction p hp φ₀ specMap hφ₀ hkM t
  let RC : AffineDeformation C B S hS toSC hC := ⟨.of C', hC', toSC', qC, gC, hgC⟩
  let OC := BasedRing.original RC
  let PC := BasedRing.prod OC OC
  let WC := BasedRing.squareZero RC (BasedRing.kernelSite RC hqC hsqC)
  let QC := BasedRing.prod OC WC
  let eC := BasedRing.overIso RC (BasedRing.differenceMap RC hqC hsqC)
    (BasedRing.differenceEquiv RC hqC hsqC) rfl
  obtain ⟨kP₀, kQ₀, hkr₁₀, hkr₂₀, hks₀, hke₀⟩ := exists_restrictedDifferenceBase hq hsq RC hqC
    hsqC hff hk hI eI heI kI hkI hP hQ toSP toSQ r₁ r₂ s e er hr₁ hr₂ hs he her
  let r₁C : (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk PC.structureMap :=
    (BasedRing.fst OC OC).toHom.right
  let r₂C : (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk PC.structureMap :=
    (BasedRing.snd OC OC).toHom.right
  let sC : squareZeroOver C B S hS toSC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ⟶
      Over.mk QC.structureMap := (BasedRing.snd OC WC).toHom.right
  let eC' : (Over.mk QC.structureMap : BigFppfOver B S hS) ≅ Over.mk PC.structureMap := eC
  let kP : (Over.mk PC.structureMap : BigFppfOver B S hS) ⟶ Over.mk toSP := kP₀
  let kQ : (Over.mk QC.structureMap : BigFppfOver B S hS) ⟶ Over.mk toSQ := kQ₀
  have hkr₁ : k ≫ r₁ = r₁C ≫ kP := hkr₁₀
  have hkr₂ : k ≫ r₂ = r₂C ≫ kP := hkr₂₀
  have hks : kI ≫ s = sC ≫ kQ := hks₀
  have hke : kQ ≫ e.hom = eC'.hom ≫ kP := hke₀
  have hb₁ : gC ≫ r₂C = gC ≫ r₁C :=
    (Under.w (BasedRing.snd OC OC).toHom).trans (Under.w (BasedRing.fst OC OC).toHom).symm
  have hb₂ : squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩ ≫
      sC ≫ eC'.hom = gC ≫ r₂C :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eC.hom)
      (Under.w (BasedRing.snd OC WC).toHom)).trans
      ((Under.w (BasedRing.differenceMap RC hqC hsqC).toHom).trans
        (Under.w (BasedRing.snd OC OC).toHom).symm))
  let : p.IsFibered := hp.isFibered
  have := hφt₁
  have := hφt₂
  have := hρt
  have := hφ₁.toIsHomLift
  have := hφ₂.toIsHomLift
  have := hψ.toIsHomLift
  have := hε.toIsHomLift
  obtain ⟨vC, ρv, hρv⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.codomain_eq p r₂ φ₁) kP
  obtain ⟨wC, ρw, hρw⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.codomain_eq p s ψ) kQ
  have := hρv.toIsHomLift
  have := hρw.toIsHomLift
  have := hp.isStronglyCartesian_homLift kP ρv
  have := hp.isStronglyCartesian_homLift kQ ρw
  have hρψ : p.IsHomLift (kI ≫ s) (ρt ≫ ψ) := IsHomLift.comp (p := p) kI s ρt ψ
  let φ₁C := IsStronglyCartesian.map p kP ρv hkr₂ (φt₁ ≫ φ₁)
  let φ₂C := IsStronglyCartesian.map p kP ρv hkr₁ (φt₂ ≫ φ₂)
  let εC := IsStronglyCartesian.map p kP ρv hke (ρw ≫ ε)
  let ψC := IsStronglyCartesian.map p kQ ρw (f' := kI ≫ s) hks (ρt ≫ ψ)
  have f₁ : φ₁C ≫ ρv = φt₁ ≫ φ₁ := IsStronglyCartesian.fac p kP ρv hkr₂ (φt₁ ≫ φ₁)
  have f₂ : φ₂C ≫ ρv = φt₂ ≫ φ₂ := IsStronglyCartesian.fac p kP ρv hkr₁ (φt₂ ≫ φ₂)
  have fε : εC ≫ ρv = ρw ≫ ε := IsStronglyCartesian.fac p kP ρv hke (ρw ≫ ε)
  have fψ : ψC ≫ ρw = ρt ≫ ψ := IsStronglyCartesian.fac p kQ ρw (f' := kI ≫ s) hks (ρt ≫ ψ)
  have : p.IsHomLift r₂C φ₁C := IsStronglyCartesian.map_isHomLift p kP ρv hkr₂ (φt₁ ≫ φ₁)
  have : p.IsHomLift r₁C φ₂C := IsStronglyCartesian.map_isHomLift p kP ρv hkr₁ (φt₂ ≫ φ₂)
  have : p.IsHomLift eC'.hom εC := IsStronglyCartesian.map_isHomLift p kP ρv hke (ρw ≫ ε)
  have : p.IsHomLift sC ψC :=
    IsStronglyCartesian.map_isHomLift p kQ ρw (f' := kI ≫ s) hks (ρt ≫ ψ)
  have := underFiber_isHomLift p hy gC t₁'
  have := underFiber_isHomLift p hy gC t₂'
  have := underFiber_isHomLift p hy
    (squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), hJ⟩) t'
  have sc₁ : p.IsStronglyCartesian r₂C φ₁C := hp.isStronglyCartesian_homLift r₂C φ₁C
  have sc₂ : p.IsStronglyCartesian r₁C φ₂C := hp.isStronglyCartesian_homLift r₁C φ₂C
  have scψ : p.IsStronglyCartesian sC ψC := hp.isStronglyCartesian_homLift sC ψC
  have scε : p.IsStronglyCartesian eC'.hom εC := hp.isStronglyCartesian_homLift eC'.hom εC
  refine ⟨PC.contains, QC.contains, PC.structureMap, QC.structureMap,
    r₁C, r₂C, sC, eC', BasedRing.differenceEquiv RC hqC hsqC,
    rfl, rfl, rfl, rfl, (squareZeroDifferenceEquiv qC hqC hsqC).property,
    t₁', t₂', t', vC, wC, φ₁C, φ₂C, ψC, εC, ?_, ?_, ?_, sc₁, sc₂, scψ, scε, ?_, ?_⟩
  · exact (liftClassesRestrict_mk p hp φ₀ specMap hφ₀ hkA t₁ t₁' φt₁ hφt₁ hct₁).symm.trans
      (congrArg _ ht₁)
  · exact (liftClassesRestrict_mk p hp φ₀ specMap hφ₀ hkA t₂ t₂' φt₂ hφt₂ hct₂).symm.trans
      (congrArg _ ht₂)
  · exact hab t t' ρt hρt hct ht
  · have : p.IsHomLift (gC ≫ r₂C) (t₂'.1.hom ≫ φ₂C) :=
      isHomLift_congr p hb₁.symm _ inferInstance
    refine IsStronglyCartesian.ext p kP ρv (gC ≫ r₂C) ?_
    rw [Category.assoc, Category.assoc, f₁, f₂, ← Category.assoc, hct₁, ← Category.assoc, hct₂,
      Category.assoc, Category.assoc, hc₁]
  · have : p.IsHomLift (gC ≫ r₂C) (t'.1.hom ≫ ψC ≫ εC) :=
      isHomLift_congr p hb₂ _ inferInstance
    refine IsStronglyCartesian.ext p kP ρv (gC ≫ r₂C) ?_
    simp only [Category.assoc]
    rw [fε, ← Category.assoc ψC, fψ, ← Category.assoc t'.1.hom, ← Category.assoc t'.1.hom, hct,
      Category.assoc, Category.assoc, hc₂, f₁, ← Category.assoc t₁'.1.hom, hct₁,
      Category.assoc]

end DeformationSituationMorphism

end Deformation.Artin

end
