module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality.TangentMap

/-!
# The zero of the infinitesimal invariants, and the tangent functor along a vertical isomorphism

The zero of `T_x(M)` and of `Inf_x(M)` as lift classes, injectivity of restriction of
endomorphisms along an invertible arrow, lifts transported along a vertical arrow, and the
`A`-linear map on tangent spaces induced by a vertical isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

namespace Deformation.Artin

/-! ### The zero of the infinitesimal invariants -/

section ZeroElement
open Functor
universe u v w

/-- A map of trivial square-zero extensions whose module map vanishes is the retraction
followed by the square-zero immersion: on rings, `(a, m) ↦ (a, 0)` factors through `A`. -/
public theorem squareZeroOverMap_eq_of_hom_apply_eq_zero (A : Type u) [CommRing A]
    (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {M N : SiteModule A B} (f : M ⟶ N) (hf : ∀ m : M.obj, f.hom.hom m = 0) :
    squareZeroOverMap A B S hS toS f =
      squareZeroRetraction A B S hS toS hA N ≫ squareZeroArrow A B S hS toS hA M := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A N.obj)) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp
  · simp [hf]

/-- The zero morphism of site modules has the zero linear map underneath it. -/
public theorem siteModule_zero_hom_apply (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (M N : SiteModule A B) (m : M.obj) : (0 : M ⟶ N).hom.hom m = 0 := rfl

/-- The map of trivial square-zero extensions induced by the zero module map is the retraction
followed by the square-zero immersion. -/
public theorem squareZeroOverMap_zero (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (M : SiteModule A B) :
    squareZeroOverMap A B S hS toS (0 : M ⟶ M) =
      squareZeroRetraction A B S hS toS hA M ≫ squareZeroArrow A B S hS toS hA M :=
  squareZeroOverMap_eq_of_hom_apply_eq_zero A B S hS toS hA (0 : M ⟶ M)
    (siteModule_zero_hom_apply A B M M)

/-- The square-zero immersion, read as a morphism of thickenings of `Spec A` under `x`. -/
public def liftBaseInclusion (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (_hp : p.IsFiberedInGroupoids)
    (M : SiteModule A B) :
    liftBaseId A B S hS toS hA p x hx ⟶ (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) :
      Under (p.obj x)) :=
  Under.homMk (squareZeroArrow A B S hS toS hA M) rfl

/-- The arrow of base thickenings induced by the zero module map factors through the trivial
thickening. -/
public theorem liftBaseThickeningMap_zero (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    liftBaseThickeningMap A B S hS toS hA p x hx (0 : M ⟶ M) =
      liftBaseSection A B S hS toS hA p x hx M ≫ liftBaseInclusion A B S hS toS hA p x hx hp M :=
  Under.UnderMorphism.ext (squareZeroOverMap_zero A B S hS toS hA M)

/-- The structure arrow of the trivial deformation, read as an arrow of lifts out of `x`
itself. -/
public def liftIdToTrivial (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    (liftId A B S hS toS hA p x hx).1 ⟶ (trivialDeformation A B S hS toS hA p x hx hp M).1 :=
  Under.homMk (trivialDeformation A B S hS toS hA p x hx hp M).1.hom (Category.id_comp _)

@[simp]
public theorem liftBaseInclusion_right (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    (liftBaseInclusion A B S hS toS hA p x hx hp M).right = squareZeroArrow A B S hS toS hA M := rfl

@[simp]
public theorem liftIdToTrivial_right (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    (liftIdToTrivial A B S hS toS hA p x hx hp M).right = (trivialDeformation A B S hS toS hA p x hx
      hp M).1.hom := rfl

/-- That arrow lies over the square-zero immersion. -/
public theorem liftIdToTrivial_isHomLift (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    (Under.post p).IsHomLift (liftBaseInclusion A B S hS toS hA p x hx hp M)
      (liftIdToTrivial A B S hS toS hA p x hx hp M) := by
  have hlift : p.IsHomLift (squareZeroArrow A B S hS toS hA M) (trivialDeformation A B S hS toS hA p
    x hx hp M).1.hom :=
    underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA M) (trivialDeformation A B S hS toS
      hA p x hx hp M)
  refine IsHomLift.of_fac' (Under.post p) _ _ (liftId A B S hS toS hA p x hx).2 (trivialDeformation
    A B S hS toS hA p x hx hp M).2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Under.homMk_right,
    liftIdToTrivial_right, liftBaseInclusion_right]
  exact IsHomLift.fac' p (squareZeroArrow A B S hS toS hA M) (trivialDeformation A B S hS toS hA p x
    hx hp M).1.hom

/-- Composing that arrow with the chosen cartesian arrow of the trivial deformation gives the
identity: the retraction is a section of the structure arrow. -/
public theorem liftIdToTrivial_comp_trivialDeformationMap (A : Type u) [CommRing A]
    (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    liftIdToTrivial A B S hS toS hA p x hx hp M ≫ trivialDeformationMap A B S hS toS hA p x hx hp M
      = 𝟙 _ :=
  Under.UnderMorphism.ext (trivialRetract_fac A B S hS toS hA p x hx hp M)

/-- `x` has no nontrivial automorphisms as a lift of itself along the trivial thickening: the
structure arrow of that lift is the identity. -/
public theorem liftId_fiber_end_eq_id (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (_hp : p.IsFiberedInGroupoids)
    (η : liftId A B S hS toS hA p x hx ⟶ liftId A B S hS toS hA p x hx) : η = 𝟙 _ := by
  have h : (𝟙 x : x ⟶ x) ≫ η.1.right = (𝟙 x : x ⟶ x) := Under.w η.1
  exact Functor.Fiber.hom_ext (Under.UnderMorphism.ext
    ((Category.id_comp η.1.right).symm.trans h))

/-- Restriction of the identity endomorphism is the identity. -/
public theorem fiberEndRestrict_id_source {C : Type*} [Category C] {Y : Type*} [Category Y]
    (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids) {U V : C} {g : V ⟶ U} {a : q.Fiber U}
    {b : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) :
    fiberEndRestrict q hq φ hφ (𝟙 a) = 𝟙 b :=
  (fiberEndRestrict_eq q hq φ hφ (𝟙 a) (𝟙 b)
    ((Category.id_comp φ).trans (Category.comp_id φ).symm)).symm

/-- The transition arrow of the trivial deformations along the zero module map is the chosen
cartesian arrow down to `x` followed by the structure arrow back up. -/
public theorem trivialTransitionUnder_zero (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
      :
    trivialTransitionUnder A B S hS toS hA p x hx hp (0 : M ⟶ M) =
      trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA p x hx hp
        M := by
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  have hcartI := (trivialDeformationMap_isCartesian A B S hS toS hA p x hx hp M).toIsHomLift
  have hcart : (Under.post p).IsStronglyCartesian (liftBaseSection A B S hS toS hA p x hx M)
      (trivialDeformationMap A B S hS toS hA p x hx hp M) :=
    (underPost_isFiberedInGroupoids p hp x).isStronglyCartesian_homLift _ _
  have hfac : trivialTransitionUnder A B S hS toS hA p x hx hp (0 : M ⟶ M) ≫
      trivialDeformationMap A B S hS toS hA p x hx hp M = trivialDeformationMap A B S hS toS hA p x
        hx hp M :=
    Functor.pullbackFiberMap_fac (Under.post p) (liftId A B S hS toS hA p x hx)
      (liftBaseOverMap A B S hS toS hA p x hx (0 : M ⟶ M))
  have hl : (Under.post p).IsHomLift (liftBaseThickeningMap A B S hS toS hA p x hx (0 : M ⟶ M))
      (trivialTransitionUnder A B S hS toS hA p x hx hp (0 : M ⟶ M)) :=
    trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp (0 : M ⟶ M)
  have hr0 : (Under.post p).IsHomLift
      (liftBaseSection A B S hS toS hA p x hx M ≫ liftBaseInclusion A B S hS toS hA p x hx hp M)
      (trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA p x hx hp
        M) := by
    have := hcartI
    have := liftIdToTrivial_isHomLift A B S hS toS hA p x hx hp M
    infer_instance
  have hr : (Under.post p).IsHomLift (liftBaseThickeningMap A B S hS toS hA p x hx (0 : M ⟶ M))
      (trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA p x hx hp
        M) :=
    isHomLift_congr (Under.post p) (liftBaseThickeningMap_zero A B S hS toS hA p x hx hp M).symm _
      hr0
  have hcomp : (trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA
    p x hx hp M) ≫
      trivialDeformationMap A B S hS toS hA p x hx hp M = trivialDeformationMap A B S hS toS hA p x
        hx hp M := by
    rw [Category.assoc, liftIdToTrivial_comp_trivialDeformationMap, Category.comp_id]
  have := hl
  have := hr
  exact IsStronglyCartesian.ext (Under.post p) (liftBaseSection A B S hS toS hA p x hx M)
    (trivialDeformationMap A B S hS toS hA p x hx hp M)
    (liftBaseThickeningMap A B S hS toS hA p x hx (0 : M ⟶ M)) (hfac.trans hcomp.symm)

/-- **The transition map of `Inf_x` along the zero module map is trivial.** -/
public theorem infinitesimalAutomorphismSetFunctor_map_zero (A : Type u) [CommRing A]
    (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids) (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶ trivialDeformation A B S hS toS hA p x hx
      hp M) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map (0 : M ⟶ M) θ = 𝟙 _ := by
  have h0 := infAutSetFunctor_map_eq A B S hS toS hA p x hx hp (0 : M ⟶ M) θ
  have h1 : fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
      (trivialTransitionUnder A B S hS toS hA p x hx hp (0 : M ⟶ M))
      (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp (0 : M ⟶ M)) θ = 𝟙 _ := by
    have hψ := (trivialDeformationMap_isCartesian A B S hS toS hA p x hx hp M).toIsHomLift
    have hφ := liftIdToTrivial_isHomLift A B S hS toS hA p x hx hp M
    have hψφ : (Under.post p).IsHomLift
        (liftBaseSection A B S hS toS hA p x hx M ≫ liftBaseInclusion A B S hS toS hA p x hx hp M)
        (trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA p x hx
          hp M) := by
      have := hψ
      have := hφ
      infer_instance
    have hstep : fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
        (trivialDeformationMap A B S hS toS hA p x hx hp M ≫ liftIdToTrivial A B S hS toS hA p x hx
          hp M) hψφ θ =
          fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
            (trivialDeformationMap A B S hS toS hA p x hx hp M) hψ
            (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
              (liftIdToTrivial A B S hS toS hA p x hx hp M) hφ θ) :=
      fiberEndRestrict_comp (Under.post p) (underPost_isFiberedInGroupoids p hp x)
        (liftIdToTrivial A B S hS toS hA p x hx hp M) hφ (trivialDeformationMap A B S hS toS hA p x
          hx hp M) hψ hψφ θ
    have hid := liftId_fiber_end_eq_id A B S hS toS hA p x hx hp
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
        (liftIdToTrivial A B S hS toS hA p x hx hp M) hφ θ)
    rw [hid] at hstep
    rw [fiberEndRestrict_id_source] at hstep
    refine Eq.trans (fiberEndRestrict_congr (Under.post p)
      (underPost_isFiberedInGroupoids p hp x) _ _
      (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp (0 : M ⟶ M)) hψφ
      (trivialTransitionUnder_zero A B S hS toS hA p x hx hp M) θ) hstep
  exact h0.trans h1

/-- **The zero of `Inf_x(M)` is the identity automorphism of the trivial deformation.** -/
public theorem autEquiv_zero (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp) (M : SiteModule A B) :
    Inf.autEquiv M 0 = 𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) := by
  have hmap : Inf.functor.map (0 : M ⟶ M) = 0 := Inf.functor.map_zero M M
  have hz : Inf.functor.map (0 : M ⟶ M) (0 : Inf.functor.obj M) = 0 := by
    rw [hmap]; simp
  have hnat := Inf.autEquiv_natural (0 : M ⟶ M) (0 : Inf.functor.obj M)
  rw [hz] at hnat
  rw [hnat]
  exact infinitesimalAutomorphismSetFunctor_map_zero A B S hS toS hA p x hx hp M (Inf.autEquiv M 0)

/-- **The zero of `T_x(M)` is the class of the trivial deformation.** -/
public theorem liftEquiv_zero (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
    (T : TangentFunctorData A B S hS toS hA p x hx) (M : SiteModule A B) :
    T.liftEquiv M 0 = Quotient.mk _ (trivialDeformation A B S hS toS hA p x hx hp M) := by
  have hmap : T.functor.map (0 : M ⟶ M) = 0 := T.functor.map_zero M M
  have hz : T.functor.map (0 : M ⟶ M) (0 : T.functor.obj M) = 0 := by
    rw [hmap]; simp
  have hnat := T.liftEquiv_natural (0 : M ⟶ M) (0 : T.functor.obj M)
  rw [hz] at hnat
  obtain ⟨a', ha'⟩ := Quotient.exists_rep (T.liftEquiv M 0)
  have hpb : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx (0 : M ⟶ M) (T.liftEquiv M 0)
      (Quotient.mk _ (trivialDeformation A B S hS toS hA p x hx hp M)) := by
    refine ⟨a', trivialDeformation A B S hS toS hA p x hx hp M, ha', rfl,
      trivialRetract A B S hS toS hA p x hx hp M ≫ a'.1.hom, ?_, ?_⟩
    · have h1 := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
      have h2 := underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA M) a'
      have hcomp : p.IsHomLift (squareZeroRetraction A B S hS toS hA M ≫ squareZeroArrow A B S hS
        toS hA M)
          (trivialRetract A B S hS toS hA p x hx hp M ≫ a'.1.hom) := by
        have := h1
        have := h2
        infer_instance
      have hcomp' : p.IsHomLift (squareZeroOverMap A B S hS toS (0 : M ⟶ M))
          (trivialRetract A B S hS toS hA p x hx hp M ≫ a'.1.hom) :=
        isHomLift_congr p (squareZeroOverMap_zero A B S hS toS hA M).symm _ hcomp
      have := hcomp'
      exact hp.isStronglyCartesian_homLift _ _
    · rw [← Category.assoc, trivialRetract_fac, Category.id_comp]
  exact isPullbackOfSquareZeroLift_unique A B S hS toS hA p x hx hp (0 : M ⟶ M) hnat hpb

end ZeroElement

/-! ### Injectivity of restriction of endomorphisms along an invertible arrow -/

section FiberEndInjective
open Functor
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {Y : Type u₂} [Category.{v₂} Y]

/-- **Restriction of endomorphisms along an invertible arrow is injective.**  The defining
square of `Deformation.Artin.fiberEndRestrict` reads the restricted endomorphism against the
original one through that arrow, so cancelling the arrow recovers the original. -/
public theorem fiberEndRestrict_injective_of_isIso (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)
    {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (hiso : IsIso φ) :
    Function.Injective (fiberEndRestrict q hq φ hφ) := by
  have := hiso
  intro θ θ' hθ
  apply Functor.Fiber.hom_ext
  have e1 := fiberEndRestrict_fac q hq φ hφ θ
  have e2 := fiberEndRestrict_fac q hq φ hφ θ'
  rw [hθ] at e1
  exact (cancel_epi φ).mp (e1.symm.trans e2)

/-- Exactness of `0 ⟶ M₁ ⟶ M₂` is injectivity: `Function.Exact 0 g` says that the kernel of
`g` is the image of the zero map. -/
public theorem exact_zero_iff_injective {R : Type*} [Semiring R] {M₁ : Type*} {M₂ : Type*}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (hg : Function.Injective g) :
    Function.Exact (0 : M₁ →ₗ[R] M₁) g := by
  intro b
  refine ⟨fun hb => ⟨0, ?_⟩, ?_⟩
  · have hb0 : b = 0 := hg (hb.trans (map_zero g).symm)
    simp [hb0]
  · rintro ⟨a, ha⟩
    rw [← ha]
    simp

end FiberEndInjective

/-! ### Lifts transported along a vertical arrow -/

section UnderFiberTransport
open Functor
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]

/-- A lift of `y₂` under `a`, read through a vertical arrow `ι : y₁ ⟶ y₂`, is a lift of `y₁`
under `a`: the underlying object of `X` is untouched and only the structure arrow changes, by
precomposition with `ι`. -/
public theorem underMap_mem_fiber (p : X ⥤ C) {U V : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a))) :
    (Under.post p).obj ((Under.map ι).obj t.1) = Under.mk (eqToHom hy₁ ≫ a) := by
  have := hι
  have := underFiber_isHomLift p hy₂ a t
  refine StructuredArrow.obj_ext _ _ (underFiber_right_obj p hy₂ a t) ?_
  change p.map (ι ≫ t.1.hom) ≫ eqToHom (underFiber_right_obj p hy₂ a t) = eqToHom hy₁ ≫ a
  rw [p.map_comp, IsHomLift.fac' p (𝟙 U) ι, IsHomLift.fac' p a t.1.hom]
  simp

/-- **Transport of lifts along a vertical arrow.**  Precomposition of the structure arrow with
`ι : y₁ ⟶ y₂` carries lifts of `y₂` under `a` to lifts of `y₁` under `a`.  This is the
comparison the six-term sequence of Stacks 0DNN needs, and it is built here from
`CategoryTheory.Under.map`, which leaves every object and every arrow of `X` alone. -/
public def underFiberTransport (p : X ⥤ C) {U V : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) :
    (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a)) ⥤
      (Under.post p).Fiber (Under.mk (eqToHom hy₁ ≫ a)) where
  obj t := ⟨(Under.map ι).obj t.1, underMap_mem_fiber p hy₁ hy₂ ι hι a t⟩
  map {s t} m := ⟨(Under.map ι).map m.1, by
    have h₀ : p.IsHomLift (𝟙 V) m.1.right :=
      underPost_isHomLift_right p (𝟙 (Under.mk (eqToHom hy₂ ≫ a))) m.1 m.2
    refine IsHomLift.of_fac' (Under.post p) (𝟙 _) _
      (underMap_mem_fiber p hy₁ hy₂ ι hι a s) (underMap_mem_fiber p hy₁ hy₂ ι hι a t) ?_
    apply Under.UnderMorphism.ext
    simp only [Under.comp_right, Under.eqToHom_right, Under.id_right, Under.post_map,
      Under.homMk_right, Under.map_map_right]
    exact IsHomLift.fac' p (𝟙 V) m.1.right⟩
  map_id t := Functor.Fiber.hom_ext ((Under.map ι).map_id t.1)
  map_comp m n := Functor.Fiber.hom_ext ((Under.map ι).map_comp m.1 n.1)

@[simp]
public theorem underFiberTransport_obj (p : X ⥤ C) {U V : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a))) :
    ((underFiberTransport p hy₁ hy₂ ι hι a).obj t).1 = (Under.map ι).obj t.1 := rfl

/-- The structure arrow of a transported lift is the original one precomposed with `ι`. -/
@[simp]
public theorem underFiberTransport_obj_hom (p : X ⥤ C) {U V : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a))) :
    ((underFiberTransport p hy₁ hy₂ ι hι a).obj t).1.hom = ι ≫ t.1.hom := rfl

@[simp]
public theorem underFiberTransport_map (p : X ⥤ C) {U V : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) {s t : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a))} (m : s ⟶ t) :
    ((underFiberTransport p hy₁ hy₂ ι hι a).map m).1 = (Under.map ι).map m.1 := rfl

/-- A transported arrow of lifts lying over an arrow of base thickenings lies over the
corresponding arrow of base thickenings of `y₁`. -/
public theorem underMap_map_isHomLift (p : X ⥤ C) {U V W : C} {y₁ y₂ : X}
    (hy₁ : p.obj y₁ = U) (hy₂ : p.obj y₂ = U) (ι : y₁ ⟶ y₂) (hι : p.IsHomLift (𝟙 U) ι)
    (a : U ⟶ V) (a' : U ⟶ W) (g : V ⟶ W)
    (hcomm : (eqToHom hy₁ ≫ a) ≫ g = eqToHom hy₁ ≫ a')
    (s : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a)))
    (t : (Under.post p).Fiber (Under.mk (eqToHom hy₂ ≫ a')))
    (m : s.1 ⟶ t.1) (hm : p.IsHomLift g m.right) :
    (Under.post p).IsHomLift
      (Under.homMk g hcomm :
        (Under.mk (eqToHom hy₁ ≫ a) : Under (p.obj y₁)) ⟶ Under.mk (eqToHom hy₁ ≫ a'))
      ((Under.map ι).map m) := by
  have := hm
  refine IsHomLift.of_fac' (Under.post p) _ _
    (underMap_mem_fiber p hy₁ hy₂ ι hι a s)
    (underMap_mem_fiber p hy₁ hy₂ ι hι a' t) ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Under.homMk_right,
    Under.map_map_right]
  exact IsHomLift.fac' p g m.right

end UnderFiberTransport


/-! ### The tangent functor along a vertical isomorphism -/

section TransportTangent
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) (y₁ y₂ : Y)
  (hy₁ : p.obj y₁ = algebraOver A B S hS toS hA)
  (hy₂ : p.obj y₂ = algebraOver A B S hS toS hA)
  (ι : y₁ ≅ y₂) (hι : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.hom)

/-- **Transport of lifts over the trivial square-zero extension along a vertical
isomorphism.** -/
public def squareZeroLiftTransport (M : SiteModule A B) :
    (Under.post p).Fiber
        (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₂)) ⥤
      (Under.post p).Fiber
        (Under.mk (eqToHom hy₁ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₁)) :=
  underFiberTransport p hy₁ hy₂ ι.hom hι (squareZeroArrow A B S hS toS hA M)

/-- The induced map on lift classes. -/
public def liftClassOfTransport (M : SiteModule A B) :
    squareZeroLiftClasses A B S hS toS hA p y₂ hy₂ M →
      squareZeroLiftClasses A B S hS toS hA p y₁ hy₁ M :=
  isoClassMap (squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M)

public theorem liftClassOfTransport_mk (M : SiteModule A B)
    (t : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₂))) :
    liftClassOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M (Quotient.mk _ t) =
      Quotient.mk _ ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj t) :=
  rfl

/-- Transport carries a pullback of lifts to a pullback of lifts: the cartesian arrow is
literally the same arrow of `Y`, only the structure arrows change. -/
public theorem isPullbackOfSquareZeroLift_transport {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p y₂ hy₂ M)
    (b : squareZeroLiftClasses A B S hS toS hA p y₂ hy₂ N)
    (h : IsPullbackOfSquareZeroLift A B S hS toS hA p y₂ hy₂ f a b) :
    IsPullbackOfSquareZeroLift A B S hS toS hA p y₁ hy₁ f
      (liftClassOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M a)
      (liftClassOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι N b) := by
  obtain ⟨a', b', ha', hb', φ, hc, hw⟩ := h
  refine ⟨(squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj a',
    (squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι N).obj b', ?_, ?_, φ, hc, ?_⟩
  · rw [← ha']; rfl
  · rw [← hb']; rfl
  · change (ι.hom ≫ b'.1.hom) ≫ φ = ι.hom ≫ a'.1.hom
    rw [Category.assoc, hw]

variable (T₂ : TangentFunctorData A B S hS toS hA p y₂ hy₂)
  (T₁ : TangentFunctorData A B S hS toS hA p y₁ hy₁)

/-- **The map `T_{y₂}(M) ⟶ T_{y₁}(M)` induced by a vertical isomorphism `y₁ ≅ y₂`**: the map
on lift classes read through the two defining bijections. -/
public def tangentMapOfTransport (M : SiteModule A B) : T₂.functor.obj M → T₁.functor.obj M :=
  fun z => (T₁.liftEquiv M).symm
    (liftClassOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M (T₂.liftEquiv M z))

public theorem liftEquiv_tangentMapOfTransport (M : SiteModule A B) (z : T₂.functor.obj M) :
    T₁.liftEquiv M
        (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M z) =
      liftClassOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M (T₂.liftEquiv M z) :=
  (T₁.liftEquiv M).apply_symm_apply _

/-- The induced map is natural in the coordinate module. -/
public theorem tangentMapOfTransport_natural (hp : p.IsFiberedInGroupoids)
    {M N : SiteModule A B} (f : M ⟶ N) (z : T₂.functor.obj M) :
    tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ N (T₂.functor.map f z) =
      T₁.functor.map f
        (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M z) := by
  apply (T₁.liftEquiv N).injective
  rw [liftEquiv_tangentMapOfTransport]
  have h2 := isPullbackOfSquareZeroLift_transport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι f
    (T₂.liftEquiv M z) (T₂.liftEquiv N (T₂.functor.map f z)) (T₂.liftEquiv_natural f z)
  have h3 := T₁.liftEquiv_natural f
    (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M z)
  rw [liftEquiv_tangentMapOfTransport] at h3
  exact isPullbackOfSquareZeroLift_unique A B S hS toS hA p y₁ hy₁ hp f h2 h3

/-- **The map induced on tangent functors by a vertical isomorphism is `A`-linear.** -/
public theorem isLinearMap_tangentMapOfTransport (hp : p.IsFiberedInGroupoids)
    (M : SiteModule A B) :
    IsLinearMap A (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M) :=
  isLinearMap_of_natural_siteModule A B hA T₂.functor T₁.functor
    (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁)
    (fun g z => tangentMapOfTransport_natural A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ hp g z)
    M

/-- The map `T_{y₂}(M) ⟶ T_{y₁}(M)` induced by a vertical isomorphism, as an `A`-linear
map. -/
public def tangentLinearMapOfTransport (hp : p.IsFiberedInGroupoids) (M : SiteModule A B) :
    T₂.functor.obj M →ₗ[A] T₁.functor.obj M :=
  IsLinearMap.mk' (tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M)
    (isLinearMap_tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ hp M)

@[simp]
public theorem tangentLinearMapOfTransport_apply (hp : p.IsFiberedInGroupoids)
    (M : SiteModule A B) (z : T₂.functor.obj M) :
    tangentLinearMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ hp M z =
      tangentMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι T₂ T₁ M z := rfl

end TransportTangent

end Deformation.Artin

end
