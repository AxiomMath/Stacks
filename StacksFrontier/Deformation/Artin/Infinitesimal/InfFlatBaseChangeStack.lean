module

public import StacksFrontier.Deformation.Artin.Infinitesimal.InfIsomSections
public import StacksFrontier.Deformation.Artin.Infinitesimal.ElementsLiftClasses
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismSpaceStack
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Flat base change for the infinitesimal automorphisms of an algebraic stack (Stacks 0DNR)

Let `𝒳` be an algebraic stack over `S` whose inertia `ℐ_𝒳 ⟶ 𝒳` is locally of finite presentation,
`A → C` a flat homomorphism of `S`-algebras, `x` an object of `𝒳` over `Spec A` and `y = x|_C`.
Then `Inf_x(M) ⊗_A C = Inf_y(M ⊗_A C)`, the identification being induced by the map of
Stacks 07YA (`Deformation.Artin.infBaseChangeMap`).

## The argument

The source writes `Inf_x(M) = Hom_A(e^*Ω_{G/A}, M)` for the automorphism group algebraic space
`G` of `x` over `Spec A` and argues with the sheaf of differentials of `G`. Here the same group
space `G = Isom(x, x)` is used, but the conclusion is read off flat base change for *tangent*
spaces, which this development has for any algebraic stack locally of finite presentation over
its base (Stacks 0DNT, `Deformation.Artin.exists_tangentFlatBaseChange`):

1. `G` is an algebraic space over `Spec A`, locally of finite presentation because the inertia is
   (`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_autSpace`); its category of elements
   is an algebraic stack over the base scheme `Spec A`, locally of finite presentation over it
   (`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_spaceToBase`).
2. The identity `e` of `x` is a point of `G` over `Spec A`, and its tangent space at `M` is the set
   of sections of `G` over `Spec A[M]` restricting to `e`, which is `Inf_x(M)`
   (`Deformation.Artin.infIsomEquiv`, `Deformation.Artin.elemLiftClassEquiv`); likewise the
   restriction `e_C` of `e` to `Spec C` has tangent space `Inf_y`. Transporting the linear
   structures of `Inf_x` and `Inf_y` along these bijections gives tangent functors of `G` at `e`
   and `e_C` in the sense of Stacks 07Y9 (`Deformation.Artin.tangentDataOfInf`).
3. Stacks 0DNT for `G` gives `C ⊗_A T_e(M) ≅ T_{e_C}(C ⊗_A M)` induced by restriction of
   sections along `Spec C[C ⊗_A M] ⟶ Spec A[M]`, and that restriction is the map of Stacks 07YA on
   infinitesimal automorphisms (`Deformation.Artin.morRestrict_infIsomSec`).

No Kähler differentials of algebraic spaces enter: the finiteness the source extracts from
Stacks 05ZF is that of `G` over `Spec A`, which is exactly what Stacks 0DNT consumes.

## Main results

* `Deformation.Artin.tangentDataOfInf`: the tangent functor of the automorphism space at a point,
  built from the infinitesimal automorphisms.
* `Deformation.Artin.exists_infFlatBaseChange_of_inertia`: **Stacks 0DNR**.

## References

* [Stacks Project, Tag 0DNR](https://stacks.math.columbia.edu/tag/0DNR)
* [Stacks Project, Tag 0DNT](https://stacks.math.columbia.edu/tag/0DNT)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Stack
open scoped TensorProduct

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- The `ULift` functor on modules is linear. -/
instance moduleCatUliftFunctor_linear (R : Type u) [CommRing R] :
    (ModuleCat.uliftFunctor.{w, u} R).Linear R where
  map_smul _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

section TangentOfInf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{u} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [p.IsFibered]
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : X} (hx : p.obj x = algebraOver A B S hS toS hA)

/-- The automorphism presheaf `Mor(x, x)` of `x`, on the big fppf site of `Spec A`. -/
abbrev autPresheaf : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u :=
  (Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).op ⋙
    p.morPresheaf (fiberPt p hx) (fiberPt p hx)

variable {D : Type u} [CommRing D] {toSD : Spec (.of D) ⟶ S} {hD : B.Contains (Spec (.of D))}
  (toSD₀ : Spec (.of D) ⟶ Spec (.of A))
  (s : algebraOver D B S hS toSD hD ⟶ algebraOver A B S hS toS hA)
  (hs : s.left = ObjectProperty.homMk toSD₀)
  {x' : X} (hx' : p.obj x' = algebraOver D B S hS toSD hD) (φ' : x' ⟶ x) [p.IsHomLift s φ']

/-- The identity of `x` over `Spec D`, as a point of the automorphism space. -/
abbrev autPt : (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.obj :=
  elemObj (autPresheaf p hx) (algebraOver D B (Spec (.of A)) hA toSD₀ hD) (𝟙 _)

/-- **`Inf_{x'}(M)` is the set of lift classes of the identity in the automorphism space.** -/
def infLiftClassEquiv (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    (M : SiteModule D B) :
    (Dx.functor.obj M : Type u) ≃
      squareZeroLiftClasses D B (Spec (.of A)) hA toSD₀ hD
        (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.p (autPt p hx toSD₀)
        (elemObj_p_obj _ _ _) M :=
  (Dx.autEquiv M).trans ((infIsomEquiv p hp hx toSD₀ s hs hx' φ' M).trans
    (elemLiftClassEquiv (autPresheaf p hx) (𝟙 _)
      (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)).symm)

/-- Under `elemLiftClassEquiv`, the lift class attached to `t` in `Inf_{x'}(M)` is the section of
`Mor(x, x)` attached to the corresponding infinitesimal automorphism. -/
theorem elemLiftClassEquiv_infLiftClassEquiv
    (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    (M : SiteModule D B) (t : (Dx.functor.obj M : Type u)) :
    (elemLiftClassEquiv (autPresheaf p hx) (𝟙 _)
        (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)
        (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M t)).1 =
      infIsomSec p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t) := by
  simp [infLiftClassEquiv]

/-- The lift class attached to `t` in `Inf_{x'}(M)` is the class of the lift of the identity
given by the section of `Mor(x, x)` attached to the corresponding infinitesimal automorphism. -/
theorem infLiftClassEquiv_apply
    (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    (M : SiteModule D B) (t : (Dx.functor.obj M : Type u)) :
    infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M t =
      Quotient.mk _ (elemLift (autPresheaf p hx) (𝟙 _)
        (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)
        (infIsomSec p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t))
        (infIsomSec_restrict p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t)).symm) :=
  rfl

/-- The transition of `Inf_{x'}` along a module map restricts sections of the automorphism
space. -/
theorem infIsomSec_map (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    {M N : SiteModule D B} (f : M ⟶ N) (t : (Dx.functor.obj M : Type u)) :
    infIsomSec p hp hx toSD₀ s hs hx' φ' N (Dx.autEquiv N (Dx.functor.map f t)) =
      (autPresheaf p hx).map (squareZeroOverMap D B (Spec (.of A)) hA toSD₀ f).op
        (infIsomSec p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t)) := by
  rw [Dx.autEquiv_natural f t]
  have : (Under.post p : Under x' ⥤ Under (p.obj x')).IsFibered := underPost_isFibered p hp x'
  let k := (trivialTransitionUnder D B S hS toSD hD p x' hx' hp f).right
  have : p.IsHomLift (squareZeroOverMap D B S hS toSD f) k :=
    underPost_isHomLift_right p _ _
      (trivialTransitionUnder_isHomLift D B S hS toSD hD p x' hx' hp f)
  have hk : k ≫ infRetract p hp hx' φ' M = infRetract p hp hx' φ' N := by
    have h := congrArg Under.Hom.right (Functor.pullbackFiberMap_fac (Under.post p)
      (liftId D B S hS toSD hD p x' hx') (liftBaseOverMap D B S hS toSD hD p x' hx' f))
    simp only [Under.comp_right] at h
    change k ≫ trivialRetract D B S hS toSD hD p x' hx' hp M ≫ φ' =
      trivialRetract D B S hS toSD hD p x' hx' hp N ≫ φ'
    rw [← Category.assoc]
    exact congrArg (· ≫ φ') h
  refine (morRestrict_infIsomSec p hp hx toSD₀ s hs hx' φ' toSD₀ s hs hx' φ' N M
    (squareZeroOverMap D B (Spec (.of A)) hA toSD₀ f) (squareZeroOverMap D B S hS toSD f) rfl k hk
    _ _ ?_).symm
  rw [infinitesimalAutomorphismSetFunctor_map D B S hS toSD hD p x' hx' hp f (Dx.autEquiv M t)]
  exact congrArg Under.Hom.right (fiberEndRestrict_fac (Under.post p)
    (underPost_isFiberedInGroupoids p hp x')
    (Functor.pullbackFiberMap (Under.post p) (liftId D B S hS toSD hD p x' hx')
      (liftBaseOverMap D B S hS toSD hD p x' hx' f))
    (Functor.pullbackFiberMap_isHomLift _ _ _)
    (show (Under.post p).pullbackFiber (liftId D B S hS toSD hD p x' hx')
        (liftBaseOver D B S hS toSD hD p x' hx' M).hom ⟶
      (Under.post p).pullbackFiber (liftId D B S hS toSD hD p x' hx')
        (liftBaseOver D B S hS toSD hD p x' hx' M).hom from Dx.autEquiv M t))

/-- For a module map `f : M ⟶ N`, the lift class attached to the image of `t` in `Inf_{x'}(N)` is
the pullback along `f` of the lift class attached to `t`. -/
theorem isPullbackOfSquareZeroLift_infLiftClassEquiv
    (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    {M N : SiteModule D B} (f : M ⟶ N) (t : (Dx.functor.obj M : Type u)) :
    IsPullbackOfSquareZeroLift D B (Spec (.of A)) hA toSD₀ hD
      (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.p (autPt p hx toSD₀)
      (elemObj_p_obj _ _ _) f (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M t)
      (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx N (Dx.functor.map f t)) := by
  set g := infIsomSec p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t)
  have hg := (infIsomSec_restrict p hp hx toSD₀ s hs hx' φ' M (Dx.autEquiv M t)).symm
  have hm : squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD N ≫
      squareZeroOverMap D B (Spec (.of A)) hA toSD₀ f =
        squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M :=
    squareZeroArrow_naturality D B (Spec (.of A)) hA toSD₀ hD f
  have hg₂ : (𝟙 _ : (autPresheaf p hx).obj (op (algebraOver D B (Spec (.of A)) hA toSD₀ hD))) =
      (autPresheaf p hx).map (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD N).op
        ((autPresheaf p hx).map (squareZeroOverMap D B (Spec (.of A)) hA toSD₀ f).op g) := by
    rwa [← Functor.map_comp_apply, ← op_comp, hm]
  obtain ⟨φ, hφ, hc⟩ := exists_elemLift_hom (autPresheaf p hx) (𝟙 _)
    (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD M)
    (squareZeroArrow D B (Spec (.of A)) hA toSD₀ hD N)
    (squareZeroOverMap D B (Spec (.of A)) hA toSD₀ f) hm g hg hg₂
  refine ⟨_, _, rfl, ?_, φ, hφ, hc⟩
  rw [infLiftClassEquiv_apply]
  congr 2
  exact (infIsomSec_map p hp hx toSD₀ s hs hx' φ' Dx f t).symm

/-- **The tangent functor of the automorphism space at the identity of `x'`**, built from the
infinitesimal automorphisms of `x'`. -/
def tangentDataOfInf (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp) :
    TangentFunctorData D B (Spec (.of A)) hA toSD₀ hD
      (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.p (autPt p hx toSD₀)
      (elemObj_p_obj _ _ _) where
  functor := Dx.functor ⋙ ModuleCat.uliftFunctor.{u + 1, u} D
  liftEquiv M := Equiv.ulift.trans (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M)
  naturality {M N} f a := by
    obtain ⟨b, hb₁, hb₂⟩ := exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift D B
      (Spec (.of A)) hA toSD₀ hD (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.p
      (autPt p hx toSD₀) (elemObj_p_obj _ _ _)
      (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).isFiberedInGroupoids f
      (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M a.down)
    have h := isPullbackOfSquareZeroLift_unique D B (Spec (.of A)) hA toSD₀ hD
      (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).val.p (autPt p hx toSD₀)
      (elemObj_p_obj _ _ _)
      (fibredCategory B (Spec (.of A)) hA (autPresheaf p hx)).isFiberedInGroupoids f hb₂
      (isPullbackOfSquareZeroLift_infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx f a.down)
    change IsCanonicalLiftTransition _ _ _ _ _ _ _ _ _ f
      (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M a.down)
      (infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx N (Dx.functor.map f a.down))
    rwa [← h]
  liftEquiv_natural {M N} f a :=
    isPullbackOfSquareZeroLift_infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx f a.down

/-- The lift-class bijection of `tangentDataOfInf` is `infLiftClassEquiv`, read through `ULift`. -/
theorem tangentDataOfInf_liftEquiv
    (Dx : InfinitesimalAutomorphismFunctorData D B S hS toSD hD p x' hx' hp)
    (M : SiteModule D B) (t : ((tangentDataOfInf p hp hx toSD₀ s hs hx' φ' Dx).functor.obj M :
      Type (u + 1))) :
    (tangentDataOfInf p hp hx toSD₀ s hs hx' φ' Dx).liftEquiv M t =
      infLiftClassEquiv p hp hx toSD₀ s hs hx' φ' Dx M t.down :=
  rfl

end TangentOfInf

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism `Spec A'[N] ⟶ Spec A[M]` has the same underlying morphism of the site over
whichever base it is read. -/
theorem squareZeroOverBaseMap_left_eq {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
    (S₁ : Scheme.{u}) (hS₁ : B.Contains S₁) (toS₁ : Spec (.of A) ⟶ S₁)
    (toS₁' : Spec (.of A') ⟶ S₁) (hf₁ : Spec.map (CommRingCat.ofHom f) ≫ toS₁ = toS₁')
    (S₂ : Scheme.{u}) (hS₂ : B.Contains S₂) (toS₂ : Spec (.of A) ⟶ S₂)
    (toS₂' : Spec (.of A') ⟶ S₂) (hf₂ : Spec.map (CommRingCat.ofHom f) ≫ toS₂ = toS₂')
    (M : SiteModule A B) (N : SiteModule A' B) (ψ : (M.obj : Type u) →+ (N.obj : Type u))
    (hψ : ∀ (a : A) (m : M.obj), ψ (a • m) = f a • ψ m) :
    (squareZeroOverBaseMap f B S₁ hS₁ toS₁ toS₁' hf₁ M N ψ hψ).left =
      (squareZeroOverBaseMap f B S₂ hS₂ toS₂ toS₂' hf₂ M N ψ hψ).left :=
  rfl

variable {X : Type v} [Category.{u} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [p.IsFibered]
  {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  (hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC)
  {x y : X} (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC) (φ : y ⟶ x)
  [hφ : p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ]
  (Dx : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
  (Dy : InfinitesimalAutomorphismFunctorData C B S hS toSC hC p y hy hp)

/-- **The map of Stacks 07YA on infinitesimal automorphisms is restriction of sections of the
automorphism space** along `Spec C[N] ⟶ Spec A[M]`, read over `Spec A`. -/
theorem infIsomSec_infBaseChangeMap (M : SiteModule A B) (N : SiteModule C B)
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N.obj)
    (t : (Dx.functor.obj M : Type u)) :
    haveI : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) (𝟙 x) := IsHomLift.id hx
    morRestrict p (fiberPt p hx) (fiberPt p hx)
        ((Over.iteratedSliceBackward (algebraOver A B S hS toS hA)).map
          (squareZeroOverBaseMap (algebraMap A C) B (Spec (.of A)) hA (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap A C))) (Category.comp_id _) M N
            (restrictScalarsAddHom (algebraMap A C) ψ)
            (restrictScalarsAddHom_smul (algebraMap A C) ψ)))
        (infIsomSec p hp hx (𝟙 _) (𝟙 _) rfl hx (𝟙 x) M (Dx.autEquiv M t)) =
      infIsomSec p hp hx (Spec.map (CommRingCat.ofHom (algebraMap A C)))
        (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) rfl hy φ N
        (Dy.autEquiv N (infBaseChangeMap (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy
          φ hφ hp Dx Dy ψ t)) := by
  have : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) (𝟙 x) := IsHomLift.id hx
  have := infBaseChangeArrow_isHomLift (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy φ hφ
    hp (M := M) (N := N) ψ
  have hk : infBaseChangeArrow (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy φ hφ hp
        (M := M) (N := N) ψ ≫ infRetract p hp hx (𝟙 x) M = infRetract p hp hy φ N := by
    have := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
    have := hp.isStronglyCartesian_homLift (squareZeroRetraction A B S hS toS hA M)
      (trivialRetract A B S hS toS hA p x hx hp M)
    have := trivialRetract_isHomLift C B S hS toSC hC p y hy hp N
    change _ ≫ trivialRetract A B S hS toS hA p x hx hp M ≫ 𝟙 x =
      trivialRetract C B S hS toSC hC p y hy hp N ≫ φ
    rw [Category.comp_id]
    exact IsStronglyCartesian.fac p _ _ _ _
  exact morRestrict_infIsomSec p hp hx (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) rfl hy φ
    (𝟙 (Spec (.of A))) (𝟙 (algebraOver A B S hS toS hA)) rfl hx (𝟙 x) N M
    (squareZeroOverBaseMap (algebraMap A C) B (Spec (.of A)) hA (𝟙 _)
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) (Category.comp_id _) M N
      (restrictScalarsAddHom (algebraMap A C) ψ) (restrictScalarsAddHom_smul (algebraMap A C) ψ))
    (squareZeroOverBaseMap (algebraMap A C) B S hS toS toSC hf M N
      (restrictScalarsAddHom (algebraMap A C) ψ) (restrictScalarsAddHom_smul (algebraMap A C) ψ))
    (squareZeroOverBaseMap_left_eq (algebraMap A C) S hS toS toSC hf (Spec (.of A)) hA (𝟙 _)
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) (Category.comp_id _) M N
      (restrictScalarsAddHom (algebraMap A C) ψ) (restrictScalarsAddHom_smul (algebraMap A C) ψ))
    (infBaseChangeArrow (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy φ hφ hp
      (M := M) (N := N) ψ) hk
    (Dy.autEquiv N (infBaseChangeMap (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy φ hφ
      hp Dx Dy ψ t)) (Dx.autEquiv M t)
    (infBaseChangeMap_fac (algebraMap A C) B S hS toS hA toSC hC hf p x y hx hy φ hφ hp Dx Dy ψ t)

end BaseChange

section Main

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-- **Stacks 0DNR: infinitesimal automorphisms commute with flat base change.** Let `𝒳` be an
algebraic stack over `S` whose inertia `ℐ_𝒳 ⟶ 𝒳` is locally of finite presentation, let `A → C`
be a flat homomorphism of `S`-algebras, let `x` be an object of `𝒳` over `Spec A` and let
`y = x|_{Spec C}`, exhibited by an arrow `φ : y ⟶ x` over `Spec C ⟶ Spec A`. Then for every
`A`-module `M` there is a `C`-linear isomorphism `C ⊗_A Inf_x(M) ≅ Inf_y(C ⊗_A M)`, sending `1 ⊗ θ`
to the image of `θ` under the map `Inf_x(M) ⟶ Inf_y(C ⊗_A M)` of Stacks 07YA (restriction of
infinitesimal automorphisms along the arrow of trivial deformations over
`Spec C[C ⊗_A M] ⟶ Spec A[M]`). The modules `Inf_x`, `Inf_y` are arbitrary realizations of the
functors of Stacks 07Y9. -/
@[stacks 0DNR]
theorem exists_infFlatBaseChange_of_inertia (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C]
    (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
    (hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC)
    (x y : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = algebraOver A B S hS toS hA)
    (hy : 𝒳.val.val.p.obj y = algebraOver C B S hS toSC hC) (φ : y ⟶ x)
    (hφ : 𝒳.val.val.p.IsHomLift
      (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
    (Dx : InfinitesimalAutomorphismFunctorData A B S hS toS hA 𝒳.val.val.p x hx
      𝒳.val.isFiberedInGroupoids)
    (Dy : InfinitesimalAutomorphismFunctorData C B S hS toSC hC 𝒳.val.val.p y hy
      𝒳.val.isFiberedInGroupoids)
    (M : SiteModule A B) :
    ∃ e : (C ⊗[A] (Dx.functor.obj M : Type u)) ≃ₗ[C]
        (Dy.functor.obj ⟨ModuleCat.of C (C ⊗[A] M.obj), isSiteModule_tensor hC M⟩ : Type u),
      ∀ t : (Dx.functor.obj M : Type u), e ((1 : C) ⊗ₜ t) =
        infBaseChangeMap (algebraMap A C) B S hS toS hA toSC hC hf 𝒳.val.val.p x y hx hy φ hφ
          𝒳.val.isFiberedInGroupoids Dx Dy (tensorCoeff (A₁ := C) M.obj) t := by
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  let N : SiteModule C B := ⟨ModuleCat.of C (C ⊗[A] M.obj), isSiteModule_tensor hC M⟩
  -- the automorphism space of `x` and its stack over `Spec A`
  let G := autPresheaf p hx
  have hG : IsAlgebraicSpace B (Spec (.of A)) hA G :=
    isAlgebraicSpace_autSpace 𝒳 (algebraOver A B S hS toS hA) (fiberPt p hx)
  have hGl : Space.IsLocallyOfFinitePresentation B (Spec (.of A)) hA (terminal.from G) :=
    isLocallyOfFinitePresentation_autSpace 𝒳 hI (algebraOver A B S hS toS hA) (fiberPt p hx)
  have h𝒢 := isAlgebraicStack_fibredCategory.{u, w} B (Spec (.of A)) hA G hG
  have hf𝒢 := hasPropertyOnEverySmoothDiagram_spaceToBase.{u, w} B (Spec (.of A)) hA G hG hGl
  -- the two points
  let jC : Spec (.of C) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A C))
  have hs₁ : Over.Hom.left (𝟙 (algebraOver A B S hS toS hA)) = ObjectProperty.homMk (𝟙 _) := rfl
  have hs₂ : Over.Hom.left (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) =
      ObjectProperty.homMk jC := rfl
  have : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) (𝟙 x) := IsHomLift.id hx
  let Tx := tangentDataOfInf p hp hx (𝟙 _) _ hs₁ hx (𝟙 x) Dx
  let Ty := tangentDataOfInf p hp hx jC _ hs₂ hy φ Dy
  have hf₀ : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ 𝟙 (Spec (.of A)) = jC :=
    Category.comp_id _
  let b := algebraOverMapOfRingHom (algebraMap A C) B (Spec (.of A)) hA (𝟙 _) jC hA hC hf₀
  have hβ' : (𝟙 _ : G.obj (op (algebraOver C B (Spec (.of A)) hA jC hC))) =
      G.map b.op (𝟙 _) :=
    (morRestrict_id_hom p (fiberPt p hx) _).symm
  let β := elemHom G b hβ'
  have hβ : (fibredCategory B (Spec (.of A)) hA G).val.p.IsStronglyCartesian b β :=
    (fibredCategory B (Spec (.of A)) hA G).isFiberedInGroupoids.isStronglyCartesian_homLift b β
  obtain ⟨r, g, e', hr, hrz, hall⟩ := exists_tangentFlatBaseChange h𝒢
    (spaceToBase.{u, w} B (Spec (.of A)) hA G hG) hf𝒢 A C (𝟙 _) hA jC hC
    (autPt p hx (𝟙 _)) (autPt p hx jC) (elemObj_p_obj _ _ _) (elemObj_p_obj _ _ _) b rfl β hβ
    M (isSiteModule_tensor hC M) Tx Ty
  -- the morphism `Spec C[C ⊗ M] ⟶ Spec A[M]` over `Spec A`
  let ψ := tensorCoeff (A₁ := C) M.obj
  let H₀ := squareZeroOverBaseMap (algebraMap A C) B (Spec (.of A)) hA (𝟙 _) jC hf₀ M N
    (restrictScalarsAddHom (algebraMap A C) ψ) (restrictScalarsAddHom_smul (algebraMap A C) ψ)
  have hg : g = H₀ := by
    apply (BigFppfOver.toScheme B (Spec (.of A)) hA).map_injective
    rw [hr, squareZeroOverBaseMap_spec]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun z ↦ TrivSqZeroExt.ext (hrz z).1 (hrz z).2)
  -- the final isomorphism
  let eF : (C ⊗[A] (Dx.functor.obj M : Type u)) ≃ₗ[C] (Dy.functor.obj N : Type u) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
      (ULift.moduleEquiv (R := A) (M := (Dx.functor.obj M : Type u))).symm).trans
      (e'.trans (ULift.moduleEquiv (R := C) (M := (Dy.functor.obj N : Type u))))
  refine ⟨eF, fun t ↦ ?_⟩
  rw [show eF ((1 : C) ⊗ₜ t) = (e' ((1 : C) ⊗ₜ ULift.up t)).down from rfl]
  obtain ⟨a, c, ha, hc, φ', hφ', hcomm⟩ := hall (ULift.up t)
  -- the sections named by the two lifts
  have hsa : elemLiftSec G (𝟙 _) (squareZeroArrow A B (Spec (.of A)) hA (𝟙 _) hA M) a =
      infIsomSec p hp hx (𝟙 _) _ hs₁ hx (𝟙 x) M (Dx.autEquiv M t) := by
    rw [← elemLiftClassEquiv_mk, ha]
    exact elemLiftClassEquiv_infLiftClassEquiv p hp hx (𝟙 _) _ hs₁ hx (𝟙 x) Dx M t
  have hsc : elemLiftSec G (𝟙 _) (squareZeroArrow C B (Spec (.of A)) hA jC hC N) c =
      infIsomSec p hp hx jC _ hs₂ hy φ N (Dy.autEquiv N (e' ((1 : C) ⊗ₜ ULift.up t)).down) := by
    rw [← elemLiftClassEquiv_mk, hc]
    exact elemLiftClassEquiv_infLiftClassEquiv p hp hx jC _ hs₂ hy φ Dy N _
  -- restriction of sections is the map of Stacks 07YA
  have hnat' : G.map H₀.op (infIsomSec p hp hx (𝟙 _) _ hs₁ hx (𝟙 x) M (Dx.autEquiv M t)) =
      infIsomSec p hp hx jC _ hs₂ hy φ N (Dy.autEquiv N (infBaseChangeMap (algebraMap A C) B S hS
        toS hA toSC hC hf p x y hx hy φ hφ hp Dx Dy ψ t)) :=
    infIsomSec_infBaseChangeMap p hp hf hx hy φ Dx Dy M N ψ t
  have := hφ'.toIsHomLift
  have hcart := elemSecAt_hom G g φ'
    (underFiber_right_obj _ (elemObj_p_obj G _ _) _ c)
    (underFiber_right_obj _ (elemObj_p_obj G _ _) _ a)
  change elemLiftSec G _ _ c = G.map g.op (elemLiftSec G _ _ a) at hcart
  rw [hsa, hsc, hg, hnat'] at hcart
  exact (Dy.autEquiv N).injective (infIsomSec_injective p hp hx jC _ hs₂ hy φ N hcart)

end Main

end Deformation.Artin
