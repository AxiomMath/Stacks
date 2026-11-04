module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Functoriality
public import StacksFrontier.Deformation.RimSchlessingerCategory.AutomorphismLifting
public import StacksFrontier.Deformation.SchlessingerConditions.SmallExtensionLift
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# A smoothness criterion for morphisms of deformation categories

A morphism `φ : 𝓕 ⟶ 𝓖` of deformation categories over `𝒞_Λ` is smooth precisely when its
differential on tangent spaces is surjective and a lift of the image of an object along a
small extension already forces the object itself to have a lift.

## Main results

* `Deformation.isSmooth_iff_differential_surjective_and_lifts`: the criterion.

## References

* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory IsLocalRing
universe u w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-! ### Lifts of the image are reached from lifts -/

/-- The functor of isomorphism classes of a deformation category satisfies Schlessinger's
condition (S2). -/
private theorem schlessingerConditionS2_isomorphismClasses
    {𝓒 : BasedCategory.{_, _} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓒 : IsDeformationCategory 𝓒.p) :
    SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓒 h𝓒.predeformation.cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses 𝓒 h𝓒.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓒.satisfiesRS) (.inl h𝓒.predeformation)

/-- If the differential of `φ` is surjective and a lift of the image of an object along a small
extension forces the object itself to have a lift, then every lift `g` of `φ.obj x` along a
small extension `f` is, up to an isomorphism lying over `𝟙 A'`, the image of a lift of `x`. -/
private theorem mapLiftClasses_surjective_of_differential_surjective
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    (hd : Function.Surjective
      (differential h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ))
    (hlifts : ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄
      (f : B ⟶ A), InfinitesimalLifting.IsSmallExtension
        (CommRingCat.ofHom f.hom.toRingHom) → ∀ (x : 𝓕.p.Fiber A),
          (∃ (y' : 𝓖.obj) (g : y' ⟶ φ.obj x.1), 𝓖.p.IsHomLift f g) →
            ∃ (x' : 𝓕.obj) (h : x' ⟶ x.1), 𝓕.p.IsHomLift f h)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom))
    (x : 𝓕.p.Fiber A) (y' : 𝓖.obj) (g : y' ⟶ φ.obj x.1)
    (hg : 𝓖.p.IsHomLift f g) :
    ∃ (x' : 𝓕.obj) (h : x' ⟶ x.1) (a : φ.obj x' ⟶ y'),
      𝓕.p.IsHomLift f h ∧ 𝓖.p.IsHomLift (𝟙 A') a ∧ φ.map h = a ≫ g := by
  let hf : Function.Surjective f.hom := hsmall.2.2.2.2.1
  let hann := smallExtension_kernel_annihilated f hsmall
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let hS2𝓕 := schlessingerConditionS2_isomorphismClasses h𝓕
  let hS2𝓖 := schlessingerConditionS2_isomorphismClasses h𝓖
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨hS2𝓖⟩
  let xG := (fiberFunctor φ A).obj x
  let := liftAction 𝓕 h𝓕 f hf hann x
  let := liftAction 𝓖 h𝓖 f hf hann xG
  let dφ := IsLinearMap.mk'
    (differential h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ)
    (differential_isLinearMap 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation hS2𝓕 hS2𝓖 φ)
  let L := TensorProduct.map dφ
    (LinearMap.id : RingHom.ker f.hom.toRingHom →ₗ[k] RingHom.ker f.hom.toRingHom)
  have hL : Function.Surjective L :=
    TensorProduct.map_surjective hd Function.surjective_id
  obtain ⟨x₁, h₁, hh₁⟩ := hlifts f hsmall x ⟨y', g, hg⟩
  let lsrc : Lift 𝓕.p f x := ⟨x₁, h₁, hh₁⟩
  let ltar : Lift 𝓖.p f xG := ⟨y', g, hg⟩
  let a₀ : LiftClasses 𝓕.p f x := ThinSkeleton.mk lsrc
  let b : LiftClasses 𝓖.p f xG := ThinSkeleton.mk ltar
  let b₀ : LiftClasses 𝓖.p f xG := mapLiftClasses φ f x a₀
  obtain ⟨tG, htG⟩ := (liftAction_bijective 𝓖 h𝓖 f hf hann xG b₀).2 b
  obtain ⟨tF, htF⟩ := hL tG
  have hclass : mapLiftClasses φ f x (tF +ᵥ a₀) = b := by
    rw [mapLiftClasses_vadd 𝓕 𝓖 h𝓕 h𝓖 φ f hf hann x a₀ tF, show L tF = tG from htF]
    simpa [b₀] using htG
  obtain ⟨lsrc', hsrc'⟩ := Quotient.exists_rep (tF +ᵥ a₀ : LiftClasses 𝓕.p f x)
  have hclass' : mapLiftClasses φ f x (ThinSkeleton.mk lsrc') = b :=
    (congrArg (mapLiftClasses φ f x) hsrc').trans hclass
  change ThinSkeleton.mk ((liftFunctor φ f x).obj lsrc') = ThinSkeleton.mk ltar at hclass'
  obtain ⟨i⟩ := Quotient.exact hclass'
  exact ⟨lsrc'.obj, lsrc'.hom, i.hom.hom, lsrc'.isHomLift, i.hom.isHomLift, i.hom.fac.symm⟩

/-! ### The criterion -/

/-- Surjectivity of the differential and preservation of the existence of lifts across small
extensions characterize smoothness. -/
@[stacks 0DYP]
public theorem isSmooth_iff_differential_surjective_and_lifts
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) :
    IsSmooth φ ↔
      (Function.Surjective
        (differential h𝓕.predeformation.cofibered
          h𝓖.predeformation.cofibered φ) ∧
       ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄
         (f : B ⟶ A),
         InfinitesimalLifting.IsSmallExtension
           (CommRingCat.ofHom f.hom.toRingHom) →
         ∀ (x : 𝓕.p.Fiber A),
           (∃ (y' : 𝓖.obj) (g : y' ⟶ φ.obj x.1),
             𝓖.p.IsHomLift f g) →
           (∃ (x' : 𝓕.obj) (h : x' ⟶ x.1),
             𝓕.p.IsHomLift f h)) := by
  refine ⟨fun hsmooth ↦ ⟨?_, fun B A f hsmall x ⟨y', g, hg⟩ ↦ ?_⟩, fun ⟨hd, hlifts⟩ ↦ ?_⟩
  · let D := augmentedDualNumbers (Λ := Λ) (k := k)
    let K : ArtinianLocalAlgCat.{u, w, w} Λ k := residueFieldObject.{u, w, w} Λ k
    let f : D ⟶ K := residueFieldMorphism
    have hf : Function.Surjective f.hom := residueFieldMorphism_surjective
    let x₀ := specialFiberObject 𝓕.p h𝓕.predeformation
    let x₀G : 𝓖.p.Fiber K := ⟨φ.obj x₀.1, (φ.w_obj x₀.1).trans x₀.2⟩
    intro z
    change (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered).obj D at z
    obtain ⟨yD, hyD⟩ := classOf_surjective 𝓖 h𝓖.predeformation.cofibered D z
    obtain ⟨yK, c, hc⟩ :=
      exists_pushforward h𝓖.predeformation.cofibered f yD.1 yD.2
    let yKfiber : 𝓖.p.Fiber K := ⟨yK, IsHomLift.codomain_eq 𝓖.p f c⟩
    obtain ⟨iK⟩ := specialFiberObjects_isomorphic 𝓖.p h𝓖.predeformation yKfiber x₀G
    let g : yD.1 ⟶ φ.obj x₀.1 := c ≫ iK.hom.1
    have hg : 𝓖.p.IsHomLift f g := by
      let := hc
      let := iK.hom.2
      exact IsHomLift.comp_lift_id_right' 𝓖.p f c K iK.hom.1
    obtain ⟨xD, h, a, hh, ha, -⟩ := hsmooth f hf yD.1 x₀.1 g hg
    let xDfiber : 𝓕.p.Fiber D := ⟨xD, IsHomLift.domain_eq 𝓕.p f h⟩
    let xGDfiber : 𝓖.p.Fiber D := (fiberFunctor φ D).obj xDfiber
    let aFiber : xGDfiber ⟶ yD := ⟨a, ha⟩
    let : IsGroupoid (𝓖.p.Fiber D) :=
      fiber_isGroupoid 𝓖.p h𝓖.predeformation.cofibered D
    exact ⟨classOf 𝓕 h𝓕.predeformation.cofibered xDfiber,
      (mapIsomorphismClasses_classOf h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ
        xDfiber).trans ((classOf_eq_of_isIsomorphic 𝓖 h𝓖.predeformation.cofibered xGDfiber yD
          ⟨asIso aFiber⟩).trans hyD)⟩
  · obtain ⟨x', h, -, hh, -, -⟩ := hsmooth f hsmall.2.2.2.2.1 y' x.1 g hg
    exact ⟨x', h, hh⟩
  · apply isSmooth_of_lifts_smallExtensions
      h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ
    intro B A f hsmall y x g hg
    exact mapLiftClasses_surjective_of_differential_surjective h𝓕 h𝓖 φ hd hlifts f hsmall
      ⟨x, (φ.w_obj x).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)⟩ y g hg

end

end Deformation
