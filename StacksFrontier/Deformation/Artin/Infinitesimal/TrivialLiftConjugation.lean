module

public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentAtPoint
import all StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison

/-!
# The pushforward of a point to the dual numbers and the trivial deformation

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `k` be a
field over `S` and `x₀` an object of `𝒳` over `Spec k`, and let `𝓕 = 𝓕_{𝒳,k,x₀}` be the
predeformation category of `x₀`. For a point `y` of `𝓕` over the residue field, the pushforward
of `y` to the dual numbers `k[ε]` is isomorphic to the trivial deformation of `x₀` over `k[k]`.
This file records that isomorphism together with what conjugation by it does: it identifies the
automorphisms of the pushforward with the endomorphisms of the trivial deformation, and carries
the arrow induced by the scaling `ε ↦ cε` of the dual numbers to the transition arrow of the
trivial deformations along multiplication by `c`, up to an endomorphism of the trivial
deformation.

## Main results

* `Deformation.Artin.trivialDeformation_right_post`: the trivial deformation of `x₀` over `k[V]`
  lives on the spectrum of `k[V]`.
* `Deformation.Artin.exists_trivialLift_conjugation`: the pushforward of a point over the
  residue field to the dual numbers is isomorphic to the trivial deformation, and conjugation by
  the isomorphism carries the scaling of the dual numbers to the transition maps of the trivial
  deformations.

## References

* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Under.post CategoryTheory.BasedCategory.ofFunctor
  Deformation.Artin.predeformationCategory

universe u v w

namespace Deformation.Artin

section TrivialLiftConjugation

attribute [local instance] PredeformationConstruction.category

open Functor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

/-- The trivial square-zero extension by the zero space is a residue-field object. -/
private theorem isIso_residueMorphism_dualPointObj :
    IsIso (residueMorphism.{u, u, u} (dualPointObj Λ k)) :=
  ArtinianLocalAlgCat.isIso_of_bijective_hom _
    ⟨fun _ _ h => (bijective_residueMap_dualPointObj Λ k).1 (congrArg ULift.down h),
      fun b => ⟨(bijective_residueMap_dualPointObj Λ k).2 b.down |>.choose,
        ULift.ext _ _ ((bijective_residueMap_dualPointObj Λ k).2 b.down).choose_spec⟩⟩

/-- **The pushforward of a point to the dual numbers is the trivial deformation.** For a point
`y` of the predeformation category over the residue field and a choice `P` of its pushforwards,
the pushforward to the canonical dual numbers is isomorphic to the trivial deformation over
`k[k]`, by an isomorphism lying over the comparison of the two presentations of the dual
numbers. -/
private theorem exists_iso_trivialDeformationFib
    (hpre : IsPredeformationCategory
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.Fiber
      (residueFieldObject.{u, u, u} Λ k))
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y.1) :
    ∃ ι : (P.obj (dualNumbersUnder (p := (predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (x := y.1))).1 ≅
        (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).1,
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.IsHomLift
        (dualNumbersUnderHom (p := (predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (x := y.1)) ι.hom := by
  let π := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
  let z₀ := trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k PUnit.{u + 1})
  let zε := trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)
  let i : z₀.1 ⟶ zε.1 := trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx
    (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k)
  have hi : π.IsHomLift ((artinianSquareZeroExtensionFunctor Λ k).map 0) i :=
    trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx 0
  have : IsIso (residueMorphism.{u, u, u} (π.obj z₀.1)) :=
    isIso_residueMorphism_dualPointObj (Λ := Λ) (k := k)
  obtain ⟨j⟩ := nonempty_iso_of_isIso_residueMorphism hpre y z₀.1
  let Uε := dualNumbersUnder (p := π) (x := y.1)
  let σ : Uε.right ⟶ π.obj zε.1 := dualNumbersUnderHom (p := π) (x := y.1)
  have hsq : π.map (j.hom ≫ i) = Uε.hom ≫ σ := by
    have hmi : π.map i = (artinianSquareZeroExtensionFunctor Λ k).map 0 := rfl
    rw [π.map_comp, hmi]
    exact (dualNumbersUnder_hom_comp_dualNumbersUnderHom (p := π) (x := y.1) (π.map j.hom)).symm
  have := P.inclusion_cocartesian Uε
  let ιhom : (P.obj Uε).1 ⟶ zε.1 :=
    IsStronglyCocartesian.map π Uε.hom (P.inclusion Uε) (g := σ) hsq (j.hom ≫ i)
  have hι : π.IsHomLift σ ιhom := IsStronglyCocartesian.map_isHomLift π _ _ hsq _
  have : π.IsStronglyCocartesian σ ιhom :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hpre.cofibered σ ιhom hι
  have : IsIso σ := inferInstanceAs (IsIso (dualNumbersUnderHom (p := π) (x := y.1)))
  have : IsIso ιhom := IsStronglyCocartesian.isIso_of_base_isIso π σ ιhom
  exact ⟨asIso ιhom, hι⟩

include hx₀ in
/-- The trivial deformation of the point over `k[V]` lives on the spectrum of `k[V]`. -/
public theorem trivialDeformation_right_post (V : FGModuleCat.{u} k) :
    (p ⋙ Over.post B.inclusion).obj
        (trivialDeformation k B S hS toS hk p x₀ hx hp ((fgSiteModule B hk).obj V)).1.right =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ) :=
  lift_base B S hS iΛ toS hk p x₀ hx₀ hx V (trivialLift B S hS toS hk p hp x₀ hx V)

/-- **Conjugation with the trivial lift.** Let `y` be a point of the predeformation category
`𝓕_{𝒳,k,x₀}` over the residue field and `P` a choice of pushforwards of `y`. The object `x'₀` of
`𝒳` underlying the pushforward of `y` to the dual numbers is isomorphic, compatibly with the
arrows out of `x₀` and over the comparison of the two presentations of the dual numbers, to the
trivial deformation of `x₀` over `k[k]`. Conjugation by this isomorphism identifies the
automorphisms of the pushforward with the endomorphisms of the trivial lift, and carries the
arrow induced by the scaling `ε ↦ cε` to the transition arrow of the trivial deformations along
multiplication by `c`, up to an endomorphism of the trivial lift. -/
public theorem exists_trivialLift_conjugation
    (hpre : IsPredeformationCategory
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (y : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.Fiber
      (residueFieldObject.{u, u, u} Λ k))
    (P : ChosenPushforwardsAt
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection y.1) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    let yε := P.obj (dualNumbersUnder (p := D.projection) (x := y.1))
    let t := trivialDeformation k B S hS toS hk p x₀ hx hp
      ((fgSiteModule B hk).obj (FGModuleCat.of k k))
    ∃ η : (D.objects yε.1).point ≅ t.1.right,
      (D.objects yε.1).arrow ≫ η.hom = t.1.hom ∧
      (∀ hb : (p ⋙ Over.post B.inclusion).obj t.1.right = Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))))
            ≫ iΛ),
        eqToHom (congrArg Over.left (D.objects yε.1).base).symm ≫
            ((p ⋙ Over.post B.inclusion).map η.hom).left ≫ eqToHom (congrArg Over.left hb) =
          Spec.map (CommRingCat.ofHom (CategoryTheory.inv
            (dualNumbersUnderHom (p := D.projection) (x := y.1)) ≫
              eqToHom (yε.2.symm.trans (D.object_projection yε.1))).hom.toRingHom)) ∧
      ∃ Ψ : Aut yε ≃ (t ⟶ t),
        (∀ a, (Ψ a).1.right = η.inv ≫ (D.morphisms yε.1 yε.1 a.hom.1).arrow ≫ η.hom) ∧
        ∀ c : k, ∃ δ : t ⟶ t,
          δ.1.right ≫ η.inv ≫ (D.morphisms yε.1 yε.1
              (P.map (tangentScaling (p := D.projection) (x := y.1) c))).arrow ≫ η.hom =
            (letI := underPost_isFibered p hp x₀; Functor.pullbackFiberMap (Under.post p)
              (liftId k B S hS toS hk p x₀ hx) (liftBaseOverMap k B S hS toS hk p x₀ hx
                ((fgSiteModule B hk).map (c • 𝟙 (FGModuleCat.of k k))))).right := by
  intro D yε t
  obtain ⟨ι, hι⟩ := exists_iso_trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx hpre y P
  let zε := trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)
  have arrow_comp_eq_id : ∀ {a b : D.carrier} (f : a ⟶ b) (g : b ⟶ a), f ≫ g = 𝟙 a →
      (D.morphisms b a g).arrow ≫ (D.morphisms a b f).arrow = 𝟙 (D.objects a).point :=
    fun f g h => (D.reversed_composition f g).symm.trans
      ((congrArg (fun f => (D.morphisms _ _ f).arrow) h).trans (D.reversed_identity _))
  let η : (D.objects yε.1).point ≅ t.1.right :=
    { hom := (D.morphisms zε.1 yε.1 ι.inv).arrow
      inv := (D.morphisms yε.1 zε.1 ι.hom).arrow
      hom_inv_id := arrow_comp_eq_id _ _ ι.hom_inv_id
      inv_hom_id := arrow_comp_eq_id _ _ ι.inv_hom_id }
  refine ⟨η, (D.morphisms zε.1 yε.1 ι.inv).triangle, fun hb => ?_, ?_⟩
  · have : D.projection.IsHomLift
        (asIso (dualNumbersUnderHom (p := D.projection) (x := y.1))).hom ι.hom := hι
    have : D.projection.IsHomLift
        (CategoryTheory.inv (dualNumbersUnderHom (p := D.projection) (x := y.1))) ι.inv :=
      IsHomLift.inv_lift_inv D.projection (asIso _) ι
    have hinv : D.projection.map ι.inv = CategoryTheory.inv
        (dualNumbersUnderHom (p := D.projection) (x := y.1)) ≫ eqToHom yε.2.symm := by
      rw [IsHomLift.fac' D.projection (CategoryTheory.inv
        (dualNumbersUnderHom (p := D.projection) (x := y.1))) ι.inv]
      exact Category.id_comp _
    have h := (D.morphisms zε.1 yε.1 ι.inv).arrow_base
    change _ = Spec.map (CommRingCat.ofHom (D.projection.map ι.inv).hom.toRingHom) at h
    rwa [hinv] at h
  refine ⟨(fiberAutMulEquivOfIso ι).toEquiv.trans
    ((trivialAutEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).trans
      (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k))), ?_, ?_⟩
  · intro a
    show (D.morphisms zε.1 zε.1 (ι.inv ≫ a.hom.1 ≫ ι.hom)).arrow = _
    rw [D.reversed_composition, D.reversed_composition, Category.assoc]
    rfl
  · intro c
    let π := D.projection
    let s := tangentScaling (p := π) (x := y.1) c
    let σ := dualNumbersUnderHom (p := π) (x := y.1)
    let gc := (artinianSquareZeroExtensionFunctor Λ k).map (c • 𝟙 (FGModuleCat.of k k))
    let τ : zε.1 ⟶ zε.1 := trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx
      (c • 𝟙 (FGModuleCat.of k k))
    have : π.IsHomLift gc τ :=
      trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx _
    have : π.IsHomLift s.right (P.map s) := P.map_isHomLift s
    have : π.IsHomLift σ ι.hom := hι
    have h1 : π.IsHomLift (s.right ≫ σ) (P.map s ≫ ι.hom) := inferInstance
    have : π.IsStronglyCocartesian (s.right ≫ σ) (P.map s ≫ ι.hom) :=
      isStronglyCocartesian_of_isCofiberedInGroupoids hpre.cofibered _ _ h1
    have hf' : σ ≫ gc = (s.right ≫ σ) ≫ 𝟙 (π.obj zε.1) :=
      (tangentScaling_right_comp_dualNumbersUnderHom (p := π) (x := y.1) c).symm.trans
        (Category.comp_id _).symm
    let δD : zε.1 ⟶ zε.1 :=
      IsStronglyCocartesian.map π (s.right ≫ σ) (P.map s ≫ ι.hom) hf' (ι.hom ≫ τ)
    have hδ : π.IsHomLift (𝟙 (π.obj zε.1)) δD :=
      IsStronglyCocartesian.map_isHomLift π _ _ hf' _
    have hfac : (P.map s ≫ ι.hom) ≫ δD = ι.hom ≫ τ :=
      IsStronglyCocartesian.fac π _ _ hf' _
    refine ⟨trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k) ⟨δD, hδ⟩, ?_⟩
    have harr : (D.morphisms zε.1 zε.1 δD).arrow ≫ (D.morphisms yε.1 zε.1 ι.hom).arrow ≫
        (D.morphisms yε.1 yε.1 (P.map s)).arrow =
          (D.morphisms zε.1 zε.1 τ).arrow ≫ (D.morphisms yε.1 zε.1 ι.hom).arrow := by
      simpa only [D.reversed_composition] using
        congrArg (fun f => (D.morphisms yε.1 zε.1 f).arrow) hfac
    have hgoal : (D.morphisms zε.1 zε.1 δD).arrow ≫ (D.morphisms yε.1 zε.1 ι.hom).arrow ≫
        (D.morphisms yε.1 yε.1 (P.map s)).arrow ≫ (D.morphisms zε.1 yε.1 ι.inv).arrow =
          (D.morphisms zε.1 zε.1 τ).arrow := by
      rw [reassoc_of% harr, arrow_comp_eq_id _ _ ι.inv_hom_id, Category.comp_id]
    exact hgoal

end TrivialLiftConjugation

end Deformation.Artin

end
