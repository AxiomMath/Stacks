module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityLevelLift
public import StacksFrontier.Deformation.Schlessinger.VersalExistence

/-!
# The base-lifting condition of the versality criterion for a naive obstruction theory

For a family over `Spec A` whose deformation theory is controlled by a morphism
`ξ : E ⟶ NL_{A/Λ}` with `H^{-1}(ξ ⊗ᴸ_A k)` surjective, the base of a formal object of the
predeformation category at the residue point lifts across every small-extension triangle of formal
objects. This is condition (2) of the versality criterion of [Stacks, Tag 06IU].

## Main results

* `Deformation.Artin.baseLifts_of_surjective_derivedTensorFibre_neg_one`: condition (2) of
  [Stacks, Tag 06IU] for the formal object of a family whose deformation theory is controlled by a
  morphism `ξ : E ⟶ NL_{A/Λ}` satisfying hypothesis (i) of [Stacks, Tag 07YM] and condition (2) of
  that tag in degree `-1`.
* `Deformation.Artin.isVersal_of_surjective_derivedTensorFibre_neg_one`: under the same hypotheses,
  together with (S1), (S2) and the surjectivity of `Deformation.mapIsomorphismClasses` at the dual
  numbers, the formal object is versal.

## References

* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

universe u

section ObjectBaseLift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type u} [Category.{u} F] (p : F ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k]
  [Algebra Λ A] [Algebra Λ k] [Algebra A k]
  (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [Mono iΛ]
  (hA : B.Contains (Spec (CommRingCat.of A)))

include hp hRS in
/-- Let `x` be a family over `Spec A` whose deformation theory is controlled by
`ξ : E ⟶ NL_{A/Λ}` in the sense of hypothesis (i) of [Stacks, Tag 07YM], with `H^{-1}(ξ ⊗ᴸ_A k)`
surjective, and let `η` be a formal object of the predeformation category of `x` at the residue
point, presented over `Spec A` by `gR : Spec η.base ⟶ Spec A` through the compatible family `r`.
Then the base of `η` lifts across every small-extension triangle of formal objects: this is
condition (2) of the criterion of [Stacks, Tag 06IU]. -/
public theorem baseLifts_of_surjective_derivedTensorFibre_neg_one
    (hmkk : Cardinal.mk k ≤ max Cardinal.aleph0 (Cardinal.mk A))
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    {Xf : F}
    (hXf : p.obj Xf = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA)
    (hKill : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A]
      (D : SquareZeroThickening A B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ = B.inclusion.map D.toS' →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hXf ≫ D.arrow))) →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0)
    {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (CC : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hpre : Deformation.IsPredeformationCategory.{u, u, u} CC.projection)
    (η : Deformation.FormalObject CC.projection)
    (r : ∀ n, (CC.objects (η.level n)).point ⟶ Xf)
    (gR : Spec (CommRingCat.of η.base) ⟶ Spec (CommRingCat.of A))
    (hbase : ∀ n, schemeMap (p ⋙ Over.post B.inclusion)
        (deformationPointBase CC (η.level n) (Deformation.AdicTruncation.obj η.base n)
          (η.level_eq n))
        (algebraOver_post B S hS p _ hA hXf) (r n) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ gR)
    (r₀ : x₀ ⟶ Xf)
    (hclosed : ∀ n, (CC.objects (η.level n)).arrow ≫ r n = r₀)
    (hr₀ : schemeMap (p ⋙ Over.post B.inclusion) hx₀
        (algebraOver_post B S hS p _ hA hXf) r₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A k)))
    (hpoints : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (CommRingCat.of A₁) ⟶ Spec (CommRingCat.of A)),
      f ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A₁)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (residueMap A₁)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀
          (algebraOver_post B S hS p _ hA hXf) r₀ →
      ∃ a : η.base ⟶ Deformation.artinianToComplete.obj A₁,
        Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR = f)
    (hinj : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (a b : η.base ⟶ Deformation.artinianToComplete.obj A₁),
      Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR =
        Spec.map (CommRingCat.ofHom b.hom.toRingHom) ≫ gR → a = b) :
    ∀ ⦃B₁ A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k⦄ (f : B₁ ⟶ A₁),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ ⦃yy xx : Deformation.FormalObject CC.projection⦄ (g : yy ⟶ xx),
        (Deformation.FormalObject.projection (p := CC.projection)).IsHomLift
          (Deformation.artinianToComplete.map f) g →
      ∀ (a : η ⟶ xx), ∃ b : η.base ⟶ yy.base, b ≫ g.base = a.base :=
  Deformation.baseLifts_of_levelLifts (BasedCategory.ofFunctor CC.projection)
    hpre η
    (levelLifts_of_surjective_derivedTensorFibre_neg_one B S hS p hp hRS iΛ hA hmkk T E hE ξ
      hsurj hXf hKill hx₀ CC η r gR hbase r₀ hclosed hr₀ hpoints hinj)

include hp hRS in
/-- Under the hypotheses of `baseLifts_of_surjective_derivedTensorFibre_neg_one`, if the
predeformation category satisfies (S1) and (S2) and `Deformation.mapIsomorphismClasses` is
surjective at the dual numbers, then `η` is versal in the sense of [Stacks, Tag 0CXJ]. -/
public theorem isVersal_of_surjective_derivedTensorFibre_neg_one
    (hmkk : Cardinal.mk k ≤ max Cardinal.aleph0 (Cardinal.mk A))
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    {Xf : F}
    (hXf : p.obj Xf = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA)
    (hKill : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A]
      (D : SquareZeroThickening A B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ = B.inclusion.map D.toS' →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hXf ≫ D.arrow))) →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0)
    {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (CC : PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hpre : Deformation.IsPredeformationCategory.{u, u, u} CC.projection)
    (hS1 : Deformation.SchlessingerConditionS1 CC.projection)
    (hS2 : Deformation.SchlessingerConditionS2 CC.projection)
    (η : Deformation.FormalObject CC.projection)
    (htangent : Function.Surjective
      (Deformation.mapIsomorphismClasses
        (Deformation.categoryOfElements_projection_isCofibered
          (Deformation.restrictedCoyoneda η.base))
        hpre.cofibered
        (Deformation.associatedMorphism hpre.cofibered η
          (Deformation.chosenPushforwardsOfCofibered CC.projection
            hpre.cofibered)).toBasedFunctor
        (Deformation.artinianDualNumbers Λ k)))
    (r : ∀ n, (CC.objects (η.level n)).point ⟶ Xf)
    (gR : Spec (CommRingCat.of η.base) ⟶ Spec (CommRingCat.of A))
    (hbase : ∀ n, schemeMap (p ⋙ Over.post B.inclusion)
        (deformationPointBase CC (η.level n) (Deformation.AdicTruncation.obj η.base n)
          (η.level_eq n))
        (algebraOver_post B S hS p _ hA hXf) (r n) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ gR)
    (r₀ : x₀ ⟶ Xf)
    (hclosed : ∀ n, (CC.objects (η.level n)).arrow ≫ r n = r₀)
    (hr₀ : schemeMap (p ⋙ Over.post B.inclusion) hx₀
        (algebraOver_post B S hS p _ hA hXf) r₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A k)))
    (hpoints : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (CommRingCat.of A₁) ⟶ Spec (CommRingCat.of A)),
      f ≫ (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A₁)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (residueMap A₁)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀
          (algebraOver_post B S hS p _ hA hXf) r₀ →
      ∃ a : η.base ⟶ Deformation.artinianToComplete.obj A₁,
        Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR = f)
    (hinj : ∀ (A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (a b : η.base ⟶ Deformation.artinianToComplete.obj A₁),
      Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ gR =
        Spec.map (CommRingCat.ofHom b.hom.toRingHom) ≫ gR → a = b) :
    Deformation.IsVersal hpre.cofibered η :=
  (Deformation.isVersal_iff_differential_surjective_and_base_lifts
      (BasedCategory.ofFunctor CC.projection) hpre hS1 hS2 η
      (Deformation.chosenPushforwardsOfCofibered CC.projection hpre.cofibered)).2
    ⟨htangent,
      baseLifts_of_surjective_derivedTensorFibre_neg_one B S hS p hp hRS iΛ hA hmkk T E hE ξ
        hsurj hXf hKill hx₀ CC hpre η r gR hbase r₀ hclosed hr₀ hpoints hinj⟩

end ObjectBaseLift

end Deformation.Artin

end
