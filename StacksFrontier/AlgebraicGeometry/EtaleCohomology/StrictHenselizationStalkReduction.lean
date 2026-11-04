module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# The stalk of a derived direct image, reduced to two statements about the base change

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, and
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection. The comparison of [Stacks, Tag 03Q9]

`(Rf_*K)_s ≅ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)` in `D⁺(Ab)`

is formal once two statements about the base change are known:

1. a natural map on abelian sheaves `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, such as
   `AlgebraicGeometry.pushforwardStalkToSectionsAb`, is an isomorphism;
2. `p⁻¹` carries injective abelian sheaves on `X_étale` to sheaves acyclic for global sections on
   the base change.

Given these, both sides are right derived functors on `D⁺` of isomorphic functors once the exact
functors `p⁻¹` and the stalk are moved past the derivation, which is
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`.

## Main definitions

* `AlgebraicGeometry.strictHenselizationStalkPlusIsoOfRightAcyclic` — the isomorphism of functors
  `D⁺(X_étale) ⥤ D⁺(Ab)` under the two statements above.

## Implementation notes

Nothing here carries a Stacks tag: the two inputs are the content of [Stacks, Tag 03Q6] at the
system of étale neighbourhoods of `s`, and they are discharged elsewhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u


namespace CategoryTheory.Functor

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] {C₂ : Type*} [Category* C₂] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An exact functor commutes with the homology of the bounded below derived category:
`Hⁿ(G(K)) ≅ G(Hⁿ(K))`, naturally in `K : D⁺(C₁)`. -/
def mapDerivedCategoryPlusHomologyIso (n : ℤ) :
    G.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor C₂ n ≅
      DerivedCategory.Plus.homologyFunctor C₁ n ⋙ G :=
  isoWhiskerLeft DerivedCategory.Plus.ι (G.mapDerivedCategoryHomologyIso n)

/-- An exact functor commutes with the single functors into the bounded below derived
categories: `G(M[n]) ≅ G(M)[n]`. -/
def mapDerivedCategoryPlusSingleFunctorIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C₁ n ⋙ G.mapDerivedCategoryPlus ≅
      G ⋙ DerivedCategory.Plus.singleFunctor C₂ n :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (show DerivedCategory.singleFunctor C₁ n ⋙ G.mapDerivedCategory ≅
      G ⋙ DerivedCategory.singleFunctor C₂ n from G.mapDerivedCategorySingleFunctor n)

end CategoryTheory.Functor

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- Prefer the direct existence theorem to searching for an injective replacement.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- **The stalk of a derived direct image is the derived sections on the base change to the strict
henselization, under two inputs.** If a natural map `φ` on abelian sheaves
`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an isomorphism and `p⁻¹` carries injective
abelian sheaves to sheaves acyclic for global sections on the base change, then

`p⁻¹ ⋙ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), -) ≅ Rf_* ⋙ (-)_s`

as functors `D⁺(X_étale) ⥤ D⁺(Ab)`. -/
def strictHenselizationStalkPlusIsoOfRightAcyclic
    (φ : smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
    [IsIso φ]
    (hacyclic : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).rightAcyclic
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj I)) :
    (smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus ≅
      (smallEtalePushforwardAb f).rightDerivedFunctorPlus ⋙
        (smallEtaleStalkAb s.hom).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso _ _ _ _
    (asIso φ).symm hacyclic

/-- The cohomology form of `strictHenselizationStalkPlusIsoOfRightAcyclic`: for `K` in
`D⁺(X_étale)` and `n : ℤ`, `(Rⁿf_*K)_s ≅ Hⁿ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, under the same two
inputs. -/
def strictHenselizationStalkHomologyIsoOfRightAcyclic
    (φ : smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
    [IsIso φ]
    (hacyclic : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).rightAcyclic
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj I))
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((smallEtalePushforwardAb f).rightDerivedFunctorPlus.obj K)) ≅
      (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} n).obj
        ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus.obj
          ((smallEtalePullbackAb
            (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategoryPlus.obj K)) :=
  (((smallEtaleStalkAb s.hom).mapDerivedCategoryPlusHomologyIso n).app
      ((smallEtalePushforwardAb f).rightDerivedFunctorPlus.obj K)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} n).mapIso
      ((strictHenselizationStalkPlusIsoOfRightAcyclic B hS f s φ hacyclic).app K).symm

/-- The form of `strictHenselizationStalkPlusIsoOfRightAcyclic` for one abelian sheaf: for `F` on
`X_étale` and `n : ℤ`, `(Rⁿf_*F)_s ≅ Hⁿ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, under the same two
inputs, the derived functors being `CategoryTheory.Functor.rightDerivedPlus`. -/
def strictHenselizationStalkRightDerivedIsoOfRightAcyclic
    (φ : smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
    [IsIso φ]
    (hacyclic : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).rightAcyclic
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj I))
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (n : ℤ) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb f).rightDerivedPlus n).obj F) ≅
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedPlus n).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  strictHenselizationStalkHomologyIsoOfRightAcyclic B hS f s φ hacyclic
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) n ≪≫
    (DerivedCategory.Plus.homologyFunctor Ab.{u + 1} n).mapIso
      ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerivedFunctorPlus.mapIso
        (((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)
          ).mapDerivedCategoryPlusSingleFunctorIso 0).app F))

end AlgebraicGeometry

end
