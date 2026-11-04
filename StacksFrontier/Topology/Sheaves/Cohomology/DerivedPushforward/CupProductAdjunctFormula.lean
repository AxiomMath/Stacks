module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductOfCohomologyClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductCanonicalInstances
public import StacksFrontier.Homology.Tor.ProductOfGeneratorsIso

/-!
# The cup product of two classes, read as morphisms out of `L(A[-n])`

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)` and `c` a one-point comparison, i.e. a left
adjoint `L` of `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` together with a comparison
`α : L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_X} L y`. A class `ξ ∈ Hⁱ(X, K)` is a morphism `A[-i] ⟶ RΓ(X, K)`
(Tag 06XS), hence by adjunction a morphism `ξ̃ : L(A[-i]) ⟶ K`. This file records that, under
this reading, the cup product of Section 0FKU is the tensor product of morphisms:

`(ξ ∪ η)~ = L(χ) ≫ α ≫ (ξ̃ ⊗ η̃)`,

with `χ : A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` the splitting `pinnedSplitting`. This is Tag 0FP2 read
against the pairing `cupPairing` of Section 0FKU.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.classAdjunct`: the morphism `ξ̃ : L(A[-i]) ⟶ K`
  attached to a class `ξ ∈ Hⁱ(X, K)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.classAdjunctEquiv`: the bijection
  `Hⁱ(X, K) ≃ Hom(L(A[-i]), K)`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.classAdjunct_comp`: naturality in `K`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.classAdjunct_cupPairing`: the formula above.

## Implementation notes

The derived categories are those of the standard model `HasDerivedCategory.standard`, on which
`cupPairing`, `pinnedSplitting` and `OnePointComparison` are defined.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedRelativeCupProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (c : OnePointComparison X)

/-- **The morphism out of `L(A[-i])` attached to a class** `ξ ∈ Hⁱ(X, K)`: the adjoint transpose,
for `L ⊣ RΓ(X, -)`, of the morphism `A[-i] ⟶ RΓ(X, K)` representing `ξ`. -/
def classAdjunct (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    c.pullback.obj (baseShift X i) ⟶ K :=
  (c.adjunction.homEquiv _ _).symm (classRepresentative K i ξ)

/-- **Naturality of `classAdjunct`**: the morphism attached to the image of `ξ` under `u` is the
morphism attached to `ξ` followed by `u`. -/
theorem classAdjunct_comp {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : K ⟶ K') (i : ℤ) (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    classAdjunct c K' i
        (ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
          ((baseSections X).map u)) =
      classAdjunct c K i ξ ≫ u := by
  rw [classAdjunct, classRepresentative_comp, Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **The bijection `Hom_A(A, Hⁱ(X, K)) ≃ Hom(L(A[-i]), K)`** of which `classAdjunct` is the
forward map: Tag 06XS followed by the adjunction. -/
def classAdjunctEquiv (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ) :
    (ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) ≃
      (c.pullback.obj (baseShift X i) ⟶ K) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
      ((baseSections X).obj K) i (baseRing X)).symm.toEquiv.trans
    (c.adjunction.homEquiv _ _).symm

/-- The bijection `classAdjunctEquiv` sends a class `ξ` to `classAdjunct c K i ξ`. -/
theorem classAdjunctEquiv_apply (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (i : ℤ) (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    classAdjunctEquiv c K i ξ = classAdjunct c K i ξ :=
  rfl

/-- The morphism `A[-i-j] ⟶ RΓ(X, K ⊗^𝐋 M)` representing the cup product `ξ ∪ η` is the splitting
`pinnedSplitting` followed by the tensor product of the representing morphisms and the global cup
product. -/
theorem classRepresentative_cupPairing
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    classRepresentative (((derivedTensorProductFunctor X.sheaf).obj K).obj M) (i + j)
        ((λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
          cupPairing (globalCupProduct c) K M i j) =
      pinnedSplitting X i j ≫
        ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
          ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
            (globalCupProduct c).app (K, M) := by
  refine (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    ((baseSections X).obj (((derivedTensorProductFunctor X.sheaf).obj K).obj M)) (i + j)
    (baseRing X)).injective ?_
  refine (LinearEquiv.apply_symm_apply _ _).trans ?_
  have harg : pinnedSplitting X i j ≫
        ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
          ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
            (globalCupProduct c).app (K, M) =
      (pinnedSplitting X i j ≫
          ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
            ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η)) ≫
        (globalCupProduct c).app (K, M) := by
    simp only [Category.assoc]
  rw [harg, DerivedCategory.homologyFromSingleLinearEquiv_comp,
    homologyFromSingle_pinnedSplitting_comp]
  simp only [Category.assoc]
  rfl

/-- **The cup product as a tensor product of morphisms** (Tag 0FP2 against Section 0FKU): the
morphism out of `L(A[-i-j])` attached to `ξ ∪ η` is `L(χ)` followed by the comparison
`α : L(A[-i] ⊗^𝐋_A A[-j]) ⟶ L(A[-i]) ⊗^𝐋 L(A[-j])` and the tensor product `ξ̃ ⊗ η̃` of the
morphisms attached to `ξ` and `η`, for `χ = pinnedSplitting`. -/
theorem classAdjunct_cupPairing
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    classAdjunct c (((derivedTensorProductFunctor X.sheaf).obj K).obj M) (i + j)
        ((λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
          cupPairing (globalCupProduct c) K M i j) =
      c.pullback.map (pinnedSplitting X i j) ≫
        c.tensorComparison.app (baseShift X i, baseShift X j) ≫
          ((derivedTensorProductFunctor X.sheaf).map (classAdjunct c K i ξ)).app
              (c.pullback.obj (baseShift X j)) ≫
            ((derivedTensorProductFunctor X.sheaf).obj K).map (classAdjunct c M j η) := by
  have h := congrArg (c.adjunction.homEquiv _ _).symm (classRepresentative_cupPairing c K M i j ξ η)
  rw [globalCupProduct_app] at h
  exact h.trans (homEquiv_symm_comp_adjunctionBitensorMap_curried c.adjunction (tensorBase X)
    (derivedTensorProductFunctor X.sheaf) c.tensorComparison (pinnedSplitting X i j)
    (classRepresentative K i ξ) (classRepresentative M j η))

/-! ### The splitting and the comparison are invertible for the canonical comparison -/

variable (X) in
/-- The generator of `Hⁱ(A[-i])` of Tag 06XS is the class of the generating cocycle `1`. -/
theorem baseGenerator_eq_genClass (i : ℤ) :
    baseGenerator X i = RingTheory.TorProducts.genClass (baseRing X) i := by
  rw [baseGenerator, DerivedCategory.homologyFromSingleLinearEquiv_apply,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans
    (RingTheory.TorProducts.singleFunctorCompHomologyFunctorIso_inv_app_eq_genClass _ i)

variable (X) in
/-- The tensoring of the two generators is the class `tensorGen` of Tag 068H. -/
theorem tensorGenerator_eq_tensorGen (i j : ℤ) :
    tensorGenerator X i j = RingTheory.TorProducts.tensorGen (baseRing X) i j := by
  rw [tensorGenerator, baseGenerator_eq_genClass, baseGenerator_eq_genClass]
  rfl

variable (X) in
/-- The splitting `pinnedSplitting X i j : A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` is an isomorphism. -/
instance isIso_pinnedSplitting (i j : ℤ) : IsIso (pinnedSplitting X i j) :=
  RingTheory.TorProducts.isIso_of_homologyFromSingle_eq_tensorGen (baseRing X) i j _
    ((homologyFromSingle_pinnedSplitting X i j).trans (tensorGenerator_eq_tensorGen X i j))

variable (X) in
/-- The comparison `α : L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_X} L y` of the canonical one-point comparison
`onePointComparisonCanonical X` is an isomorphism. -/
instance isIso_tensorComparison_onePointComparisonCanonical :
    IsIso (onePointComparisonCanonical X).tensorComparison := by
  dsimp only [onePointComparisonCanonical,
    Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOfBaseTensorComparison,
    baseTensorComparison]
  have h₁ :=
    CochainComplex.DerivedTensor.RestrictScalars.isIso_restrictScalarsDerivedTensorComparison
      (basePointCommRingEquiv X)
  have h₂ := Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_onePointTensorComparison
    ↥(baseRing X)
  have h₃ := Functor.isIso_whiskerRight
    (CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison
      (basePointCommRingEquiv X))
    (Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointExtension X)
  have h₄ := Functor.isIso_whiskerLeft
    (Functor.prod
      (Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRestrict X).functor.mapDerivedCategory
      (Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRestrict X).functor.mapDerivedCategory)
    (Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison ↥(baseRing X))
  have h₅ := @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ h₄
  have h₆ := @Functor.isIso_whiskerRight _ _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Stacks.Cohomology.DerivedSectionsLeftAdjoint.toBasePoint X)) h₅
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₆
    (Functor.isoWhiskerLeft ((Stacks.Cohomology.DerivedSectionsLeftAdjoint.baseToPoint X).prod
      (Stacks.Cohomology.DerivedSectionsLeftAdjoint.baseToPoint X))
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        (Stacks.Cohomology.DerivedSectionsLeftAdjoint.toBasePoint X))).isIso_hom

end Stacks.Cohomology.DerivedGlobalCupProduct

end
