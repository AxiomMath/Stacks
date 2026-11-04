module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.ProductNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupClassSplitting

/-!
# On cohomology, `ξ ∪ -` is the cup product with `ξ`

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)` and `K, M ∈ D(𝒪_X)`.  The second clause of
Remark 0G6W says that the map `ξ ∪ -` of
`Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass` induces, on cohomology, the cup product
with `ξ`.  The cup product on cohomology is the pairing
`Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing` of Section 0FKU — the tensoring of the two
classes by the pairing of Tag 068H followed by `Hⁱ⁺ʲ(μ)` — and that is the right-hand side of the
theorem below.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.tensorGenerator_comp` — the tensoring of the two
  generators of `Hⁱ(A[-i])` and `Hʲ(A[-j])`, pushed along the morphisms representing two classes
  `ξ` and `η`, is the tensoring of `ξ` and `η`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClass_cupPairing` —
  **the second clause of Remark 0G6W, against the source's pairing**: `Hⁱ⁺ʲ(ξ ∪ -)` carries the
  class of `η`, read through the source's identifications, to `ξ ∪ η` as `cupPairing` defines it.

## Implementation notes

The source's identification `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` is taken to be
`Stacks.Cohomology.DerivedGlobalCupProduct.pinnedSplitting`, the morphism pinned by the condition
that its class be the tensoring of the two generators, rather than `baseShiftSplitting`, which is
assembled from the shift-tensor commutation but whose class cannot be computed, because the
`commShift_left` datum of `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` is
obtained from a bare existence statement. The theorem
`Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClass` from which this one
is derived quantifies over *every* `χ`; the choice fixes which morphism the right-hand side is
read against.

## References

* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-! ### `A[-i]` as the single complex of a free module -/

/-- The single cochain complex with the free module `A` of rank one in degree `i`, for
`A = Γ(X, 𝒪_X)`.  Its image in `D(A)` is `Stacks.Cohomology.DerivedGlobalCupProduct.baseShift`,
by definition of `DerivedCategory.singleFunctor`. -/
private abbrev singleBase (i : ℤ) : CochainComplex (ModuleCat.{u} (baseRing X)) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} (baseRing X)) i).obj
    (ModuleCat.of (baseRing X) (baseRing X))

/-- Every term of the single complex of the free module `A` in degree `i` is projective. -/
private theorem projective_singleBase_X (i n : ℤ) : Projective ((singleBase X i).X n) := by
  have : Projective (ModuleCat.of (baseRing X) (baseRing X)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  by_cases hn : n = i
  · exact Projective.of_iso
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) i
        (ModuleCat.of (baseRing X) (baseRing X)) n hn).symm inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i
      (ModuleCat.of (baseRing X) (baseRing X)) n hn).projective

/-- The single complex of the free module `A` in degree `i` is K-flat (Tag 064K). -/
private theorem kFlat_singleBase (i : ℤ) : (singleBase X i).KFlat := by
  have h (k : ℤ) : Module.Flat (baseRing X) ((singleBase X i).X k) :=
    have := projective_singleBase_X X i k
    have : Module.Projective (baseRing X) ((singleBase X i).X k) := inferInstance
    inferInstance
  exact CochainComplex.KFlat.kFlat_of_flat (singleBase X i) i

/-- The single complex of the free module `A` in degree `i` is K-projective. -/
private instance isKProjective_singleBase (i : ℤ) : (singleBase X i).IsKProjective :=
  have := projective_singleBase_X X i
  CochainComplex.isKProjective_of_projective (singleBase X i) i

/-! ### The tensoring of the generators computes the tensoring of the classes -/

variable {X}

/-- **The tensoring of the generators is the tensoring of the classes.**  Pushing the tensoring
of the generators of `Hⁱ(A[-i])` and `Hʲ(A[-j])` along the tensor product of the morphisms
representing `ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(X, M)` gives the tensoring of `ξ` and `η` by the pairing
of Tag 068H. -/
theorem tensorGenerator_comp (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    tensorGenerator X i j ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
            ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η)) =
      (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
        (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections X).obj K)
          ((baseSections X).obj M) i j).map := by
  have hnat :
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
              (classRepresentative K i ξ) ⊗ₘ
            (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) j).map
              (classRepresentative M j η)) ≫
          (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections X).obj K)
            ((baseSections X).obj M) i j).map =
        (RingTheory.TorProducts.cohomologyTensorProduct (baseShift X i) (baseShift X j) i j).map ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
            (((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
              ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η)) :=
    RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective
      (singleBase X i) (singleBase X j) (kFlat_singleBase X i) (kFlat_singleBase X j)
      (classRepresentative K i ξ) (classRepresentative M j η) i j
  rw [tensorGenerator, Category.assoc, Category.assoc, ← hnat,
    tensorHom_comp_tensorHom_assoc, baseGenerator_comp, baseGenerator_comp]

/-- The class of the morphism `A[-i-j] ⟶ RΓ(X, K) ⊗^𝐋_A RΓ(X, M)` through which the source's
cup product is defined — `pinnedSplitting` followed by the tensor product of the morphisms
representing `ξ` and `η` — is the tensoring of the classes `ξ` and `η` by the pairing of
Tag 068H. -/
theorem homologyFromSingle_pinnedSplitting_comp
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
        (((tensorBase X).obj ((baseSections X).obj K)).obj ((baseSections X).obj M)) (i + j)
        (baseRing X)
        (pinnedSplitting X i j ≫
          (((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
            ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η))) =
      (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
        (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections X).obj K)
          ((baseSections X).obj M) i j).map := by
  rw [DerivedCategory.homologyFromSingleLinearEquiv_comp, homologyFromSingle_pinnedSplitting,
    tensorGenerator_comp]

/-! ### The second clause of Remark 0G6W -/

/-- **The cup product with a class on cohomology, against the pairing of Section 0FKU, for the
global cup product of a one-point comparison `c`.**  For `ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(X, M)`, the
map `Hⁱ⁺ʲ(ξ ∪ -)` carries the class of `η`, read in `Hⁱ⁺ʲ(RΓ(X, M)[-i])` through the
identifications `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` (here `pinnedSplitting`) and
`A[-i] ⊗^𝐋_A RΓ(X, M) = RΓ(X, M)[-i]`, to `ξ ∪ η` as
`Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing` defines it. -/
theorem homologyFromSingle_cupWithClass_cupPairing (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
          (((baseSections X).obj M)⟦-i⟧) (i + j) (baseRing X)
          (pinnedSplitting X i j ≫
            ((tensorBase X).obj (baseShift X i)).map (classRepresentative M j η) ≫
              (baseShiftTensorIso X i ((baseSections X).obj M)).hom) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (cupWithClass c K M i ξ) =
      (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
        cupPairing (globalCupProduct c) K M i j := by
  have harg : pinnedSplitting X i j ≫
        ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
          ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
            (globalCupProduct c).app (K, M) =
      (pinnedSplitting X i j ≫
          (((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
            ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η))) ≫
        (globalCupProduct c).app (K, M) := by
    simp only [Category.assoc]
  refine (homologyFromSingle_cupWithClass c K M i j ξ η (pinnedSplitting X i j)).trans ?_
  rw [harg]
  rw [DerivedCategory.homologyFromSingleLinearEquiv_comp]
  rw [homologyFromSingle_pinnedSplitting_comp]
  rw [cupPairing_eq]
  simp only [Category.assoc]

end Stacks.Cohomology.DerivedGlobalCupProduct

end
