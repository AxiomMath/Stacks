module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct

/-!
# Cup product with a cohomology class

Let `(X, 𝒪_X)` be a ringed space, let `K, M ∈ D(𝒪_X)` and set `A = Γ(X, 𝒪_X)`.  A class
`ξ ∈ Hⁱ(X, K)` is the same thing as a morphism `A[-i] ⟶ RΓ(X, K)` in `D(A)`: the free module
`A` is projective, so `A[-i]` corepresents `Hⁱ` on all of `D(A)`.  Tensoring such a morphism
with `RΓ(X, M)` over `A` and following it by the global cup product `μ` of Section 0FKU gives

`ξ ∪ - : RΓ(X, M)[-i] = A[-i] ⊗^𝐋_A RΓ(X, M) ⟶ RΓ(X, K) ⊗^𝐋_A RΓ(X, M) ⟶ RΓ(X, K ⊗^𝐋_{𝒪_X} M)`

and on cohomology this map is the cup product with `ξ`.  This is Remark 0G6W.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.baseShift` — the complex `A[-i]`, the free
  `A`-module of rank one placed in cohomological degree `i`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.baseShiftTensorIso` — the identification
  `A[-i] ⊗^𝐋_A N = N[-i]`, for an arbitrary `N ∈ D(A)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.baseShiftSplitting` — the identification
  `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.classRepresentative` — the morphism
  `A[-i] ⟶ RΓ(X, K)` representing a class `ξ ∈ Hⁱ(X, K)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass` — **the map `"ξ ∪ -"`** of Remark
  0G6W, `RΓ(X, M)[-i] ⟶ RΓ(X, K ⊗^𝐋_{𝒪_X} M)`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass_eq` — the defining composition, with
  the global cup product written out as the relative cup product construction of Tag 0B68.
* `Stacks.Cohomology.DerivedGlobalCupProduct.comp_cupWithClass` — composing `ξ ∪ -` with a
  morphism `η : W ⟶ RΓ(X, M)`, read through `baseShiftTensorIso`, is the cup product of `ξ` and
  `η` in the shape in which Tag 0FP2 states it.
* `Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClass` — **Remark 0G6W on
  cohomology**: the map induced by `ξ ∪ -` on `Hⁱ⁺ʲ` carries the class of `η ∈ Hʲ(X, M)` to the
  class of the cup product `ξ ∪ η`.

## Implementation notes

The only parameter is `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison`, the datum
from which `globalCupProduct` of Tag 0FKU is built. The identification
`A[-i] ⊗^𝐋_A N = N[-i]` is assembled from the Koszul symmetry, the right unit and the
first-variable shift commutation of the derived tensor product of Tag 064M, and the passage from
a class to its representing morphism is the inverse of the corepresentability isomorphism
`DerivedCategory.homologyFromSingleLinearEquiv`.

The identification `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` appears in `homologyFromSingle_cupWithClass` as
a universally quantified morphism `χ`, as it does in
`Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_comp_relativeCupProduct` for
Tag 0FP2; `baseShiftSplitting` is the canonical choice.

## References

* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-! ### The shifted free module of rank one, and the source's identifications -/

variable (X : RingedSpace.{u, u})

/-- **The complex `A[-i]`** over `A = Γ(X, 𝒪_X)`: the free `A`-module of rank one placed in
cohomological degree `i`.  It corepresents `Hⁱ` on `D(A)`, so a morphism `A[-i] ⟶ RΓ(X, K)` is
the same thing as a class in `Hⁱ(X, K)`. -/
abbrev baseShift (i : ℤ) : DerivedCategory (ModuleCat.{u} (baseRing X)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} (baseRing X)) i).obj
    (ModuleCat.of (baseRing X) (baseRing X))

/-- The left unit identification `A[0] ⊗^𝐋_A N = N` for the derived tensor product over
`A = Γ(X, 𝒪_X)`, obtained from the Koszul symmetry of Tag 0BYI and the right unit of
Tag 064M. -/
def baseUnitorIso (N : DerivedCategory (ModuleCat.{u} (baseRing X))) :
    ((tensorBase X).obj (baseShift X 0)).obj N ≅ N :=
  CochainComplex.DerivedTensor.derivedTensorProductCommIso (baseShift X 0) N ≪≫
    CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso N

/-- **The identification `A[-i] ⊗^𝐋_A N = N[-i]`** over `A = Γ(X, 𝒪_X)`: the shift is moved out
of the first tensor factor and the unit is cancelled. -/
def baseShiftTensorIso (i : ℤ) (N : DerivedCategory (ModuleCat.{u} (baseRing X))) :
    ((tensorBase X).obj (baseShift X i)).obj N ≅ N⟦-i⟧ := by
  letI : ((tensorBase X).flip.obj N).CommShift ℤ :=
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (baseRing X)).commShift_left N
  exact ((tensorBase X).flip.obj N).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} (baseRing X))).shiftIso (-i) i 0
        (neg_add_cancel i)).app (ModuleCat.of (baseRing X) (baseRing X))).symm ≪≫
    (((tensorBase X).flip.obj N).commShiftIso (-i)).app (baseShift X 0) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (-i)).mapIso
        (baseUnitorIso X N)

/-- **The identification `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]`** over `A = Γ(X, 𝒪_X)`, the canonical
choice: the shift identification `A[-i-j] = A[-j][-i]` followed by the inverse of
`baseShiftTensorIso` at `N = A[-j]`. -/
def baseShiftSplitting (i j : ℤ) :
    baseShift X (i + j) ≅ ((tensorBase X).obj (baseShift X i)).obj (baseShift X j) :=
  (((DerivedCategory.singleFunctors (ModuleCat.{u} (baseRing X))).shiftIso (-i) (i + j) j
      (by omega)).app (ModuleCat.of (baseRing X) (baseRing X))).symm ≪≫
    (baseShiftTensorIso X i (baseShift X j)).symm

/-! ### The map `"ξ ∪ -"` -/

variable {X}

/-- The morphism `A[-i] ⟶ RΓ(X, K)` in `D(A)` representing a class `ξ ∈ Hⁱ(X, K)`, for
`A = Γ(X, 𝒪_X)`.  The free module `A` is projective, so taking `Hⁱ` is an `A`-linear
isomorphism `Hom_{D(A)}(A[-i], RΓ(X, K)) ≅ Hⁱ(X, K)` by Tag 06XS; this is its inverse. -/
def classRepresentative (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    baseShift X i ⟶ (baseSections X).obj K :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    ((baseSections X).obj K) i (baseRing X)).symm ξ

/-- **The map `"ξ ∪ -"` for the global cup product of a one-point comparison `c`.**  For a class
`ξ ∈ Hⁱ(X, K)` it is the morphism

`ξ ∪ - : RΓ(X, M)[-i] ⟶ RΓ(X, K ⊗^𝐋_{𝒪_X} M)`

in `D(A)` for `A = Γ(X, 𝒪_X)`, namely the composition of the identification
`RΓ(X, M)[-i] = A[-i] ⊗^𝐋_A RΓ(X, M)`, of `ξ ⊗ 1` for the morphism representing `ξ`, and of
the global cup product `μ` of Section 0FKU built from `c`. -/
def cupWithClass (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    ((baseSections X).obj M)⟦-i⟧ ⟶
      (baseSections X).obj (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  (baseShiftTensorIso X i ((baseSections X).obj M)).inv ≫
    ((tensorBase X).map (classRepresentative K i ξ)).app ((baseSections X).obj M) ≫
      (globalCupProduct c).app (K, M)

/-- The composition defining `ξ ∪ -`, with the global cup product written out as the relative
cup product construction of Tag 0B68 for the one-point comparison. -/
theorem cupWithClass_eq (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    cupWithClass c K M i ξ =
      (baseShiftTensorIso X i ((baseSections X).obj M)).inv ≫
        ((tensorBase X).map (classRepresentative K i ξ)).app ((baseSections X).obj M) ≫
          adjunctionBitensorMap c.adjunction (Functor.uncurry.obj (tensorBase X))
            (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)) c.tensorComparison K M :=
  rfl

/-- Composing `ξ ∪ -` with a morphism `η : W ⟶ RΓ(X, M)`, read through the identification
`A[-i] ⊗^𝐋_A W = W[-i]`, gives the cup product of `ξ` and `η`: the tensor product `ξ ⊗ η` of
the two morphisms followed by the global cup product, which is the shape in which Tag 0FP2
states the cup product of two classes. -/
theorem comp_cupWithClass (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    {W : DerivedCategory (ModuleCat.{u} (baseRing X))} (η : W ⟶ (baseSections X).obj M) :
    ((tensorBase X).obj (baseShift X i)).map η ≫
        (baseShiftTensorIso X i ((baseSections X).obj M)).hom ≫ cupWithClass c K M i ξ =
      ((tensorBase X).map (classRepresentative K i ξ)).app W ≫
        ((tensorBase X).obj ((baseSections X).obj K)).map η ≫
          (globalCupProduct c).app (K, M) := by
  have h : (baseShiftTensorIso X i ((baseSections X).obj M)).hom ≫ cupWithClass c K M i ξ =
      ((tensorBase X).map (classRepresentative K i ξ)).app ((baseSections X).obj M) ≫
        (globalCupProduct c).app (K, M) :=
    (baseShiftTensorIso X i ((baseSections X).obj M)).hom_inv_id_assoc _
  rw [h]
  exact ((tensorBase X).map (classRepresentative K i ξ)).naturality_assoc η _

/-- **The cup product with a class on cohomology, for the global cup product of a one-point
comparison `c`.**  For classes `ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(X, M)`, the map `Hⁱ⁺ʲ(ξ ∪ -)` carries
the class of `η`, read in `Hⁱ⁺ʲ(RΓ(X, M)[-i])` through an identification
`χ : A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` and `A[-i] ⊗^𝐋_A RΓ(X, M) = RΓ(X, M)[-i]`, to the class of the
composition `A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j] ⟶ RΓ(X, K) ⊗^𝐋_A RΓ(X, M) ⟶ RΓ(X, K ⊗^𝐋_{𝒪_X} M)`
of Section 0FKU. -/
theorem homologyFromSingle_cupWithClass (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j)
    (χ : baseShift X (i + j) ⟶ ((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
          (((baseSections X).obj M)⟦-i⟧) (i + j) (baseRing X)
          (χ ≫ ((tensorBase X).obj (baseShift X i)).map (classRepresentative M j η) ≫
            (baseShiftTensorIso X i ((baseSections X).obj M)).hom) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (cupWithClass c K M i ξ) =
      DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
        ((baseSections X).obj (((derivedTensorProductFunctor X.sheaf).obj K).obj M)) (i + j)
        (baseRing X)
        (χ ≫ ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
          ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
            (globalCupProduct c).app (K, M)) := by
  have key : ((tensorBase X).obj (baseShift X i)).map (classRepresentative M j η) ≫
        (baseShiftTensorIso X i ((baseSections X).obj M)).hom ≫ cupWithClass c K M i ξ =
      ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
        ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
          (globalCupProduct c).app (K, M) :=
    comp_cupWithClass c K M i ξ (classRepresentative M j η)
  rw [← DerivedCategory.homologyFromSingleLinearEquiv_comp]
  congr 1
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => χ ≫ f) ((Category.assoc _ _ _).trans key))

end Stacks.Cohomology.DerivedGlobalCupProduct

end
