module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupWithCohomologyClass

/-!
# The generator of `Hⁱ(A[-i])`, and the splitting `A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` it pins down

Let `(X, 𝒪_X)` be a ringed space and `A = Γ(X, 𝒪_X)`.  Remark 0G6W reads a class
`ξ ∈ Hⁱ(X, K)` as a morphism `A[-i] ⟶ RΓ(X, K)` in `D(A)`, which is
`Stacks.Cohomology.DerivedGlobalCupProduct.classRepresentative`.  Under that reading `ξ` is the
image of one distinguished class, the class of the identity of `A[-i]`; this file names it and
records that it generates.

It then defines a morphism `χ : A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` of the kind over which
`Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClass` quantifies. The free
module `A` is projective, so `A[-i-j]` corepresents `Hⁱ⁺ʲ` on all of `D(A)` and a class in
`Hⁱ⁺ʲ(A[-i] ⊗^𝐋_A A[-j])` is the class of exactly one morphism out of `A[-i-j]`; `χ` is the one
whose class is the tensoring of the two generators by the pairing of Tag 068H.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.baseGenerator` — the generator of `Hⁱ(A[-i])`, the
  class of `𝟙 (A[-i])`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.tensorGenerator` — the tensoring of the generators
  of `Hⁱ(A[-i])` and `Hʲ(A[-j])`, a class in `Hⁱ⁺ʲ(A[-i] ⊗^𝐋_A A[-j])`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.pinnedSplitting` — the morphism
  `A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` whose class is `tensorGenerator`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.baseGenerator_comp` — **the generator generates**:
  a class `ξ ∈ Hⁱ(X, K)` is the image of `baseGenerator` under `Hⁱ` of the morphism representing
  it.
* `Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_pinnedSplitting` — the class of
  `pinnedSplitting` is `tensorGenerator`.

## Implementation notes

The identification `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` of the source is
`Stacks.Cohomology.DerivedGlobalCupProduct.baseShiftSplitting`, which is built from
`baseShiftTensorIso` and hence from the `commShift_left` datum of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`; that datum comes from a bare
existence statement and no equation about it is recorded, so the class of `baseShiftSplitting`
cannot be computed. `pinnedSplitting` instead produces the morphism from the class it must have,
and nothing in `baseGenerator`, `tensorGenerator` or `pinnedSplitting` mentions `commShift_left`.
Whether the two agree is exactly the normalisation of the `commShift_left` datum.

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

/-- **The generator of `Hⁱ(A[-i])`** for `A = Γ(X, 𝒪_X)`: the class of the identity of `A[-i]`
under the corepresentability isomorphism `Hom_{D(A)}(A[-i], A[-i]) ≅ Hⁱ(A[-i])` of Tag 06XS. -/
def baseGenerator (i : ℤ) :
    ModuleCat.of (baseRing X) (baseRing X) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).obj (baseShift X i) :=
  DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    (baseShift X i) i (baseRing X) (𝟙 (baseShift X i))

variable {X}

/-- **The generator generates.**  A class `ξ ∈ Hⁱ(X, K)` is the image of the generator of
`Hⁱ(A[-i])` under `Hⁱ` of the morphism `A[-i] ⟶ RΓ(X, K)` representing it. -/
theorem baseGenerator_comp (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    baseGenerator X i ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
          (classRepresentative K i ξ) = ξ := by
  rw [baseGenerator, ← DerivedCategory.homologyFromSingleLinearEquiv_comp, Category.id_comp,
    classRepresentative]
  exact (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    ((baseSections X).obj K) i (baseRing X)).apply_symm_apply ξ

variable (X)

/-- **The tensoring of the two generators**, a class in `Hⁱ⁺ʲ(A[-i] ⊗^𝐋_A A[-j])`: the pairing
of Tag 068H applied to the generators of `Hⁱ(A[-i])` and of `Hʲ(A[-j])`. -/
def tensorGenerator (i j : ℤ) :
    ModuleCat.of (baseRing X) (baseRing X) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).obj
        (((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) :=
  (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫
    (baseGenerator X i ⊗ₘ baseGenerator X j) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct (baseShift X i) (baseShift X j) i j).map

/-- **The splitting `A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` pinned by its class.**  `A[-i-j]`
corepresents `Hⁱ⁺ʲ` on `D(A)` by Tag 06XS, so there is exactly one morphism
`A[-i-j] ⟶ A[-i] ⊗^𝐋_A A[-j]` whose class is the tensoring of the two generators; this is it. -/
def pinnedSplitting (i j : ℤ) :
    baseShift X (i + j) ⟶ ((tensorBase X).obj (baseShift X i)).obj (baseShift X j) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    (((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) (i + j) (baseRing X)).symm
      (tensorGenerator X i j)

/-- The class of `Stacks.Cohomology.DerivedGlobalCupProduct.pinnedSplitting` in
`Hⁱ⁺ʲ(A[-i] ⊗^𝐋_A A[-j])` is the tensoring of the two generators. -/
theorem homologyFromSingle_pinnedSplitting (i j : ℤ) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
        (((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) (i + j) (baseRing X)
        (pinnedSplitting X i j) = tensorGenerator X i j :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
    (((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) (i + j)
      (baseRing X)).apply_symm_apply _

end Stacks.Cohomology.DerivedGlobalCupProduct

end
