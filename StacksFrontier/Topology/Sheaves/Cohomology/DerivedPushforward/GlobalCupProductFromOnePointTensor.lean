module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LeftAdjointOfDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison

/-!
# The global cup product from the one-point tensor comparison

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`. A
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S` consists of a functor
`L : D(A) ⥤ D(𝒪_S)`, an adjunction `L ⊣ RΓ(S, -)`, and a comparison of bifunctors
`L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`. This file constructs one from a comparison

`E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪_{({*}, A)}} E y`

for `E : D(A) ⥤ D(𝒪_{({*}, A)})` the one-point identification on derived categories, using the
left adjoint of derived global sections and the derived-pullback monoidality of Tag 079U. From
such a comparison it then defines the global cup product of Section 0FKU, the pairings on
cohomology, and the Künneth map for two module sheaves of Tag 0G49.

All declarations are in the namespace `Stacks.Cohomology.DerivedSectionsLeftAdjoint`.

## Main definitions

* `baseToPoint`: `E`, the one-point identification on derived categories: restriction of scalars
  along `π^♯` followed by the identification `D(Γ({*}, 𝒪)) ≅ D(𝒪_{({*}, A)})`.
* `BaseTensorComparison`: the type of morphisms of bifunctors
  `E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪_{pt}} E y`.
* `onePointComparisonOfBaseTensorComparison`: the `OnePointComparison S` built from a
  `BaseTensorComparison S`.
* `globalCupProductOfBaseTensorComparison`: the global cup product `μ` of Section 0FKU built
  from a `BaseTensorComparison S`.
* `cupPairingOfBaseTensorComparison`: the pairings `Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋 M)`
  of that cup product.
* `kunnethMapOfSheavesFromBaseTensorComparison`: the Künneth map for two module sheaves of
  Tag 0G49 built from a `BaseTensorComparison S`.

## Main results

* `derivedBaseExtension_eq`: the left adjoint of derived global sections is `E` followed by
  `Lπ^*`.
* `onePointComparisonOfBaseTensorComparison_tensorComparison`: the comparison of the produced
  `OnePointComparison` is the given one-point comparison whiskered by `Lπ^*`, followed by the
  derived-pullback monoidality of Tag 079U.
* `kunnethMapOfSheavesFromBaseTensorComparison_eq`: the Künneth map so obtained is
  `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` at the produced cup product.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsLeftAdjoint

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-! ### The one-point identification on derived categories -/

/-- **The one-point identification on derived categories**, `E : D(A) ⥤ D(𝒪_{({*}, A)})` for
`A = Γ(S, 𝒪_S)`: restriction of scalars along `π^♯`, followed by the identification of
`Γ({*}, 𝒪)`-modules with sheaves of modules on the point. -/
abbrev baseToPoint : DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (basePoint S))) :=
  (basePointRestrict S).functor.mapDerivedCategory ⋙ basePointExtension S

/-- The left adjoint of derived global sections is `E` followed by the derived pullback along the
structure morphism to the coefficient point. -/
theorem derivedBaseExtension_eq :
    derivedBaseExtension S = baseToPoint S ⋙ derivedPullback (toBasePoint S) :=
  rfl

/-! ### One-point tensor comparisons -/

/-- **A one-point tensor comparison**: a morphism of bifunctors

`E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪_{({*}, A)}} E y`

for the one-point identification `E` of `baseToPoint`. -/
abbrev BaseTensorComparison :=
  Functor.uncurry.obj (tensorBase S) ⋙ baseToPoint S ⟶
    (baseToPoint S).prod (baseToPoint S) ⋙
      Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf)

/-- **A one-point comparison on a ringed space `S` from a one-point tensor comparison**: the
functor and the adjunction are those of `derivedBaseAdjunction`, and the comparison of bifunctors
is the given one whiskered by `Lπ^*`, followed by the derived-pullback monoidality of Tag 079U. -/
def onePointComparisonOfBaseTensorComparison (τ : BaseTensorComparison S) :
    OnePointComparison S where
  pullback := derivedBaseExtension S
  adjunction := derivedBaseAdjunction S
  tensorComparison :=
    Functor.whiskerRight τ (derivedPullback (toBasePoint S)) ≫
      Functor.whiskerLeft ((baseToPoint S).prod (baseToPoint S))
        (derivedPullbackTensorIso (toBasePoint S)).hom

/-- The comparison of bifunctors of the produced one-point comparison is the given one-point
comparison whiskered by `Lπ^*`, followed by the comparison of Tag 079U. -/
theorem onePointComparisonOfBaseTensorComparison_tensorComparison (τ : BaseTensorComparison S) :
    (onePointComparisonOfBaseTensorComparison S τ).tensorComparison =
      Functor.whiskerRight τ (derivedPullback (toBasePoint S)) ≫
        Functor.whiskerLeft ((baseToPoint S).prod (baseToPoint S))
          (derivedPullbackTensorIso (toBasePoint S)).hom :=
  rfl

/-- The functor of the produced one-point comparison is the left adjoint of derived global
sections. -/
theorem onePointComparisonOfBaseTensorComparison_pullback (τ : BaseTensorComparison S) :
    (onePointComparisonOfBaseTensorComparison S τ).pullback = derivedBaseExtension S :=
  rfl

/-! ### The global cup product and the Künneth map for sheaves -/

/-- **The global cup product `μ` of Section 0FKU on a ringed space, from a one-point tensor
comparison.** -/
def globalCupProductOfBaseTensorComparison (τ : BaseTensorComparison S) : GlobalCupProduct S :=
  globalCupProduct (onePointComparisonOfBaseTensorComparison S τ)

/-- The pairings `Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋 M)` of Section 0FKU from the same
datum. -/
def cupPairingOfBaseTensorComparison (τ : BaseTensorComparison S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    cohomologyModule K i ⊗ cohomologyModule M j ⟶
      cohomologyModule (((derivedTensorProductFunctor S.sheaf).obj K).obj M) (i + j) :=
  cupPairing (globalCupProductOfBaseTensorComparison S τ) K M i j

section Kunneth

variable {S} {X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- **The Künneth map for two module sheaves of Tag 0G49, from a one-point tensor comparison.**

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(W, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

in `D(A)` for `A = Γ(S, 𝒪_S)` and `p ≫ a = f = q ≫ b`, defined as
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` at the global cup product
`globalCupProductOfBaseTensorComparison`. -/
def kunnethMapOfSheavesFromBaseTensorComparison (τ : BaseTensorComparison S)
    (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    ((tensorBase S).obj ((sectionsOverBase a).obj (singleD F))).obj
        ((sectionsOverBase b).obj (singleD G)) ⟶
      (sectionsOverBase f).obj
        (singleD (sheafTensorObj ((modulePullback p).obj F) ((modulePullback q).obj G))) :=
  kunnethMapOfSheaves a b p q f hp hq (globalCupProductOfBaseTensorComparison S τ) F G

/-- The map is `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` at the produced cup
product. -/
theorem kunnethMapOfSheavesFromBaseTensorComparison_eq (τ : BaseTensorComparison S)
    (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    kunnethMapOfSheavesFromBaseTensorComparison a b p q f hp hq τ F G =
      kunnethMapOfSheaves a b p q f hp hq (globalCupProductOfBaseTensorComparison S τ) F G :=
  rfl

end Kunneth

end Stacks.Cohomology.DerivedSectionsLeftAdjoint

end
