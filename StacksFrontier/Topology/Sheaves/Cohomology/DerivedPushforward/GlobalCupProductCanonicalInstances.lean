module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupClassOnCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# Remark 0G6W and Tag 0G49 at the canonical global cup product

Let `(X, 𝒪_X)` be a ringed space and set `A = Γ(X, 𝒪_X)`. The cup product with a cohomology class
of Remark 0G6W and the Künneth map for two module sheaves of Tag 0G49 are defined for a global cup
product `μ` of Cohomology, Section 0FKU given as a parameter: a
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison` for the first two and a
`Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` for the third. This file states them at the
canonical global cup product `Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`, which
exists on an arbitrary ringed space.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.onePointComparisonCanonical`: the canonical one-point comparison
  on an arbitrary ringed space.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClassCanonical`: the map `ξ ∪ -` of
  Remark 0G6W at the canonical global cup product.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesCanonical`: the Künneth map for two module
  sheaves of Tag 0G49 at the canonical global cup product.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesSchemeCanonical`: the same map at the fibre
  product of two schemes.

## Main results

* `Stacks.Cohomology.GlobalKunneth.globalCupProduct_onePointComparisonCanonical`: the global cup
  product of the canonical one-point comparison is `globalCupProductCanonical`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClassCanonical` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.homologyFromSingle_cupWithClassCanonical_cupPairing`:
  the second clause of Remark 0G6W at the canonical global cup product, in the composition shape of
  Tag 0FP2 and against the pairing of Section 0FKU respectively.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesCanonical_naturality_derived`: the derived
  Künneth map of Tag 0G7V underlying the Künneth map for two module sheaves is natural in the two
  sheaves.

## References

* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### The canonical one-point comparison -/

/-- **The canonical one-point comparison on an arbitrary ringed space**: the left adjoint `L` of
derived global sections of Tag 079W and Tag 0D5W, together with the comparison
`L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y` of `Stacks.Cohomology.GlobalKunneth.baseTensorComparison`,
assembled from the one-point tensor comparison, the restriction-of-scalars comparison and the
derived-pullback monoidality of Tag 079U. -/
def onePointComparisonCanonical (S : RingedSpace.{u, u}) : OnePointComparison S :=
  onePointComparisonOfBaseTensorComparison S (baseTensorComparison S)

/-- The global cup product of the canonical one-point comparison is the canonical global cup
product `globalCupProductCanonical`. -/
theorem globalCupProduct_onePointComparisonCanonical (S : RingedSpace.{u, u}) :
    globalCupProduct (onePointComparisonCanonical S) = globalCupProductCanonical S :=
  rfl

end Stacks.Cohomology.GlobalKunneth

namespace Stacks.Cohomology.DerivedGlobalCupProduct

open Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-! ### Remark 0G6W at the canonical global cup product -/

/-- **The map `ξ ∪ -` at the canonical global cup product.** For a class `ξ ∈ Hⁱ(X, K)` it is the
morphism

`ξ ∪ - : RΓ(X, M)[-i] ⟶ RΓ(X, K ⊗^𝐋_{𝒪_X} M)`

in `D(A)` for `A = Γ(X, 𝒪_X)`, namely the composition of the identification
`RΓ(X, M)[-i] = A[-i] ⊗^𝐋_A RΓ(X, M)`, of `ξ ⊗ 1` for the morphism representing `ξ`, and of the
global cup product `μ` of Section 0FKU, `globalCupProductCanonical`. -/
@[stacks 0G6W "the construction of the map ξ ∪ - : RΓ(X, M)[-i] ⟶ RΓ(X, K ⊗^L M) attached to a \
  class ξ ∈ H^i(X, K), the first clause of the remark, at the global cup product μ of Section \
  0FKU, `globalCupProductCanonical`, on an arbitrary ringed space"]
def cupWithClassCanonical (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (i : ℤ) (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    ((baseSections X).obj M)⟦-i⟧ ⟶
      (baseSections X).obj (((derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  cupWithClass (onePointComparisonCanonical X) K M i ξ

/-- `cupWithClassCanonical` is `cupWithClass` at the canonical one-point comparison. -/
theorem cupWithClassCanonical_eq (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (i : ℤ) (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    cupWithClassCanonical X K M i ξ = cupWithClass (onePointComparisonCanonical X) K M i ξ :=
  rfl

/-- On cohomology the map `ξ ∪ -` at the canonical global cup product is the cup product with `ξ`:
for `ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(X, M)`, the map `Hⁱ⁺ʲ(ξ ∪ -)` carries the class of `η`, read in
`Hⁱ⁺ʲ(RΓ(X, M)[-i])` through the identifications `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` and
`A[-i] ⊗^𝐋_A RΓ(X, M) = RΓ(X, M)[-i]`, to the class of the cup product `ξ ∪ η` in the composition
shape of Section 0FKU and Tag 0FP2. -/
@[stacks 0G6W "the second clause of the remark: on cohomology ξ ∪ - is the cup product with ξ, \
  for the global cup product `globalCupProductCanonical`.  The cup product of two classes is in \
  the composition shape of Section 0FKU and Tag 0FP2, A[-i-j] ⟶ A[-i] ⊗ᴸ A[-j] ⟶ RΓ(X, K) ⊗ᴸ \
  RΓ(X, M) ⟶ RΓ(X, K ⊗ᴸ M), for every identification χ of A[-i-j] with A[-i] ⊗ᴸ A[-j]"]
theorem homologyFromSingle_cupWithClassCanonical
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j)
    (χ : baseShift X (i + j) ⟶ ((tensorBase X).obj (baseShift X i)).obj (baseShift X j)) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
          (((baseSections X).obj M)⟦-i⟧) (i + j) (baseRing X)
          (χ ≫ ((tensorBase X).obj (baseShift X i)).map (classRepresentative M j η) ≫
            (baseShiftTensorIso X i ((baseSections X).obj M)).hom) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (cupWithClassCanonical X K M i ξ) =
      DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
        ((baseSections X).obj (((derivedTensorProductFunctor X.sheaf).obj K).obj M)) (i + j)
        (baseRing X)
        (χ ≫ ((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
          ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η) ≫
            (globalCupProductCanonical X).app (K, M)) :=
  homologyFromSingle_cupWithClass (onePointComparisonCanonical X) K M i j ξ η χ

/-- On cohomology, `Hⁱ⁺ʲ(ξ ∪ -)` at the canonical global cup product carries the class of `η` to
`ξ ∪ η` as `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing` defines it for the canonical
global cup product, the source's identification `A[-i-j] = A[-i] ⊗^𝐋_A A[-j]` being
`pinnedSplitting`. -/
@[stacks 0G6W "the second clause of the remark, with the cup product of two classes read against \
  the cohomology-level pairing `cupPairing` of Section 0FKU at the global cup product \
  `globalCupProductCanonical`: the tensoring of classes of Tag 068H followed by H^{i+j}(μ), which \
  is how the source defines ∪.  The source's identification A[-i-j] = A[-i] ⊗ᴸ A[-j] is \
  `pinnedSplitting`"]
theorem homologyFromSingle_cupWithClassCanonical_cupPairing
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing X) (baseRing X))
          (((baseSections X).obj M)⟦-i⟧) (i + j) (baseRing X)
          (pinnedSplitting X i j ≫
            ((tensorBase X).obj (baseShift X i)).map (classRepresentative M j η) ≫
              (baseShiftTensorIso X i ((baseSections X).obj M)).hom) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (cupWithClassCanonical X K M i ξ) =
      (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
        cupPairing (globalCupProductCanonical X) K M i j :=
  homologyFromSingle_cupWithClass_cupPairing (onePointComparisonCanonical X) K M i j ξ η

end Stacks.Cohomology.DerivedGlobalCupProduct

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### Tag 0G49 at the canonical global cup product -/

section

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- **The global Künneth map for two module sheaves at the canonical global cup product.**

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(W, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

in `D(A)` for `A = Γ(S, 𝒪_S)`, where `p ≫ a = f = q ≫ b`; the source takes `W = X ×_S Y` with
its two projections.  It is `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` at the
canonical global cup product of Section 0FKU. -/
@[stacks 0G49 "the map, at the A-linear global cup product `globalCupProductCanonical` of \
  Section 0FKU on the base"]
def kunnethMapOfSheavesCanonical (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    ((tensorBase S).obj ((sectionsOverBase a).obj (singleD F))).obj
        ((sectionsOverBase b).obj (singleD G)) ⟶
      (sectionsOverBase f).obj
        (singleD (sheafTensorObj ((modulePullback p).obj F) ((modulePullback q).obj G))) :=
  kunnethMapOfSheaves a b p q f hp hq (globalCupProductCanonical S) F G

/-- `kunnethMapOfSheavesCanonical` is `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves` at the
canonical global cup product. -/
theorem kunnethMapOfSheavesCanonical_eq (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    kunnethMapOfSheavesCanonical a b p q f hp hq F G =
      kunnethMapOfSheaves a b p q f hp hq (globalCupProductCanonical S) F G :=
  rfl

/-- `kunnethMapOfSheavesCanonical` is the map built from the one-point tensor comparison alone, at
the canonical comparison `Stacks.Cohomology.GlobalKunneth.baseTensorComparison`. -/
theorem kunnethMapOfSheavesCanonical_eq_fromBaseTensorComparison (F : Modules X.sheaf)
    (G : Modules Y.sheaf) :
    kunnethMapOfSheavesCanonical a b p q f hp hq F G =
      kunnethMapOfSheavesFromBaseTensorComparison a b p q f hp hq (baseTensorComparison S) F G :=
  rfl

/-- The Künneth map for two module sheaves at the canonical global cup product is the derived
Künneth map `kunnethGlobalMapCanonical` at the two sheaves placed in degree zero, followed by
derived global sections of the canonical comparison from the derived tensor product of the derived
pullbacks to the ordinary tensor product of the ordinary pullbacks. -/
@[stacks 0G49 "the map is the derived map at the sheaves in degree zero: both sides are at the \
  canonical global cup product, the right-hand side being `kunnethGlobalMapCanonical` of Tag 0G7V"]
theorem kunnethMapOfSheavesCanonical_eq_kunnethGlobalMapCanonical (F : Modules X.sheaf)
    (G : Modules Y.sheaf) :
    kunnethMapOfSheavesCanonical a b p q f hp hq F G =
      kunnethGlobalMapCanonical a b p q f hp hq (singleD F) (singleD G) ≫
        (sectionsOverBase f).map (externalTensorComparison p q F G) :=
  rfl

/-- The derived Künneth map `kunnethGlobalMapCanonical` at sheaves placed in degree zero, the
first factor of `kunnethMapOfSheavesCanonical`, is natural in the two sheaves `ℱ` and `𝒢`. -/
@[stacks 0G49 "naturality inherited from the derived map, at the canonical global cup product"]
theorem kunnethMapOfSheavesCanonical_naturality_derived
    {F F' : Modules X.sheaf} {G G' : Modules Y.sheaf} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsOverBase a).map (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor (Modules X.sheaf) 0).map φ)) ×ₘ
            (sectionsOverBase b).map (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor (Modules Y.sheaf) 0).map ψ))) ≫
        kunnethGlobalMapCanonical a b p q f hp hq (singleD F') (singleD G') =
      kunnethGlobalMapCanonical a b p q f hp hq (singleD F) (singleD G) ≫
        (sectionsOverBase f).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullback p).map (DerivedCategory.Q.map
                ((CochainComplex.singleFunctor (Modules X.sheaf) 0).map φ)) ×ₘ
              (derivedPullback q).map (DerivedCategory.Q.map
                ((CochainComplex.singleFunctor (Modules Y.sheaf) 0).map ψ)))) :=
  kunnethMapOfSheaves_naturality_derived a b p q f hp hq (globalCupProductCanonical S) φ ψ

end

/-! ### Tag 0G49 at the fibre product of two schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The global Künneth map at the fibre product of two schemes, at the canonical global cup
product.** For schemes `a : X ⟶ S` and `b : Y ⟶ S` over a base, `A = Γ(S, 𝒪_S)`, an
`𝒪_X`-module `ℱ` and an `𝒪_Y`-module `𝒢`, the canonical map

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗_{𝒪_{X ×_S Y}} q^*𝒢)`

in `D(A)`, where `p` and `q` are the two projections of `X ×_S Y` and the target is the external
tensor product of Tag 0G46 placed in degree zero. -/
@[stacks 0G49 "the map at X ×_S Y, at the global cup product `globalCupProductCanonical` on \
  the base"]
def kunnethMapOfSheavesSchemeCanonical (F : X.Modules) (G : Y.Modules) :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase a.toLRSHom.toShHom).obj (singleD F))).obj
        ((sectionsOverBase b.toLRSHom.toShHom).obj (singleD G)) ⟶
      (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (singleD (externalTensorProduct a b F G)) :=
  kunnethMapOfSheavesScheme a b (globalCupProductCanonical S.toRingedSpace) F G

/-- `kunnethMapOfSheavesSchemeCanonical` is
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesScheme` at the canonical global cup product. -/
theorem kunnethMapOfSheavesSchemeCanonical_eq (F : X.Modules) (G : Y.Modules) :
    kunnethMapOfSheavesSchemeCanonical a b F G =
      kunnethMapOfSheavesScheme a b (globalCupProductCanonical S.toRingedSpace) F G :=
  rfl

/-- At the fibre product of two schemes, the Künneth map for two module sheaves at the canonical
global cup product is the derived Künneth map `kunnethGlobalMapSchemeCanonical` at the two sheaves
placed in degree zero, followed by derived global sections of `externalTensorComparison`. -/
@[stacks 0G49 "the map at the fibre product is the derived map at the sheaves in degree zero: \
  both sides are at the canonical global cup product, the right-hand side being \
  `kunnethGlobalMapSchemeCanonical` of Tag 0G7V"]
theorem kunnethMapOfSheavesSchemeCanonical_eq_kunnethGlobalMapSchemeCanonical
    (F : X.Modules) (G : Y.Modules) :
    kunnethMapOfSheavesSchemeCanonical a b F G =
      kunnethGlobalMapSchemeCanonical a b (singleD F) (singleD G) ≫
        (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
          (externalTensorComparison (pullback.fst a b).toLRSHom.toShHom
            (pullback.snd a b).toLRSHom.toShHom F G) :=
  rfl

end Schemes

end Stacks.Cohomology.GlobalKunneth

end
