module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductSection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductThroughThePoint

/-!
# Section 0FKU in full, with no parameter

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductSection` states the
recipe of Cohomology, Section 20.31 for the global cup product built from an *arbitrary* one-point
comparison, whose tensor comparison is unconstrained (it may be zero, and then so is `μ`). This
file states the section for the cup product of the source: the instance at
`Stacks.Cohomology.DerivedGlobalCupProduct.canonicalOnePointComparison`, the one-point comparison
attached to the morphism of ringed spaces `π : (S, 𝒪_S) ⟶ ({*}, Γ(S, 𝒪_S))`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.section_cupProduct_canonical` — **Section 0FKU in
  full**, with no parameter, on an arbitrary ringed space: both displays of the section
  conjoined for `μ = globalCupProduct (canonicalOnePointComparison S)`. Besides the conjuncts of
  `section_cupProduct` at that comparison it states that `μ`, read through the Leray
  identification of `RΓ(S, -)` with `RΓ({*}, Rπ_*(-))`, *is* the relative cup product of Tag 0B68
  for `π` read through the one-point identification `D({*}, A) = D(A)`, which is the source's
  definition of `μ`, and that the tensor comparison it uses (that of Tag 079U) is invertible.

## References

* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomology, Section 0FKU in full, with no parameter: both displays of the section, for the
global cup product of an arbitrary ringed space.**

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)` and `π : (S, 𝒪_S) ⟶ ({*}, A)` the morphism of
ringed spaces of Tag 01BH. The global cup product `μ` is
`globalCupProduct (canonicalOnePointComparison S)` (also spelled `cupProductOnSpace S`), a
morphism `RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋_{𝒪_S} M)` in `D(A)` for all `K, M ∈ D(𝒪_S)`. The
conjuncts are:

* the canonical one-point comparison is the one presented by `Lπ^*` through the one-point
  identification `D(A) ≌ D(𝒪_{({*}, A)})`, the adjunction `Lπ^* ⊣ Rπ_*` of Tag 079W, the Leray
  identification `RΓ({*}, Rπ_*(-)) ≅ RΓ(S, -)` of Tag 0D5W, and the comparison of Tag 079U
  (`canonicalPointPresentation S` and `canonicalSectionsIso S`);
* `μ` is the relative cup product construction (Tag 0B68) for that adjunction and comparison;
* **the source's definition of `μ`**: read through the Leray identification in each factor and at
  the target, `μ` is the doubled-counit morphism of the canonical presentation, and that morphism
  is, across the equality of rings `Γ({*}, 𝒪) = A`, the relative cup product of Tag 0B68 for `π`
  at `(K, M)` composed with the identification of `⊗^𝐋_A` with `⊗^𝐋_{𝒪_{({*}, A)}}` — that is,
  "the relative cup product for `f : (X, 𝒪_X) ⟶ (pt, A)` via `D(pt, A) = D(A)`";
* the tensor comparison is invertible (so in particular it is not the zero morphism);
* `μ` is natural in the two complexes jointly;
* the second display: the pairings `∪ : Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋_{𝒪_S} M)` are the
  tensoring of classes of More on Algebra, Section 15.64 followed by `Hⁱ⁺ʲ(μ)`, i.e.
  `ξ ∪ η = μ(ξ ⊗ η)`.

The numbered items of Section 20.31 are excluded, each carrying its own tag: Lemma 20.31.1 is
Tag 0FP2, Remark 20.31.2 is Tag 0G6W, Lemma 20.31.3 is Tag 0FP3, Lemma 20.31.4 is Tag 0FKV, and
Lemmas 20.31.5 to 20.31.8 are Tags 0FP4, 0FP5, 0FP6 and 0H99. -/
@[stacks 0FKU "Section 20.31 IN FULL, both displays, on an arbitrary ringed space and with no
  parameter: the global cup product μ : RΓ(X, K) ⊗^L_A RΓ(X, M) ⟶ RΓ(X, K ⊗^L M) in D(A) is
  globalCupProduct (canonicalOnePointComparison X), built from Lπ^* ⊣ Rπ_* for the morphism
  π : (X, O_X) ⟶ (pt, A) and the comparison of Tag 079U (first conjunct); it is the relative cup
  product recipe for that datum (second); read through the Leray identification it is the
  relative cup product of Tag 0B68 for π via D(pt, A) = D(A) (third and fourth); its tensor
  comparison is invertible (fifth); it is natural in both complexes (sixth); and the induced
  pairings H^i(X, K) × H^j(X, M) ⟶ H^{i+j}(X, K ⊗^L M) are ξ ∪ η = μ(ξ ⊗ η) with the tensoring
  of classes of More on Algebra, Section 15.64 (seventh). The numbered items of the section are
  excluded, each having its own tag: 0FP2, 0G6W, 0FP3, 0FKV, 0FP4, 0FP5, 0FP6, 0H99"]
theorem section_cupProduct_canonical (S : RingedSpace.{u, u}) :
    canonicalOnePointComparison S =
        (canonicalPointPresentation S).toComparison S (baseRing_coeffPoint S)
          (canonicalSectionsIso S) ∧
    (∀ K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      (globalCupProduct (canonicalOnePointComparison S)).app (K, M) =
        adjunctionBitensorMap (canonicalOnePointComparison S).adjunction
          (Functor.uncurry.obj (tensorBase S))
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (canonicalOnePointComparison S).tensorComparison K M) ∧
    (∀ K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      (Functor.uncurry.obj (tensorBase S)).map
            ((canonicalSectionsIso S).hom.app K ×ₘ (canonicalSectionsIso S).hom.app M) ≫
          (globalCupProduct (canonicalOnePointComparison S)).app (K, M) =
        (canonicalPointPresentation S).bitensorMap S (baseRing_coeffPoint S) K M ≫
          (canonicalSectionsIso S).hom.app ((spaceTensor S).obj (K, M))) ∧
    (∀ K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      HEq ((canonicalPointPresentation S).bitensorMap S (baseRing_coeffPoint S) K M)
        (adjunctionBitensorMap (onePointDerivedAdjunction ↥(baseRing S))
            (coeffTensor S) (pointTensor S)
            (onePointDerivedTensorIso ↥(baseRing S)).hom
            ((derivedPushforward (toCoeffPoint S)).obj K)
            ((derivedPushforward (toCoeffPoint S)).obj M) ≫
          (baseSections (coeffPt S)).map (relativeCupProduct (toCoeffPoint S) K M))) ∧
    IsIso (canonicalOnePointComparison S).tensorComparison ∧
    (∀ K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      ∀ (k : K ⟶ K') (m : M ⟶ M'),
      (Functor.uncurry.obj (tensorBase S)).map
            ((baseSections S).map k ×ₘ (baseSections S).map m) ≫
          (globalCupProduct (canonicalOnePointComparison S)).app (K', M') =
        (globalCupProduct (canonicalOnePointComparison S)).app (K, M) ≫
          (baseSections S).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (k ×ₘ m))) ∧
    (∀ (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ),
      ∃ p : RingTheory.TorProducts.CohomologyTensorProduct ((baseSections S).obj K)
          ((baseSections S).obj M) i j,
        cupPairing (globalCupProduct (canonicalOnePointComparison S)) K M i j =
          p.map ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
            ((globalCupProduct (canonicalOnePointComparison S)).app (K, M))) :=
  ⟨rfl, (section_cupProduct (canonicalOnePointComparison S)).1,
    globalCupProduct_canonicalOnePointComparison_app S,
    canonicalPointPresentation_bitensorMap_heq S,
    inferInstance,
    (section_cupProduct (canonicalOnePointComparison S)).2.1,
    (section_cupProduct (canonicalOnePointComparison S)).2.2⟩

end Stacks.Cohomology.DerivedGlobalCupProduct

end
