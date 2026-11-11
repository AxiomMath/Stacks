module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct

/-!
# Section 0FKU in full: both displays of the global cup product

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct`
constructs the global
cup product `μ : RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋_{𝒪_S} M)` from a one-point comparison and
the pairings it induces on cohomology. This file conjoins the two displays of Section 20.31 with
the source's definitions of them, as one statement, for an arbitrary one-point comparison. The
statement at the canonical one-point comparison, which is the one the source uses, is in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductSectionCanonical`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.section_cupProduct` — the same three conjuncts of
  the recipe, for the global cup product built from an *arbitrary* one-point comparison. Its
  tensor comparison is an arbitrary morphism of bifunctors (it may be zero, and then so is `μ`),
  so this statement does not single out the cup product of the source; it carries no tag. Its
  conjuncts are `μ` together with the source's definition of it as the relative cup product
  of Tag 0B68, its joint naturality, and the induced pairings with the two-step recipe
  `ξ ∪ η = μ(ξ ⊗ η)`. The numbered items of Section 20.31 are excluded, each carrying its own
  tag: Lemma 20.31.1 is Tag 0FP2, Remark 20.31.2 is Tag 0G6W, Lemma 20.31.3 is Tag 0FP3, Lemma
  20.31.4 is Tag 0FKV and Lemmas 20.31.5 to 20.31.8 are Tags 0FP4, 0FP5, 0FP6 and 0H99.

## References

* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}}

/-- **The recipe of Cohomology, Section 0FKU, for the global cup product built from an arbitrary
one-point comparison.** Section 0FKU itself is `section_cupProduct_canonical`, the instance at
the canonical one-point comparison.

The conjuncts are, in the order the source states them:

* the first display, `μ : RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋_{𝒪_S} M)`, together with the
  source's *definition* of it — it is the relative cup product of Tag 0B68, namely the adjoint
  transpose of the tensor comparison followed by the counit of `L ⊣ RΓ(S, -)` in both tensor
  factors, which is what "we define it as the relative cup product for the morphism of ringed
  spaces `f : (S, 𝒪_S) ⟶ (pt, A)` via `D(pt, A) = D(A)`" says once `Rf_*` is read as `RΓ(S, -)`;
* that `μ` is natural in the two complexes jointly, so that it is a morphism of bifunctors on
  `D(𝒪_S) × D(𝒪_S)` and not a separate map for each pair;
* the second display, the induced pairings
  `∪ : Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋_{𝒪_S} M)`, together with the source's two-step
  recipe `ξ ∪ η = μ(ξ ⊗ η)`: the tensoring step is a
  `RingTheory.TorProducts.CohomologyTensorProduct`, i.e. a pairing sending the tensor of the
  classes of two cocycles to the class of their tensor, which is Equation 15.64.0.1 of Tag 068H
  and is the source's "we can first tensor them, see More on Algebra, Section 15.64"; the second
  step is `Hⁱ⁺ʲ(μ)`.

The one-point comparison `c` is an arbitrary parameter: a left adjoint of `RΓ(S, -)` together
with an *unconstrained* morphism of bifunctors `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`, which need not
be the comparison of Tag 079U, need not be invertible and may be zero, in which case `μ` is zero.
So this theorem is the recipe of the section for an arbitrary such datum, and does not by itself
single out the cup product of the source. The source's `μ` is the instance at
`canonicalOnePointComparison S`, and Section 0FKU is stated for it, with no parameter, in
`section_cupProduct_canonical`, which carries the tag.

The remaining numbered items of Section 20.31 are not conjoined here because each carries its own
tag: Lemma 20.31.1 is Tag 0FP2, Remark 20.31.2 is Tag 0G6W, Lemma 20.31.3 is Tag 0FP3, Lemma
20.31.4 is Tag 0FKV, and Lemmas 20.31.5 to 20.31.8 are Tags 0FP4, 0FP5, 0FP6 and 0H99. What is
left to Tag 0FKU itself is the construction of the two displays, which this states for an
arbitrary `c` and `section_cupProduct_canonical` states for the canonical one. -/
theorem section_cupProduct (c : OnePointComparison S) :
    (∀ K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      (globalCupProduct c).app (K, M) =
        adjunctionBitensorMap c.adjunction (Functor.uncurry.obj (tensorBase S))
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison K M) ∧
    (∀ K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      ∀ (k : K ⟶ K') (m : M ⟶ M'),
      (Functor.uncurry.obj (tensorBase S)).map
            ((baseSections S).map k ×ₘ (baseSections S).map m) ≫
          (globalCupProduct c).app (K', M') =
        (globalCupProduct c).app (K, M) ≫
          (baseSections S).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (k ×ₘ m))) ∧
    (∀ (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ),
      ∃ p : RingTheory.TorProducts.CohomologyTensorProduct ((baseSections S).obj K)
          ((baseSections S).obj M) i j,
        cupPairing (globalCupProduct c) K M i j =
          p.map ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
            ((globalCupProduct c).app (K, M))) :=
  ⟨fun K M => globalCupProduct_app c K M,
    fun _ _ _ _ k m => globalCupProduct_naturality (globalCupProduct c) k m,
    fun K M i j => cupPairing_tensorStep (globalCupProduct c) K M i j⟩

end Stacks.Cohomology.DerivedGlobalCupProduct

end
