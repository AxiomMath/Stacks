module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CanonicalOnePointComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductComposition

/-!
# The global cup product of the canonical one-point comparison factors through the point

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, and let `π : S ⟶ ({*}, A)` be the morphism
of [Stacks, Tag 01BH]. The canonical one-point comparison of
`Stacks.Cohomology.DerivedGlobalCupProduct.canonicalOnePointComparison` is built from a
*composite* adjunction -- the derived one-point identification `D(A) ≌ D(𝒪_{({*}, A)})` followed
by `Lπ^* ⊣ Rπ_*` of [Stacks, Tag 079W] -- and from the *composite* tensor comparison
`Lπ^*(one-point comparison) ≫ (comparison of Tag 079U)`.

This file shows that the doubled-counit adjunction morphism of the composite adjunction at the
composite comparison is the one for the one-point adjunction at the pair `(Rπ_*K, Rπ_*M)`,
followed by derived global sections on the point of the relative cup product of
[Stacks, Tag 0B68] for `π`.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_ofNatIsoRight`: the abstract
  relative cup product is carried along a transport of the *right* adjoint alone, the comparison
  being untouched.
* `Stacks.Cohomology.DerivedGlobalCupProduct.canonicalPointPresentation_adjunctionBitensorMap`:
  the doubled-counit adjunction morphism of the canonical presentation factors through the point.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct_toComparison_app`: the global cup
  product of the one-point comparison a point presentation produces is the presentation's own
  doubled-counit adjunction morphism, conjugated by the identification of the presentation's
  right adjoint with `RΓ(S, -)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct_canonicalOnePointComparison_app`
  and `Stacks.Cohomology.DerivedGlobalCupProduct.canonicalPointPresentation_bitensorMap_heq`:
  **the factorization, for the global cup product of `canonicalOnePointComparison S` itself.**

## Implementation notes

`Stacks.Cohomology.DerivedGlobalCupProduct.PointPresentation.toComparison` is defined by
substituting away the equality of rings `h : A = Γ(S, 𝒪_S)`, and `subst` needs a free local on
one side of it. In a statement about `canonicalOnePointComparison S` neither side of
`baseRing_coeffPoint S` is free, so the square is proved for an arbitrary `(A, G, d, h, e)` and
then instantiated. For the same reason the presentation's own doubled-counit adjunction morphism,
which lives over `A`, reaches `Γ(S, 𝒪_S)` only as the transport `PointPresentation.bitensorMap`.

`coeffPt`, `coeffTensor`, `pointTensor` and `spaceTensor` name the four recurring spellings once.
Written out, the statement of the factorization exhausts the 200000-heartbeat budget on
`isDefEq`: `baseRing (coefficientPoint (baseRing S))` and
`baseRing (onePointRingedSpace ↥(baseRing S))` are definitionally equal through
`CommRingCat.of ↥(baseRing S) = baseRing S`, and the unifier re-derives that crossing once per
occurrence.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section TransportRight

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (cr : R ≅ R')
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract relative cup product is carried along a transport of the right adjoint
alone.** When only `R` is replaced, by `cr : R ≅ R'`, and the comparison `α` is unchanged, the
two doubled-counit adjunction morphisms are related by `cr` in each argument on the source and at
the tensor product on the target. -/
theorem adjunctionBitensorMap_ofNatIsoRight (G G' : D) :
    A.map (cr.hom.app G ×ₘ cr.hom.app G') ≫
        adjunctionBitensorMap (adj.ofNatIsoRight cr) A B α G G' =
      adjunctionBitensorMap adj A B α G G' ≫ cr.hom.app (B.obj (G, G')) := by
  refine adjunctionBitensorMap_transport adj (adj.ofNatIsoRight cr) (Iso.refl L) cr A B α α
    ?_ ?_ G G'
  · congr 1
    exact Adjunction.ext (by simp)
  · ext X
    simp only [Functor.comp_obj, Functor.prod_obj, Iso.refl_hom, Functor.whiskerLeft_id',
      Category.id_comp, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [show (NatTrans.prod (𝟙 L) (𝟙 L)).app X = 𝟙 ((L.prod L).obj X) from rfl]
    simp

end TransportRight

end Stacks.Cohomology.DerivedRelativeCupProduct

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-- The coefficient point of `A = Γ(S, 𝒪_S)`. -/
abbrev coeffPt : RingedSpace.{u, u} := onePointRingedSpace ↥(baseRing S)

/-- `⊗^𝐋_A` on `D(A)`, `A` the coefficient point's own ring of global functions. -/
abbrev coeffTensor := Functor.uncurry.obj (tensorBase (coeffPt S))

/-- `⊗^𝐋_{𝒪}` on the coefficient point. -/
abbrev pointTensor := Functor.uncurry.obj (derivedTensorProductFunctor (coeffPt S).sheaf)

/-- `⊗^𝐋_{𝒪_S}` on `S`. -/
abbrev spaceTensor := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)

/-- **The global cup product of the canonical presentation factors through the point.**  The
doubled-counit adjunction morphism of the composite adjunction
`E ⊣ RΓ({*}, -)` then `Lπ^* ⊣ Rπ_*`, at the composite tensor comparison that
`canonicalPointPresentation` carries, is the one for the one-point adjunction at the pair
`(Rπ_*K, Rπ_*M)` followed by derived global sections on the point of the relative cup product of
[Stacks, Tag 0B68] for `π`. -/
theorem canonicalPointPresentation_adjunctionBitensorMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    adjunctionBitensorMap (canonicalPointPresentation S).adjunction
        (coeffTensor S) (spaceTensor S)
        (canonicalPointPresentation S).tensorIso.hom K M =
      adjunctionBitensorMap (onePointDerivedAdjunction ↥(baseRing S))
          (coeffTensor S) (pointTensor S)
          (onePointDerivedTensorIso ↥(baseRing S)).hom
          ((derivedPushforward (toCoeffPoint S)).obj K)
          ((derivedPushforward (toCoeffPoint S)).obj M) ≫
        (baseSections (coeffPt S)).map (relativeCupProduct (toCoeffPoint S) K M) :=
  adjunctionBitensorMap_comp (onePointDerivedAdjunction ↥(baseRing S))
    (derivedAdjunction (toCoeffPoint S)) _ _ _
    (onePointDerivedTensorIso ↥(baseRing S)).hom
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison (toCoeffPoint S)) K M

/-! ### Through `PointPresentation.toComparison`, to the canonical one-point comparison -/

/-- **The doubled-counit adjunction morphism of a point presentation, read over `Γ(S, 𝒪_S)`**:
the presentation's abstract relative cup product of [Stacks, Tag 0B68], which lives over `A`,
transported along the equality of rings `h : A = Γ(S, 𝒪_S)`. -/
def PointPresentation.bitensorMap {A : CommRingCat.{u}}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)}
    (d : PointPresentation S A G) (h : A = baseRing S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (Functor.uncurry.obj (tensorBase S)).obj
        ((transportFunctor h G).obj K, (transportFunctor h G).obj M) ⟶
      (transportFunctor h G).obj ((spaceTensor S).obj (K, M)) := by
  subst h
  exact adjunctionBitensorMap d.adjunction (Functor.uncurry.obj (tensorBase S)) (spaceTensor S)
    d.tensorIso.hom K M

/-- The transported morphism *is* the presentation's own doubled-counit adjunction morphism of
[Stacks, Tag 0B68], across the equality of rings. -/
theorem PointPresentation.bitensorMap_heq {A : CommRingCat.{u}}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)}
    (d : PointPresentation S A G) (h : A = baseRing S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    HEq (d.bitensorMap S h K M)
      (adjunctionBitensorMap d.adjunction
        (Functor.uncurry.obj
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A))
        (spaceTensor S) d.tensorIso.hom K M) := by
  subst h; rfl

/-- **The global cup product of the one-point comparison a point presentation produces.** It is
the presentation's own doubled-counit adjunction morphism, conjugated by the identification `e`
of the presentation's right adjoint with `RΓ(S, -)` in each tensor factor and at the tensor
product. -/
theorem globalCupProduct_toComparison_app {A : CommRingCat.{u}}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)}
    (d : PointPresentation S A G) (h : A = baseRing S)
    (e : transportFunctor h G ≅ baseSections S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (Functor.uncurry.obj (tensorBase S)).map (e.hom.app K ×ₘ e.hom.app M) ≫
        (globalCupProduct (d.toComparison S h e)).app (K, M) =
      d.bitensorMap S h K M ≫ e.hom.app ((spaceTensor S).obj (K, M)) := by
  subst h
  exact adjunctionBitensorMap_ofNatIsoRight d.adjunction e
    (Functor.uncurry.obj (tensorBase S)) (spaceTensor S) d.tensorIso.hom K M

/-- **The global cup product of the canonical one-point comparison**, the `μ` of
Cohomology, Section 0FKU on an arbitrary ringed space, conjugated by the Leray identification
`canonicalSectionsIso` into the canonical presentation's doubled-counit adjunction morphism. -/
theorem globalCupProduct_canonicalOnePointComparison_app
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (Functor.uncurry.obj (tensorBase S)).map
          ((canonicalSectionsIso S).hom.app K ×ₘ (canonicalSectionsIso S).hom.app M) ≫
        (globalCupProduct (canonicalOnePointComparison S)).app (K, M) =
      (canonicalPointPresentation S).bitensorMap S (baseRing_coeffPoint S) K M ≫
        (canonicalSectionsIso S).hom.app ((spaceTensor S).obj (K, M)) :=
  globalCupProduct_toComparison_app S (canonicalPointPresentation S) (baseRing_coeffPoint S)
    (canonicalSectionsIso S) K M

/-- **The right-hand column of [Stacks, Tag 0FKV] factors through the point**: the morphism that
`globalCupProduct_canonicalOnePointComparison_app` identifies the global cup product of
`canonicalOnePointComparison S` with is, across the equality of rings, the one-point cup product
at the pair `(Rπ_*K, Rπ_*M)` followed by derived global sections on the point of the relative cup
product of [Stacks, Tag 0B68] for `π`. -/
theorem canonicalPointPresentation_bitensorMap_heq
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    HEq ((canonicalPointPresentation S).bitensorMap S (baseRing_coeffPoint S) K M)
      (adjunctionBitensorMap (onePointDerivedAdjunction ↥(baseRing S))
          (coeffTensor S) (pointTensor S)
          (onePointDerivedTensorIso ↥(baseRing S)).hom
          ((derivedPushforward (toCoeffPoint S)).obj K)
          ((derivedPushforward (toCoeffPoint S)).obj M) ≫
        (baseSections (coeffPt S)).map (relativeCupProduct (toCoeffPoint S) K M)) := by
  refine ((canonicalPointPresentation S).bitensorMap_heq S (baseRing_coeffPoint S) K M).trans
    (heq_of_eq ?_)
  exact canonicalPointPresentation_adjunctionBitensorMap S K M

end Stacks.Cohomology.DerivedGlobalCupProduct

end
