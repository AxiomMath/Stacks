module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw

/-!
# The monoidality coherence of a composite, for the relative Künneth map

Let `a : X ⟶ S` and `p : W ⟶ X` be morphisms of ringed spaces.  The relative Künneth morphism of
Tag 0FLP at the composite `p ≫ a` is identified, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism`, with a chain of
three comparisons, granted the coherence
`Stacks.Cohomology.DerivedKunneth.PullbackTensorComparisonComp` between the monoidality
isomorphism of Stacks 079U for derived pullback and the composition isomorphism of Stacks 0D5S.
This module proves that coherence at every pair of derived modules on the base.

## Main results

* `Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp`: the coherence
  `PullbackTensorComparisonComp a p P Q` holds for all `P` and `Q`.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedPullback.Composition
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunneth

/-- For a functor `F` and morphisms with `m ≫ n = 𝟙 V`, the composite
`(d ≫ e ≫ F.map m) ≫ F.map n` equals `d ≫ e`. -/
lemma comp_map_comp_map_cancel {C₀ : Type*} [Category C₀] {D₀ : Type*} [Category D₀]
    (F : C₀ ⥤ D₀) {T U : D₀} {V V' : C₀} {d : T ⟶ U} {e : U ⟶ F.obj V} {m : V ⟶ V'}
    {n : V' ⟶ V} (h : m ≫ n = 𝟙 V) :
    (d ≫ e ≫ F.map m) ≫ F.map n = d ≫ e := by
  rw [Category.assoc, Category.assoc, ← F.map_comp, h, F.map_id, Category.comp_id]

section Geometry

attribute [local instance] HasDerivedCategory.standard

variable {S X W : RingedSpace.{u, u}} (a : X ⟶ S) (p : W ⟶ X)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The monoidality isomorphism of derived pullback (Stacks 079U) is compatible with the
composition isomorphism `L(p ≫ a)^* ≅ Lp^* ∘ La^*` (Stacks 0D5S): the coherence
`PullbackTensorComparisonComp a p P Q` holds for all derived modules `P` and `Q` on `S`. -/
theorem pullbackTensorComparisonComp
    (P Q : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    PullbackTensorComparisonComp a p P Q := by
  have h :
      (derivedPullbackCompIsoCanonical p a).hom.app
            ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).obj (P, Q)) ≫
          (pullbackTensorComparison (p ≫ a)).app (P, Q) =
        (derivedPullback p).map ((pullbackTensorComparison a).app (P, Q)) ≫
          (pullbackTensorComparison p).app
              ((derivedPullback a).obj P, (derivedPullback a).obj Q) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
              ((derivedPullbackCompIsoCanonical p a).hom.app P ×ₘ
                (derivedPullbackCompIsoCanonical p a).hom.app Q) :=
    NatTrans.congr_app
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp p a) (P, Q)
  have hid :
      ((derivedPullbackCompIsoCanonical p a).hom.app P ×ₘ
            (derivedPullbackCompIsoCanonical p a).hom.app Q) ≫
          ((derivedPullbackCompIsoCanonical p a).inv.app P ×ₘ
            (derivedPullbackCompIsoCanonical p a).inv.app Q) = 𝟙 _ :=
    CategoryTheory.Prod.hom_ext ((derivedPullbackCompIsoCanonical p a).hom_inv_id_app P)
      ((derivedPullbackCompIsoCanonical p a).hom_inv_id_app Q)
  unfold PullbackTensorComparisonComp
  rw [h]
  exact comp_map_comp_map_cancel
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)) hid

end Geometry

end Stacks.Cohomology.DerivedKunneth

end
