module

public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# The edge morphism of a composite is the inverse of the composite right-derived comparison

Two unrelated families in this development compare `(P ⋙ Q).rightDerived n` with
`P ⋙ Q.rightDerived n`:

* `Stacks.Cohomology.RightDerivedEdge.edge P Q n : P ⋙ Q.rightDerived n ⟶ (P ⋙ Q).rightDerived n`,
  built for `P` additive and preserving injective objects — with **no** exactness hypothesis on
  `P` — out of `Stacks.Cohomology.RightDerivedEdge.resolutionComparison`, which maps the chosen
  injective resolution of `P X` into `P` applied to the chosen injective resolution of `X`; and
* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n :
  (P ⋙ Q).rightDerived n ≅ P ⋙ Q.rightDerived n`, built for `P` **exact** and preserving
  injective objects out of `Stacks.Cohomology.CompositeRightDerived.mapInjRes`, which carries an
  injective resolution of `X` to one of `P X`.

This file identifies them: where both exist, the edge morphism is the inverse of the comparison.
Neither family named the other on any line of either tree before this file.

## Main results

* `Stacks.Cohomology.DerivedCompTransport.edge_app_comp_compRightDerivedNatIso_hom_app` and
  `…compRightDerivedNatIso_hom_app_comp_edge_app`: the two cancellations at an object.
* `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_inv_app_eq_edge_app` and
  `…compRightDerivedNatIso_inv_eq_edge`: **the inverse of the comparison is the edge morphism**,
  pointwise and as an equality of natural transformations.

## Implementation notes

The proof is the one-variable transport `…DerivedCompTransport.isoRightDerivedObj_hom_eq` between
the two injective resolutions of `P X` that the two families choose — the globally chosen one and
the image of the chosen resolution of `X` — along `resolutionComparison`, which descends the
identity of `P X` by `…RightDerivedEdge.ι_f_zero_comp_resolutionComparison` together with
`…DerivedCompTransport.mapInjRes_ι_f_zero`. No homotopy uniqueness of descents is used.

`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` writes the induced map on homology as
`HomologicalComplex.homologyMap`, while
`Stacks.Cohomology.DerivedCompTransport.isoRightDerivedObj_hom_eq` writes it as the image under
`Q.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n`. The two spellings are
definitionally equal and are distinct rewriting keys, so the cancellation is assembled as a term
rather than by `rw`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

universe vA uA vB uB vD uD

variable {A : Type uA} {B : Type uB} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vD} D]
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [HasInjectiveResolutions B] [Abelian D]
  (P : A ⥤ B) (Q : B ⥤ D) [P.Additive] [Q.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] [P.PreservesInjectiveObjects]

/-- Two isomorphisms cancelling in the middle of a four-factor composite, at variables: the
form in which the two readings of the comparison of resolutions meet. Stated at variables
because the goal carries two spellings of the induced map on homology. -/
private theorem cancel_middle {V : Type*} [Category* V] {W X' Y' Z' : V}
    (a : W ⟶ X') (m : X' ⟶ Y') (bi : Y' ⟶ Z') (bh : Z' ⟶ Y') (ki : Y' ⟶ W)
    (hb : bi ≫ bh = 𝟙 Y') (h : (a ≫ m) ≫ ki = 𝟙 W) :
    (a ≫ m ≫ bi) ≫ bh ≫ ki = 𝟙 W := by
  rw [Category.assoc, Category.assoc, ← Category.assoc bi bh ki, hb, Category.id_comp,
    ← Category.assoc]
  exact h

/-- The comparison of resolutions underlying the edge morphism descends the identity of `P X`
from the chosen injective resolution of `P X` to the image under `P` of the chosen injective
resolution of `X`. -/
theorem ι_f_zero_comp_resolutionComparison_eq (X : A) :
    (injectiveResolution (P.obj X)).ι.f 0 ≫
        (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X).f 0 =
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).ι.f 0 :=
  (Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X).trans
    (mapInjRes_ι_f_zero P (injectiveResolution X)).symm

/-- **The edge morphism of the pair `(P, Q)` is a left inverse of the composite right-derived
comparison.** Both are read off the same pair of injective resolutions of `P X` — the chosen one
and the image of the chosen resolution of `X` — and the comparison between those two resolutions
is `Stacks.Cohomology.RightDerivedEdge.resolutionComparison`. -/
theorem edge_app_comp_compRightDerivedNatIso_hom_app (n : ℕ) (X : A) :
    (Stacks.Cohomology.RightDerivedEdge.edge P Q n).app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).hom.app X =
      𝟙 _ := by
  have hhom := isoRightDerivedObj_hom_eq Q n (injectiveResolution (P.obj X))
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes P (injectiveResolution X))
    (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X)
    (ι_f_zero_comp_resolutionComparison_eq P X)
  rw [Stacks.Cohomology.RightDerivedEdge.edge_app_eq P Q n (injectiveResolution X)
      (injectiveResolution (P.obj X))
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X)
      (Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X),
    compRightDerivedNatIso_hom_app_mapInjRes P Q n (injectiveResolution X)]
  exact cancel_middle
    ((injectiveResolution (P.obj X)).isoRightDerivedObj Q n).hom
    (HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X)) n)
    ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).inv
    ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).hom
    ((Stacks.Cohomology.CompositeRightDerived.mapInjRes P
      (injectiveResolution X)).isoRightDerivedObj Q n).inv
    (((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).inv_hom_id)
    ((congrArg (fun g => g ≫ ((Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).isoRightDerivedObj Q n).inv) hhom.symm).trans
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).isoRightDerivedObj Q n).hom_inv_id)

/-- **The inverse of the composite right-derived comparison is the edge morphism of the pair**,
at an object. -/
theorem compRightDerivedNatIso_inv_app_eq_edge_app (n : ℕ) (X : A) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).inv.app X =
      (Stacks.Cohomology.RightDerivedEdge.edge P Q n).app X := by
  rw [← Category.id_comp
      ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).inv.app X),
    ← edge_app_comp_compRightDerivedNatIso_hom_app P Q n X, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- **The composite right-derived comparison is a left inverse of the edge morphism**, both being
invertible. -/
theorem compRightDerivedNatIso_hom_app_comp_edge_app (n : ℕ) (X : A) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).hom.app X ≫
        (Stacks.Cohomology.RightDerivedEdge.edge P Q n).app X =
      𝟙 _ := by
  rw [← compRightDerivedNatIso_inv_app_eq_edge_app P Q n X]
  exact (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
    P Q n).hom_inv_id_app X

/-- **The inverse of the composite right-derived comparison is the edge morphism of the
pair.** -/
theorem compRightDerivedNatIso_inv_eq_edge (n : ℕ) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).inv =
      Stacks.Cohomology.RightDerivedEdge.edge P Q n :=
  NatTrans.ext (funext fun X ↦ compRightDerivedNatIso_inv_app_eq_edge_app P Q n X)

end Stacks.Cohomology.DerivedCompTransport

end
