module

public import StacksFrontier.AlgebraicGeometry.Curves.IsSplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCompletedLocalRing
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.PrescribedResidueFieldPoint

/-!
# A split node is carried along an isomorphism of curves over a field

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`e : Y ⟶ X` be an isomorphism over `Spec k`. Then a split node of `X` is a split node of `Y` at
the corresponding point. Each of the three clauses of `Stacks.Curves.IsSplitNode` is carried:

* the node condition by Stacks Tag 0C57, nodes being étale-local and an isomorphism being étale;
* the residue field condition because the residue-field map of an isomorphism is an isomorphism;
* the splitting of the quadratic algebra because the quadratic algebra depends only on the local
  ring (`Stacks.Curves.quadraticAlgebra_split_of_ringEquiv`).

The structure morphism of `Y` is given as an argument together with its compatibility with `e`,
so that the statement applies to a scheme whose structure morphism is presented in some other
way than as the composite — for instance the fibre of a morphism, presented by
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`.

## Main results

* `Stacks.Curves.fieldToResidue_comp` — the structural map from the ground field to a residue
  field is natural in the scheme.
* `Stacks.Curves.isSplitNode_of_isIso` — a split node is carried along an isomorphism over the
  ground field.

## References

* [Stacks Project, Tag 0CBV](https://stacks.math.columbia.edu/tag/0CBV)
* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- **The structural map from the ground field to a residue field is natural in the scheme**: for
a morphism `e : Y ⟶ X` of schemes over `k` the map `k → κ(y)` is the map `k → κ(e y)` followed by
the residue-field map of `e`. -/
theorem fieldToResidue_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (.of k)) (e : Y ⟶ X) (y : Y) :
    fieldToResidue (e ≫ fX) y = fieldToResidue fX (e.base y) ≫ e.residueFieldMap y := by
  rw [AlgebraicGeometry.fieldToResidue_eq_specGammaResidue_comp_residueFieldMap (e ≫ fX) y,
    AlgebraicGeometry.fieldToResidue_eq_specGammaResidue_comp_residueFieldMap fX (e.base y),
    Scheme.residueFieldMap_comp, Category.assoc]
  rfl

/-- **A split node is carried along an isomorphism of curves over the ground field.** -/
theorem isSplitNode_of_isIso (k : Type u) [Field k] (X Y : Scheme.{u})
    (fX : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType fX]
    (hdim : topologicalKrullDim X = 1)
    (e : Y ⟶ X) [IsIso e] (fY : Y ⟶ AlgebraicGeometry.Spec (.of k)) (hfY : e ≫ fX = fY)
    (y : Y) :
    letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨fX⟩
    letI : Y.Over (AlgebraicGeometry.Spec (.of k)) := ⟨fY⟩
    IsSplitNode k X (e.base y) → IsSplitNode k Y y := by
  subst hfY
  intro hx
  refine ⟨(isNode_iff_of_etale k X Y fX hdim e y).mp hx.1, ?_, ?_⟩
  · show Function.Bijective (fieldToResidue (e ≫ fX) y).hom
    rw [fieldToResidue_comp]
    exact (ConcreteCategory.bijective_of_isIso (e.residueFieldMap y)).comp hx.2.1
  · exact quadraticAlgebra_split_of_ringEquiv (X.presheaf.stalk (e.base y))
      (Y.presheaf.stalk y) (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv hx.2.2

end Stacks.Curves

end
