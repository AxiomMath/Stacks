module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalDichotomy
public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResidues

/-!
# Descending a vector field from the normalization of an at-worst-nodal curve

Let `k` be algebraically closed and let `X` be a reduced scheme locally of finite type over `k` of
dimension one whose singularities are at worst nodal, with normalization `ν : X^ν ⟶ X`. A vector
field `D'` on `X^ν` whose induced derivation on `(ν_* 𝒪_{X^ν})_x` fixes every `k`-point of that
stalk at each node of `X` is `ν^♯` applied to a unique vector field on `X`.

`Stacks.Curves.existsUnique_descend_normalization_of_isRegular_or_isNode` proves this with the
dichotomy "the local ring is regular, or the point is a node" imposed point by point.
`Stacks.Curves.isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities` supplies that
dichotomy from `Stacks.Curves.HasAtWorstNodalSingularities` — the regularity at a smooth closed
point by Tag 0B8X, and at a point that is not closed because such a point is the generic point of
an irreducible component, where the stalk of a reduced scheme is a field. Composing the two leaves
a statement whose only hypothesis on `D'` is the one the source imposes.

## Main results

* `Stacks.Curves.existsUnique_descend_normalization_of_hasAtWorstNodalSingularities` — **a vector
  field on the normalization fixing the `k`-points of the stalk of `ν_* 𝒪_{X^ν}` at every node
  descends to a unique vector field on `X`.**

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.Curves

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **Descending a vector field from the normalization of an at-worst-nodal curve.** For `k`
algebraically closed and `X` a reduced scheme locally of finite type over `k` of dimension one
whose singularities are at worst nodal, a vector field `D'` on the normalization whose induced
derivation on `(ν_* 𝒪_{X^ν})_x` fixes every `k`-point of that stalk at each node of `X` is `ν^♯`
applied to a unique vector field on `X`.

This is `Stacks.Curves.existsUnique_descend_normalization_of_isRegular_or_isNode` with its
point-by-point dichotomy supplied by
`Stacks.Curves.isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities`. At a node the
`k`-points of the stalk are the residues at the two points of `X^ν` above `x`, so the condition on
`D'` is the source's requirement that it fix those two points. -/
theorem existsUnique_descend_normalization_of_hasAtWorstNodalSingularities
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))))
    (h : ∀ x : X, IsNode k X x →
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
      letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
      ∀ ε : (((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
        NodalVectorFields.Fixes ε (stalkDerivation (Scheme.normalization X hfin) D' x)) :
    ∃! D : SheafDerivationOf (X ↘ Spec (.of k)), ∀ (U : X.Opens) (s : Γ(X, U)),
      ((Scheme.normalization X hfin).app U).hom (D.onSections s) =
        D'.onSections (((Scheme.normalization X hfin).app U).hom s) := by
  refine existsUnique_descend_normalization_of_isRegular_or_isNode k X hfin hdim D' fun x => ?_
  rcases isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities k X hdim hnodal x with
    hreg | hnode
  · exact Or.inl hreg
  · exact Or.inr ⟨hnode, h x hnode⟩

end Stacks.Curves

end
