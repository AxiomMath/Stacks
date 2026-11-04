module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters

/-!
# The dimension and the depth of the local ring at a node

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a node of `X`.  Then `𝒪_{X,x}` is one-dimensional and of depth one, over an arbitrary
base field.  Consequently the local ring at a node is a nodal `k`-algebra exactly when the
residue field extension `κ(x)/k` is separable.

## Main results

* `Stacks.Curves.ringKrullDim_stalk_eq_one_and_depth_eq_one_of_isNode` — the local ring at a
  node is one-dimensional of depth one.
* `Stacks.Curves.isNodalAlgebra_stalk_iff_isSeparableExtension_of_isNode` — at a node, the
  nodal-algebra condition is exactly separability of the residue field extension.

## Implementation notes

The `k`-algebra structure on `𝒪_{X,x}` is the one induced by the germ at `x` of the structure
morphism, and the structure on `κ(x)` is induced from it along the residue map; these are the
structures used throughout the node files.

The dimension is obtained from the two bounds already available: the dimension of a local ring
of `X` is at most the dimension of `X`, and a reduced local ring of delta invariant one is not a
field.  Reducedness and the delta invariant come from
`Stacks.Curves.isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode`,
which holds over an arbitrary field.  The depth is then the general fact that a reduced
one-dimensional Noetherian local ring has depth one, `IsLocalRing.depth_eq_one_of_isReduced`.

Separability of `κ(x)/k` is not obtained from the node condition here; it is the one clause of
the nodal-algebra condition that the delta invariant and the number of geometric branches do not
see, and the source derives it from the closed subscheme cut out by the first Fitting ideal of
`Ω_{X/k}`.  The second result isolates exactly that: everything else in condition (2) of Tag
0C4D follows from condition (1) over an arbitrary field.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3R](https://stacks.math.columbia.edu/tag/0C3R)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u v

namespace Stacks.Curves

/-- **The local ring at a node of a one-dimensional scheme locally of finite type over an
arbitrary field is one-dimensional of depth one.**

The depth assertion is the depth clause of condition (5) of Stacks Tag 0C4D, derived from
condition (1) over an arbitrary field; no separability of the residue field extension is used or
asserted. -/
@[stacks 0C4D "the dimension and the depth of the local ring at a node, over an arbitrary base \
field: the depth clause of condition (5), from condition (1)"]
theorem ringKrullDim_stalk_eq_one_and_depth_eq_one_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    ringKrullDim (X.presheaf.stalk x) = 1 ∧
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) = 1 := by
  obtain ⟨hred, hdelta, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode k X hX x
      hnode
  let : _root_.IsReduced (X.presheaf.stalk x) := hred
  have hNag : IsNagataRing (X.presheaf.stalk x) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ AlgebraicGeometry.Spec (.of k)) x
  let : IsNoetherianRing (X.presheaf.stalk x) := hNag.isNoetherianRing
  have hdimle : ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) :=
    hX ▸ AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim x
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 :=
    ringKrullDim_eq_one_of_isReduced_of_deltaInvariant_eq_one (X.presheaf.stalk x) hdimle hdelta
  exact ⟨hdim, IsLocalRing.depth_eq_one_of_isReduced hdim⟩

/-- **At a node of a one-dimensional scheme locally of finite type over an arbitrary field, the
local ring is a nodal `k`-algebra exactly when the residue field extension is separable.**

This is the whole of the gap between conditions (1) and (2) of Stacks Tag 0C4D over an arbitrary
field: the implication from (1) to (2) holds as soon as `κ(x)/k` is separable, and separability
is itself one of the clauses of (2). -/
@[stacks 0C4D "conditions (1) and (2) over an arbitrary base field, at a point already known to \
be a node: the nodal-algebra condition on the local ring is exactly separability of the residue \
field extension"]
theorem isNodalAlgebra_stalk_iff_isSeparableExtension_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    (IsNodalAlgebra k (X.presheaf.stalk x) ↔
      Algebra.IsSeparableExtension k (X.residueField x)) := by
  intro kToStalk
  refine ⟨fun h => ?_, fun hsep =>
    isNodalAlgebra_stalk_of_isNode_of_isSeparableExtension k X hX x hsep hnode⟩
  exact ((isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hX
    x).mp h).1

end Stacks.Curves

end
