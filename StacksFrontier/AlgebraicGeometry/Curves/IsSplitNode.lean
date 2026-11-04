module

public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FieldExtensionStalk

/-!
# Split nodes

Let `k` be a field, `X` a `1`-dimensional algebraic `k`-scheme and `x ∈ X` a closed point. The
point `x` is a *split node* when it is a node, its residue field `κ(x)` is the base field `k`
(the structure map `k → κ(x)` is bijective), and the separable quadratic `κ(x)`-algebra
`Stacks.Curves.quadraticAlgebra` attached to the local ring `𝒪_{X, x}` is the trivial one
`κ(x) × κ(x)`.

## Main definitions

* `Stacks.Curves.IsSplitNode`: `x` is a node with residue field `k` whose associated quadratic
  algebra is split.

## References

* [Stacks Project, Tag 0CBV](https://stacks.math.columbia.edu/tag/0CBV)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- A point of a scheme over `k` is a split node if it is a node, the structure map `k → κ(x)`
is bijective, and the quadratic algebra of `𝒪_{X, x}` is the trivial quadratic extension
`κ(x) × κ(x)`. -/
@[stacks 0CBV]
def IsSplitNode (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) : Prop :=
  IsNode k X x ∧ Function.Bijective (fieldToResidue (X ↘ Spec (.of k)) x).hom ∧
    Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
      (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x)))

/-- The conditions defining a split node. -/
@[simp]
theorem isSplitNode_iff (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (x : X) :
    IsSplitNode k X x ↔
      IsNode k X x ∧ Function.Bijective (fieldToResidue (X ↘ Spec (.of k)) x).hom ∧
        Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
          (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x))) :=
  Iff.rfl

/-- A split node is a node. -/
theorem IsSplitNode.isNode {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {x : X} (hx : IsSplitNode k X x) : IsNode k X x :=
  hx.1

/-- A split node is a closed point. -/
theorem IsSplitNode.isClosed {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {x : X} (hx : IsSplitNode k X x) : IsClosed ({x} : Set X) :=
  hx.1.1

/-- The residue field of a split node is the base field. -/
theorem IsSplitNode.bijective_fieldToResidue {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {x : X} (hx : IsSplitNode k X x) :
    Function.Bijective (fieldToResidue (X ↘ Spec (.of k)) x).hom :=
  hx.2.1

/-- The quadratic algebra of a split node is the trivial quadratic extension of its residue
field. -/
theorem IsSplitNode.nonempty_quadraticAlgebra_algEquiv_prod {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] {x : X} (hx : IsSplitNode k X x) :
    Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
      (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x))) :=
  hx.2.2

end Stacks.Curves

end
