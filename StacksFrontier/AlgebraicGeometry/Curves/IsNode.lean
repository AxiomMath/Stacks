module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Multicross
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting

/-!
# Multicross singularities, ordinary double points, and nodes

Let `k` be an algebraically closed field and `X` an algebraic `1`-dimensional `k`-scheme. A
closed point `x ∈ X` is a *multicross singularity* when the completed local ring
`𝒪_{X,x}^∧` is, as a `k`-algebra, the multicross ring of `n ≥ 2` branches — the subring of
`k[[t]] × ⋯ × k[[t]]` of tuples with a common constant coefficient. It is an *ordinary double
point* (equivalently: a node, or a nodal singularity) when `n = 2`.

Over a field that is not algebraically closed the notion is defined by base change: a closed
point of a `1`-dimensional locally algebraic `k`-scheme `X` is a *node* when some point of
`X_{k̄}` above it is an ordinary double point, and the singularities of `X` are *at worst
nodal* when every closed point is either in the smooth locus of `X → Spec k` or a node.

Two predicates in this file would both be called "node" in the Stacks project. They are kept
apart the way the source itself keeps them apart: Tag 0C1W's pointwise condition over an
algebraically closed field is `Stacks.Curves.IsOrdinaryDoublePoint`, and Tag 0C47's condition
over an arbitrary field — "there exists an ordinary double point of `X_{k̄}` mapping to `x`" —
is `Stacks.Curves.IsNode`.

## Main definitions

* `Stacks.Curves.HasMulticrossCompletion` — the completed local ring at `x` is the multicross
  ring with `n` branches, as a `k`-algebra.
* `Stacks.Curves.IsMulticrossSingularity` — `x` is a closed point whose completed local ring is
  a multicross ring with at least two branches (Tag 0C1W).
* `Stacks.Curves.IsOrdinaryDoublePoint` — `x` is a closed point whose completed local ring is
  the two-branch multicross ring (Tag 0C1W).
* `Stacks.Curves.IsNode` — a closed point of a scheme over an arbitrary field with an ordinary
  double point above it after base change to an algebraic closure (Tag 0C47).
* `Stacks.Curves.HasAtWorstNodalSingularities` — every closed point is smooth over the base
  field or a node (Tag 0C47).

## Main results

* `Stacks.Curves.isMulticrossSingularity_iff_of_isClosed` and
  `Stacks.Curves.isOrdinaryDoublePoint_iff_of_isClosed` give the source's characterizations at
  a closed point.
* `Stacks.Curves.IsOrdinaryDoublePoint.isMulticrossSingularity` — an ordinary double point is a
  multicross singularity.

## Implementation notes

The completed local ring is Mathlib's `AdicCompletion` at the maximal ideal of the stalk. Both
the completion and the multicross ring carry their canonical `k`-algebra structures — the
latter by the instance `Stacks.Curves.multicrossAlgebra` — and the isomorphism of the source is
represented by a `k`-algebra equivalence.

The pointwise predicates retain closedness of the point but not the ambient finite-type,
quasi-compactness or dimension hypotheses: those are hypotheses on the curve in the source,
while the completed-local-ring condition is also the notion used for locally algebraic curves
in Tag 0C47.

For Tag 0C47 the algebraic closure is Mathlib's canonical `AlgebraicClosure k`, and base change
is the categorical pullback along `Spec (AlgebraicClosure k) ⟶ Spec k`. The pullback is viewed
over the algebraic closure through its second projection, so that the condition on the point
above `x` is exactly `IsOrdinaryDoublePoint`.

## References

* [Stacks Project, Tag 0C1U](https://stacks.math.columbia.edu/tag/0C1U)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-! ### Multicross singularities over an algebraically closed field -/

/-- The completed local ring at `x` is the multicross ring with `n` branches, as a
`k`-algebra. -/
def HasMulticrossCompletion (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (x : X) (n : ℕ) : Prop :=
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom
  letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  Nonempty (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[k]
    ↥(multicross k n))

/-- The completed-local-ring equivalence defining `HasMulticrossCompletion`. -/
@[simp]
theorem hasMulticrossCompletion_iff (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X) (n : ℕ) :
    HasMulticrossCompletion k X x n ↔
      let kToStalk : k →+* X.presheaf.stalk x :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
          X.presheaf.germ ⊤ x trivial).hom
      letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
      Nonempty (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[k]
        ↥(multicross k n)) :=
  Iff.rfl

/-- **Stacks 0C1W.** A point is a multicross singularity if it is closed and its completed
local ring is a multicross ring with at least two branches. -/
@[stacks 0C1W "multicross singularity"]
def IsMulticrossSingularity (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧ ∃ n : ℕ, 2 ≤ n ∧ HasMulticrossCompletion k X x n

/-- **Stacks 0C1W.** A point is an ordinary double point — a node, or a nodal singularity — if
it is closed and its completed local ring is the two-branch multicross ring. -/
@[stacks 0C1W "node (ordinary double point)",
  sga "7 VI 6.6" "dim 1, k alg. closed",
  sga "7 XV 1.2.1" "dim 1, alg. closed k",
  sga "7 XVII 1.1" "n=2, k alg. closed",
  sga "7 IX 10.5.4",
  sga "7 IX 12.1.11"]
def IsOrdinaryDoublePoint (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧ HasMulticrossCompletion k X x 2

/-- The defining conditions for a multicross singularity. -/
@[simp]
theorem isMulticrossSingularity_iff (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X) :
    IsMulticrossSingularity k X x ↔
      IsClosed ({x} : Set X) ∧ ∃ n : ℕ, 2 ≤ n ∧ HasMulticrossCompletion k X x n :=
  Iff.rfl

/-- At a closed point, being a multicross singularity is exactly the completed-local-ring
condition in Tag 0C1W. -/
theorem isMulticrossSingularity_iff_of_isClosed (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsMulticrossSingularity k X x ↔ ∃ n : ℕ, 2 ≤ n ∧ HasMulticrossCompletion k X x n :=
  and_iff_right hx

/-- The defining conditions for an ordinary double point. -/
@[simp]
theorem isOrdinaryDoublePoint_iff (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (x : X) :
    IsOrdinaryDoublePoint k X x ↔
      IsClosed ({x} : Set X) ∧ HasMulticrossCompletion k X x 2 :=
  Iff.rfl

/-- At a closed point, being an ordinary double point is exactly having the two-branch
completed local ring. -/
theorem isOrdinaryDoublePoint_iff_of_isClosed (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsOrdinaryDoublePoint k X x ↔ HasMulticrossCompletion k X x 2 :=
  and_iff_right hx

/-- A multicross singularity is a closed point. -/
theorem IsMulticrossSingularity.isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] {x : X} (hx : IsMulticrossSingularity k X x) :
    IsClosed ({x} : Set X) :=
  hx.1

/-- A multicross singularity has a multicross completed local ring with at least two
branches. -/
theorem IsMulticrossSingularity.exists_hasMulticrossCompletion {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {x : X}
    (hx : IsMulticrossSingularity k X x) :
    ∃ n : ℕ, 2 ≤ n ∧ HasMulticrossCompletion k X x n :=
  hx.2

/-- An ordinary double point is a closed point. -/
theorem IsOrdinaryDoublePoint.isClosed {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {x : X} (hx : IsOrdinaryDoublePoint k X x) :
    IsClosed ({x} : Set X) :=
  hx.1

/-- The completed local ring of an ordinary double point is the two-branch multicross ring. -/
theorem IsOrdinaryDoublePoint.hasMulticrossCompletion {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] {x : X} (hx : IsOrdinaryDoublePoint k X x) :
    HasMulticrossCompletion k X x 2 :=
  hx.2

/-- An ordinary double point is a multicross singularity, with two branches. -/
theorem IsOrdinaryDoublePoint.isMulticrossSingularity {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] {x : X} (hx : IsOrdinaryDoublePoint k X x) :
    IsMulticrossSingularity k X x :=
  ⟨hx.1, 2, le_rfl, hx.2⟩

/-! ### Nodes over an arbitrary field -/

/-- **Stacks 0C47.** A point of a scheme over `k` is a node if it is closed and an ordinary
double point lies above it after base change to an algebraic closure of `k`. -/
@[stacks 0C47 "part (1)"]
def IsNode (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) : Prop :=
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
  let fst : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let snd : Y ⟶ Spec (.of K) := pullback.snd (X ↘ Spec (.of k)) g
  letI : Y.Over (Spec (.of K)) := ⟨snd⟩
  IsClosed ({x} : Set X) ∧ ∃ xbar : Y, fst.base xbar = x ∧ IsOrdinaryDoublePoint K Y xbar

/-- **Stacks 0C47.** A scheme over `k` has at-worst-nodal singularities if each of its closed
points is smooth over `k` or is a node. -/
@[stacks 0C47 "part (2)"]
def HasAtWorstNodalSingularities (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) →
    InfinitesimalLifting.SmoothAt (X ↘ Spec (.of k)) x ∨ IsNode k X x

/-- The conditions defining a node over a field. -/
@[simp]
theorem isNode_iff (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] (x : X) :
    IsNode k X x ↔
      let K := AlgebraicClosure k
      let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
      let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
      let fst : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
      let snd : Y ⟶ Spec (.of K) := pullback.snd (X ↘ Spec (.of k)) g
      letI : Y.Over (Spec (.of K)) := ⟨snd⟩
      IsClosed ({x} : Set X) ∧ ∃ xbar : Y, fst.base xbar = x ∧
        IsOrdinaryDoublePoint K Y xbar :=
  Iff.rfl

/-- The conditions defining at-worst-nodal singularities. -/
@[simp]
theorem hasAtWorstNodalSingularities_iff (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] :
    HasAtWorstNodalSingularities k X ↔ ∀ x : X, IsClosed ({x} : Set X) →
      InfinitesimalLifting.SmoothAt (X ↘ Spec (.of k)) x ∨ IsNode k X x :=
  Iff.rfl

/-- A node is a closed point. -/
theorem IsNode.isClosed {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {x : X} (hx : IsNode k X x) : IsClosed ({x} : Set X) :=
  hx.1

end Stacks.Curves

end
