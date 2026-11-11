module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack

/-!
# The standing data of the example of a non-algebraic Hom-stack

Section 0AF8 of the source fixes the following data, used by Lemma 0AFB and Proposition 0AFC:

* an algebraically closed field `k` which is not the algebraic closure of a finite field;
* the base `S = Spec k⟦t⟧`, with thickenings `Sₙ` of its closed point;
* a morphism `f : X ⟶ S` which is projective and flat, whose fibres are geometrically connected
  curves, whose special fibre `X₀ = X ×_S S₀` is a nodal curve with smooth irreducible components
  whose dual graph has a loop consisting of rational curves, and with `X` a regular scheme;
* a non-zero abelian variety `A₀` over `k`, and the constant abelian scheme
  `A = A₀ ×_{Spec k} S`.

This file bundles exactly these hypotheses as `Stacks.Examples.NonAlgebraicHomStack.Situation`.

## Main definitions

* `Stacks.Examples.NonAlgebraicHomStack.specialFibre`: `X₀ = X ×_S Spec (k⟦t⟧ / (t))`, as a
  scheme over `Spec k`.
* `Stacks.Examples.NonAlgebraicHomStack.HasLoopOfRationalCurves`: a scheme over `k` has a loop of
  rational curves in the dual graph of its irreducible components.
* `Stacks.Examples.NonAlgebraicHomStack.Situation`: the standing data of Section 0AF8.

## Implementation notes

* *Not the algebraic closure of a finite field.* For an algebraically closed `k` this says that
  `k` is not algebraic over a finite prime field: `k` is the algebraic closure of a finite field
  exactly when its prime subfield is finite and `k` is algebraic over it.
* *Curves.* The fibres of `f` are "curves" in the loose sense of the source: the special fibre is
  a nodal curve with several irreducible components, so it is not a variety. The condition
  recorded is that every fibre of `f` has dimension one.
* *The dual graph and its loop.* The dual graph of the nodal curve `X₀` has the irreducible
  components of `X₀` as vertices and the nodes as edges, a node joining the components through
  it. As the components are smooth, no node lies on a single component twice, so a loop is a
  cycle `C₀, x₀, C₁, x₁, …, C_{m-1}, x_{m-1}` with `m ≥ 2`, pairwise distinct components `Cᵢ`
  and pairwise distinct nodes `xᵢ ∈ Cᵢ ∩ C_{i+1}` (indices modulo `m`). It consists of rational
  curves when each `Cᵢ`, with its reduced structure, is isomorphic to `ℙ¹_k` over `k`; for a
  smooth projective curve over an algebraically closed field this is rationality.
* *Non-zero.* An abelian variety `A₀` over `k` is non-zero when its structure morphism
  `A₀ ⟶ Spec k` is not an isomorphism.
* The index `n` of the thickenings `Xₙ` of `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack` is
  shifted by one against the source: `X₀` here is `X ×_S Spec (k⟦t⟧/(t))`, the source's
  `X ×_S S₁ = X ×_S Spec (k[t]/(t))`, which the source also calls `X₀`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Curves
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Examples.NonAlgebraicHomStack

variable {k : Type u} [Field k]

/-- The special fibre `X₀ = X ×_S Spec (k⟦t⟧ / (t))` of a scheme over `S = Spec k⟦t⟧`. -/
abbrev specialFibre {X : Scheme.{u}} (f : X ⟶ base k) : Scheme.{u} := thickening f 0

/-- The structure morphism of the special fibre to `Spec k`, through `k ⟶ k⟦t⟧ / (t)`. -/
instance specialFibre.over {X : Scheme.{u}} (f : X ⟶ base k) :
    (specialFibre f).Over (Spec (.of k)) where
  hom := pullback.snd f (adicThickeningι (PowerSeries k) (uniformizer k) 0) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k ⧸ uniformizer k ^ (0 + 1))))

/-- A scheme `Y` over `k` **has a loop of rational curves**: there are `m ≥ 2` pairwise distinct
irreducible components `C₀, …, C_{m-1}` of `Y` and pairwise distinct nodes `x₀, …, x_{m-1}` of
`Y` with `xᵢ ∈ Cᵢ ∩ C_{i+1}` (indices modulo `m`), each `Cᵢ` with its reduced structure being
isomorphic to the projective line `ℙ¹_k` over `k`. This is a cycle consisting of rational curves
in the dual graph of `Y`, whose vertices are the irreducible components and whose edges are the
nodes. -/
def HasLoopOfRationalCurves (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    Prop :=
  ∃ (m : ℕ) (_ : 2 ≤ m) (C : Fin m → irreducibleComponents Y) (x : Fin m → Y),
    Function.Injective C ∧ Function.Injective x ∧
    (∀ i, IsNode k Y (x i)) ∧
    (∀ i, x i ∈ (C i : Set Y) ∧ x i ∈ (C (finRotate m i) : Set Y)) ∧
    ∀ i, Nonempty (Over.mk (Y.reducedComponentι (C i) ≫ (Y ↘ Spec (.of k))) ≅
      Over.mk (projectiveLine k ↘ Spec (.of k)))

/-- **The standing data of Section 0AF8**: an algebraically closed field `k` which is not the
algebraic closure of a finite field; a morphism `f : X ⟶ S = Spec k⟦t⟧` which is projective and
flat, whose fibres are geometrically connected curves, whose special fibre `X₀` is a nodal curve
with smooth irreducible components whose dual graph has a loop of rational curves, and with `X`
regular; and a non-zero abelian variety `A₀` over `k`. The constant abelian scheme is
`Stacks.Examples.NonAlgebraicHomStack.Situation.abelianScheme`. -/
structure Situation (k : Type u) [Field k] where
  /-- The field is algebraically closed. -/
  isAlgClosed : IsAlgClosed k
  /-- The field is not the algebraic closure of a finite field. -/
  not_isAlgebraic_finite : ¬ (Finite (⊥ : Subfield k) ∧ Algebra.IsAlgebraic (⊥ : Subfield k) k)
  /-- The total space of the family. -/
  X : Scheme.{u}
  /-- The family over `S = Spec k⟦t⟧`. -/
  f : X ⟶ base k
  /-- `f` is projective. -/
  isProjective : IsProjective f
  /-- `f` is flat. -/
  flat : Flat f
  /-- The fibres of `f` are geometrically connected. -/
  geometricallyConnected : GeometricallyConnected f
  /-- The fibres of `f` are curves. -/
  dim_fiber : ∀ s : base k, topologicalKrullDim (f.fiber s) = 1
  /-- The special fibre is a nodal curve. -/
  nodal : HasAtWorstNodalSingularities k (specialFibre f)
  /-- The irreducible components of the special fibre are smooth. -/
  smooth_components : ∀ Z : irreducibleComponents (specialFibre f),
    Smooth ((specialFibre f).reducedComponentι Z ≫ (specialFibre f ↘ Spec (.of k)))
  /-- The dual graph of the special fibre has a loop consisting of rational curves. -/
  hasLoop : HasLoopOfRationalCurves k (specialFibre f)
  /-- `X` is regular. -/
  regular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  /-- The abelian variety `A₀` over `k`. -/
  A₀ : Over (Spec (.of k))
  /-- The group structure of `A₀`. -/
  [grp : GrpObj A₀]
  /-- `A₀` is an abelian variety. -/
  isAbelianVariety : IsAbelianVariety k A₀
  /-- `A₀` is non-zero. -/
  nonzero : ¬ IsIso A₀.hom

attribute [instance] Situation.grp

namespace Situation

variable (sit : Situation k)

/-- The structure morphism `S = Spec k⟦t⟧ ⟶ Spec k`. -/
abbrev baseToField : base k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))

/-- The constant abelian scheme `A = A₀ ×_{Spec k} S` over `S`. -/
abbrev abelianScheme : Over (base k) :=
  (Over.pullback (baseToField (k := k))).obj sit.A₀

/-- The group structure of the constant abelian scheme, carried by the base change functor. -/
instance : GrpObj sit.abelianScheme :=
  ((Over.pullback (baseToField (k := k))).mapGrp.obj (.mk sit.A₀)).grp

end Situation

end Stacks.Examples.NonAlgebraicHomStack
