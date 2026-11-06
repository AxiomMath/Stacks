module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AutomorphismTopology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale fundamental group

Let `X` be a connected scheme and let `x` be a geometric point of `X`, i.e. a morphism
`Spec Ω ⟶ X` with `Ω` algebraically closed. The *fibre* of a finite étale cover `Y ⟶ X` at `x`
is the set of lifts of `x` to `Y`, and sending a cover to its fibre is a functor
`FÉt_X ⥤ Type`, the *fibre functor* `F_x`. The étale fundamental group
`π₁(X, x) = Aut(F_x)` is the group of natural automorphisms of this functor, carrying the
topology of Stacks 0BMR: the one induced by evaluation on every finite étale cover.

Each natural automorphism acts on each fibre by evaluating its component there, so `π₁(X, x)`
acts on every geometric fibre, and this is the action through which the fundamental group
classifies finite étale covers. Once the fibres are known to be finite — which is the content of
the Galois-category theory for `FÉt_X` — Stacks 0BMR makes `π₁(X, x)` profinite: compact,
Hausdorff and totally disconnected.

## Main definitions

* `AlgebraicGeometry.finiteEtaleFiber` — the fibre of a finite étale cover at a geometric point,
  as the set of lifts of the point.
* `AlgebraicGeometry.finiteEtaleFiberFunctor` — the fibre functor `FÉt_X ⥤ Type u` at a
  geometric point.
* `AlgebraicGeometry.EtaleFundamentalGroup` — the étale fundamental group
  `π₁(X, x) = Aut(F_x)`, with its group structure, its canonical topology, and its action on
  every fibre.

## Implementation notes

The category of finite étale covers is `AlgebraicGeometry.FiniteEtaleOver`, and the topology is
`Stacks.FundamentalGroup.functorAutomorphismTopology`. The compactness, Hausdorffness and total
disconnectedness instances are conditional on `∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)`;
they follow from `Stacks.FundamentalGroup.isProfiniteTop_functorAutomorphismTopology` once that
hypothesis is available, so they apply directly after the Galois-category result supplies
finiteness of the fibres.

The name is `EtaleFundamentalGroup` rather than `FundamentalGroup`: Mathlib's root-namespace
`FundamentalGroup X x` is the topological fundamental group with the same argument shape, so the
shorter name would be ambiguous in any file with `open AlgebraicGeometry`.

## References

* [Stacks Project, Tag 0BNC](https://stacks.math.columbia.edu/tag/0BNC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The fibre of a finite étale cover at a geometric point, as the set of lifts of the point to
the cover. -/
public abbrev finiteEtaleFiber {X : Scheme.{u}} (x : GeometricPoint X)
    (Y : FiniteEtaleOver X) :=
  { f : (x.source ⟶ Y.left) // f ≫ Y.hom = x.hom }

/-- The fibre functor on finite étale covers associated to a geometric point. -/
@[implicit_reducible]
public def finiteEtaleFiberFunctor {X : Scheme.{u}} (x : GeometricPoint X) :
    FiniteEtaleOver X ⥤ Type u where
  obj Y := finiteEtaleFiber x Y
  map {Y Z} f := ↾ (fun y ↦ ⟨y.1 ≫ f.left, by
    rw [Category.assoc, MorphismProperty.Over.w f, y.2]⟩)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- **Stacks Project, Tag 0BNC.** The étale fundamental group of a connected scheme at a
geometric point is the automorphism group of its finite-étale fibre functor, endowed with the
topology induced by its actions on all fibres. -/
@[stacks 0BNC]
public def EtaleFundamentalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) : Type (u + 1) :=
  Aut (finiteEtaleFiberFunctor x)

/-- The étale fundamental group is a group, being an automorphism group. -/
public instance etaleFundamentalGroupGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    Group (EtaleFundamentalGroup X x) :=
  inferInstanceAs (Group (Aut (finiteEtaleFiberFunctor x)))

/-- The topology on the étale fundamental group induced by evaluation on every finite étale
cover. -/
public instance etaleFundamentalGroupTopologicalSpace (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    TopologicalSpace (EtaleFundamentalGroup X x) :=
  Stacks.FundamentalGroup.functorAutomorphismTopology (finiteEtaleFiberFunctor x)

/-- The canonical topology makes the étale fundamental group a topological group. -/
public instance etaleFundamentalGroupIsTopologicalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    IsTopologicalGroup (EtaleFundamentalGroup X x) :=
  Stacks.FundamentalGroup.functorAutomorphismIsTopologicalGroup (finiteEtaleFiberFunctor x)

/-- The fundamental group acts on the fibre of every finite étale cover by evaluating natural
automorphisms on that cover. -/
public instance etaleFundamentalGroupMulAction (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) (Y : FiniteEtaleOver X) :
    MulAction (EtaleFundamentalGroup X x) ((finiteEtaleFiberFunctor x).obj Y) where
  smul σ y := (σ.asIso.app Y).hom y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- If all geometric fibres are finite, the canonical topology on the fundamental group is
compact. -/
public instance etaleFundamentalGroupCompactSpace (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X)
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)] :
    CompactSpace (EtaleFundamentalGroup X x) :=
  (Stacks.FundamentalGroup.isProfiniteTop_functorAutomorphismTopology
    (finiteEtaleFiberFunctor x)).1

/-- If all geometric fibres are finite, the canonical topology on the fundamental group is
Hausdorff. -/
public instance etaleFundamentalGroupT2Space (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X)
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)] :
    T2Space (EtaleFundamentalGroup X x) :=
  (Stacks.FundamentalGroup.isProfiniteTop_functorAutomorphismTopology
    (finiteEtaleFiberFunctor x)).2.1

/-- If all geometric fibres are finite, the canonical topology on the fundamental group is
totally disconnected. -/
public instance etaleFundamentalGroupTotallyDisconnectedSpace (X : Scheme.{u})
    [ConnectedSpace X] (x : GeometricPoint X)
    [∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)] :
    TotallyDisconnectedSpace (EtaleFundamentalGroup X x) :=
  (Stacks.FundamentalGroup.isProfiniteTop_functorAutomorphismTopology
    (finiteEtaleFiberFunctor x)).2.2

end AlgebraicGeometry

end
