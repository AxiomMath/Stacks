module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksCore.Tactic.StacksAttribute

/-!
# Vector fields: `k`-derivations of the structure sheaf

For a scheme `X` over a field `k`, a vector field on `X` is a `k`-linear derivation of the
structure sheaf `𝒪_X` into itself, written `Der_k(𝒪_X, 𝒪_X)` in Section 53.26 of the Stacks
project. Such a derivation fixes a closed point `x` when it preserves the ideal sheaf of `x`.

## Main definitions

* `Stacks.Curves.SheafDerivation` — `Der_k(𝒪_X, 𝒪_X)`, the `k`-linear derivations of `𝒪_X`
  into itself, realised as the relative derivations along the structural sheaf map
  `k_X ⟶ 𝒪_X` with values in `𝒪_X` viewed as a module over itself.
* `Stacks.Curves.SheafDerivation.Fixes` — a derivation fixes a closed point `x` if it
  preserves the vanishing ideal sheaf of `x`.

## Implementation notes

`Der_k(𝒪_X, 𝒪_X)` is assembled from two general constructions already in this tree, rather
than introduced as a bespoke structure: `AlgebraicGeometry.inverseImageStructureMap` (Stacks
01SA) supplies the structural sheaf map `g⁻¹ 𝒪_{Spec k} ⟶ 𝒪_X` attached to the structure
morphism `g : X ⟶ Spec k`, and `AlgebraicGeometry.SheafOfModules.SheafDerivation` (Stacks 08RM)
is the general notion of relative derivations of sheaves of rings with values in a sheaf of
modules. Taking the coefficient module to be `𝒪_X` itself, via `SheafOfModules.unit`, gives
exactly the self-derivations of the source. Restriction of scalars from `𝒪_{Spec k}` to `k`
along `Scheme.ΓSpecIso` is definitionally transparent, so no separate comparison is needed
between the sheaf-theoretic and ring-theoretic readings of "relative to `k`".

Fixing a point is stated on affine opens using Mathlib's quasi-coherent vanishing ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal`, as in Section 53.26's "the ideal sheaf of `x`".

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- **Stacks 0E66.** `Der_k(𝒪_X, 𝒪_X)`: the `k`-linear derivations of the structure sheaf of a
`k`-scheme `X` into itself. These are the vector fields on `X` of Section 53.26. -/
@[stacks 0E66]
abbrev SheafDerivation (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] :=
  AlgebraicGeometry.SheafOfModules.SheafDerivation
    (AlgebraicGeometry.inverseImageStructureMap (X ↘ Spec (.of k)))
    (SheafOfModules.unit X.ringCatSheaf)

/-- A vector field fixes a closed point if it preserves the point's vanishing ideal sheaf. It
suffices to impose this on affine opens, where the quasi-coherent ideal sheaf is represented by
`IdealSheafData.ideal`. -/
def SheafDerivation.Fixes {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (D : SheafDerivation k X) (x : X) (hx : IsClosed ({x} : Set X)) : Prop :=
  ∀ (U : X.affineOpens) (s : Γ(X, U)),
    s ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).ideal U →
      D.d (X := Opposite.op U.1) s ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).ideal U

end Stacks.Curves

end
