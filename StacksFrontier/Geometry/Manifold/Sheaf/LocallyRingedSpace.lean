module

public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0092 — the smooth case

The second half of Stacks example 0092: an infinitely differentiable map `f : M → N` of
`C^∞`-manifolds induces a canonical morphism of ringed spaces
`(M, C^∞_M) → (N, C^∞_N)`, whose map on structure sheaves is precomposition with `f`, as in
the continuous-function case (`fSharp`). Mathlib's `ChartedSpace.locallyRingedSpaceMap`
constructs it, over any nontrivially normed field and model with corners, as a morphism of
locally ringed spaces between the spaces `ChartedSpace.locallyRingedSpace` carrying the sheaf
`smoothSheafCommRing` of smooth scalar-valued functions; real `C^∞`-manifolds are the case
`𝕜 = ℝ`.
-/

add_to_stacks 0092 "smooth case: a smooth map `f : M → N` of `C^∞`-manifolds induces the
  morphism of (locally) ringed spaces `(M, C^∞_M) → (N, C^∞_N)` given by `h ↦ h ∘ f` on
  sections" ChartedSpace.locallyRingedSpaceMap
