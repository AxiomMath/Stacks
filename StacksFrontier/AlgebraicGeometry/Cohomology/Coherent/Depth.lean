module

public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth and Serre's conditions for sheaves on a locally Noetherian scheme

The depth of a sheaf of modules at a point of a scheme is the depth of its stalk over the
local ring at that point, and the depth of the scheme itself is the depth of that local ring
over itself. Serre's condition `(Sₖ)` for a sheaf compares its depth at every point with the
dimension of the support of the corresponding stalk. A sheaf is Cohen–Macaulay when it
satisfies `(Sₖ)` for every `k`.

## Main definitions

* `AlgebraicGeometry.SheafHasDepthAt` says that a sheaf of modules has depth `k` at a point.
* `AlgebraicGeometry.SchemeHasDepthAt` says that a scheme has depth `k` at a point.
* `AlgebraicGeometry.SheafHasPropertySk` is Serre's condition `(Sₖ)` for a sheaf of modules.
* `AlgebraicGeometry.SheafIsCohenMacaulay` is the Cohen–Macaulay condition for a sheaf of
  modules.

## Implementation notes

The sheaf predicates use the canonical stalk module structure over the stalk of the structure
sheaf. Depth takes values in `ℕ∞` while support dimension takes values in `WithBot ℕ∞`, so the
inequality in `(Sₖ)` is compared in the latter type. None of the definitions requires coherence
or local Noetherianity in order to be stated, although that is the setting they are intended
for. Serre's condition for a *scheme* is `AlgebraicGeometry.HasPropertySk`, whose pointwise API
is `AlgebraicGeometry.hasPropertySk_iff`.

Quantification over `ℕ` in `SheafIsCohenMacaulay` represents the source's nonnegative integers.
Since the definition is an `abbrev` that unfolds to the Serre conditions, clients can use their
API directly.

## References

* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
* [Stacks Project, Tag 0343](https://stacks.math.columbia.edu/tag/0343)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0341.** A sheaf of modules has depth `k` at `x` when its stalk has
depth `k` over the local ring at `x`. -/
@[stacks 0341 "part (1)"]
abbrev SheafHasDepthAt (X : Scheme.{u})
    (F : SheafOfModules.{u} (structureSheafRing
      X.toRingedSpace)) (x : X)
    (k : ℕ) : Prop :=
  Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (↑(TopCat.Presheaf.stalk F.val.presheaf x)) = (k : ℕ∞)

/-- **Stacks Project, Tag 0341.** A scheme has depth `k` at `x` when its local ring at `x` has
depth `k` over itself. -/
@[stacks 0341 "part (2)"]
abbrev SchemeHasDepthAt (X : Scheme.{u}) (x : X) (k : ℕ) : Prop :=
  Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x) = (k : ℕ∞)

/-- **Stacks Project, Tag 0341.** Serre's condition `(Sₖ)` for a sheaf of modules: at every
point its depth is at least the minimum of `k` and the dimension of the support of its
stalk. -/
@[stacks 0341 "part (3)", ega "IV 5.7.2" "more general"]
abbrev SheafHasPropertySk (X : Scheme.{u})
    (F : SheafOfModules.{u} (structureSheafRing
      X.toRingedSpace))
    (k : ℕ) : Prop :=
  ∀ x : X,
    min (k : WithBot ℕ∞)
        (Module.supportDim (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk F.val.presheaf x))) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (↑(TopCat.Presheaf.stalk F.val.presheaf x)) : WithBot ℕ∞)

add_to_stacks 0341 "part (4)" AlgebraicGeometry.HasPropertySk

/-- **Stacks Project, Tag 0343.** A sheaf of modules is Cohen–Macaulay when it satisfies
Serre's condition `(Sₖ)` for every `k`. -/
@[stacks 0343, ega "IV 5.7.1"]
abbrev SheafIsCohenMacaulay (X : Scheme.{u})
    (F : SheafOfModules.{u} (structureSheafRing
      X.toRingedSpace)) : Prop :=
  ∀ k : ℕ, SheafHasPropertySk X F k

end AlgebraicGeometry
