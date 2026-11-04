/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Morphisms of reduced varieties over an algebraically closed field are determined by points

Let `k` be algebraically closed, `X` a reduced scheme locally of finite type over `k` and `Y` a
separated scheme over `k`. Two morphisms `f g : X ⟶ Y` over `k` which agree on every `k`-rational
point of `X` are equal (`Stacks.Varieties.overHom_ext_of_points`): the closed points of `X` are
its `k`-points, and Mathlib's `AlgebraicGeometry.ext_of_apply_eq` concludes.

This is how the seesaw arguments in the proof of [Stacks, Tag 03U1] identify a classifying map
into the Jacobian from its values at rational points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.Varieties

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Morphisms over `k` from a reduced scheme locally of finite type agree when they agree on
`k`-points.** -/
theorem overHom_ext_of_points {X Y : Over (Spec (.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  have hwf : f.left ≫ Y.hom = X.hom := Over.w f
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := hwf ▸ inferInstance
  refine Over.OverMorphism.ext (ext_of_apply_eq Y.hom Set.univ isClosed_univ.isLocallyClosed
    dense_univ (fun x _ hx => ?_) (hwf.trans (Over.w g).symm))
  have e := congrArg (fun r => r.left (IsLocalRing.closedPoint k))
    (h (Over.homMk (pointOfClosedPoint X.hom x hx)
      (by simpa using pointOfClosedPoint_comp X.hom x hx)))
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at e
  rwa [← pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint k)]

end Stacks.Varieties
