module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeTorIndependence
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition

/-!
# The naive half of `A ⊗ᴸ_B B' = A'`

Let `R → A` be a ring map, `R → R'` arbitrary, `A' = A ⊗[R] R'`, `B = A ⊗[R] A`,
`B' = A' ⊗[R'] A'`, and `Δ : B → A`, `Δ' : B' → A'` the two multiplication maps. This file proves
that `B' ⊗_B A = A'` as a `B'`-module, `B'` acting through `Δ'`; equivalently, the commuting
square `Dualizing.lmul'_comp_diagonalBaseChangeMap` is a pushout of rings.

## Main definitions

* `Dualizing.diagonalAlgebraBaseChange`: `A'` as a `B'`-algebra through `Δ'`.
* `Dualizing.smulDiagonalBaseChange`, `Dualizing.moduleDiagonalBaseChange`: the action of `B` on
  `B'` through the map of diagonals `Dualizing.diagonalBaseChangeMap`.
* `Dualizing.diagonalBaseChangePushoutEquiv`: the `B'`-algebra isomorphism
  `B' ⊗_B A ≃ₐ[B'] A'`.

## Main results

* `Dualizing.isPushout_diagonal_diagonalBaseChange`: `Algebra.IsPushout B A B' A'`, that is
  `A' = A ⊗_B B'`.
* `Dualizing.isPushout_diagonalBaseChange_diagonal`: the same square read the other way round,
  `Algebra.IsPushout B B' A A'`.

## Implementation notes

The action of `B` on `B'` used here is the map of diagonals `Dualizing.diagonalBaseChangeMap`,
`a₁ ⊗ a₂ ↦ (a₁ ⊗ 1) ⊗ (a₂ ⊗ 1)`. Once `Algebra B A` is an instance, `TensorProduct.leftHasSMul`
supplies a different action, `b ↦ (Δ b ⊗ 1) ⊗ 1`, for which the square does not commute. The
local instances `Dualizing.smulDiagonalBaseChange` and `Dualizing.moduleDiagonalBaseChange`
therefore fix the scalar action and the module structure at a priority that wins; both agree by
definition with `Dualizing.diagonalBaseChangeAlgebra`. A consumer of
`Dualizing.isPushout_diagonal_diagonalBaseChange` has to use the same actions, as
`Dualizing.diagonalBaseChangePushoutEquiv` does.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- `A'` as a `B'`-algebra, through the multiplication map `Δ' : B' → A'`. -/
abbrev diagonalAlgebraBaseChange :
    Algebra ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R') :=
  (Algebra.TensorProduct.lmul' R' :
    (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom.toAlgebra

/-- The scalar action of `B` on `B'` given by the map of diagonals
`Dualizing.diagonalBaseChangeMap`. -/
abbrev smulDiagonalBaseChange :
    SMul (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
  (diagonalBaseChangeAlgebra R A R').toSMul

/-- The `B`-module structure on `B'` given by the map of diagonals
`Dualizing.diagonalBaseChangeMap`. -/
abbrev moduleDiagonalBaseChange :
    Module (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
  (diagonalBaseChangeAlgebra R A R').toModule

attribute [local instance 10000] diagonalBaseChangeAlgebra smulDiagonalBaseChange
  moduleDiagonalBaseChange

attribute [local instance] isScalarTower_diagonalBaseChange isPushout_diagonalBaseChange
  diagonalAlgebraSelf diagonalAlgebraBaseChange

/-- The scalar tower `B → B' → A'`: the composite `B → B' → A'` is `B → A → A'`, by the
commuting square `Dualizing.lmul'_comp_diagonalBaseChangeMap`. -/
theorem isScalarTower_diagonal_diagonalBaseChange :
    IsScalarTower (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R') :=
  IsScalarTower.of_algebraMap_eq' (lmul'_comp_diagonalBaseChangeMap R A R').symm

/-- `R → B' → A'` is `R → A'`. -/
theorem isScalarTower_base_diagonalBaseChange :
    IsScalarTower R ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R') := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [IsScalarTower.algebraMap_apply R R' (A ⊗[R] R'),
    IsScalarTower.algebraMap_apply R R' ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')),
    ← IsScalarTower.algebraMap_apply R' ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R')]

attribute [local instance] isScalarTower_diagonal_diagonalBaseChange
  isScalarTower_base_diagonalBaseChange

/-- The commuting square `B → A`, `B → B'`, `A → A'`, `B' → A'` of
`Dualizing.lmul'_comp_diagonalBaseChangeMap` is a pushout of rings: `A' = A ⊗_B B'`. -/
theorem isPushout_diagonal_diagonalBaseChange :
    Algebra.IsPushout (A ⊗[R] A) A ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) (A ⊗[R] R') :=
  (Algebra.IsPushout.comp_iff R (A ⊗[R] A) R'
    ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))).mp inferInstance

/-- `Dualizing.isPushout_diagonal_diagonalBaseChange` read the other way round: `B' ⊗_B A = A'`. -/
theorem isPushout_diagonalBaseChange_diagonal :
    Algebra.IsPushout (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) A (A ⊗[R] R') :=
  (isPushout_diagonal_diagonalBaseChange R A R').symm

attribute [local instance] isPushout_diagonalBaseChange_diagonal

/-- The `B'`-algebra isomorphism `B' ⊗_B A ≃ₐ[B'] A'`, `B'` acting on `A'` through `Δ'`. -/
def diagonalBaseChangePushoutEquiv :
    (((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) ⊗[A ⊗[R] A] A) ≃ₐ[(A ⊗[R] R') ⊗[R'] (A ⊗[R] R')]
      (A ⊗[R] R') :=
  Algebra.IsPushout.equiv (A ⊗[R] A) ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) A (A ⊗[R] R')

end

end Dualizing

end
