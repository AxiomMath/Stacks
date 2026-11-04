module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonStructureSheaf
public import StacksFrontier.CategoryTheory.Monoidal.PullbackComparisonDevissage

/-!
# The comparison map of Equation 48.8.0.1 with its data supplied

`Stacks.Duality.compareWithPullback` takes the cotensorator `α` of derived pullback and the right
unitor `ρ` of the derived tensor product as arguments. This file supplies both from the monoidal
structures `Stacks.Duality.quasiCoherentDerivedMonoidal` and
`Stacks.Duality.quasiCoherentDerivedPullbackMonoidal`, and identifies the resulting maps with the
abstract ones of `CategoryTheory.MonoidalProjectionFormula`, for which [Stacks, Tag 0A9T],
[Stacks, Tag 08EU] and [Stacks, Tag 0A9U] are proved abstractly.

## Main definitions

* `Stacks.Duality.pullbackCotensorator` — the datum `α`, the cotensorator of `Lf^*` read on the
  interchanged tensor products.
* `Stacks.Duality.quasiCoherentRightUnitor` — the datum `ρ`, the right unitor of
  `Stacks.Duality.quasiCoherentDerivedMonoidal`.

## Main results

* `Stacks.Duality.projectionFormulaMap_pullbackCotensorator` — the projection-formula map at
  this `α` is the abstract one.
* `Stacks.Duality.compareWithPullback_pullbackCotensorator` — Equation 48.8.0.1 at this `α` and
  `ρ` is the abstract `CategoryTheory.MonoidalProjectionFormula.comparisonUnit`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The cotensorator of `Lf^*` on `D_QCoh`**, read on the interchanged tensor products: the
canonical map `Lf^*(K₂ ⊗ᴸ K₁) ⟶ Lf^*K₂ ⊗ᴸ Lf^*K₁` of [Stacks, Tag 079U]. -/
def pullbackCotensorator :
    quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X :=
  @MonoidalProjectionFormula.oplaxSwap _ _ _ _ (quasiCoherentDerivedMonoidal Y)
    (quasiCoherentDerivedMonoidal X) (quasiCoherentDerivedPullback' f)
    (quasiCoherentDerivedPullbackMonoidal f)

/-- **The right unitor of `D_QCoh(𝒪_Y)`**: `K ⊗ᴸ 𝒪_Y ≅ K`, naturally in `K`, from
[Stacks, Tag 0FPT]. -/
def quasiCoherentRightUnitor :
    (quasiCoherentDerivedTensor Y).flip.obj (derivedStructureSheaf Y) ≅ 𝟭 _ :=
  @rightUnitorNatIso _ _ (quasiCoherentDerivedMonoidal Y)

/-- The projection-formula map at `α = pullbackCotensorator f` is the abstract one for the
monoidal functor `Lf^*` and the adjunction `Lf^* ⊣ Rf_*`. -/
theorem projectionFormulaMap_pullbackCotensorator (E : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    projectionFormulaMap f hpush (pullbackCotensorator f) E K =
      @MonoidalProjectionFormula.projectionFormulaMap _ _ _ _ (quasiCoherentDerivedMonoidal Y)
        (quasiCoherentDerivedMonoidal X) _ (quasiCoherentDerivedPullbackMonoidal f) _
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        E K :=
  rfl

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush (pullbackCotensorator f) E K)]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-- **Equation 48.8.0.1 at `α = pullbackCotensorator f` and `ρ = quasiCoherentRightUnitor` is the
abstract comparison map** `CategoryTheory.MonoidalProjectionFormula.comparisonUnit` for the
monoidal functor `Lf^*` and the adjunctions `Lf^* ⊣ Rf_* ⊣ a`. -/
theorem compareWithPullback_pullbackCotensorator (K : quasiCoherentDerivedCategory Y) :
    compareWithPullback f hpush (pullbackCotensorator f) adj quasiCoherentRightUnitor K =
      (@MonoidalProjectionFormula.comparisonUnit _ _ _ _ (quasiCoherentDerivedMonoidal Y)
        (quasiCoherentDerivedMonoidal X) _ (quasiCoherentDerivedPullbackMonoidal f) _
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        _ adj (by assumption)).app K :=
  rfl

end Stacks.Duality
