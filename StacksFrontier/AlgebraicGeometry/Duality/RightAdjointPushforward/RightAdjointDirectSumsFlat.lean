module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSumsPerfectProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperFlatRestriction

/-!
# The right adjoint of pushforward along a proper flat morphism commutes with direct sums

Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` proper, flat and of finite
presentation. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` preserves compact objects, so its right
adjoint `a` commutes with direct sums: [Stacks, Tag 0E4I].

## Main results

* `Stacks.Duality.isCompactObject_quasiCoherentDerivedPushforward_of_flat` — `Rf_*` preserves
  compact objects.
* `Stacks.Duality.preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_flat` —
  the right adjoint of `Rf_*` commutes with direct sums.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **Direct image along a proper flat morphism of finite presentation preserves compact
objects** of `D_QCoh`, over a quasi-compact quasi-separated base. -/
theorem isCompactObject_quasiCoherentDerivedPushforward_of_flat
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (E : quasiCoherentDerivedCategory X) (hE : IsCompactObject.{u} E) :
    IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E) :=
  isCompactObject_of_isPerfect _ (isPerfect_derivedPushforward_of_isCompactObject_of_flat f E hE)

/-- Let `Y` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ Y` be proper, flat and of
finite presentation, and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then
`a` commutes with direct sums. -/
@[stacks 0E4I]
theorem preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_flat
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⊣ a) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) a :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  preservesColimitsOfShape_rightAdjoint_of_isCompactObject_map f _ adj
    (isCompactObject_quasiCoherentDerivedPushforward_of_flat f _) J

end Stacks.Duality
