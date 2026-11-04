module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksCore.Tactic.StacksAttribute

/-!
# The blowup of a regular scheme at a closed point of dimension two is regular

Let `X` be a regular scheme and let `w ∈ X` be a closed point whose local ring is regular of
dimension two. Then the blowup `b : X' ⟶ X` of `X` at `w` — the blowup in the ideal sheaf
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of the closed subset `{w}` — is again a
regular scheme.

This is the relative form of the regularity of the blowup of `Spec A` at the closed point for
`A` a two-dimensional regular local ring.

## Main results

* `AlgebraicGeometry.isRegular_blowUp_vanishingIdeal_of_isRegular`:
  `IsRegular (blowUp (vanishingIdeal {w}))` at a closed point `w` of a regular scheme whose local
  ring there has dimension two.
* `AlgebraicGeometry.isRegular_blowUp_vanishingIdeal_of_forall_isRegularLocalRing`: the same with
  the regularity of `X` unbundled into local Noetherianity plus regularity of every local ring.

## References

* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The blowup of a locally Noetherian scheme with regular local rings at a closed point whose
local ring has dimension two is a regular scheme. -/
@[ega "IV 19.4.11" "(iii), special case"]
theorem isRegular_blowUp_vanishingIdeal_of_forall_isRegularLocalRing {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y)) (w : X)
    (hw : IsClosed ({w} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk w) = 2) :
    IsRegular (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X))) :=
  (isRegular_iff_regular_stalks _).mpr ⟨LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase _),
    isRegularLocalRing_stalk_blowUp w hw hreg hdim _ rfl⟩

/-- The blowup of a regular scheme at a closed point whose local ring is regular of dimension two
is again a regular scheme. The case `X = Spec A`, for `A` a two-dimensional regular local ring
and `w` its closed point, is `AlgebraicGeometry.isRegular_blowUp_maximalIdeal`. -/
@[stacks 0AGR "regularity, relative form: the blowup of a regular scheme at a closed point whose \
local ring is regular of dimension two is regular. The absolute statement, for Spec of a \
two-dimensional regular local ring, is isRegular_blowUp_maximalIdeal",
  ega "IV 19.4.11" "(iii), special case"]
theorem isRegular_blowUp_vanishingIdeal_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) (w : X)
    (hw : IsClosed ({w} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk w) = 2) :
    IsRegular (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X))) :=
  have h := (isRegular_iff_regular_stalks X).mp hX
  have : IsLocallyNoetherian X := h.1
  isRegular_blowUp_vanishingIdeal_of_forall_isRegularLocalRing h.2 w hw hdim

end AlgebraicGeometry

end
