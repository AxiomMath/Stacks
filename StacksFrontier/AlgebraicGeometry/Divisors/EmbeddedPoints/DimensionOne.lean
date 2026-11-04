module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.SerreStructureSheaf

/-!
# Cohen--Macaulay schemes of dimension at most one

A locally Noetherian scheme of dimension at most one is Cohen--Macaulay if and only if it has
no embedded points.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one`
  characterizes Cohen--Macaulay schemes of dimension at most one by the absence of embedded
  points.

## Implementation notes

Cohen--Macaulayness is `AlgebraicGeometry.IsCohenMacaulay`, which is Serre's condition `(Sₖ)`
for every `k`, and the absence of embedded points is `AlgebraicGeometry.HasNoEmbeddedPoints`.
Under the dimension bound all of those conditions collapse to `(S₁)`, because the support
dimension that `(Sₖ)` compares against is the Krull dimension of a stalk and so is at most one.
Serre's condition `(S₁)` for the scheme is the same as `(S₁)` for the structure sheaf read as a
module over itself, since the stalk of that module is the local ring; the absence of embedded
points for that module is then [Stacks, Tag 0346].

Two definitionally equal module structures on the stalk of a presheaf of modules are in scope,
the one built by hand in [Stacks, Tag 01CB] and `PresheafOfModules`' own. Serre's condition for
a sheaf of modules is stated against the first and the identification of the structure-sheaf
stalk with the local ring against the second, so the two are compared here.

## References

* [Stacks Project, Tag 0BXG](https://stacks.math.columbia.edu/tag/0BXG)
* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

private theorem ringKrullDim_stalk_le_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ 1) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk] at hX
  exact (le_iSup_of_le x le_rfl).trans hX

private theorem all_propertySk_iff_propertySk_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ 1) :
    (∀ k : ℕ, HasPropertySk X k) ↔ HasPropertySk X 1 := by
  refine ⟨fun h => h 1, fun h k => ?_⟩
  rw [hasPropertySk_iff] at h ⊢
  exact fun x => (min_le_right _ _).trans
    ((min_eq_right (ringKrullDim_stalk_le_one hX x)).ge.trans (h x))

/-- Serre's condition `(S₁)` for the structure sheaf read as a module over itself is Serre's
condition for the scheme: the stalk of that module is the local ring. -/
private lemma serre_one_structureSheaf_iff (X : Scheme.{u}) (x : X) :
    (min (1 : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule X).val.presheaf x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule X).val.presheaf x) :
          WithBot ℕ∞)) ↔
    (min (1 : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) : WithBot ℕ∞)) := by
  rw [Module.supportDim_eq_of_equiv (structureSheafStalkLinearEquiv X x),
    Module.depth_eq_depth_of_linearEquiv
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (structureSheafStalkLinearEquiv X x),
    Module.supportDim_self_eq_ringKrullDim]

/-- A locally Noetherian scheme of dimension at most one is Cohen--Macaulay if and only if it
has no embedded points. -/
@[stacks 0BXG, ega "IV 7.2.1.1" "a) <=> c)", ega "IV 5.7.8" "more general"]
theorem isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ 1) :
    IsCohenMacaulay X ↔ HasNoEmbeddedPoints X := by
  rw [isCohenMacaulay_iff_forall_hasPropertySk, all_propertySk_iff_propertySk_one hX]
  let F := SheafOfModules.unit X.ringCatSheaf
  have : F.IsCoherent := by
    dsimp [F]
    infer_instance
  rw [← AlgebraicGeometry.structureSheaf_sheafHasPropertySk_one_iff X]
  simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint] using
    (hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one X F).symm

end AlgebraicGeometry

end
