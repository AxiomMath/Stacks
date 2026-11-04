module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Castelnuovo–Mumford regularity

A coherent sheaf on projective `n`-space over a field is `m`-regular when its `i`-th cohomology
after twisting by `m - i` vanishes for every `1 ≤ i ≤ n`.

## Main definitions

* `AlgebraicGeometry.IsMRegular` is `m`-regularity of a coherent sheaf on projective space.

## Implementation notes

Projective space over a field is the base change of integral projective space, and its sheaf
twist is the pullback of the integral twisting sheaf. Cohomology is the right-derived
global-sections group over the whole space, which requires enough injectives in the category of
module sheaves; these are supplied by a scoped instance, since that category is Grothendieck
abelian. Vanishing is expressed by `IsZero`, so clients can use the predicate directly at each
degree.

## References

* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The category of module sheaves on projective space over a field has enough injectives,
being Grothendieck abelian. -/
noncomputable scoped instance modulesEnoughInjectives (k : Type u) [Field k] (n : ℕ) :
    EnoughInjectives ((projectiveSpaceOverRing n (.of k)).Modules) :=
  IsGrothendieckAbelian.enoughInjectives

/-- A coherent sheaf on projective `n`-space over `k` is `m`-regular if its
cohomology in degree `i` vanishes after the twist by `m - i`, for `1 ≤ i ≤ n`. -/
@[stacks 08A3]
public noncomputable abbrev IsMRegular (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ n →
    IsZero (Hgroup (projectiveSpaceOverRing n (.of k)).ringCatSheaf ⊤ i
      (projectiveTwist n F (m - i)))

end AlgebraicGeometry

end
