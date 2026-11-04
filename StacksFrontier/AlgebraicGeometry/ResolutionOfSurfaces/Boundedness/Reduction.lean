module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.RingTheory.Length.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to rational singularities

For a domain `A`, reduction to rational singularities is possible when the lengths of
`H¹(X, 𝒪_X)` over `A` are bounded as `X` ranges over all normal modifications of `Spec A`.

## Main definitions

* `AlgebraicGeometry.firstCohomologyAsBaseModule` is `H¹(X, 𝒪_X)`, regarded as a module over
  the base ring of a morphism `X ⟶ Spec A`.
* `AlgebraicGeometry.IsReductionToRationalSingularitiesPossible` expresses the uniform finite
  bound on the lengths of these modules.

## References

* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The first cohomology `H¹(X, 𝒪_X)` of the structure sheaf of `X`, computed by the first right
derived functor of global sections on sheaves of `𝒪_X`-modules and regarded as an `A`-module by
restriction of scalars along the map `A ⟶ Γ(X, 𝒪_X)` induced by `X ⟶ Spec A`. -/
def firstCohomologyAsBaseModule {A : Type u} [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) : ModuleCat.{u} A :=
  letI : (SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).Additive := {}
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
    (((SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))

/-- Reduction to rational singularities is possible for `A` if the `A`-module lengths of
`H¹(X, 𝒪_X)` have a common finite bound over all normal modifications `X ⟶ Spec A`. -/
@[stacks 0B4N "reduction_to_rational_singularities_possible"]
abbrev IsReductionToRationalSingularitiesPossible (A : Type u) [CommRing A] [IsDomain A] :
    Prop :=
  ∃ n : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
    Module.length A (firstCohomologyAsBaseModule X f) ≤ n

end AlgebraicGeometry
