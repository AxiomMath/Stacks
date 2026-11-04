module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Local
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# Universal catenarity of a scheme with a dualizing complex

A locally Noetherian scheme carrying a dualizing complex is universally catenary. Over an affine
open `U` the complex is the sheaf associated to a dualizing complex over `Γ(X, U)`, so that ring
is universally catenary, and universal catenarity of a locally Noetherian scheme is exactly that
condition over every affine open.

## Main results

* `Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex` — a locally Noetherian scheme with
  a dualizing complex is universally catenary.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe w u

namespace Stacks.Duality

/-- A locally Noetherian scheme carrying a dualizing complex is universally catenary. -/
theorem isUniversallyCatenary_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    AlgebraicGeometry.Scheme.IsUniversallyCatenary X := by
  refine (Scheme.isUniversallyCatenary_iff_forall_affineOpens X).mpr fun U => ?_
  have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨ω, hω, -⟩ := hK (U : X.Opens) U.property
  exact Dualizing.isUniversallyCatenary_of_isDualizingComplex hω

end Stacks.Duality

end
