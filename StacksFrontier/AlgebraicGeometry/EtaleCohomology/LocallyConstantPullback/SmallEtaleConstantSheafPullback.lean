module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients

/-!
# The inverse image of a constant abelian sheaf on Mathlib's small étale site

For a morphism of schemes `f : T ⟶ Z`, the inverse image `f⁻¹` on abelian sheaves of the small
étale sites carries the constant sheaf with value `M` to the constant sheaf with value `M`,
naturally in `M`. The isomorphism is the general
`Stacks.ConstantSheaf.sheafPullbackConstantSheafIso` for the base change functor of small étale
sites, which carries the final object `Z ⟶ Z` to a final object: both `C_Z ⋙ f⁻¹` and `C_T` are
left adjoint to sections over the final object, so they agree. Its unit-level description is what
the consumers of this form use.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbConstantSheafIso` — `f⁻¹ M̲ ≅ M̲`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {T Z : Scheme.{u}} (f : T ⟶ Z)

/-- **The inverse image of a constant abelian sheaf is the constant sheaf with the same value**,
on small étale sites: base change carries the final object to the final object. -/
def smallEtalePullbackAbConstantSheafIso :
    constantSheaf Z.smallEtaleTopology Ab.{u + 1} ⋙ smallEtalePullbackAb f ≅
      constantSheaf T.smallEtaleTopology Ab.{u + 1} :=
  Stacks.ConstantSheaf.sheafPullbackConstantSheafIso (smallEtaleBaseChange f) Ab.{u + 1}
    Z.smallEtaleTopology T.smallEtaleTopology (isTerminalEtaleMkId Z) (isTerminalEtaleMkId T)
    (((isTerminalEtaleMkId Z).isTerminalObj (smallEtaleBaseChange f)).uniqueUpToIso
      (isTerminalEtaleMkId T))

end Stacks.EtaleCohomology
