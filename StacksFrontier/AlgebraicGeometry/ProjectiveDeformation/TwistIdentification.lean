module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.UniformDegreeBound
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.TwistIdentification

/-!
# Deformations of projective schemes: the twist identification

`StacksFrontier/AlgebraicGeometry/ProjectiveDeformation/UniformDegreeBound.lean` derives conclusions
(4) and (5) of [Stacks, Tag 0D4F] from the statement `RelativeAmpleTwistIdentification`: for `L`
ample relative to a quasi-compact quasi-separated `g`, the canonical morphism
`r : Y ⟶ Proj_T(⨁_{d ≥ 0} g_* L^{⊗ d})` of [Stacks, Tag 01VJ] pulls the first Serre twist back to
`L`. This file proves that statement.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.relativeAmpleTwistIdentification`:
  **`RelativeAmpleTwistIdentification` is a theorem**, [Stacks, Tag 01QI] (2) relative to a base
  in degree one, which is `Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
-/

@[expose] public section

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

/-- **`RelativeAmpleTwistIdentification` is a theorem.** For `L` ample relative to a quasi-compact
quasi-separated `g`, the isomorphism `r^* 𝒪(1) ≅ L` is the degree-one component of the map `θ` of
[Stacks, Tag 01O9] for the adjunction map, an isomorphism by [Stacks, Tag 01QI] (2) relative to the
base (`Stacks.RelativeAmple.TwistIdentification.isIso_theta_one_directImagePowerMap`). -/
public theorem relativeAmpleTwistIdentification : RelativeAmpleTwistIdentification.{u} :=
  fun _ _ g _ _ M _ hM =>
    ⟨Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso g M hM⟩

end Stacks.AlgebraicGeometry.ProjectiveDeformation
