module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# Modules on the small étale site of a scheme have enough injectives

Let `S` be a scheme of a big étale site `B`. The `𝒪`-modules on the small étale site of `S`
form a Grothendieck abelian category at module universe `u`, hence have enough injectives and
injective resolutions.

## Main results

* `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_smallEtaleModules`: the `𝒪`-modules on the
  small étale site of `S` form a Grothendieck abelian category at module universe `u`.
* `AlgebraicGeometry.SmallEtale.enoughInjectives_smallEtaleModules`: they have enough injectives.
* `AlgebraicGeometry.SmallEtale.hasInjectiveResolutions_smallEtaleModules`: they have injective
  resolutions.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules on the small étale site of `S` are Grothendieck abelian at module
universe `u`. -/
public theorem isGrothendieckAbelian_smallEtaleModules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (structureSheaf B S hS)

/-- The `𝒪`-modules on the small étale site of `S` have enough injectives. -/
public noncomputable instance enoughInjectives_smallEtaleModules :
    EnoughInjectives (SheafOfModules.{u} (structureSheaf B S hS)) :=
  haveI := isGrothendieckAbelian_smallEtaleModules B S hS
  inferInstance

/-- The `𝒪`-modules on the small étale site of `S` have injective resolutions. -/
public noncomputable instance hasInjectiveResolutions_smallEtaleModules :
    HasInjectiveResolutions (SheafOfModules.{u} (structureSheaf B S hS)) :=
  haveI := isGrothendieckAbelian_smallEtaleModules B S hS
  inferInstance

end AlgebraicGeometry.SmallEtale

end
