module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.SectionRingVeroneseChart.IntegerDegree

/-!
# Under the identification `P = Proj A` the twists are the tensor powers

Let `P` be a proper scheme over a ring `R`, let `𝓛` be an ample invertible `𝒪_P`-module and set
`A = ⨁_{m ≥ 0} Γ(P, 𝓛^{⊗ m})`, so that `P = Proj A`
(`Stacks.SectionRingProjIso.projIsoOfIsProper`). Under this identification the twist `𝒪_P(m)` is
the integral tensor power `𝓛^{⊗ m}`, for every integer `m`.

## Main definitions

* `Stacks.SectionRingProjIso.twistIsoTensorPow`: the isomorphism `𝒪_P(m) ≅ 𝓛^{⊗ m}`, for every
  integer `m`, between the pullback along `Stacks.SectionRingProjIso.projIsoOfIsProper` of the
  `m`-th twisting sheaf of `Proj A` and `𝓛^{⊗ m}`.

## Implementation notes

The isomorphism is the comparison `Stacks.SectionRingVeroneseChart.twistComparisonIso` of
Situation 01QH, which needs only ampleness; properness makes the morphism along which the twist is
pulled back an isomorphism.

## References

* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.AmpleFiniteAvoidance (grading)

universe u

namespace Stacks.SectionRingProjIso

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Under the identification `P = Proj A` the twist `𝒪_P(m)` is the integral tensor power
`𝓛^{⊗ m}`**, for every integer `m`: the pullback along
`Stacks.SectionRingProjIso.projIsoOfIsProper` of the `m`-th twisting sheaf of `Proj Γ_*(P, 𝓛)` is
isomorphic to `𝓛^{⊗ m}`. -/
def twistIsoTensorPow (hL : Stacks.Ample.IsAmple X L) {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    [IsProper f] (m : ℤ) :
    (Scheme.Modules.pullback (projIsoOfIsProper L hL f).hom).obj
        (twistingSheaf (grading L) m) ≅
      tensorPowModule X L m :=
  Stacks.SectionRingVeroneseChart.twistComparisonIso L hL m

end Monoidal

end Stacks.SectionRingProjIso

end
