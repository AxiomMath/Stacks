module

public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.ProjTwistQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Further results on `Basic`

Results about the objects of `StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic` that need
imports beyond those of that module.

## Main definitions

* `unitModuleIsoTwistingSheafZero_unconditional`: the isomorphism `𝒪_X ≅ 𝒪(0)` on `Proj 𝒜`, for
  an arbitrary nonnegatively graded ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v w

namespace Stacks.AlgebraicGeometry.ProjTwistPowers

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)]

/-- **`𝒪_X ≅ 𝒪(0)`**, for an arbitrary nonnegatively graded ring and with no generation
hypothesis: it is the inverse of
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`, which reads a section of
`𝒪(0)` as a section of `𝒪_X` through `HomogeneousLocalization.val` — in degree zero a local
fraction of the twist already has numerator and denominator of equal degree. -/
def unitModuleIsoTwistingSheafZero_unconditional :
    Stacks.Ample.unitModule (AlgebraicGeometry.Proj 𝒜) ≅ twistingSheaf 𝒜 0 :=
  (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit 𝒜).symm

end Stacks.AlgebraicGeometry.ProjTwistPowers

end
