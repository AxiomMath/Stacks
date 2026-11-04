module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpQuasiProjectiveUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowups in ideals of finite type are quasi-projective

The blowup `b : X' ⟶ X` of a scheme in a quasi-coherent sheaf of ideals of finite type is
quasi-projective: it is proper, in particular of finite type, and the twist `𝒪_{X'}(1)` is an
invertible module ample relative to `b` (Stacks 02NS, part (2)). Over a base carrying an ample
invertible module it is therefore H-projective (Stacks 087S, part (1)).

## Main results

* `AlgebraicGeometry.C1573.isProjectiveMorphism_blowUpToBase`: over a base carrying an ample
  invertible module it is H-projective.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
-/

namespace AlgebraicGeometry.C1573
end AlgebraicGeometry.C1573

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry.C1573
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Over a base carrying an ample invertible module, the blowup in a quasi-coherent ideal of
finite type is H-projective.** -/
@[ega "IV 19.4.1" "special case"]
theorem C1573.isProjectiveMorphism_blowUpToBase (hI : I.IsFiniteType) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (hM : Stacks.Ample.IsAmple X M) :
    IsProjectiveMorphism (blowUpToBase I) := by
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase_of_fg I fun U => hI U
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective _ M hM (isQuasiProjective_blowUpToBase I hI),
      inferInstance⟩

end AlgebraicGeometry

end
