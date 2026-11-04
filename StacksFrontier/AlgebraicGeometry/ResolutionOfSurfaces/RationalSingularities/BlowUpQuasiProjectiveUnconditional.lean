module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.TwistAmple
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup in an ideal sheaf of finite type is quasi-projective

The blowup morphism `b : X' ⟶ X` of a scheme in a quasi-coherent ideal sheaf of finite type is
quasi-projective: it is of finite type, and the twisting sheaf `𝒪_{X'}(1)` is a `b`-relatively
ample invertible module ([Stacks, Tag 02NS], part (2)).

## Main results

* `AlgebraicGeometry.isQuasiProjective_blowUpToBase`: the blowup morphism in an ideal sheaf of
  finite type is quasi-projective.
* `AlgebraicGeometry.blowUpIsQuasiProjective`: the hypothesis
  `AlgebraicGeometry.BlowUpIsQuasiProjective` holds.

## Implementation notes

The relative ampleness of the twist,
`AlgebraicGeometry.isRelativelyAmple_twist_reesSituation`, is stated over a transition datum for
the chart twists. That datum is constructed, with no hypothesis, as
`Stacks.RelativeProj.Situation.twistTransition`, so the twist used here is
`Stacks.RelativeProj.Situation.twistSheaf`.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The blowup in a quasi-coherent ideal sheaf of finite type is quasi-projective.** The
blowup morphism is proper, hence of finite type, and `𝒪_{X'}(1)` is an invertible module which is
ample relative to it ([Stacks, Tag 02NS], part (2)), for the transition datum of the chart twists
constructed in `Stacks.RelativeProj.Situation.twistTransition`. -/
@[ega "II 4.6.18" "special case"]
theorem isQuasiProjective_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : Scheme.IdealSheafData.IsFiniteType I) : IsQuasiProjective (blowUpToBase I) := by
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase_of_fg I fun U => hI U
  exact ⟨⟨inferInstance, inferInstance⟩,
    Stacks.RelativeProj.Situation.twist
      (Stacks.RelativeProj.Situation.twistTransition (reesSituation I) 1),
    inferInstance,
    isRelativelyAmple_twist_reesSituation I hI
      (Stacks.RelativeProj.Situation.twistTransition (reesSituation I) 1)⟩

/-- The hypothesis `AlgebraicGeometry.BlowUpIsQuasiProjective` holds: every blowup morphism in a
quasi-coherent ideal sheaf of finite type is quasi-projective. -/
theorem blowUpIsQuasiProjective : BlowUpIsQuasiProjective.{u} := by
  unfold BlowUpIsQuasiProjective
  intro X I hI
  exact isQuasiProjective_blowUpToBase I hI

end AlgebraicGeometry

end
