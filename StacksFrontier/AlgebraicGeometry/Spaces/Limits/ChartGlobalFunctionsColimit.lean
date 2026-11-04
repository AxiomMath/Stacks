module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism

/-!
# Global functions on the limit of the affine chart system

In Situation 084R let `U₀ → X₀` be an affine scheme-valued point of the chosen stage and let
`Uᵢ = U₀ ×_{X₀} Xᵢ` be the system of its base changes, which is a system of *affine* schemes
because the transition morphisms of the situation are affine. This file records that the ring
of global functions of the limit of that system is the directed colimit of the rings of global
functions of its stages:

`Γ(U, 𝒪_U) = colim_{i ≥ 0} Γ(Uᵢ, 𝒪_{Uᵢ})`.

In the proof of Stacks 07SQ this is the statement that lets the coordinates `h₁, …, hₙ` of the
chart over the limit be chosen already at a finite stage, which is what display 70.5.10.1 — the
square of Stacks 084U — needs in order to exist at that stage.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_chartStages_appTop`: the colimit
  assertion for the chart system.

## Implementation notes

*Nothing new is proved.* This is the structure-sheaf case of Stacks 01Z0, already available as
`AlgebraicGeometry.isStagesColimit_appTop_of_isLimit_of_directed` for a directed inverse system
of quasi-compact quasi-separated schemes with affine transition morphisms, instantiated at the
chart system. The three instance hypotheses of that result are all free here because every
stage of the chart system is affine: quasi-compactness and quasi-separatedness of an affine
scheme are instances, and a morphism between affine schemes is an affine morphism by
`AlgebraicGeometry.isAffineHom_of_isAffine`. The one input supplied by hand is affineness of
the stages, `AlgebraicGeometry.Space.LimitSituation.isAffine_chartStagesDiagram_obj`.

*Why it is worth stating.* The library builds the chart system and its limiting cone
(`AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram`,
`.chartStagesCone`, `.isLimit_chartStagesCone`) and separately proves the colimit assertion for
an abstract qcqs system, but nowhere puts the two together; the equalizer-presentation files
that consume the chart system consume its *sections* rather than this colimit. The point of
Stacks 07SQ at which the coordinates are descended is the one place the combination is needed.

*The index.* The index is `AlgebraicGeometry.Space.LimitSituation.Stages`, the stages at or
beyond the chosen one, which is a nonempty directed preorder in the universe of the site. The
universe restriction is not removable; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) (V : BigAffineFppf B S hS)
  (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- **The global functions of the limit of the chart system are the colimit of the global
functions of its stages.** For an affine scheme-valued point `U₀ ⟶ X₀` of the chosen stage of a
limit situation, the affine schemes `Uᵢ = U₀ ×_{X₀} Xᵢ` have a limit `U`, and
`Γ(U, 𝒪_U) = colim_i Γ(Uᵢ, 𝒪_{Uᵢ})`.

This is the structure-sheaf case of Stacks 01Z0,
`AlgebraicGeometry.isStagesColimit_appTop_of_isLimit_of_directed`, instantiated at the chart
system; every stage being affine, that result's affineness, quasi-compactness and
quasi-separatedness hypotheses are all instances.

In the proof of Stacks 07SQ this is what descends the coordinates `hν` of the étale chart from
the limit to a finite stage, so that the square of Stacks 084U can be formed there. No
`@[stacks]` attribute is attached: the tag 01Z0 is already carried, keyed to the structure
sheaf, by the result this instantiates. -/
theorem isStagesColimit_chartStages_appTop (hI : #A.I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit
      (G := fun a : A.Stages => (Γ((A.chartStagesDiagram V g).obj (op a), ⊤) : Type u))
      (T := (Γ((A.chartStagesCone V g hI).pt, ⊤) : Type u))
      (fun (a b : A.Stages) (h : a ≤ b) x =>
        ((A.chartStagesDiagram V g).map (homOfLE h).op).appTop.hom x)
      (fun (a : A.Stages) x => ((A.chartStagesCone V g hI).π.app (op a)).appTop.hom x) := by
  have : ∀ a, IsAffine ((A.chartStagesDiagram V g).obj a) :=
    A.isAffine_chartStagesDiagram_obj V g
  exact isStagesColimit_appTop_of_isLimit_of_directed (A.chartStagesDiagram V g)
    (A.chartStagesCone V g hI) (A.isLimit_chartStagesCone V g hI)

end AlgebraicGeometry.Space.LimitSituation

end
