module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitModulePullbackSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitModulePullbackSystemFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituationExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyLimitSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyLimitStageDescent

/-!
# The resolution property of a limit of algebraic spaces (Stacks 0GV2)

Let `X = lim X_i` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms.  Then `X` has the resolution property
if and only if some `X_i` has it.

The direction from a stage to the limit is
`AlgebraicGeometry.Space.hasResolutionProperty_limitAlgebraicSpace_of_stage`.  The direction from
the limit to a stage is the source's argument, carried out in
`AlgebraicGeometry.Space.exists_stage_hasResolutionProperty_of_inputs`; this file discharges its
inputs.

## Main results

* `AlgebraicGeometry.Space.hasResolutionProperty_limitAlgebraicSpace_iff`: **Stacks 0GV2.**

## Implementation notes

The inputs of `exists_stage_hasResolutionProperty_of_inputs` are: the faithfulness and fullness
clauses of the colimit assertion of Stacks 07V7 for the system
(`limitModulePullbackSystem_faithfulness`, `limitModulePullbackSystem_fullness`), Stacks 0D2X(1)
(`exists_isFiniteLocallyFreeOnSite_stage_model`), and the existence of the situation of
Stacks 0GUY with `π` finite and of finite presentation
(`ResolutionPropertyDescentSituation.exists_isFinitePresentation`, through Zariski's main theorem
in the form of Stacks 0874).  The converse of Stacks 0GV1 used in the last step is
`hasResolutionProperty_of_epi_idealDirectImage_of_isFinitePresentationOnSite`, proved without
Noetherian hypotheses for `π_*𝒪_Y` of finite presentation; the source instead reduces it to the
Noetherian case by absolute Noetherian approximation.

## References

* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **Stacks 0GV2.**  Let `X = lim X_i` be the limit of a cofiltered system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms.  Then `X` has the
resolution property if and only if some `X_i` has it.

The system is indexed by a cofiltered category, which contains the directed systems of the
source; the bounds `hSize` and `hHomSize` on the index are those under which the limit of the
presheaves `D` is an algebraic space of the big fppf site (`limitAlgebraicSpace`, Stacks 07SF).

If `X_i` has the resolution property, so does `X`, by the affine case of Stacks 0GUU along the
affine projection `X ⟶ X_i`.  Conversely, the proof is the source's; see the module
documentation. -/
@[stacks 0GV2]
theorem hasResolutionProperty_limitAlgebraicSpace_iff
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) :
    HasResolutionProperty.{u, u} B S hS
        (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
        (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2 ↔
      ∃ i, HasResolutionProperty.{u, u} B S hS (D.obj i) (hD i) := by
  refine ⟨fun hres => ?_, fun ⟨i, h⟩ =>
    hasResolutionProperty_limitAlgebraicSpace_of_stage B S hS hZ D hSize hHomSize hD hAffine i
      (hqc i) (hqs i) h⟩
  refine exists_stage_hasResolutionProperty_of_inputs B S hS hZ D hSize hHomSize hD hAffine hqc hqs
    (limitModulePullbackSystem_faithfulness B S hS D hSize hHomSize hD hAffine hqc)
    (limitModulePullbackSystem_fullness B S hS D hSize hHomSize hD hAffine hZ hqc hqs)
    (fun F hF => ?_) (fun X hXqc hXqs => ?_) hres
  · obtain ⟨i, G, hG, ⟨ε⟩⟩ := exists_isFiniteLocallyFreeOnSite_stage_model B S hS D hSize
      hHomSize hD hAffine hZ hqc hqs F hF
    exact ⟨i, G, hG, ⟨ε.symm⟩⟩
  · obtain ⟨sit, -, -, hfp⟩ :=
      ResolutionPropertyDescentSituation.exists_isFinitePresentation B S hS hZ X hXqc hXqs
    exact ⟨sit, hfp⟩

end AlgebraicGeometry.Space

end
