module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesReindex

/-!
# The regular functions on the chart of a limit are the colimit of those on the stage charts

Let `A` be a limit situation and let `C` be the chart system of an affine scheme-valued point
`U₀ ⟶ X₀` of its chosen stage, so that the chart of the stage `i` is `Uᵢ = Xᵢ ×_{X₀} U₀` and the
chart of the limit is `U = X ×_{X₀} U₀`. All of these are affine schemes and `U = lim Uᵢ`. Hence

`Γ(U, 𝒪_U) = colim_i Γ(Uᵢ, 𝒪_{Uᵢ})`

elementwise, as a `Stacks.IsStagesColimit`.

This is the affine case of Stacks 01Z0 for the structure sheaf,
`AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`, read on the chart
system through the reindexing of `StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesReindex`:
that case is stated for an inverse system indexed by the opposite of a nonempty directed
preorder, while a chart system is indexed by the slice of the index category over the chosen
index, and `AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence` identifies the two.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_chartAppTop`: the colimit
  description, in the elementwise form `Stacks.IsStagesColimit`.
* `AlgebraicGeometry.Space.LimitSituation.exists_stage_chartAppTop_eq` and
  `AlgebraicGeometry.Space.LimitSituation.exists_ge_chartAppTop_eq`: its two substantive
  clauses, named separately because they are what a lift of finitely many elements and of
  finitely many relations out of the limit consumes.

## Implementation notes

*Why this is stated for the chart system rather than proved again.* The two halves of the affine
case — that a global section of a limit of affine schemes comes from a stage, and that one dying
in the limit dies at a stage — are
`AlgebraicGeometry.exists_appTop_eq_of_isAffine_of_isLimit_of_directed` and its vanishing
counterpart, both already proved for an arbitrary inverse system of affine schemes over a
directed preorder. Nothing about charts enters them. What the chart system contributes is only
that its reindexed diagram consists of affine schemes
(`AlgebraicGeometry.Space.LimitSituation.isAffine_stagesSchemeDiagram_obj`) and that the
reindexed cone of a limit bridge is limiting
(`AlgebraicGeometry.Space.LimitSituation.isLimit_stagesSchemeCone`), so the whole content of
this file is supplying those two to the general statement.

*What consumes it.* The proof of Stacks 07SQ chooses, over the limit, finitely many regular
functions on the chart of the limit — the images of the coordinates of a presentation of the
étale algebra — and lifts them, together with the finitely many relations they satisfy, to a
single stage; that is exactly the two clauses below, applied `n` times and then `n` times again
after taking an upper bound. The resulting homomorphism out of the presentation is
`AlgebraicGeometry.Space.coordinateHom`, and the square it sits in is Stacks 084U,
`AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : LimitSituation B S hS hZ X) {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
    (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
    (L : AffineChartSystem.LimitBridge C)

/-- **The regular functions on the chart of the limit are the filtered colimit of the regular
functions on the charts of the stages.** The chart system's reindexed diagram is a diagram of
affine schemes and the reindexed cone of its limit bridge is limiting, so this is the affine case
of Stacks 01Z0 for the structure sheaf. -/
theorem isStagesColimit_chartAppTop :
    Stacks.IsStagesColimit
      (G := fun i : A.Stages => (Γ((stagesSchemeDiagram A C).obj (op i), ⊤) : Type u))
      (T := (Γ((stagesSchemeCone A C L).pt, ⊤) : Type u))
      (fun (i j : A.Stages) (h : i ≤ j) x =>
        ((stagesSchemeDiagram A C).map (homOfLE h).op).appTop.hom x)
      (fun (i : A.Stages) x => ((stagesSchemeCone A C L).π.app (op i)).appTop.hom x) := by
  have : ∀ a : (A.Stages)ᵒᵖ, IsAffine ((stagesSchemeDiagram A C).obj a) :=
    fun a => isAffine_stagesSchemeDiagram_obj A C a
  exact isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed
    (stagesSchemeDiagram A C) (stagesSchemeCone A C L) (isLimit_stagesSchemeCone A C L)

/-- **A regular function on the chart of the limit comes from the chart of a stage.** -/
theorem exists_stage_chartAppTop_eq (t : Γ((stagesSchemeCone A C L).pt, ⊤)) :
    ∃ (i : A.Stages) (x : Γ((stagesSchemeDiagram A C).obj (op i), ⊤)),
      ((stagesSchemeCone A C L).π.app (op i)).appTop.hom x = t :=
  (isStagesColimit_chartAppTop A C L).exists_stage t

/-- **Two regular functions on the chart of a stage with the same restriction to the chart of the
limit already agree on the chart of a later stage.** -/
theorem exists_ge_chartAppTop_eq (i : A.Stages)
    (x y : Γ((stagesSchemeDiagram A C).obj (op i), ⊤))
    (hxy : ((stagesSchemeCone A C L).π.app (op i)).appTop.hom x =
      ((stagesSchemeCone A C L).π.app (op i)).appTop.hom y) :
    ∃ (j : A.Stages) (h : i ≤ j),
      ((stagesSchemeDiagram A C).map (homOfLE h).op).appTop.hom x =
        ((stagesSchemeDiagram A C).map (homOfLE h).op).appTop.hom y :=
  (isStagesColimit_chartAppTop A C L).exists_trans_eq i x y hxy

end AlgebraicGeometry.Space.LimitSituation

end
