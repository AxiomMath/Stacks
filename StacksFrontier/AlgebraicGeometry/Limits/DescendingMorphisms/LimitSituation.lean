module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Situation
public import StacksFrontier.CategoryTheory.Filtered.UpSetCofinal

/-!
# Situation 081D: a morphism over one stage of a limit of schemes

Let `S = lim S_i` be the limit of a directed inverse system of schemes with affine transition
morphisms, let `0` be an index, and let `f₀ : X₀ ⟶ Y₀` be a morphism of schemes over `S₀` with
`S₀`, `X₀` and `Y₀` quasi-compact and quasi-separated. Nothing is assumed of the stages `S_i` for
`i` not above `0`. This is Situation 081D of the Stacks project, recorded as
`AlgebraicGeometry.MorphismLimitSituation`.

The descent results of this directory are stated for
`AlgebraicGeometry.MorphismDescentSituation`, which also asks every stage of the system to be
quasi-compact and quasi-separated. Restricting the system to the cofinal set of stages
`{i // 0 ≤ i}` produces such a situation, with the same limit, the same `f₀`, the same base
changes `f_i` for `i ≥ 0` and the same base change `f`, so those results apply to Situation 081D
as stated.

## Main definitions

* `AlgebraicGeometry.MorphismLimitSituation`: Situation 081D.
* `AlgebraicGeometry.MorphismLimitSituation.stageHom`,
  `AlgebraicGeometry.MorphismLimitSituation.limitHom`: the base changes `f_i` and `f` of `f₀`.
* `AlgebraicGeometry.MorphismLimitSituation.toMorphismDescentSituation`: the restriction of the
  system to the stages `i ≥ 0`, as a `AlgebraicGeometry.MorphismDescentSituation`.

## Main results

* `AlgebraicGeometry.MorphismLimitSituation.compactSpace_stage`,
  `AlgebraicGeometry.MorphismLimitSituation.quasiSeparatedSpace_stage`: every stage `S_i` with
  `i ≥ 0` is quasi-compact and quasi-separated, being affine over `S₀`.
* `AlgebraicGeometry.MorphismLimitSituation.toMorphismDescentSituation_stageMap`,
  `AlgebraicGeometry.MorphismLimitSituation.toMorphismDescentSituation_limitHom`: the restriction
  has the same transition morphisms `S_i ⟶ S₀` and the same morphism `f`.

## References

* [Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **Stacks 081D.** A directed inverse system `(S_i)` of schemes with affine transition
morphisms, a chosen limit cone `S = lim S_i`, a chosen index `0`, and a morphism `f₀ : X₀ ⟶ Y₀` of
schemes over `S₀`, where `S₀`, `X₀` and `Y₀` are quasi-compact and quasi-separated. -/
@[stacks 081D "the base changes f_i (i ≥ 0) and f are stageHom and limitHom; \
toMorphismDescentSituation restricts to the cofinal stages i ≥ 0, which are qcqs"]
structure MorphismLimitSituation (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The inverse system of schemes. -/
  system : Iᵒᵖ ⥤ Scheme.{u}
  /-- Every transition morphism in the inverse system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (system.map f)
  /-- The chosen cone exhibiting the limit `S` and its projections. -/
  limitCone : Cone system
  /-- The chosen cone is limiting. -/
  isLimit : IsLimit limitCone
  /-- The chosen index `0`. -/
  base : I
  /-- `S₀` is quasi-compact. -/
  quasiCompact_base : CompactSpace (system.obj (op base))
  /-- `S₀` is quasi-separated. -/
  quasiSeparated_base : QuasiSeparatedSpace (system.obj (op base))
  /-- The scheme `X₀`, given as a scheme over `S₀`. -/
  source : Over (system.obj (op base))
  /-- The scheme `Y₀`, given as a scheme over `S₀`. -/
  target : Over (system.obj (op base))
  /-- The morphism `f₀ : X₀ ⟶ Y₀` of schemes over `S₀`. -/
  hom : source ⟶ target
  /-- `X₀` is quasi-compact. -/
  quasiCompact_source : CompactSpace source.left
  /-- `X₀` is quasi-separated. -/
  quasiSeparated_source : QuasiSeparatedSpace source.left
  /-- `Y₀` is quasi-compact. -/
  quasiCompact_target : CompactSpace target.left
  /-- `Y₀` is quasi-separated. -/
  quasiSeparated_target : QuasiSeparatedSpace target.left

namespace MorphismLimitSituation

attribute [instance] quasiCompact_base quasiSeparated_base quasiCompact_source
  quasiSeparated_source quasiCompact_target quasiSeparated_target

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismLimitSituation.{v, u} I)

/-- The transition morphism `S_i ⟶ S₀` from a stage later than the chosen index. -/
abbrev stageMap (i : I) (h : D.base ≤ i) : D.system.obj (op i) ⟶ D.system.obj (op D.base) :=
  D.system.map (Quiver.Hom.op (homOfLE h))

/-- The canonical projection `S ⟶ S₀` from the limit to the scheme at the chosen index. -/
abbrev limitProjection : D.limitCone.pt ⟶ D.system.obj (op D.base) :=
  D.limitCone.π.app (op D.base)

/-- The scheme `X`, the base change of `X₀` to the limit `S`. -/
noncomputable abbrev limitSource : Scheme.{u} :=
  ((Over.pullback D.limitProjection).obj D.source).left

/-- The scheme `Y`, the base change of `Y₀` to the limit `S`. -/
noncomputable abbrev limitTarget : Scheme.{u} :=
  ((Over.pullback D.limitProjection).obj D.target).left

/-- The morphism `f : X ⟶ Y`, the base change of `f₀` to the limit `S`. -/
noncomputable abbrev limitHom : D.limitSource ⟶ D.limitTarget :=
  ((Over.pullback D.limitProjection).map D.hom).left

/-- A stage `S_i` with `i ≥ 0` is quasi-compact, being affine over the quasi-compact `S₀`. -/
theorem compactSpace_stage (i : I) (h : D.base ≤ i) : CompactSpace (D.system.obj (op i)) :=
  haveI := D.transition_affine (homOfLE h).op
  QuasiCompact.compactSpace_of_compactSpace (D.stageMap i h)

/-- A stage `S_i` with `i ≥ 0` is quasi-separated, being affine over the quasi-separated `S₀`. -/
theorem quasiSeparatedSpace_stage (i : I) (h : D.base ≤ i) :
    QuasiSeparatedSpace (D.system.obj (op i)) :=
  haveI := D.transition_affine (homOfLE h).op
  quasiSeparatedSpace_of_quasiSeparated (D.stageMap i h)

/-- The restriction of Situation 081D to the cofinal stages `{i // 0 ≤ i}`: every stage there is
quasi-compact and quasi-separated, and the restricted cone is still a limit cone, so this is a
`AlgebraicGeometry.MorphismDescentSituation` with the same `S`, `S₀` and `f₀ : X₀ ⟶ Y₀`. -/
noncomputable def toMorphismDescentSituation :
    MorphismDescentSituation.{v, u} {i : I // D.base ≤ i} where
  system := (upSetInclusion D.base).op ⋙ D.system
  transition_affine _ := D.transition_affine _
  quasiCompact i := D.compactSpace_stage i.1 i.2
  quasiSeparated i := D.quasiSeparatedSpace_stage i.1 i.2
  limitCone := D.limitCone.whisker (upSetInclusion D.base).op
  isLimit :=
    haveI := final_upSetInclusion D.base
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm D.isLimit
  base := ⟨D.base, le_rfl⟩
  source := D.source
  target := D.target
  hom := D.hom
  quasiCompact_source := D.quasiCompact_source
  quasiSeparated_source := D.quasiSeparated_source
  quasiCompact_target := D.quasiCompact_target
  quasiSeparated_target := D.quasiSeparated_target

/-- The restriction to the stages `i ≥ 0` has the same limit `S`. -/
theorem toMorphismDescentSituation_limitScheme :
    D.toMorphismDescentSituation.limitScheme = D.limitCone.pt :=
  rfl

/-- The restriction to the stages `i ≥ 0` has the same base change `f : X ⟶ Y` of `f₀` to `S`. -/
theorem toMorphismDescentSituation_limitHom :
    D.toMorphismDescentSituation.limitHom = D.limitHom :=
  rfl

/-- The morphism `f_i : X_i ⟶ Y_i`, the base change of `f₀` along the transition morphism
`S_i ⟶ S₀`, for a stage `i ≥ 0`; it is the base change at the stage `⟨i, h⟩` of the restriction
`AlgebraicGeometry.MorphismLimitSituation.toMorphismDescentSituation`, whose transition morphism
to `S₀` is `D.stageMap i h`. -/
noncomputable abbrev stageHom (i : I) (h : D.base ≤ i) :
    D.toMorphismDescentSituation.stageSource ⟨i, h⟩ h ⟶
      D.toMorphismDescentSituation.stageTarget ⟨i, h⟩ h :=
  D.toMorphismDescentSituation.stageHom ⟨i, h⟩ h

/-- The transition morphism `S_i ⟶ S₀` of the restriction to the stages `i ≥ 0` is the transition
morphism `S_i ⟶ S₀` of the system, so `f_i` is the base change of `f₀` along it. -/
theorem toMorphismDescentSituation_stageMap (i : I) (h : D.base ≤ i) :
    D.toMorphismDescentSituation.stageMap ⟨i, h⟩ h = D.stageMap i h :=
  rfl

end MorphismLimitSituation

end AlgebraicGeometry
