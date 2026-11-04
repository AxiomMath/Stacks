module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Supplement to `DescendingMorphisms`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `MorphismDescentSystemOfChartsBounded`
* `baseAtToInitial`
* `sourceAt`
* `targetAt`
* `mapAt`
* `sourceLimit`
* `targetLimit`
* `mapLimit`
* `sourceAt_isPullback`
* `targetAt_isPullback`
* `sourceLimit_isPullback`
* `targetLimit_isPullback`
* `mapAt_fst`
* `mapAt_snd`
* `mapLimit_fst`
* `mapLimit_snd`
* `sourceAt_isAlgebraicSpace`
* `targetAt_isAlgebraicSpace`
* `sourceLimit_isAlgebraicSpace`
* `targetLimit_isAlgebraicSpace`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition). -/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

/-- **Stacks 084W.** The standing situation for descending a property of a
morphism of algebraic spaces along a directed limit: a directed inverse system of algebraic
spaces over `S` with affine transition morphisms and algebraic limit, a distinguished stage of
the system, and a morphism of quasi-compact quasi-separated algebraic spaces over that
stage. -/
structure MorphismDescentSystemOfChartsBounded (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  base : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- The systems of affine charts of the system are size-bounded, so that their limits remain
  in the site. -/
  chartsBounded : Space.ChartsBounded B S hS base
  /-- Every member of the system is an algebraic space over `S`. -/
  base_isAlgebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (base.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a)
  /-- The limit `B` of the system is an algebraic space over `S`. -/
  limit_isAlgebraicSpace : IsAlgebraicSpace B S hS (limit base)
  /-- The distinguished stage `0 ∈ I`, over which the morphism to be descended is given. -/
  initial : I
  /-- The source `X₀` of the given morphism. -/
  source₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target `Y₀` of the given morphism. -/
  target₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The structure morphism `X₀ ⟶ B₀` exhibiting the source over the distinguished stage. -/
  sourceToBase : source₀ ⟶ base.obj (op initial)
  /-- The structure morphism `Y₀ ⟶ B₀` exhibiting the target over the distinguished stage. -/
  targetToBase : target₀ ⟶ base.obj (op initial)
  /-- The morphism `f₀ : X₀ ⟶ Y₀` to be descended. -/
  map₀ : source₀ ⟶ target₀
  /-- The given morphism is a morphism over the distinguished stage. -/
  map₀_over : map₀ ≫ targetToBase = sourceToBase
  /-- The source `X₀` is an algebraic space over `S`. -/
  source₀_isAlgebraicSpace : IsAlgebraicSpace B S hS source₀
  /-- The target `Y₀` is an algebraic space over `S`. -/
  target₀_isAlgebraicSpace : IsAlgebraicSpace B S hS target₀
  /-- The distinguished stage `B₀` is quasi-compact. -/
  base₀_quasiCompact : IsQuasiCompactSpace B S hS (base.obj (op initial))
  /-- The distinguished stage `B₀` is quasi-separated. -/
  base₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op initial))
  /-- The source `X₀` is quasi-compact. -/
  source₀_quasiCompact : IsQuasiCompactSpace B S hS source₀
  /-- The source `X₀` is quasi-separated. -/
  source₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ source₀
  /-- The target `Y₀` is quasi-compact. -/
  target₀_quasiCompact : IsQuasiCompactSpace B S hS target₀
  /-- The target `Y₀` is quasi-separated. -/
  target₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ target₀

namespace MorphismDescentSystemOfChartsBounded

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)

/-- The transition morphism `B_i ⟶ B₀` from a stage `i` at or beyond the distinguished stage
to the distinguished stage. -/
def baseAtToInitial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    D.base.obj (op i) ⟶ D.base.obj (op D.initial) :=
  D.base.map (homOfLE hi).op

/-- The source `X_i = B_i ×_{B₀} X₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def sourceAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.sourceToBase

/-- The target `Y_i = B_i ×_{B₀} Y₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def targetAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.targetToBase

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage `i ≥ 0`. -/
noncomputable def mapAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) : D.sourceAt i hi ⟶ D.targetAt i hi :=
  pullback.lift
    (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
    (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀)
    (by
      calc
        pullback.fst (D.baseAtToInitial i hi) D.sourceToBase ≫ D.baseAtToInitial i hi =
            pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.sourceToBase :=
          pullback.condition
        _ = pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫
            (D.map₀ ≫ D.targetToBase) := by rw [D.map₀_over]
        _ = (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀) ≫
            D.targetToBase := (Category.assoc _ _ _).symm)

/-- The source `X = B ×_{B₀} X₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def sourceLimit (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.sourceToBase

/-- The target `Y = B ×_{B₀} Y₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def targetLimit (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.targetToBase

/-- The base change `f : X ⟶ Y` of `f₀` to the limit `B`. -/
noncomputable def mapLimit (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    D.sourceLimit ⟶ D.targetLimit :=
  pullback.lift
    (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
    (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀)
    (by dsimp [sourceLimit, targetLimit]; simp [Category.assoc, D.map₀_over, pullback.condition])

/-- The square exhibiting `X_i` as the fibre product of `B_i` and `X₀` over `B₀` is
cartesian. -/
theorem sourceAt_isPullback (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase)
      (D.baseAtToInitial i hi) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y_i` as the fibre product of `B_i` and `Y₀` over `B₀` is
cartesian. -/
theorem targetAt_isPullback (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.targetToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase)
      (D.baseAtToInitial i hi) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `X` as the fibre product of `B` and `X₀` over `B₀` is cartesian. -/
theorem sourceLimit_isPullback (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase)
      (limit.π D.base (op D.initial)) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y` as the fibre product of `B` and `Y₀` over `B₀` is cartesian. -/
theorem targetLimit_isPullback (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.targetToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase)
      (limit.π D.base (op D.initial)) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The base change `f_i` of `f₀` to a stage is the identity on the base coordinate. -/
@[simp] theorem mapAt_fst (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (D.baseAtToInitial i hi) D.sourceToBase := pullback.lift_fst _ _ _

/-- The base change `f_i` of `f₀` to a stage is `f₀` on the other coordinate. -/
@[simp] theorem mapAt_snd (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀ := pullback.lift_snd _ _ _

/-- The base change `f` of `f₀` to the limit is the identity on the base coordinate. -/
@[simp] theorem mapLimit_fst (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    D.mapLimit ≫ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase :=
  pullback.lift_fst _ _ _

/-- The base change `f` of `f₀` to the limit is `f₀` on the other coordinate. -/
@[simp] theorem mapLimit_snd (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    D.mapLimit ≫ pullback.snd (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀ :=
  pullback.lift_snd _ _ _

/-- The source `X_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem sourceAt_isAlgebraicSpace (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.sourceAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem targetAt_isAlgebraicSpace (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.targetAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The source `X` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem sourceLimit_isAlgebraicSpace (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsAlgebraicSpace B S hS D.sourceLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem targetLimit_isAlgebraicSpace (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsAlgebraicSpace B S hS D.targetLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

end MorphismDescentSystemOfChartsBounded

end AlgebraicGeometry.Space

end
