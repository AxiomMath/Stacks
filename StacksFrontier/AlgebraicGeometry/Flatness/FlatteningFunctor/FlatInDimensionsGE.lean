module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.NonFlatLocusFibreDimension

/-!
# Flatness over the base in dimensions at least `n`

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `n` be a natural number. We say that `F` is flat over `S`
in dimensions `≥ n` when the closed subset of the fibre `X_s` of points at which `F` is not
flat over `S` has dimension less than `n`, for every point `s` of `S`.

This is the first of the two equivalent conditions of the dimension criterion
`AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff` (Stacks 0CWF): it is a
condition on the fibres only, it mentions nothing beyond the dimension of a subspace of a
fibre, and it is the form in which base-change stability was established. The second
condition, the bound `trdeg_{κ(f x)} κ(x) < n` at every point `x` where `F` is not flat over
`S`, is recorded here as a characterization.

## Main definitions

* `AlgebraicGeometry.IsFlatOverInDimensionsGE`: **Stacks 0CWG**, flatness over the base in
  dimensions at least `n`.

## Main results

* `AlgebraicGeometry.isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt`: the pointwise
  transcendence degree characterization, i.e. the second condition of Stacks 0CWF.
* `AlgebraicGeometry.IsFlatOverInDimensionsGE.of_isPullback`: the condition is stable under
  arbitrary base change.

## Implementation notes

There is no index shift against the dimension criterion: the source phrases its first
condition as `dim(Z) < n` for the closed subset `Z` of the fibre where `F` is not flat, so
flatness in dimensions `≥ n` holds exactly when the failure of flatness is confined to
dimensions below `n`, and the strict inequality `< (n : WithBot ℕ∞)` of the definition is the
one of `AlgebraicGeometry.topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff` verbatim. The
source's `n ≥ 0` is the range of `ℕ`, so it needs no hypothesis.

The non-flat locus in a fibre is the complement of the flat locus of
`AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType` (Stacks 05M9); it is a
set of points of the scheme-theoretic fibre `AlgebraicGeometry.Scheme.Hom.fiber`, and its
dimension is the dimension of that set as a subspace, which is how the dimension criterion
phrases its first condition.

The hypotheses of the source definition — `f` locally of finite type, `F` quasi-coherent of
finite type — are carried as instance arguments even though the defining condition does not
need them, so that the notion is only available in the situation where the two conditions of
Stacks 0CWF are equivalent.

Base-change stability needs the hypotheses of the definition for the base-changed family as
well. They follow from those for `f` and `F`, but not by instance search, since recognizing
the base change requires the pullback square; they are therefore instance arguments of
`AlgebraicGeometry.IsFlatOverInDimensionsGE.of_isPullback`, to be supplied by the caller from
`CategoryTheory.MorphismProperty.of_isPullback`,
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` and
`AlgebraicGeometry.SheafOfModules.pullback_isFiniteType`.

## References

* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CWG.** Let `f : X ⟶ S` be locally of finite type and let `F` be a
quasi-coherent `𝒪_X`-module of finite type. Then `F` is *flat over `S` in dimensions `≥ n`* if
for every point `s` of `S` the closed subset of the fibre `X_s` of points at which `F` is not
flat over `S` has dimension less than `n`.

This is the first of the two equivalent conditions of Stacks 0CWF; the second one is
`AlgebraicGeometry.isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt`. -/
@[stacks 0CWG]
def IsFlatOverInDimensionsGE {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) : Prop :=
  ∀ s : S, topologicalKrullDim
    ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} < (n : WithBot ℕ∞)

/-- Flatness over the base in dimensions `≥ n` unfolds to the fibrewise dimension bound on the
non-flat locus. -/
theorem isFlatOverInDimensionsGE_iff_forall_topologicalKrullDim_lt {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (n : ℕ) :
    IsFlatOverInDimensionsGE f F n ↔
      ∀ s : S, topologicalKrullDim
        ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} <
          (n : WithBot ℕ∞) :=
  Iff.rfl

/-- **Stacks Project, Tag 0CWF.** `F` is flat over `S` in dimensions `≥ n` if and only if
`trdeg_{κ(f x)} κ(x) < n` at every point `x` of `X` at which `F` is not flat over `S`: the
second of the two equivalent conditions defining Stacks 0CWG. -/
theorem isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ) :
    IsFlatOverInDimensionsGE f F n ↔
      ∀ x : X, ¬ IsFlatOverAt f.toLRSHom.toShHom F x →
        letI : Algebra (S.residueField (f x)) (X.residueField x) :=
          (f.residueFieldMap x).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) < (n : WithBot ℕ∞) :=
  topologicalKrullDim_not_isFlatOverAt_fiber_lt_iff f F n

/-- Flatness over the base in dimensions `≥ n` is stable under arbitrary base change. -/
theorem IsFlatOverInDimensionsGE.of_isPullback {X S S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    [LocallyOfFiniteType f'] [((Scheme.Modules.pullback g').obj F).IsQuasicoherent]
    [((Scheme.Modules.pullback g').obj F).IsFiniteType]
    (hF : IsFlatOverInDimensionsGE f F n) :
    IsFlatOverInDimensionsGE f' ((Scheme.Modules.pullback g').obj F) n := fun s' ↦
  topologicalKrullDim_not_isFlatOverAt_fiber_lt_of_isPullback hsq F n hF s'

end AlgebraicGeometry

end
