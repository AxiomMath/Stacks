module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Restricting the source of a morphism descent system to a closed subspace

In the situation of Stacks 084W, carried by
`AlgebraicGeometry.Space.MorphismDescentSituation`, several arguments begin by replacing the
distinguished source `X₀` by a closed subspace of it — the scheme-theoretic support of a module,
or the reduced subspace on a closed set of points — and running the same descent for the
restricted morphism. Stacks 08K2 is the example this file was written for: its proof opens "we
may replace `X₀` by the scheme theoretic support of `F₀`".

That replacement is a new situation of Stacks 084W over the *same* inverse system of bases, with
the same distinguished stage, the same target and the same structure morphism of the target, and
with source `W`, structure morphism `W ⟶ X₀ ⟶ B₀` and morphism `W ⟶ X₀ ⟶ Y₀`. The two
finiteness conditions that Stacks 084W imposes on the source survive: a closed subspace of a
quasi-compact algebraic space is quasi-compact, and a closed immersion is quasi-separated, so a
closed subspace of a quasi-separated algebraic space is quasi-separated by part (2) of
Stacks 04ZH.

Each stage and the limit of the restricted situation then map to those of the original by the
base change of `W ⟶ X₀` along the projection, which is again a closed immersion, and the
restricted morphism to the stage is that base change followed by the original one.

## Main definitions

* `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSource`: the situation of Stacks 084W
  obtained by replacing the distinguished source by a closed subspace of it.
* `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSourceAtHom` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSourceLimitHom`: the comparison
  morphisms from the restricted source at a stage, and at the limit, to the original one.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSourceAtHom_isPullback` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSourceLimitHom_isPullback`: each
  comparison morphism is a base change of the inclusion of the closed subspace.
* `AlgebraicGeometry.Space.MorphismDescentSituation.isClosedImmersion_restrictSourceAtHom` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.isClosedImmersion_restrictSourceLimitHom`:
  each comparison morphism is therefore a closed immersion.
* `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSource_mapAt` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.restrictSource_mapLimit`: the restricted
  morphism at a stage, and at the limit, factors as the comparison morphism followed by the
  original one.
* `AlgebraicGeometry.Space.MorphismDescentSituation.isLocallyOfFiniteType_restrictSource_map₀`:
  the restricted morphism over the distinguished stage stays locally of finite type.

## Implementation notes

The targets are not merely isomorphic but equal: the restricted situation keeps `base`,
`initial`, `target₀` and `targetToBase`, so `targetAt`, `targetLimit` and the projections out of
them are the very same terms, and the three lemmas recording this hold by `rfl`. Only the
sources change, which is why the comparison morphisms are needed on the source side alone.

The closed subspace is given as a `CategoryTheory.Subfunctor` of the source together with the
hypotheses that it is an algebraic space and that its inclusion is a closed immersion, rather
than as a bundled `AlgebraicGeometry.Space.ClosedSubspaces`, so that the reduced closed subspace
on a closed set of points can be fed in directly from
`AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspace` and
`AlgebraicGeometry.Space.isClosedImmersion_ι_reducedClosedSubspace`.

## References

* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I) (W : Subfunctor D.source₀)
  (hW : IsAlgebraicSpace B S hS W.toFunctor) (hWci : IsClosedImmersion B S hS W.ι)

/-- **The situation of Stacks 084W obtained by restricting the distinguished source to a closed
subspace of it.** The inverse system of bases, the distinguished stage and the whole target side
are unchanged; the source becomes the closed subspace and the two morphisms out of it are
composed with its inclusion.

Quasi-compactness of the new source is
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion` and its quasi-separatedness
is part (2) of Stacks 04ZH applied to the inclusion, which is quasi-separated because it is a
closed immersion. -/
noncomputable def restrictSource : MorphismDescentSituation B S hS hZ I where
  base := D.base
  base_isAlgebraicSpace := D.base_isAlgebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  initial := D.initial
  source₀ := W.toFunctor
  target₀ := D.target₀
  sourceToBase := W.ι ≫ D.sourceToBase
  targetToBase := D.targetToBase
  map₀ := W.ι ≫ D.map₀
  map₀_over := by rw [Category.assoc, D.map₀_over]
  source₀_isAlgebraicSpace := hW
  target₀_isAlgebraicSpace := D.target₀_isAlgebraicSpace
  base₀_quasiCompact := D.base₀_quasiCompact
  base₀_quasiSeparated := D.base₀_quasiSeparated
  source₀_quasiCompact :=
    isQuasiCompactSpace_of_isClosedImmersion B S hS D.source₀_quasiCompact W.ι hWci
  source₀_quasiSeparated :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW D.source₀_quasiSeparated
      (isQuasiSeparated_of_isClosedImmersion B S hS hWci)
  target₀_quasiCompact := D.target₀_quasiCompact
  target₀_quasiSeparated := D.target₀_quasiSeparated

/-- The inverse system of bases of the restricted situation is that of the original one. -/
@[simp] theorem restrictSource_base : (D.restrictSource W hW hWci).base = D.base := rfl

/-- The distinguished stage of the restricted situation is that of the original one. -/
@[simp] theorem restrictSource_initial :
    (D.restrictSource W hW hWci).initial = D.initial := rfl

/-- The source of the restricted situation is the closed subspace `W`. -/
@[simp] theorem restrictSource_source₀ :
    (D.restrictSource W hW hWci).source₀ = W.toFunctor := rfl

/-- The morphism of the restricted situation is the original one composed with the inclusion of
`W`. -/
@[simp] theorem restrictSource_map₀ :
    (D.restrictSource W hW hWci).map₀ = W.ι ≫ D.map₀ := rfl

/-- The structure morphism of the target of the restricted situation is the original one. -/
@[simp] theorem restrictSource_targetToBase :
    (D.restrictSource W hW hWci).targetToBase = D.targetToBase := rfl

/-- The structure morphism of the source of the restricted situation is the original one composed
with the inclusion of `W`. -/
@[simp] theorem restrictSource_sourceToBase :
    (D.restrictSource W hW hWci).sourceToBase = W.ι ≫ D.sourceToBase := rfl

/-- The transition morphisms of the bases of the restricted situation are the original ones. -/
@[simp] theorem restrictSource_baseAtToInitial (i : I) (hi : D.initial ≤ i) :
    (D.restrictSource W hW hWci).baseAtToInitial i hi = D.baseAtToInitial i hi := rfl

/-- The target of the restricted situation at a stage is the target of the original one. -/
@[simp] theorem restrictSource_targetAt (i : I) (hi : D.initial ≤ i) :
    (D.restrictSource W hW hWci).targetAt i hi = D.targetAt i hi := rfl

/-- The target of the restricted situation at the limit is the target of the original one. -/
@[simp] theorem restrictSource_targetLimit :
    (D.restrictSource W hW hWci).targetLimit = D.targetLimit := rfl

/-- **The comparison morphism `W ×_{B₀} B_i ⟶ X₀ ×_{B₀} B_i` at a stage.** -/
noncomputable def restrictSourceAtHom (i : I) (hi : D.initial ≤ i) :
    (D.restrictSource W hW hWci).sourceAt i hi ⟶ D.sourceAt i hi :=
  pullback.lift (pullback.fst (D.baseAtToInitial i hi) (W.ι ≫ D.sourceToBase))
    (pullback.snd (D.baseAtToInitial i hi) (W.ι ≫ D.sourceToBase) ≫ W.ι)
    ((pullback.condition).trans (Category.assoc _ _ _).symm)

/-- **The comparison morphism `W ×_{B₀} B ⟶ X₀ ×_{B₀} B` at the limit.** -/
noncomputable def restrictSourceLimitHom :
    (D.restrictSource W hW hWci).sourceLimit ⟶ D.sourceLimit :=
  pullback.lift (pullback.fst (limit.π D.base (op D.initial)) (W.ι ≫ D.sourceToBase))
    (pullback.snd (limit.π D.base (op D.initial)) (W.ι ≫ D.sourceToBase) ≫ W.ι)
    ((pullback.condition).trans (Category.assoc _ _ _).symm)

/-- The comparison morphism at a stage commutes with the projections to the base at that stage. -/
@[simp] theorem restrictSourceAtHom_fst (i : I) (hi : D.initial ≤ i) :
    D.restrictSourceAtHom W hW hWci i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.sourceToBase =
      pullback.fst (D.baseAtToInitial i hi) (W.ι ≫ D.sourceToBase) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism at a stage followed by the projection to `X₀` is the projection to `W`
followed by the inclusion of `W`. -/
@[simp] theorem restrictSourceAtHom_snd (i : I) (hi : D.initial ≤ i) :
    D.restrictSourceAtHom W hW hWci i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.sourceToBase =
      pullback.snd (D.baseAtToInitial i hi) (W.ι ≫ D.sourceToBase) ≫ W.ι :=
  pullback.lift_snd _ _ _

/-- The comparison morphism at the limit commutes with the projections to the limit base. -/
@[simp] theorem restrictSourceLimitHom_fst :
    D.restrictSourceLimitHom W hW hWci ≫
        pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase =
      pullback.fst (limit.π D.base (op D.initial)) (W.ι ≫ D.sourceToBase) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism at the limit followed by the projection to `X₀` is the projection to
`W` followed by the inclusion of `W`. -/
@[simp] theorem restrictSourceLimitHom_snd :
    D.restrictSourceLimitHom W hW hWci ≫
        pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase =
      pullback.snd (limit.π D.base (op D.initial)) (W.ι ≫ D.sourceToBase) ≫ W.ι :=
  pullback.lift_snd _ _ _

/-- **The comparison morphism at a stage is a base change of the inclusion of the closed
subspace**, by the pasting of the cartesian square defining the restricted source at that stage
with the one defining the original source there. -/
theorem restrictSourceAtHom_isPullback (i : I) (hi : D.initial ≤ i) :
    IsPullback (D.restrictSourceAtHom W hW hWci i hi)
      (pullback.snd (D.baseAtToInitial i hi) (W.ι ≫ D.sourceToBase))
      (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) W.ι :=
  IsPullback.of_right
    (by rw [restrictSourceAtHom_fst]; exact IsPullback.of_hasPullback _ _)
    (restrictSourceAtHom_snd D W hW hWci i hi) (IsPullback.of_hasPullback _ _)

/-- **The comparison morphism at the limit is a base change of the inclusion of the closed
subspace.** -/
theorem restrictSourceLimitHom_isPullback :
    IsPullback (D.restrictSourceLimitHom W hW hWci)
      (pullback.snd (limit.π D.base (op D.initial)) (W.ι ≫ D.sourceToBase))
      (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) W.ι :=
  IsPullback.of_right
    (by rw [restrictSourceLimitHom_fst]; exact IsPullback.of_hasPullback _ _)
    (restrictSourceLimitHom_snd D W hW hWci) (IsPullback.of_hasPullback _ _)

/-- **Stacks 02YW for the comparison morphism at a stage.** It is a base change of a closed
immersion, hence a closed immersion. -/
theorem isClosedImmersion_restrictSourceAtHom (i : I) (hi : D.initial ≤ i) :
    IsClosedImmersion B S hS (D.restrictSourceAtHom W hW hWci i hi) :=
  (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (D.restrictSourceAtHom_isPullback W hW hWci i hi).flip hWci

/-- **Stacks 02YW for the comparison morphism at the limit.** -/
theorem isClosedImmersion_restrictSourceLimitHom :
    IsClosedImmersion B S hS (D.restrictSourceLimitHom W hW hWci) :=
  (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (D.restrictSourceLimitHom_isPullback W hW hWci).flip hWci

/-- **The restricted morphism at a stage is the comparison morphism followed by the original
one.** -/
theorem restrictSource_mapAt (i : I) (hi : D.initial ≤ i) :
    (D.restrictSource W hW hWci).mapAt i hi =
      D.restrictSourceAtHom W hW hWci i hi ≫ D.mapAt i hi := by
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, D.mapAt_fst, restrictSourceAtHom_fst]
    exact (D.restrictSource W hW hWci).mapAt_fst i hi
  · erw [Category.assoc, D.mapAt_snd, ← Category.assoc, restrictSourceAtHom_snd, Category.assoc]
    exact (D.restrictSource W hW hWci).mapAt_snd i hi

/-- **The restricted morphism at the limit is the comparison morphism followed by the original
one.** -/
theorem restrictSource_mapLimit :
    (D.restrictSource W hW hWci).mapLimit =
      D.restrictSourceLimitHom W hW hWci ≫ D.mapLimit := by
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, D.mapLimit_fst, restrictSourceLimitHom_fst]
    exact (D.restrictSource W hW hWci).mapLimit_fst
  · erw [Category.assoc, D.mapLimit_snd, ← Category.assoc, restrictSourceLimitHom_snd,
      Category.assoc]
    exact (D.restrictSource W hW hWci).mapLimit_snd

/-- **Stacks 03XG for the restricted morphism over the distinguished stage.** A closed immersion
is locally of finite type, so composing it with a morphism locally of finite type leaves a
morphism locally of finite type. -/
theorem isLocallyOfFiniteType_restrictSource_map₀
    (hlft : IsLocallyOfFiniteType B S hS D.map₀) :
    IsLocallyOfFiniteType B S hS (D.restrictSource W hW hWci).map₀ :=
  isLocallyOfFiniteType_comp B S hS hW D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
    W.ι D.map₀ (isLocallyOfFiniteType_of_isClosedImmersion B S hS W.ι hWci) hlft

end AlgebraicGeometry.Space.MorphismDescentSituation

end
