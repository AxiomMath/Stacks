module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.IsomorphismOfChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitsSupplement

/-!
# Supplement to `DescentSituationMorphismDescent`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `morphismDescentSystemOfChartsBounded`
* `morphismDescentSystem_base_of_chartsBounded`
* `morphismDescentSystem_initial_of_chartsBounded`
* `morphismDescentSystem_source₀_of_chartsBounded`
* `morphismDescentSystem_target₀_of_chartsBounded`
* `morphismDescentSystem_sourceToBase_of_chartsBounded`
* `morphismDescentSystem_targetToBase_of_chartsBounded`
* `morphismDescentSystem_map₀_of_chartsBounded`
* `exists_isIso_mapAt_of_isIso_mapLimit_of_chartsBounded`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition). -/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **A morphism over the chosen stage of a descent situation, as a morphism descent system.**
Given two algebraic spaces of finite presentation over the stage `X₀` of a descent situation and
a morphism between them over `X₀`, this is the situation of Stacks 084W attached to that
morphism, so that the descent results of
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded` — Stacks 084S among them — apply.

The quasi-compactness and quasi-separatedness that Stacks 084W asks of the source and of the
target are supplied by finite presentation over the stage, the stage itself being quasi-compact
and quasi-separated in a descent situation. -/
noncomputable def morphismDescentSystemOfChartsBounded (hI : ChartsBounded B S hS D.system)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    MorphismDescentSystemOfChartsBounded B S hS hZ I where
  base := D.system
  chartsBounded := hI
  base_isAlgebraicSpace := D.algebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace :=
    IsAlgebraicSpace.of_iso D.limitAlgebraicSpace
      (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system))
  initial := D.base
  source₀ := X₀.left
  target₀ := Y₀.left
  sourceToBase := X₀.hom
  targetToBase := Y₀.hom
  map₀ := f₀.left
  map₀_over := Over.w f₀
  source₀_isAlgebraicSpace := hX₀
  target₀_isAlgebraicSpace := hY₀
  base₀_quasiCompact := D.quasiCompact D.base
  base₀_quasiSeparated := D.quasiSeparated D.base
  source₀_quasiCompact :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS X₀.hom (D.algebraicSpace D.base)
      (D.quasiCompact D.base) hX₀fp
  source₀_quasiSeparated :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX₀ (D.quasiSeparated D.base)
      hX₀fp.2.2
  target₀_quasiCompact :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS Y₀.hom (D.algebraicSpace D.base)
      (D.quasiCompact D.base) hY₀fp
  target₀_quasiSeparated :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY₀ (D.quasiSeparated D.base)
      hY₀fp.2.2

section Data

variable (hI : ChartsBounded B S hS D.system) (X₀ Y₀ : Over (D.system.obj (op D.base)))
  (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
  (hX₀fp : IsFinitePresentation B S hS X₀.hom) (hY₀fp : IsFinitePresentation B S hS Y₀.hom)
  (f₀ : X₀ ⟶ Y₀)

/-- The inverse system of the morphism descent system of a morphism over the chosen stage is the
inverse system of the descent situation. -/
@[simp]
theorem morphismDescentSystem_base_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).base = D.system := rfl

/-- The distinguished stage of the morphism descent system is the chosen stage of the descent
situation. -/
@[simp]
theorem morphismDescentSystem_initial_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).initial = D.base := rfl

/-- The source of the morphism descent system is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSystem_source₀_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).source₀ =
      X₀.left := rfl

/-- The target of the morphism descent system is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSystem_target₀_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).target₀ =
      Y₀.left := rfl

/-- The structure morphism of the source of the morphism descent system is the given one. -/
@[simp]
theorem morphismDescentSystem_sourceToBase_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).sourceToBase =
      X₀.hom := rfl

/-- The structure morphism of the target of the morphism descent system is the given one. -/
@[simp]
theorem morphismDescentSystem_targetToBase_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).targetToBase =
      Y₀.hom := rfl

/-- The morphism to be descended is the given morphism over the stage. -/
@[simp]
theorem morphismDescentSystem_map₀_of_chartsBounded :
    (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).map₀ = f₀.left := rfl

end Data

/-- **Stacks 084S in Situation 084R.** Let `f₀ : X₀ ⟶ Y₀` be a morphism between two algebraic
spaces of finite presentation over the chosen stage of a descent situation. If `f₀` is locally
of finite presentation and its base change to the limit is an isomorphism, then its base change
to some later stage is an isomorphism. -/
theorem exists_isIso_mapAt_of_isIso_mapLimit_of_chartsBounded (hI : ChartsBounded B S hS D.system)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀)
    (hfp : IsLocallyOfFinitePresentation B S hS f₀.left)
    (hiso :
      IsIso (D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapLimit) :
    ∃ (i : I) (hi : D.base ≤ i),
      IsIso ((D.morphismDescentSystemOfChartsBounded hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapAt i hi) :=
  MorphismDescentSystemOfChartsBounded.exists_isIso_mapAt _ hiso hfp

end DescentSituation

end AlgebraicGeometry.Space

end
