module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits

/-!
# A morphism over a stage of Situation 084R as a morphism descent system

Situation 084R, carried by `AlgebraicGeometry.Space.DescentSituation`, fixes a directed inverse
system of quasi-compact and quasi-separated algebraic spaces over `S` with affine transition
morphisms, a chosen limit and a chosen stage. Situation 084W, carried by
`AlgebraicGeometry.Space.MorphismDescentSystem`, fixes the same data together with a morphism of
quasi-compact quasi-separated algebraic spaces over the chosen stage.

This file reads a morphism over the chosen stage of a descent situation as a morphism descent
system, and as a situation of Stacks 084W in the sense of
`AlgebraicGeometry.Space.MorphismDescentSituation`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSystem`: the morphism descent system
  of a morphism between two algebraic spaces of finite presentation over the chosen stage of a
  descent situation, given a bound on the size of the index.
* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSituation`: the same morphism as a
  situation of Stacks 084W, with no bound on the index.

## Main results

* `DescentSituation.exists_isIso_mapAt_of_isIso_mapLimit`,
  `DescentSituation.exists_isIso_mapAt_of_isIso_mapLimit_of_isSiteSmall` and
  `DescentSituation.exists_isIso_mapAt_of_isIso_mapLimit_of_siteContainsBaseChangeLimits`:
  Stacks 084S in Situation 084R. A morphism locally of finite presentation between algebraic
  spaces of finite presentation over the chosen stage whose base change to the limit is an
  isomorphism has an isomorphism as its base change to some later stage.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The morphism descent system of a morphism over the chosen stage of a descent situation: given
two algebraic spaces of finite presentation over the stage of a descent situation, a morphism
between them over the stage, and the bound `#I < B.cutoff.ord.cof` on the index, the situation
of Stacks 084W attached to that morphism. -/
noncomputable def morphismDescentSystem (hI : #I < B.cutoff.ord.cof)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    MorphismDescentSystem B S hS hZ I where
  base := D.system
  indexSize := hI
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

variable (hI : #I < B.cutoff.ord.cof) (X₀ Y₀ : Over (D.system.obj (op D.base)))
  (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
  (hX₀fp : IsFinitePresentation B S hS X₀.hom) (hY₀fp : IsFinitePresentation B S hS Y₀.hom)
  (f₀ : X₀ ⟶ Y₀)

/-- The inverse system of the morphism descent system of a morphism over the chosen stage is the
inverse system of the descent situation. -/
@[simp]
theorem morphismDescentSystem_base :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).base = D.system := rfl

/-- The distinguished stage of the morphism descent system is the chosen stage of the descent
situation. -/
@[simp]
theorem morphismDescentSystem_initial :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).initial = D.base := rfl

/-- The source of the morphism descent system is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSystem_source₀ :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).source₀ = X₀.left := rfl

/-- The target of the morphism descent system is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSystem_target₀ :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).target₀ = Y₀.left := rfl

/-- The structure morphism of the source of the morphism descent system is the given one. -/
@[simp]
theorem morphismDescentSystem_sourceToBase :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).sourceToBase = X₀.hom := rfl

/-- The structure morphism of the target of the morphism descent system is the given one. -/
@[simp]
theorem morphismDescentSystem_targetToBase :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).targetToBase = Y₀.hom := rfl

/-- The morphism to be descended is the given morphism over the stage. -/
@[simp]
theorem morphismDescentSystem_map₀ :
    (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).map₀ = f₀.left := rfl

end Data

/-- **Stacks 084S in Situation 084R.** Let `f₀ : X₀ ⟶ Y₀` be a morphism between two algebraic
spaces of finite presentation over the chosen stage of a descent situation. If `f₀` is locally
of finite presentation and its base change to the limit is an isomorphism, then its base change
to some later stage is an isomorphism. -/
theorem exists_isIso_mapAt_of_isIso_mapLimit (hI : #I < B.cutoff.ord.cof)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀)
    (hfp : IsLocallyOfFinitePresentation B S hS f₀.left)
    (hiso : IsIso (D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapLimit) :
    ∃ (i : I) (hi : D.base ≤ i),
      IsIso ((D.morphismDescentSystem hI X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapAt i hi) :=
  MorphismDescentSystem.exists_isIso_mapAt _ hiso hfp

/-! ### Asking nothing of the index

The same construction as a situation of Stacks 084W in the sense of
`AlgebraicGeometry.Space.MorphismDescentSituation`, which needs no bound on the index, and
Stacks 084S for it under smallness of the system for the site. -/

/-- A morphism over the chosen stage of a descent situation as a situation of Stacks 084W: given
two algebraic spaces of finite presentation over the stage of a descent situation and a morphism
between them over the stage, the situation of Stacks 084W attached to that morphism, with no
bound on the size of the index. -/
noncomputable def morphismDescentSituation
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    MorphismDescentSituation B S hS hZ I where
  base := D.system
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

section SituationData

variable (X₀ Y₀ : Over (D.system.obj (op D.base)))
  (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
  (hX₀fp : IsFinitePresentation B S hS X₀.hom) (hY₀fp : IsFinitePresentation B S hS Y₀.hom)
  (f₀ : X₀ ⟶ Y₀)

/-- The inverse system of the situation of a morphism over the chosen stage is the
inverse system of the descent situation. -/
@[simp]
theorem morphismDescentSituation_base :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).base = D.system := rfl

/-- The distinguished stage of the situation is the chosen stage of the descent
situation. -/
@[simp]
theorem morphismDescentSituation_initial :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).initial = D.base := rfl

/-- The source of the situation is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSituation_source₀ :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).source₀ = X₀.left := rfl

/-- The target of the situation is the given algebraic space over the stage. -/
@[simp]
theorem morphismDescentSituation_target₀ :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).target₀ = Y₀.left := rfl

/-- The structure morphism of the source of the situation is the given one. -/
@[simp]
theorem morphismDescentSituation_sourceToBase :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).sourceToBase = X₀.hom := rfl

/-- The structure morphism of the target of the situation is the given one. -/
@[simp]
theorem morphismDescentSituation_targetToBase :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).targetToBase = Y₀.hom := rfl

/-- The morphism to be descended is the given morphism over the stage. -/
@[simp]
theorem morphismDescentSituation_map₀ :
    (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).map₀ = f₀.left := rfl

end SituationData

/-- **Stacks 084S in Situation 084R.** Let `f₀ : X₀ ⟶ Y₀` be a morphism between two algebraic
spaces of finite presentation over the chosen stage of a descent situation. If `f₀` is locally
of finite presentation and its base change to the limit is an isomorphism, then its base change
to some later stage is an isomorphism. Here the system is assumed small for the site in place of
a bound on the index. -/
theorem exists_isIso_mapAt_of_isIso_mapLimit_of_isSiteSmall (hb : IsSiteSmall B S hS D.system)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀)
    (hfp : IsLocallyOfFinitePresentation B S hS f₀.left)
    (hiso : IsIso (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapLimit) :
    ∃ (i : I) (hi : D.base ≤ i),
      IsIso ((D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapAt i hi) :=
  MorphismDescentSituation.exists_isIso_mapAt _ hb hiso hfp

/-- **Stacks 084S in Situation 084R, under the chapter's convention.** Let `f₀ : X₀ ⟶ Y₀` be a
morphism between two algebraic spaces of finite presentation over the chosen stage of a descent
situation. If `f₀` is locally of finite presentation and its base change to the limit is an
isomorphism, then its base change to some later stage is an isomorphism. Here the system is
assumed to satisfy the convention of Section 70.2 (tag 07SD) in place of a bound on the index. -/
theorem exists_isIso_mapAt_of_isIso_mapLimit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (X₀ Y₀ : Over (D.system.obj (op D.base)))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀)
    (hfp : IsLocallyOfFinitePresentation B S hS f₀.left)
    (hiso : IsIso (D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapLimit) :
    ∃ (i : I) (hi : D.base ≤ i),
      IsIso ((D.morphismDescentSituation X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapAt i hi) :=
  MorphismDescentSituation.exists_isIso_mapAt_of_siteContainsBaseChangeLimits _ hconv hiso hfp

end DescentSituation

end AlgebraicGeometry.Space

end
