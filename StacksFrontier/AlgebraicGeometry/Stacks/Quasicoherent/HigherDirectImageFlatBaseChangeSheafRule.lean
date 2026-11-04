module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterionHypotheses

/-!
# The rule `LQCoh^fbc` of Stacks 0765, with the flat base change property read on sheaves

**Stacks 0765** applies the criterion of **Stacks 076Z** to the rule assigning to an algebraic
stack `𝒳` the full subcategory `LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒳_étale, 𝒪_𝒳)` of the locally
quasi-coherent modules (**Stacks 06WJ**) with the flat base change property (**Stacks 0762**).
This file defines that rule, in the shape `AlgebraicGeometry.Stack.StackEtaleModuleRule` the
criterion is stated for, and verifies hypotheses (2) and (3) of the criterion for it.

The flat base change property is read in the source's ambient category: the comparison maps of
**Stacks 0761** are taken with `a_{small}^*` the inverse image of *sheaves* of modules, which is
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`. A rule is a predicate on presheaves
of modules; a member of this one is a sheaf, local quasi-coherence containing the étale sheaf
condition, and the flat base change property is asked of it as a sheaf.

## Main definitions

* `AlgebraicGeometry.Stack.flatBaseChangePropertySheafRule`: the rule of the flat base change
  property, read on sheaves.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafRule`: the rule `LQCoh^fbc`.

## Main results

* `Stack.isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule`: hypothesis
  (2) of **Stacks 076Z** for `LQCoh^fbc`, from **Stacks 06WL** and part (1) of **Stacks 0764**.
* `AlgebraicGeometry.Stack.isSmoothLocal_locallyQuasicoherentFlatBaseChangeSheafRule`:
  hypothesis (3) of **Stacks 076Z** for `LQCoh^fbc`, from hypothesis (2), **Stacks 075Y** and
  part (3) of **Stacks 0764**.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rule of the flat base change property, read on sheaves.** The rule in the sense of
**Stacks 076Z** whose members are the étale sheaves of modules with the flat base change property
of **Stacks 0762**, the comparison maps taken with the inverse image of sheaves of modules. A
presheaf of modules is a member when it is an étale sheaf and, as a sheaf, has the property; the
sheaf condition is a proposition, so the quantification over its proofs asks nothing more. -/
noncomputable abbrev flatBaseChangePropertySheafRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf ∧
      ∀ hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf,
        HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS p hp ⟨F, hF⟩

/-- **The rule `LQCoh^fbc` of Stacks 0765.** The rule in the sense of **Stacks 076Z** assigning
to a category fibred in groupoids the étale modules which are locally quasi-coherent
(**Stacks 06WJ**) and have the flat base change property (**Stacks 0762**) in the source's
reading on sheaves, at section universe `u + 1`, where the higher direct images live. -/
noncomputable abbrev locallyQuasicoherentFlatBaseChangeSheafRule : StackEtaleModuleRule B S hS :=
  fun {𝒳 : Type (u + 1)} [Category.{u} 𝒳] p hp F =>
    locallyQuasicoherentRule B E h S hS p hp F ∧ flatBaseChangePropertySheafRule B E h S hS p hp F

/-- The inverse image of an étale sheaf of modules along the functor of a 1-morphism of algebraic
stacks, as a sheaf of modules on the source's étale site. -/
private noncomputable abbrev pullbackSheaf {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒳)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
  (modulePullback B S hS (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
    𝒳.val.val.p (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
    𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom) rfl (etaleTopology B)
    (etaleTopology_le_topology B)).obj F

/-- **Hypothesis (2) of Stacks 076Z for the flat base change property on sheaves**, which is
part (1) of **Stacks 0764**: the inverse image of an étale sheaf of modules with the flat base
change property along a 1-morphism of algebraic stacks has the property. No smoothness is used.
-/
theorem isStableUnderSmoothPullback_flatBaseChangePropertySheafRule :
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertySheafRule B E h S hS) := by
  intro _ 𝒳 g _ F hF
  refine ⟨(pullbackSheaf B S hS g F).isSheaf, fun _ => ?_⟩
  exact hasFlatBaseChangePropertySheaf_modulePullback B E h S hS
    (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
    (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor g.hom) rfl F (hF.2 F.isSheaf)

/-- **Hypothesis (2) of Stacks 076Z for `LQCoh^fbc`.** The inverse image along a smooth
1-morphism of algebraic stacks of a locally quasi-coherent module with the flat base change
property is again one: local quasi-coherence by **Stacks 06WL**
(`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`), and the flat
base change property by part (1) of **Stacks 0764**
(`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_flatBaseChangePropertySheafRule`). -/
theorem isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule :
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) :=
  fun g hg F hF =>
    ⟨isStableUnderSmoothPullback_locallyQuasicoherentRule B E h S hS g hg F hF.1,
      isStableUnderSmoothPullback_flatBaseChangePropertySheafRule B E h S hS g hg F hF.2⟩

/-- **The converse half of hypothesis (3) of Stacks 076Z for the flat base change property on
sheaves**, which is part (3) of **Stacks 0764**: if the inverse images of an étale sheaf of
modules along a jointly surjective family of smooth 1-morphisms of algebraic stacks have the flat
base change property, so does the sheaf. -/
theorem isSmoothLocalConverse_flatBaseChangePropertySheafRule :
    StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (flatBaseChangePropertySheafRule B E h S hS) :=
  fun f hsmooth hjs F hall => ⟨F.isSheaf, fun _ =>
    hasFlatBaseChangePropertySheaf_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F
      fun j => (hall j).2 (pullbackSheaf B S hS (f j) F).isSheaf⟩

/-- **Hypothesis (3) of Stacks 076Z for `LQCoh^fbc`.** Membership in the rule is local for a
jointly surjective family of smooth 1-morphisms of algebraic stacks. The forward half is
hypothesis (2),
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule`;
the converse half is **Stacks 075Y** for local quasi-coherence
(`AlgebraicGeometry.Stack.isSmoothLocalConverse_locallyQuasicoherentRule`) together with part (3)
of **Stacks 0764** for the flat base change property
(`AlgebraicGeometry.Stack.isSmoothLocalConverse_flatBaseChangePropertySheafRule`). -/
theorem isSmoothLocal_locallyQuasicoherentFlatBaseChangeSheafRule :
    StackEtaleModuleRule.IsSmoothLocal.{u, t, s} B S hS
      (locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS) :=
  fun f hsmooth hjs F =>
    ⟨fun hF j => isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeSheafRule
        B E h S hS (f j) (hsmooth j) F hF,
      fun hall => ⟨isSmoothLocalConverse_locallyQuasicoherentRule B E h S hS f hsmooth hjs F
          fun j => (hall j).1,
        isSmoothLocalConverse_flatBaseChangePropertySheafRule B E h S hS f hsmooth hjs F
          fun j => (hall j).2⟩⟩

end AlgebraicGeometry.Stack

end
