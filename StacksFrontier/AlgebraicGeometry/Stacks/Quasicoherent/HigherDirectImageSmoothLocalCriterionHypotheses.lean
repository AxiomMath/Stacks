module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescentSectionUniverse

/-!
# Two hypotheses of the criterion of Stacks 076Z, discharged

The criterion of **Stacks 076Z**, formalized in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion`, asks
four hypotheses of a rule assigning to an algebraic stack a subcategory of its étale modules. Two
of them are proved here, for the two rules that module uses:

* the converse half of hypothesis (3) for the rule of local quasi-coherence, which is
  **Stacks 075Y**;
* hypothesis (2) for the rule of the flat base change property, which is part (1) of
  **Stacks 0764**.

Both are stated at the seating the criterion uses, with module sections in `u + 1`, which is the
universe the higher direct images of **Stacks 06WE** produce their modules in. They are what a
consumer of `AlgebraicGeometry.Stack.isSmoothLocal_locallyQuasicoherentRule` and of
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule`
passes for the hypotheses `hconv` and `hfbc` of those theorems, which carry them because that is
the shape the criterion's own statement has.

## Main results

* `AlgebraicGeometry.Stack.isSmoothLocalConverse_locallyQuasicoherentRule`: the converse half of
  hypothesis (3) of **Stacks 076Z** for local quasi-coherence, which is **Stacks 075Y**.
* `AlgebraicGeometry.Stack.isStableUnderSmoothPullback_flatBaseChangePropertyRule`:
  hypothesis (2) of **Stacks 076Z** for the flat base change property, which is part (1) of
  **Stacks 0764**.

## Implementation notes

Neither statement needs a universe generalization of an existing result. **Stacks 075Y** is
proved at an arbitrary section universe as
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective'`, because the
étale-locality of quasi-coherence it ends with is consumed in the form
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite` of
**Stacks 03DN**, where the section and scalar universes are independent, rather than in the form
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`, where they
are equal. Part (1) of **Stacks 0764** is proved as
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_modulePresheafPullback`, which takes the
structure functor of the source as a parameter, so it applies at the strict presentation of the
source of the 1-morphism with no transport. In both cases the sheaf condition the existing result
asks of the module is the one an object of `SheafOfModules` already carries.

Neither theorem is registered for its tag here. **Stacks 075Y** is registered on
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`, and this is a
reading of it at one seating; part (1) of **Stacks 0764** is one clause of a multi-part tag, and
its registration sits on `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_modulePullback`.

## References

* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The converse half of hypothesis (3) of Stacks 076Z for local quasi-coherence**, which is
**Stacks 075Y**: if the inverse image of a sheaf of `𝒪_𝒳`-modules along each member of a jointly
surjective family of smooth 1-morphisms is locally quasi-coherent, so is the sheaf.

This is `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective'`, the
section-universe-free form of **Stacks 075Y**, read at section universe `u + 1`, which is the
universe the higher direct images of **Stacks 06WE** produce their modules in. The sheaf
condition that tag asks of the module is the one carried by an object of `SheafOfModules`. -/
theorem isSmoothLocalConverse_locallyQuasicoherentRule :
    StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS) :=
  fun f hsmooth hjs F hall =>
    isLocallyQuasicoherent_of_isSmooth_jointlySurjective' B E h S hS f hsmooth hjs F.val
      F.isSheaf hall

/-- **Hypothesis (2) of Stacks 076Z for the flat base change property**, which is part (1) of
**Stacks 0764**: the inverse image of a module with the flat base change property along a
1-morphism of algebraic stacks has the flat base change property. No smoothness of the
1-morphism is needed.

This is `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_modulePresheafPullback` at the
strict presentation of the structure functor of the source; the sheaf condition that statement
asks of the module is the one an object of `SheafOfModules` comes with. -/
theorem isStableUnderSmoothPullback_flatBaseChangePropertyRule :
    StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS) :=
  fun {_ 𝒳} g _ F hF =>
    hasFlatBaseChangePropertyUnivLE_modulePresheafPullback.{u, u + 1, u, u + 1, u, u + 1}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      (isFibredOneMorphism_homFunctor_comp B S hS g.hom) F.val F.isSheaf hF

end AlgebraicGeometry.Stack

end
