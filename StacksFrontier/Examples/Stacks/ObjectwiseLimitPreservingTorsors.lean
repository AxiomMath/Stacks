module

public import StacksFrontier.Examples.Stacks.ObjectwiseLimitPreserving
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.CartesianFullSubcategory

/-!
# A stack limit preserving on objects but not limit preserving

Over a nonempty scheme `S` there is a stack in groupoids over the big fppf site of `S` whose
structure morphism is limit preserving on objects while the stack itself is not limit
preserving (Stacks 07Z1). The construction, the stack of torsors under a countable product of
copies of a nonzero injective abelian sheaf, is
`exists_stack_isLimitPreservingOnObjects_not_isLimitPreserving`, which uses that categories of
torsors under group objects over sheaves are stacks in groupoids. This file supplies that input
from Stacks 04UM.

## Main results

* `torsorsProjection_isStackInGroupoids`: the projection `𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of
  `AlgebraicGeometry.ClassifyingTorsors` is a stack in groupoids.
* `exists_isStackInGroupoids_isLimitPreservingOnObjects_not_isLimitPreserving`: **Stacks 07Z1**.

## Implementation notes

The category `𝒢/ℬ-Torsors` appears twice in the library: as
`AlgebraicGeometry.ClassifyingTorsors.Torsor`, used by the construction, and as
`AlgebraicGeometry.Space.SheafTorsors`, for which Stacks 04UM is proved
(`AlgebraicGeometry.Space.SheafTorsors.projection_isStackInGroupoids`). The two have the same
objects and morphisms field by field, so they are equivalent over the site with identity unit
and counit, and being a stack in groupoids transports along such an equivalence
(`CategoryTheory.BasedCategory.Equivalence.isStackInGroupoids`).

## References

* [Stacks Project, Tag 07Z1](https://stacks.math.columbia.edu/tag/07Z1)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.ObjectwiseLimitPreserving

universe u v w

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ℬ : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The category `𝒢/ℬ-Torsors` of `AlgebraicGeometry.ClassifyingTorsors` and the category of
Stacks 04UL in `AlgebraicGeometry.Space.SheafTorsors` have the same objects and morphisms, so
they are equivalent as categories over the big fppf site of `S`. -/
def sheafTorsorsEquivalence (𝒢 : Grp (Over ℬ)) :
    BasedCategory.Equivalence (BasedCategory.ofFunctor (Space.SheafTorsors.projection 𝒢))
      (BasedCategory.ofFunctor (ClassifyingTorsors.torsorsProjection 𝒢)) where
  functor :=
    { obj T := ClassifyingTorsors.Torsor.mk (Space.SheafTorsors.base T)
        (Space.SheafTorsors.sec T) (Space.SheafTorsors.total T) (Space.SheafTorsors.action T)
        (Space.SheafTorsors.isTorsor T)
      map φ := ClassifyingTorsors.TorsorHom.mk (Space.SheafTorsors.Hom.base φ)
        (Space.SheafTorsors.Hom.comp_sec φ) (Space.SheafTorsors.Hom.map φ)
        (Space.SheafTorsors.Hom.isPullback φ) (Space.SheafTorsors.Hom.smul_comp φ)
      w := rfl }
  inverse :=
    { obj T := Space.SheafTorsors.mk (ClassifyingTorsors.Torsor.U T)
        (ClassifyingTorsors.Torsor.b T) (ClassifyingTorsors.Torsor.F T)
        (ClassifyingTorsors.Torsor.action T) (ClassifyingTorsors.Torsor.isTorsor T)
      map φ := Space.SheafTorsors.Hom.mk (ClassifyingTorsors.TorsorHom.f φ)
        (ClassifyingTorsors.TorsorHom.comp_b φ) (ClassifyingTorsors.TorsorHom.g φ)
        (ClassifyingTorsors.TorsorHom.isPullback φ) (ClassifyingTorsors.TorsorHom.smul_comp φ)
      w := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- For a sheaf `ℬ` on the big fppf site of `S` and a group object `𝒢` over `ℬ` whose
underlying presheaf is a sheaf, the projection from `𝒢/ℬ-Torsors` to the site is a stack in
groupoids: Stacks 04UM, `AlgebraicGeometry.Space.SheafTorsors.projection_isStackInGroupoids`,
carried along `sheafTorsorsEquivalence`. -/
theorem torsorsProjection_isStackInGroupoids (𝒢 : Grp (Over ℬ))
    (hℬ : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) ℬ)
    (h𝒢 : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) 𝒢.X.left) :
    Functor.IsStackInGroupoids.{u + 1} (ClassifyingTorsors.torsorsProjection 𝒢)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  (sheafTorsorsEquivalence 𝒢).isStackInGroupoids
    (Space.SheafTorsors.projection_isStackInGroupoids 𝒢 hℬ h𝒢)

attribute [local instance] uliftCategory

/-- **Stacks 07Z1.** Let `S` be a nonempty scheme. There exists a stack in groupoids
`p : 𝒳 ⥤ (Sch/S)_fppf` such that `p` is limit preserving on objects (Stacks 06CU), but `𝒳`
is not limit preserving (Stacks 07XL). The stack is the stack of torsors under a countable
product of copies of a nonzero injective abelian sheaf, a stack in groupoids by Stacks 04UM. -/
@[stacks 07Z1]
theorem exists_isStackInGroupoids_isLimitPreservingOnObjects_not_isLimitPreserving
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [Nonempty S] :
    ∃ 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
        (AlgebraicGeometry.BigFppfOver B S hS),
      𝒳.val.p.IsStackInGroupoids.{u + 1}
          (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
        AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
          (AlgebraicGeometry.Stack.terminalCFG B S hS)
          (Bicategory.InducedBicategory.mkHom
            (AlgebraicGeometry.Stack.toTerminalCFG B S hS 𝒳)) ∧
        ¬ Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳 :=
  exists_stack_isLimitPreservingOnObjects_not_isLimitPreserving B S hS
    (fun 𝒢 hℬ h𝒢 => torsorsProjection_isStackInGroupoids 𝒢 hℬ h𝒢)

end AlgebraicGeometry.Stack.ObjectwiseLimitPreserving

end
