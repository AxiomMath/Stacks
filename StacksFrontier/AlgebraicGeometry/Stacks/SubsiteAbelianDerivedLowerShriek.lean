module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriekUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AS parts (1) and (3), each as one statement

Let `𝒳` be an algebraic stack and let `g` be the comparison morphism of topoi of **Stacks 0788**,
from the lisse-étale site to the étale site, or from the flat-fppf site to the fppf site.
**Stacks 07AS** parts (1) and (3) assert that the lower-shriek functor `g_!` on abelian sheaves
has an unbounded left derived functor `Lg_!`, that `Lg_!` is left adjoint to `g⁻¹`, and that
`g⁻¹ ∘ Lg_! = id`.

The three assertions are proved, for every algebraic stack and with nothing assumed, in
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleDerivedLowerShriek.lean` (part (1)) and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriekUnconditional.lean` (part (3)),
one declaration per assertion.  This file states each part as a single proposition, the
conjunction of its three assertions, so that each numbered part is carried by one declaration.
The module-level parts (2) and (4) are stated the same way in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteModuleDerivedLowerShriek.lean`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriek_derived`: **Stacks 07AS (1)**.
* `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek_derived`: **Stacks 07AS (3)**.

## References

* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Stack.LisseEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AS (1)**, all three assertions, for every algebraic stack and with NO hypothesis.
For `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` the comparison morphism of topoi of
**Stacks 0788** (1):

* the functor `g_! : Ab(𝒳_{lisse,étale}) ⥤ Ab(𝒳_{étale})` has a left derived functor
  `Lg_! : D(𝒳_{lisse,étale}) ⟶ D(𝒳_{étale})` — degreewise `g_!` followed by the localization of
  the homotopy category of `Ab(𝒳_{étale})` has a pointwise left derived functor along the
  localization of the homotopy category of `Ab(𝒳_{lisse,étale})`, and `Lg_!` is that total left
  derived functor;
* `Lg_!` is left adjoint to `g⁻¹`, by an adjunction whose unit is an isomorphism;
* `g⁻¹ ∘ Lg_! = id`. -/
@[stacks 07AS "part (1), the whole of it: existence of the unbounded left derived functor `Lg_!` \
of `g_!` on abelian sheaves for the lisse-étale site, its adjunction `Lg_! ⊣ g⁻¹` (with \
invertible unit), and `g⁻¹ ∘ Lg_! = id`, for every algebraic stack and with NO hypothesis. The \
acyclicity statement of Tag 07AC is the theorem \
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic` and the invertibility of the \
ordinary unit is Tag 077I"]
theorem abelianLowerShriek_derived :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_additive.{u, w} B S hS 𝒳
    ((abelianLowerShriek.{u, w} B S hS 𝒳
        (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) ∧
    (∃ adj : derivedAbelianLowerShriek.{u, w} B S hS 𝒳 ⊣
        derivedAbelianRestriction.{u, w} B S hS 𝒳, IsIso adj.unit) ∧
    Nonempty (derivedAbelianLowerShriek.{u, w} B S hS 𝒳 ⋙
        derivedAbelianRestriction.{u, w} B S hS 𝒳 ≅
      𝟭 (DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}))) :=
  ⟨abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳,
    ⟨derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳,
      isIso_derivedAbelianLowerShriekAdjunction_unit.{u, w} B S hS 𝒳⟩,
    ⟨derivedAbelianLowerShriekRestrictionIso.{u, w} B S hS 𝒳⟩⟩

end AlgebraicGeometry.Stack.LisseEtale

namespace AlgebraicGeometry.Stack.FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AS (3)**, all three assertions, for every algebraic stack and with NO hypothesis.
For `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the comparison morphism of topoi of
**Stacks 0788** (2):

* the functor `g_! : Ab(𝒳_{flat,fppf}) ⥤ Ab(𝒳_{fppf})` has a left derived functor
  `Lg_! : D(𝒳_{flat,fppf}) ⟶ D(𝒳_{fppf})` — degreewise `g_!` followed by the localization of the
  homotopy category of `Ab(𝒳_{fppf})` has a pointwise left derived functor along the localization
  of the homotopy category of `Ab(𝒳_{flat,fppf})`, and `Lg_!` is that total left derived functor;
* `Lg_!` is left adjoint to `g⁻¹`, by an adjunction whose unit is an isomorphism;
* `g⁻¹ ∘ Lg_! = id`. -/
@[stacks 07AS "part (3), the whole of it: existence of the unbounded left derived functor `Lg_!` \
of `g_!` on abelian sheaves for the flat-fppf site, its adjunction `Lg_! ⊣ g⁻¹` (with \
invertible unit), and `g⁻¹ ∘ Lg_! = id`, for every algebraic stack and with NO hypothesis. The \
acyclicity statement of Tag 07AC is the theorem \
`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic` and the invertibility of the \
ordinary unit is Tag 077I"]
theorem abelianLowerShriek_derived :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    haveI := abelianLowerShriek_additive B S hS 𝒳
    ((abelianLowerShriek B S hS 𝒳 flatClosure).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) ∧
    (∃ adj : derivedAbelianLowerShriekFunctor B S hS 𝒳 ⊣ derivedAbelianRestriction B S hS 𝒳,
      IsIso adj.unit) ∧
    Nonempty (derivedAbelianLowerShriekFunctor B S hS 𝒳 ⋙ derivedAbelianRestriction B S hS 𝒳 ≅
      𝟭 (DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}))) :=
  ⟨abelianLowerShriek_hasPointwiseLeftDerivedFunctor B S hS 𝒳,
    ⟨derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳,
      isIso_derivedAbelianLowerShriekAdjunction_unit B S hS 𝒳 (abelianLowerShriekAcyclic B S hS 𝒳)⟩,
    ⟨derivedAbelianLowerShriekFunctorRestrictionIso B S hS 𝒳⟩⟩

end AlgebraicGeometry.Stack.FlatFppf

end
