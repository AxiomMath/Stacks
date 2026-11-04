module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflectionAcyclic
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequatorVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteModuleInjectives
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `D⁺(Adeq(𝒪)) ≌ D⁺_{Adeq}(𝒪)` over an affine base, with no hypothesis

Let `U = Spec A` be an affine scheme and `(Sch/U)_τ` a chosen big site over `U` with structure
sheaf `𝒪`. Adequacy cuts out the abelian subcategory `Adeq(𝒪)` of the `𝒪`-modules, with exact
inclusion ([Stacks, Tag 06VQ]), and the inclusion induces the canonical comparison functor
`D⁺(Adeq(𝒪)) ⥤ D⁺_{Adeq}(𝒪)` into the bounded below objects of `D(𝒪)` whose cohomology sheaves
are adequate. [Stacks, Tag 06ZV] asserts that this functor is an equivalence.

## Main results

* `Stacks.Adequate.enoughInjectives_adequate` — `Adeq(𝒪)` has enough injectives, over an affine
  base.
* `Stacks.Adequate.rightAcyclic_affineAdequator` — every adequate module is acyclic for the
  adequator.
* `Stacks.Adequate.isEquivalence_boundedBelowComparison_adequate` — **[Stacks, Tag 06ZV]**: the
  comparison functor `D⁺(Adeq(𝒪)) ⥤ D⁺_{Adeq}(𝒪)` is an equivalence.

## Implementation notes

The statement is at the value universe `u` of the site, which is where the adequator of
[Stacks, Tag 06ZS] is constructed. It holds for any choice of models of the two derived
categories, the instances `HasDerivedCategory` being arguments. The abelian structure of
`Adeq(𝒪)` is `Stacks.Adequate.abelian_adequate`, built from the closure of adequacy under kernels,
cokernels and finite products; the three closure theorems are local instances here.

## References

* [Stacks Project, Tag 06ZV](https://stacks.math.columbia.edu/tag/06ZV)
* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe w w' u

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

attribute [local instance] adequate_isClosedUnderKernels adequate_isClosedUnderCokernels
  adequate_isClosedUnderFiniteProducts

/-- The inclusion `Adeq(𝒪) ⥤ Mod(𝒪)` is left exact, [Stacks, Tag 06VQ] (2). -/
local instance : PreservesFiniteLimits (adequate.{u, u} B).ι := (exact_ι_adequate B).1

/-- The inclusion `Adeq(𝒪) ⥤ Mod(𝒪)` is right exact, [Stacks, Tag 06VQ] (2). -/
local instance : PreservesFiniteColimits (adequate.{u, u} B).ι := (exact_ι_adequate B).2

/-- The adequator is additive. -/
local instance : (affineAdequator B).Additive :=
  (affineAdequatorAdjunction B).right_adjoint_additive

/-- **`Adeq(𝒪)` has enough injectives** over an affine base. -/
public instance enoughInjectives_adequate :
    EnoughInjectives (adequate.{u, u} B).FullSubcategory :=
  EnoughInjectives.of_adjunction (affineAdequatorAdjunction B)

/-- **Every adequate module is acyclic for the adequator**: the complex `𝓕[0]` computes
`RA(𝓕)`. This is the vanishing `R^p A(𝓕) = 0` for `p > 0` of [Stacks, Tag 06ZU]. -/
public theorem rightAcyclic_affineAdequator
    [HasDerivedCategory.{w} (SheafOfModules.{u} B.structureSheaf)]
    [HasDerivedCategory.{w'} (adequate.{u, u} B).FullSubcategory]
    (F : (adequate.{u, u} B).FullSubcategory) :
    (affineAdequator B).rightAcyclic ((adequate.{u, u} B).ι.obj F) := by
  have : PreservesFiniteLimits (affineAdequator B) :=
    (affineAdequatorAdjunction B).rightAdjoint_preservesLimits.{0, 0}.preservesFiniteLimits
  exact (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).2
    (isZero_rightDerived_affineAdequator B F)

/-- **[Stacks, Tag 06ZV].** Let `U = Spec A` be an affine scheme. The canonical functor
`D⁺(Adeq(𝒪)) ⥤ D⁺_{Adeq}(𝒪)`, the inclusion `Adeq(𝒪) ⥤ Mod((Sch/U)_τ, 𝒪)` applied
degreewise to bounded below complexes, is an equivalence onto the bounded below objects of
`D(𝒪)` whose cohomology sheaves are adequate. -/
@[stacks 06ZV]
public theorem isEquivalence_boundedBelowComparison_adequate
    [HasDerivedCategory.{w} (SheafOfModules.{u} B.structureSheaf)]
    [HasDerivedCategory.{w'} (adequate.{u, u} B).FullSubcategory] :
    (DerivedCategoryB.boundedBelowComparison (adequate.{u, u} B)).IsEquivalence :=
  DerivedCategoryB.isEquivalence_boundedBelowComparison_of_rightAcyclic _
    (affineAdequatorAdjunction B) (rightAcyclic_affineAdequator B)

end Stacks.Adequate

end
