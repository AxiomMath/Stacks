module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekAcyclic
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibreStandardResolution
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartRingedTopoi

/-!
# The derived lower shriek of modules on the site of polynomial charts

Let `X` be a scheme over a ring `Λ`, and let `π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)` be the morphism of
topoi of the fibred category of polynomial charts of `X`, the situation of Stacks 08P8 recorded
as `AlgebraicGeometry.PolynomialChart.fibredCategorySituation`. The chart category has its
objects in `Type (u + 1)` and its morphisms in `Type u`, so modules on it are taken in the
coefficient universe `u + 1`, where `𝒪_X` is presented by `liftedStructureSheaf`.

This file checks that the module lower shriek of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ModuleLowerShriekAcyclic.lean` is
available there with nothing left to supply: every instance it asks for — sheafification on both
sites, the left adjoints of restriction, the smallness of the chart category in `u + 1` and
Grothendieck abelianness of both categories of modules — is found at these universes.

## Main results

* `Lπ_! : D(π⁻¹𝒪_X) ⥤ D(𝒪_X)` exists on the chart site (Stacks 07AC): instance search finds the
  pointwise left derived functor of degreewise lower shriek followed by localization there.
* `AlgebraicGeometry.PolynomialChart.nonempty_chartDerivedModuleLowerShriekAdjunction`:
  `Lπ_!` is left adjoint to `π^*` there (Stacks 08PC (3)).

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.DerivedLowerShriek

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u + 1`;
the structures used here are those of the fibred category situation. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

attribute [local instance] HasDerivedCategory.standard

/-- **`Lπ_! ⊣ π^*` on the site of polynomial charts** (Stacks 08PC (3)): the derived lower
shriek of `π⁻¹𝒪_X`-modules along `C_{X/Λ} ⥤ X_Zar` is left adjoint to derived restriction,
with the modules in the coefficient universe `u + 1`. -/
theorem nonempty_chartDerivedModuleLowerShriekAdjunction :
    Nonempty ((fibredCategorySituation Λ X structureMap).derivedModuleLowerShriek
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{u, u} X)) ⊣
      derivedRestriction (fibredCategorySituation Λ X structureMap).topology
        (fibredCategorySituation Λ X structureMap).base.J
        (fibredCategorySituation Λ X structureMap).p
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{u, u} X))) :=
  ⟨(fibredCategorySituation Λ X structureMap).derivedModuleLowerShriekAdjunction _⟩

end AlgebraicGeometry.PolynomialChart

end
