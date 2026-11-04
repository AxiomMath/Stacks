module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateExtComparison
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsScalingSite

/-!
# The higher right derived functors of the adequator vanish

Let `U = Spec A` be an affine scheme and `(Sch/U)_τ` a big site with structure sheaf `𝒪`.
[Stacks, Tag 06ZU] asserts that for every object `𝓕` of `Adeq(𝒪)` we have `R^p A(𝓕) = 0` for
all `p > 0`, where `A : Mod((Sch/U)_τ, 𝒪) ⥤ Adeq(𝒪)` is the adequator of [Stacks, Tag 06ZS],
the right adjoint of the inclusion.

## Main results

* `Stacks.Adequate.isZero_rightDerived_affineAdequator` — **[Stacks, Tag 06ZU]**: for every
  adequate `𝓕` and every `p > 0`, `R^p A(𝓕) = 0` for the adequator
  `Stacks.Adequate.affineAdequator` of [Stacks, Tag 06ZS].

## Implementation notes

The abelian structure on `Adeq(𝒪)` is `Stacks.Adequate.abelian_adequate` ([Stacks, Tag 06VQ]
(1)), with its additive structure induced from the `𝒪`-modules, and the adequator is additive
as a right adjoint of the additive inclusion; both enter the statement through `letI`, exactly
as in `Stacks.Adequate.isZero_rightDerived_affineAdequator_of_site`. The right derived functors
are taken with respect to the injective resolutions supplied by
`Stacks.Adequate.BigSite.enoughInjectives_sheafOfModules`.

## References

* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06ZI](https://stacks.math.columbia.edu/tag/06ZI)
* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **[Stacks, Tag 06ZU].** Let `U = Spec A` be an affine scheme. For every object `𝓕` of
`Adeq(𝒪)` and every `p > 0`, `R^p A(𝓕) = 0`, where `A` is the adequator
`Stacks.Adequate.affineAdequator` of [Stacks, Tag 06ZS], the right adjoint of the inclusion
`Adeq(𝒪) → Mod((Sch/U)_τ, 𝒪)`.

The `letI` preamble is not a list of hypotheses: it is the abelian structure of `Adeq(𝒪)`
(Tag 06VQ (1)) and the additivity of the adequator, which is a right adjoint of an additive
functor. -/
@[stacks 06ZU]
public theorem isZero_rightDerived_affineAdequator
    (F : (adequate.{u, u} B).FullSubcategory) (p : ℕ) (hp : 0 < p) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : (affineAdequator B).Additive :=
      (affineAdequatorAdjunction B).right_adjoint_additive
    IsZero (((affineAdequator B).rightDerived p).obj F.obj) := by
  let : HasExt.{u + 1} (siteModuleFunctors B) := HasExt.standard _
  refine isZero_rightDerived_affineAdequator_of_site.{u + 1} B (fun X Y hX hY q hq ↦ ?_) F p hp
  obtain ⟨q, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by lia⟩
  exact subsingleton_ext_siteModuleFunctors_of_moduleExtension B X hX
    (fun M k ↦ subsingleton_ext_siteModuleFunctors_of_zExt B X _ (k + 1)
      (subsingleton_zExt_siteModuleFunctors_isLinearlyAdequate B X hX M ((k + 1 : ℕ) : ℤ)
        (by lia))) Y hY q

end Stacks.Adequate

end
