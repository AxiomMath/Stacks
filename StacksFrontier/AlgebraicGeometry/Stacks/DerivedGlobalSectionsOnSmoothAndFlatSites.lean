module

public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedSections
public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedSectionsOverSmoothAndFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfVanishingCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteConstantSheafLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedGlobalSectionsFromConstantSheafCounit
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections on the lisse-étale and on the flat-fppf site

Let `𝒳` be an algebraic stack, and let `g` be either of the comparison morphisms of topoi of
Stacks 08MZ,

`g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` or `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})`.

**Stacks 0H10 (1)(a)** and **(2)(a)** assert, for `K` in the unbounded derived category of
abelian sheaves on the big site,

`RΓ(𝒳_{étale}, K) = RΓ(𝒳_{lisse,étale}, g⁻¹K)`, resp.
`RΓ(𝒳_{fppf}, K) = RΓ(𝒳_{flat,fppf}, g⁻¹K)`.

Both are proved here, with no hypothesis, by the source's argument

`RΓ(𝒳, K) = RHom(ℤ, K) = RHom(Lg_! ℤ, K) = RHom(ℤ, g⁻¹K) = RΓ(𝒳', g⁻¹K)`:

it is
`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSectionsRestrictionIsoOfCounit`
at the two inclusions of sites, fed with Stacks 0H0Z in its counit form,
`isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf` in
`AlgebraicGeometry.Stack.FlatFppf` and
`isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf` in
`AlgebraicGeometry.Stack.LisseEtale`.

Parts (1)(b) and (2)(b) are in
`StacksFrontier/AlgebraicGeometry/Stacks/DerivedSectionsOverSmoothAndFlatObjects.lean`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedGlobalSectionsRestrictionIso`: **Stacks 0H10 (2)(a)**.
* `AlgebraicGeometry.Stack.LisseEtale.derivedGlobalSectionsRestrictionIso`:
  **Stacks 0H10 (1)(a)**.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

namespace FlatFppf

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- **Stacks 0H10, part (2)(a), for complexes, with no hypothesis.** Let `𝒳` be an algebraic
stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison morphism of topoi of
Stacks 08MZ, whose inverse image is restriction to the flat objects. For every `K` in the
unbounded derived category of abelian sheaves on `𝒳_{fppf}`,

`RΓ(𝒳_{flat,fppf}, g⁻¹K) = RΓ(𝒳_{fppf}, K)`,

naturally in `K`, where on each side `RΓ` is the total right derived functor of global sections
(`Sheaf.Γ`, the right adjoint of the constant sheaf functor).

The proof is the source's: global sections are corepresented by `ℤ`, and `Lg_! ℤ = ℤ`
(Stacks 0H0Z, `isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf`)
turns the derived adjunction `Lg_! ⊣ g⁻¹` of Stacks 07AS (3) into the comparison. -/
@[stacks 0H10 "part (2)(a) for complexes, at the flat-fppf site, with NO hypothesis: \
RΓ(𝒳_{flat,fppf}, g⁻¹K) = RΓ(𝒳_{fppf}, K), from Lg_! ℤ = ℤ (Tag 0H0Z, proved)"]
def derivedGlobalSectionsRestrictionIso :
    Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι ⋙
        derivedGlobalSectionsOnFlatSite B S hS 𝒳 ≅
      AlgebraicGeometry.Stack.derivedGlobalSections.{u, u + 1} B S hS 𝒳.val :=
  haveI := hasPointwiseRightKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳
    (abelianLowerShriekAcyclic B S hS 𝒳)
  haveI := isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (abelianLowerShriekAcyclic B S hS 𝒳) DerivedCategory.Qh
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
        (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
        (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  open Stacks.Cohomology.DerivedLowerShriek.BigSite
    (derivedAbelianGlobalSectionsRestrictionIsoOfCounit) in
  derivedAbelianGlobalSectionsRestrictionIsoOfCounit.{u + 1}
    (isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf B S hS 𝒳)

end FlatFppf

namespace LisseEtale

/-- Unbounded derived global sections on the lisse-étale site of an algebraic stack:
`RΓ(𝒳_{lisse,étale}, -)`, the total right derived functor of global sections. -/
abbrev derivedGlobalSections :
    DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory AbCat.{u, u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSections.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)

/-- Unbounded derived global sections on the étale site of an algebraic stack:
`RΓ(𝒳_{étale}, -)`, the total right derived functor of global sections. -/
abbrev derivedGlobalSectionsEtale :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AbCat.{u, u + 1}) ⥤ DerivedCategory AbCat.{u, u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianGlobalSections.{u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))

/-- **Stacks 0H10, part (1)(a), for complexes, with no hypothesis.** Let `𝒳` be an algebraic
stack and let `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` be the comparison morphism of topoi of
Stacks 08MZ, whose inverse image is restriction to the smooth objects. For every `K` in the
unbounded derived category of abelian sheaves on `𝒳_{étale}`,

`RΓ(𝒳_{lisse,étale}, g⁻¹K) = RΓ(𝒳_{étale}, K)`,

naturally in `K`, where on each side `RΓ` is the total right derived functor of global sections
(`Sheaf.Γ`, the right adjoint of the constant sheaf functor).

The proof is the source's: global sections are corepresented by `ℤ`, and `Lg_! ℤ = ℤ`
(Stacks 0H0Z, `LisseEtale.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf`)
turns the derived adjunction `Lg_! ⊣ g⁻¹` of Stacks 07AS (1) into the comparison. -/
@[stacks 0H10 "part (1)(a) for complexes, at the lisse-étale site, with NO hypothesis: \
RΓ(𝒳_{lisse,étale}, g⁻¹K) = RΓ(𝒳_{étale}, K), from Lg_! ℤ = ℤ (Tag 0H0Z, proved)"]
def derivedGlobalSectionsRestrictionIso :
    derivedAbelianRestriction.{u, w} B S hS 𝒳 ⋙ derivedGlobalSections B S hS 𝒳 ≅
      derivedGlobalSectionsEtale B S hS 𝒳 :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  haveI := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  open Stacks.Cohomology.DerivedLowerShriek.BigSite
    (derivedAbelianGlobalSectionsRestrictionIsoOfCounit) in
  derivedAbelianGlobalSectionsRestrictionIsoOfCounit.{u + 1}
    (isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf.{u, w} B S hS 𝒳)

end LisseEtale

end AlgebraicGeometry.Stack

end
