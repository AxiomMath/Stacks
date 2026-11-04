module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedSections
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianAcyclicityFromContinuity
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an object of the lisse-étale and of the flat-fppf site

Let `𝒳` be an algebraic stack, and let `g` be either of the comparison morphisms of topoi of
Stacks 08MZ,

`g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` or `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})`,

whose inverse image is restriction to the smooth, resp. flat, objects. **Stacks 0H10 (1)(b)**
and **(2)(b)** assert, for `K` in the unbounded derived category of abelian sheaves on the big
site and `x` an object of the small one,

`RΓ(x, K) = RΓ(𝒳_{lisse,étale}/x, g⁻¹K)`, resp. `RΓ(x, K) = RΓ(𝒳_{flat,fppf}/x, g⁻¹K)`.

Both are proved here with no hypothesis.

## The half of Stacks 0794 at a generator

`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedSections.lean` proves part (2)(b) assuming
`AlgebraicGeometry.Stack.FlatFppf.DerivedLowerShriekComputesFlatGenerator`: that the counit
`Lg_! ∘ Q ⟶ Q ∘ g_!` of the left derived functor is invertible at the single complex on
`j_{x!} ℤ_x`. That is the half of Stacks 0794 saying the left derived functor is computed on the
complexes of its resolving class, and it is a theorem here:
`AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekComputesFlatGenerator`, and its lisse-étale
sibling `AlgebraicGeometry.Stack.LisseEtale.derivedLowerShriekComputesSmoothGenerator`. Both are
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_of_acyclic`
— a bounded above complex of direct sums of the `j_{U!} ℤ_U` is `P`-cellular for the class `P`
with which `Lg_!` is built, so the counit is invertible on it — fed with the acyclicity
statement of Stacks 07AC for the inclusion, which is a theorem for both sites
(`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`,
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`), and with
`Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_single`.

The same statement for an arbitrary bounded above complex of such direct sums is recorded as
`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedAbelianLowerShriekComparison_app` and
`AlgebraicGeometry.Stack.LisseEtale.isIso_derivedAbelianLowerShriekComparison_app`.

## Cohomology over an object

As in `FlatFppfDerivedSections.lean`, cohomology over `x` is the right derived functor of
sections over `x` on the site itself, which is the convention Stacks 0DD8 is stated with here;
it agrees with derived global sections on the slice site by the localization comparison of
Stacks 03F3.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekComputesFlatGenerator`: the half of
  **Stacks 0794** at the generator `j_{x!} ℤ_x`, discharging `hgen`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedLowerShriekComputesSmoothGenerator`: the same for
  the lisse-étale site.
* `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIsoOfFlatObject`:
  **Stacks 0H10 (2)(b)**, unconditionally.
* `AlgebraicGeometry.Stack.LisseEtale.derivedSectionsRestrictionIso`:
  **Stacks 0H10 (1)(b)**, unconditionally.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **`Lg_!` on the flat-fppf site is computed degreewise on a bounded above complex of direct
sums of the `j_{U!} ℤ_U`** (the half of Stacks 0794 saying that the left derived functor is
computed on its resolving class), with no hypothesis. -/
theorem isIso_derivedAbelianLowerShriekComparison_app
    (L : CochainComplex (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) ℤ)
    [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnitsAb.{u + 1} (inclusionTopology B S hS 𝒳) (L.X n)) :
    haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳
      (abelianLowerShriekAcyclic B S hS 𝒳)
    IsIso ((derivedAbelianLowerShriekComparison.{u + 1} (inclusionTopology B S hS 𝒳)
      (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  have := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳
    (abelianLowerShriekAcyclic B S hS 𝒳)
  isIso_derivedAbelianLowerShriekComparison_app_of_acyclic.{u + 1, u, u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (abelianLowerShriekAcyclic B S hS 𝒳) L hL

/-- **The half of Stacks 0794 at a generator of the flat-fppf site, proved.** The counit of
`Lg_!` is invertible at the single complex on `j_{x!} ℤ_x`, for every object `x` of the
flat-fppf site of every algebraic stack: this is the hypothesis `hgen` of
`AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso`, discharged. -/
theorem derivedLowerShriekComputesFlatGenerator
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    DerivedLowerShriekComputesFlatGenerator B S hS 𝒳 x :=
  isIso_derivedAbelianLowerShriekComparison_app B S hS 𝒳 _
    (isSumOfExtensionByZeroUnitsAb_single.{u + 1, u, u + 1} (inclusionTopology B S hS 𝒳) x)

/-- **Stacks 0H10, part (2)(b), for complexes, with no hypothesis.** Let `𝒳` be an algebraic
stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison morphism of topoi of
Stacks 08MZ, whose inverse image is restriction to the flat objects. For every object `x` of the
flat-fppf site and every `K` in the unbounded derived category of abelian sheaves on
`𝒳_{fppf}`,

`RΓ(𝒳_{flat,fppf}/x, g⁻¹K) = RΓ(x, K)`,

naturally in `K`, where on each side cohomology over `x` is the right derived functor of sections
over `x` on the respective site (the convention of Stacks 0DD8 here; it is cohomology of the
slice site by Stacks 03F3). This is `derivedSectionsRestrictionIso` with its hypothesis `hgen`
proved, by `derivedLowerShriekComputesFlatGenerator`. -/
@[stacks 0H10 "part (2)(b) for complexes, at the flat-fppf site, with NO hypothesis: the half of \
Tag 0794 that `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso` carries as `hgen` \
is `AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekComputesFlatGenerator`. Cohomology over \
an object is the derived functor of sections over it (equal to cohomology of the slice site by \
Tag 03F3)"]
def derivedSectionsRestrictionIsoOfFlatObject
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι ⋙
        derivedSections B S hS 𝒳 x ≅
      derivedSectionsFppf B S hS 𝒳 ((objectProperty B S hS 𝒳).ι.obj x) :=
  derivedSectionsRestrictionIso B S hS 𝒳 x (derivedLowerShriekComputesFlatGenerator B S hS 𝒳 x)

end AlgebraicGeometry.Stack.FlatFppf

namespace AlgebraicGeometry.Stack.LisseEtale

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **`Lg_!` on the lisse-étale site is computed degreewise on a bounded above complex of direct
sums of the `j_{U!} ℤ_U`** (the half of Stacks 0794 saying that the left derived functor is
computed on its resolving class), with no hypothesis. -/
theorem isIso_derivedAbelianLowerShriekComparison_app
    (L : CochainComplex (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) ℤ)
    [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnitsAb.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
      (L.X n)) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
    IsIso ((derivedAbelianLowerShriekComparison.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :=
  have := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  isIso_derivedAbelianLowerShriekComparison_app_of_acyclic.{u + 1, u, u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι (abelianLowerShriekAcyclic.{u, w} B S hS 𝒳) L hL

/-- **The half of Stacks 0794 at a generator of the lisse-étale site, proved.** The counit of
`Lg_!` is invertible at the single complex on `j_{x!} ℤ_x`, for every object `x` of the
lisse-étale site of every algebraic stack. -/
theorem derivedLowerShriekComputesSmoothGenerator (x : LisseEtale.{u, w} B S hS 𝒳) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
    Stacks.Cohomology.DerivedLowerShriek.BigSite.DerivedAbelianLowerShriekComputesGenerator.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι x :=
  isIso_derivedAbelianLowerShriekComparison_app B S hS 𝒳 _
    (isSumOfExtensionByZeroUnitsAb_single.{u + 1, u, u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) x)

/-- Unbounded derived sections over an object of the lisse-étale site of an algebraic stack:
`RΓ(x, -)` on `D(𝒳_{lisse,étale})`, the total right derived functor of sections over `x`. -/
abbrev derivedSections (x : LisseEtale.{u, w} B S hS 𝒳) :
    DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory AbCat.{u, u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSections.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳) x

/-- Unbounded derived sections over an object of the étale site of an algebraic stack:
`RΓ(x, -)` on `D(𝒳_{étale})`. -/
abbrev derivedSectionsEtale (x : 𝒳.val.val.obj) :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AbCat.{u, u + 1}) ⥤ DerivedCategory AbCat.{u, u + 1} :=
  Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSections.{u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) x

/-- **Stacks 0H10, part (1)(b), for complexes, with no hypothesis.** Let `𝒳` be an algebraic
stack and let `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` be the comparison morphism of topoi of
Stacks 08MZ, whose inverse image is restriction to the smooth objects. For every object `x` of
the lisse-étale site and every `K` in the unbounded derived category of abelian sheaves on
`𝒳_{étale}`,

`RΓ(𝒳_{lisse,étale}/x, g⁻¹K) = RΓ(x, K)`,

naturally in `K`, where on each side cohomology over `x` is the right derived functor of sections
over `x` on the respective site (the convention of Stacks 0DD8 here; it is cohomology of the
slice site by Stacks 03F3).

This is Stacks 0DD8 (1) on sites that need not be small,
`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSectionsRestrictionIso`, at the
lisse-étale inclusion: continuity and cocontinuity come from
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, the existence and absoluteness
of `Lg_!` from `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`, and the counit at
the generator from `derivedLowerShriekComputesSmoothGenerator`. -/
@[stacks 0H10 "part (1)(b) for complexes, at the lisse-étale site, with NO hypothesis. \
Cohomology over an object is the derived functor of sections over it (equal to cohomology of the \
slice site by Tag 03F3)"]
def derivedSectionsRestrictionIso (x : LisseEtale.{u, w} B S hS 𝒳) :
    derivedAbelianRestriction.{u, w} B S hS 𝒳 ⋙ derivedSections B S hS 𝒳 x ≅
      derivedSectionsEtale B S hS 𝒳 ((smoothObject.{u, w} B S hS 𝒳).ι.obj x) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  haveI := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSectionsRestrictionIso.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι x (derivedLowerShriekComputesSmoothGenerator B S hS 𝒳 x)

end AlgebraicGeometry.Stack.LisseEtale

end
