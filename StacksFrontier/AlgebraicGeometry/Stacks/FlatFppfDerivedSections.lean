module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over a flat object, on the flat-fppf site and on the fppf site

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison
morphism of topoi of Stacks 08MZ, so that `g⁻¹` is restriction to the flat objects. **Stacks 0H10
(2)(b)** asserts, for a complex `K` of abelian sheaves on the fppf site and an object `x` of the
flat-fppf site,

`RΓ(x, K) = RΓ(𝒳_{flat,fppf}/x, g⁻¹K)`.

This file proves it, as the instance at the flat-fppf inclusion of **Stacks 0DD8 (1)** — the same
statement for an arbitrary continuous and cocontinuous functor of sites — in the universe-free
form of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedSectionsOnABigSite.lean`.

## Cohomology over an object, not on the slice

The source writes the right-hand side as derived global sections on the *slice* site
`𝒳_{flat,fppf}/x`. Here, as in the library's form of Stacks 0DD8 and as in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyComparison.lean`, cohomology over `x` is
the right derived functor of sections over `x` on the site itself. The two agree by the
localization comparison of Stacks 03F3, which this library has only for a *small* site, whereas
neither the fppf site of `𝒳` nor its flat-fppf subsite is small; the sections convention is the
one available, and it is the convention Stacks 0DD8 and Stacks 03YU are stated with here.

## What is proved and what is carried

Every hypothesis of Stacks 0DD8 (1) is discharged for this inclusion with no assumption on `𝒳`:

* continuity and cocontinuity of the inclusion, from
  `AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`, which holds for every algebraic
  stack;
* the existence of `g_!` and of `g_*`, from essential smallness of the two sites
  (`AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_subsiteRestriction` and
  `AlgebraicGeometry.Stack.FlatFppf.hasPointwiseRightKanExtension_inclusion_ab`);
* Grothendieck abelianness of the abelian sheaves on both sites, from the same essential
  smallness;
* existence and absoluteness of `Lg_!` — Stacks 07AS (3) — from
  `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`, which discharges the acyclicity
  statement of Stacks 07AC for this inclusion.

One input is carried, as the explicit hypothesis `hgen`: the half of **Stacks 0794** which says
that the left derived functor is computed on the `P`-cellular complexes, at the single complex of
one generator `j_{x!} ℤ_x`. It is not available as a declaration in this library — the resolving
class of the construction is private to
`StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean` — and it is the same
hypothesis `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSectionsRestrictionIso` carries for
a small site.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso`: **Stacks 0H10 (2)(b)**.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSections_restriction`: the form in which the
  proof of Stacks 0H14 uses it — vanishing of `RΓ(x, K)` for an object `x` of the flat-fppf site
  transports to vanishing of `RΓ(x, g⁻¹K)` computed on the flat-fppf site.
* `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek_extensionByZeroUnit_iso`: the part of
  **Stacks 0H0Z** this library can discharge — `g_! (j_{x!} ℤ_x) ≅ j_{g(x)!} ℤ_{g(x)}` on the
  generators, with no hypothesis.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The one input of Stacks 07AC that this library leaves open, at a generator of the
flat-fppf site.** The derived lower-shriek comparison is invertible at the single complex of the
free abelian sheaf `j_{x!} ℤ_x` on an object `x` of the flat-fppf site: that is the half of
Stacks 0794 asserting that the left derived functor is computed on the `P`-cellular complexes,
read at a one-term complex whose term lies in `P`.

It is a hypothesis rather than a theorem because the resolving class of the construction of
`Lg_!` is private to `StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`; the
same hypothesis is carried by
`Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSectionsRestrictionIso`. Everything else
Stacks 0DD8 (1) needs is discharged for this inclusion — see the module docstring. -/
abbrev DerivedLowerShriekComputesFlatGenerator
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) : Prop :=
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳
    (abelianLowerShriekAcyclic B S hS 𝒳)
  BigSite.DerivedAbelianLowerShriekComputesGenerator.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι x

/-- Unbounded derived sections over an object of the flat-fppf site of an algebraic stack:
`RΓ(x, -)` on `D(𝒳_{flat,fppf})`, the total right derived functor of sections over `x`. -/
abbrev derivedSections (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  BigSite.derivedAbelianSections.{u + 1} (inclusionTopology B S hS 𝒳) x

/-- Unbounded derived sections over an object of the fppf site of an algebraic stack:
`RΓ(x, -)` on `D(𝒳_{fppf})`. -/
abbrev derivedSectionsFppf (x : 𝒳.val.val.obj) :
    DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  BigSite.derivedAbelianSections.{u + 1} (fppfTopology B S hS 𝒳) x

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- **Stacks 0H10, part (2)(b), for complexes.** Let `𝒳` be an algebraic stack and let
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison morphism of topoi of Stacks 08MZ, whose
inverse image is restriction to the flat objects. For every object `x` of the flat-fppf site and
every `K` in the unbounded derived category of abelian sheaves on `𝒳_{fppf}`,

`RΓ(x, g⁻¹K) = RΓ(x, K)`,

naturally in `K`, where on each side cohomology over `x` is the right derived functor of sections
over `x` on the respective site (the convention of Stacks 0DD8 and Stacks 03YU here; see the
module docstring on why not the slice site).

The closure condition of Stacks 07AK (1), the existence of `g_!` and `g_*`, Grothendieck
abelianness of both categories of abelian sheaves, and the acyclicity statement of Stacks 07AC
that Stacks 07AS (3) needs are all discharged, with no hypothesis on `𝒳`. The single carried
input is `hgen`. -/
@[stacks 0H10 "part (2)(b) for complexes, at the flat-fppf site, with cohomology over an object \
taken as the derived functor of sections over it; conditional only on the half of Stacks 0794 \
that computes Lg_! on a generator"]
def derivedSectionsRestrictionIso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))
    (hgen : DerivedLowerShriekComputesFlatGenerator B S hS 𝒳 x) :
    Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳)
          (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι ⋙
        derivedSections B S hS 𝒳 x ≅
      derivedSectionsFppf B S hS 𝒳 ((objectProperty B S hS 𝒳).ι.obj x) :=
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
  BigSite.derivedAbelianSectionsRestrictionIso.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι x hgen

/-- **The form in which the proof of Stacks 0H14 uses Stacks 0H10 (2)(b).** If the derived
sections of `K` over an object `x` of the flat-fppf site vanish, computed on the fppf site, then
the derived sections of `g⁻¹K` over `x` vanish, computed on the flat-fppf site.

This is the first step of the vanishing argument of Stacks 0H14: it turns the hypothesis of that
lemma — vanishing of `RΓ(x, K)` for the flat objects lying over affine schemes — into a statement
about `g⁻¹K` on the flat-fppf site, where
`AlgebraicGeometry.Stack.FlatFppf.isCoveringFamily_isAffine` makes those objects a covering
family. -/
theorem isZero_derivedSections_restriction
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))
    (hgen : DerivedLowerShriekComputesFlatGenerator B S hS 𝒳 x)
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hK : IsZero ((derivedSectionsFppf B S hS 𝒳
      ((objectProperty B S hS 𝒳).ι.obj x)).obj K)) :
    IsZero ((derivedSections B S hS 𝒳 x).obj
      ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι).obj K)) :=
  IsZero.of_iso hK ((derivedSectionsRestrictionIso B S hS 𝒳 x hgen).app K)

/-- **The degree-zero comparison of Stacks 0H0Z, on the generators of `Ab(𝒳_{flat,fppf})`.** For
every object `x` of the flat-fppf site of an algebraic stack,

`g_! (j_{x!} ℤ_x) ≅ j_{g(x)!} ℤ_{g(x)}`,

with no hypothesis. This is
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekExtensionByZeroUnitAbIso` at the
flat-fppf inclusion; it is what the proof of **Stacks 0H0Z** uses in place of
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso`, which is unavailable here
because neither site has a terminal object as soon as `𝒳` has a nontrivial automorphism
(`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`).

It is recorded here because it is the only part of Stacks 0H0Z that this library can discharge:
the passage from the generators to the constant sheaf is what the source obtains from a
presentation of `𝒳`, through Stacks 07AV and the descent statements of Stacks 06XD and 06XH,
none of which is available. -/
theorem abelianLowerShriek_extensionByZeroUnit_iso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    Nonempty ((Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriek.{u + 1}
          (inclusionTopology B S hS 𝒳)
          (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι).obj
        (extensionByZeroUnitAb.{u + 1} (inclusionTopology B S hS 𝒳) x) ≅
      extensionByZeroUnitAb.{u + 1} (fppfTopology B S hS 𝒳)
        ((objectProperty B S hS 𝒳).ι.obj x)) :=
  ⟨abelianLowerShriekExtensionByZeroUnitAbIso.{u + 1} (inclusionTopology B S hS 𝒳)
    (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι x⟩

end AlgebraicGeometry.Stack.FlatFppf

end
