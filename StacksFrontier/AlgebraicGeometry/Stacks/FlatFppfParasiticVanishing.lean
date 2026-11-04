module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedSections
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the derived sections over a flat object of a complex with parasitic cohomology

Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒳_{fppf})` whose cohomology sheaves
are parasitic, i.e. have vanishing sections at every object of `𝒳` lying over a scheme `U` for
which `U → 𝒳` is flat (**Stacks 0773**). **Stacks 0H13** says that then `RΓ(x, K) = 0` for every
such object `x`.

This file proves the steps of the source's own proof; they are assembled into **Stacks 0H13** in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfParasiticVanishingUnconditional.lean`. Write
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` for the comparison morphism of topoi of Stacks 08MZ.

* The objects of the flat-fppf site of **Stacks 0787** are exactly the flat objects of `𝒳`, and
  `g⁻¹` is restriction to them, so the parasitic hypothesis says precisely that every cohomology
  sheaf of `g⁻¹K` vanishes. That is `isZero_abelianRestriction_iff` below — the abelian-sheaf
  reading of **Stacks 07AR** (2), whose module form is
  `AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`.
* Hence `g⁻¹K = 0`: restriction is exact, so the cohomology sheaves of `g⁻¹K` are the
  restrictions of those of `K`, and an object of a derived category vanishes exactly when all of
  its cohomology objects do. That is the source's *"hence `g^{-1}K = 0` and we win"*, and it is
  `isZero_derivedAbelianRestriction_iff` below.
* **Stacks 0H10 (2)(b)**, which this library has as
  `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso`, identifies `RΓ(x, K)` with
  `RΓ(x, g⁻¹K)` for an object `x` of the flat-fppf site; the latter vanishes because `g⁻¹K` does.

Cohomology over an object is the right derived functor of sections over it, as in the
forms of Stacks 0H10 (2)(b) and Stacks 0DD8, not derived global sections on the slice site; see
the module docstring of `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedSections.lean` for
why the slice convention is unavailable here.

## The parasitic hypothesis on an abelian sheaf

`AlgebraicGeometry.Stack.IsParasitic` (**Stacks 0773**) is stated for a presheaf of modules over
the structure sheaf, whereas `D(𝒳_{fppf})` in Stacks 104.8 — and in **Stacks 0H14**,
`AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine` — is
the derived category of *abelian* sheaves, which is also where `RΓ(x, -)` is available. The
parasitic condition makes no reference to the module structure: it is vanishing of the sections
at the flat objects, and that is what is written out here, at the same `flatObject` predicate of
**Stacks 0787** that `AlgebraicGeometry.Stack.IsParasitic` quantifies over and in the same
`Subsingleton` form. No new predicate is introduced.

## What is carried, and why

The conditional form of **Stacks 0H13**, the corollary
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSections_of_parasitic_cohomology` in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfParasiticVanishingUnconditional.lean`, takes two
inputs as hypotheses rather than theorems, inputs that Stacks 0H10 and Stacks 0H14
carry for the same reasons; that file discharges both:

* `hgen`, the half of **Stacks 0794** which says that the left derived functor of `g_!` is
  computed on the `P`-cellular complexes, read at the single complex of the generator
  `j_{x!} ℤ_x` for the one object `x` in question. It is exactly the input that
  `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso` carries, because the resolving
  class of the construction of `Lg_!` is private to
  `StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`.
* The instance `(derivedSections B S hS 𝒳 ⟨x, hx⟩).PreservesZeroMorphisms`, the analogue of
  what the conditional form of Stacks 0H14 (since replaced by
  `AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine`)
  carried: `CategoryTheory.Functor.totalRightDerived` is a left Kan extension along a
  localization functor and comes with no additivity instance, so that a zero object goes to a
  zero object is assumed rather than silently used.

Everything else is proved, with no hypothesis on `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isZero_abelianRestriction_iff`: the abelian-sheaf reading of
  **Stacks 07AR** (2) — `g⁻¹F = 0` exactly when `F` is parasitic.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedAbelianRestriction_iff`: the same for
  complexes, with no hypothesis — `g⁻¹K = 0` exactly when every cohomology sheaf of `K` is
  parasitic.
* **Stacks 0H13** itself is
  `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSectionsFppf_of_parasitic_cohomology`, in
  `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfParasiticVanishingUnconditional.lean`, assembled
  from the two results above.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0H13](https://stacks.math.columbia.edu/tag/0H13)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.FlatFppf

universe t v₁ u₁ u w

/-- A sheaf of abelian groups on a site is a zero object exactly when all of its groups of
sections vanish. This is the abelian-sheaf counterpart of
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`'s underlying
`isZero_sheafOfModules_iff`: the forgetful functor to presheaves is faithful, so the identity of
a sheaf vanishes exactly when each of its components does. -/
private theorem isZero_sheafAb_iff {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [Abelian (Sheaf J AddCommGrpCat.{t})]
    (F : Sheaf J AddCommGrpCat.{t}) :
    IsZero F ↔ ∀ U : Cᵒᵖ, Subsingleton (F.obj.obj U) := by
  refine ⟨fun h U => AddCommGrpCat.subsingleton_of_isZero
    (Functor.map_isZero (sheafToPresheaf J AddCommGrpCat.{t} ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{t}).obj U) h), fun h => ?_⟩
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf J AddCommGrpCat.{t}).map_injective
  ext U x
  exact (h U).elim _ _

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AR (2), read on abelian sheaves.** The restriction `g⁻¹F` of an abelian sheaf `F`
on `𝒳_{fppf}` to the flat-fppf site vanishes exactly when `F` is parasitic in the sense of
**Stacks 0773**, i.e. its sections vanish at every flat object of `𝒳`.

The flat-fppf site of **Stacks 0787** has the flat objects of `𝒳` for its objects and `g⁻¹` is
restriction along their inclusion, with the same groups of sections, so the two conditions are
the same condition read on the two sites. The module form of this statement is
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`. -/
theorem isZero_abelianRestriction_iff
    (F : Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) :
    IsZero ((Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι).obj F) ↔
      ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Subsingleton (F.obj.obj (op x)) := by
  rw [isZero_sheafAb_iff]
  exact ⟨fun h x hx => h (op ⟨x, hx⟩), fun h U => h _ U.unop.2⟩

/-- **The kernel of `g⁻¹` on the unbounded derived category, with no hypothesis on `K`.** For a
complex `K` of abelian sheaves on `𝒳_{fppf}`, the restriction `g⁻¹K` to the flat-fppf site
vanishes exactly when every cohomology sheaf of `K` is parasitic (**Stacks 0773**).

This is the step *"our assumption means that the cohomology sheaves of `g^{-1}K` are zero, hence
`g^{-1}K = 0`"* of the proof of **Stacks 0H13**. Both sides are tested degree by degree:
restriction along a continuous and cocontinuous functor of sites is exact, so the cohomology
sheaves of `g⁻¹K` are the restrictions of those of `K`, vanishing of the restriction of a sheaf
is the parasitic condition by `isZero_abelianRestriction_iff`, and an object of a derived
category vanishes exactly when all of its cohomology objects do. It is the abelian-sheaf
counterpart of
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedModuleRestriction_iff_forall_isParasitic`. -/
theorem isZero_derivedAbelianRestriction_iff
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1})) :
    IsZero ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι).obj K) ↔
      ∀ n : ℤ, ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
        Subsingleton (((DerivedCategory.homologyFunctor
            (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) n).obj K).obj.obj (op x)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  rw [← isZero_abelianRestriction_iff]
  exact (((Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι).mapDerivedCategoryHomologyIso n).app K).isZero_iff

end AlgebraicGeometry.Stack.FlatFppf

end
