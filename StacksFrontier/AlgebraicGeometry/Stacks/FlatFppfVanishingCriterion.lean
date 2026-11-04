module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedSections
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedSections
public import StacksFrontier.CategoryTheory.Sites.VanishingOfDerivedSections
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the cohomology of a complex with no cohomology over the flat affine objects

Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒳_{fppf})` such that
`RΓ(x, K) = 0` for every object `x` of `𝒳` lying over an affine scheme `U` with `U → 𝒳` flat.
**Stacks 0H14** says that then `H^i(𝒳, K) = 0` for all `i`.

This file proves the steps of the source's own proof; they are assembled into **Stacks 0H14** as
`AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine`, in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatAffineCohomologyVanishing.lean`, which also
discharges the two inputs described below. Write
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` for the comparison morphism of topoi of Stacks 08MZ.

* The hypothesis is first moved across `g`: by **Stacks 0H10 (2)(b)**, which this library has as
  `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSections_restriction`, the derived sections of
  `g⁻¹K` over a flat object lying over an affine scheme vanish, computed on the flat-fppf site.
* Those objects are a covering family of the flat-fppf site
  (`AlgebraicGeometry.Stack.FlatFppf.isCoveringFamily_isAffine`), so `g⁻¹K = 0` by the vanishing
  criterion `Stacks.Cohomology.DerivedSectionsVanishing.isZero_of_isZero_derivedAbelianSections`.
  That is the sentence *"since every object of that site has a covering by such objects, the
  cohomology sheaves vanish, hence the complex is zero"* of the source, and it is proved, not
  assumed: see the module docstring of
  `StacksFrontier/CategoryTheory/Sites/VanishingOfDerivedSections.lean` for the route, which is
  through the projection from cycles on a K-injective representative rather than through the
  hypercohomology edge morphism of Stacks 0BKV.
* Derived global sections on the flat-fppf site then vanish at `g⁻¹K`, and **Stacks 0H10 (2)(a)**
  identifies them with the derived global sections of `K` on the fppf site.

## What is carried, and why

Two inputs of the source's proof are hypotheses rather than theorems in this file (`hglobal` was
an input of a conditional form of Stacks 0H14, now removed in favour of
`AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine`,
which proves both):

* `hgen`, the half of **Stacks 0794** which says that the left derived functor of `g_!` is
  computed on the `P`-cellular complexes, read at the single complex of a generator
  `j_{x!} ℤ_x`, and only at the flat objects `x` lying over an affine scheme — the ones the
  covering family consists of. It is exactly the input that the library's form of Stacks 0H10 (2)(b),
  `AlgebraicGeometry.Stack.FlatFppf.derivedSectionsRestrictionIso`, carries, for the reason
  given there: the resolving class of the construction of `Lg_!` is private to
  `StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`.
* `hglobal`, the comparison of **Stacks 0H10 part (2)(a)** for complexes,
  `RΓ(𝒳_{fppf}, K) = RΓ(𝒳_{flat,fppf}, g⁻¹K)`. The source obtains it from `Lg_! ℤ = ℤ`, which is
  **Stacks 0H0Z**, through the derived adjunction `Lg_! ⊣ g⁻¹` of Stacks 07AS (3) — and that
  adjunction *is* available here, as
  `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekAdjunction`. What is missing is
  Stacks 0H0Z: this library has only its value on the generators,
  `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek_extensionByZeroUnit_iso`, and the passage
  from those to the constant sheaf is what the source takes from a presentation of `𝒳`, through
  Stacks 07AV and the descent statements of Stacks 06XD and 06XH, none of which this library
  has.

Everything else the proof uses is discharged with no hypothesis on `𝒳`.

The instance argument `(derivedGlobalSectionsOnFlatSite B S hS 𝒳).PreservesZeroMorphisms` is the
one
`AlgebraicGeometry.Stack.isZero_homology_derivedGlobalSections_of_isCoveringFamily` also carries:
`CategoryTheory.Functor.totalRightDerived` is a left Kan extension along a localization functor
and comes with no additivity instance, so that a zero object goes to a zero object is left as an
assumption rather than silently used.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedGlobalSectionsOnFlatSite`: unbounded derived global
  sections on the flat-fppf site.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_restriction_of_isZero_derivedSections_flatAffine`: the
  unconditional half — `g⁻¹K = 0`.
* **Stacks 0H14** itself is
  `AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine`, in
  `StacksFrontier/AlgebraicGeometry/Stacks/FlatAffineCohomologyVanishing.lean`.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
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

/-- Global sections of abelian sheaves on the flat-fppf site form an additive functor: the
global sections functor is a right adjoint, so it preserves binary products. -/
instance globalSectionsOnFlatSite_additive
    [HasGlobalSectionsFunctor (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}] :
    (Sheaf.Γ (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Unbounded derived global sections on the flat-fppf site of an algebraic stack:
`RΓ(𝒳_{flat,fppf}, -)`, the total right derived functor of global sections. It is the target of
the comparison of Stacks 0H10 part (2)(a), which is the hypothesis `hglobal` below. -/
abbrev derivedGlobalSectionsOnFlatSite
    [HasGlobalSectionsFunctor (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}] :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  ((Sheaf.Γ (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))

/-- **The inverse image of `K` on the flat-fppf site is zero.** If the derived sections of a
complex `K` of abelian fppf sheaves vanish over every object of `𝒳` that lies over an affine
scheme and is flat over `𝒳`, then `g⁻¹K = 0`.

This is the first two steps of the proof of **Stacks 0H14**: Stacks 0H10 (2)(b) carries the
hypothesis over to the flat-fppf site, where those objects form a covering family, and a complex
of abelian sheaves whose derived sections vanish on a covering family is zero. -/
theorem isZero_restriction_of_isZero_derivedSections_flatAffine
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hgen : ∀ x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x.obj)) →
      DerivedLowerShriekComputesFlatGenerator B S hS 𝒳 x)
    (hK : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsZero ((derivedSectionsFppf B S hS 𝒳 x).obj K)) :
    IsZero ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
      (objectProperty B S hS 𝒳).ι).obj K) := by
  have hP : (inclusionTopology B S hS 𝒳).IsCoveringFamily
      (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x.obj))) := by
    rw [inclusionTopology_eq_topology]
    exact isCoveringFamily_isAffine B S hS 𝒳
  refine Stacks.Cohomology.DerivedSectionsVanishing.isZero_of_isZero_derivedAbelianSections.{u + 1}
    (inclusionTopology B S hS 𝒳) hP _ fun x hx => ?_
  exact isZero_derivedSections_restriction B S hS 𝒳 x (hgen x hx) K (hK x.obj x.property hx)

end AlgebraicGeometry.Stack.FlatFppf

end
