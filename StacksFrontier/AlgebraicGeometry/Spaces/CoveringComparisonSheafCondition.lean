module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies

/-!
# The sheaf condition for the coarser covering families of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an algebraic space over
`S`. The covering families of algebraic spaces over `S` are ordered across the five topologies
of **Stacks 03YH**: a Zariski, étale, smooth, syntomic or fppf covering is an fpqc covering,
by **Stacks 0DFQ**. A presheaf on the slice category over `X` therefore satisfies the sheaf
condition for a covering family in any of those five senses as soon as it satisfies it for
every fpqc one. That is all this module says: the covering comparisons of
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies`, transported from covering
families to the sheaf condition on their presieves.

The point of stating it is that the list of sheaf conditions in a statement like
**Stacks 0DG7** — that `π_X⁻¹F` is a sheaf for the smooth, syntomic, fppf, fpqc and ph
coverings of algebraic spaces over `X` — collapses to two independent ones. Taking the
presheaf `P` below to be the one underlying the inverse image
`(AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleMorphism T X).inverseImage.obj F` turns
the fpqc clause of Tag 0DG7 into its smooth, syntomic and fppf clauses (and, a fortiori, into
étale and Zariski ones); only the fpqc and the ph clause carry content of their own.

## Main results

* `AlgebraicGeometry.Space.isSheafFor_fppfCovering_of_isSheafFor_fpqcCoverings`, and the
  syntomic, smooth, étale and Zariski variants: a presheaf on the slice category over an
  algebraic space over `S` which satisfies the sheaf condition for every fpqc covering family
  satisfies it for every covering family of each of the four coarser topologies.

## Implementation notes

The covering family of a `CategoryTheory.PreZeroHypercover` of an object `U` of the slice
category is read in algebraic spaces over `S` by `CategoryTheory.PreZeroHypercover.map` along
`CategoryTheory.Over.forget`, which is the form the covering predicates of
`StacksFrontier.AlgebraicGeometry.Spaces.Coverings` take. The presieve in the sheaf condition is
the one generated in the slice category itself, so no comparison of presieves is involved and
the hypothesis is applied to the very hypercover of the conclusion. The presheaf, its universe
of values and the index universe of the covering family are arbitrary.

The Zariski case carries the algebraicity of the target and of the sources as extra
hypotheses, because `AlgebraicGeometry.Space.IsZariskiCovering` is stated for arbitrary
presheaves on the big fppf site while the other four predicates have those conditions as
fields; this follows `AlgebraicGeometry.Space.isFpqcCovering_of_isZariskiCovering`.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {P : (Over X)ᵒᵖ ⥤ Type w}

/-- A presheaf on the slice category over an algebraic space `X` over `S` which satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `S` satisfies it for
every fppf covering family, since an fppf covering is an fpqc covering by **Stacks 0DFQ**. -/
theorem isSheafFor_fppfCovering_of_isSheafFor_fpqcCoverings
    (hP : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      IsFpqcCovering B S hS (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
        Presieve.IsSheafFor P E.presieve₀)
    {U : Over X} (E : PreZeroHypercover.{v} U)
    (hE : IsFppfCovering B S hS (fun i ↦ ((E.map (Over.forget X)).X i).obj)
      (fun i ↦ ((E.map (Over.forget X)).f i).hom)) :
    Presieve.IsSheafFor P E.presieve₀ :=
  hP U E (isFpqcCovering_of_isFppfCovering B S hS _ _ hE)

/-- A presheaf on the slice category over an algebraic space `X` over `S` which satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `S` satisfies it for
every syntomic covering family, since a syntomic covering is an fpqc covering by
**Stacks 0DFQ**. -/
theorem isSheafFor_syntomicCovering_of_isSheafFor_fpqcCoverings
    (hP : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      IsFpqcCovering B S hS (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
        Presieve.IsSheafFor P E.presieve₀)
    {U : Over X} (E : PreZeroHypercover.{v} U)
    (hE : IsSyntomicCovering B S hS (fun i ↦ ((E.map (Over.forget X)).X i).obj)
      (fun i ↦ ((E.map (Over.forget X)).f i).hom)) :
    Presieve.IsSheafFor P E.presieve₀ :=
  hP U E (isFpqcCovering_of_isSyntomicCovering B S hS _ _ hE)

/-- A presheaf on the slice category over an algebraic space `X` over `S` which satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `S` satisfies it for
every smooth covering family, since a smooth covering is an fpqc covering by
**Stacks 0DFQ**. -/
theorem isSheafFor_smoothCovering_of_isSheafFor_fpqcCoverings
    (hP : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      IsFpqcCovering B S hS (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
        Presieve.IsSheafFor P E.presieve₀)
    {U : Over X} (E : PreZeroHypercover.{v} U)
    (hE : IsSmoothCovering B S hS (fun i ↦ ((E.map (Over.forget X)).X i).obj)
      (fun i ↦ ((E.map (Over.forget X)).f i).hom)) :
    Presieve.IsSheafFor P E.presieve₀ :=
  hP U E (isFpqcCovering_of_isSmoothCovering B S hS _ _ hE)

/-- A presheaf on the slice category over an algebraic space `X` over `S` which satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `S` satisfies it for
every étale covering family, since an étale covering is an fpqc covering by **Stacks 0DFQ**. -/
theorem isSheafFor_etaleCovering_of_isSheafFor_fpqcCoverings
    (hP : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      IsFpqcCovering B S hS (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
        Presieve.IsSheafFor P E.presieve₀)
    {U : Over X} (E : PreZeroHypercover.{v} U)
    (hE : IsEtaleCovering B S hS (fun i ↦ ((E.map (Over.forget X)).X i).obj)
      (fun i ↦ ((E.map (Over.forget X)).f i).hom)) :
    Presieve.IsSheafFor P E.presieve₀ :=
  hP U E (isFpqcCovering_of_isEtaleCovering B S hS _ _ hE)

/-- A presheaf on the slice category over an algebraic space `X` over `S` which satisfies the
sheaf condition for every fpqc covering family of algebraic spaces over `S` satisfies it for
every Zariski covering family whose target and sources are algebraic spaces, since such a
Zariski covering is an fpqc covering by **Stacks 0DFQ**. -/
theorem isSheafFor_zariskiCovering_of_isSheafFor_fpqcCoverings
    (hP : ∀ (U : Over X) (E : PreZeroHypercover.{v} U),
      IsFpqcCovering B S hS (fun i ↦ ((E.map (Over.forget X)).f i).hom) →
        Presieve.IsSheafFor P E.presieve₀)
    {U : Over X} (E : PreZeroHypercover.{v} U)
    (hE : IsZariskiCovering B S hS E.I₀ (fun i ↦ ((E.map (Over.forget X)).X i).obj)
      (fun i ↦ ((E.map (Over.forget X)).f i).hom)) :
    Presieve.IsSheafFor P E.presieve₀ :=
  hP U E (isFpqcCovering_of_isZariskiCovering B S hS _ _ U.left.property
    (fun i ↦ ((E.map (Over.forget X)).X i).property) hE)

end AlgebraicGeometry.Space

end
