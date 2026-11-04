module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites

/-!
# Every set-sized collection of schemes lies in a big fppf site

A big fppf site of `AlgebraicGeometry.BigFppfSite` is built from a size cutoff `κ`, giving the
full subcategory `Sch_κ`, together with a set-sized system of chosen fppf covering families. The
construction retains all of its choices, so nothing in the structure says that a *given* scheme
can be found inside one. This file supplies that, in the form the source uses whenever it says
"let `S` be a scheme and fix a big fppf site containing it": for any set of schemes that is small
in the working universe there is a big fppf site all of whose members it contains.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.ofCutoff`: a big fppf site with a prescribed cutoff.

## Main results

* `AlgebraicGeometry.BigFppfSite.exists_containing`: a small set of schemes is contained in some
  big fppf site.
* `AlgebraicGeometry.BigFppfSite.exists_contains`: the one-scheme case, stated so that it can be
  used without naming a set.

## Implementation notes

The cutoff comes from **Stacks 000J**, `AlgebraicGeometry.exists_size_cutoff`, which produces an
uncountable strong prelimit of uncountable cofinality above the sizes of the given schemes —
exactly the three conditions `AlgebraicGeometry.BigFppfSite` asks of its cutoff. The chosen
covering system comes from `exists_covBounded_isSite` applied to the fppf covering
families of `Sch_κ`, whose site axioms are `AlgebraicGeometry.isSite_fppfCutoff`; the set of
initially prescribed coverings is taken empty, which is what makes the support condition
vacuous.

This is the single-site companion of `AlgebraicGeometry.exists_common_bigFppfSite`
(**Stacks 022J**), which enlarges a family of big fppf sites to a common one. That theorem starts
from sites and so cannot be used here, where there is no site to start from; conversely the
construction here is the `ι = PEmpty` skeleton of that one with a prescribed cutoff.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.BigFppfSite

/-- **A big fppf site with a prescribed cutoff and prescribed initial schemes.** The cutoff `κ`
must satisfy the three conditions of **Stacks 000J** and dominate the sizes of the initial
schemes; the chosen covering system is a bounded representative system for the fppf covering
families of `Sch_κ` (**Stacks 000X**), with no initially prescribed coverings. Its cutoff is `κ`
by definition, so its underlying category is `Sch_κ` on the nose. -/
public noncomputable abbrev ofCutoff (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    (S₀ : Set Scheme.{u}) [Small.{u} S₀] (hS₀ : ∀ X ∈ S₀, X.size < κ) : BigFppfSite.{u} :=
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1} (AlgebraicGeometry.SchemeBelow κ)) := ∅
  have : Small.{u + 1} Cov₀ := inferInstance
  have h := _root_.exists_covBounded_isSite (AlgebraicGeometry.IsFppfCovering (κ := κ))
    (isSite_fppfCutoff κ) Cov₀ (by intro U hU; cases hU)
  { initialSchemes := S₀
    initialSchemes_small := inferInstance
    cutoff := κ
    aleph0_lt_cutoff := hκ
    cutoff_isStrongPrelimit := hsl
    aleph0_lt_cutoff_cof := hcof
    initialSchemes_mem := hS₀
    initialCoverings := Cov₀
    initialCoverings_small := inferInstance
    initialCoverings_supported := by simp [Cov₀]
    coveringBound := Classical.choose h
    coveringOrdinal := Classical.choose (Classical.choose_spec h)
    coveringOrdinal_isSuccLimit := (Classical.choose_spec (Classical.choose_spec h)).1
    initialCoverings_mem := by simp [Cov₀]
    coverings_isSite := (Classical.choose_spec (Classical.choose_spec h)).2.2.1
    fppf_has_representative := (Classical.choose_spec (Classical.choose_spec h)).2.2.2 }

/-- The cutoff of `AlgebraicGeometry.BigFppfSite.ofCutoff κ hκ hsl hcof S₀ hS₀` is `κ`. -/
@[simp]
public theorem ofCutoff_cutoff (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    (S₀ : Set Scheme.{u}) [Small.{u} S₀] (hS₀ : ∀ X ∈ S₀, X.size < κ) :
    (ofCutoff κ hκ hsl hcof S₀ hS₀).cutoff = κ := rfl

/-- **A set-sized collection of schemes is contained in some big fppf site.**

The cutoff is the one **Stacks 000J** supplies above the sizes of the given schemes, and the
site is `AlgebraicGeometry.BigFppfSite.ofCutoff` at that cutoff. -/
theorem exists_containing (S₀ : Set Scheme.{u}) [Small.{u} S₀] :
    ∃ B : BigFppfSite.{u}, ∀ X ∈ S₀, B.Contains X := by
  obtain ⟨κ, hκ₀, hκ₁, hκ₂, hκS₀⟩ := AlgebraicGeometry.exists_size_cutoff S₀
  exact ⟨ofCutoff κ hκ₀ hκ₁ hκ₂ S₀ hκS₀, hκS₀⟩

/-- **A scheme is contained in some big fppf site.** The one-object case of
`AlgebraicGeometry.BigFppfSite.exists_containing`. -/
theorem exists_contains (X : Scheme.{u}) : ∃ B : BigFppfSite.{u}, B.Contains X := by
  obtain ⟨B, hB⟩ := exists_containing {X}
  exact ⟨B, hB X rfl⟩

end AlgebraicGeometry.BigFppfSite

end
