module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology

/-!
# Étale cohomology of abelian sheaves on an algebraic space

`AlgebraicGeometry.Space.SmallEtaleCohomology` supplies cohomology of *modules* on the small
étale ringed site of an algebraic space — the derived functors of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`, as constructed for an arbitrary ringed
site in Stacks 071H.  Several statements of Chapters 68 and 69 are instead about cohomology of
*abelian sheaves* on the small étale site, that is about the right derived functors of
Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of `constantSheaf`.  This file names
those derived functors and records the two facts their existence rests on.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleCohomology` is the `p`-th right derived functor of global
  sections on the small étale site of an algebraic space, with coefficients in abelian groups:
  `H^p(X_étale, -)`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleGamma_additive`: global sections on the small étale site
  is an additive functor, so its right derived functors are defined.
* `AlgebraicGeometry.Space.smallEtaleCohomologyZeroIso`: in degree zero the derived functor is
  global sections itself.

## Implementation notes

The two inputs to `CategoryTheory.Functor.rightDerived` are enough injectives in the source
and additivity of the functor.  Enough injectives is
`AlgebraicGeometry.Space.smallEtaleAbelianSheaf_enoughInjectives`, which holds because the
small étale site is essentially small at `u`, so its category of `Ab.{u + 1}`-valued sheaves
is Grothendieck abelian; it is found by instance search once this file is imported, and is
not restated.  Additivity is not found by instance search and is supplied here: `Sheaf.Γ` is
a right adjoint, hence preserves binary products, hence is additive.

The same adjointness makes `Sheaf.Γ` preserve all finite limits, which is the hypothesis of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` and hence gives the degree-zero
identification.

The coefficients are `Ab.{u + 1}`, the universe in which the small étale site of a
`Scheme.{u}` is a site; this is the same choice as in
`AlgebraicGeometry.Space.smallEtaleAbelianSheaf_enoughInjectives`.  As there, no sheaf
condition and no atlas is needed, so the declarations are stated for an arbitrary presheaf on
the big fppf category over `S`.

No `@[stacks]` tag is carried here.  Tag 071H is already registered on the general
construction in `StacksDraft.Ch21.Sec2.CohomologyOfModulesOnASite`, and the Chapter 68–69
statements these declarations are prerequisites for — Stacks 073E and 07V6 — are not proved.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Global sections of abelian sheaves on the small étale site of a presheaf on the big fppf
category over `S` is an additive functor: it is a right adjoint, so it preserves binary
products.

This is the hypothesis, besides enough injectives, under which
`CategoryTheory.Functor.rightDerived` of `CategoryTheory.Sheaf.Γ` is defined. -/
instance smallEtaleGamma_additive :
    (Sheaf.Γ (SmallEtale.topology B S hS F) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Cohomology of abelian sheaves on the small étale site of an algebraic space: the `p`-th
right derived functor of global sections. -/
def smallEtaleCohomology (p : ℕ) :
    Sheaf (SmallEtale.topology B S hS F) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (Sheaf.Γ (SmallEtale.topology B S hS F) Ab.{u + 1}).rightDerived p

/-- In degree zero, cohomology on the small étale site is global sections: `Sheaf.Γ` is a
right adjoint, hence left exact. -/
def smallEtaleCohomologyZeroIso :
    smallEtaleCohomology B S hS F 0 ≅ Sheaf.Γ (SmallEtale.topology B S hS F) Ab.{u + 1} :=
  Functor.rightDerivedZeroIsoSelf _

end AlgebraicGeometry.Space

end
