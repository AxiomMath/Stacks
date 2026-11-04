module

public import Mathlib.CategoryTheory.Generator.Basic
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflectionLarge
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSections

/-!
# A separating family for the adequate modules on a chosen big site over an affine base

Let `U = Spec A` be affine and let `B` be a chosen big `τ`-site over `U`. The linearly adequate
module-valued functors on the `A`-algebras of the site form a separating family for the adequate
ones there, which is `AdequateFunctor.isSeparating_ofLinearPresentationSite_large`, the form of
[Stacks, Tag 06UX] over the algebras of the site. This file transports that family to
`Adeq(𝒪)` along an identification `E` of `Adeq(𝒪)` with the adequate module-valued functors on
the algebras of the site, which is the identification of [Stacks, Tag 06ZJ].

Everything is at a module universe `max u m` independent of the universe `u` of the site, which
is the generality [Stacks, Tag 06ZU] is stated in; the size side condition that `Spec A` belongs
to the site is the field `Stacks.Adequate.BigSite.base_mem`, so no hypothesis beyond `E` is
needed.

## Main definitions

* `Stacks.Adequate.linearlyAdequateFamilyOn` — the chosen family of linearly adequate
  module-valued functors on the `A`-algebras of the site, as a property of the adequate ones.
* `Stacks.Adequate.adequateSeparatingFamily` — its transport to `Adeq(𝒪)` along `E`.

## Main results

* `Stacks.Adequate.isSeparating_linearlyAdequateFamilyOn` — the chosen family separates the
  adequate module-valued functors on the `A`-algebras of the site.
* `Stacks.Adequate.isSeparating_adequateSeparatingFamily` — `Adeq(𝒪)` has a separating family,
  namely the image of that one under `E.inverse`.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The family of linearly adequate module-valued functors on the `A`-algebras of a chosen big
site presented by maps of finite free `A`-modules, as a property of the adequate ones. The
presentations form a type, which is what makes the family small. -/
public abbrev linearlyAdequateFamilyOn :
    ObjectProperty (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
  ObjectProperty.ofObj (AdequateFunctor.ofLinearPresentationSite_large.{u, m} (A : Type u) B.cutoff)

/-- **The linearly adequate functors separate the adequate module-valued functors on the
`A`-algebras of a chosen big site**, at every module universe above the universe of the site. -/
public theorem isSeparating_linearlyAdequateFamilyOn :
    (linearlyAdequateFamilyOn.{u, m} B).IsSeparating :=
  AdequateFunctor.isSeparating_ofLinearPresentationSite_large.{u, m} B.base_mem

variable (E : (adequate.{u, max u m} B).FullSubcategory ≌
  (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).FullSubcategory)

/-- The family of linearly adequate functors on the `A`-algebras of the site, carried into
`Adeq(𝒪)` by the inverse of an identification `E` of the two categories. -/
public abbrev adequateSeparatingFamily :
    ObjectProperty (adequate.{u, max u m} B).FullSubcategory :=
  (linearlyAdequateFamilyOn.{u, m} B).strictMap E.inverse

/-- **The adequate `𝒪`-modules on a chosen big site over an affine base have a separating
family**, given an identification `E` of `Adeq(𝒪)` with the adequate module-valued functors on
the `A`-algebras of the site: the image under `E.inverse` of the family of linearly adequate
functors. -/
public theorem isSeparating_adequateSeparatingFamily :
    (adequateSeparatingFamily.{u, m} B E).IsSeparating :=
  (isSeparating_linearlyAdequateFamilyOn.{u, m} B).of_equivalence E.symm

end Stacks.Adequate

end
