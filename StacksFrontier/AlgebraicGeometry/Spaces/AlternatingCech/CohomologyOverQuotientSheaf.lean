module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExtSpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOverASheafOfSets
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology

/-!
# Cohomology over a sheaf of sets on the spaces-étale site

The rows `q > 0` of the first page of the alternating Čech spectral sequence of
[Stacks, Tag 0728] are the groups `Ext^q(K^p, ℱ)`, and [Stacks, Tag 072C] needs them read as the
cohomology of the quotient `U_p = W_p/S_{p+1}`.  The machinery for that passage is
[Stacks, Tag 07A0]: `Ext` out of the free abelian sheaf on a sheaf of sets `K` is the cohomology
of the site of elements of `K` with the restricted coefficients, in *every* degree.

This file seats Tag 07A0 on the spaces-étale site of an algebraic space and reads it in the
`Abelian.zExt` spelling in which the first page of Tag 0728 is stated.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.zExtFreeAbelianSheafOnAddEquiv`: **[Stacks, Tag 07A0] on
  the spaces-étale site** — `Ext^p(ℤ_K, ℱ)`, in the `Abelian.zExt` spelling of
  [Stacks, Tag 0728]'s first page, is the cohomology of the site of elements of `K`, as an
  additive equivalence.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_zExt_freeAbelianSheafOn_of_subsingleton_sheafH`:
  the same in vanishing form, which is the shape the row hypothesis of [Stacks, Tag 072B] is
  stated in.

## Implementation notes

**That the seating works is the content.**  `Stacks.Cohomology.SheafOfSets` is developed for a
small site with coefficients at its own universe, and it needs three instances: `SmallCategory`,
`HasSheafify` for abelian coefficients, and `HasExt` for the sheaf category.  The spaces-étale
site `AlgebraicGeometry.Space.SpacesEtale.topology` has all three at `AddCommGrpCat.{u + 1}`,
which is the universe at which the alternating Čech development states its coefficients, so
Tag 07A0 applies here with no re-seating.  The two halves of its proof — exactness of `j⁻¹` and
its preservation of injectives, the latter being the injectivity assertion of Tag 07A0 — are
instances of that development, and the general engine behind it is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfAdjunction`: `Ext` out of the image of a
left adjoint whose right adjoint is right exact and preserves injectives.

**The universe gap, and what it does and does not cost.**  Tag 07A0 lands at `Ext` in the
morphism universe `u + 1` of the sheaf category, because its proof goes through injective
resolutions there; the first page of Tag 0728 is at `u + 2`, the universe of
`CategoryTheory.HasDerivedCategory.standard`.  `CategoryTheory.Abelian.Ext.chgUniv` crosses that
gap, and Mathlib has it only as an `Equiv`.

That `Equiv` *is* additive: the upgrade is
`Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv`, proved from
`CategoryTheory.Abelian.Ext.homEquiv_chgUniv`.  So the comparison is available as an additive
equivalence, which is what `AlgebraicGeometry.Space.SpacesEtale.zExtFreeAbelianSheafOnAddEquiv`
below states, and that is strictly more than a bijection.

What is genuinely unavailable is an isomorphism in `AddCommGrpCat`, and the reason is the
universe gap itself rather than additivity: `Abelian.zExt` of the Koszul term lives in
`Type (u + 2)` and `CategoryTheory.Sheaf.H` of the restricted coefficients in `Type (u + 1)`, so
the two groups are not objects of one `AddCommGrpCat` and no isomorphism between them can be
written.  This is the same situation as
`Stacks.Cohomology.SimplicialComponent.sheafHAddEquivChgUniv`, which is an `AddEquiv` for
exactly this reason; `Stacks.Cohomology.SimplicialComponent.cohomologyObjIsoExtUniv` recovers an
honest iso only because it crosses the gap and comes back, landing at the universe it started
from.

**The columns `p > 0`.**  Tag 07A0 is `Ext` out of the *free abelian* sheaf `ℤ_K`, which is
`j_!` of the *unit* coefficient sheaf (`Stacks.Cohomology.SheafOfSets.extensionByZeroUnitIso`).
The term `K^p` of the Koszul complex is instead `j_!` of the *sign twist*: it is the twist
`ℤ(χ_p)` of `W_p` by `AlgebraicGeometry.Space.SpacesEtale.isIso_signTwistToKoszul`, which is
[Stacks, Tag 0726].  Those columns are therefore not read through this file but through the
quotient `U_p` as an object of the spaces-étale site of `X`,
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientObject`, by
`AlgebraicGeometry.Space.SpacesEtale.nonempty_zExtKoszulSignTwistAddEquiv`.

## References

* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SheafOfSets

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **[Stacks, Tag 07A0] on the spaces-étale site of an algebraic space, as an additive
equivalence**, in the `Abelian.zExt` spelling in which the first page of [Stacks, Tag 0728] is
stated: `Ext^p(ℤ_K, ℱ)` is the cohomology of the site of elements of the sheaf of sets `K` with
coefficients in the restriction of `ℱ`.

The comparison itself is `Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`, which applies to
the spaces-étale site with nothing re-seated.  It lands at `Ext` in the morphism universe
`u + 1` of the sheaf category, while the first page of Tag 0728 is at the universe `u + 2` of
`CategoryTheory.HasDerivedCategory.standard`.  Mathlib has
`CategoryTheory.Abelian.Ext.chgUniv` only as an `Equiv`, but that `Equiv` is additive and the
upgrade is `Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv`; so the universe gap is
crossed here additively and not merely as a bijection.  The remaining step is
`CategoryTheory.Abelian.Ext.homAddEquiv`, which is the `zExt` spelling itself. -/
def zExtFreeAbelianSheafOnAddEquiv
    (K : Sheaf (topology B S hS X) (Type (u + 1)))
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Abelian.zExt (freeAbelianSheafOn (topology B S hS X) K) F (p : ℤ) ≃+
      Sheaf.H.{u + 1, u + 1} ((inverseImage (topology B S hS X) K).obj F) p :=
  let e1 : Abelian.Ext.{u + 2} (freeAbelianSheafOn (topology B S hS X) K) F p ≃+
      Abelian.zExt (freeAbelianSheafOn (topology B S hS X) K) F (p : ℤ) :=
    Abelian.Ext.homAddEquiv
  let e2 : Abelian.Ext.{u + 2} (freeAbelianSheafOn (topology B S hS X) K) F p ≃+
      Abelian.Ext.{u + 1} (freeAbelianSheafOn (topology B S hS X) K) F p :=
    Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
  let e3 : Abelian.Ext.{u + 1} (freeAbelianSheafOn (topology B S hS X) K) F p ≃+
      Sheaf.H.{u + 1, u + 1} ((inverseImage (topology B S hS X) K).obj F) p :=
    ((cohomologyOnSheafIso (topology B S hS X) K p).app F).addCommGroupIsoToAddEquiv
  e1.symm.trans (e2.trans e3)

/-- **The vanishing form of [Stacks, Tag 07A0] on the spaces-étale site of an algebraic space**,
in the `Abelian.zExt` spelling in which the first page of [Stacks, Tag 0728] is stated.  If the
cohomology of the site of elements of a sheaf of sets `K` with coefficients in the restriction of
`ℱ` vanishes in degree `p`, then so does `Ext^p(ℤ_K, ℱ)`, the `Ext` out of the free abelian sheaf
on `K`.

This is read off from
`AlgebraicGeometry.Space.SpacesEtale.zExtFreeAbelianSheafOnAddEquiv`, and is kept because the
row hypothesis of [Stacks, Tag 072B] is stated in this shape. -/
theorem isZero_zExt_freeAbelianSheafOn_of_subsingleton_sheafH
    (K : Sheaf (topology B S hS X) (Type (u + 1)))
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : Subsingleton
      (Sheaf.H.{u + 1, u + 1} ((inverseImage (topology B S hS X) K).obj F) p)) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt (freeAbelianSheafOn (topology B S hS X) K) F (p : ℤ))) := by
  have : Subsingleton
      (Abelian.zExt (freeAbelianSheafOn (topology B S hS X) K) F (p : ℤ)) :=
    (zExtFreeAbelianSheafOnAddEquiv B S hS X K F p).toEquiv.subsingleton_congr.mpr h
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.Space.SpacesEtale

end
