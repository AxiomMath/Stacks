module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite

/-!
# The Comparison Lemma for modules on the site of the charts of the members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be an étale covering of
`X`, for instance a Zariski covering.  The charts of the members of the covering form a site,
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`, cover dense in the small étale site of
`X`; restriction of `𝒪_X`-modules to it,
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestriction`, is fully faithful by the
Comparison Lemma for sheaves of modules.

This file supplies the remaining half: that restriction is an **equivalence**.  By
`Stacks.DenseSubsiteModules.essSurj_moduleRestriction` the only thing missing is the Comparison
Lemma for sheaves of abelian groups on this pair of sites, and Mathlib supplies that as soon as
the categories `StructuredArrow W (memberFunctor).op` admit limits in `AddCommGrpCat`.  They do,
because the site of the charts of the members is **essentially small**: the functor to the small
étale site of `X` is an induced-category functor, hence fully faithful, and the small étale site
of an algebraic space is essentially small.  Note that this holds for an arbitrary index type
`I : Type v`, even though the objects of the site then live in `Type (max (u + 1) v)`: a member
chart and a chart of another member are isomorphic in the site exactly when the induced charts of
`X` are, so the index does not enlarge the skeleton.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.essentiallySmall_memberSite_anyIndex`: **the
  site of the charts of the members is essentially small.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.essSurj_memberRestriction_anyIndex` and
  `.isEquivalence_memberRestriction_anyIndex`: **restriction of `𝒪_X`-modules to the charts
  of the members is essentially surjective, hence an equivalence.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestrictionEquivalence`: the
  equivalence itself, and `.isCoverDense_memberFunctor_of_isZariskiCovering` the cover density
  that a Zariski covering supplies for it.

  The `_anyIndex` suffixes are a remnant and nothing now depends on them.  They were what
  distinguished these results from same-named ones in
  `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteModel.lean`, which stated
  them for an index type `I : Type u` in the universe of the schemes of the big fppf site, where
  this file states them for `I : Type v` -- an index type in any universe, which is what the
  consumers of Stacks 04W6 in this development need.

  Those pairs were two declarations of one statement, and a scanner that hashes the printed
  statement could not tell them apart: the index type is bound in each file's `variable` block
  (`{I : Type u}` at `MemberSiteModel.lean:96` against `{I : Type v}` at line 85 below), so it is
  outside the hashed text while being exactly what the statements differ in.  Both have now been
  merged onto the universe-general declarations here, and `MemberSiteModel` imports them -- which
  is why the equivalence below carries the plain name `.memberRestrictionEquivalence` rather than
  a suffix.  The `Type u` forms could not have been the survivors: the equivalence at `Type u`
  yields `Equivalence.{u+1, u+1, u+1, u+1}` where
  `Equivalence.{u+1, max (u+1) v, u+1, max (max (u+1) v) u}` is required, so keeping it would have
  narrowed the index universe and left Stacks 04W6 unable to use it.

  `.essentiallySmall_memberSite_anyIndex` keeps its suffix only because renaming it would churn
  its call sites for nothing; it too is now the only declaration of its statement.  Merging it
  meant deleting a small model of the site that `MemberSiteModel` built to prove the `Type u`
  instance -- an index type `Σ i : I, SmallModel ...`, the induced category on the charts it
  names, and the comparison functor.  That was safe to delete rather than a design loss: none of
  its five declarations had a consumer outside its own file, so it existed only to support the
  duplicate instance.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_of_essSurj`: a descent datum
  relative to an étale family is effective as soon as the canonical descent functor of the family
  is essentially surjective.  This is the effectivity clause of Stacks 04W6 reduced to essential
  surjectivity; the clause itself is not proved here.

## Implementation notes

`Stacks.DenseSubsiteModules.essSurj_moduleRestriction` takes the topologies, the functor and the
ring sheaf implicitly, so they are passed by name.

The equivalence is stated inside a section assuming cover density rather than taking a covering
as an argument, because its target `AlgebraicGeometry.Space.QuasiCoherentDescent.memberRing`
cannot be written down before that assumption is in scope; a consumer holding a covering gets
the assumption from
`AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_memberFunctor_of_isZariskiCovering`.

`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` is a lemma rather than an instance,
so the limits of the structured-arrow categories are registered here as an instance; with it
instance search finds the Comparison Lemma for sheaves of abelian groups, and hence essential
surjectivity, on its own.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### Essential smallness -/

/-- **The site of the charts of the members of a family of algebraic spaces étale over `X` is
essentially small.**  Its functor to the small étale site of `X` is the functor of an induced
category, hence fully faithful, and the small étale site of an algebraic space is essentially
small. -/
instance essentiallySmall_memberSite_anyIndex : EssentiallySmall.{u} (MemberSite B S hS Yi f hf) :=
  essentiallySmall_of_fully_faithful (memberFunctor B S hS Yi f hf)

/-- The diagrams over which the Comparison Lemma for sheaves of abelian groups on the charts of
the members takes limits are essentially small, so those limits exist. -/
instance hasLimitsOfShape_structuredArrow_memberFunctor_anyIndex (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (memberFunctor B S hS Yi f hf).op) AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-! ### The equivalence -/

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **Restriction of `𝒪_X`-modules to the site of the charts of the members is essentially
surjective**, by the Comparison Lemma for sheaves of modules: every sheaf of modules on that
site is the restriction of an `𝒪_X`-module. -/
theorem essSurj_memberRestriction_anyIndex : (memberRestriction B S hS Yi f hf).EssSurj :=
  Stacks.DenseSubsiteModules.essSurj_moduleRestriction
    (J := memberTopology B S hS Yi f hf) (K := SmallEtale.topology B S hS X.1)
    (v := memberFunctor B S hS Yi f hf)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **Restriction of `𝒪_X`-modules to the site of the charts of the members is an
equivalence.**  Full faithfulness is `.full_memberRestriction` together with the Comparison
Lemma, and essential surjectivity is
`AlgebraicGeometry.Space.QuasiCoherentDescent.essSurj_memberRestriction_anyIndex`. -/
theorem isEquivalence_memberRestriction_anyIndex :
    (memberRestriction B S hS Yi f hf).IsEquivalence :=
  Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction
    (J := memberTopology B S hS Yi f hf) (K := SmallEtale.topology B S hS X.1)
    (v := memberFunctor B S hS Yi f hf)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **The `𝒪_X`-modules are the modules on the site of the charts of the members.** -/
def memberRestrictionEquivalence :
    Modules.{u, u} B S hS X.1 X.2 ≌ SheafOfModules.{u} (memberRing B S hS Yi f hf) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (memberTopology B S hS Yi f hf)
    (SmallEtale.topology B S hS X.1) (memberFunctor B S hS Yi f hf)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- The equivalence of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestrictionEquivalence` is
restriction. -/
theorem memberRestrictionEquivalence_functor :
    (memberRestrictionEquivalence B S hS Yi f hf).functor =
      memberRestriction B S hS Yi f hf :=
  rfl

end CoverDense

/-! ### The equivalence for a covering -/

/-- **The charts of the members of a Zariski covering are cover dense in the small étale site of
`X`**, a Zariski covering being an étale covering by Stacks 0DF1. -/
theorem isCoverDense_memberFunctor_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1) :=
  isCoverDense_memberFunctor B S hS Yi f hf
    (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov)

/-! ### Effectivity reduced to essential surjectivity -/

/-- **A descent datum relative to a family of algebraic spaces étale over `X` is effective as
soon as the canonical descent functor of the family is essentially surjective.**  This is the
effectivity clause of Stacks 04W6 reduced to essential surjectivity of the functor whose full
faithfulness is the other clause; the effectivity clause itself is not proved here. -/
theorem isEtaleEffective_of_essSurj
    (hess : (etaleCanonicalDescentFunctor B S hS Yi f hf).EssSurj)
    (D : DescentDatum B S hS Yi f) : IsEtaleEffective B S hS Yi f hf D :=
  (isEtaleEffective_iff_essImage B S hS Yi f hf D).2 (hess.mem_essImage D)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
