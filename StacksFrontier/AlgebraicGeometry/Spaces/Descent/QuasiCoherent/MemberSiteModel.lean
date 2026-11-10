module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteComparison

/-!
# The Comparison Lemma for modules on the charts of an étale covering

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be an étale covering.
The charts of the members form the site
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`, cover dense in the small étale site of
`X` by `AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_memberFunctor`.  Cover density
alone gives that restriction of `𝒪_X`-modules to that site is **full**.

Here the restriction is shown to be an **equivalence**.  By
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` that needs two further inputs, and both
are supplied here with no hypothesis beyond the covering:

* the dense-subsite condition, which follows from cover density because
  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor` is an
  `CategoryTheory.inducedFunctor` and so fully faithful, and because the topology on the charts
  of the members is by definition the restricted one;
* the Comparison Lemma for sheaves of abelian groups, which needs limits of `AddCommGrpCat.{u}`
  over the comma categories of `memberFunctor`.  Those are limits of shape a category one
  universe above the coefficients, so the input is a *size* condition, and it is met because the
  site of the charts of the members is essentially small —
  `AlgebraicGeometry.Space.QuasiCoherentDescent.essentiallySmall_memberSite_anyIndex`, imported
  from `MemberSiteComparison`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.hasLimitsOfShape_structuredArrow_memberFunctor`:
  the size input of the Comparison Lemma — limits over the comma categories of `memberFunctor`
  exist in any category with limits whose morphisms lie one universe below its objects.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEquivalence_memberRestriction` and
  `.essSurj_memberRestriction`: restriction of `𝒪_X`-modules to the charts of the members is an
  equivalence, and in particular essentially surjective.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEquivalence_memberRestriction_of_isEtaleCovering`:
  the same with the cover density supplied by the covering rather than assumed.

The equivalence is the backbone of the converse direction of Stacks 03M3: an `𝒪_X`-module is
then *the same thing* as a module on the charts of the members, and for the one-member covering
`{φ : U ⟶ X}` of Stacks 03M3 the objects of that site are the charts of `U` and its morphisms
are the morphisms of the induced charts of `X`, that is the arrows of `R = U ×_X U`.  So a
quasi-coherent module on the groupoid `(U, R, s, t, c)` gives an `𝒪_X`-module as soon as its
transition morphism is read on sections.

## Implementation notes

The model is built as a `CategoryTheory.InducedCategory` **over the site of the charts of the
members itself**, not as a sigma of the small models of the members.  The morphisms of that site
are the morphisms of the *induced charts of `X`*, not of the charts of a member, so a sigma of
the members' models would have to compare two different hom types; as an induced category the
comparison is the identity on morphisms and is fully faithful by
`CategoryTheory.fullyFaithfulInducedFunctor`, with nothing to prove.

Essential surjectivity of the comparison is the only step that uses the small models: a chart of
a member is isomorphic to one coming from the model of that member, and
`AlgebraicGeometry.Space.smallEtalePostcomp` carries that isomorphism to an isomorphism of the
induced charts of `X`, which — again by full faithfulness of the induced functor — is an
isomorphism of the site of the charts of the members.

The three instances of the Comparison Lemma are taken from
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` rather than synthesized at
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberRestriction`: that abbreviation fixes the
module universe through `AlgebraicGeometry.Space.Modules`, and elaborating the instances at the
unfolded `Stacks.DenseSubsiteModules.moduleRestriction` instead leaves the universe of the sheaf
of modules open, where it defaults one universe too high.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The size input of the Comparison Lemma -/

/-- Limits over the comma categories of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor` exist in any category with limits
whose morphisms lie one universe below its objects.  This is the size input of the Comparison
Lemma for sheaves of abelian groups, and it holds because the site of the charts of the members
is essentially small. -/
instance hasLimitsOfShape_structuredArrow_memberFunctor
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (A : Type (u + 1)) [Category.{u} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (memberFunctor B S hS Yi f hf).op) A :=
  have : EssentiallySmall.{u} (StructuredArrow W (memberFunctor B S hS Yi f hf).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-! ### The Comparison Lemma -/

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- **Restriction of `𝒪_X`-modules to the charts of the members is an equivalence.** -/
instance isEquivalence_memberRestriction :
    (memberRestriction B S hS Yi f hf).IsEquivalence :=
  (memberRestrictionEquivalence B S hS Yi f hf).isEquivalence_functor

/-- Restriction of `𝒪_X`-modules to the charts of the members is essentially surjective: every
module on the charts of the members comes from an `𝒪_X`-module. -/
instance essSurj_memberRestriction :
    (memberRestriction B S hS Yi f hf).EssSurj :=
  inferInstance

end CoverDense

/-- **Restriction to the charts of an étale covering is an equivalence**, with the cover density
supplied by the covering rather than assumed. -/
theorem isEquivalence_memberRestriction_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    haveI := isCoverDense_memberFunctor B S hS Yi f hf hcov
    (memberRestriction B S hS Yi f hf).IsEquivalence :=
  have := isCoverDense_memberFunctor B S hS Yi f hf hcov
  isEquivalence_memberRestriction B S hS Yi f hf

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
