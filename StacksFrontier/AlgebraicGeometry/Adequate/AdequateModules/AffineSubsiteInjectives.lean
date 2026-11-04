module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSheafTopology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Modules.Injective
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Sheafification on the affine subsite of a chosen big site, at a free module universe

Let `U = Spec A` be affine and let `B` be a chosen big `τ`-site over `U`. The `A`-algebras of
the site are a dense subsite of `B`, which is `Stacks.Adequate.affineSpecOver_isDenseSubsite`,
[Stacks, Tag 021V] and its four analogues. This file supplies, at a module universe independent
of the universe `u` of the site, the standing inputs that the Comparison Lemma for sheaves of
modules and [Stacks, Tag 03FB] ask for on that subsite, together with the consequence for the
forgetful functor to presheaves of modules.

Each one is a consequence of essential smallness of the `A`-algebras of the site,
`AdequateFunctor.essentiallySmall_algebraInSite`: the subsite is essentially small at `u`, hence
at every universe above `u`, and sheafification, the identification of its weak equivalences
with the locally bijective maps, and the Comparison Lemma for abelian sheaves all transport from
a small model. The pattern is the one already used for the big site itself in
`Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat` and its two companions.

## Main results

* `Stacks.Adequate.essentiallySmall_affineSubsite` and
  `Stacks.Adequate.essentiallySmall_affineSubsite_max` — the `A`-algebras of the site form an
  essentially small category, at `u` and at every universe above `u`.
* `Stacks.Adequate.hasSheafify_affineSubsiteTopology` — abelian presheaves on the affine subsite
  admit sheafification.
* `Stacks.Adequate.wEqualsLocallyBijective_affineSubsiteTopology` — that sheafification inverts
  exactly the locally bijective maps.
* `Stacks.Adequate.isEquivalence_affineSheafPushforwardContinuous` — **the Comparison Lemma for
  abelian sheaves on the affine subsite**: restriction of abelian sheaves along the
  affine-spectrum functor is an equivalence of categories.
* `Stacks.Adequate.preservesInjectiveObjects_forget_affineAlgebraRingSheaf` —
  [Stacks, Tag 03FB] on the affine subsite: the forgetful functor from sheaves of modules there
  to presheaves of modules preserves injective objects.

## Implementation notes

These are theorems rather than instances, so that instance selection elsewhere in the library is
unchanged; a consumer introduces the ones it needs with `haveI`.

The module universe is written `max u m` throughout, which is the generality in which
[Stacks, Tag 06ZU] is stated: the limit shapes needed for the Comparison Lemma are the
structured-arrow categories of the affine-spectrum functor, and those are essentially small at
`u` alone, so `u`-smallness is what produces limits in abelian groups at any universe above `u`.

## References

* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 03FB](https://stacks.math.columbia.edu/tag/03FB)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The `A`-algebras of a chosen big site over `Spec A` form an essentially small category: such
an algebra has cardinality below the cutoff, so it is isomorphic to one carried by a subset of a
fixed type of that cardinality. -/
public theorem essentiallySmall_affineSubsite :
    EssentiallySmall.{u} (AdequateFunctor.AlgebrasInSite (A : Type u)
      (schemeSizeBelow B.cutoff)) :=
  have := AdequateFunctor.essentiallySmall_algebraInSite (A : Type u) B.cutoff
  inferInstance

/-- The `A`-algebras of a chosen big site over `Spec A` are essentially small at every universe
above the universe of the site, a small model at `u` lifting to one at `max u m`. -/
public theorem essentiallySmall_affineSubsite_max :
    EssentiallySmall.{max u m} (AdequateFunctor.AlgebrasInSite (A : Type u)
      (schemeSizeBelow B.cutoff)) := by
  have := essentiallySmall_affineSubsite B
  rw [essentiallySmall_iff]
  exact ⟨small_lift _, inferInstance⟩

/-- **Abelian presheaves on the affine subsite admit sheafification**, at every coefficient
universe above the universe of the site: the subsite is essentially small, so sheafification
transports from a small model. -/
public theorem hasSheafify_affineSubsiteTopology :
    HasSheafify (affineSubsiteTopology B) AddCommGrpCat.{max u m} :=
  have := essentiallySmall_affineSubsite_max.{u, m} B
  hasSheafifyEssentiallySmallSite _ _

/-- **Sheafification of abelian presheaves on the affine subsite inverts exactly the locally
bijective maps**, at every coefficient universe above the universe of the site: this holds on a
small model of the subsite and transports along the dense inclusion of that model. -/
public theorem wEqualsLocallyBijective_affineSubsiteTopology :
    (affineSubsiteTopology B).WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
  have := essentiallySmall_affineSubsite_max.{u, m} B
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _, max u m}
    (affineSubsiteTopology B)

/-- **The Comparison Lemma for abelian sheaves on the affine subsite**, at every coefficient
universe above the universe of the site. The `A`-algebras of the site are a dense subsite, and
the limits the comparison needs are over the structured-arrow categories of the affine-spectrum
functor, which are essentially small at the universe of the site itself. -/
public theorem isEquivalence_affineSheafPushforwardContinuous :
    ((affineSpecOver B A (𝟙 (Spec A))).sheafPushforwardContinuous
      AddCommGrpCat.{max u m} (affineSubsiteTopology B) B.topology).IsEquivalence :=
  have := AdequateFunctor.essentiallySmall_algebraInSite (A : Type u) B.cutoff
  have : ∀ X : (B.category)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (affineSpecOver B A (𝟙 (Spec A))).op) AddCommGrpCat.{max u m} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  inferInstance

/-- **[Stacks, Tag 03FB] on the affine subsite.** The forgetful functor from sheaves of modules
over the tautological sheaf of rings on the `A`-algebras of the site to presheaves of modules
preserves injective objects, because sheafification of presheaves of modules there is an exact
left adjoint of it. -/
public theorem preservesInjectiveObjects_forget_affineAlgebraRingSheaf :
    (SheafOfModules.forget.{max u m} (affineAlgebraRingSheaf B)).PreservesInjectiveObjects :=
  have := hasSheafify_affineSubsiteTopology.{u, m} B
  have := wEqualsLocallyBijective_affineSubsiteTopology.{u, m} B
  SheafOfModules.forget_preservesInjectiveObjects

end Stacks.Adequate

end
