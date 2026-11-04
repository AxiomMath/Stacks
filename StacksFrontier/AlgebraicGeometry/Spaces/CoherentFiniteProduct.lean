module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# A finite product of coherent modules is coherent

Stacks 01BY (3) asserts that a finite direct sum of coherent sheaves of modules is coherent.
On a site that is `Stacks.SheafOfModules.isCoherentOnSite_sigma`, stated for the *coproduct*
`∐`.  This file states the same for the *product* `∏ᶜ` and for the biproduct `⨁`, which for a
finite family in an additive category are the same object, and transports the result to
coherence of a module on an algebraic space,
`AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_pi` and
  `Stacks.SheafOfModules.isCoherentOnSite_biproduct`: **a product, respectively a biproduct, of
  finitely many coherent sheaves of modules on a site is coherent.**
* `AlgebraicGeometry.Space.isCoherent_pi` and
  `AlgebraicGeometry.Space.isCoherent_biproduct`: **a finite product, respectively a finite
  biproduct, of coherent modules on an algebraic space is coherent.**
* `AlgebraicGeometry.Space.isCoherent_piConst` and
  `AlgebraicGeometry.Space.isCoherent_biproductConst`: the case of `n` copies of one coherent
  module, which is the shape `(i_*ℐ)^{⊕ r}` in which Stacks 07UQ hands its source to the
  dévissage of Stacks 08AN.

## Implementation notes

**The family is arbitrary, not constant.**  Nothing in the argument sees the summands as
copies of one module — `Stacks.SheafOfModules.isCoherentOnSite_of_split`, which runs the
induction behind `Stacks.SheafOfModules.isCoherentOnSite_sigma`, takes two different sheaves
of modules — so the general family costs nothing and the constant case is a corollary.

**No `Fin (n + 1)` decomposition of a biproduct is used, and Mathlib has none.**  The
induction over the index type was already performed, for the coproduct, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteCoherenceFiniteFamilies.lean`, where the
splitting of `∐_{Fin (n+1)} M` into its zeroth summand and the coproduct of the others is
written out with `Fin.cases` and no reindexing isomorphism.  What is added here is only the
exchange between the three ways of writing a finite direct sum, which is Mathlib's
`CategoryTheory.Limits.biproduct.isoCoproduct` and
`CategoryTheory.Limits.biproduct.isoProduct` composed; the biproduct of the family exists
because the product does, by
`CategoryTheory.Limits.HasBiproduct.of_hasProduct` in the preadditive category of sheaves of
modules.

**Why the product form is needed at all.**  Products of sheaves of modules exist
unconditionally, while the coproduct needs sheafification of presheaves of abelian groups;
more to the point, consumers write a finite direct sum as `∏ᶜ` or as `⨁` rather than as `∐`,
and the two conclusions below are what they can apply.  Quasi-coherence of a finite product is
already available unconditionally, as
`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`; coherence on the site was
the missing half, and once it is in hand
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite` supplies the whole of Stacks 07UA
with no quasi-coherence input.

**The existence of the direct sum is an instance binder in the general statements and is
synthesized in the constant ones.**  The index type of the general statements lies in an
arbitrary universe, where `CategoryTheory.Limits.HasProduct` and
`CategoryTheory.Limits.HasBiproduct` need not be synthesizable — the finite limits of a
category of sheaves of modules are indexed by types in `Type 0` — so they are taken as
instance binders, which keeps those statements applicable to a goal whose direct sum was
formed with the ambient instance.  At the index type `Fin n` of the constant statements both
classes *are* found by instance search, so no binder is written there.  Both are
`Prop`-valued, so a mismatch between a binder's instance and the ambient one cannot change
the object either statement is about.

No tag attribute is carried: the direct-sum clause of Stacks 01BY (3) on a site is already
registered on `Stacks.SheafOfModules.isCoherentOnSite_sigma`, and Stacks 07UA on
`AlgebraicGeometry.Space.IsCoherent`; the statements below are those two composed with an
isomorphism.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace Stacks.SheafOfModules

variable {C : Type t} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 01BY (3), for a finite product, on a site.**  A product of finitely
many coherent sheaves of modules on a site is coherent.

For a finite family in a preadditive category the product, the coproduct and the biproduct
agree; the coproduct case is `Stacks.SheafOfModules.isCoherentOnSite_sigma`, and the two
comparisons are `CategoryTheory.Limits.biproduct.isoCoproduct` and
`CategoryTheory.Limits.biproduct.isoProduct`. -/
theorem isCoherentOnSite_pi {I : Type*} [Finite I] (M : I → SheafOfModules.{w} R)
    [HasProduct M] (hM : ∀ i, SheafOfModules.IsCoherentOnSite (M i)) :
    SheafOfModules.IsCoherentOnSite (∏ᶜ M) :=
  have : HasBiproduct M := HasBiproduct.of_hasProduct M
  isCoherentOnSite_of_iso (biproduct.isoProduct M)
    (isCoherentOnSite_of_iso (biproduct.isoCoproduct M).symm (isCoherentOnSite_sigma M hM))

/-- **Stacks Project, Tag 01BY (3), for a finite biproduct, on a site.**  A biproduct of
finitely many coherent sheaves of modules on a site is coherent.  This is
`Stacks.SheafOfModules.isCoherentOnSite_pi` read through
`CategoryTheory.Limits.biproduct.isoProduct`. -/
theorem isCoherentOnSite_biproduct {I : Type*} [Finite I] (M : I → SheafOfModules.{w} R)
    [HasBiproduct M] (hM : ∀ i, SheafOfModules.IsCoherentOnSite (M i)) :
    SheafOfModules.IsCoherentOnSite (⨁ M) :=
  isCoherentOnSite_of_iso (biproduct.isoProduct M).symm (isCoherentOnSite_pi M hM)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A finite product of coherent modules on an algebraic space is coherent**, for the
predicate `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.

Coherence on the small étale ringed site is `Stacks.SheafOfModules.isCoherentOnSite_pi`, and
the quasi-coherence clause of Stacks 07UA needs no separate argument: it follows from
coherence on the site, by `AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`. -/
theorem isCoherent_pi {I : Type*} [Finite I] (M : I → Modules.{u, u} B S hS F hF)
    [HasProduct M] (hM : ∀ i, IsCoherent B S hS F hF (M i)) :
    IsCoherent B S hS F hF (∏ᶜ M) :=
  have : SheafOfModules.IsCoherentOnSite (∏ᶜ M) :=
    Stacks.SheafOfModules.isCoherentOnSite_pi M fun i => (hM i).toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF (∏ᶜ M)

/-- **A finite biproduct of coherent modules on an algebraic space is coherent**, for the
predicate `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.

This is `AlgebraicGeometry.Space.isCoherent_pi` transported along
`CategoryTheory.Limits.biproduct.isoProduct`, the identification of the biproduct of a finite
family with its product. -/
theorem isCoherent_biproduct {I : Type*} [Finite I] (M : I → Modules.{u, u} B S hS F hF)
    [HasBiproduct M] (hM : ∀ i, IsCoherent B S hS F hF (M i)) :
    IsCoherent B S hS F hF (⨁ M) :=
  have : SheafOfModules.IsCoherentOnSite (⨁ M) :=
    Stacks.SheafOfModules.isCoherentOnSite_biproduct M fun i => (hM i).toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF (⨁ M)

/-- **A finite product of copies of a coherent module on an algebraic space is coherent.**
This is the shape `ℐ^{⊕ r}` in which Stacks 07UQ writes the source of its injection. -/
theorem isCoherent_piConst (M : Modules.{u, u} B S hS F hF) (hM : IsCoherent B S hS F hF M)
    (n : ℕ) :
    IsCoherent B S hS F hF (∏ᶜ fun _ : Fin n => M) :=
  isCoherent_pi B S hS F hF (fun _ : Fin n => M) fun _ => hM

/-- **A finite biproduct of copies of a coherent module on an algebraic space is coherent.**
This is the shape `(i_*ℐ)^{⊕ r}` in which the dévissage of Stacks 08AN consumes the injection
of Stacks 07UQ. -/
theorem isCoherent_biproductConst (M : Modules.{u, u} B S hS F hF)
    (hM : IsCoherent B S hS F hF M) (n : ℕ) :
    IsCoherent B S hS F hF (⨁ fun _ : Fin n => M) :=
  isCoherent_biproduct B S hS F hF (fun _ : Fin n => M) fun _ => hM

end AlgebraicGeometry.Space

end
