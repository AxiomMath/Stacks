module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpaceNonAbelianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf

/-!
# The formal completion of `Spec ℤ` at `p`, and the two halves of Stacks 0ALG

Stacks, Section 110.13 argues that quasi-coherent modules on a formal algebraic space need not
form an abelian category by taking `X = Spf(ℤ_p)`, identifying `QCoh(𝒪_X)` with the
`p`-adically complete abelian groups, and quoting the non-abelianness of the latter.  The
argument therefore has two halves: the *exhibition* of the space, and the *identification* of
its quasi-coherent modules.  This file supplies the first half for the source's own choice of
space and records what the second half still needs.

The space is `Spf(ℤ_p)` in the form the library builds it: the completion of `Spec ℤ` along the
closed subscheme cut out by `(p)`, that is the fppf-sheaf colimit of the spectra of the rings
`ℤ ⧸ p ^ (n + 1)`.  By Stacks 0GXX (2), recorded here as
`AlgebraicGeometry.FormalSpace.nonempty_iso_formalSpectrum_spfPadic`, this colimit is the
formal spectrum of the `(p)`-adic completion of `ℤ`, so it is `Spf(ℤ_p)` and not merely
something resembling it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.intSite`: a big fppf site containing `Spec ℤ`, taken over
  `Spec ℤ` as the base scheme.
* `AlgebraicGeometry.FormalSpace.spfPadic`: the completion of `Spec ℤ` along `(p)`.
* `AlgebraicGeometry.FormalSpace.spfPadicFibred`: the category fibred in groupoids attached to
  that sheaf of sets, and `AlgebraicGeometry.FormalSpace.spfPadicProjection` its structure
  functor to the big fppf category over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_spfPadic`,
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_spfPadic` and
  `AlgebraicGeometry.FormalSpace.isNoetherian_spfPadic`: `Spf(ℤ_p)` is a Noetherian affine
  formal algebraic space, and a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.nonempty_iso_formalSpectrum_spfPadic`: that space is the
  formal spectrum of the `(p)`-adic completion of `ℤ`.
* `AlgebraicGeometry.FormalSpace.exists_isNoetherian_isAffineFormalAlgebraicSpace`: there is a
  Noetherian affine formal algebraic space, over a big fppf site exhibited together with it.
* `AlgebraicGeometry.FormalSpace.isFiberedInGroupoids_spfPadicProjection`: the attached
  category is fibred in groupoids, so its category of quasi-coherent modules is defined.
* `AlgebraicGeometry.FormalSpace.not_abelian_quasicoherentModules_spfPadic_of_equivalence`:
  the quasi-coherent modules on that category are not abelian as soon as they are identified
  with a category of adically complete modules of the kind Stacks 07JR rules out.

## What Stacks 0ALG still needs

Stacks 0ALG is the assertion that there *is* a Noetherian affine formal algebraic space whose
quasi-coherent modules are not abelian.  Of its two halves, the exhibition is complete here:
`spfPadic p` is the source's space, and the three predicates of Stacks 0AI7, 0AIM and 0AID (5)
hold of it unconditionally.  No declaration in this file carries the tag, because the
identification is missing, and with it the only step that could produce the non-abelianness.

What is missing is precisely an equivalence

`FibredSite.quasicoherentModules intSite _ _ (spfPadicProjection p) _ ≌`
`  Stacks.Examples.IAdicallyCompleteModuleCat (AdicCompletion (Ideal.span {p}) ℤ) _`

and `not_abelian_quasicoherentModules_spfPadic_of_equivalence` is the statement that such an
equivalence finishes Stacks 0ALG for this space.  Its module-theoretic half is available and
its geometric half is not.

* **Available: the module-theoretic half.**  The passage between adically complete modules and
  inverse systems of adic quotients is
  `Stacks.Examples.iAdicallyCompleteModuleCatEquivAdicModuleSystems` in
  `StacksFrontier/Examples/Completion/CompleteModulesEquivAdicSystems.lean`, an equivalence
  `IAdicallyCompleteModuleCat R I ≌ AdicModuleSystems I` for every commutative ring `R` and
  every finitely generated `I`, and `Stacks.Examples.AdicTower.limitEquivalence` in
  `StacksFrontier/Examples/Completion/AdicTowerEquivalence.lean` is the same passage for adic
  towers.  These are the categorical form of Stacks 09B8, whose ring-theoretic half is
  `Stacks.AdicCompletion.InverseLimit.InverseSystem.quotientEquiv` and
  `Stacks.AdicCompletion.InverseLimit.InverseSystem.isAdicComplete` in
  `StacksFrontier/RingTheory/AdicCompletion/InverseLimit.lean`.  So the remaining gap is exactly
  the geometric statement `QCoh(Spf(ℤ_p)) ≌ AdicModuleSystems (p)`, which is the shape the
  source's own derivation produces.
* **Not available: the geometric half.**  That statement is the description of a quasi-coherent
  module on `colim Spec (ℤ ⧸ p ^ (n + 1))` by the system of its restrictions to the stages,
  which is Stacks 06WK read on the fibred category of a sheaf of sets together with
  Stacks 0GQD on each stage.  Of Stacks 06WK only the étale sheaf condition of clause (1) in
  the forward direction is proved, as
  `AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherent` in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentEtaleSheafClause.lean`;
  that conjunct is a sheaf condition and says nothing about the restrictions, so it supplies
  no part of the description.  Stacks 0GQD is only a reduction to two hypotheses,
  `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction` in
  `StacksFrontier/AlgebraicGeometry/Stacks/QuasicoherentRestrictionAlgebraicSpace.lean`; the same
  absence is recorded in
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackQuasicoherentModules.lean`.
* **The one input both bottom out at.**  The residue of Stacks 06WK is
  `AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` in
  `StacksFrontier/AlgebraicGeometry/Stacks/EtaleRestrictionFunctorialComparison.lean`, which asks
  for quasi-coherence read for a coarser topology; that is the unavailable half of
  Stacks 0EM8, which at the big site of a scheme is the essential-surjectivity half of
  Descent, Proposition 03DX.  The library carries that half as the hypothesis
  `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/QuasicoherentColimitsOfSize.lean`
  and nothing discharges it.  Until it is discharged no declaration here can carry
  Stacks 0ALG: every route to the non-abelianness runs through the identification of the
  quasi-coherent modules, and knowing only that the complete modules embed in them would not
  suffice, since refuting normality of a monomorphism quantifies over *all* objects of
  `QCoh(Spf(ℤ_p))`.
* No declaration in `StacksFrontier/AlgebraicGeometry/FormalSpace/` other than the transport in
  `StacksFrontier/AlgebraicGeometry/FormalSpace/FormalSpaceNonAbelianQuasicoherent.lean` mentions
  quasi-coherent modules at all, so the geometric half has no preliminary form to build on.

## Implementation notes

`ℤ` is replaced by `ULift ℤ` so that the chart ring lives in the universe of the schemes of
the site; the two are isomorphic as rings, which is how the Noetherian hypothesis of
`AlgebraicGeometry.FormalSpace.isNoetherian_completionAlongIdeal` is met.  The base scheme is
the chart itself and the structure morphism is the identity, which is the situation of Stacks,
Section 110.13, where the site is the big fppf site over `Spec ℤ`.

A big fppf site containing `Spec ℤ` is produced by
`AlgebraicGeometry.BigFppfSite.exists_contains`; since that is an existence statement and the
later definitions must speak about one fixed site, `intSite` is its choice and
`intSite_contains` the accompanying specification.

The category fibred in groupoids attached to the sheaf of sets `X` is the one of Stacks 0049
for the presheaf of groupoids `X.obj ⋙ typeToGrpd` with discrete values, so fibredness in
groupoids is `CategoryTheory.isFiberedInGroupoids_presheafOfGroupoids`.  The library's
`CategoryTheory.PresheafOfCategories.discreteProjection` is the same construction for a
presheaf valued in the universe of the morphisms of the site; the sheaves carrying formal
algebraic spaces take values one universe higher, so it does not apply here.

## References

* [Stacks Project, Tag 0ALG](https://stacks.math.columbia.edu/tag/0ALG)
* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0049](https://stacks.math.columbia.edu/tag/0049)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u m r s

/-- The affine scheme `Spec ℤ`, with `ℤ` placed in the universe of the schemes of the site. -/
def intBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- A big fppf site containing `Spec ℤ`, chosen once and for all from
`AlgebraicGeometry.BigFppfSite.exists_contains`. -/
def intSite : BigFppfSite.{u} := (BigFppfSite.exists_contains intBase.{u}).choose

/-- The chosen big fppf site contains `Spec ℤ`. -/
theorem intSite_contains : (intSite.{u}).Contains intBase.{u} :=
  (BigFppfSite.exists_contains intBase.{u}).choose_spec

/-- `ℤ` in the universe of the schemes of the site is a Noetherian ring. -/
theorem isNoetherianRing_uliftInt : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_surjective ℤ (ULift.{u} ℤ)
    (ULift.ringEquiv.{0, u}.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom
    (ULift.ringEquiv.{0, u}.symm).surjective

/-- `Spf(ℤ_p)`: the completion of `Spec ℤ` along the closed subscheme cut out by `(p)`, that is
the fppf-sheaf colimit of the spectra of `ℤ ⧸ p ^ (n + 1)`.  For a prime `p` the `(p)`-adic
completion of `ℤ` is the ring of `p`-adic integers, and this sheaf is its formal spectrum by
Stacks 0GXX (2). -/
def spfPadic (p : ℕ) : FppfSheaf intSite.{u} intBase.{u} intSite_contains :=
  completionAlongIdeal intSite.{u} intBase.{u} intSite_contains (𝟙 _) intSite_contains
    (Ideal.span {(p : ULift.{u} ℤ)})

/-- **Stacks 0AI7** for `Spf(ℤ_p)`: it is an affine formal algebraic space over `Spec ℤ`. -/
theorem isAffineFormalAlgebraicSpace_spfPadic (p : ℕ) :
    IsAffineFormalAlgebraicSpace intSite.{u} intBase.{u} intSite_contains (spfPadic.{u} p) :=
  isAffineFormalAlgebraicSpace_completionAlongIdeal intSite.{u} intBase.{u} intSite_contains
    (𝟙 _) intSite_contains _

/-- **Stacks 0AIM** for `Spf(ℤ_p)`: it is a formal algebraic space over `Spec ℤ`, being an
affine one. -/
theorem isFormalAlgebraicSpace_spfPadic (p : ℕ) :
    IsFormalAlgebraicSpace intSite.{u} intBase.{u} intSite_contains (spfPadic.{u} p) :=
  isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace intSite.{u} intBase.{u}
    intSite_contains (isAffineFormalAlgebraicSpace_spfPadic.{u} p)

/-- **Stacks 0AID (5)** for `Spf(ℤ_p)`: it is a Noetherian affine formal algebraic space, being
the completion of the Noetherian affine scheme `Spec ℤ` along an ideal. -/
theorem isNoetherian_spfPadic (p : ℕ) :
    IsNoetherian intSite.{u} intBase.{u} intSite_contains (spfPadic.{u} p) :=
  let := isNoetherianRing_uliftInt.{u}
  isNoetherian_completionAlongIdeal intSite.{u} intBase.{u} intSite_contains (𝟙 _)
    intSite_contains _

section FormalSpectrum

attribute [local instance] adicCompletionLimitTopology isTopologicalRing_adicCompletion
  isLinearTopology_adicCompletion

/-- **Stacks 0GXX (2)** for `Spf(ℤ_p)`: the completion of `Spec ℤ` along `(p)` is the formal
spectrum of the `(p)`-adic completion of `ℤ`.  For a prime `p` that completion is the ring of
`p`-adic integers, so this is what makes `spfPadic p` the space `Spf(ℤ_p)` of Stacks,
Section 110.13 rather than merely a space resembling it. -/
theorem nonempty_iso_formalSpectrum_spfPadic (p : ℕ) :
    Nonempty (spfPadic.{u} p ≅
      formalSpectrum (adicCompletionQuotientSystem intSite.{u} intBase.{u} intSite_contains
        (𝟙 _) intSite_contains (Ideal.span {(p : ULift.{u} ℤ)}))) :=
  (isAdic_and_iso_formalSpectrum_adicCompletion intSite.{u} intBase.{u} intSite_contains
    (𝟙 _) intSite_contains _ (Submodule.fg_span (Set.finite_singleton _))).2

end FormalSpectrum

/-- There is a Noetherian affine formal algebraic space, exhibited together with the big fppf
site and the base scheme it lives over: the completion of `Spec ℤ` along `(p)`.

This is the first of the two halves of Stacks 0ALG; the second, the identification of its
quasi-coherent modules, is discussed in the module docstring. -/
theorem exists_isNoetherian_isAffineFormalAlgebraicSpace :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧ IsFormalAlgebraicSpace B S hS X ∧
        IsNoetherian B S hS X :=
  ⟨intSite.{u}, intBase.{u}, intSite_contains, spfPadic.{u} 2,
    isAffineFormalAlgebraicSpace_spfPadic.{u} 2, isFormalAlgebraicSpace_spfPadic.{u} 2,
    isNoetherian_spfPadic.{u} 2⟩

/-- The category fibred in groupoids attached to the sheaf of sets `Spf(ℤ_p)`: the category of
Stacks 0049 for the presheaf of groupoids with discrete values `X.obj ⋙ typeToGrpd`. -/
def spfPadicFibred (p : ℕ) :
    BasedCategory (BigFppfOver intSite.{u} intBase.{u} intSite_contains) :=
  presheafOfGroupoids ((spfPadic.{u} p).obj ⋙ typeToGrpd)

/-- The structure functor of the category fibred in groupoids attached to `Spf(ℤ_p)`. -/
abbrev spfPadicProjection (p : ℕ) :
    (spfPadicFibred.{u} p).obj ⥤ BigFppfOver intSite.{u} intBase.{u} intSite_contains :=
  (spfPadicFibred.{u} p).p

/-- **Stacks 0049** for `Spf(ℤ_p)`: the attached category is fibred in groupoids over the big
fppf category of schemes over `Spec ℤ`, so its category of quasi-coherent modules is defined. -/
theorem isFiberedInGroupoids_spfPadicProjection (p : ℕ) :
    (spfPadicProjection.{u} p).IsFiberedInGroupoids :=
  isFiberedInGroupoids_presheafOfGroupoids _

/-- The quasi-coherent modules on `Spf(ℤ_p)` are not abelian as soon as they are equivalent to
the category of `I`-adically complete `R`-modules for a Noetherian domain `R` which is complete
for a principal ideal `I = (π)` with `π` neither zero nor a unit.

Together with `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_spfPadic`,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_spfPadic` and
`AlgebraicGeometry.FormalSpace.isNoetherian_spfPadic`, this is Stacks 0ALG for the source's own
space *granted the identification of its quasi-coherent modules*, which the library does not
have; see the section "What Stacks 0ALG still needs" of this file.  The equivalence is an input
here and not a conclusion, so no tag is registered.

The intended instance is `R` the `(p)`-adic completion of `ℤ`, `π` the image of `p` and `I` the
ideal it generates, in which case the category on the right is the category of `p`-adically
complete abelian groups of Stacks, Section 110.13. -/
theorem not_abelian_quasicoherentModules_spfPadic_of_equivalence (p : ℕ)
    (R : Type r) [CommRing R] [IsNoetherianRing R] [NoZeroDivisors R]
    (I : Ideal R) (hR : IsAdicComplete I R) (π : R) (hIspan : I = Ideal.span {π})
    (hπ : π ≠ 0) (hπnonunit : ¬ IsUnit π)
    (E : Type s) [AddCommGroup E] [Module R E] (eER : E ≃ₗ[R] R)
    (e : FibredSite.quasicoherentModules.{u, u + 1, u + 1, m}
        intSite.{u} intBase.{u} intSite_contains (spfPadicProjection.{u} p)
        (isFiberedInGroupoids_spfPadicProjection.{u} p) ≌
      Stacks.Examples.IAdicallyCompleteModuleCat.{s} R I) :
    ¬ Nonempty (Abelian (FibredSite.quasicoherentModules.{u, u + 1, u + 1, m}
      intSite.{u} intBase.{u} intSite_contains (spfPadicProjection.{u} p)
      (isFiberedInGroupoids_spfPadicProjection.{u} p))) :=
  not_abelian_quasicoherentModules_of_equivalence intSite.{u} intBase.{u} intSite_contains
    (spfPadicProjection.{u} p) (isFiberedInGroupoids_spfPadicProjection.{u} p) R I hR π hIspan
    hπ hπnonunit E eER e

end AlgebraicGeometry.FormalSpace

end
