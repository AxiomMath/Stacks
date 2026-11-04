module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartRestrictionModuleIdentification
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace

/-!
# The two spellings of equation 075K on modules, and Stacks 0GQC for the functorial one

Restriction of an `𝒪_𝒳`-module to the small étale site of the algebraic space representing a
category fibred in groupoids — equation 075K read on sheaves of modules — occurs twice in this
development, in two different packagings:

* `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`, which folds a 1-morphism
  `f : 𝒰 ⥤ 𝒳` into the restriction and is therefore a map on objects only, not a functor in
  the module; and
* `AlgebraicGeometry.Space.moduleRestriction`, the functor `ℱ ↦ ℱ|_{X_étale}`, which is what
  the comparison functor of Stacks 0GQD is built from.

`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestriction` proves **Stacks 0GQC**
unconditionally, but about the first spelling. This file identifies the two at the identity
1-morphism and carries 0GQC across, so that the statement is available about the functor.

## Main results

* `AlgebraicGeometry.Space.moduleRestriction_obj_eq_etaleRestrictedModuleInverseImage`: **the two
  spellings agree on the nose.** Both are the same `CategoryTheory.SheafOfModules.pushforward`,
  so the identification is reflexivity; see the implementation notes for why.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_moduleRestriction`: **Stacks 0GQC for the
  functorial spelling** — the restriction of a locally quasi-coherent module along
  `AlgebraicGeometry.Space.moduleRestriction` is quasi-coherent on the small étale site of the
  representing algebraic space.
* `AlgebraicGeometry.Space.restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent`:
  the hypothesis `AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` of Stacks 0GQD,
  **reduced to the forward direction of Stacks 06WK** and to nothing else, at every module
  universe.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_forallIsLocallyQuasicoherent`:
  that reduction at the module universe `max (u + 1) w m` where the quasi-inverse `π_X^*` of
  Stacks 0GQD exists, so that **the comparison functor is an equivalence over `hcounit` and
  clause (a) of Stacks 06WK alone.**

## The hypothesis `hres` of Stacks 0GQD

`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` differs from Stacks 0GQC exactly in
its quantifier. It ranges over
`AlgebraicGeometry.FibredSite.quasicoherentModules`, the modules quasi-coherent on the inherited
**fppf** site (Stacks 06WG), whereas Stacks 0GQC takes
`AlgebraicGeometry.Stack.IsLocallyQuasicoherent` (Stacks 06WJ) as its hypothesis. The step
between them is the forward direction of **Stacks 06WK**, clause (a), and it is named here as
`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent`. Of the two clauses of local
quasi-coherence that step has to produce, the first — that the module is a sheaf for the
inherited étale topology — is
`AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherentFppf`; the second — that the restriction
of the module to the small étale site of the scheme below each object of `𝒳` is quasi-coherent —
needs quasi-coherence read for a *coarser* topology, which is the half of Stacks 0EM8 identified
at the big site of a scheme with the essential-surjectivity half of Descent, Proposition 03DX.
The other half is `Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`, which goes the other
way.

## The module universe

`AlgebraicGeometry.Space.moduleRestriction` and
`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` leave the universe of the module
sections free, and so does the whole 075K/06WJ/0GQC chain:
`AlgebraicGeometry.Space.inheritedEtaleModules` carries a module universe parameter, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestriction` holds at every value of it.
A left adjoint of restriction exists in this library only at a module universe dominating
`max (u + 1) w` — the objects of the small étale site live in `Type (u + 1)` — and the statement
at such a universe, where `hres` and the quasi-inverse `π_X^*` are both available, is
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_forallIsLocallyQuasicoherent`.

## Implementation notes

The identification is reflexivity, and it is worth saying why, since the two sides are built
through different files. Both are
`CategoryTheory.SheafOfModules.pushforward` of the module along a continuous functor
`X_étale ⥤ 𝒳` with a coefficient homomorphism of structure sheaves, and at the identity
1-morphism the three ingredients match definitionally:

* the index functors. `AlgebraicGeometry.Space.etaleChartToFibred` at `f = 𝟭 𝒳` is
  `AlgebraicGeometry.Space.restrictionFunctor ⋙ 𝟭 𝒳`, which is the restriction functor itself by
  structure eta;
* the coefficient homomorphisms. `AlgebraicGeometry.Space.etaleChartStructureHom` and
  `AlgebraicGeometry.Space.restrictionStructureHom` are both the whiskering of the
  `CategoryTheory.eqToHom` of an equality of functors `X_étale ⥤ (Sch/S)_{fppf}` with the
  structure sheaf of the big fppf category. The two equalities proved —
  `AlgebraicGeometry.Space.etaleChartToFibred_comp` at `f = 𝟭 𝒳` and
  `AlgebraicGeometry.Space.restrictionFunctor_comp` — have definitionally equal statements by the
  previous point, and they are propositions, so the two `CategoryTheory.eqToHom`s are
  definitionally equal for that reason alone;
* the coefficient sheaves of rings. `AlgebraicGeometry.Space.structureRingSheaf`, which
  `AlgebraicGeometry.Space.moduleRestriction` is built at, and
  `AlgebraicGeometry.Space.Modules`, which it and
  `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` are both typed at, are the same
  `AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site, differing only in the
  ascription of the topology.

So no transport and no isomorphism is needed; in particular the comparison is not of the kind
that `AlgebraicGeometry.Space.chartRestriction_iso` has to make, where the two sides evaluate
the module at two objects of `𝒳` produced by two different chosen quasi-inverses.

## References

* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Clause (a) of the forward direction of Stacks 06WK**, at the module universe `m`: every
module quasi-coherent on the inherited fppf site of `𝒳` (Stacks 06WG) is locally quasi-coherent
(Stacks 06WJ), the auxiliary big étale site being the canonical
`AlgebraicGeometry.associatedBigEtaleSite`.

Of the two clauses of local quasi-coherence, the étale sheaf condition is
`AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherentFppf`, while the quasi-coherence of the
restriction to the small étale site of the scheme below each object needs quasi-coherence read
for a coarser topology, which is one half of Stacks 0EM8.

It is exactly the residue between Stacks 0GQC and the hypothesis
`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` of Stacks 0GQD; see
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent`. -/
noncomputable abbrev ForallQuasicoherentIsLocallyQuasicoherent : Prop :=
  ∀ M : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp,
    IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp
      ((FibredSite.toSiteModules B S hS p hp .etale).obj M).val

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- **The functorial spelling of equation 075K on modules is the one with a 1-morphism folded
in, at the identity 1-morphism.** The value of `AlgebraicGeometry.Space.moduleRestriction` at an
`𝒪_𝒳`-module is `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` of it along `𝟭 𝒳`.

Both sides are the pushforward of the module along the functor
`u_X : X_étale ⥤ 𝒳` of Stacks 073M with the identification `𝒪_X = u_X^*𝒪_𝒳` of structure
sheaves as coefficient homomorphism, so the two agree definitionally; the implementation notes
of this file spell out the three matchings involved. -/
theorem moduleRestriction_obj_eq_etaleRestrictedModuleInverseImage
    (ℱ : inheritedEtaleModules B S hS p hp) :
    (moduleRestriction.{u, v, w, m} B S hS X p hp e).obj ℱ =
      etaleRestrictedModuleInverseImage B S hS p p hp hp e (𝟭 𝒳)
        (Functor.IsFibredOneMorphism.id p) ℱ :=
  rfl

/-- **Stacks 0GQC for the functorial restriction.** Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category
fibred in groupoids representable by the algebraic space `X`, through a chosen equivalence over
the site as in Stacks 073M. If `ℱ` is a locally quasi-coherent `𝒪_𝒳`-module (Stacks 06WJ), then
its restriction `ℱ|_{X_étale}` along `AlgebraicGeometry.Space.moduleRestriction` is
quasi-coherent on the small étale site of `X`.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestriction`, carried across
`AlgebraicGeometry.Space.moduleRestriction_obj_eq_etaleRestrictedModuleInverseImage`. -/
theorem isQuasicoherentOnSite_moduleRestriction (ℱ : inheritedEtaleModules B S hS p hp)
    (hℱ : Stack.IsLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS p hp ℱ.val) :
    quasicoherentModulesProperty.{u, m} B S hS X
      ((moduleRestriction.{u, v, w, m} B S hS X p hp e).obj ℱ) :=
  isQuasicoherentOnSite_etaleRestriction B S hS X p e hp ℱ hℱ

/-- **The hypothesis `hres` of Stacks 0GQD reduced to the forward direction of Stacks 06WK**, at
every module universe.

`AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` quantifies over the modules
quasi-coherent on the inherited fppf site, while Stacks 0GQC takes local quasi-coherence as its
hypothesis; so once
`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` is granted, `hres` follows
from `AlgebraicGeometry.Space.isQuasicoherentOnSite_moduleRestriction` and nothing else. That
hypothesis is clause (a) of Stacks 06WK and is the *whole* residue: no part of 0GQC, of
equation 075K or of the chart-local identification of Remark 0GQA is assumed here.

The module universe `m` is free, so in particular this applies at `max (u + 1) w m`, which is
where a left adjoint of `AlgebraicGeometry.Space.moduleRestriction` exists
(`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`); that instance is
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_forallIsLocallyQuasicoherent`
below. -/
theorem restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent
    (hlqc : Stack.ForallQuasicoherentIsLocallyQuasicoherent.{u, v, w, m} B S hS p hp) :
    RestrictionPreservesQuasicoherent.{u, v, w, m} B S hS X p hp e :=
  fun M => isQuasicoherentOnSite_moduleRestriction B S hS X p hp e _ (hlqc M)

/-- **The reduction of Stacks 0GQD with `hres` and the quasi-inverse at one module universe.**
Restriction to the small étale site of `X` is an equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)` over
`hcounit` and clause (a) of the forward direction of Stacks 06WK, at the module universe
`max (u + 1) w m` where a left adjoint `P` of restriction exists
(`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`).

This is `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_hcounit` with `hres`
supplied by
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent`
at that same universe, and nothing else changed.

The hypothesis `hcounit`, that the canonical map `π_X^*(ℱ|_{X_étale}) ⟶ ℱ` is an isomorphism
for quasi-coherent `ℱ`, is the geometric content of the proof of Stacks 0GQD; it rests on the
essential-surjectivity half of Descent, Proposition 03DX(2), as does
`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent`, by way of the
coarser-topology half of Stacks 0EM8. -/
theorem isEquivalence_quasicoherentRestriction_of_forallIsLocallyQuasicoherent
    (hlqc : Stack.ForallQuasicoherentIsLocallyQuasicoherent.{u, v, w, max (u + 1) w m}
      B S hS p hp)
    {P : Modules.{u, max (u + 1) w m} B S hS X.1 X.2 ⥤
      SheafOfModules.{max (u + 1) w m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    (adj : P ⊣ moduleRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e)
    (Pq : QuasicoherentSheaves.{u, max (u + 1) w m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, max (u + 1) w m} B S hS p hp)
    (hPq : Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, max (u + 1) w m} B S hS X).ι ⋙ P)
    (hcounit : ∀ M : FibredSite.quasicoherentModules.{u, v, w, max (u + 1) w m} B S hS p hp,
      IsIso (adj.counit.app ((FibredSite.toSiteModules B S hS p hp .etale).obj M))) :
    (quasicoherentRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e
      (restrictionPreservesQuasicoherent_of_forallIsLocallyQuasicoherent.{u, v, w,
        max (u + 1) w m} B S hS X p hp e hlqc)).IsEquivalence :=
  isEquivalence_quasicoherentRestriction_of_hcounit.{u, v, w, m} B S hS X p hp e _ adj Pq hPq
    hcounit

end AlgebraicGeometry.Space

end
