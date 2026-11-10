module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a relatively perfect complex along a proper flat morphism

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation and let `E` be an `S`-perfect
object of `D(𝒪_X)` in the sense of Stacks 0DI0. [Stacks, Tag 0DJT] asserts two independent
things: that `Rf_*E` is a *perfect* object of `D(𝒪_S)`, and that its formation commutes with
arbitrary base change. This file is about the first of the two. The second is a statement about
the invertibility of the canonical derived base-change comparison and nothing here bears on it.

The source proves perfectness by reducing to a Noetherian base — write an affine base as a
filtered colimit of Noetherian rings, descend `X` and `E` along it by [Stacks, Tag 0DI8], and
transfer back by base change — and then quotes [Stacks, Tag 08EV] over that Noetherian base.
This file is the Noetherian case: it discharges, from relative perfectness of `E` and properness
of `f`, every hypothesis [Stacks, Tag 08EV] makes of its source complex, and reaches the
conclusion of [Stacks, Tag 0DJT] from what this library has of [Stacks, Tag 08EV].

## Main definitions

* `PushforwardTorDimensionResidue` is the Tor-dimension half of [Stacks, Tag 08EV], quantified
  over the source complex: `Rf_*K` is of locally finite Tor dimension for *every* `S`-perfect `K`.
  It is what the perfectness result below carries in place of that half of the tag.

## Main results

* `isCoherent_homology_and_bounds_of_isPerfectRelativeTo`: what [Stacks, Tag 08EV] asks of its
  source complex, derived from relative perfectness — the cohomology sheaves of `E` are coherent
  and `E` is bounded.
* `isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo`: **the pseudo-coherence half of
  the conclusion of [Stacks, Tag 0DJT]**, `Rf_*E` is a pseudo-coherent object of `D(𝒪_S)`.
* `isPerfect_derivedPushforward_of_isPerfectRelativeTo`: **the perfectness clause of
  [Stacks, Tag 0DJT]** over a Noetherian base, granted the residue above.

## What is proved, and what is carried

By [Stacks, Tag 08CQ] a perfect object of `D(𝒪_S)` is exactly a pseudo-coherent one of locally
finite Tor dimension, and the source's proof of [Stacks, Tag 08EV] establishes the two halves
separately. This library carries the pseudo-coherence half, as
`Stacks.AlgebraicGeometry.ProperSupportCoherent`'s
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp`, and not the Tor-dimension half.

*The hypotheses of [Stacks, Tag 08EV] on the source complex are discharged here.* `S` is
Noetherian and `f` is of finite type and quasi-compact, so `X` is Noetherian. Relative
perfectness has pseudo-coherence of `E` as its first clause, which over a Noetherian scheme gives
coherent cohomology sheaves and a bound above by [Stacks, Tag 08E8]; and its Tor clause bounds
the cohomology of `E` below on the members of a covering, which quasi-compactness of `X` turns
into a global bound, by `AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`. Finally `f` being
proper, *every* closed subset of `X` is proper over `S` — the reduced induced closed subscheme on
it maps to `X` by a closed immersion, which is proper, and a composition of proper morphisms is
proper — in particular the support of each cohomology sheaf. So no boundedness, coherence or
support hypothesis is imposed below, exactly as in [Stacks, Tag 0DJT].

*`hqc` is carried.* The cohomology sheaves of a pseudo-coherent object of `D(𝒪_X)` on a scheme are
quasi-coherent, since the object is locally the image of a complex of finite free modules; this
library has no such statement, and [Stacks, Tag 08E8] is stated for objects of `D_QCoh(𝒪_X)`, so
quasi-coherence is a named hypothesis. It is a statement about `E` alone and says nothing about
`Rf_*E`.

*`haff` is carried.* It is
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5], and it is what this library's
pseudo-coherence half of [Stacks, Tag 08EV] takes.

*`htor` is the Tor-dimension half of [Stacks, Tag 08EV], and it is not proved.* The source tensors
`Rf_*E` with an arbitrary quasi-coherent `𝒪_S`-module `ℱ`, rewrites
`Rf_*E ⊗^𝐋_{𝒪_S} ℱ = Rf_*(E ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}ℱ)` by [Stacks, Tag 08EU] and
[Stacks, Tag 08DE], bounds the cohomology of the right-hand side using the finite Tor dimension
of `E` over `f^{-1}𝒪_S` — which for [Stacks, Tag 0DJT] is the Tor clause of relative perfectness
— and converts the resulting vanishing on quasi-coherent test modules into genuine Tor amplitude
by [Stacks, Tag 08EA]. Two of those steps are absent from this library: [Stacks, Tag 08EA] is
carried only as its clause `(1) implies (2)`, which is the direction the proof does not use, and
[Stacks, Tag 08EU] is carried only at `K = 𝒪_S[0]`, and even there with the right unitors of the
two derived tensor products and the right-unitor coherence of the [Stacks, Tag 079U] comparison
as explicit hypotheses, so the projection formula is unavailable at the `ℱ` the proof needs.

It is carried as `PushforwardTorDimensionResidue`, that half of [Stacks, Tag 08EV] *quantified
over the source complex*, rather than as the single instance of it the conclusion needs: the
quantified statement is strictly stronger, so it is a citation of the missing half of a tag and
not a restatement of the conclusion. No bare `@[stacks 0DJT]` is placed.

*The reduction to a Noetherian base is not carried out.* `IsNoetherian S` is a hypothesis below,
where [Stacks, Tag 0DJT] assumes none: the source's descent along a filtered colimit of
Noetherian rings needs [Stacks, Tag 0DI8], whose formalization in this tree stops at the
statement of the colimit presentation of the relative-perfect categories.

## Implementation notes

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`; pseudo-coherence is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the spelling of [Stacks, Tag 08CB] part (3)
that the pseudo-coherence half of [Stacks, Tag 08EV] concludes in; perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the spelling of [Stacks, Tag 08CM] that
[Stacks, Tag 08CQ] is stated at. Relative perfectness is
`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo`, [Stacks, Tag 0DI0].

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product on the inverse-image ringed space is a family of certificates, one on each open
subspace, and it is pinned by the hypothesis `hD` that its underived tensor product is the
genuine `- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU. Without that pinning the Tor clause of relative
perfectness carries no information: at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` it holds for
every object.

Properness is Mathlib's `IsProper`, which extends `LocallyOfFiniteType` and gives `QuasiCompact`,
so neither a finite-type nor a quasi-compactness hypothesis is repeated; together with
`LocallyOfFinitePresentation` and the separatedness inside `IsProper` it is the source's "flat,
proper and of finite presentation". `IsNoetherian S` is [Stacks, Tag 01OV] part (2).

## References

* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DI8](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSupportCoherent

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Certificates

variable [Flat f] [LocallyOfFinitePresentation f]

/-- The family of certificates for the derived tensor product on the inverse-image ringed space
`(X, f⁻¹𝒪_S)`, one on each open subspace, as part (3) of Stacks 08CG asks for. -/
abbrev TensorFamily : Type _ :=
  ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)

/-- The pinning of a family of certificates: its underived tensor product is the genuine
`- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU on every open subspace. -/
abbrev IsGenuineTensorFamily (D : TensorFamily f) : Prop :=
  ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding).sheaf

/-- **The Tor-dimension half of [Stacks, Tag 08EV], quantified over the source complex.** A
morphism `f` has this property when `Rf_*K` is of locally finite Tor dimension for *every*
`S`-perfect object `K` of `D(𝒪_X)`.

This is the half of the source's proof of [Stacks, Tag 08EV] that this library cannot carry out:
it needs the clause `(2) implies (1)` of [Stacks, Tag 08EA], which is carried only in the
opposite direction, and the projection formula of [Stacks, Tag 08EU] at a general target complex,
which is carried only at `K = 𝒪_S[0]`.

It is stated with a universal quantifier over `K` on purpose. The perfectness result below needs
it at one object only, and at that object it is — granted the pseudo-coherence proved below and
[Stacks, Tag 08CQ] — equivalent to the conclusion; quantified, it is strictly stronger, and
therefore a named citation of the missing half of [Stacks, Tag 08EV] rather than an assumption of
what is to be proved. -/
def PushforwardTorDimensionResidue (D : TensorFamily f) : Prop :=
  ∀ K : DerivedCategory X.Modules, f.IsPerfectRelativeTo D K →
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj K)

end Certificates

section ProperSupport

/-- **Every closed subset of the source of a proper morphism is proper over the target.** The
reduced induced closed subscheme on it maps to `X` by a closed immersion, which is proper, and a
composition of proper morphisms is proper. -/
theorem isProperOver_of_isProper [IsProper f] (T : Closeds X) : IsProperOver f T := by
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
  infer_instance

end ProperSupport

section Hypotheses

variable [IsNoetherian S] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **What [Stacks, Tag 08EV] asks of its source complex, for an `S`-perfect complex.** Let `S` be
a Noetherian scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let
`E` be an `S`-perfect object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent. Then those
cohomology sheaves are coherent and `E` is bounded.

`X` is Noetherian, being quasi-compact and locally of finite type over a Noetherian scheme.
Coherence and the bound above are then [Stacks, Tag 08E8] applied to the pseudo-coherence clause
of relative perfectness, and the bound below comes from the Tor clause through
`AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`. -/
theorem isCoherent_homology_and_bounds_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) :
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent) ∧
      ∃ a b : ℤ, E.IsGE a ∧ E.IsLE b := by
  have hXnoeth : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨⟨b, hb⟩, hcoh⟩ :=
    (AlgebraicGeometry.isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨E, hqc⟩).1 hE.1
  obtain ⟨a, hGE⟩ := AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo f D hD E hE
  exact ⟨hcoh, a, b, hGE, (DerivedCategory.isLE_iff E b).2 fun j hj => hb j hj⟩

/-- **The pseudo-coherence half of the conclusion of [Stacks, Tag 0DJT].** Let `S` be a Noetherian
scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let `E` be an
`S`-perfect object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. Then `Rf_*E` is a
pseudo-coherent object of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor dimension;
this is the first of the two. Everything the pseudo-coherence half of [Stacks, Tag 08EV] asks of
`E` is supplied by `isCoherent_homology_and_bounds_of_isPerfectRelativeTo`, and its support
hypothesis by `isProperOver_of_isProper`. The hypothesis `haff` is the one that half carries for
[Stacks, Tag 02O5]. -/
theorem isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨hcoh, a, b, hGE, hLE⟩ :=
    isCoherent_homology_and_bounds_of_isPerfectRelativeTo f D hD E hE hqc
  exact isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh
    (fun _ => isProperOver_of_isProper f _) haff a b hGE hLE

/-- **[Stacks, Tag 0DJT], the perfectness clause, over a Noetherian base.** Let `S` be a
Noetherian scheme, let `f : X ⟶ S` be a proper, flat morphism of finite presentation and let `E`
be an `S`-perfect object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. Then `Rf_*E` is a
perfect object of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the pseudo-coherence proved
above. The base-change clause of the tag — invertibility of the canonical derived base-change
comparison — is a separate assertion and is not proved here.

The hypothesis `htor` is `PushforwardTorDimensionResidue`, the Tor-dimension half of
[Stacks, Tag 08EV] quantified over the source complex, which is the half of that proof this
library cannot carry out; `haff` is its named form of [Stacks, Tag 02O5]; and `hqc` is
quasi-coherence of the cohomology sheaves of `E`. -/
@[stacks 0DJT "the perfectness clause only, over a Noetherian base: Rf_*E is perfect for E \
S-perfect and f proper, flat, locally of finite presentation. Three inputs are granted: Tag \
02O5 (haff), quasi-coherence of the H^i(E) (hqc), and the Tor-dimension half of Tag 08EV \
quantified over the source complex (htor). The base-change clause is not proved here"]
theorem isPerfect_derivedPushforward_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (htor : PushforwardTorDimensionResidue f D) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2
      (isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo f D hD E hE hqc haff))
    (htor E hE)

end Hypotheses

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
