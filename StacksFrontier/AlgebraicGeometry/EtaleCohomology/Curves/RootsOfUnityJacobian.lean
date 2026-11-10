module

public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurve
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMapCriterion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Clopen
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleInvertible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The Jacobian as an abelian variety, and the divisibility it gives the Picard group

The degree-two étale cohomology of a curve with roots-of-unity coefficients is computed by
[Stacks, Tag 03RQ] and [Stacks, Tag 03RR] out of one geometric input: that `Pic⁰` of a smooth
projective curve is an *abelian variety*, so that its group of rational points is divisible by
clause (4) of [Stacks, Tag 03RP]. This file supplies that input and spends it.

## The abelian variety

[Stacks, Tag 0BA0] presents `Pic_{X/k}` as the disjoint union of its degree components
(clause (1)) and its degree-zero component as an open *and closed subgroup scheme* (clause (3)).
The second of these already has the shape of an `AlgebraicGeometry.OpenSubgroupScheme` of a
`CategoryTheory.Grp (Over (Spec k))` in
`StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Clopen`, and an `OpenSubgroupScheme` carries
its own group object: `H.carrier.X` is an object of `Over (Spec k)` with a
`CategoryTheory.GrpObj` instance. So once the remaining half of clause (1) — that the degree
components are `g`-dimensional smooth proper varieties — is granted, Remark 0H2U turns that group
object into an abelian variety, with no further input:
`AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier`.

That is the link the consumers of Tags 03RQ and 03RR were missing, and the only one of the five
that is *supplied* here rather than carried. The other four are carried as explicit named
hypotheses, in this order:

* the scheme `Pic_{X/k}` and its group structure, carried as the bundled
  `G : CategoryTheory.Grp (Over (Spec k))` — this is representability of the Picard functor,
  [Stacks, Tag 0B9Z], together with the fact that the Picard functor is group-valued;
* the degree-zero component as an open subgroup scheme of it, carried as `H` — Tag 0BA0,
  clause (3), in the shape `StacksFrontier/AlgebraicGeometry/GroupScheme/Subgroups/Clopen.lean`
  already uses;
* properness, smoothness and connectedness of `Pic⁰`, carried as `hproper`, `hsmooth` and
  `hconn` — the unproved half of Tag 0BA0, clause (1).  Connectedness, not just the dimension
  count, is what Remark 0H2U needs, and the dimension `g` itself is not needed at all.  These
  three are **not** carried by
  `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier_of_smooth_surjective`, which
  derives all three from the Abel map of clause (4) instead, by the descent theorems recorded
  in the next section; what that declaration carries in their place is the *existence* of the
  Abel map;
* flatness of `[n]` on `Pic⁰`, which `Stacks.Groupoids.exists_zpow_eq_of_flat` carries as
  `hflat`.  It is carried here only by the two divisibility statements
  `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian` and
  `AlgebraicGeometry.exists_nsmul_eq_schemePicard_of_jacobian`; every cohomological consumer
  discharges it from `n` being invertible in `k`, by
  `AlgebraicGeometry.OpenSubgroupScheme.flat_zpow_carrier_of_isUnit`;
* the identification of the rational points of `Pic⁰` with the relevant Picard group, carried as
  `φ` with `hmul` and `hsurj`.

## The two spellings of the surjection, which are not interchangeable

On a smooth **projective** curve the target is `Pic⁰(X)`, not `Pic(X)`: the degree homomorphism
`AlgebraicGeometry.picardDegree` is onto `𝐙` —
`AlgebraicGeometry.surjective_picardDegree_of_eq_one`, over a class of degree one — which is not
`n`-divisible, so a surjection of `Pic⁰(X̄)(k)` onto all of `Pic(X)` would be a false hypothesis
and the conclusion vacuous. Hence
`AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian` takes `φ` into the subgroup
`AlgebraicGeometry.curvePicardDegreeZero`.

On an **affine** curve the target is all of `Pic(X)`: restriction along `X ⊂ X̄` carries
`Pic⁰(X̄)` onto `Pic(X)`, because every class on `X` extends to `X̄` and can then be corrected to
degree zero using a puncture, which is where the affine curve's `r ≥ 1` enters. Hence
`AlgebraicGeometry.exists_nsmul_eq_schemePicard_of_jacobian` takes `φ` into `schemePicard X`, and
there the scheme `X` of the cohomology and the curve whose Jacobian `Pic⁰` is are *different*
curves — nothing here ties `G` to `X`.

## What is spent, and what is not

The divisibility so obtained discharges the `hdvd` hypothesis of both assembled consumers:
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian` for
all eight clauses of Tag 03RQ and
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian` for clauses (2)
and (3) of Tag 03RR. Their other hypotheses are untouched and are discussed where they are
carried.

It does **not** discharge the divisibility hypotheses of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwo`. Those are stated
for `Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1`, on Mathlib's
small étale site at coefficient universe `AddCommGrpCat.{max (u + 1) v}`; what identifies such a
group with `Pic(X)` is [Stacks, Tag 03P8], and the library proves it only as
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup`, on
`AlgebraicGeometry.SmallEtale.topology` at coefficient universe `AddCommGrpCat.{u}`.  Since
`Stacks.Kummer.multiplicativePresheaf` ends in `AddCommGrpCat.uliftFunctor` and
`AlgebraicGeometry.unitsPresheaf` does not, `max (u + 1) v` is never `u`: the two coefficient
categories are never the same category.

That by itself is **not** an obstruction, and in particular it does not block that cluster's
`hGm`, which is proved: `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`. The
two coefficient universes never agree and do not have to, because restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite` carries `Stacks.Kummer.multiplicativeSheaf` to the
coefficient-universe lift of the middle term of `AlgebraicGeometry.kummerSmallEtale`
definitionally, and
`Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift` then descends the
universe.  What remains true of the Tag 03P8 half is only that it has not been carried across:
that comparison is an *isomorphism* and not a vanishing, so the descent above does not apply to
it verbatim — `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` is the shape it would need
— and no such transport has been built here.

## Main results

* `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier` (in
  `StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMapCriterion`, used here):
  the degree-zero component of the Picard scheme is an abelian variety.
* `AlgebraicGeometry.OpenSubgroupScheme.smooth_carrier_of_smooth_surjective`,
  `AlgebraicGeometry.OpenSubgroupScheme.isProper_carrier_of_isProper_surjective` and
  `AlgebraicGeometry.OpenSubgroupScheme.connectedSpace_carrier_of_connectedSpace_surjective`:
  **Tag 0BA0, the unproved half of clause (1)** — smoothness, properness and connectedness of a
  degree component of the Picard scheme, each obtained from the Abel map of clause (4) by a
  descent theorem, and together exactly the three hypotheses of the previous result.
* `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier_of_smooth_surjective`: the two
  combined — the degree-zero component is an abelian variety, with properness, smoothness and
  connectedness no longer hypotheses.
* `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian` and
  `AlgebraicGeometry.exists_nsmul_eq_schemePicard_of_jacobian`: the `n`-divisibility of `Pic⁰(X)`
  of a projective curve, and of `Pic(X)` of an affine one.
* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian`
  and `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian`: the two
  assembled consumers with their divisibility hypothesis discharged.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Remark 0H2U](https://stacks.math.columbia.edu/tag/0H2U)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 02K5](https://stacks.math.columbia.edu/tag/02K5)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

namespace OpenSubgroupScheme

/-- **Multiplication by an invertible integer on a proper, smooth, connected open subgroup scheme
over an algebraically closed field is flat.** The carrier is an abelian variety by
`AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier`, and on an abelian variety
multiplication by `n` is étale, hence flat, whenever `n` is invertible in `k`, by
`Stacks.Groupoids.flat_zpow_id_left_of_isUnit`. This is the hypothesis `hflat` of
`AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian`. -/
theorem flat_zpow_carrier_of_isUnit {k : Type u} [Field k] [IsAlgClosed k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left) (n : ℕ) (hn : IsUnit (n : k)) :
    Flat ((𝟙 H.carrier.X : H.carrier.X ⟶ H.carrier.X) ^ (n : ℤ)).left :=
  have : IsAbelianVariety k H.carrier.X := H.isAbelianVariety_carrier hproper hsmooth hconn
  Stacks.Groupoids.flat_zpow_id_left_of_isUnit H.carrier.X n hn

/-! ### The three properties of the degree component, off the Abel map

The three hypotheses of `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier` are the
unproved half of clause (1) of [Stacks, Tag 0BA0]. They are *not* irreducible: the source's own
route to them is the Abel map `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` of clause (4), surjective for
`d ≥ g` and smooth for `d ≥ 2g - 1` by clause (5), out of the symmetric power `Sym^d X`, which
for a smooth projective curve is a smooth projective — hence proper, smooth and connected —
variety over `k`. Each of the three properties travels along such a map by a descent theorem
this library already has, so all three reduce to the *existence* of the Abel map and the three
properties of its source.

Two things are *not* reduced away, and neither is proved here. The dimension `g`, which no
declaration in this library computes for a Picard scheme and which Remark 0H2U does not need.
And the passage from degree `d` to degree `0`: `γ_d` is surjective onto `Pic^d_{X/k}`, whereas
only `Pic^0_{X/k}` is a subgroup scheme, so applying the results below to the degree-zero
component asks for a morphism onto *it* — the composite of `γ_d` with a translation
`Pic^d_{X/k} ≅ Pic^0_{X/k}` by a class of degree `-d`.  On the Picard *group* that translation is
available: `AlgebraicGeometry.picardDegreeTranslate` is the bijection
`{x | deg x = deg M} ≃ Pic⁰(X)` for an arbitrary class `M`, and classes of a prescribed degree
exist — `AlgebraicGeometry.picardDegree_divisorSchemePicardClass_eq_one` produces one of degree
one from a `k`-rational point of the curve and
`AlgebraicGeometry.surjective_picardDegree_of_eq_one` then makes the degree onto `𝐙`.

The degree `AlgebraicGeometry.invertibleCurveDegree` is computed in this library:
`AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections` computes
`deg 𝒪_X(D) = dim_k Γ(D, 𝒪_D)` for every effective Cartier divisor on a proper integral curve,
and `AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_one` evaluates it at a `k`-rational
point.

What is still missing is the translation as a morphism of *schemes*, and the obstruction to that
is not the class.  Translation by a rational point of a group scheme is already an isomorphism,
`CategoryTheory.GrpObj.mulRight`, and `AlgebraicGeometry.Surjective` transports along an
isomorphism; what is absent is a degree-`d` component to translate.  The degree decomposition is
carried throughout as a bare family `P : ℤ → Scheme` with open immersions into `G.X.left` — see
`AlgebraicGeometry.OpenSubgroupScheme.isClosedImmersion_of_degreeDecomposition` — whose only tie
to `H` is that the ranges of `j 0` and of `H.ι` agree, so nothing relates `P d` to `H.carrier`
for `d ≠ 0`; and `γ_d` itself is only ever a carried morphism, neither `Hilb^d_{X/k}` nor
`Pic^d_{X/k}` being available as a scheme ([Stacks, Tag 0B97] and [Stacks, Tag 0B9Z]).  The
hypothesis below is therefore still a surjection onto the component itself, not `γ_d`.
-/

/-- **Stacks Project, Tag 0BA0, clause (1): smoothness of a degree component of the Picard
scheme, off the Abel map.** Let `H` be the degree-`d` component of the Picard scheme, presented
as an open subgroup scheme of `Pic_{X/k}` as in clause (3), and let `abel : A ⟶ H` be a surjective
smooth morphism from a scheme `A` smooth over `k` — the Abel map `γ_d` of clause (4) out of
`Hilb^d_{X/k} = Sym^d X`, which clause (5) makes surjective and smooth for `d ≥ 2g - 1`. Then
`H` is smooth over `k`.

This is descent of smoothness along a surjective smooth morphism, `[Stacks, Tag 02K5]`, proved in
this library as `Stacks.Smooth.smooth_of_comp_surjective_smooth`.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem smooth_carrier_of_smooth_surjective {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (abel : A ⟶ H.carrier.X.left)
    (hcomm : abel ≫ H.carrier.X.hom = sA) (hsurj : Surjective abel) (habel : Smooth abel)
    (hsmoothA : Smooth sA) : Smooth H.carrier.X.hom := by
  subst hcomm
  have := hsurj
  have := habel
  have := hsmoothA
  exact _root_.Stacks.Smooth.smooth_of_comp_surjective_smooth abel H.carrier.X.hom

/-- **Stacks Project, Tag 0BA0, clause (1): properness of a degree component of the Picard
scheme, off the Abel map.** In the situation of
`AlgebraicGeometry.OpenSubgroupScheme.smooth_carrier_of_smooth_surjective`, with `A` moreover
proper over `k`, the degree component is proper over `k`.

Properness has three parts and each is supplied without further hypotheses. Universal closedness
is `[Stacks, Tag 03GN]`, `AlgebraicGeometry.universallyClosed_of_universallyClosed_of_surjective`:
a map is closed as soon as its precomposition with a continuous surjection is. Separatedness is
automatic for a group scheme over a field, `[Stacks, Tag 047L]`,
`AlgebraicGeometry.isSeparated_hom_of_groupScheme_over_field`, and the carrier of an open subgroup
scheme is one. Locally-of-finite-typeness comes from the smoothness just proved, a smooth
morphism being locally of finite presentation.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem isProper_carrier_of_isProper_surjective {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (abel : A ⟶ H.carrier.X.left)
    (hcomm : abel ≫ H.carrier.X.hom = sA) (hsurj : Surjective abel) (habel : Smooth abel)
    (hproperA : IsProper sA) (hsmoothA : Smooth sA) : IsProper H.carrier.X.hom := by
  have := hsurj
  have := hproperA
  have : Smooth H.carrier.X.hom :=
    H.smooth_carrier_of_smooth_surjective sA abel hcomm hsurj habel hsmoothA
  have : IsSeparated H.carrier.X.hom := isSeparated_hom_of_groupScheme_over_field H.carrier
  exact isProper_of_isProper_of_surjective abel H.carrier.X.hom sA hcomm

/-- **Stacks Project, Tag 0BA0, clause (1): connectedness of a degree component of the Picard
scheme, off the Abel map.** The continuous image of a connected space is connected, so a degree
component admitting a surjection from a connected scheme — the Abel map out of
`Hilb^d_{X/k} = Sym^d X`, connected because `X` is — is connected.

Connectedness, and not the dimension count, is what Remark 0H2U asks of clause (1), and it is
established here on the *scheme* `H.carrier.X.left`: `AlgebraicGeometry.schemePicard` carries no
topology, so no connectedness statement about it would say anything.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem connectedSpace_carrier_of_connectedSpace_surjective {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {A : Scheme.{u}}
    (abel : A ⟶ H.carrier.X.left) (hsurj : Surjective abel) (hconnA : ConnectedSpace A) :
    ConnectedSpace H.carrier.X.left :=
  have := hsurj
  have := hconnA
  abel.surjective.connectedSpace abel.continuous

/-- **Stacks Project, Tag 0BA0: the degree-zero component of the Picard scheme of a curve is an
abelian variety, off the Abel map.** This is
`AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier` with its three hypotheses — the
unproved half of clause (1) — replaced by the Abel map of clause (4) and the three properties of
its source: a surjective smooth `abel : A ⟶ Pic⁰_{X/k}` out of a scheme `A` proper, smooth and
connected over `k`.

For the tag's curve `A` is `Hilb^d_{X/k} = Sym^d X`, a smooth projective variety, and `abel` is
`γ_d`, surjective for `d ≥ g` and smooth for `d ≥ 2g - 1` by clause (5). What remains carried is
therefore the *existence* of the Abel map, which is representability of the Hilbert and Picard
functors, [Stacks, Tag 0B97] and [Stacks, Tag 0B9Z], together with clause (4) — and not any of
properness, smoothness or connectedness of `Pic⁰`.

The dimension `g` plays no part here either.

This is a partial step towards [Stacks, Tag 0BA0], which is registered on its full statement. -/
theorem isAbelianVariety_carrier_of_smooth_surjective {k : Type u} [Field k]
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G) {A : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (abel : A ⟶ H.carrier.X.left)
    (hcomm : abel ≫ H.carrier.X.hom = sA) (hsurj : Surjective abel) (habel : Smooth abel)
    (hproperA : IsProper sA) (hsmoothA : Smooth sA) (hconnA : ConnectedSpace A) :
    IsAbelianVariety k H.carrier.X :=
  H.isAbelianVariety_carrier
    (H.isProper_carrier_of_isProper_surjective sA abel hcomm hsurj habel hproperA hsmoothA)
    (H.smooth_carrier_of_smooth_surjective sA abel hcomm hsurj habel hsmoothA)
    (H.connectedSpace_carrier_of_connectedSpace_surjective abel hsurj hconnA)

end OpenSubgroupScheme

section ProjectiveCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

include f in
/-- **`Pic⁰(X)` of a smooth projective curve is `n`-divisible**, which is clause (4) of
[Stacks, Tag 03RP] applied to the Jacobian of [Stacks, Tag 0BA0].

The degree-zero component `H` of the Picard scheme is an abelian variety by
`AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier`; its group of rational points is
`n`-divisible by `Stacks.Groupoids.exists_pow_eq_of_flat`, over the flatness of `[n]`; and `φ`
carries that divisibility to `Pic⁰(X)` by
`Stacks.Groupoids.exists_nsmul_eq_of_surjective`.

The target of `φ` is the subgroup `Pic⁰(X)` and not all of `Pic(X)`: on a projective curve the
degree is onto `𝐙`, so a surjection onto `Pic(X)` would be false and the statement vacuous. The
witness `y` is not asked to lie in `Pic⁰(X)`, which is the shape the consumers of this
divisibility use; it does lie there, being `φ` of a rational point.

This is a partial form of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP). -/
theorem exists_nsmul_eq_curvePicardDegreeZero_of_jacobian
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hflat : Flat ((𝟙 H.carrier.X : H.carrier.X ⟶ H.carrier.X) ^ (n : ℤ)).left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k X f))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ)
    (x : schemePicard X) (hx : x ∈ curvePicardDegreeZero k X f) :
    ∃ y, n • y = x := by
  have : IsAbelianVariety k H.carrier.X :=
    H.isAbelianVariety_carrier hproper hsmooth hconn
  obtain ⟨y, hy⟩ := Stacks.Groupoids.exists_nsmul_eq_of_surjective H.carrier.X n hflat φ hmul
    hsurj ⟨x, hx⟩
  refine ⟨(y : schemePicard X), ?_⟩
  have h := congrArg (fun z : ↥(curvePicardDegreeZero k X f) => (z : schemePicard X)) hy.symm
  simpa using h

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ] with the divisibility of `Pic⁰(X)` discharged.**
This is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees` with
its `hdvd` replaced by the geometric input it stands for: that the degree-zero component of the
Picard scheme is an abelian variety whose rational points are `Pic⁰(X)`, and that `[n]` on it is
flat.

The remaining three hypotheses of that theorem — `hGm`, which is [Stacks, Tag 03RM] on this site
and is universe-blocked, `hdeg`, the surjectivity of the degree, and `hgenus`, clause (7) of
[Stacks, Tag 03RP] — are carried unchanged; they are discussed where they are carried. Of those
three only `hGm` and `hgenus` are open: `hdeg` is `AlgebraicGeometry.surjective_curvePicardDegree`
and is discharged as well on
`etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_closedPoint` below.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian [Smooth f]
    (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k X f n) ≃+
      (Fin (2 * genus f) → ZMod n)))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k X f))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
          picardDegreeZMod k X f n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q) :=
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees k X f B hX n hn hGm hdeg
    (fun x hx => exists_nsmul_eq_curvePicardDegreeZero_of_jacobian k X f n H hproper hsmooth
      hconn (H.flat_zpow_carrier_of_isUnit hproper hsmooth hconn n hn) φ hmul hsurj x hx)
    hgenus

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ] with both arithmetic inputs discharged.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian`
with its `hdeg` supplied as well: the degree homomorphism of a smooth projective curve over an
algebraically closed field is onto `𝐙`, by
`AlgebraicGeometry.surjective_curvePicardDegree`, because a closed point is a Picard class of
degree one.

What is left carried is `hGm`, which is [Stacks, Tag 03RM] on this site and is proved as
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve` — the form of this
statement with it discharged is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm`
— and `hgenus`, clause (7) of [Stacks, Tag 03RP], which the source itself
says has no elementary proof — together with the geometric input that replaced `hdvd`.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_closedPoint
    [Smooth f] (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k X f n) ≃+
      (Fin (2 * genus f) → ZMod n)))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → ↥(curvePicardDegreeZero k X f))
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
          picardDegreeZMod k X f n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q) :=
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian k X f B hX n hn hGm
    (surjective_curvePicardDegree k X f) hgenus H hproper hsmooth hconn φ hmul hsurj

end ProjectiveCurve

section AffineCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

/-- **`Pic(X)` of a smooth affine curve is `n`-divisible**, which is clause (4) of
[Stacks, Tag 03RP] applied to the Jacobian of the compactification.

Here `H` is the degree-zero component of the Picard scheme of a smooth projective curve `X̄`, and
`φ` is the composite of the identification of its rational points with `Pic⁰(X̄)` with
restriction along the open immersion `X ⊂ X̄`.  Restriction is onto because every class on `X`
extends to `X̄` and can be corrected to degree zero by a multiple of a puncture, which is where
the affine curve's `r ≥ 1` is used; that surjectivity is the content of `hsurj`.

Nothing here ties `H` to `X`: the statement is that *some* abelian variety whose rational points
surject onto `Pic(X)` makes `Pic(X)` divisible.  On a projective `X` the hypothesis `hsurj`
would be false, `AlgebraicGeometry.picardDegree` being onto `𝐙`, which is why the projective
consumer uses `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian` with its
`φ` into the degree-zero subgroup instead.

This is a partial form of [Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP). -/
theorem exists_nsmul_eq_schemePicard_of_jacobian
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (hflat : Flat ((𝟙 H.carrier.X : H.carrier.X ⟶ H.carrier.X) ^ (n : ℤ)).left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → schemePicard X)
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ)
    (x : schemePicard X) :
    ∃ y, x = n • y :=
  have : IsAbelianVariety k H.carrier.X := H.isAbelianVariety_carrier hproper hsmooth hconn
  Stacks.Groupoids.exists_nsmul_eq_of_surjective H.carrier.X n hflat φ hmul hsurj x

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
omit [Smooth f] in
/-- **Clauses (2) and (3) of [Stacks, Tag 03RR] with the divisibility of `Pic(X)` discharged.**
This is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve` with its `hdvd`
replaced by the geometric input it stands for: an abelian variety — the degree-zero Picard scheme
of the compactification — whose rational points surject onto `Pic(X)`. The flatness of `[n]` on
it is not carried: it holds because `n` is invertible in `k`, by
`AlgebraicGeometry.OpenSubgroupScheme.flat_zpow_carrier_of_isUnit`.

The other four hypotheses of that theorem are carried unchanged: `hGm`, which is
[Stacks, Tag 03RM] on this site and is **not** universe-blocked — it is proved outright, as
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, and the form of this
statement with it discharged as well is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_gm` — and
`hunits`, `htors`, `hrank`, the rank count of the degree-one sequence.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian (hn : IsUnit (n : k))
    {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j]
    (r : ℕ) {a b : ℕ}
    (hunits : Nonempty (↥(etaleH1RootsOfUnityToPicard X B hX n).ker ≃+ (Fin a → ZMod n)))
    (htors : Nonempty (↥(picardNTorsion X n) ≃+ (Fin b → ZMod n)))
    (hrank : a + b = 2 * genus fbar + r - 1)
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → schemePicard X)
    (hmul : ∀ a' b', φ (a' * b') = φ a' + φ b') (hsurj : Function.Surjective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve k X f B hX n hn fbar j r hunits htors hrank hGm
    (exists_nsmul_eq_schemePicard_of_jacobian k X n H hproper hsmooth hconn
      (H.flat_zpow_carrier_of_isUnit hproper hsmooth hconn n hn) φ hmul hsurj)

end AffineCurve

end AlgebraicGeometry

end
