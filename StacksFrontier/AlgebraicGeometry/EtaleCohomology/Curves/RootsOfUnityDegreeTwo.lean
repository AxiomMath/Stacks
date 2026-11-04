module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactBoundary
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Degree two for the roots of unity on a smooth curve: exactly the divisibility of `H¹(X, 𝐆_m)`

Let `X` be a smooth curve over an algebraically closed field `k` and let `n` be invertible on
`X`. Then

`H²_étale(X, μ_n) = 0` **if and only if** multiplication by `n` is surjective on
`H¹_étale(X, 𝐆_m)`.

This is the degree-two step of clause (3) of [Stacks, Tag 03RR] and of the `q = 2` clause of
[Stacks, Tag 03RQ], as far as the Kummer sequence can take it. Its `q ≥ 3` companion is
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve`, where both outer
terms of the Kummer long exact sequence vanish and the conclusion is unconditional. In degree
two only the right-hand one vanishes, and the segment

`H¹(X, 𝐆_m) --·n--> H¹(X, 𝐆_m) ⟶ H²(X, μ_n) ⟶ H²(X, 𝐆_m) = 0`

therefore does not kill `H²(X, μ_n)`: it identifies it with the cokernel of multiplication by
`n`. The equivalence below is that identification, stated as the vanishing criterion it gives.

## What this settles, and what it does not

The source proves the degree-two vanishing from the `n`-divisibility of `Pic(X)`, and by
[Stacks, Tag 03P8] `Pic(X)` is `H¹_étale(X, 𝐆_m)`. So the right-hand side of the equivalence is
precisely the source's input, and the equivalence says that input is not merely sufficient but
necessary: there is no route to `H²_étale(X, μ_n) = 0` through this sequence that avoids it.

Both directions are proved, so this file settles the cohomological half of the degree-two step
completely. What remains is the divisibility itself, which is not cohomology. For the affine
curve of Tag 03RR the source gets it from the surjection `Pic⁰(X̄) ↠ Pic(X)` onto the Picard
group of the open curve together with the divisibility of `Pic⁰(X̄)`; the latter is the
surjectivity of multiplication by `n` on an abelian variety, [Stacks, Tag 03RP], applied to the
Picard scheme of a curve, [Stacks, Tag 0BA0]. Both of those tags have registrations here, and
neither supplies what is wanted. Of Tag 03RP the library has commutativity, clause (3) that
`[d]` is onto (`Stacks.Groupoids.surjective_zpow_id_left_of_flat`) and clause (4) that `A(k)` is
divisible (`Stacks.Groupoids.exists_zpow_eq_of_flat`), the last two over the flatness of `[d]`,
with `Stacks.Groupoids.exists_nsmul_eq_of_surjective` transporting clause (4) along any surjection
out of `A(k)`. Of Tag 0BA0 it has eleven registrations, covering clauses (1) to (6). What is
missing is an abelian variety for clause (4) to be applied to: `Pic⁰` exists only as the kernel
subgroup `AlgebraicGeometry.picardDegreeZero`, with no scheme structure and no abelian-variety
structure on it, while `AlgebraicGeometry.picardScheme` is `(picardFunctor …).reprX` with no
`CategoryTheory.GrpObj` on it. That is missing mathematics rather than a missing application, and
nothing of it is assumed here. The *translation* by a class of degree one is not part of what is
missing: `AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_one` computes the value `1` at
a `k`-rational point, `AlgebraicGeometry.picardDegreeTranslate` is the translation itself, and on
a smooth projective curve over an algebraically closed field the degree is onto `𝐙` outright, by
`AlgebraicGeometry.surjective_curvePicardDegree`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_iff_smoothCurve` — the
  equivalence above.
* `Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_of_nsmul_surjective` — its
  useful direction on its own: the degree-two vanishing from the divisibility.
* `Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_le_of_nsmul_surjective` — the
  whole of `H^q_étale(X, μ_n) = 0` for `q ≥ 2`, which is clause (3) of [Stacks, Tag 03RR], and is
  registered under that tag.
* `Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve` — the
  **projective** curve's degree two, `H²_étale(X, μ_n) ≅ 𝐙/n𝐙`, which is the `q = 2` clause of
  the first list of [Stacks, Tag 03RQ] and is registered under that tag.

## Implementation notes

**This file registers the `q = 2` clause of the first list of [Stacks, Tag 03RQ]**, on the last
of the four results above, **and clause (3) of [Stacks, Tag 03RR]** on the third. On this site
clause (3) carries no more than the divisibility, [Stacks, Tag 03RM] being used
in its unconditional form rather than carried; on the big-étale-site of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurve`, where clause (2)
also lives, Tag 03RM is carried as a hypothesis `hGm` by the statements of that file — but **not
because it has to be**. The coefficient universes of the two sheaves of units are never
equal, and that is no obstruction: the asymmetry is a postcomposed
`AddCommGrpCat.uliftFunctor`, and restriction along the dense subsite is precomposition, which
commutes with it. So the restriction of `𝐆_m` from Mathlib's site *is* the coefficient-universe
lift of the other spelling, definitionally, and the vanishing descends —
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve` is the transport, and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveGmVanishing` the
assemblies with `hGm` discharged. Clause (2) of Tag 03RR is not in this file: it is the
rank count `2g + r - 1`, which is not a cohomological statement and of which no summand is
separately unconditional.

No result below carries any form of [Stacks, Tag 03Q9]. [Stacks, Tag 03RM] is
unconditional, and so is the
[Stacks, Tag 03RJ] it rests on,
`Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf` — and
not because Tag 03Q9 is supplied. That chain does not need it at any strength: at an
individual étale neighbourhood `Spec K ×_X V` is already étale over `Spec K`, hence a coproduct
of spectra of finite separable extensions, so the limit over neighbourhoods that Tag 03Q9 is
about is never formed.

Carrying another tag's conclusion as a named hypothesis does not forbid registering; what it
requires is that the hypothesis be named in the attribute string. The divisibility input below
is such a hypothesis, and it is named.

The divisibility hypothesis is stated as surjectivity of `n • ·` on `H¹_étale(X, 𝐆_m)` rather
than on `Pic(X)`, because the two live on different sites in this library. [Stacks, Tag 03RM]
and Tag 03RJ are proved on Mathlib's small étale site `X.smallEtaleTopology`, for
`Stacks.Kummer.multiplicativeSheaf`, while Tag 03P8 is proved as
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup` on the small étale site
`AlgebraicGeometry.SmallEtale.topology` cut out of a big étale site.

What transporting between them needs is narrower than a comparison of the two sites, which the
library has: `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite` makes the second a dense
subsite of the first and `AlgebraicGeometry.SmallEtale.sheafEquiv` is the resulting equivalence
of their categories of abelian sheaves, and the cohomological half of the transport is general
too, `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`. What is missing is
the identification of the two sheaves of units across that equivalence —
`Stacks.Kummer.multiplicativeSheaf` on the one side against
`Stacks.Cohomology.Torsors.Generators.unitsAddSheaf` of
`AlgebraicGeometry.smallEtaleRingedSite` on the other. Their coefficient universes,
`AddCommGrpCat.{max (u + 1) v}` against `AddCommGrpCat.{u}`, do differ, but that is **not** an
additional obstruction: the difference is a
postcomposed `AddCommGrpCat.uliftFunctor`, restriction along the dense subsite commutes with it,
and the coefficient universe descends afterwards —
`Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift` for a vanishing and
`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` for an isomorphism, which is the shape
this `Pic`-side comparison would need. Until the identification of the two sheaves of units
exists the statement stays on the site where its cohomological input lives; what is open is that
declaration, not the universes.

No affineness is assumed: the equivalence holds for every smooth curve over the algebraically
closed field, covering the affine curve of Tag 03RR and the projective curve of Tag 03RQ alike.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR): clause (3) for an
  affine smooth curve, whose degree-two case this is.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ): the `q = 2` clause for
  a smooth projective curve.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing for
  `𝐆_m`, which supplies the right-hand zero of the segment above.
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8): `H¹(X, 𝐆_m) = Pic(X)`,
  which reads the right-hand side of the equivalence as divisibility of the Picard group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The pinned instance at the coefficient universe `u + 1`

`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve` is stated with its
coefficient universe pinned to `u + 1`, behind a `local instance` that does not leave its file.
The same pin is needed here to elaborate `Sheaf.H` at that universe. -/

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- The second map of the Kummer sequence induces multiplication by `n` on cohomology in every
degree, because it is `n • 𝟙` on the sheaf of units written additively. -/
theorem sheafH_map_kummerSequence_g (X : Scheme.{u}) (n q : ℕ)
    (y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.kummerSequence.{u, u + 1} X n).X₂ q) :
    Sheaf.H.map (Stacks.Kummer.kummerSequence.{u, u + 1} X n).g q y = n • y :=
  Stacks.Cohomology.sheafH_map_nsmul_id n q y

/-- **The degree-two roots-of-unity cohomology of a smooth curve vanishes exactly when
`H¹_étale(X, 𝐆_m)` is `n`-divisible.** Let `X` be a smooth curve over an algebraically closed
field `k` and let `n` be invertible in the ring of global functions on `X`. Then

`H²_étale(X, μ_n) = 0 ↔ n • · : H¹_étale(X, 𝐆_m) → H¹_étale(X, 𝐆_m)` is surjective.

Both directions are the Kummer long exact sequence at
`H²_étale(X, μ_n)` and at `H¹_étale(X, 𝐆_m)` respectively; the forward one needs nothing beyond
short exactness, and the backward one uses
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`, [Stacks, Tag
03RM], in degree two.

Under [Stacks, Tag 03P8] the right-hand side is the `n`-divisibility of `Pic(X)`, which is the
hypothesis the source's proof of clause (3) of [Stacks, Tag 03RR] uses in this degree.
Tag 03RM is used in its unconditional form; no form of [Stacks, Tag 03Q9] is
carried.
This declaration carries no tag because its conclusion is the *affine* curve's degree two,
clause (3) of [Stacks, Tag 03RR], whose rank half is not in this file; the projective curve's
degree two, which is the `q = 2` clause of [Stacks, Tag 03RQ], is
`Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve` below. -/
theorem subsingleton_sheafH_rootsOfUnitySheaf_two_iff_smoothCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    [Smooth g] {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤))) :
    Subsingleton
        (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) 2) ↔
      Function.Surjective
        (fun y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 =>
          n • y) := by
  rw [show (fun y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 =>
        n • y) =
      ⇑(Sheaf.H.map.{u + 1, u + 1} (Stacks.Kummer.kummerSequence.{u, u + 1} X n).g 1) from
    funext fun y => (sheafH_map_kummerSequence_g X n 1 y).symm]
  exact Stacks.Cohomology.subsingleton_sheafH_X₁_iff_surjective_of_shortExact
    (Stacks.Kummer.kummerSequence_shortExact.{u, u + 1} X hn0 hn) 1 2 rfl
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g 2 le_rfl)

/-- **The degree-two roots-of-unity cohomology of a smooth curve vanishes once
`H¹_étale(X, 𝐆_m)` is `n`-divisible**, the direction of
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_iff_smoothCurve` that a
computation consumes. Together with
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve` in the degrees `q ≥ 3`
this gives `H^q_étale(X, μ_n) = 0` for all `q ≥ 2` from that one divisibility statement. -/
theorem subsingleton_sheafH_rootsOfUnitySheaf_two_of_nsmul_surjective {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    [Smooth g] {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (hdiv : Function.Surjective
      (fun y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 =>
        n • y)) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) 2) :=
  (subsingleton_sheafH_rootsOfUnitySheaf_two_iff_smoothCurve g hn0 hn).2 hdiv

/-- **The whole of the degree `≥ 2` vanishing for `μ_n` on a smooth curve, from the
`n`-divisibility of `H¹_étale(X, 𝐆_m)`.** Degree two is
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_of_nsmul_surjective` and the
degrees `q ≥ 3`, where the divisibility is not needed, are
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve`.

The one hypothesis beyond the source's is the `n`-divisibility of `H¹_étale(X, 𝐆_m)`, which is
the source's own input in this degree read through [Stacks, Tag 03P8] as the divisibility of
`Pic(X)`, and it is the ONLY one — no form of [Stacks, Tag 03Q9] is carried. The
`n`-divisibility of all of `Pic(X)` is the affine curve's hypothesis,
false on a projective curve, so this conclusion is clause (3) of [Stacks, Tag 03RR] and not a
clause of [Stacks, Tag 03RQ] — and that is where it is registered. [Stacks, Tag 03RM] is *not*
among the hypotheses: it is used in its unconditional form, so on this site clause
(3) of Tag 03RR costs the divisibility and nothing else.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem subsingleton_sheafH_rootsOfUnitySheaf_two_le_of_nsmul_surjective {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    [Smooth g] {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (hdiv : Function.Surjective
      (fun y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 =>
        n • y))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) q) := by
  rcases eq_or_lt_of_le hq with hq2 | hq3
  · exact hq2 ▸ subsingleton_sheafH_rootsOfUnitySheaf_two_of_nsmul_surjective g hn0 hn hdiv
  · exact subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve g hn0 hn q hq3

/-! ### The value of degree two on a projective curve: `𝐙/n𝐙`

The third term of the Kummer sequence is the same abelian sheaf as `𝐆_m`, and its first term the
same as `μ_n`, but neither pair agrees at `implicit` transparency; so the connecting homomorphism
is restated once, at the `𝐆_m` and `μ_n` spellings, in a private declaration of its own rather
than in a `have` inside the proof below. Everything after that stays in one spelling, and in
particular the two kernels compared below are subgroups of one syntactic group. -/

/-- The Kummer connecting homomorphism `H¹_étale(X, 𝐆_m) ⟶ H²_étale(X, μ_n)`, which is
`Stacks.Cohomology.sheafHBoundary` of the Kummer sequence read at the `𝐆_m` and `μ_n` spellings
of its outer terms. -/
private def kummerBoundaryTwo {X : Scheme.{u}} {n : ℕ}
    (hS : (Stacks.Kummer.kummerSequence.{u, u + 1} X n).ShortExact) :
    Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 →+
      Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) 2 :=
  Stacks.Cohomology.sheafHBoundary hS 1 2 rfl

/-- The Kummer connecting homomorphism out of degree one is onto when `H²_étale(X, 𝐆_m)`
vanishes, which is [Stacks, Tag 03RM] in degree two. -/
private theorem surjective_kummerBoundaryTwo {X : Scheme.{u}} {n : ℕ}
    (hS : (Stacks.Kummer.kummerSequence.{u, u + 1} X n).ShortExact)
    (hGm : Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 2)) :
    Function.Surjective (kummerBoundaryTwo hS) :=
  Stacks.Cohomology.surjective_sheafHBoundary_of_subsingleton hS 1 2 rfl hGm

/-- The Kummer connecting homomorphism out of degree one kills exactly the `n`-divisible classes
of `H¹_étale(X, 𝐆_m)`, the second map of the Kummer sequence inducing multiplication by `n`
there. -/
@[sga "4½ Arcata 2.2.4" "Exactness at H¹(X"]
private theorem kummerBoundaryTwo_eq_zero_iff {X : Scheme.{u}} {n : ℕ}
    (hS : (Stacks.Kummer.kummerSequence.{u, u + 1} X n).ShortExact)
    (y : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1) :
    kummerBoundaryTwo hS y = 0 ↔ ∃ z, y = n • z := by
  refine (Stacks.Cohomology.sheafHBoundary_eq_zero_iff hS 1 2 rfl y).trans ?_
  simp only [sheafH_map_kummerSequence_g]
  exact exists_congr fun z => eq_comm

/-- **`H²_étale(X, μ_n) ≅ 𝐙/n𝐙`** for a smooth curve over an algebraically closed field on which
`H¹_étale(X, 𝐆_m)` carries a degree modulo `n`, which is the `q = 2` clause of the first list of
[Stacks, Tag 03RQ].

On a *projective* curve the degree-two group is not zero: the Kummer segment
`H¹(X, 𝐆_m) --·n--> H¹(X, 𝐆_m) --∂--> H²(X, μ_n) ⟶ H²(X, 𝐆_m) = 0` presents it as the cokernel
of multiplication by `n`, and through [Stacks, Tag 03P8] that cokernel is `Pic(X)/n·Pic(X)`,
which the degree identifies with `𝐙/n𝐙` because `deg : Pic(X) ⟶ 𝐙` is onto and `Pic⁰(X)` is
`n`-divisible. The right-hand zero is [Stacks, Tag 03RM], used here in its unconditional form
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`, so the only
cohomological hypothesis at all: that theorem is unconditional.

The arithmetic input is carried as the homomorphism `d` with its two properties, which say
exactly that `H¹_étale(X, 𝐆_m)` has a degree modulo `n` that is onto `𝐙/n𝐙` and kills precisely
the `n`-divisible classes. That is [Stacks, Tag 03P8] on this site together with the surjectivity
of `AlgebraicGeometry.picardDegree` and the `n`-divisibility of `Pic⁰(X)`; `d` bundles them
because `Pic(X)` itself cannot be named on this site — 03P8 is proved for the small étale site
`AlgebraicGeometry.SmallEtale.topology` of a big étale site, at coefficient universe
`AddCommGrpCat.{u}`, and this site's `𝐆_m` lives at `AddCommGrpCat.{max (u + 1) v}`. The
companion statement on that other site, where the three inputs *are* separately nameable, is
`AlgebraicGeometry.etaleH2RootsOfUnityAddEquivZMod`.

The conclusion is an existence statement because `d` is not canonical: a different degree gives a
different isomorphism. On the other site the isomorphism is pinned by the degree, which is
`AlgebraicGeometry.etaleH2RootsOfUnityAddEquivZMod_apply`.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    [Smooth g] {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (d : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 →+ ZMod n)
    (hdsurj : Function.Surjective d)
    (hdker : ∀ y, d y = 0 ↔ ∃ z, y = n • z) :
    Nonempty
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) 2 ≃+ ZMod n) := by
  have hS := Stacks.Kummer.kummerSequence_shortExact.{u, u + 1} X hn0 hn
  have hker : (kummerBoundaryTwo hS).ker = d.ker := by
    ext y
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hdker,
      kummerBoundaryTwo_eq_zero_iff hS y]
  exact ⟨((QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_kummerBoundaryTwo hS
      (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g 2 le_rfl))).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ hdsurj)⟩

end Stacks.EtaleCohomology

end
