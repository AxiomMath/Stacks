module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupBoundedSiteVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityJacobian
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 03RQ with the vanishing of `𝐆_m` discharged, and its canonical statement

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAllDegrees.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityJacobian.lean` assemble all
eight clauses of [Stacks, Tag 03RQ] over a hypothesis `hGm`, the vanishing of
`H^q_ét(X, 𝐆_m)` for `q ≥ 2` on the size-bounded small étale site of [Stacks, Tag 021B] at
coefficients `AddCommGrpCat.{u}`.  That hypothesis is [Stacks, Tag 03RM], and the library proves
Tag 03RM — on Mathlib's small étale site, at coefficients `AddCommGrpCat.{u + 1}`.

`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve` transports it to the site
and the coefficient universe the computation uses, and this file is those assembled statements
with `hGm` supplied rather than carried — together with the form the source's lemma actually
states, its four *canonical* identifications alone, which needs no genus hypothesis.

## Main results

* `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_gm`: all eight clauses with
  `hGm` and `hdeg` discharged, over `hdvd` and `hgenus`.
* `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm`: all eight
  clauses with `hGm`, `hdeg` and `hdvd` discharged, over `hgenus` and the geometric input that
  `hdvd` stands for.
* `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_gm`: the source's **canonical**
  four identifications alone, with `hGm` and `hdeg` discharged, over `hdvd` — and carrying **no**
  `hgenus`.
* `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_jacobian_of_gm`: the same four,
  with `hdvd` discharged too, over the geometric input it stands for — again with no `hgenus`.

## What remains open

`hgenus`, the identification `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`, which is clause (7) of
[Stacks, Tag 03RP] and has no registration anywhere in this library; the source itself records
that this description of the torsion has no elementary proof.  It is needed only for the second
list's `q = 1` clause.

That is exactly why the two `canonical` statements do not carry it.  The lemma of
[Stacks, Tag 03RQ] states its four identifications `H⁰ = μ_n(k)`, `H¹ = Pic⁰(X)[n]`,
`H² = 𝐙/n𝐙`, `H^q = 0` for `q ≥ 3` and calls them *canonical*; the `(𝐙/n𝐙)^{2g}` shape belongs
to the *second*, constant-coefficient list, which the source itself marks “(noncanonical)” and
which rests on the paragraph above the lemma — `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`, cited to Picard
Schemes of Curves, Section [Stacks, Tag 0B9R] and Groupoids, Section [Stacks, Tag 0BF9], and of
which the source says that it “does not appear to have an elementary proof”.  The canonical list
never mentions the genus, so a statement of it alone needs no genus hypothesis.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

section ProjectiveCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ] with the vanishing of `𝐆_m` discharged.**  This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_closedPoint`
with its `hGm` supplied rather than carried: it is
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, which is
[Stacks, Tag 03RM] read on this site and at this coefficient universe.

The remaining two hypotheses are carried unchanged: `hdvd`, clause (4) of [Stacks, Tag 03RP] on
the Picard scheme of [Stacks, Tag 0BA0], which is discharged in turn on
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm`
below; and `hgenus`, clause (7) of Tag 03RP.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_gm [Smooth f]
    (hn : IsUnit (n : k))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x)
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k X f n) ≃+
      (Fin (2 * genus f) → ZMod n))) :
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
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_closedPoint k X f B hX n hn
    (fun q hq => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq) hdvd hgenus

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ] with the vanishing of `𝐆_m` discharged as well as
the divisibility of `Pic⁰(X)`.**  This is
`etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_closedPoint`
with its `hGm` supplied from
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`.

Only `hgenus` and the geometric input of the Jacobian remain.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_gm
    [Smooth f] (hn : IsUnit (n : k))
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
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_closedPoint
    k X f B hX n hn
    (fun q hq => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq)
    hgenus H hproper hsmooth hconn φ hmul hsurj

/-! ### The canonical statement, with no genus hypothesis

The lemma of [Stacks, Tag 03RQ] states four *canonical* identifications, and `Pic⁰(X)[n]` — not
`(𝐙/n𝐙)^{2g}` — is the one it gives in degree one.  The `(𝐙/n𝐙)^{2g}` shape is the source's
second, constant-coefficient list, which it marks “(noncanonical)”.  So `hgenus` is an input to
the secondary spelling only, and the two statements below, which assert the canonical list and
nothing else, carry no genus hypothesis at all. -/

include f in
/-- **The canonical statement of [Stacks, Tag 03RQ], with no genus hypothesis.** Let `X` be a
smooth projective curve over an algebraically closed field `k` and let `n ≥ 1` be invertible in
`k`.  Then, writing `∂` for `AlgebraicGeometry.etaleH2RootsOfUnityFromPicard` and `deg` for
`AlgebraicGeometry.picardDegree`, there are canonical identifications

* `H⁰_ét(X, μ_n) = μ_n(k)`, by pullback along the structure morphism;
* `H¹_ét(X, μ_n) = Pic⁰(X)[n]`, by the canonical map
  `AlgebraicGeometry.etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion` through the Kummer
  sequence;
* `H²_ét(X, μ_n) = 𝐙/n𝐙`, by the unique isomorphism carrying `∂ x` to `deg x mod n` — `∂` being
  onto, that condition pins the isomorphism down;
* `H^q_ét(X, μ_n) = 0` for `q ≥ 3`.

These are the four identifications the source's lemma actually states, and the source calls them
canonical.  **The genus does not occur in any of them**, so unlike the eight-clause assemblies
above this statement carries no `hgenus`: `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}` is what the source's
*second*, explicitly noncanonical list needs, and that list is not asserted here.

`hGm` ([Stacks, Tag 03RM] on this site) and `hdeg` (surjectivity of the degree) are discharged,
from `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve` and
`AlgebraicGeometry.surjective_curvePicardDegree` respectively.  **CONDITIONAL** on exactly one
hypothesis beyond `hn`, which is a hypothesis of the lemma itself: `hdvd`, the `n`-divisibility
of `Pic⁰(X)`, clause (4) of [Stacks, Tag 03RP] applied to the Picard scheme of
[Stacks, Tag 0BA0].  It is discharged in turn on
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_jacobian_of_gm`
below.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
@[sga "4 IX 4.6" "special case", sga "4½ Arcata 3.3.5", sga "4½ Arcata 4.4" "special case"]
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_gm [Smooth f]
    (hn : IsUnit (n : k))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f B hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
          picardDegreeZMod k X f n x) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  have hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q) :=
    fun q hq => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq
  have hdeg := surjective_curvePicardDegree k X f
  obtain ⟨h0, h1, -, -⟩ :=
    etaleCohomology_rootsOfUnity_smoothProjectiveCurve k X f B hX n hn
  exact ⟨h0, h1, ⟨etaleH2RootsOfUnityAddEquivZMod k X f B hX n hn (hGm 2 le_rfl) hdeg hdvd,
    etaleH2RootsOfUnityAddEquivZMod_apply k X f B hX n hn (hGm 2 le_rfl) hdeg hdvd⟩,
    subsingleton_etaleH_rootsOfUnity_of_three_le k X f B hX n hn hGm⟩

include f in
/-- **The canonical statement of [Stacks, Tag 03RQ] with all three of `hGm`, `hdeg` and `hdvd`
discharged, and still no genus hypothesis.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_gm` with its
`hdvd` supplied from `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_jacobian`: an
open subgroup scheme of a group scheme over `k` that is proper, smooth and connected is an
abelian variety, and multiplication by `n` is onto its `k`-points, so a surjection from those
points onto `Pic⁰(X)` makes `Pic⁰(X)` `n`-divisible.  No Picard scheme is needed; the geometric
input `G`, `H`, `hproper`, `hsmooth`, `hconn`, `φ`, `hmul`, `hsurj` is what `hdvd` is
traded for.

Beyond `hn`, which is a hypothesis of the source lemma itself, that geometric input is all this
statement carries.  In particular it carries **no** `hgenus`: as on the declaration above, the
`(𝐙/n𝐙)^{2g}` shape belongs to the source's second, explicitly noncanonical list, not to the
canonical four asserted here.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
@[sga "4 IX 4.6" "special case",
  sga "4 IX 4.7" "special case",
  sga "4½ Arcata 3.3.5" "partial",
  sga "4½ Arcata 4.4" "special case",
  sga "4½ Dualite 2.5" "partial"]
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_jacobian_of_gm
    [Smooth f] (hn : IsUnit (n : k))
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
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_gm k X f B hX n hn
    (fun x hx => exists_nsmul_eq_curvePicardDegreeZero_of_jacobian k X f n H hproper hsmooth
      hconn (H.flat_zpow_carrier_of_isUnit hproper hsmooth hconn n hn) φ hmul hsurj x hx)

end ProjectiveCurve

end AlgebraicGeometry

end
