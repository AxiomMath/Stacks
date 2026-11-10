module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnitySupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale cohomology of a smooth projective curve in every degree, and the genus

Let `X` be a smooth projective curve over an algebraically closed field `k` and let `n ≥ 1` be
invertible in `k`. [Stacks, Tag 03RQ] gives two lists of four identifications each:

```
H^q_ét(X, μ_n)   = μ_n(k),  Pic⁰(X)[n],  𝐙/n𝐙,  0        for q = 0, 1, 2, q ≥ 3;
H^q_ét(X, 𝐙/n𝐙) = 𝐙/n𝐙,    (𝐙/n𝐙)^{2g}, 𝐙/n𝐙,  0        for q = 0, 1, 2, q ≥ 3,
```

the second list being noncanonical, since `μ_n ≅ 𝐙/n𝐙` only after a choice of primitive root.
Degrees `0` and `1` of both lists are proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve`, where
Tag 03RQ is registered, except that the second list's degree `1` is stated there as `Pic⁰(X)[n]`
rather than `(𝐙/n𝐙)^{2g}`. Degree `2` and the degrees `q ≥ 3` of the first list are proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard`. This file
transports those to the second list along the isomorphism of abelian sheaves
`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`, puts the genus into the second list's
degree `1`, and assembles all eight clauses into one statement.

## The genus

`AlgebraicGeometry.genus` is `dim_k H¹(X, 𝒪_X)`, and it is what enters the source's
`(𝐙/n𝐙)^{2g}`. The shape is equivalent to `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`, which is the `n`-torsion
of a `g`-dimensional abelian variety: the Picard scheme of [Stacks, Tag 0BA0] together with
clause (7) of [Stacks, Tag 03RP]. Both of those tags have registrations in this library — Tag
0BA0 eleven of them, covering clauses (1) to (6), and Tag 03RP three, its commutativity clause
and clauses (3) and (4) — but clause (7) of Tag 03RP, the structure of the `n`-torsion of an
abelian variety, has none, and none of the Tag 0BA0 registrations puts an
`AlgebraicGeometry.IsAbelianVariety` structure on the degree-zero Picard scheme. So the
identification is carried here as the hypothesis `hgenus` and nothing below asserts that it
holds. What is proved is that it is the *only* missing step: granted it, the second list's degree
`1` has the source's shape, with the genus of the curve literally in the statement.

## Main results

* `AlgebraicGeometry.nonempty_etaleH2ConstantZModAddEquiv` —
  **`H²_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`**.
* `AlgebraicGeometry.subsingleton_etaleH_constantZMod_of_three_le` —
  **`H^q_ét(X, 𝐙/n𝐙) = 0` for `q ≥ 3`**.
* `AlgebraicGeometry.nonempty_etaleH1ConstantZModAddEquivGenusPow` —
  **`H¹_ét(X, 𝐙/n𝐙) ≅ (𝐙/n𝐙)^{2g}`**, the genus entering the statement.
* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees` — all eight
  clauses of Tag 03RQ in one statement, forwarding to
  `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve` for the four it proves
  unconditionally. This is where Tag 03RQ is registered for the degrees `q = 2` and `q ≥ 3` of
  both lists.

## What the registration below carries

The assembly carries Tag 03RQ for all eight clauses, over four explicit named hypotheses — not
axioms, and not weakenings of any clause — none of which is the conclusion of another clause of
the same statement:

* `hGm`, `H^q_ét(X, 𝐆_m) = 0` for `q ≥ 2` **on this site**, which is [Stacks, Tag 03RM];
* `hdeg`, surjectivity of `AlgebraicGeometry.picardDegree`;
* `hdvd`, the `n`-divisibility of `Pic⁰(X)`, which is [Stacks, Tag 03RP] clause (4) applied to
  the Jacobian, hence Tag 03RP together with [Stacks, Tag 0BA0];
* `hgenus`, `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`, which is clause (7) of Tag 03RP, likewise on the Picard
  scheme of Tag 0BA0.

All four are discussed in detail in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard`.

`hGm` is the one of the four that the library *does* prove, and it is discharged:
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve` is Tag 03RM over
the unrestricted [Stacks, Tag 03Q9], and it is stated on Mathlib's small étale site
`AlgebraicGeometry.Scheme.smallEtaleTopology` for `Stacks.Kummer.multiplicativeSheaf`, whose
coefficient universe is `AddCommGrpCat.{max (u + 1) v}` and can therefore never be the
`AddCommGrpCat.{u}` of this site. The two coefficient universes do not have to agree. The sites
are compared in the library — the dense subsite
`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, the equivalence of abelian sheaf
categories `AlgebraicGeometry.SmallEtale.sheafEquiv`, and the cohomological transport
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` — and the restriction of
`Stacks.Kummer.multiplicativeSheaf` along the embedding *is*, definitionally, the
coefficient-universe lift of the middle term of `AlgebraicGeometry.kummerSmallEtale`; so the site
comparison runs at `AddCommGrpCat.{u + 1}` and the coefficient universe descends afterwards, on
this site alone, by `Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift`. That
transport is `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, and the
form of this statement with `hGm` discharged from it is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_gm`. On
Tag 03RM's own site the same two degrees are registered separately, as
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve` and
`Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve`, where
Tag 03RM *is* consumed and only its `h03Q9` is carried; those cover the first list only, the
isomorphism of abelian sheaves `μ_n ≅ 𝐙/n𝐙` existing only on this site.

The declaration carries the tag although it takes another tag's conclusion as a hypothesis;
every such hypothesis is named in the attribute string.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-- The constant sheaf `𝐙/n𝐙` on the small étale site of `X`, the coefficient sheaf of the
second list of [Stacks, Tag 03RQ]. -/
abbrev smallEtaleConstantZModSheaf (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (n : ℕ) : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u} :=
  (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} (ZMod n)))

/-- For `n` invertible in `k`, cohomology of the constant sheaf `𝐙/n𝐙` is isomorphic to that of
`μ_n`, in every degree. -/
private theorem nonempty_etaleH_constantZMod_addEquiv_rootsOfUnity (g : X ⟶ Spec (.of k))
    (hn : IsUnit (n : k)) (q : ℕ) :
    Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q ≃+
      Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  ⟨sheafHAddEquivOfIso (SmallEtale.topology B X hX)
    (constantZModSheafIsoRootsOfUnitySheaf B k g hX n
      (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast k n hn)) hn) q⟩

include f in
/-- **`H²_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`**, the `q = 2` clause of the noncanonical list of
[Stacks, Tag 03RQ]: the constant sheaf is `μ_n`, whose degree-two cohomology is `𝐙/n𝐙`.

The hypotheses are those of `AlgebraicGeometry.etaleH2RootsOfUnityAddEquivZMod`, unchanged. The
identification is asserted as the existence of an isomorphism, as the source's second list is
noncanonical: the sheaf isomorphism it is transported along depends on a choice of isomorphism
`𝐙/n𝐙 ≅ μ_n(k)`. -/
theorem nonempty_etaleH2ConstantZModAddEquiv [Smooth f] (hn : IsUnit (n : k))
    (hGm : Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ 2))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x) :
    Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 2 ≃+ ZMod n) := by
  obtain ⟨e⟩ := nonempty_etaleH_constantZMod_addEquiv_rootsOfUnity k X B hX n f hn 2
  exact ⟨e.trans (etaleH2RootsOfUnityAddEquivZMod k X f B hX n hn hGm hdeg hdvd)⟩

omit [IsCurve k f] [IsProjectiveVariety k f] in
include f in
/-- **`H^q_ét(X, 𝐙/n𝐙) = 0` for every `q ≥ 3`**, the `q ≥ 3` clause of the noncanonical list of
[Stacks, Tag 03RQ]: the constant sheaf is `μ_n`, whose cohomology vanishes in those degrees by
`AlgebraicGeometry.subsingleton_etaleH_rootsOfUnity_of_three_le`. The hypothesis `hGm` is
[Stacks, Tag 03RM] on this site. -/
theorem subsingleton_etaleH_constantZMod_of_three_le [Smooth f] (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q) := by
  have := subsingleton_etaleH_rootsOfUnity_of_three_le k X f B hX n hn hGm q hq
  obtain ⟨e⟩ := nonempty_etaleH_constantZMod_addEquiv_rootsOfUnity k X B hX n f hn q
  exact e.injective.subsingleton

include f in
/-- **`H¹_ét(X, 𝐙/n𝐙) ≅ (𝐙/n𝐙)^{2g}`**, the `q = 1` clause of the noncanonical list of
[Stacks, Tag 03RQ] in the shape the source gives it, with `g` the genus
`AlgebraicGeometry.genus` of the curve.

`AlgebraicGeometry.nonempty_etaleH1ConstantZModAddEquiv` already identifies this group with
`Pic⁰(X)[n]`; the content of the source's shape is therefore exactly the hypothesis `hgenus`,
that the `n`-torsion of `Pic⁰(X)` is `(𝐙/n𝐙)^{2g}`. That is the `n`-torsion of a
`g`-dimensional abelian variety, which is [Stacks, Tag 03RP] applied to the Picard scheme of
[Stacks, Tag 0BA0]; the library has neither, so it is carried rather than discharged, and this
theorem is the statement that it is the only thing standing between the proved degree-one clause
and the source's. -/
theorem nonempty_etaleH1ConstantZModAddEquivGenusPow [Smooth f] (hn : IsUnit (n : k))
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k X f n) ≃+
      (Fin (2 * genus f) → ZMod n))) :
    Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) 1 ≃+
      (Fin (2 * genus f) → ZMod n)) := by
  obtain ⟨eg⟩ := hgenus
  obtain ⟨e1⟩ := nonempty_etaleH1ConstantZModAddEquiv k X f B hX n hn
  exact ⟨e1.trans eg⟩

include f in
/-- **The étale cohomology of a smooth projective curve with roots-of-unity and with constant
cyclic coefficients, in every degree: all eight clauses of [Stacks, Tag 03RQ].** Let `X` be a
smooth projective curve of genus `g` over an algebraically closed field `k` and let `n ≥ 1` be
invertible in `k`. Then, writing `∂` for the canonical map
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard` and `deg` for
`AlgebraicGeometry.picardDegree`:

* `H⁰_ét(X, μ_n) = μ_n(k)`, by pullback along the structure morphism;
* `H¹_ét(X, μ_n) = Pic⁰(X)[n]`, by the canonical map through the Kummer sequence;
* `H²_ét(X, μ_n) = 𝐙/n𝐙`, by the unique isomorphism carrying `∂ x` to `deg x mod n` — `∂` being
  onto, that condition pins the isomorphism, so this identification is canonical;
* `H^q_ét(X, μ_n) = 0` for `q ≥ 3`;
* `H⁰_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`;
* `H¹_ét(X, 𝐙/n𝐙) ≅ (𝐙/n𝐙)^{2g}`;
* `H²_ét(X, 𝐙/n𝐙) ≅ 𝐙/n𝐙`;
* `H^q_ét(X, 𝐙/n𝐙) = 0` for `q ≥ 3`.

The first list's identifications are canonical, each asserted of a named map; the second list's
are the source's noncanonical ones and are asserted as the existence of an isomorphism.

**CONDITIONAL**, on four hypotheses, none of them the conclusion of any clause above: `hGm`, the
vanishing of `H^q_ét(X, 𝐆_m)` for `q ≥ 2` on this site, which is [Stacks, Tag 03RM]; `hdeg`,
surjectivity of the degree homomorphism on `Pic(X)`; `hdvd`, the `n`-divisibility of `Pic⁰(X)`,
which is clause (4) of [Stacks, Tag 03RP] applied to the Picard scheme of [Stacks, Tag 0BA0]; and
`hgenus`, the identification `Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`, which is clause (7) of Tag 03RP on that
same scheme. All four are named in the attribute string. Three of them the library does not have;
`hdeg` it does, as `AlgebraicGeometry.surjective_curvePicardDegree`, and
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_closedPoint`
below is this statement with `hdeg` discharged. The four clauses this forwards to are taken
unchanged from the unconditional
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve`, which keeps its own
registration of Tag 03RQ for them.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
@[sga "4½ Arcata 3.3.5" "partial"]
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees [Smooth f]
    (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
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
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf B X hX n) q) := by
  obtain ⟨h0, h1, h0c, _⟩ :=
    etaleCohomology_rootsOfUnity_smoothProjectiveCurve k X f B hX n hn
  refine ⟨h0, h1, ⟨etaleH2RootsOfUnityAddEquivZMod k X f B hX n hn (hGm 2 le_rfl) hdeg hdvd,
    etaleH2RootsOfUnityAddEquivZMod_apply k X f B hX n hn (hGm 2 le_rfl) hdeg hdvd⟩,
    subsingleton_etaleH_rootsOfUnity_of_three_le k X f B hX n hn hGm, h0c,
    nonempty_etaleH1ConstantZModAddEquivGenusPow k X f B hX n hn hgenus,
    nonempty_etaleH2ConstantZModAddEquiv k X f B hX n hn (hGm 2 le_rfl) hdeg hdvd,
    subsingleton_etaleH_constantZMod_of_three_le k X f B hX n hn hGm⟩

include f in
/-- **All eight clauses of [Stacks, Tag 03RQ] with the surjectivity of the degree discharged.**
This is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees` with
its `hdeg` supplied rather than carried: a closed point of a smooth projective curve over an
algebraically closed field is a Picard class of degree one, so the degree homomorphism is onto
`𝐙`. That is `AlgebraicGeometry.surjective_curvePicardDegree`, and it needs nothing beyond what
this statement already carries.

The remaining three hypotheses are carried unchanged: `hGm`, which is [Stacks, Tag 03RM] on this
site and is proved as `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`,
the form of this statement with it discharged being
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_gm`;
`hdvd`, clause (4) of [Stacks, Tag 03RP] on the
Picard scheme of [Stacks, Tag 0BA0]; and `hgenus`, clause (7) of Tag 03RP. They are discussed
where they are carried.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_closedPoint [Smooth f]
    (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
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
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees k X f B hX n hn hGm
    (surjective_curvePicardDegree k X f) hdvd hgenus

end Curve

end AlgebraicGeometry

end
