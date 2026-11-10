module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve
public import StacksFrontier.AlgebraicGeometry.Picard.ClosedPointDegreeOne
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ShortExactBoundary
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree two and above for the roots of unity on a smooth projective curve

Let `X` be a smooth projective curve over an algebraically closed field `k` and let `n ≥ 1` be
invertible in `k`. This file carries the degrees `q = 2` and `q ≥ 3` of [Stacks, Tag 03RQ] on
the *same* site, and at the same coefficient universe, as the degrees `0` and `1` already
proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve`: the
small étale site `AlgebraicGeometry.SmallEtale.topology` cut out of a big étale site, with
abelian coefficients `AddCommGrpCat.{u}`.

The Kummer sequence `0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` is short exact there, and its second map induces
multiplication by `n` on cohomology, so the long exact sequence has the segment

`H¹(X, 𝐆_m) --·n--> H¹(X, 𝐆_m) --∂--> H²(X, μ_n) --> H²(X, 𝐆_m)`.

Through [Stacks, Tag 03P8], `H¹(X, 𝐆_m) = Pic(X)`, so the connecting homomorphism is a
canonical map `Pic(X) ⟶ H²_ét(X, μ_n)`, and the segment says exactly that it kills precisely
`n·Pic(X)` and has for its image the kernel of `H²(X, μ_n) ⟶ H²(X, 𝐆_m)`. **Both of those are
proved here with no hypothesis beyond the ones the degree-`0` and degree-`1` clauses already
carry**, which is the whole cohomological content of the `q = 2` clause:

`H²_ét(X, μ_n) ⊇ Pic(X)/n·Pic(X)`, canonically, with equality as soon as `H²(X, 𝐆_m) = 0`.

The source's value `𝐙/n𝐙` for that group is then pure algebra, and it is proved here too: the
degree homomorphism `AlgebraicGeometry.picardDegree` has kernel `Pic⁰(X)`, so if it is
surjective and `Pic⁰(X)` is `n`-divisible then `Pic(X)/n·Pic(X) = 𝐙/n𝐙`.

## What is proved unconditionally, and what is carried

Unconditional, under exactly the hypotheses of the proved degree-`0` and degree-`1` clauses:

* `AlgebraicGeometry.etaleH2RootsOfUnityFromPicard`, the canonical map
  `Pic(X) ⟶ H²_ét(X, μ_n)`;
* `AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`, its kernel is `n·Pic(X)`;
* `AlgebraicGeometry.exists_etaleH2RootsOfUnityFromPicard_iff`, its image is the kernel of
  `H²(X, μ_n) ⟶ H²(X, 𝐆_m)`;
* `AlgebraicGeometry.picardDegreeZMod_eq_zero_iff`, the algebra:
  `Pic(X)/n·Pic(X) = 𝐙/n𝐙` from surjectivity of the degree and `n`-divisibility of `Pic⁰(X)`.

Carried as named hypotheses, because the library does not have them:

* `hGm`, the vanishing `H^q_ét(X, 𝐆_m) = 0` for `q ≥ 2`, which is [Stacks, Tag 03RM]. This one is
  **no longer open**: it is
  `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, which carries nothing,
  and the assemblies downstream with it supplied rather than carried are in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegreesGmVanishing`. The
  library proves Tag 03RM as
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`, *unconditionally*
  — no form of [Stacks, Tag 03Q9] is carried there any more, that chain having turned out not to
  need it at any strength — but on Mathlib's
  small étale site `Scheme.smallEtaleTopology` for `Stacks.Kummer.multiplicativeSheaf`, whose
  coefficient universe is `AddCommGrpCat.{max (u + 1) v}` and can therefore never be the
  `AddCommGrpCat.{u}` of this site. This does not block the transport to this site: **the
  asymmetry of coefficient universes is exactly what makes the comparison free.** The site
  comparison is in the library, as the dense subsite
  `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, the
  equivalence of abelian sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv` and the
  cohomological transport
  `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`; and the two sheaves
  of units differ by precisely a postcomposed `AddCommGrpCat.uliftFunctor`, with which
  restriction along the embedding — being precomposition — commutes. So the restriction of
  `Stacks.Kummer.multiplicativeSheaf` *is* the coefficient-universe lift of the middle term of
  `AlgebraicGeometry.kummerSmallEtale`, definitionally; the site comparison runs at
  `AddCommGrpCat.{u + 1}`, and the coefficient universe descends afterwards on this site alone by
  `Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift`. The statements below keep
  `hGm` as an explicit hypothesis, as they keep `hdeg`, so that they stay available over a weaker
  input. On Tag 03RM's own site the first list's degrees `q = 2` and
  `q ≥ 3` are proved with Tag 03RM consumed, as
  `Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve` and
  `Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve`; the second list
  cannot be reached there, the sheaf isomorphism `μ_n ≅ 𝐙/n𝐙` existing only on this site.
* `hdeg`, surjectivity of `AlgebraicGeometry.picardDegree`. This one is **no longer carried**: it
  is `AlgebraicGeometry.surjective_curvePicardDegree` below. On a smooth projective curve over an
  algebraically closed field a closed point is a divisor of degree one, and both halves of that
  are in the library — `AlgebraicGeometry.invertibleCurveDegree_divisorSheaf_eq_one` computes the
  value `1`, and `AlgebraicGeometry.divisorSchemePicardClass` takes the divisor to a class in
  `AlgebraicGeometry.schemePicard`, which is the group the degree is defined on. (The older
  divisor-to-class map `Stacks.Divisors.picardClass` does land in the other spelling
  `Stacks.Picard.ofScheme`, on which no degree homomorphism is defined; it is not what is used.)
  The statements below keep `hdeg` as an explicit hypothesis so that they stay available over a
  weaker base, and the discharged forms are assembled downstream.
* `hdvd`, `n`-divisibility of `Pic⁰(X)`, which is clause (4) of [Stacks, Tag 03RP] applied to
  the Picard scheme of [Stacks, Tag 0BA0] — not a clause of Tag 03RP on its own. The library has
  `Pic⁰(X)` only as the kernel subgroup `AlgebraicGeometry.picardDegreeZero`, with no scheme
  structure and no abelian-variety structure. Of Tag 03RP the library has three registrations:
  commutativity, on `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`;
  clause (3), that `[d]` is onto on an abelian variety, as
  `Stacks.Groupoids.surjective_zpow_id_left_of_flat`; and clause (4), that `A(k)` is divisible
  over an algebraically closed field, as `Stacks.Groupoids.exists_zpow_eq_of_flat` — the last two
  over the flatness of `[d]` as their one hypothesis.
  `Stacks.Groupoids.exists_nsmul_eq_of_surjective` transports clause (4) to any additive group that
  `A(k)` surjects onto, and is the transport that discharges `hdvd` outright once an abelian
  variety is available. So what is missing at `hdvd` is the abelian variety, not the divisibility
  of its rational points. Tag 0BA0 has eleven registrations here, covering clauses (1) to (6), and
  none of them supplies it: `AlgebraicGeometry.picardScheme` is `(picardFunctor …).reprX`,
  conditional on a representability instance the development lacks, and carries no
  `CategoryTheory.GrpObj` and no `AlgebraicGeometry.IsAbelianVariety`.

  Note the spelling: `hdvd` is divisibility of `AlgebraicGeometry.curvePicardDegreeZero`, not of
  all of `schemePicard X`. The latter is the shape the affine curve of [Stacks, Tag 03RR] uses,
  and on a projective curve it is *false* — `Pic(X)` surjects onto `𝐙` — so carrying it here
  would make the clause vacuous.

**This file registers no tag**, but not because carrying another tag's conclusion forbids it: a
hypothesis-carrying registration is this development's practice, and the statements below are
registered downstream, where they are assembled for both lists. All eight clauses of Tag 03RQ
carry the tag on
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegrees`, over exactly the
hypotheses listed above together with `hgenus`; the degrees `q = 0` and `q = 1` keep their own
unconditional registration on
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve`.

## Relation to the two existing degree-two and higher files

`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_two_iff_smoothCurve` and
`Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve` prove the *affine*
shape of these degrees — `H²(X, μ_n) = 0` and `H^q(X, μ_n) = 0` — on Mathlib's small étale site,
which is the shape clause (3) of [Stacks, Tag 03RR] wants. Neither is duplicated here: the
projective curve of Tag 03RQ has `H²_ét(X, μ_n) = 𝐙/n𝐙`, not `0`, because its Picard group is
*not* `n`-divisible — it surjects onto `𝐙` — and what this file adds in that degree is the
cokernel presentation and the named connecting homomorphism, neither of which exists in the
tree. The `q ≥ 3` statement below is the Tag 03RQ-site counterpart of the second of those, and
is a different type, on a different site, at a different coefficient universe.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
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

/-- **The degree homomorphism `deg : Pic(X) ⟶ 𝐙`** of a projective curve, whose kernel is
`AlgebraicGeometry.curvePicardDegreeZero`. -/
abbrev curvePicardDegree : schemePicard X →+ ℤ :=
  picardDegree k f (topologicalKrullDim_le_one_of_isCurve k X f)

omit [IsAlgClosed k] in
/-- `Pic⁰(X)` is the kernel of the degree homomorphism `deg : Pic(X) ⟶ 𝐙`. -/
theorem curvePicardDegreeZero_eq_ker :
    curvePicardDegreeZero k X f = (curvePicardDegree k X f).ker :=
  rfl

/-- **The degree homomorphism of a smooth projective curve is onto `𝐙`.** This is the hypothesis
`hdeg` below, discharged: a closed point of the curve is a Picard class of degree one, by
`AlgebraicGeometry.picardDegree_divisorSchemePicardClass_pointOfClosedPoint_eq_one`, and every
integer is the degree of one of its multiples. -/
theorem surjective_curvePicardDegree [Smooth f] :
    Function.Surjective (curvePicardDegree k X f) :=
  surjective_picardDegree_of_isAlgClosed k f (topologicalKrullDim_le_one_of_isCurve k X f)

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-! ### The connecting homomorphism `Pic(X) ⟶ H²_ét(X, μ_n)` -/

/-- **[Stacks, Tag 03P8] at the quotient term of the Kummer sequence.** The second and third
terms of `AlgebraicGeometry.kummerSmallEtale` are the same abelian sheaf, the second map being
the `n`-th power map of the sheaf of units to itself; so
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup` identifies
`H¹_ét(X, 𝐆_m)` with `Pic(X)` at the third term as well as at the second.

The two spellings agree definitionally but not at `implicit` transparency, so an identification
stated at one of them does not rewrite at the other. `AlgebraicGeometry.etaleH1UnitsEquivPicard`
restates the identification at the second term, which is where degree one needs it; this does
the same at the third, which is where the connecting homomorphism out of degree one starts. Both
are the one source identification, restated rather than transported, exactly as the
implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve`
prescribe. -/
@[sga "6 XIII 3.11" "partial"]
def etaleH1UnitsEquivPicardQuotient :
    Sheaf.H (kummerSmallEtale B X hX n).X₃ 1 ≃+ schemePicard X :=
  Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup B X hX

/-- **The second map of the Kummer sequence is multiplication by `n` on `Pic(X)`**, read through
the two restatements of [Stacks, Tag 03P8] at the second and third terms.

This is `AlgebraicGeometry.kummerSequence_firstCohomologyMap_g` with both ends named, and it is
the only place where the second and third terms of the Kummer sequence have to be compared. The
comparison is by `congrArg`, not by `rw`: the two spellings of the sheaf of units are equal at
default transparency but not at `implicit` transparency, so a rewrite across them fails its
type-correctness check while a term-level application does not. -/
theorem etaleH1UnitsEquivPicardQuotient_map_g
    (y : Sheaf.H (kummerSmallEtale B X hX n).X₂ 1) :
    etaleH1UnitsEquivPicardQuotient X B hX n
        (Sheaf.H.map (kummerSmallEtale B X hX n).g 1 y) =
      n • etaleH1UnitsEquivPicard X B hX n y :=
  (congrArg (etaleH1UnitsEquivPicardQuotient X B hX n)
      (kummerSequence_firstCohomologyMap_g (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n y)).trans
    (map_nsmul (etaleH1UnitsEquivPicard X B hX n) n y)

include f in
/-- **The canonical map `Pic(X) ⟶ H²_ét(X, μ_n)`**: the identification
`Pic(X) = H¹_ét(X, 𝐆_m)` of [Stacks, Tag 03P8] followed by the connecting homomorphism of the
Kummer sequence from degree one to degree two. -/
def etaleH2RootsOfUnityFromPicard (hn : IsUnit (n : k)) :
    schemePicard X →+ Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 :=
  (Stacks.Cohomology.sheafHBoundary
      (kummerSmallEtale_shortExact k X f B hX n hn) 1 2 rfl).comp
    (etaleH1UnitsEquivPicardQuotient X B hX n).symm.toAddMonoidHom

include f in
omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
/-- `etaleH2RootsOfUnityFromPicard` is the Kummer connecting homomorphism applied to the class in
`H¹_ét(X, 𝐆_m)` of a line bundle. -/
@[simp] theorem etaleH2RootsOfUnityFromPicard_apply (hn : IsUnit (n : k))
    (x : schemePicard X) :
    etaleH2RootsOfUnityFromPicard k X f B hX n hn x =
      Stacks.Cohomology.sheafHBoundary
        (kummerSmallEtale_shortExact k X f B hX n hn) 1 2 rfl
        ((etaleH1UnitsEquivPicardQuotient X B hX n).symm x) :=
  rfl

include f in
omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
/-- **The canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` kills exactly `n·Pic(X)`.** This is exactness
of the Kummer long exact sequence at `H¹_ét(X, 𝐆_m)`, the second map of the Kummer sequence
inducing multiplication by `n` there. So the map presents `Pic(X)/n·Pic(X)` as a subgroup of
`H²_ét(X, μ_n)`. -/
@[sga "4 IX 4.6" "special case", sga "4½ Arcata 2.2.4" "partial"]
theorem etaleH2RootsOfUnityFromPicard_eq_zero_iff (hn : IsUnit (n : k))
    (x : schemePicard X) :
    etaleH2RootsOfUnityFromPicard k X f B hX n hn x = 0 ↔ ∃ y, x = n • y := by
  rw [etaleH2RootsOfUnityFromPicard_apply,
    Stacks.Cohomology.sheafHBoundary_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨etaleH1UnitsEquivPicard X B hX n z, ?_⟩
    rw [← etaleH1UnitsEquivPicardQuotient_map_g X B hX n z, hz, AddEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨(etaleH1UnitsEquivPicard X B hX n).symm y,
      (etaleH1UnitsEquivPicardQuotient X B hX n).injective
        ((etaleH1UnitsEquivPicardQuotient_map_g X B hX n
          ((etaleH1UnitsEquivPicard X B hX n).symm y)).trans (by simp))⟩

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
include f in
/-- **The image of `Pic(X) ⟶ H²_ét(X, μ_n)` is the kernel of
`H²_ét(X, μ_n) ⟶ H²_ét(X, 𝐆_m)`.** This is exactness of the Kummer long exact sequence at
`H²_ét(X, μ_n)`. -/
theorem exists_etaleH2RootsOfUnityFromPicard_iff (hn : IsUnit (n : k))
    (w : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2) :
    (∃ x, etaleH2RootsOfUnityFromPicard k X f B hX n hn x = w) ↔
      Sheaf.H.map (kummerSmallEtale B X hX n).f 2 w = 0 := by
  rw [← Stacks.Cohomology.exists_sheafHBoundary_iff
    (kummerSmallEtale_shortExact k X f B hX n hn) 1 2 rfl w]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(etaleH1UnitsEquivPicardQuotient X B hX n).symm x,
      (etaleH2RootsOfUnityFromPicard_apply k X f B hX n hn x).symm.trans hx⟩
  · rintro ⟨z, hz⟩
    refine ⟨etaleH1UnitsEquivPicardQuotient X B hX n z, ?_⟩
    rwa [etaleH2RootsOfUnityFromPicard_apply, AddEquiv.symm_apply_apply]

include f in
omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] in
/-- **`H²_ét(X, μ_n) = Pic(X)/n·Pic(X)`, the canonical map being onto, once
`H²_ét(X, 𝐆_m) = 0`.** The vanishing is [Stacks, Tag 03RM] in the spelling of this site; see the
module documentation for why it is carried rather than discharged. -/
theorem surjective_etaleH2RootsOfUnityFromPicard (hn : IsUnit (n : k))
    (hGm : Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ 2)) :
    Function.Surjective (etaleH2RootsOfUnityFromPicard k X f B hX n hn) := fun w =>
  (exists_etaleH2RootsOfUnityFromPicard_iff k X f B hX n hn w).2 (hGm.elim _ _)

/-! ### `Pic(X)/n·Pic(X) = 𝐙/n𝐙` -/

/-- The degree homomorphism of the curve read modulo `n`. Its kernel is the set of classes whose
degree is divisible by `n`. -/
abbrev picardDegreeZMod : schemePicard X →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (curvePicardDegree k X f)

include f in
omit [IsAlgClosed k] in
/-- **`deg mod n` is onto `𝐙/n𝐙`** when the degree homomorphism is onto `𝐙`. -/
theorem surjective_picardDegreeZMod
    (hdeg : Function.Surjective (curvePicardDegree k X f)) :
    Function.Surjective (picardDegreeZMod k X f n) := fun z => by
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  obtain ⟨x, hx⟩ := hdeg m
  exact ⟨x, by simpa [hx] using hm⟩

include f in
omit [IsAlgClosed k] in
/-- **`Pic(X)/n·Pic(X) = 𝐙/n𝐙`**, as the statement that `deg mod n` kills exactly `n·Pic(X)`.

The two hypotheses are the exact sequence `0 ⟶ Pic⁰(X) ⟶ Pic(X) ⟶ 𝐙 ⟶ 0` and the
`n`-divisibility of its left-hand term; `Pic⁰(X)` being the kernel of the degree is
`AlgebraicGeometry.curvePicardDegreeZero_eq_ker`, so nothing else about the curve enters. Given
a class `x` of degree `n·m` and a class `b` of degree one, `x - n·(m·b)` has degree zero, hence
is `n·c` for some `c`, and `x = n·(c + m·b)`. -/
theorem picardDegreeZMod_eq_zero_iff
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x)
    (x : schemePicard X) :
    picardDegreeZMod k X f n x = 0 ↔ ∃ y, x = n • y := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ : (n : ℤ) ∣ curvePicardDegree k X f x := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hx
    obtain ⟨b, hb⟩ := hdeg 1
    have hc : x - n • (m • b) ∈ curvePicardDegreeZero k X f := by
      simp [curvePicardDegreeZero_eq_ker, hb, hm]
    obtain ⟨c, hcc⟩ := hdvd _ hc
    refine ⟨c + m • b, ?_⟩
    rw [smul_add, hcc]
    abel
  · rintro ⟨y, rfl⟩
    simp

include f in
omit [IsAlgClosed k] in
/-- **The canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` and the degree modulo `n` have the same
kernel**, namely `n·Pic(X)`: the first by
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`, unconditionally, and the second
by `AlgebraicGeometry.picardDegreeZMod_eq_zero_iff` under the two hypotheses recorded there. -/
theorem ker_etaleH2RootsOfUnityFromPicard_eq (hn : IsUnit (n : k))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x) :
    (etaleH2RootsOfUnityFromPicard k X f B hX n hn).ker =
      (picardDegreeZMod k X f n).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker,
    etaleH2RootsOfUnityFromPicard_eq_zero_iff k X f B hX n hn x,
    picardDegreeZMod_eq_zero_iff k X f n hdeg hdvd x]

include f in
/-- **`H²_ét(X, μ_n) = 𝐙/n𝐙`** for a smooth projective curve over an algebraically closed field,
the `q = 2` clause of the first list of [Stacks, Tag 03RQ].

The three hypotheses are the ones the library does not have, each named in the module
documentation: `hGm` is [Stacks, Tag 03RM] on this site, `hdeg` is surjectivity of the degree,
and `hdvd` is the `n`-divisibility of `Pic⁰(X)`, which is [Stacks, Tag 03RP] for the Picard
scheme of [Stacks, Tag 0BA0]. Given them, both `deg mod n` and the canonical map
`Pic(X) ⟶ H²_ét(X, μ_n)` are surjections of `Pic(X)` with the same kernel `n·Pic(X)`, so the two
quotients agree. The identification is therefore not canonical in either direction on its own —
it depends on the chosen splitting of neither, but it is read off from the degree, which is
canonical, so the resulting isomorphism is canonical too. -/
def etaleH2RootsOfUnityAddEquivZMod (hn : IsUnit (n : k))
    (hGm : Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ 2))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x) :
    Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_etaleH2RootsOfUnityFromPicard k X f B hX n hn hGm)).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq
      (ker_etaleH2RootsOfUnityFromPicard_eq k X f B hX n hn hdeg hdvd))).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_picardDegreeZMod k X f n hdeg))

include f in
omit [IsAlgClosed k] in
/-- **The identification `H²_ét(X, μ_n) = 𝐙/n𝐙` is normalised by the degree**: it carries the
canonical image of a Picard class in `H²_ét(X, μ_n)` to the degree of that class modulo `n`.

This is what makes the identification canonical rather than merely an isomorphism of abstract
groups: the two surjections of `Pic(X)` it is built from are the canonical boundary and the
canonical degree, and this says the triangle they form commutes. It is also the normalisation
that `Stacks.EtaleCohomology.RootsOfUnityH2Degree` asks of a degree-two identification. -/
theorem etaleH2RootsOfUnityAddEquivZMod_apply (hn : IsUnit (n : k))
    (hGm : Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ 2))
    (hdeg : Function.Surjective (curvePicardDegree k X f))
    (hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x)
    (x : schemePicard X) :
    etaleH2RootsOfUnityAddEquivZMod k X f B hX n hn hGm hdeg hdvd
        (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
      picardDegreeZMod k X f n x := by
  rw [etaleH2RootsOfUnityAddEquivZMod, AddEquiv.trans_apply, AddEquiv.trans_apply]
  have h₁ : (QuotientAddGroup.quotientKerEquivOfSurjective
      (etaleH2RootsOfUnityFromPicard k X f B hX n hn)
        (surjective_etaleH2RootsOfUnityFromPicard k X f B hX n hn hGm)).symm
        (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) =
      QuotientAddGroup.mk x := by
    rw [AddEquiv.symm_apply_eq]
    simp [QuotientAddGroup.quotientKerEquivOfSurjective]
  rw [h₁]
  rfl

end Curve

section KScheme

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

/-! ### The degrees `q ≥ 3` -/

include f in
/-- **`H^q_ét(X, μ_n) = 0` for every `q ≥ 3`**, the `q ≥ 3` clause of the first list of
[Stacks, Tag 03RQ], on the site of that tag's other clauses.

Both outer terms of the Kummer segment
`H^{q-1}(X, 𝐆_m) ⟶ H^q(X, μ_n) ⟶ H^q(X, 𝐆_m)` vanish, since `q - 1 ≥ 2` and `q ≥ 2`; the
divisibility of `Pic(X)` that degree two needs does not enter. The hypothesis `hGm` is
[Stacks, Tag 03RM] on this site; see the module documentation for why it is carried. -/
theorem subsingleton_etaleH_rootsOfUnity_of_three_le (hn : IsUnit (n : k))
    (hGm : ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₂ q))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
  exact Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact
    (kummerSmallEtale_shortExact k X f B hX n hn) p (p + 1) rfl
    (hGm (p + 1) (by lia)) (hGm p (by lia))

end KScheme

end AlgebraicGeometry

end
