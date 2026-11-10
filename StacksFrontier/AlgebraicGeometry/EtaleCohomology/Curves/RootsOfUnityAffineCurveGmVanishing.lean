module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupBoundedSiteVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityJacobian
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 03RR with the vanishing of `𝐆_m` discharged

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAffineCurve.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityJacobian.lean` assemble
clauses (2) and (3) of [Stacks, Tag 03RR] over a hypothesis `hGm`, the vanishing of
`H^q_ét(X, 𝐆_m)` for `q ≥ 2` on the size-bounded small étale site of [Stacks, Tag 021B] at
coefficients `AddCommGrpCat.{u}`.  That hypothesis is [Stacks, Tag 03RM], and the library proves
Tag 03RM — on Mathlib's small étale site, at coefficients `AddCommGrpCat.{u + 1}`.

`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve` transports it to the site
and the coefficient universe the computation uses, and this file is those assembled statements
with `hGm` supplied rather than carried.  It is the exact counterpart, for the affine curve of
Tag 03RR, of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAllDegreesGmVanishing.lean`
for the projective curve of [Stacks, Tag 03RQ].

## Main results

* `subsingleton_etaleH_rootsOfUnity_affineSmoothCurve_three_le`: the degrees `q ≥ 3` of clause
  (3), **unconditionally** — no hypothesis beyond the lemma's own.
* `etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_gm`: clauses (1) and (3),
  over `hdvd` alone.  Neither the rank count nor the genus occurs.
* `etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_jacobian_of_gm`: the same
  two clauses with `hdvd` discharged as well, over the geometric input it stands for.
* `etaleCohomology_rootsOfUnity_affineSmoothCurve_of_gm`: all three clauses, over `hunits`,
  `htors`, `hrank` and `hdvd`.
* `etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_gm`: all three clauses with
  `hdvd` discharged too, over the rank count and the geometric input.

## Clause (2) and the rank count

Unlike [Stacks, Tag 03RQ], whose lemma states four *canonical* identifications and relegates the
`(𝐙/n𝐙)^{2g}` shape to a second list it marks “(noncanonical)”, the lemma of
[Stacks, Tag 03RR] has only one list, and its degree-one clause is stated in the
genus-and-puncture-indexed form `H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g + r - 1}` and in no other.  So there
is no canonical spelling of clause (2) to retreat to: the rank count `hrank` is part of what the
source asserts in that clause, not an artefact of this formalization, and the statements above
that avoid it avoid clause (2) itself.  Clauses (1) and (3), by contrast, are stated canonically
by the source — `H⁰_ét(X, μ_n) = μ_n(k)` and `H^q_ét(X, μ_n) = 0` for `q ≥ 2` — and the genus
occurs in neither, which is why the two `clauses_one_three` statements carry no rank count.

## What remains open

* `hdvd`, the `n`-divisibility of `Pic(X)`, which the source gets from the surjection
  `Pic⁰(X̄) ↠ Pic(X)` of [Stacks, Tag 0BA0] together with [Stacks, Tag 03RP].  Reduced here to
  the geometric input of `AlgebraicGeometry.exists_nsmul_eq_schemePicard_of_jacobian`; what is
  missing is the abelian-variety structure on the Picard scheme and the surjection, not the
  divisibility of the rational points.
* `hunits`, `htors` and `hrank`, the rank count of clause (2).  `htors` is clause (7) of
  [Stacks, Tag 03RP], which has no registration anywhere in this library and of which the source
  itself records that it has no elementary proof; the exact rank of the units quotient is
  *false* in general, only the inequality
  `Stacks.AlgebraicGeometry.UnitsBoundaryValuations.units_quotient_free_finrank_lt_of_isNormal`
  being a theorem.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

section AffineCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **`H^q_ét(X, μ_n) = 0` for every `q ≥ 3` on a smooth curve, unconditionally** — the degrees
above two of clause (3) of [Stacks, Tag 03RR], on the site of that tag's other clauses.

This is `AlgebraicGeometry.subsingleton_etaleH_rootsOfUnity_of_three_le` with its `hGm` supplied
rather than carried, from
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`, which is
[Stacks, Tag 03RM] read on this site and at this coefficient universe.  Both outer terms of the
Kummer segment `H^{q-1}(X, 𝐆_m) ⟶ H^q(X, μ_n) ⟶ H^q(X, 𝐆_m)` vanish, so the divisibility of
`Pic(X)` that degree two needs does not enter — and with `hGm` gone there is nothing left to
carry.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
@[sga "4 IX 4.6" "special case"]
theorem subsingleton_etaleH_rootsOfUnity_affineSmoothCurve_three_le (hn : IsUnit (n : k))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  subsingleton_etaleH_rootsOfUnity_of_three_le k X f B hX n hn
    (fun q' hq' => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q' hq') q hq

include f in
/-- **Clauses (1) and (3) of [Stacks, Tag 03RR], over the divisibility of `Pic(X)` alone.** Let
`X` be a smooth curve over an algebraically closed field `k` and let `n` be invertible in `k`.
Then

* `H⁰_ét(X, μ_n) = μ_n(k)`, by pullback along the structure morphism;
* `H^q_ét(X, μ_n) = 0` for every `q ≥ 2`.

Both are canonical statements of the source's lemma, and the genus and the number of punctures
occur in neither, so neither the rank count of clause (2) nor any genus hypothesis is carried
here: this is clauses (1) and (3) and nothing else.

`hGm` is discharged, from
`AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`. **CONDITIONAL** on
exactly one hypothesis beyond `hn`: `hdvd`, the `n`-divisibility of `Pic(X)`, which is needed
only in degree two. It is discharged in turn on
`etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_jacobian_of_gm` below.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_gm
    (hn : IsUnit (n : k)) (hdvd : ∀ x : schemePicard X, ∃ y, x = n • y) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  refine ⟨baseRootsToEtaleH0_bijective_of_isIntegral B k X hX f n
    (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast k n hn)), fun q hq => ?_⟩
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · obtain rfl : q = 2 := by lia
    exact subsingleton_etaleH2_rootsOfUnity_of_divisible k X f B hX n hn
      (subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n 2 le_rfl) hdvd
  · exact subsingleton_etaleH_rootsOfUnity_affineSmoothCurve_three_le k X f B hX n hn q hq3

include f in
/-- **Clauses (1) and (3) of [Stacks, Tag 03RR] with the divisibility of `Pic(X)` discharged as
well.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_gm` with
its `hdvd` replaced by the geometric input it stands for, through
`AlgebraicGeometry.exists_nsmul_eq_schemePicard_of_jacobian`: an abelian variety — the
degree-zero Picard scheme of the compactification — whose rational points surject onto `Pic(X)`.
The flatness of `[n]` on it is not carried: it holds because `n` is invertible in `k`, by
`AlgebraicGeometry.OpenSubgroupScheme.flat_zpow_carrier_of_isUnit`.

Nothing else is carried. In particular no rank count, no genus and no `HasExt`-level hypothesis
beyond the instance the site needs.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_jacobian_of_gm
    (hn : IsUnit (n : k))
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → schemePicard X)
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_gm k X f B hX n hn
    (exists_nsmul_eq_schemePicard_of_jacobian k X n H hproper hsmooth hconn
      (H.flat_zpow_carrier_of_isUnit hproper hsmooth hconn n hn) φ hmul hsurj)

include f in
/-- **All three clauses of [Stacks, Tag 03RR] with the vanishing of `𝐆_m` discharged.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve` with its `hGm` supplied rather
than carried: it is `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`,
which is [Stacks, Tag 03RM] read on this site and at this coefficient universe.

The remaining four hypotheses are carried unchanged: `hunits`, `htors` and `hrank`, the rank
count of the degree-one sequence, and `hdvd`, the `n`-divisibility of `Pic(X)`, which is
discharged in turn on
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_gm` below.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_gm (hn : IsUnit (n : k))
    {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j]
    (r : ℕ) {a b : ℕ}
    (hunits : Nonempty (↥(etaleH1RootsOfUnityToPicard X B hX n).ker ≃+ (Fin a → ZMod n)))
    (htors : Nonempty (↥(picardNTorsion X n) ≃+ (Fin b → ZMod n)))
    (hrank : a + b = 2 * genus fbar + r - 1)
    (hdvd : ∀ x : schemePicard X, ∃ y, x = n • y) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve k X f B hX n hn fbar j r hunits htors
    hrank (fun q hq => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq) hdvd

include f in
/-- **All three clauses of [Stacks, Tag 03RR] with the vanishing of `𝐆_m` discharged as well as
the divisibility of `Pic(X)`.** This is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian` with its `hGm`
supplied from `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`.

Only the rank count `hunits`, `htors`, `hrank` and the geometric input that `hdvd` stands for
remain.

This is a partial form of [Stacks, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR); the full
statement is
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_gm (hn : IsUnit (n : k))
    {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j]
    (r : ℕ) {a b : ℕ}
    (hunits : Nonempty (↥(etaleH1RootsOfUnityToPicard X B hX n).ker ≃+ (Fin a → ZMod n)))
    (htors : Nonempty (↥(picardNTorsion X n) ≃+ (Fin b → ZMod n)))
    (hrank : a + b = 2 * genus fbar + r - 1)
    {G : Grp (Over (Spec (.of k)))} (H : OpenSubgroupScheme G)
    (hproper : IsProper H.carrier.X.hom) (hsmooth : Smooth H.carrier.X.hom)
    (hconn : ConnectedSpace H.carrier.X.left)
    (φ : (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) → schemePicard X)
    (hmul : ∀ a' b', φ (a' * b') = φ a' + φ b') (hsurj : Function.Surjective φ) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian k X f B hX n hn fbar j r
    hunits htors hrank
    (fun q hq => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve f B hX n q hq)
    H hproper hsmooth hconn φ hmul hsurj

end AffineCurve

end AlgebraicGeometry

end
