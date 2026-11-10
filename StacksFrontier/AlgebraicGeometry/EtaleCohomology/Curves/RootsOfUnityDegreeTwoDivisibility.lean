module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityDegreeTwoPicard

/-!
# `hdvd` is equivalent to the degree-two clause of Stacks 03RQ, not merely sufficient for it

The four-case registration of [Stacks, Tag 03RQ],
`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_canonical_of_gm`, carries
the hypothesis

> `hdvd : ∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x`

the `n`-divisibility of `Pic⁰(X)`, which is clause (4) of [Stacks, Tag 03RP] for the Picard
scheme of [Stacks, Tag 0BA0]. This file measures what that hypothesis is worth. The answer is
that it cannot be weakened: **it is equivalent to the clause it feeds.**

## What `hdvd` is used for

Exactly one thing. Across the whole tree the `Pic⁰`-shaped `hdvd` is *applied* at exactly one
place — inside `AlgebraicGeometry.picardDegreeZMod_eq_zero_iff`, to prove that the kernel of
`deg mod n` on `Pic(X)` is `n·Pic(X)` — and every other occurrence is a binder passing it along
to that one. (The application in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAffineCurve.lean` is of the
*affine* hypothesis, divisibility of all of `Pic(X)`, which is a different statement.) Its one
use is therefore the inclusion

> `Pic⁰(X) ⊆ n·Pic(X)`.

Two remarks on the shape, both of which close off an apparent weakening.

* The witness `y` of `hdvd` ranges over all of `Pic(X)`, not over `Pic⁰(X)`, so `hdvd` is a priori
  weaker than `n`-divisibility of the *group* `Pic⁰(X)`. It is not: if `n • y = x` and
  `deg x = 0` then `n · deg y = 0` in `𝐙`, so `deg y = 0` for `n ≠ 0` and `y` lies in `Pic⁰(X)`
  anyway.
* The hypothesis is not divisibility of all of `Pic(X)`, which on a projective curve is *false*
  — `Pic(X)` surjects onto `𝐙` — so there is no room to strengthen the spelling either.

## The measurement

The canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` kills exactly `n·Pic(X)`, unconditionally:
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`, which is exactness of the Kummer
sequence at `H¹_ét(X, 𝐆_m)`. So `n·Pic(X)` is already a *named, unconditional* subgroup of
`Pic(X)` — the kernel of the connecting homomorphism — and `hdvd` says precisely that it contains
`Pic⁰(X)`, equivalently that the two canonical surjections of `Pic(X)` in play have the same
kernel. That is the content of the degree-two clause. Concretely:

* `ker_etaleH2RootsOfUnityFromPicard_le_ker_picardDegreeZMod`: one inclusion always holds, with no
  hypothesis at all.
* `exists_nsmul_eq_curvePicardDegreeZero_iff_ker_eq`: `hdvd` holds **if and only if** the two
  kernels are equal.
* `exists_nsmul_eq_of_etaleH2RootsOfUnityAddEquivZMod`: and therefore any degree-normalised
  identification `H²_ét(X, μ_n) ≃ 𝐙/n𝐙` — the degree-two clause of Tag 03RQ in the normalised
  form that `AlgebraicGeometry.etaleH2RootsOfUnityAddEquivZMod_apply` records — *implies* `hdvd`.
  This direction needs neither the surjectivity of the degree nor the vanishing of
  `H²_ét(X, 𝐆_m)`.

So no hypothesis weaker than `hdvd` can discharge the degree-two clause: a weaker hypothesis
sufficient for the clause would, by the last statement, prove `hdvd`. In particular the
candidate weakenings are all dead:

* divisibility only on a subgroup of `Pic⁰(X)` is not enough, because the clause returns the
  inclusion for all of `Pic⁰(X)`;
* a statement about the `n`-*torsion* `Pic⁰(X)[n]` is a different and independent input — it is
  the separate hypothesis `hgenus` of the same registration, used for `q = 1`, and it bears on
  `q = 2` not at all;
* and the surjectivity of `n • ·` onto a quotient of `Pic(X)` is the clause itself.

## Why the elementary routes do not reach it

Recorded here because they are the routes one would try, and each fails for a stateable reason.

* **The Kummer sequence on the curve** is the route the clause already runs on, and it is where
  `n·Pic(X)` acquires its unconditional name. It cannot also supply `Pic⁰(X) ⊆ n·Pic(X)`: that
  inclusion is, by `exists_nsmul_eq_curvePicardDegreeZero_iff_ker_eq`, equivalent to the
  conclusion the sequence is being used to reach.
* **Riemann–Roch and the Abel–Jacobi map.** Surjectivity of `X^g ⟶ Pic^g` — every class of degree
  at least the genus is effective — gives that `Pic⁰(X)` is *generated* by differences of closed
  points. Generation is not divisibility: the group of degree-zero divisors is free abelian, hence
  not `n`-divisible for any `n ≥ 2`, and divisibility of a quotient is not a consequence of
  divisibility of generators. Surjectivity of `n • ·` is a statement about the group structure of
  `Pic⁰(X)`, which on this route is never produced.
* **`Stacks.Models.injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion`** in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/PicardTorsion.lean` is [Stacks, Tag 0CAE]: the
  injectivity of `Pic(X)[h] ⟶ Pic((X_k)_red)[h]` for a regular proper model over a discrete
  valuation ring. It is about `h`-*torsion* of the Picard group of a model over a DVR, not about
  divisibility of `Pic⁰` of a curve over an algebraically closed field, and its implementation
  note about "a quotient of an `n`-divisible, `n`-torsion-free group by a subgroup that is not
  `n`-divisible" is a remark on the kernel of restriction along a thickening, with no `Pic⁰` in
  it. Nothing there is reusable.

What remains is the route the registration already names: an abelian variety with a surjection
onto `Pic⁰(X)`, whose rational points are `n`-divisible because `k` is algebraically closed, fed
through the general `Stacks.Groupoids.exists_nsmul_eq_of_surjective`. The transport is
done; the abelian variety is what is missing, and it is [Stacks, Tag 0B9Z] over the Picard scheme
of [Stacks, Tag 0BA0].

## Main results

* `AlgebraicGeometry.ker_etaleH2RootsOfUnityFromPicard_le_ker_picardDegreeZMod`:
  `n·Pic(X) ⊆ ker(deg mod n)`, unconditionally.
* `AlgebraicGeometry.exists_nsmul_eq_of_ker_picardDegreeZMod_le`: the converse inclusion of
  kernels gives `hdvd`.
* `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_iff_ker_eq`: **`hdvd` is equivalent to
  the equality of the two kernels.**
* `AlgebraicGeometry.exists_nsmul_eq_of_etaleH2RootsOfUnityAddEquivZMod`: **a degree-normalised
  identification `H²_ét(X, μ_n) ≃ 𝐙/n𝐙` implies `hdvd`**, so `hdvd` is necessary for the
  degree-two clause and not merely sufficient.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0CAE](https://stacks.math.columbia.edu/tag/0CAE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

section Curve

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)

include f in
/-- **`n·Pic(X)` is contained in the kernel of `deg mod n`**, with no hypothesis: the degree of
`n • y` is `n` times the degree of `y`.

This is the inclusion of kernels that always holds, the kernel of
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard` being `n·Pic(X)` unconditionally by
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`. The reverse inclusion is `hdvd`. -/
theorem nsmul_le_ker_picardDegreeZMod (x : schemePicard X) (hx : ∃ y, x = n • y) :
    picardDegreeZMod k X f n x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have hdeg : curvePicardDegree k X f (n • y) = (n : ℤ) * curvePicardDegree k X f y := by
    rw [map_nsmul, nsmul_eq_mul]
  change ((curvePicardDegree k X f (n • y) : ℤ) : ZMod n) = 0
  rw [hdeg, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Dvd.intro _ rfl

variable [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

include f in
/-- **The kernel of the canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` is contained in the kernel of
`deg mod n`**, with no hypothesis beyond the invertibility of `n` that the map itself needs.

The first kernel is `n·Pic(X)` by `AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`,
and `nsmul_le_ker_picardDegreeZMod` is the inclusion. -/
theorem ker_etaleH2RootsOfUnityFromPicard_le_ker_picardDegreeZMod (hn : IsUnit (n : k)) :
    (etaleH2RootsOfUnityFromPicard k X f B hX n hn).ker ≤ (picardDegreeZMod k X f n).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx ⊢
  exact nsmul_le_ker_picardDegreeZMod k X f n x
    ((etaleH2RootsOfUnityFromPicard_eq_zero_iff k X f B hX n hn x).1 hx)

include f in
/-- **The reverse inclusion of kernels gives `hdvd`.** If every class whose degree is divisible by
`n` is killed by the canonical map `Pic(X) ⟶ H²_ét(X, μ_n)`, then every degree-zero class is `n`
times a class.

A degree-zero class has degree divisible by `n` outright, so it lies in the kernel of `deg mod n`,
hence in the kernel of the canonical map, which is `n·Pic(X)` by
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`. Neither the surjectivity of the
degree nor the vanishing of `H²_ét(X, 𝐆_m)` is used. -/
theorem exists_nsmul_eq_of_ker_picardDegreeZMod_le (hn : IsUnit (n : k))
    (hle : (picardDegreeZMod k X f n).ker ≤ (etaleH2RootsOfUnityFromPicard k X f B hX n hn).ker)
    (x : schemePicard X) (hx : x ∈ curvePicardDegreeZero k X f) :
    ∃ y, n • y = x := by
  have h0 : curvePicardDegree k X f x = 0 := by
    rw [curvePicardDegreeZero_eq_ker, AddMonoidHom.mem_ker] at hx
    exact hx
  have hker : x ∈ (picardDegreeZMod k X f n).ker := by
    rw [AddMonoidHom.mem_ker]
    change ((curvePicardDegree k X f x : ℤ) : ZMod n) = 0
    rw [h0, Int.cast_zero]
  obtain ⟨y, hy⟩ := (etaleH2RootsOfUnityFromPicard_eq_zero_iff k X f B hX n hn x).1
    (AddMonoidHom.mem_ker.1 (hle hker))
  exact ⟨y, hy.symm⟩

include f in
/-- **`hdvd` is equivalent to the equality of the two kernels.** For a smooth projective curve
over an algebraically closed field, the `n`-divisibility of `Pic⁰(X)` holds if and only if the
canonical map `Pic(X) ⟶ H²_ét(X, μ_n)` and the degree modulo `n` have the same kernel.

The forward direction is `AlgebraicGeometry.ker_etaleH2RootsOfUnityFromPicard_eq`, which is where
`hdvd` is consumed; the backward direction is
`exists_nsmul_eq_of_ker_picardDegreeZMod_le`. Together they say that `hdvd` is not an auxiliary
input to the degree-two clause of [Stacks, Tag 03RQ] but a restatement of it: there is no weaker
hypothesis that would do, because any hypothesis giving the clause gives `hdvd` back. -/
theorem exists_nsmul_eq_curvePicardDegreeZero_iff_ker_eq (hn : IsUnit (n : k))
    (hdeg : Function.Surjective (curvePicardDegree k X f)) :
    (∀ x ∈ curvePicardDegreeZero k X f, ∃ y, n • y = x) ↔
      (etaleH2RootsOfUnityFromPicard k X f B hX n hn).ker =
        (picardDegreeZMod k X f n).ker := by
  constructor
  · intro hdvd
    exact ker_etaleH2RootsOfUnityFromPicard_eq k X f B hX n hn hdeg hdvd
  · intro hker
    exact exists_nsmul_eq_of_ker_picardDegreeZMod_le k X f B hX n hn (le_of_eq hker.symm)

include f in
/-- **A degree-normalised identification `H²_ét(X, μ_n) ≃ 𝐙/n𝐙` implies `hdvd`.** So the
`n`-divisibility of `Pic⁰(X)` is *necessary* for the degree-two clause of [Stacks, Tag 03RQ] in
the normalised form that
`AlgebraicGeometry.etaleH2RootsOfUnityAddEquivZMod_apply` records, and not merely sufficient for
it.

A degree-zero class goes to `0` in `𝐙/n𝐙` under `deg mod n`, hence — by the normalisation — its
image in `H²_ét(X, μ_n)` goes to `0` under the identification, hence is `0` because the
identification is injective, hence the class is `n` times a class by
`AlgebraicGeometry.etaleH2RootsOfUnityFromPicard_eq_zero_iff`.

Neither the surjectivity of the degree nor the vanishing of `H²_ét(X, 𝐆_m)` is used: the
hypothesis `hGm` of the existing construction enters only to make the identification exist, and
here the identification is given. -/
theorem exists_nsmul_eq_of_etaleH2RootsOfUnityAddEquivZMod (hn : IsUnit (n : k))
    (e : Sheaf.H (kummerSmallEtale B X hX n).X₁ 2 ≃+ ZMod n)
    (he : ∀ x : schemePicard X,
      e (etaleH2RootsOfUnityFromPicard k X f B hX n hn x) = picardDegreeZMod k X f n x)
    (x : schemePicard X) (hx : x ∈ curvePicardDegreeZero k X f) :
    ∃ y, n • y = x := by
  refine exists_nsmul_eq_of_ker_picardDegreeZMod_le k X f B hX n hn ?_ x hx
  intro z hz
  rw [AddMonoidHom.mem_ker] at hz ⊢
  refine e.injective ?_
  rw [he z, hz, map_zero]

end Curve

end AlgebraicGeometry

end
