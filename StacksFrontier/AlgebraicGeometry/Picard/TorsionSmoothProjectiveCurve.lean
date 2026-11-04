module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyTorsionStructure
public import StacksFrontier.GroupTheory.TorsionByIntKer

/-!
# Torsion in the Picard group of a smooth projective curve

Let `k` be an algebraically closed field and let `X` be a smooth projective curve of genus `g`
over `k`.  [Stacks, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z) says

1. if `n ≥ 1` is invertible in `k` then `Pic(X)[n] ≅ (ℤ/nℤ)^{⊕2g}`, and
2. if `char k = p > 0` then there is an integer `0 ≤ f ≤ g` with
   `Pic(X)[p^m] ≅ (ℤ/p^mℤ)^{⊕f}` for every `m ≥ 1`.

The source's proof is three lines long.  It writes down the short exact sequence

`0 → Pic⁰(X) → Pic(X) --deg--> ℤ → 0`,

identifies `Pic⁰(X)` with the group of `k`-points of `Pic⁰_{X/k}`, which is a `g`-dimensional
abelian variety over `k` (Picard Schemes of Curves, Lemma 44.6.7, Tag 0BA0), and then quotes the
torsion structure of an abelian variety (Groupoids, Proposition 39.9.11, Tag 03RP).  Both clauses
of 0C1Z are that quotation transported across the two identifications, and that transport is what
this file contains.

## Where Tag 0C1Z is registered

This module contains the transport step of the source's proof in an abstract form: the Picard
group is an abstract abelian group `P` with a degree homomorphism, and `Pic⁰_{X/k}` an abelian
variety `A` whose `k`-points are identified with `ker degree`. The two theorems below take that
identification (`hker`), the dimension (`hdim`) and the torsion of `A` (`hdeg`, resp. `htors`) as
data; they are not registrations of Tag 0C1Z.

Tag 0C1Z itself is registered, with nothing assumed beyond the source's hypotheses, on
`Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve` (clause (1)) and
`Stacks.Picard.exists_rank_torsionBy_prime_pow_addEquiv_pi_zmod_of_smoothProjectiveCurve`
(clause (2)) in `Picard/TorsionSmoothProjectiveCurve/Unconditional.lean`. There `Pic⁰_{X/k}` is
`Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme`, an abelian variety of dimension `g` by
`Stacks.PicardFunctor.isAbelianVariety_degreeZeroOpenSubgroupScheme`, and the torsion of an
abelian variety is
`AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod_of_isUnit` and
`AlgebraicGeometry.IsAbelianVariety.exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod`.

## Main definitions

* `Stacks.Picard.torsionByDegreeKerAddEquiv`: the `m`-torsion of the Picard group is the
  `m`-torsion of the group of `k`-points of `Pic⁰_{X/k}`, for `m ≠ 0`.

## Main results

* `Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_abelianVariety`: the content of clause (1)
  of Tag 0C1Z, transported from an abstract Jacobian.
* `Stacks.Picard.exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod_of_abelianVariety`:
  the same for clause (2).

The registered, unconditional forms are in
`Picard/TorsionSmoothProjectiveCurve/Unconditional.lean`.

## Implementation notes

The Picard group is kept as an abstract abelian group `P` carrying a degree homomorphism.  That is
a generalisation, not a weakening: this library has several parallel spellings of the Picard group
of a scheme (`AlgebraicGeometry.Scheme.picardGroup`, `Stacks.Picard.ofScheme`,
`Stacks.SheafOfModules.PicardGroup`), and leaving `P` abstract lets an instantiation pick
whichever one the Jacobian uses.  It also makes the universes work out: a Picard group of
a scheme in `Scheme.{u}` lives in `Type (u + 1)` while the group of `k`-points lives in
`Type u`.

The genus is `AlgebraicGeometry.genus`, Tag 0BY7, and the dimension of the abelian variety is
`Stacks.Groupoids.abelianVarietyDimension`; `hdim` relates them, which is where the `g` of the
source enters.  No hypothesis is placed on `X` or on `f : X ⟶ Spec k` beyond `hdim`: smoothness,
properness and dimension one are used by the source only to produce `Pic⁰_{X/k}` and the degree
map, and those are hypotheses here, so demanding them again would be an added hypothesis and
nothing else.

The `m`-torsion is `Submodule.torsionBy ℤ`, matching
`StacksFrontier/GroupTheory/TorsionCardinalityZMod.lean` and the library's form of Tag 03RP.  The
equivalences are asserted through `Nonempty`, as in the source, which chooses them
noncanonically; the ones at different `m` in clause (2) need not be compatible.

## References

* [Stacks Project, Lemma 53.17.1 (Tag 0C1Z)](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Lemma 44.6.7 (Tag 0BA0)](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Lemma 39.9.8 (Tag 0BFG)](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Lemma 39.9.9 (Tag 0BFH)](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Lemma 39.9.10 (Tag 0C0Y)](https://stacks.math.columbia.edu/tag/0C0Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.MonObj

namespace Stacks.Picard

universe u v w

/-- **The `m`-torsion of the Picard group is the `m`-torsion of the degree-zero part**, for
`m ≠ 0`.

This is the whole of the source's first step for Tag 0C1Z: an `m`-torsion Picard class has degree
`0` because `ℤ` is torsion free, so it already lies in `Pic⁰(X) = ker degree`, which `e` then
identifies with the group of `k`-points of `Pic⁰_{X/k}`. -/
def torsionByDegreeKerAddEquiv {P : Type v} [AddCommGroup P] {H : Type w} [AddCommGroup H]
    (degree : P →+ ℤ) (e : degree.ker ≃+ H) {m : ℤ} (hm : m ≠ 0) :
    Submodule.torsionBy ℤ P m ≃+ Submodule.torsionBy ℤ H m :=
  (AddCommGroup.torsionByIntKerAddEquiv degree hm).trans
    (Stacks.Models.DVRArith.torsionByCongr' e.toIntLinearEquiv m).toAddEquiv

/-- **Tag 0C1Z, clause (1), transported from an abstract Jacobian.** Let `k` be an algebraically
closed field, let `f : X ⟶ Spec k` be a scheme over `k` of genus `g = genus f`, and let `P` be its
Picard group, equipped with its degree homomorphism `degree : P →+ ℤ`.  Suppose, as Tag 0BA0
asserts for a smooth projective curve, that `Pic⁰_{X/k}` is an abelian variety `A` over `k` of
dimension `g` (`hdim`) whose group of `k`-points is the degree-zero part of `P` (`hker`).  Then
for every `n ≥ 1` invertible in `k` such that every divisor `d` of `n` has the point count of
Tag 0BFG (`hdeg`),

`P[n] ≅ (ℤ/nℤ)^{⊕2g}`.

See the module documentation for why `hdim`, `hker` and `hdeg` are hypotheses and for the source
of the derivation. -/
theorem nonempty_torsionBy_addEquiv_pi_zmod_of_abelianVariety {k : Type u} [Field k]
    [IsAlgClosed k] {P : Type v} [AddCommGroup P] (degree : P →+ ℤ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (hdim : Stacks.Groupoids.abelianVarietyDimension A = genus f)
    (hker : letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
      degree.ker ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k))
    (hdeg : ∀ d : ℕ, d ∣ n →
      Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]}
        = d ^ (2 * Stacks.Groupoids.abelianVarietyDimension A)) :
    Nonempty (Submodule.torsionBy ℤ P (n : ℤ) ≃+ (Fin (2 * genus f) → ZMod n)) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨e⟩ := IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod A n hn hnk hdeg
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [← hdim]
  exact ⟨(torsionByDegreeKerAddEquiv degree hker hnz).trans e⟩

/-- **Tag 0C1Z, clause (2), transported from an abstract Jacobian.** Let `k` be an algebraically
closed field of characteristic `p > 0`, let `f : X ⟶ Spec k` be a scheme over `k` of genus
`g = genus f`, and let `P` be its Picard group with its degree homomorphism `degree : P →+ ℤ`.
Suppose, as Tag 0BA0 asserts for a smooth projective curve, that `Pic⁰_{X/k}` is an abelian
variety `A` over `k` of dimension `g` (`hdim`) whose group of `k`-points is the degree-zero part
of `P` (`hker`), and suppose the characteristic-`p` clause of Tag 03RP for `A` (`htors`).  Then
there is an integer `0 ≤ r ≤ g` with

`P[p^m] ≅ (ℤ/p^mℤ)^{⊕r}` for every `m ≥ 1`,

one and the same `r` for all `m`; this is the source's `f`, renamed because `f` is the structure
morphism here.  See the module documentation for why `hdim`, `hker` and `htors` are hypotheses and
for the source of the derivation. -/
theorem exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod_of_abelianVariety
    {k : Type u} [Field k] [IsAlgClosed k] {P : Type v} [AddCommGroup P] (degree : P →+ ℤ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (hdim : Stacks.Groupoids.abelianVarietyDimension A = genus f)
    (hker : letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
      degree.ker ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (htors : letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
      ∃ r : ℕ, r ≤ Stacks.Groupoids.abelianVarietyDimension A ∧ ∀ m : ℕ, 1 ≤ m →
        Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
          ((p : ℤ) ^ m) ≃+ (Fin r → ZMod (p ^ m)))) :
    ∃ r : ℕ, r ≤ genus f ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty (Submodule.torsionBy ℤ P ((p : ℤ) ^ m) ≃+ (Fin r → ZMod (p ^ m))) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨r, hr, h⟩ := htors
  refine ⟨r, hdim ▸ hr, fun m hm => ?_⟩
  obtain ⟨e⟩ := h m hm
  have hnz : ((p : ℤ) ^ m) ≠ 0 := pow_ne_zero m (by exact_mod_cast hp.ne')
  exact ⟨(torsionByDegreeKerAddEquiv degree hker hnz).trans e⟩

end Stacks.Picard

end
