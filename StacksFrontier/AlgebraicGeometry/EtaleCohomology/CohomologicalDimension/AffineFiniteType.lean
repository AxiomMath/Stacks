module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.NoetherNormalization
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula

/-!
# Cohomological dimension of an affine scheme of finite type over a field

[Stacks, Tag 0F0V] (Étale Cohomology, Proposition 59.95.6): let `K` be a field and let `X` be an
affine scheme of finite type over `K`. Then

`cd(X) ≤ dim(X) + cd(K)`.

Here `cd` is the cohomological dimension of [Stacks, Tag 0F0Q],
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension`, and `cd(K)` is that of `Spec(K)`.

The proof is the source's induction on `dim(X)`. Dimension at most one is Stacks 0F0S, that is
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_unbotD_add_of_topologicalKrullDim_le_one`,
which also covers the empty scheme and dimension zero, where `X ⟶ Spec K` is finite. In
dimension `d ≥ 2`, Noether normalization (Stacks 0CBI) gives a finite morphism `X ⟶ 𝔸^d_K`, so
`cd(X) ≤ cd(𝔸^d_K)` (Stacks 03QP and the Leray spectral sequence,
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_affineSpace`), and the bound for `𝔸^d_K`
is the inductive step `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_polynomial_le`:
the Leray spectral sequence for `𝔸^d_K ⊂ ℙ¹ × 𝔸^{d-1}_K ⟶ 𝔸^{d-1}_K`, Interlude I
(`AlgebraicGeometry.isZero_stalk_rightDerived_smallEtalePushforwardAb_of_chart`) and Interlude II
(`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound`, the conditional form
of Stacks 0F0W), all with the induction hypothesis in the dimensions below `d`.

The lemma `AlgebraicGeometry.toENat_trdeg_residueField_le_of_topologicalKrullDim_le` records that
`E_n = {x ∈ X | trdeg_K κ(x) ≤ n}` is all of `X` when `dim(X) ≤ n`: by the dimension formula of
[Stacks, Tag 0A21], `trdeg_K κ(x) ≤ dim_x(X) ≤ dim(X)` at every point. This is what turns
Stacks 0F0W with `a = dim X` back into the present bound.

## Main results

* `AlgebraicGeometry.toENat_trdeg_residueField_le_topologicalKrullDim`: at every point of a
  scheme locally of finite type over a field, the transcendence degree of the residue field is
  at most the dimension of the scheme.
* `AlgebraicGeometry.Scheme.trdegLESet_eq_univ_of_topologicalKrullDim_le`: the same, as
  `E_n = X` for the set `E_n` of Stacks 0F0W.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le`:
  Tag 0F0V, in the form `dim(X) ≤ n → cd(X) ≤ n + cd(K)` for every natural number `n`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_topologicalKrullDim_add`:
  Tag 0F0V verbatim, `cd(X) ≤ dim(X) + cd(K)`, for nonempty `X`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_lt_top_of_isAffine`: `cd(X) < ∞` when
  `cd(K) < ∞`.

## Implementation notes

*The empty scheme.* The dimension is `topologicalKrullDim X : WithBot ℕ∞`, which is `⊥` (the
`−∞` of [Stacks, Tag 0055]) exactly when `X` is empty. For `X = ∅` the source's inequality
reads `cd(∅) ≤ −∞`, and it is false: `cd(∅) = 0`, Definition 0F0Q taking values in
`{0, 1, 2, …} ∪ {∞}`. So the verbatim inequality is stated for nonempty `X`, and the form with
a natural number `n ≥ dim(X)` covers every `X`, the empty one included; for nonempty `X` of
finite dimension the two say the same thing (take `n = dim X`), and for `dim X = ∞` the
verbatim form is trivial.

*Inputs.* Besides the companion results of this directory (Stacks 0F0S, 0F0T in transcendence
degree one and the conditional form of 0F0W), the proof uses Stacks 0F0R
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected`), the
stalk formula for higher direct images (Stacks 03Q9,
`AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`) and Stacks 095U for
`ℙ¹_A ⟶ Spec A` (`AlgebraicGeometry.isZero_rightDerived_etaleAbelianDirectImage_projectiveLine`,
from the proper base change theorem). All of them are proved.

*Coefficients.* As in Definition 0F0Q, abelian sheaves on Mathlib's small étale site have
coefficients in `AddCommGrpCat.{u + 1}`, the universe of objects of the site, and torsion is
the local condition of [Stacks, Tag 0DD7]. The transcendence degree of `κ(x)` over `K` is taken
along the algebra structure induced by the structure morphism through global sections, as in
the dimension theory of Tag 0A21.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry

/-- At every point `x` of a scheme `X` locally of finite type over a field `k`, the
transcendence degree of `κ(x)` over `k` is at most `dim(X)`: by the dimension formula of
[Stacks, Tag 0A21] it is at most `dim_x(X)`, which is at most `dim(X)`. -/
theorem toENat_trdeg_residueField_le_topologicalKrullDim
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) ≤
      topologicalKrullDim X := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  refine le_trans ?_ (topologicalKrullDimAt_le_topologicalKrullDim x)
  rw [topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x]
  exact le_add_of_nonneg_right ringKrullDim_nonneg_of_nontrivial

/-- **`E_n = X` when `dim(X) ≤ n`.** If a scheme `X` locally of finite type over a field `k` has
dimension at most `n`, then every point of `X` lies in `E_n`, the set of points whose residue
field has transcendence degree at most `n` over `k`. -/
theorem toENat_trdeg_residueField_le_of_topologicalKrullDim_le
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {n : ℕ} (hX : topologicalKrullDim X ≤ n) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg k (X.residueField x)) ≤ n := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have h := (toENat_trdeg_residueField_le_topologicalKrullDim k X f x).trans hX
  exact_mod_cast h

namespace Scheme

/-- **`E_n = X` when `dim(X) ≤ n`**, for the set `E_n = Scheme.trdegLESet K f n` of points whose
residue field has transcendence degree at most `n` over `K`. -/
theorem trdegLESet_eq_univ_of_topologicalKrullDim_le (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {n : ℕ} (hX : topologicalKrullDim X ≤ n) :
    trdegLESet K f n = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Cardinal.toENat_le_natCast.1 (toENat_trdeg_residueField_le_of_topologicalKrullDim_le K X f hX x)

/-- **Stacks Project, Tag 0F0V**, for every bound `n` on the dimension. Let `K` be a field and
let `X` be an affine scheme of finite type over `K` with `dim(X) ≤ n`. Then `cd(X) ≤ n + cd(K)`.

The proof is the source's induction on the dimension: dimension at most one is Stacks 0F0S, and
in dimension `d ≥ 2` Noether normalization reduces to `𝔸^d_K`, which is the inductive step
`etaleCohomologicalDimension_spec_polynomial_le`. This form holds for every `X`, the empty one
included; with `n = dim(X)` it is the source's `cd(X) ≤ dim(X) + cd(K)`. -/
@[stacks 0F0V "for every natural number n ≥ dim X, which also covers the empty scheme; the \
literal inequality cd(X) ≤ dim(X) + cd(K) for nonempty X is \
etaleCohomologicalDimension_le_topologicalKrullDim_add",
  sga "4 X 5.2" "special case",
  sga "4 XIV 3.2" "more general"]
theorem etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [IsAffine X] (n : ℕ) (hX : topologicalKrullDim X ≤ n) :
    etaleCohomologicalDimension X ≤ n + etaleCohomologicalDimension (Spec (.of K)) := by
  induction n using Nat.strong_induction_on generalizing K X with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `dim(X) ≤ 1`: Stacks 0F0S
    refine (etaleCohomologicalDimension_le_unbotD_add_of_topologicalKrullDim_le_one f
      (hX.trans (by exact_mod_cast (by omega : n ≤ 1)))).trans (add_le_add ?_ le_rfl)
    induction hd : topologicalKrullDim X using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      rw [hd] at hX
      simpa using WithBot.coe_le_coe.mp hX
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    by_cases hle : topologicalKrullDim X ≤ n'
    · exact (ih n' (by omega) K X f hle).trans
        (add_le_add (by exact_mod_cast Nat.le_succ n') le_rfl)
    -- `dim(X) = n' + 1`: Noether normalization and the inductive step
    have hd : topologicalKrullDim X = ((n' + 1 : ℕ) : ℕ∞) := by
      induction hx : topologicalKrullDim X using WithBot.recBotCoe with
      | bot => rw [hx] at hle; exact absurd bot_le hle
      | coe a =>
        rw [hx] at hle hX
        have h1 : a ≤ ((n' + 1 : ℕ) : ℕ∞) := by exact_mod_cast hX
        have h2 : ¬ a ≤ (n' : ℕ∞) := fun h => hle (by exact_mod_cast h)
        induction a using ENat.recTopCoe with
        | top => exact absurd h1 (by simp)
        | coe a =>
          have h1' : a ≤ n' + 1 := by exact_mod_cast h1
          have h2' : ¬ a ≤ n' := fun h => h2 (by exact_mod_cast h)
          have : a = n' + 1 := by omega
          rw [this]
    refine (etaleCohomologicalDimension_le_affineSpace f (n' + 1) hd).trans ?_
    -- `𝔸^{n'+1}_K ≅ Spec K[t₁, …, t_{n'}][X]`
    let e₁ := AffineSpace.SpecIso (ULift (Fin (n' + 1))) (.of K)
    let e₂ : MvPolynomial (ULift (Fin (n' + 1))) K ≃+* (MvPolynomial (Fin n') K)[X] :=
      ((MvPolynomial.renameEquiv K Equiv.ulift).trans (MvPolynomial.finSuccEquiv K n')).toRingEquiv
    let e := e₁ ≪≫ (Scheme.Spec.mapIso e₂.toCommRingCatIso.op).symm
    refine (etaleCohomologicalDimension_le_of_isIntegralHom e.hom).trans ?_
    exact etaleCohomologicalDimension_spec_polynomial_le n'
      (fun m hm E _ Z _ g _ hZ => ih m (by omega) E Z g hZ) K

/-- **Stacks Project, Tag 0F0V.** Let `K` be a field and let `X` be a nonempty affine scheme of
finite type over `K`. Then `cd(X) ≤ dim(X) + cd(K)`.

The inequality is read in `WithBot ℕ∞`, where `dim(X)` lives. Nonemptiness is needed: for
`X = ∅` the dimension is `−∞` and `cd(∅) = 0`, so the inequality fails; the empty case is covered
by `etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le`. -/
@[stacks 0F0V "verbatim, cd(X) ≤ dim(X) + cd(K) in WithBot ℕ∞, for nonempty X: for X = ∅ the \
source's inequality reads 0 ≤ −∞ and fails; etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le \
covers every X",
  sga "4 X 5.2" "special case",
  sga "5 VII 7.1.1" "a), special case"]
theorem etaleCohomologicalDimension_le_topologicalKrullDim_add
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [IsAffine X] [Nonempty X] :
    (etaleCohomologicalDimension X : WithBot ℕ∞) ≤
      topologicalKrullDim X + (etaleCohomologicalDimension (Spec (.of K)) : WithBot ℕ∞) := by
  have hbot : topologicalKrullDim X ≠ ⊥ := fun h ↦
    not_isEmpty_of_nonempty X ((topologicalKrullDim_eq_bot_iff_isEmpty X).mp h)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  rw [← he]
  induction e using ENat.recTopCoe with
  | top =>
    rw [← WithBot.coe_add, top_add]
    exact WithBot.coe_le_coe.mpr le_top
  | coe n =>
    rw [← WithBot.coe_add]
    exact WithBot.coe_le_coe.mpr
      (etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le
        K X f n (by rw [← he]; exact_mod_cast le_rfl))

/-- **An affine scheme of finite type over a field of finite cohomological dimension has finite
cohomological dimension.** Its dimension is finite
(`AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType`), and Stacks 0F0V bounds
`cd(X)` by `dim(X) + cd(K)`. -/
theorem etaleCohomologicalDimension_lt_top_of_isAffine
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [IsAffine X] (hK : etaleCohomologicalDimension (Spec (.of K)) < ⊤) :
    etaleCohomologicalDimension X < ⊤ := by
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType K f
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X ≤ n := by
    induction hx : topologicalKrullDim X using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe a =>
      rw [hx] at htop
      induction a using ENat.recTopCoe with
      | top => exact absurd rfl htop
      | coe a => exact ⟨a, le_rfl⟩
  refine lt_of_le_of_lt
    (etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le
      K X f n hn) ?_
  exact ENat.add_lt_top.mpr ⟨ENat.coe_lt_top n, hK⟩

end Scheme

end AlgebraicGeometry
