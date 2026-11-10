module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicardContraction
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicardDecomposition

/-!
# `Pic(X) = Pic(X') ⊕ ℤ` for a contraction, with exactness as the only hypothesis

Let `b : X ⟶ X'` contract an exceptional curve of the first kind `E ⊆ X`, presented by its ideal
sheaf `D` together with an isomorphism `e : 𝐏¹_k ≅ E` carrying the normal sheaf to `𝒪(-1)`. The
short exact sequence

`0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0`

of the contraction yields the direct-sum decomposition

`Pic(X) = Pic(X') ⊕ ℤ`,

in which `ℒ` corresponds to the pair `(ℒ', n)` exactly when `ℒ = (b^*ℒ')(-nE)`, equivalently
`ℒ(nE) = b^*ℒ'`; `ℒ'` is `b_*ℒ(nE)` for any pushforward `b_*` left inverse to `b^*`; and
`ℒ ↦ ℒ'` is a group homomorphism.

## Relation to `ExceptionalCurvePicardDecomposition.lean`

That file proves the same four assertions of Tag 0C5M from the hypothesis
`Scheme.IdealSheafData.ContractionPicardSplitting`, which bundles *two* unproved halves of
Tag 0C5L — a pushforward `b_*` on Picard classes left inverse to `b^*`, and exactness at
`Pic(X)` — and whose degree map `exceptionalDegreeHom` is parametrised by an identification
`φ : ℤ ≃+ Pic(𝐏¹_k)`.

The declarations here instead take the contraction itself,
`IsContractionOfExceptionalCurve D b`, and use the unparametrised `ℤ`-valued degree
`Scheme.IdealSheafData.exceptionalDegree` of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurvePicardContraction.lean`. That leaves
exactness at `Pic(X)` as the one hypothesis, carried as
`Scheme.IdealSheafData.ContractionPicardExactness`; no pushforward is assumed, since the
homomorphism `ℒ ↦ ℒ'` constructed here is itself a left inverse to `b^*`
(`Scheme.IdealSheafData.contractedPicardHomOfExactness_schemePullbackClassHom`). The two
developments are independent and neither supersedes the other: the names here are suffixed
`OfExactness` so that both are available.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ContractionPicardExactness` — exactness at `Pic(X)`:
  a class of degree zero on the exceptional curve is pulled back along `b`.
* `AlgebraicGeometry.Scheme.IdealSheafData.contractedClass` — the class `ℒ'` on `X'` with
  `ℒ(nE) = b^*ℒ'`.
* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecompositionOfExactness` — **the identification
  `Pic(X) ≃+ Pic(X') × ℤ`.**
* `AlgebraicGeometry.Scheme.IdealSheafData.contractedPicardHomOfExactness` — **the group
  homomorphism `ℒ ↦ ℒ'`.**

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecompositionOfExactness_eq_iff` and
  `AlgebraicGeometry.Scheme.IdealSheafData.picardDecompositionOfExactness_eq_iff_exceptionalTwist`
  — **`ℒ` corresponds to `(ℒ', n)` if and only if `ℒ = (b^*ℒ')(-nE)`, equivalently
  `ℒ(nE) = b^*ℒ'`.**
* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecompositionOfExactness_apply_fst` —
  **`ℒ' = b_*ℒ(nE)`** for every pushforward `b_*` on Picard classes left inverse to `b^*`, and
  `AlgebraicGeometry.Scheme.IdealSheafData.picardDecompositionOfExactness_apply_snd` — `n` is the
  degree of `ℒ` on the exceptional curve.
* `AlgebraicGeometry.Scheme.IdealSheafData.contractedPicardHomOfExactness_schemePullbackClassHom`
  — the homomorphism `ℒ ↦ ℒ'` *is* such a left inverse, so one exists.

## How the hypothesis is discharged

Everything here is proved from the contraction itself — `IsContractionOfExceptionalCurve`, which
exhibits `X` as the blowup of a regular two-dimensional closed point of `X'` — except for one
clause of the short exact sequence, carried as the hypothesis `ContractionPicardExactness`: that
a class of degree zero on the exceptional curve is pulled back along `b`. Injectivity of `b^*`
is `Scheme.IdealSheafData.injective_schemePullbackClassHom_of_isContraction`, the vanishing of
the degree on classes pulled back along `b` is
`Scheme.IdealSheafData.exceptionalDegree_schemePullbackClassHom`, and the splitting
`n ↦ 𝒪_X(-nE)` with the degree it computes is
`Scheme.IdealSheafData.exceptionalDegree_negativeExceptionalMultiple`. The remaining clause is
the one the source deduces from `b_*ℒ` being invertible with `b^*b_*ℒ ⟶ ℒ` an isomorphism.

That clause is proved, from the contraction and nothing else, in
`StacksFrontier/AlgebraicGeometry/Surfaces/ContractionPicardDescent.lean`:
`AlgebraicGeometry.Scheme.IdealSheafData.contractionPicardExactness_of_isContraction`, with
`AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_pushforward_of_isContraction` and
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_counit_app_of_isContraction` for the source's two
clauses about `b_*ℒ`. So the hypothesis of every declaration here is dischargeable for a general
contraction, and the decomposition holds outright
(`AlgebraicGeometry.Scheme.IdealSheafData.picardDecomposition_of_isContraction`, which carries
the Tag 0C5M registration for the unconditional statement). It is kept as a hypothesis so that
the statements here read as the source's do and stay usable for any other proof of the clause —
for instance `AlgebraicGeometry.contractionPicardExactness_exceptionalIdealData`, which gets it
for the blowup of a regular local ring of dimension two from the generation half of
[Stacks, Tag 0C5G](https://stacks.math.columbia.edu/tag/0C5G)
(`AlgebraicGeometry.surjective_zsmul_picardClass_exceptionalIdealData`): there `Pic(X)` is
infinite cyclic on a class of degree `-1`, so a class of degree zero is zero. That last argument
is special to the local base, since for a general `b` the kernel of the degree is `b^*Pic(X')`,
which is nonzero whenever `Pic(X')` is.

## Implementation notes

**`𝒪_X(-nE)` and `ℒ(nE)`.** The splitting `n ↦ [𝒪_X(-nE)]` is the `ℤ`-multiple homomorphism
`Scheme.IdealSheafData.negativeExceptionalMultipleHom`. Dually `ℒ(nE)` is
`Scheme.IdealSheafData.exceptionalTwist` of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurvePicardDecomposition.lean`, defined there
as `[ℒ] + n • [𝒪_X(E)]`; the two are related by
`Scheme.IdealSheafData.exceptionalTwist_eq_sub_negativeExceptionalMultipleHom`, and the
decomposition is written through whichever of the two makes a statement read as the source does.

**The pushforward.** The library has no pushforward on Picard classes, so the source's formula
`ℒ' = b_*ℒ(nE)` is stated for every homomorphism `Pic(X) ⟶ Pic(X')` that is a left inverse to
`b^*` — a class of properties, not an assumed object — and `contractedPicardHomOfExactness` is
exhibited as one such.

## References

* [Stacks Project, Tag 0C5M](https://stacks.math.columbia.edu/tag/0C5M)
* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)
  (b : X ⟶ X')

/-! ### The twist by the exceptional curve -/

/-- `ℒ(0E)` is `ℒ`. -/
public theorem exceptionalTwist_zero (L : Stacks.Picard.ofScheme X) :
    D.exceptionalTwist 0 L = L := by
  rw [exceptionalTwist_def, zero_zsmul, add_zero]

/-- Twisting `(b^*ℒ')(-nE)` by `nE` returns `b^*ℒ'`. -/
public theorem exceptionalTwist_schemePullback_add_negativeMultiple
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.exceptionalTwist n (Stacks.Picard.schemePullbackClassHom b L' +
      negativeExceptionalMultipleHom D n) = Stacks.Picard.schemePullbackClassHom b L' := by
  rw [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom]
  exact add_sub_cancel_right _ _

/-- `ℒ(nE)` has degree zero on the exceptional curve when `n` is the degree of `ℒ` there. -/
public theorem exceptionalDegree_exceptionalTwist_self
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    D.exceptionalDegree k e (D.exceptionalTwist (D.exceptionalDegree k e L) L) = 0 := by
  rw [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom, map_sub,
    exceptionalDegree_negativeExceptionalMultiple (D := D) (k := k) (e := e) (hE := hE),
    sub_self]

/-- The twist by the degree is additive: `(ℒ₁ ⊗ ℒ₂)(mE + nE)` is `ℒ₁(mE) ⊗ ℒ₂(nE)` when `m` and
`n` are the degrees of `ℒ₁` and `ℒ₂` on the exceptional curve. -/
public theorem exceptionalTwist_self_add (L₁ L₂ : Stacks.Picard.ofScheme X) :
    D.exceptionalTwist (D.exceptionalDegree k e (L₁ + L₂)) (L₁ + L₂) =
      D.exceptionalTwist (D.exceptionalDegree k e L₁) L₁ +
        D.exceptionalTwist (D.exceptionalDegree k e L₂) L₂ := by
  rw [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom,
    exceptionalTwist_eq_sub_negativeExceptionalMultipleHom,
    exceptionalTwist_eq_sub_negativeExceptionalMultipleHom,
    map_add (D.exceptionalDegree k e), map_add (negativeExceptionalMultipleHom D)]
  exact add_sub_add_comm _ _ _ _

/-- `(b^*ℒ')(-nE)` has degree `n` on the exceptional curve. -/
public theorem exceptionalDegree_schemePullback_add_negativeMultiple
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.exceptionalDegree k e (Stacks.Picard.schemePullbackClassHom b L' +
      negativeExceptionalMultipleHom D n) = n := by
  rw [map_add,
    exceptionalDegree_schemePullbackClassHom (D := D) (k := k) (e := e) (b := b) (hb := hb),
    exceptionalDegree_negativeExceptionalMultiple (D := D) (k := k) (e := e) (hE := hE),
    zero_add]

/-! ### Exactness at `Pic(X)` -/

/-- **Exactness at `Pic(X)` of the Picard sequence of the contraction `b`**: every Picard class
of degree zero on the exceptional curve is pulled back along `b`. -/
public abbrev ContractionPicardExactness : Prop :=
  ∀ L : Stacks.Picard.ofScheme X, D.exceptionalDegree k e L = 0 →
    ∃ L' : Stacks.Picard.ofScheme X', Stacks.Picard.schemePullbackClassHom b L' = L

/-- **The class `ℒ'` on `X'` with `ℒ(nE) = b^*ℒ'`**, for `n` the degree of `ℒ` on the exceptional
curve: the twist `ℒ(nE)` has degree zero there, hence is a pullback. -/
public def contractedClass (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.ofScheme X' :=
  (hker _ (D.exceptionalDegree_exceptionalTwist_self k e hE L)).choose

/-- `b^*ℒ' = ℒ(nE)` for `ℒ'` the contracted class of `ℒ` and `n` the degree of `ℒ` on the
exceptional curve. -/
public theorem schemePullbackClassHom_contractedClass
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.schemePullbackClassHom b (D.contractedClass k e b hker hE L) =
      D.exceptionalTwist (D.exceptionalDegree k e L) L :=
  (hker _ (D.exceptionalDegree_exceptionalTwist_self k e hE L)).choose_spec

/-- The contracted class is additive, since `b^*` is injective and `ℒ ↦ ℒ(nE)` with `n` the
degree of `ℒ` is additive. -/
public theorem contractedClass_add (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L₁ L₂ : Stacks.Picard.ofScheme X) :
    D.contractedClass k e b hker hE (L₁ + L₂) =
      D.contractedClass k e b hker hE L₁ + D.contractedClass k e b hker hE L₂ := by
  refine injective_schemePullbackClassHom_of_isContraction (D := D) (b := b) (hb := hb) ?_
  rw [map_add, D.schemePullbackClassHom_contractedClass k e b hker hE,
    D.schemePullbackClassHom_contractedClass k e b hker hE,
    D.schemePullbackClassHom_contractedClass k e b hker hE,
    D.exceptionalTwist_self_add k e]

/-! ### The decomposition -/

/-- **The assignment `ℒ ↦ ℒ'` is a group homomorphism.** It sends `ℒ` to the unique class `ℒ'` on
`X'` with `ℒ(nE) = b^*ℒ'`, where `n` is the degree of `ℒ` on the exceptional curve. -/
public def contractedPicardHomOfExactness (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X' :=
  AddMonoidHom.mk' (D.contractedClass k e b hker hE) (D.contractedClass_add k e b hb hker hE)

/-- The homomorphism `ℒ ↦ ℒ'` sends `ℒ` to its contracted class. -/
public theorem contractedPicardHomOfExactness_apply
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    D.contractedPicardHomOfExactness k e b hb hker hE L = D.contractedClass k e b hker hE L :=
  rfl

/-- **The homomorphism `ℒ ↦ ℒ'` is a left inverse to `b^*`**, so a pushforward of the kind the
source's formula `ℒ' = b_*ℒ(nE)` names exists. -/
public theorem contractedPicardHomOfExactness_schemePullbackClassHom
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L' : Stacks.Picard.ofScheme X') :
    D.contractedPicardHomOfExactness k e b hb hker hE
      (Stacks.Picard.schemePullbackClassHom b L') = L' := by
  refine injective_schemePullbackClassHom_of_isContraction (D := D) (b := b) (hb := hb) ?_
  rw [contractedPicardHomOfExactness_apply, D.schemePullbackClassHom_contractedClass k e b hker hE,
    exceptionalDegree_schemePullbackClassHom (D := D) (k := k) (e := e) (b := b) (hb := hb),
    exceptionalTwist_zero]

/-- Composing `ℒ ↦ (ℒ', n)` with `(ℒ', n) ↦ (b^*ℒ')(-nE)` is the identity on `Pic(X)`. -/
public theorem picardDecompositionOfExactness_left_inv
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.schemePullbackClassHom b
        (D.contractedPicardHomOfExactness k e b hb hker hE L) +
      negativeExceptionalMultipleHom D (D.exceptionalDegree k e L) = L := by
  rw [contractedPicardHomOfExactness_apply, D.schemePullbackClassHom_contractedClass k e b hker hE,
    exceptionalTwist_eq_sub_negativeExceptionalMultipleHom]
  exact sub_add_cancel _ _

/-- Composing `(ℒ', n) ↦ (b^*ℒ')(-nE)` with `ℒ ↦ (ℒ', n)` is the identity on `Pic(X') × ℤ`. -/
public theorem picardDecompositionOfExactness_right_inv
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    (D.contractedPicardHomOfExactness k e b hb hker hE
          (Stacks.Picard.schemePullbackClassHom b L' + negativeExceptionalMultipleHom D n),
        D.exceptionalDegree k e (Stacks.Picard.schemePullbackClassHom b L' +
          negativeExceptionalMultipleHom D n)) = (L', n) := by
  have hd := D.exceptionalDegree_schemePullback_add_negativeMultiple k e b hb hE L' n
  rw [Prod.mk.injEq]
  refine ⟨injective_schemePullbackClassHom_of_isContraction (D := D) (b := b) (hb := hb) ?_, hd⟩
  rw [contractedPicardHomOfExactness_apply,
    D.schemePullbackClassHom_contractedClass k e b hker hE, hd,
    D.exceptionalTwist_schemePullback_add_negativeMultiple b]

/-- The map `ℒ ↦ (ℒ', n)` is additive. -/
public theorem picardDecompositionOfExactness_map_add
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L₁ L₂ : Stacks.Picard.ofScheme X) :
    (D.contractedPicardHomOfExactness k e b hb hker hE (L₁ + L₂),
        D.exceptionalDegree k e (L₁ + L₂)) =
      (D.contractedPicardHomOfExactness k e b hb hker hE L₁, D.exceptionalDegree k e L₁) +
        (D.contractedPicardHomOfExactness k e b hb hker hE L₂, D.exceptionalDegree k e L₂) := by
  rw [Prod.mk_add_mk, Prod.mk.injEq]
  exact ⟨map_add (D.contractedPicardHomOfExactness k e b hb hker hE) L₁ L₂,
    map_add (D.exceptionalDegree k e) L₁ L₂⟩

/-- **The identification `Pic(X) = Pic(X') ⊕ ℤ`.** For the contraction `b : X ⟶ X'` of an
exceptional curve of the first kind, a class `ℒ` on `X` is sent to the pair `(ℒ', n)` with `n` the
degree of `ℒ` on the exceptional curve, and a pair `(ℒ', n)` back to the class of
`(b^*ℒ')(-nE)`. -/
public def picardDecompositionOfExactness (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.ofScheme X ≃+ Stacks.Picard.ofScheme X' × ℤ where
  toFun L := (D.contractedPicardHomOfExactness k e b hb hker hE L, D.exceptionalDegree k e L)
  invFun p :=
    Stacks.Picard.schemePullbackClassHom b p.1 + negativeExceptionalMultipleHom D p.2
  left_inv L := D.picardDecompositionOfExactness_left_inv k e b hb hker hE L
  right_inv := fun ⟨L', n⟩ => D.picardDecompositionOfExactness_right_inv k e b hb hker hE L' n
  map_add' L₁ L₂ := D.picardDecompositionOfExactness_map_add k e b hb hker hE L₁ L₂

/-- The integer component of the decomposition is the degree of `ℒ` on the exceptional curve. -/
public theorem picardDecompositionOfExactness_apply_snd
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    (D.picardDecompositionOfExactness k e b hb hker hE L).2 = D.exceptionalDegree k e L :=
  rfl

/-- The `Pic(X')`-component of the decomposition is the homomorphism `ℒ ↦ ℒ'`. -/
public theorem picardDecompositionOfExactness_apply_fst'
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    (D.picardDecompositionOfExactness k e b hb hker hE L).1 =
      D.contractedPicardHomOfExactness k e b hb hker hE L :=
  rfl

/-- **`ℒ' = b_*ℒ(nE)`.** The `Pic(X')`-component of the decomposition is `p(ℒ(nE))`, with `n` the
degree of `ℒ` on the exceptional curve, for every pushforward `p` on Picard classes left inverse
to `b^*`; such a `p` exists, namely `ℒ ↦ ℒ'` itself. -/
public theorem picardDecompositionOfExactness_apply_fst
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (p : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X')
    (hp : ∀ L' : Stacks.Picard.ofScheme X',
      p (Stacks.Picard.schemePullbackClassHom b L') = L')
    (L : Stacks.Picard.ofScheme X) :
    (D.picardDecompositionOfExactness k e b hb hker hE L).1 =
      p (D.exceptionalTwist (D.exceptionalDegree k e L) L) := by
  rw [← D.schemePullbackClassHom_contractedClass k e b hker hE L, hp]
  rfl

/-- The inverse of the decomposition sends `(ℒ', n)` to the class of `(b^*ℒ')(-nE)`. -/
public theorem picardDecompositionOfExactness_symm_apply
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    (D.picardDecompositionOfExactness k e b hb hker hE).symm (L', n) =
      Stacks.Picard.schemePullbackClassHom b L' + negativeExceptionalMultipleHom D n :=
  rfl

/-- **The characterisation of the decomposition.** A class `ℒ` corresponds to the pair `(ℒ', n)`
if and only if `ℒ = (b^*ℒ')(-nE)`. -/
public theorem picardDecompositionOfExactness_eq_iff
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X)
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.picardDecompositionOfExactness k e b hb hker hE L = (L', n) ↔
      L = Stacks.Picard.schemePullbackClassHom b L' + negativeExceptionalMultipleHom D n := by
  rw [← AddEquiv.eq_symm_apply, picardDecompositionOfExactness_symm_apply]

/-- **The characterisation in the form `ℒ(nE) = b^*ℒ'`.** A class `ℒ` corresponds to the pair
`(ℒ', n)` if and only if `ℒ(nE)` is the pullback of `ℒ'` along `b`. -/
public theorem picardDecompositionOfExactness_eq_iff_exceptionalTwist
    (hb : IsContractionOfExceptionalCurve D b)
    (hker : D.ContractionPicardExactness k e b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X)
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.picardDecompositionOfExactness k e b hb hker hE L = (L', n) ↔
      D.exceptionalTwist n L = Stacks.Picard.schemePullbackClassHom b L' := by
  rw [D.picardDecompositionOfExactness_eq_iff k e b hb hker hE,
    exceptionalTwist_eq_sub_negativeExceptionalMultipleHom]
  exact sub_eq_iff_eq_add.symm

end Scheme.IdealSheafData

end AlgebraicGeometry

end
