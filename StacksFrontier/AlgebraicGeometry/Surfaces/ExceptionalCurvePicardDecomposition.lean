module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicard

/-!
# `Pic(X) = Pic(X') ⊕ ℤ` for the contraction of an exceptional curve

Let `b : X ⟶ X'` be the contraction of an exceptional curve of the first kind `E ⊆ X`, presented
as an effective Cartier divisor `D` together with an isomorphism `e : 𝐏¹_k ≅ E` carrying the
normal sheaf to `𝒪(-1)`. Stacks 0C5M reads off the short exact sequence of Stacks 0C5L the
direct-sum decomposition

`Pic(X) = Pic(X') ⊕ ℤ`,

in which `ℒ` corresponds to the pair `(ℒ', n)` exactly when `ℒ = (b^*ℒ')(-nE)`, equivalently
`ℒ(nE) = b^*ℒ'`; the proof of 0C5L exhibits `ℒ'` as `b_*ℒ(nE)`; and `ℒ ↦ ℒ'` is a group
homomorphism.

All four assertions are proved here, granted the two halves of 0C5L that the library does not
yet prove. Those two are bundled as the hypothesis
`AlgebraicGeometry.Scheme.IdealSheafData.ContractionPicardSplitting`: a pushforward `b_*` on
Picard classes left inverse to `b^*` (the first claim in the proof of 0C5L, which rests on
Tag 0AGS part (4)), and exactness of `Pic(X') ⟶ Pic(X) ⟶ ℤ` at `Pic(X)` (its second claim).
Left exactness — injectivity of `b^*` — is *not* a hypothesis: it follows from the left inverse
and is proved below.

## Main definitions

* `AlgebraicGeometry.projectiveLineTwistPicardClass` — the class of the twist `𝒪(m)` in the
  Picard group of the projective line.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalTwist` — the class of `ℒ(nE)`, the twist
  of `ℒ` by `n` times the exceptional curve.
* `AlgebraicGeometry.Scheme.IdealSheafData.ContractionPicardSplitting` — the two assertions of
  Tag 0C5L the library lacks, as a hypothesis on the contraction.
* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecomposition` — **the identification
  `Pic(X) ≃+ Pic(X') × ℤ`.**
* `AlgebraicGeometry.Scheme.IdealSheafData.contractedPicardHom` — **the group homomorphism
  `ℒ ↦ ℒ'`.**

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecomposition_eq_iff` —
  **`ℒ` corresponds to `(ℒ', n)` if and only if `ℒ = (b^*ℒ')(-nE)`.**
* `AlgebraicGeometry.Scheme.IdealSheafData.contractedPicardHom_apply` — **`ℒ' = b_*ℒ(nE)`**,
  and `AlgebraicGeometry.Scheme.IdealSheafData.picardDecomposition_apply_snd` — `n` is the
  degree of `ℒ` on the exceptional curve.
* `AlgebraicGeometry.Scheme.IdealSheafData.ContractionPicardSplitting`
  `.injective_schemePullbackClassHom` — left exactness of the sequence of Tag 0C5L, which the
  left inverse `b_*` already gives.

## Implementation notes

**`𝒪_X(-nE)` and `ℒ(nE)`.** The splitting `n ↦ [𝒪_X(-nE)]` is the `ℤ`-multiple homomorphism
`Scheme.IdealSheafData.negativeExceptionalMultipleHom` of
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurvePicard.lean`, written there as
`zmultiplesHom _ (Stacks.Divisors.negativeTwistPicardClass D)`. Dually `ℒ(nE)` is
`exceptionalTwist`, defined as `[ℒ] + n • [𝒪_X(E)]`; the two are related by
`exceptionalTwist_eq_sub_negativeExceptionalMultipleHom`, and the decomposition is written
through whichever of the two makes a statement read as the source does.

**The degree is parametrised by the identification `ℤ ≃+ Pic(𝐏¹_k)`.** As in
`ExceptionalCurvePicard.lean`, the surjectivity half of Tag 0BXJ is unproved in the library, so
there is no canonical `ℤ`-valued degree; the identification `φ` and its value at `-1` travel as
hypotheses, exactly as they do for
`Scheme.IdealSheafData.exceptionalDegreeHom_negativeExceptionalMultiple`, the one input from
0C5L that *is* proved and the only one used here.

**`b_*` is a hypothesis, not a construction.** The library has no pushforward on Picard classes:
`Stacks.Picard` carries only `Stacks.Picard.schemePullbackClassHom`. The field
`ContractionPicardSplitting.pushforwardHom` stands for `b_*`, and the source's formula
`ℒ' = b_*ℒ(nE)` is proved with it in that role.

## References

* [Stacks Project, Tag 0C5M](https://stacks.math.columbia.edu/tag/0C5M)
* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RingedSpace (structureIsSheaf)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

/-- The class of the twist `𝒪(m)` in the Picard group of the projective line, presented as
`Proj k[T₀, T₁]`. This is the value the identification `ℤ ≃+ Pic(𝐏¹_k)` of Tag 0BXJ takes at
`m`. -/
public abbrev projectiveLineTwistPicardClass (k : Type u) [Field k] (m : ℤ) :
    Stacks.Picard.ofScheme (projectiveLineProj k) :=
  Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
    (structureIsSheaf (projectiveLineProj k).toRingedSpace)
    (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
    (Scheme.IdealSheafData.isInvertible_twistingSheaf_projectiveLine k m)

namespace Scheme.IdealSheafData

section Defs

variable {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  (e : projectiveLineProj k ≅ D.subscheme)
  (φ : ℤ ≃+ Stacks.Picard.ofScheme (projectiveLineProj k)) (b : X ⟶ X')

/-- **The two assertions of Tag 0C5L that the library does not yet prove**, for the contraction
`b : X ⟶ X'` of the exceptional curve cut out by `D`: a pushforward `b_*` on Picard classes that
is a left inverse to `b^*`, and exactness of `Pic(X') ⟶ Pic(X) ⟶ ℤ` at `Pic(X)`. -/
public structure ContractionPicardSplitting where
  /-- The pushforward `b_* : Pic(X) ⟶ Pic(X')` on Picard classes. -/
  pushforwardHom : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X'
  /-- `b_*b^*ℒ' = ℒ'`, the first claim in the proof of Tag 0C5L. -/
  pushforwardHom_pullback (L' : Stacks.Picard.ofScheme X') :
    pushforwardHom (Stacks.Picard.schemePullbackClassHom b L') = L'
  /-- Exactness at `Pic(X)`: a class has degree zero on the exceptional curve exactly when it is
  pulled back along `b`. -/
  exceptionalDegreeHom_eq_zero_iff (L : Stacks.Picard.ofScheme X) :
    D.exceptionalDegreeHom k e φ L = 0 ↔
      ∃ L' : Stacks.Picard.ofScheme X', Stacks.Picard.schemePullbackClassHom b L' = L

variable [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The class of `ℒ(nE)` for `E` the exceptional curve cut out by `D`: the class of `ℒ` plus `n`
times the class of `𝒪_X(E)`. -/
public abbrev exceptionalTwist (n : ℤ) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.ofScheme X :=
  L + n • Stacks.Divisors.picardClass D

/-- `ℒ(nE)` is `[ℒ] + n • [𝒪_X(E)]`. -/
public theorem exceptionalTwist_def (n : ℤ) (L : Stacks.Picard.ofScheme X) :
    D.exceptionalTwist n L = L + n • Stacks.Divisors.picardClass D :=
  rfl

/-- `ℒ(nE)` is `ℒ` less the class `[𝒪_X(-nE)]` of the splitting of Tag 0C5L. -/
public theorem exceptionalTwist_eq_sub_negativeExceptionalMultipleHom (n : ℤ)
    (L : Stacks.Picard.ofScheme X) :
    D.exceptionalTwist n L = L - D.negativeExceptionalMultipleHom n := by
  rw [exceptionalTwist_def, zmultiplesHom_apply,
    Stacks.Divisors.negativeTwistPicardClass_eq_neg, zsmul_neg, sub_neg_eq_add]

end Defs

section Splitting

variable {X X' : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}
  {φ : ℤ ≃+ Stacks.Picard.ofScheme (projectiveLineProj k)} {b : X ⟶ X'}

/-- **Left exactness of the sequence of Tag 0C5L**: `b^* : Pic(X') ⟶ Pic(X)` is injective,
because `b_*` is a left inverse to it. -/
public theorem ContractionPicardSplitting.injective_schemePullbackClassHom
    (hb : D.ContractionPicardSplitting k e φ b) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom b) := fun L₁ L₂ h => by
  rw [← hb.pushforwardHom_pullback L₁, ← hb.pushforwardHom_pullback L₂, h]

/-- A class pulled back along `b` has degree zero on the exceptional curve. -/
public theorem ContractionPicardSplitting.exceptionalDegreeHom_schemePullbackClassHom
    (hb : D.ContractionPicardSplitting k e φ b) (L' : Stacks.Picard.ofScheme X') :
    D.exceptionalDegreeHom k e φ (Stacks.Picard.schemePullbackClassHom b L') = 0 :=
  (hb.exceptionalDegreeHom_eq_zero_iff _).2 ⟨L', rfl⟩

/-- `b^*b_*ℒ = ℒ` for a class `ℒ` of degree zero on the exceptional curve. -/
public theorem ContractionPicardSplitting.schemePullbackClassHom_pushforwardHom
    (hb : D.ContractionPicardSplitting k e φ b) {L : Stacks.Picard.ofScheme X}
    (hL : D.exceptionalDegreeHom k e φ L = 0) :
    Stacks.Picard.schemePullbackClassHom b (hb.pushforwardHom L) = L := by
  obtain ⟨L', rfl⟩ := (hb.exceptionalDegreeHom_eq_zero_iff L).1 hL
  rw [hb.pushforwardHom_pullback]

end Splitting

section Decomposition

variable {X X' : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  {e : projectiveLineProj k ≅ D.subscheme}
  {φ : ℤ ≃+ Stacks.Picard.ofScheme (projectiveLineProj k)} {b : X ⟶ X'}

/-- `ℒ(nE)` has degree zero on the exceptional curve when `n` is the degree of `ℒ` there. -/
public theorem exceptionalDegreeHom_exceptionalTwist_self
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) (L : Stacks.Picard.ofScheme X) :
    D.exceptionalDegreeHom k e φ
      (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L) L) = 0 := by
  rw [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom, map_sub,
    exceptionalDegreeHom_negativeExceptionalMultiple D k e φ hE hφ, sub_self]

/-- Composing `ℒ ↦ (b_*ℒ(nE), n)` with `(ℒ', n) ↦ (b^*ℒ')(-nE)` is the identity on `Pic(X)`. -/
public theorem picardDecomposition_left_inv
    (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.schemePullbackClassHom b
        (hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L) L)) +
      D.negativeExceptionalMultipleHom (D.exceptionalDegreeHom k e φ L) = L := by
  rw [hb.schemePullbackClassHom_pushforwardHom
      (exceptionalDegreeHom_exceptionalTwist_self hE hφ L),
    exceptionalTwist_eq_sub_negativeExceptionalMultipleHom]
  exact sub_add_cancel _ _

/-- Composing `(ℒ', n) ↦ (b^*ℒ')(-nE)` with `ℒ ↦ (b_*ℒ(nE), n)` is the identity on
`Pic(X') × ℤ`. -/
public theorem picardDecomposition_right_inv
    (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1))
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    (hb.pushforwardHom (D.exceptionalTwist
          (D.exceptionalDegreeHom k e φ (Stacks.Picard.schemePullbackClassHom b L' +
            D.negativeExceptionalMultipleHom n))
          (Stacks.Picard.schemePullbackClassHom b L' + D.negativeExceptionalMultipleHom n)),
        D.exceptionalDegreeHom k e φ (Stacks.Picard.schemePullbackClassHom b L' +
          D.negativeExceptionalMultipleHom n)) = (L', n) := by
  have hd : D.exceptionalDegreeHom k e φ (Stacks.Picard.schemePullbackClassHom b L' +
      D.negativeExceptionalMultipleHom n) = n := by
    rw [map_add, hb.exceptionalDegreeHom_schemePullbackClassHom,
      exceptionalDegreeHom_negativeExceptionalMultiple D k e φ hE hφ, zero_add]
  have ht : D.exceptionalTwist n (Stacks.Picard.schemePullbackClassHom b L' +
      D.negativeExceptionalMultipleHom n) = Stacks.Picard.schemePullbackClassHom b L' := by
    rw [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom]
    exact add_sub_cancel_right _ _
  rw [hd, ht, hb.pushforwardHom_pullback]

/-- The map `ℒ ↦ (b_*ℒ(nE), n)` is additive. -/
public theorem picardDecomposition_map_add
    (hb : D.ContractionPicardSplitting k e φ b) (L₁ L₂ : Stacks.Picard.ofScheme X) :
    (hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ (L₁ + L₂)) (L₁ + L₂)),
        D.exceptionalDegreeHom k e φ (L₁ + L₂)) =
      (hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L₁) L₁),
          D.exceptionalDegreeHom k e φ L₁) +
        (hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L₂) L₂),
          D.exceptionalDegreeHom k e φ L₂) := by
  have ht : D.exceptionalTwist (D.exceptionalDegreeHom k e φ (L₁ + L₂)) (L₁ + L₂) =
      D.exceptionalTwist (D.exceptionalDegreeHom k e φ L₁) L₁ +
        D.exceptionalTwist (D.exceptionalDegreeHom k e φ L₂) L₂ := by
    simp only [exceptionalTwist_eq_sub_negativeExceptionalMultipleHom, map_add]
    rw [AddMonoidHom.map_add (negativeExceptionalMultipleHom D)]
    exact add_sub_add_comm _ _ _ _
  rw [Prod.mk_add_mk, Prod.mk.injEq]
  exact ⟨by rw [ht, map_add], map_add _ L₁ L₂⟩

/-- **Stacks Project, Tag 0C5M: the identification `Pic(X) = Pic(X') ⊕ ℤ`.** For the contraction
`b : X ⟶ X'` of an exceptional curve of the first kind, a class `ℒ` on `X` is sent to the pair
`(b_*ℒ(nE), n)` with `n` the degree of `ℒ` on the exceptional curve, and a pair `(ℒ', n)` back
to the class of `(b^*ℒ')(-nE)`. -/
@[stacks 0C5M "the identification Pic(X) = Pic(X') ⊕ Z, granted the two halves of Tag 0C5L the \
library does not prove — a pushforward b_* left inverse to b^*, and exactness at Pic(X) — \
bundled as the hypothesis ContractionPicardSplitting, and granted the identification \
Z ≃+ Pic(P¹_k) of Tag 0BXJ, of which the library has only the injectivity half"]
public def picardDecomposition (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) :
    Stacks.Picard.ofScheme X ≃+ Stacks.Picard.ofScheme X' × ℤ where
  toFun L :=
    (hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L) L),
      D.exceptionalDegreeHom k e φ L)
  invFun p :=
    Stacks.Picard.schemePullbackClassHom b p.1 + D.negativeExceptionalMultipleHom p.2
  left_inv L := picardDecomposition_left_inv hb hE hφ L
  right_inv := fun ⟨L', n⟩ => picardDecomposition_right_inv hb hE hφ L' n
  map_add' L₁ L₂ := picardDecomposition_map_add hb L₁ L₂

/-- The integer component of the decomposition of Tag 0C5M is the degree of `ℒ` on the
exceptional curve. -/
public theorem picardDecomposition_apply_snd (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) (L : Stacks.Picard.ofScheme X) :
    (picardDecomposition hb hE hφ L).2 = D.exceptionalDegreeHom k e φ L :=
  rfl

/-- The inverse of the decomposition of Tag 0C5M sends `(ℒ', n)` to the class of
`(b^*ℒ')(-nE)`. -/
public theorem picardDecomposition_symm_apply (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1))
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    (picardDecomposition hb hE hφ).symm (L', n) =
      Stacks.Picard.schemePullbackClassHom b L' + D.negativeExceptionalMultipleHom n :=
  rfl

/-- **Stacks Project, Tag 0C5M: the characterisation of the decomposition.** A class `ℒ`
corresponds to the pair `(ℒ', n)` if and only if `ℒ = (b^*ℒ')(-nE)`. -/
@[stacks 0C5M "the characterisation: L corresponds to the pair (L', n) if and only if \
L = (b^*L')(-nE), granted the two halves of Tag 0C5L the library does not prove, bundled as \
the hypothesis ContractionPicardSplitting, and the identification Z ≃+ Pic(P¹_k) of Tag 0BXJ"]
public theorem picardDecomposition_eq_iff (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) (L : Stacks.Picard.ofScheme X)
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    picardDecomposition hb hE hφ L = (L', n) ↔
      L = Stacks.Picard.schemePullbackClassHom b L' + D.negativeExceptionalMultipleHom n := by
  constructor
  · intro h
    have h' := congrArg (picardDecomposition hb hE hφ).symm h
    rwa [AddEquiv.symm_apply_apply, picardDecomposition_symm_apply] at h'
  · intro h
    rw [h, ← picardDecomposition_symm_apply hb hE hφ L' n, AddEquiv.apply_symm_apply]

/-- **Stacks Project, Tag 0C5M: the assignment `ℒ ↦ ℒ'` is a group homomorphism.** It is the
`Pic(X')`-component of the decomposition `Pic(X) ≃+ Pic(X') × ℤ`. -/
@[stacks 0C5M "the assignment L ↦ L' is a group homomorphism, granted the two halves of Tag \
0C5L the library does not prove, bundled as the hypothesis ContractionPicardSplitting, and \
granted the identification Z ≃+ Pic(P¹_k) of Tag 0BXJ"]
public def contractedPicardHom (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) :
    Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X' :=
  (AddMonoidHom.fst _ _).comp (picardDecomposition hb hE hφ).toAddMonoidHom

/-- The homomorphism `ℒ ↦ ℒ'` of Tag 0C5M sends `ℒ` to `b_*ℒ(nE)`, with `n` the degree of `ℒ`
on the exceptional curve. -/
public theorem contractedPicardHom_apply (hb : D.ContractionPicardSplitting k e φ b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = projectiveLineTwistPicardClass k (-1)) (L : Stacks.Picard.ofScheme X) :
    contractedPicardHom hb hE hφ L =
      hb.pushforwardHom (D.exceptionalTwist (D.exceptionalDegreeHom k e φ L) L) :=
  rfl

end Decomposition

end Scheme.IdealSheafData

end AlgebraicGeometry

end
