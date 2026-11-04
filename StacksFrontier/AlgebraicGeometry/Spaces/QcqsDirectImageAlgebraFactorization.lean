module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical factorization of a quasi-compact, quasi-separated morphism, with 03M9 supplied

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over a scheme
`S`.  `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization` proves that
`f_* 𝒪_Y` is a quasi-coherent `𝒪_X`-algebra and that `f` factors as
`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`, each time taking quasi-coherence of the direct image of a
quasi-coherent module along a quasi-compact quasi-separated morphism, Stacks 03M9, as the
hypothesis `h03M9`.  Stacks 03M9 is proved unconditionally as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`; this file supplies it,
giving the forms suffixed `_unconditional`.

## Main definitions

* `AlgebraicGeometry.Space.qcqsRelativeSpecDirectImage_unconditional` and
  `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap_unconditional`: the relative spectrum
  of `f_* 𝒪_Y` and the canonical morphism into it, with Stacks 03M9 supplied.

## Main statements

* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_unconditional`: for a
  quasi-compact, quasi-separated `T ⟶ X` the algebra `T_* 𝒪_T` is quasi-coherent.
* `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap_factorization_unconditional`: the
  canonical morphism composed with the structure morphism of `\underline{Spec}_X(f_* 𝒪_Y)`
  is `f`.

## Implementation notes

The factorization statements still presuppose the anti-equivalence `E` of Stacks 081V and its
base-change compatibility `C`, and `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is
uninhabited by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`, so
they are vacuous over any algebraic space with one affine chart whose ring of functions is not
zero; their `@[stacks 081X]` clauses say so.  The quasi-coherence statement mentions no `E`.
Stacks 081X itself is delivered unconditionally by
`AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (E : AffineAlgebraAntiEquivalence B S hS)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### Quasi-coherence of the direct-image algebra -/

/-- **The direct image of the structure sheaf along a quasi-compact, quasi-separated morphism of
algebraic spaces is a quasi-coherent algebra**, with nothing assumed, stated for an algebraic
space `T` over `X`.  The module underlying the algebra is the direct image of `𝒪_T`, which is
quasi-coherent by Stacks 03M9
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`).

This is `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra` with its Stacks 03M9
hypothesis supplied, read at an object of `Over X` rather than at `Over.mk f`.  The form at a
morphism `f : Y ⟶ X` is `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs` of
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs`. -/
@[stacks 081X "quasi-coherence of the pushforward algebra", ega "IV 21.12.1" "more general"]
theorem isQuasicoherent_pushforwardAlgebra_unconditional (T : Over X)
    (hfqc : IsQuasiCompact B S hS T.hom.hom) (hfqs : IsQuasiSeparated B S hS T.hom.hom) :
    (pushforwardAlgebra B S hS T).IsQuasicoherent :=
  isQuasicoherent_pushforwardAlgebra B S hS T.hom hfqc hfqs
    fun hqc hqs => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS T.hom hqc hqs

/-! ### The factorization for a quasi-compact, quasi-separated morphism, with 03M9 supplied -/

variable (C : BaseChangeCompatibility B S hS E)

variable (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)

/-- The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)` of the direct-image algebra of a
quasi-compact, quasi-separated morphism, as an algebraic space affine over `X`.

This is `AlgebraicGeometry.Space.qcqsRelativeSpecDirectImage` with its Stacks 03M9 hypothesis
supplied from `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`. -/
def qcqsRelativeSpecDirectImage_unconditional : AffineOver B S hS X :=
  qcqsRelativeSpecDirectImage B S hS E f hfqc hfqs
    fun hqc hqs => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hqc hqs

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`** attached to a
quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces.

This is `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap` with its Stacks 03M9 hypothesis
supplied from `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`. -/
def qcqsDirectImageFactorizationMap_unconditional :
    Over.mk f ⟶ (qcqsRelativeSpecDirectImage_unconditional B S hS E f hfqc hfqs).obj :=
  qcqsDirectImageFactorizationMap B S hS E C f hfqc hfqs
    fun hqc hqs => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hqc hqs

/-- **Stacks 081X.** A quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces
factors canonically as `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`, with nothing assumed beyond the
anti-equivalence of Stacks 081V and its base-change compatibility.

This is `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap_factorization` with its
Stacks 03M9 hypothesis supplied.

**This statement is vacuous**, for the reason recorded at
`AlgebraicGeometry.Space.directImageFactorizationMap_factorization`: the anti-equivalence `E` it
presupposes is an inhabitant of `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, which
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`
empties.  The same factorization against the bounded anti-equivalence is
`AlgebraicGeometry.Space.boundedQcqsDirectImageFactorizationMap_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization`.  Stacks 081X is
delivered unconditionally by `AlgebraicGeometry.Space.directImageSpec_factorization` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSpecFactorization`. -/
@[stacks 081X "the canonical factorization of a quasi-compact quasi-separated morphism — but \
presupposing an inhabitant of AffineAlgebraAntiEquivalence, which \
not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart shows is uninhabited over any \
algebraic space with one affine chart carrying a nonzero ring of functions, so the statement is \
vacuous there; the factorization against the bounded anti-equivalence, which that argument does \
not refute, is boundedQcqsDirectImageFactorizationMap_factorization"]
theorem qcqsDirectImageFactorizationMap_factorization_unconditional :
    (qcqsDirectImageFactorizationMap_unconditional B S hS E C f hfqc hfqs).left ≫
        (qcqsRelativeSpecDirectImage_unconditional B S hS E f hfqc hfqs).obj.hom = f :=
  qcqsDirectImageFactorizationMap_factorization B S hS E C f hfqc hfqs
    fun hqc hqs => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hqc hqs

end AlgebraicGeometry.Space

end
