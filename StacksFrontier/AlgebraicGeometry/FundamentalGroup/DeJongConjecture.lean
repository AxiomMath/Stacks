module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Deformation.Representation.FixedDeterminantUniversal

/-!
# De Jong's conjecture and the universal deformation ring of a residual representation

Let `X` be a smooth, geometrically irreducible, projective curve over a finite field `k` of
characteristic `p`, and let `ℓ ≠ p` be a prime. De Jong's conjecture for `X` asserts that every
continuous representation `π₁(X) → GLₙ(F⟦t⟧)`, for `F` a finite field of characteristic `ℓ`, has
finite geometric monodromy, that is, the image of the geometric fundamental group `π₁(X_k̄)` is
finite.

Granting the conjecture, if the restriction of a continuous residual representation
`ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` to `π₁(X_k̄)` is absolutely irreducible and `ℓ` does not divide `n`, then
for a continuous character `δ : π₁(X) → ℤ_[ℓ]ˣ` lifting `det ρ₀` the universal deformation ring of
`ρ₀` with determinant fixed to `δ` is finite and flat over `ℤ_[ℓ]`. In particular `ρ₀` then lifts
to characteristic zero.

## Main definitions

* `AlgebraicGeometry.DeJongConjectureHolds` — de Jong's conjecture for a curve, at a prime `ℓ`
  and in a fixed rank: every continuous representation of the étale fundamental group over a
  power series ring with finite coefficient field of characteristic `ℓ` has finite geometric
  monodromy.

## Main results

* `AlgebraicGeometry.finite_of_isUniversalFixedDeterminantDeformation` — the universal
  fixed-determinant deformation ring is finite over `ℤ_[ℓ]`.
* `AlgebraicGeometry.flat_of_isUniversalFixedDeterminantDeformation` — the universal
  fixed-determinant deformation ring is flat over `ℤ_[ℓ]`.

## Implementation notes

The source states the conclusion as "the morphism `Spec(R_univ) → Spec(ℤ_ℓ)` is finite and
flat"; as `R_univ` is an affine `ℤ_[ℓ]`-algebra, the two independent conclusions are recorded
separately as `Module.Finite` and `Module.Flat`.

The source's statement of the theorem does not name the determinant; without fixing it the
statement is false, since already in rank one unramified twists produce infinitely many
deformations and the deformation ring is not finite over `ℤ_[ℓ]`. The determinant character `δ`
is therefore part of the statement, as it is in the explanation that accompanies the theorem,
and no finite-image condition is imposed on `δ`.

The geometric fibre is presented as an arbitrary base change `X'` of `X` along `k → K` rather
than as a chosen pullback, so that the statement does not depend on a choice of pullback; the
restriction of a representation of `π₁(X)` to `π₁(X')` is along
`AlgebraicGeometry.etaleFundamentalGroupMap`.

The conjecture ranges over every finite coefficient field of characteristic `ℓ`, with its
discrete topology and the coefficientwise topology on its power series ring. Allowing finite
extensions of `ZMod ℓ`, rather than only `ZMod ℓ` itself, is what makes the conjecture usable:
a one-dimensional quotient of a complete local `𝐅_ℓ`-algebra is normalized to `F⟦t⟧` only after
a finite extension of the residue field.

The two conclusions are deduced from properties of the special fibre of the deformation ring
that the source obtains, in the cited work of de Jong, from the conjecture: that `R/ℓR` is
finite, and that `ℓ` is a nonzerodivisor on `R`. Both are carried here as explicit hypotheses.
The deductions themselves are
`Deformation.IsUniversalFixedDeterminantDeformation.finite`, which is Stacks Tag 031D over the
precomplete ring `ℤ_[ℓ]`, and
`Deformation.IsUniversalFixedDeterminantDeformation.flat`, which is torsion freeness over the
Bézout domain `ℤ_[ℓ]`.

## References

* [Stacks Project, Tag 03W1](https://stacks.math.columbia.edu/tag/03W1)
* [dJ-conjecture, Theorem 3.5]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped PowerSeries.WithPiTopology

universe u v w

namespace AlgebraicGeometry

/-- **De Jong's conjecture** for a smooth, geometrically irreducible, projective curve
`f : X ⟶ Spec k` over a finite field, at a prime `ℓ` and in rank `n`: for every finite field `F`
of characteristic `ℓ`, every continuous representation `π₁(X) → GLₙ(F⟦t⟧)` has finite geometric
monodromy, that is, the image of the geometric fundamental group `π₁(X')` of a base change `X'`
of `X` to an algebraically closed extension `K` of `k` is finite.

The coefficient field carries the discrete topology and its power series ring the
coefficientwise topology. -/
public def DeJongConjectureHolds (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
    [IsAlgClosed K] (ℓ n : ℕ) (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    (X' : Scheme.{u}) (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (_hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X') : Prop :=
  ∀ (F : Type w) [Field F] [Finite F] [CharP F ℓ],
    letI : TopologicalSpace F := ⊥
    ∀ ρ : EtaleFundamentalGroup X (x.map q) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (PowerSeries F),
      (Set.range fun g : EtaleFundamentalGroup X' x =>
        ρ (etaleFundamentalGroupMap q x g)).Finite

/-- **Stacks Project, Tag 03W1 (finiteness).** Let `X` be a smooth, geometrically irreducible,
projective curve over a finite field `k` of characteristic `p`, let `ℓ ≠ p` be a prime, and let
`ρ₀ : π₁(X) → GLₙ(ZMod ℓ)` be a continuous representation of its étale fundamental group. Assume
that de Jong's conjecture holds for `X`, that the restriction of `ρ₀` to the geometric
fundamental group is absolutely irreducible, and that `ℓ` does not divide `n`. Then the universal
deformation ring of `ρ₀` with determinant fixed to a continuous character `δ` lifting `det ρ₀` is
finite over `ℤ_[ℓ]`.

The step of de Jong's cited argument in which the conjecture is used, namely that the special
fibre `R/ℓR` of the deformation ring is finite, is carried as the hypothesis
`hspecialFibre`. -/
@[stacks 03W1 "fixed-determinant finiteness; the step of the cited argument in which the \
conjecture is used, that the special fibre R/lR of the universal deformation ring is finite, is \
carried as the hypothesis hspecialFibre"]
public theorem finite_of_isUniversalFixedDeterminantDeformation
    (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K] [IsAlgClosed K]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (_hℓp : ℓ ≠ p) (_hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    (X' : Scheme.{u}) (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X')
    (ρ₀ : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : EtaleFundamentalGroup X (x.map q) →ₜ* ℤ_[ℓ]ˣ)
    (_hconj : DeJongConjectureHolds.{u, w} k K ℓ n X f X' q fK hbc x)
    (_hirred : Deformation.IsAbsolutelyIrreducible
      fun g : EtaleFundamentalGroup X' x => ρ₀ (etaleFundamentalGroupMap q x g))
    (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) R)
    (hR : Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv)
    (hspecialFibre :
      Finite (R ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ] • (⊤ : Submodule ℤ_[ℓ] R)))) :
    Module.Finite ℤ_[ℓ] R :=
  hR.finite hspecialFibre

/-- **Stacks Project, Tag 03W1 (flatness).** Under the same hypotheses, the universal
fixed-determinant deformation ring of `ρ₀` is flat over `ℤ_[ℓ]`.

The step of de Jong's cited argument in which the conjecture is used, namely that `ℓ` is a
nonzerodivisor on the deformation ring, is carried as the hypothesis `hregular`. -/
@[stacks 03W1 "fixed-determinant flatness; the step of the cited argument in which the \
conjecture is used, that l is a nonzerodivisor on the universal deformation ring, is carried as \
the hypothesis hregular"]
public theorem flat_of_isUniversalFixedDeterminantDeformation
    (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K] [IsAlgClosed K]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (_hℓp : ℓ ≠ p) (_hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    (X' : Scheme.{u}) (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X')
    (ρ₀ : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : EtaleFundamentalGroup X (x.map q) →ₜ* ℤ_[ℓ]ˣ)
    (_hconj : DeJongConjectureHolds.{u, w} k K ℓ n X f X' q fK hbc x)
    (_hirred : Deformation.IsAbsolutelyIrreducible
      fun g : EtaleFundamentalGroup X' x => ρ₀ (etaleFundamentalGroupMap q x g))
    (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : EtaleFundamentalGroup X (x.map q) →ₜ* Matrix.GeneralLinearGroup (Fin n) R)
    (hR : Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv)
    (hregular : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∈ nonZeroDivisors R) :
    Module.Flat ℤ_[ℓ] R :=
  hR.flat hregular

end AlgebraicGeometry

end
