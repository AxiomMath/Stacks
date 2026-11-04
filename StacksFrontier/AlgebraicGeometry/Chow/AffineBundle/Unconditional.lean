module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine

/-!
# Stacks 02TT: flat pullback along an affine-space bundle is surjective

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S`, and let `f : X ⟶ Y` be flat of relative dimension `r` which is
Zariski-locally on `Y` the projection `U × 𝔸^r ⟶ U`. Stacks 02TT asserts that the flat
pullback `f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k`. This file proves it with no
hypothesis beyond the statement.

The proof assembles the three steps of the source's proof, each formalized elsewhere:

* the rank-one case for the trivial bundle `𝔸¹_B ⟶ B`, from the generic decomposition of
  `Stacks.Chow.genericDecompositionHolds_one` (the polynomial `P ∈ R(Y)[T]` cutting out the
  generic fibre) and the devissage of
  `Stacks.Chow.flatPullbackChow_surjective_of_genericDecompositionHolds` (the induction on the
  delta-dimension, with Stacks 02RC, 02RX and 02RZ);
* the trivial bundle `𝔸^r_B ⟶ B` of arbitrary rank, as a tower of affine-line projections, by
  `Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver`;
* an arbitrary affine-space bundle, by the reduction to the trivial bundle of
  `Stacks.Chow.flatPullbackChow_surjective_of_surjective_affineSpaceOver`.

The flat pullback on Chow groups is written down with Stacks 02S1,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_affineLine` — Stacks 02TT for `𝔸¹_B ⟶ B`.
* `Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver_unconditional` — Stacks 02TT for
  `𝔸^r_B ⟶ B`.
* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_general` — Stacks 02TT for a
  bundle over the base with arbitrary structure morphisms.
* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_unconditional` —
  **Stacks 02TT**.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **Stacks 02TT for the affine line.** Flat pullback along the projection `𝔸¹_B ⟶ B` is
surjective on Chow groups in every degree, for every scheme `B` locally of finite type over the
base. -/
theorem flatPullbackChow_surjective_affineLine (C : ChowSituation.{u}) (B : Scheme.{u})
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (k : ℤ) :
    Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
      (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1 (relativeDimension_affineSpaceOver B 1) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sB _ rfl 1
        (relativeDimension_affineSpaceOver B 1) k)) :=
  flatPullbackChow_surjective_of_genericDecompositionHolds C 1 k (genericDecompositionHolds_one C k)
    _ sB _ rfl _ (isAffineSpaceBundle_affineSpaceOver B 1) _

/-- **Stacks 02TT for the trivial bundle.** Flat pullback along the projection `𝔸^r_B ⟶ B` is
surjective on Chow groups in every degree: the projection is a tower of affine-line
projections. -/
theorem flatPullbackChow_surjective_affineSpaceOver_unconditional (C : ChowSituation.{u})
    (r : ℕ) (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (k : ℤ) :
    Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB
      (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r (relativeDimension_affineSpaceOver B r) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sB _ rfl r
        (relativeDimension_affineSpaceOver B r) k)) :=
  flatPullbackChow_surjective_affineSpaceOver C
    (@flatPullbackFactorsThroughRationalEquivalence_general C)
    (fun B' sB' _ j ↦ flatPullbackChow_surjective_affineLine C B' sB' j) r B sB k

/-- **Stacks 02TT**, with arbitrary structure morphisms. Let `X` and `Y` be locally of finite
type over the base of chapter 42 and let `f : X ⟶ Y` be a morphism over the base, flat of
relative dimension `r`, which is Zariski-locally on `Y` the projection `U × 𝔸^r ⟶ U`. Then
`f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k`. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_general (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChow C sX sY f hbase r hf k
      (flatPullbackFactorsThroughRationalEquivalence_general C sX sY f hbase r hf k)) :=
  flatPullbackChow_surjective_of_surjective_affineSpaceOver C r k
    (fun B sB _ ↦ flatPullbackChow_surjective_affineSpaceOver_unconditional C r B sB k)
    sX sY f hbase hf hbundle _

/-- **Stacks 02TT.** Let `(S, δ)` be the base situation of chapter 42, let `X` and `Y` be locally
of finite type over `S`, and let `f : X ⟶ Y` be flat of relative dimension `r` such that every
point of `Y` has an open neighbourhood `U` over which `f` is identified with the projection
`U × 𝔸^r ⟶ U`. Then `f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k ∈ ℤ`. -/
@[stacks 02TT]
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_unconditional (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChow C (f ≫ sY) sY f rfl r hf k
      (flatPullbackFactorsThroughRationalEquivalence_general C (f ≫ sY) sY f rfl r hf k)) :=
  flatPullbackChow_surjective_of_isAffineSpaceBundle_general C (f ≫ sY) sY f rfl r hf hbundle k

end Stacks.Chow

end
