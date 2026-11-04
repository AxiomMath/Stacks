module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.DevissageOfTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineGenericPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineLocalEquation
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.OpenDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PrincipalPrimeCycle

/-!
# Stacks 02TT, unconditionally

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be flat of relative dimension `r` which is
Zariski-locally on `Y` the projection `U × 𝔸^r ⟶ U`. Then

  `f^* : A_k(Y) ⟶ A_{k+r}(X)`

is surjective for every `k`. This file completes the proof: the last open input of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineRankOne` — that a prime divisor of the
affine line over an integral base becomes rationally equivalent to zero over a nonempty open
subscheme of the base — is discharged here from the global equation of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineLocalEquation` and the
order-of-vanishing computation of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PrincipalPrimeCycle`.

## The dimension count

The prime cycle in question is read in degree `k + 1`. If the relative dimension of its point is
not `k + 1` the cycle in that degree is zero and there is nothing to prove. Otherwise the point,
lying over the generic point of an integral `Y` of delta-dimension `n` and not being the generic
point of `𝔸¹_Y`, has relative dimension `n`, so `n = k + 1`; and the open subscheme
`f^{-1}(V)` meets the generic point, so its delta-dimension is that of `𝔸¹_Y`, namely `n + 1`,
which is `(k + 1) + 1`. That is exactly the degree in which the order-of-vanishing computation
delivers a principal divisor.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_primeCycle_affineLineOver` — the principal-divisor
  step of the fourth paragraph of the source's proof.
* `Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver_one` — **Stacks 02TT** for the trivial
  bundle of rank one, unconditionally. This is the `hone` input of
  `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rankOne`.
* `Stacks.Chow.flatPullbackChow_surjective_isAffineSpaceBundle` — **Stacks 02TT**,
  unconditionally, in arbitrary rank.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **The principal-divisor step of the fourth paragraph of the proof of Stacks 02TT.** Let `Y`
be integral of delta-dimension `n` over the base of chapter 42 and let `w` be a point of `𝔸¹_Y`
lying over the generic point of `Y` and distinct from the generic point of `𝔸¹_Y` — the generic
point of a prime divisor dominating `Y`. Then there are a nonempty open subscheme `V ⊆ Y` and a
point `w'` of `f^{-1}(V)` over `w` whose prime cycle is rationally equivalent to zero on
`f^{-1}(V)`.

The global equation of the prime divisor over such a `V` is
`Stacks.Chow.exists_opens_germ_span_eq_maximalIdeal_restrict`; that its prime cycle is then the
principal divisor of that equation is
`Stacks.Chow.isRationallyEquivalentToZero_primeCycle_of_span_germ_eq_maximalIdeal`. The
delta-dimension of `f^{-1}(V)` is that of `𝔸¹_Y` because `V` meets the generic point. -/
theorem isRationallyEquivalentToZero_primeCycle_affineLineOver (C : ChowSituation.{u})
    {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ) {n : ℤ}
    (hn : schemeDeltaDimension C sY = (n : EInt)) (w : ↥𝔸(ULift.{u} (Fin 1); Y))
    (hdom : (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y)
    (hne : w ≠ genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)) :
    ∃ (V : Y.Opens) (_ : ((V : Set Y)).Nonempty)
      (w' : ↥((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V)),
      ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι.base w' = w ∧
      IsRationallyEquivalentToZero C
        (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
        (k + ((1 : ℕ) : ℤ))
        (cycleAssociatedToClosedSubscheme C
          (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
          (integralComponentAt w').subschemeι (k + ((1 : ℕ) : ℤ))) := by
  obtain ⟨V, hgV, w', hw', t, ht, hmax, hsupp⟩ :=
    exists_opens_germ_span_eq_maximalIdeal_restrict Y w hdom hne
  refine ⟨V, ⟨genericPoint ↥Y, hgV⟩, w', hw', ?_⟩
  have hint : IsIntegral ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).toScheme :=
    isIntegral_opens_of_mem _ w'
  by_cases hd : relativeDimension C.dimensionFunction
      (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w' =
      k + ((1 : ℕ) : ℤ)
  · -- the generic point of `𝔸¹_Y` lies in `f^{-1}(V)`, so the two delta-dimensions agree
    have hgenmem : genericPoint ↥𝔸(ULift.{u} (Fin 1); Y) ∈
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V := by
      rwa [Scheme.Hom.mem_preimage, genericPoint_eq_of_isDominant]
    have hdimopen : schemeDeltaDimension C
        (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) =
        ((n + ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
      rw [schemeDeltaDimension_opensι_comp' C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) _ hgenmem]
      exact schemeDeltaDimension_affineSpaceOver C sY 1 hn
    have hdw : relativeDimension C.dimensionFunction
        (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w' =
        n := by
      rw [relativeDimension_opensι_comp C.dimensionFunction
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) _ w', hw']
      exact relativeDimension_eq_of_dominant_of_ne_genericPoint C sY hn w hdom hne
    have hnk : n = k + ((1 : ℕ) : ℤ) := hdw.symm.trans hd
    have h := isRationallyEquivalentToZero_primeCycle_of_span_germ_eq_maximalIdeal C
      (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
      (m := k + ((1 : ℕ) : ℤ) + 1) (by rw [hdimopen, hnk]; norm_num) w'
      (by rw [hdw, hnk]; ring) t ht hmax hsupp
    rwa [show k + ((1 : ℕ) : ℤ) + 1 - 1 = k + ((1 : ℕ) : ℤ) by ring] at h
  · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_eq_zero_of_ne C
      (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
      (k + ((1 : ℕ) : ℤ)) w' hd]
    exact rationallyEquivalentToZero_zero C _ _

/-- **Stacks 02TT for the trivial bundle of rank one.** Flat pullback along the projection
`𝔸¹_B ⟶ B` is surjective in every degree, for every scheme `B` locally of finite type over the
base of chapter 42.

This is the fourth paragraph of the source's proof together with the delta-dimension induction
and the prime-cycle devissage: the principal-divisor step is
`Stacks.Chow.isRationallyEquivalentToZero_primeCycle_affineLineOver`, and everything above it is
`Stacks.Chow.flatPullbackChow_surjective_affineLineOver_of_rationallyEquivalent`. -/
theorem flatPullbackChow_surjective_affineSpaceOver_one (C : ChowSituation.{u})
    (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
      (relativeDimension_affineSpaceOver B 1) j) :=
  flatPullbackChow_surjective_affineLineOver_of_rationallyEquivalent C
    (fun _ _ sY _ k w hdom hne ↦
      let ⟨_, hn⟩ := exists_schemeDeltaDimension_eq_of_irreducibleSpace C sY
      isRationallyEquivalentToZero_primeCycle_affineLineOver C sY k hn w hdom hne)
    B sB j

/-- Let `(S, δ)` be the base situation of chapter 42, let `X` and `Y` be locally of finite type
over `S` and let `f : X ⟶ Y` be flat of relative dimension `r` such that every point of `Y` has
an open neighbourhood `U` over which `f` is the projection `𝔸^r_U ⟶ U`. Then
`f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k`. -/
@[stacks 02TT]
theorem flatPullbackChow_surjective_isAffineSpaceBundle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rankOne C
    (fun B sB _ j ↦ flatPullbackChow_surjective_affineSpaceOver_one C B sB j) sY f r hf hbundle k

end Stacks.Chow

end
