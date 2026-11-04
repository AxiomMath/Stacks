module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.DevissageOfTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineDominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity

/-!
# Stacks 02TT from the principal-divisor step alone

This file chains together the three layers of the proof of Stacks 02TT that are formalized in
this repository — the rank induction and the devissage of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`, the
delta-dimension induction and the prime-cycle devissage of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineDevissage`, and the three-case
analysis of a prime cycle dominating an integral base of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineDominantPrimeCycle` — so that the
whole tag rests on a single input.

That input, `hrat` below, is the principal-divisor half of the fourth paragraph of the source's
proof: a point of `𝔸¹_Y` lying over the generic point of an integral `Y`, other than the generic
point of `𝔸¹_Y`, has, over some nonempty open subscheme `V ⊆ Y`, its prime cycle rationally
equivalent to zero on `𝔸¹_V`. The source produces it by cutting out the generic fibre of the
prime divisor by a monic irreducible polynomial `P ∈ R(Y)[T]` and spreading `P` out to a `V` over
which it still cuts out the divisor, so that the restricted cycle is `div(P)`.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_affineLineOver_of_rationallyEquivalent` — the
  rank-one case of Stacks 02TT, from `hrat`.
* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rationallyEquivalent` —
  Stacks 02TT in arbitrary rank, from `hrat`.

## Implementation notes

No `@[stacks]` attribute is placed on either result: both carry `hrat`, and a declaration
registering a tag under an assumed hypothesis proves less than the tag asserts. The attribute
belongs on the discharged form, once `hrat` is proved.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **The rank-one case of Stacks 02TT from the principal-divisor step.** Flat pullback along the
projection `𝔸¹_B ⟶ B` is surjective in every degree and over every base locally of finite type
over the base of chapter 42, granted that a prime divisor of the affine line over an integral
base becomes rationally equivalent to zero over a nonempty open subscheme of that base.

The hypothesis is fed to
`Stacks.Chow.mem_range_flatPullbackChow_primeCycle_affineLineOver_of_dominant`, which supplies
the dominant prime-cycle step of
`Stacks.Chow.flatPullbackChow_surjective_affineLineOver_of_dominant`. -/
theorem flatPullbackChow_surjective_affineLineOver_of_rationallyEquivalent
    (C : ChowSituation.{u})
    (hrat : ∀ (Y : Scheme.{u}) [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)
      (w : ↥𝔸(ULift.{u} (Fin 1); Y)),
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
      w ≠ genericPoint ↥𝔸(ULift.{u} (Fin 1); Y) →
      ∃ (V : Y.Opens) (_ : ((V : Set Y)).Nonempty)
        (w' : ↥((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V)),
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι.base w' = w ∧
        IsRationallyEquivalentToZero C
          (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
          (k + ((1 : ℕ) : ℤ))
          (cycleAssociatedToClosedSubscheme C
            (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w').subschemeι (k + ((1 : ℕ) : ℤ))))
    (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
      (relativeDimension_affineSpaceOver B 1) j) :=
  flatPullbackChow_surjective_affineLineOver_of_dominant C j
    (fun Y _ sY _ _ hn hsmaller w hdom ↦
      mem_range_flatPullbackChow_primeCycle_affineLineOver_of_dominant C sY j hn hsmaller
        (fun w' hw' hne ↦ hrat Y sY j w' hw' hne) w hdom)
    B sB

/-- **Stacks 02TT in arbitrary rank from the principal-divisor step.** Let `(S, δ)` be the base
situation of chapter 42, let `X` and `Y` be locally of finite type over `S` and let `f : X ⟶ Y`
be flat of relative dimension `r` which is Zariski-locally on `Y` the projection
`U × 𝔸^r ⟶ U`. Then `f^* : A_k(Y) ⟶ A_{k+r}(X)` is surjective for every `k`, granted the
principal-divisor step `hrat`. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rationallyEquivalent
    (C : ChowSituation.{u})
    (hrat : ∀ (Y : Scheme.{u}) [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ)
      (w : ↥𝔸(ULift.{u} (Fin 1); Y)),
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
      w ≠ genericPoint ↥𝔸(ULift.{u} (Fin 1); Y) →
      ∃ (V : Y.Opens) (_ : ((V : Set Y)).Nonempty)
        (w' : ↥((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V)),
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι.base w' = w ∧
        IsRationallyEquivalentToZero C
          (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
          (k + ((1 : ℕ) : ℤ))
          (cycleAssociatedToClosedSubscheme C
            (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w').subschemeι (k + ((1 : ℕ) : ℤ))))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  flatPullbackChow_surjective_of_isAffineSpaceBundle_of_rankOne C
    (fun B sB _ j ↦ flatPullbackChow_surjective_affineLineOver_of_rationallyEquivalent C hrat
      B sB j)
    sY f r hf hbundle k

end Stacks.Chow

end
