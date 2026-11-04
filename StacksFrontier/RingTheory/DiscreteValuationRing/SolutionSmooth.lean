module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.Smooth.SmoothAt

/-!
# A solution is a base change that is smooth at every maximal ideal

Let `D` be the base-change package attached to an extension of discrete valuation rings `A → B`
and a finite extension `K₁/K` of the fraction field of `A`, with integral closures `A₁ ⊆ K₁` and
`B₁ ⊆ L₁`. By definition `D` is a *solution* when, for every maximal ideal `q ⊆ B₁` and the prime
`p = q ∩ A₁` beneath it, the local homomorphism `(A₁)_p → (B₁)_q` is formally smooth for the
topology defined by the maximal ideal of `(B₁)_q`.

If `A₁` is Noetherian and `B₁` is of finite type over `A₁`, that adic formal smoothness is exactly
smoothness of `A₁ → B₁` at the prime `q`, by Stacks 07VH. So under those two finiteness hypotheses
being a solution is the geometric condition that `A₁ → B₁` be smooth at every maximal ideal of
`B₁`.

The finiteness hypotheses and the extra ring and algebra structures on `D.A₁` and `D.B₁` are stated
inside the conclusion, because the instances they refer to are fields of `D` rather than global
instances and so are only available after they have been introduced.

## Main results

* `IsDiscreteValuationRing.IntegralClosureBaseChange.isSolution_iff_forall_smoothAt`: for `D.A₁`
  Noetherian and `D.B₁` of finite type over it, `D.IsSolution` holds if and only if `D.A₁ → D.B₁`
  is smooth at every maximal ideal of `D.B₁`.

## References

* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [Stacks Project, Tag 07VH](https://stacks.math.columbia.edu/tag/07VH)
-/

@[expose] public section

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

namespace IsDiscreteValuationRing.IntegralClosureBaseChange

/-- **A solution is a base change smooth at every maximal ideal.** For `D.A₁` Noetherian and
`D.B₁` of finite type over `D.A₁`, the base change `D` is a solution (Stacks 09EN(2)) exactly when
`D.A₁ → D.B₁` is smooth, in the sense of Definition 00TB, at every maximal ideal of `D.B₁`: at each
such `q` the adic formal smoothness of `(D.A₁)_p → (D.B₁)_q` required by `IsSolution` is smoothness
at `q`, by Stacks 07VH. -/
theorem isSolution_iff_forall_smoothAt
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
    {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁) :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.algebraA₁B₁
    ∀ [IsNoetherianRing D.A₁] [Algebra.FiniteType D.A₁ D.B₁],
      D.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, max uA₁ uB₁} ↔
        ∀ (q : Ideal D.B₁) (hq : q.IsMaximal),
          letI : q.IsPrime := hq.isPrime
          Algebra.SmoothAt D.A₁ D.B₁ q := by
  let : CommRing D.A₁ := D.commRingA₁
  let : CommRing D.B₁ := D.commRingB₁
  let : Algebra D.A₁ D.B₁ := D.algebraA₁B₁
  intro _ _
  refine ⟨fun h q hq => ?_, fun h q hq => ?_⟩ <;>
  · have : q.IsPrime := hq.isPrime
    have : (q.comap (algebraMap D.A₁ D.B₁)).IsPrime := Ideal.IsPrime.comap _
    have : q.LiesOver (q.comap (algebraMap D.A₁ D.B₁)) := ⟨rfl⟩
    first
    | exact (smoothAt_iff_formallySmoothNAdic_localization
        (q.comap (algebraMap D.A₁ D.B₁)) q).mpr (h q hq)
    | exact (smoothAt_iff_formallySmoothNAdic_localization
        (q.comap (algebraMap D.A₁ D.B₁)) q).mp (h q hq)

end IsDiscreteValuationRing.IntegralClosureBaseChange

end
