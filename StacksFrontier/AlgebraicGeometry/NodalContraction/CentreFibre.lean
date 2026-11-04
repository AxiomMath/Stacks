module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.DvrStalk

/-!
# The contracted point lies over the closed point of the base

Let `R` be a discrete valuation ring, let `f : X ⟶ Spec R` be at-worst-nodal of relative dimension
one, and let `b : X ⟶ X'` be a morphism over `Spec R`. If the pullback along `b` of the vanishing
ideal of a closed point `z` of `X'` is an effective Cartier divisor whose subscheme has local
dimension one at some point, then `z` lies over the closed point of `Spec R`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_le_topologicalKrullDim`: the local dimension of a
  space at a point is at most its dimension.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_fiber_of_isOpen_singleton`: at a point lying over
  an open point of the base, the local dimension of a scheme is that of the fibre.
* `AlgebraicGeometry.eq_closedPoint_of_isEffectiveCartierDivisor`: the contracted point lies over
  the closed point of the base.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The local dimension of a space at a point is at most its dimension. -/
public alias topologicalKrullDimAt_le_topologicalKrullDim :=
  _root_.topologicalKrullDimAt_le_topologicalKrullDim

/-- At a point lying over an open point of the base, the local dimension of the source is the
local dimension of the fibre through that point. -/
public theorem topologicalKrullDimAt_eq_fiber_of_isOpen_singleton
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (hopen : IsOpen ({f x} : Set S)) :
    topologicalKrullDimAt X x =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have hpre : IsOpen (f ⁻¹' ({f x} : Set S)) := hopen.preimage f.continuous
  have hmem : x ∈ f ⁻¹' ({f x} : Set S) := rfl
  have hpoint : (f.fiberHomeo (f x)) (f.asFiber x) = ⟨x, hmem⟩ :=
    Subtype.ext (f.fiberι_asFiber x)
  calc
    topologicalKrullDimAt X x =
        topologicalKrullDimAt (f ⁻¹' ({f x} : Set S)) ⟨x, hmem⟩ :=
      hpre.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hmem⟩
    _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
      rw [topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f x)) (f.asFiber x), hpoint]

/-- **The contracted point lies over the closed point of the base.** Let `R` be a discrete
valuation ring, `f : X ⟶ Spec R` at-worst-nodal of relative dimension one, and `b : X ⟶ X'` a
morphism over `Spec R`. If the pullback `D` along `b` of the vanishing ideal of a closed point `z`
of `X'` is an effective Cartier divisor whose subscheme has local dimension one at some point,
then `z` lies over the closed point of `Spec R`. -/
public theorem eq_closedPoint_of_isEffectiveCartierDivisor
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (hD1 : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (b : X ⟶ X') (z : X') (hz : IsClosed ({z} : Set X'))
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : Closeds X')).comap b)
    (f : X ⟶ Spec (CommRingCat.of R)) (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (f' : X' ⟶ Spec (CommRingCat.of R)) (hbase : b ≫ f' = f)
    (x : D.subscheme) (hdimE : topologicalKrullDimAt D.subscheme x = 1) :
    f' z = IsLocalRing.closedPoint R := by
  rcases dvr_prime_cases R (f' z) with hgen | hcl
  · exfalso
    set d : X := D.subschemeι x with hd
    have hbz : b d = z :=
      IsContractionOfExceptionalCurve.eq_centre_of_mem_support hDz
        (by rw [← D.range_subschemeι]; exact ⟨x, rfl⟩)
    have hfd : f d = (⊥ : PrimeSpectrum R) := by
      rw [← hbase, Scheme.Hom.comp_apply, hbz, hgen]
    have hdimFiber : topologicalKrullDim (f.fiber (f d)) = 1 :=
      (((isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf).2.2.1 (f d)
        ⟨f.asFiber d⟩).2
    have hdimX : topologicalKrullDimAt X d ≤ 1 := by
      rw [topologicalKrullDimAt_eq_fiber_of_isOpen_singleton f d
        (by rw [hfd]; exact isOpen_generic_of_isDiscreteValuationRing R)]
      exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans_eq hdimFiber
    have hfin : topologicalKrullDimAt X d < ⊤ :=
      lt_of_le_of_lt hdimX (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top 1))
    have hdrop := topologicalKrullDimAt_subscheme_lt D hD1 x hfin
    rw [hdimE] at hdrop
    exact absurd hdimX (not_le_of_gt hdrop)
  · exact hcl

end AlgebraicGeometry

end
