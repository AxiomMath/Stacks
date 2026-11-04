module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.StalkLocallyPrincipal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed point of a curve as an effective Cartier divisor

Let `k` be a field, let `X` be a curve over `k` and let `x` be a closed point of `X`, regarded as
a reduced closed subscheme of `X` with sheaf of ideals `ℐ`. Then `ℐ` is an invertible
`𝒪_X`-module, equivalently `x` is an effective Cartier divisor on `X`, exactly when `𝒪_{X,x}` is
regular, equivalently normal, equivalently a discrete valuation ring.

## Main results

* `AlgebraicGeometry.ideal_vanishingIdeal_singleton`: on an affine open `U` around `x` the ideal
  cut out by the reduced point is the prime of `x`.
* `AlgebraicGeometry.map_germ_ideal_vanishingIdeal_singleton`: its stalk at `x` is the maximal
  ideal of `𝒪_{X,x}`.
* `AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing`: on a
  locally Noetherian integral scheme, a closed point whose local ring is a discrete valuation ring
  is an effective Cartier divisor.
* `AlgebraicGeometry.isPrincipal_maximalIdeal_stalk_of_isEffectiveCartierDivisor`: if a closed
  point is an effective Cartier divisor, the maximal ideal of its local ring is principal.
* `AlgebraicGeometry.isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve`: at a closed point of
  a curve, regularity, normality and the discrete valuation ring property of `𝒪_{X,x}` are
  equivalent to `x` being an effective Cartier divisor.

## Implementation notes

The reduced point is `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`, the
largest ideal sheaf with support `{x}`, whose quotient is the reduced induced structure. Being an
effective Cartier divisor, `Stacks.Divisors.IsEffectiveCartierDivisor I`, is by definition the
statement that the ideal sheaf `I` is an invertible `𝒪_X`-module, so a single predicate expresses
both that `ℐ` is invertible and that `x` is an effective Cartier divisor.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On an affine open `U` around a closed point `x`, the ideal of `Γ(X, U)` defining the reduced
subscheme `{x}` is the prime corresponding to `x`. -/
public theorem ideal_vanishingIdeal_singleton {x : X} (hx : IsClosed ({x} : Set X))
    (U : X.affineOpens) (hxU : x ∈ (U : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).ideal U
      = (U.2.primeIdealOf (⟨x, hxU⟩ : U.1)).asIdeal := by
  have hpre : (U.2.fromSpec ⁻¹' ((⟨{x}, hx⟩ : Closeds X) : Set X))
      = {U.2.primeIdealOf (⟨x, hxU⟩ : U.1)} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨U.2.fromSpec_primeIdealOf (⟨x, hxU⟩ : U.1), fun q hq =>
      (U.2.fromSpec.isOpenEmbedding (H := U.2.isOpenImmersion_fromSpec)).injective
        ((hq : U.2.fromSpec.base q = x).trans (U.2.fromSpec_primeIdealOf (⟨x, hxU⟩ : U.1)).symm)⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (congrArg PrimeSpectrum.vanishingIdeal hpre).trans
    (PrimeSpectrum.vanishingIdeal_singleton _)

/-- The stalk at `x` of the ideal sheaf of the reduced closed point `x` is the maximal ideal of
`𝒪_{X,x}`. -/
public theorem map_germ_ideal_vanishingIdeal_singleton {x : X} (hx : IsClosed ({x} : Set X))
    (U : X.affineOpens) (hxU : x ∈ (U : Set X)) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).ideal U)
      = maximalIdeal (X.presheaf.stalk x) := by
  let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U.1)
  have _ := U.2.isLocalization_stalk (⟨x, hxU⟩ : U.1)
  rw [ideal_vanishingIdeal_singleton hx U hxU]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal
    (U.2.primeIdealOf (⟨x, hxU⟩ : U.1)).asIdeal (X.presheaf.stalk x)

/-- A closed point is the whole support of its own reduced structure. -/
public theorem supportSet_vanishingIdeal_singleton {x : X} (hx : IsClosed ({x} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).supportSet = {x} :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)

/-- If the local ring of a locally Noetherian integral scheme at a closed point is a discrete
valuation ring, the point is an effective Cartier divisor. -/
public theorem isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing
    [IsLocallyNoetherian X] [IsIntegral X]
    {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal (maximalIdeal (X.presheaf.stalk x))
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_stalk _ fun z hz => ?_
  rw [supportSet_vanishingIdeal_singleton hx] at hz
  obtain rfl : z = x := hz
  refine ⟨⟨V, hV⟩, hxV, π, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, ?_⟩
  · exact IsDiscreteValuationRing.not_a_field _ (hπ.trans (by simp [h0]))
  · rw [map_germ_ideal_vanishingIdeal_singleton hx ⟨V, hV⟩ hxV, hπ]

/-- If a closed point of a scheme is an effective Cartier divisor, the maximal ideal of its local
ring is principal. -/
public theorem isPrincipal_maximalIdeal_stalk_of_isEffectiveCartierDivisor {x : X}
    (hx : IsClosed ({x} : Set X))
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) :
    (maximalIdeal (X.presheaf.stalk x)).IsPrincipal := by
  obtain ⟨U, hU, hxU, g, -, hgen⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor _ hC x
  refine ⟨(X.presheaf.germ U x hxU).hom g, ?_⟩
  rw [← map_germ_ideal_vanishingIdeal_singleton hx ⟨U, hU⟩ hxU, hgen, Ideal.map_span,
    Set.image_singleton]

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- At a closed point `x` of a curve over a field the following are equivalent: `𝒪_{X,x}` is
regular; `𝒪_{X,x}` is normal; `𝒪_{X,x}` is a discrete valuation ring; and the sheaf of ideals of
the reduced closed subscheme `{x}` is an invertible `𝒪_X`-module, which is to say that `x` is an
effective Cartier divisor on `X`. -/
@[stacks 0B8Y "(1), (2), (3), (4) and (5)",
  ega "II 7.4.5",
  ega "II 7.1.6" "curve stalk case",
  ega "IV 6.7.5" "partial"]
public theorem isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve [IsCurve k f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    List.TFAE [IsRegularLocalRing (X.presheaf.stalk x), IsNormalRing (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x),
      Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))] := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have H := isDiscreteValuationRing_stalk_tfae_of_isCurve k f hx
  have hd : ringKrullDim (X.presheaf.stalk x) = 1 :=
    ringKrullDim_stalk_eq_one_of_isCurve k f hx
  tfae_have 1 ↔ 2 := H.out 1 2
  tfae_have 2 ↔ 3 := H.out 2 3
  tfae_have 3 → 4 := fun _ =>
    isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hx
  tfae_have 4 → 3 := fun hC => by
    have hne : maximalIdeal (X.presheaf.stalk x) ≠ ⊥ := fun h0 => by
      rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h0)] at hd
      exact absurd hd (by decide)
    have h41 := (isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 4 1
    exact (h41.mp ⟨inferInstance, inferInstance, inferInstance,
      isPrincipal_maximalIdeal_stalk_of_isEffectiveCartierDivisor hx hC, hne⟩).2
  tfae_finish

end AlgebraicGeometry

end
