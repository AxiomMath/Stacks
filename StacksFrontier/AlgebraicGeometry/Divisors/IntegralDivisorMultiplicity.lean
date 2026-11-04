module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The multiplicity of a power of an integral effective Cartier divisor

Let `X` be an integral scheme and `D` an effective Cartier divisor on it whose closed subscheme
is integral.  If the generic point `ξ` of a prime divisor `Z` lies on `D`, then `D` and `Z` have
the same underlying closed subset, so `ξ` is the generic point of `D` as well; the local ring of
`D` at `ξ` is then a field, and the stalk of `D` at `ξ` is the maximal ideal of `𝒪_{X, ξ}`.

That local ring is a discrete valuation ring by [Stacks, Tag 0AG9], so the multiplicity of
`D ^ k` at `Z` in the sense of [Stacks, Tag 02AR] part (5) is exactly `k`.

## Main results

* `AlgebraicGeometry.genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor`: the generic
  point of an integral scheme lies off every effective Cartier divisor.
* `AlgebraicGeometry.IdealSheafData.stalk_eq_maximalIdeal_genericPoint`: the stalk of such a
  divisor at the generic point of such a prime divisor is the maximal ideal.
* `AlgebraicGeometry.effectiveCartierMultiplicity_pow`: the multiplicity of `D ^ k` is `k`.

## Implementation notes

The support of `D` is irreducible because it is the range of the closed immersion of the
integral subscheme, and it is a proper subset because an effective Cartier divisor on an
integral scheme is cut out locally by a regular, hence nonzero, element of a domain.  Those two
facts feed `AlgebraicGeometry.PrimeDivisor.support_eq_of_isIrreducible`, which is where the
codimension-one hypothesis on `Z` is spent.

`AlgebraicGeometry.isDiscreteValuationRing_stalk_genericPoint` is Tag 0AG9, stated at the point
`D.subschemeι (genericPoint D.subscheme)`; identifying that point with `Z.genericPoint` is what
`AlgebraicGeometry.subschemeι_genericPoint_eq_genericPoint` is for.

The local ring of the subscheme at its generic point is `Scheme.functionField`, which carries a
`Field` instance for an integral scheme; no separate "the stalk at the generic point is a field"
lemma is needed.  The quotient identification is
`AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`, and `ℐ.subschemeι` applied to
`AlgebraicGeometry.IdealSheafData.subschemePoint` is the point itself by `rfl`, so no transport
appears.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 0AG9](https://stacks.math.columbia.edu/tag/0AG9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The support of an integral effective Cartier divisor -/

/-- An effective Cartier divisor on an integral scheme is not the zero ideal sheaf: it is cut
out locally by a regular, hence nonzero, element of a domain. -/
theorem ne_bot_of_isEffectiveCartierDivisor [IsIntegral X] {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : D ≠ ⊥ := by
  intro hbot
  obtain ⟨U, hU, hxU, f, hf, hlocal⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD
      (genericPoint X)
  have : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have hspan : Ideal.span ({f} : Set Γ(X, U)) = ⊥ := by
    rw [← hlocal, hbot]
    simp
  exact isRegular_iff_ne_zero.mp hf (Ideal.span_singleton_eq_bot.mp hspan)

/-- **The generic point of an integral scheme lies off every effective Cartier divisor.**  The
support is closed, so a generic point lying on it would make it all of `X`, and the only ideal
sheaf with full support on a reduced scheme is the zero one. -/
theorem genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor [IsIntegral X]
    {D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    genericPoint X ∉ D.supportSet := fun hη =>
  ne_bot_of_isEffectiveCartierDivisor hD
    (Scheme.IdealSheafData.support_eq_top_iff.mp (Closeds.ext (by
      rw [Closeds.coe_top, ← Set.univ_subset_iff, ← genericPoint_closure X]
      exact closure_minimal (Set.singleton_subset_iff.mpr hη) D.support.isClosed)))

/-- The underlying closed subset of an effective Cartier divisor with integral subscheme is the
underlying closed subset of any prime divisor whose generic point lies on it. -/
theorem supportSet_eq_support_of_genericPoint_mem [IsIntegral X] {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [IsIntegral D.subscheme]
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X)) :
    ((D.support : Closeds X) : Set X) = Z.support := by
  have hrange : ((D.support : Closeds X) : Set X) = Set.range D.subschemeι :=
    (Scheme.IdealSheafData.range_subschemeι D).symm
  have hirred : IsIrreducible ((D.support : Closeds X) : Set X) := by
    rw [hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ D.subscheme).image _
      D.subschemeι.isClosedEmbedding.continuous.continuousOn
  have hproper : ((D.support : Closeds X) : Set X) ≠ Set.univ := fun h =>
    ne_bot_of_isEffectiveCartierDivisor hD
      (Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective h))
  exact Z.support_eq_of_isIrreducible (D.support : Closeds X).2 hirred subset_rfl hZ hproper

/-- The generic point of the closed subscheme of an effective Cartier divisor with integral
subscheme is the generic point of any prime divisor whose generic point lies on it. -/
theorem subschemeι_genericPoint_eq_genericPoint [IsIntegral X] {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [IsIntegral D.subscheme]
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X)) :
    D.subschemeι (_root_.genericPoint D.subscheme) = Z.genericPoint := by
  have hsupp := supportSet_eq_support_of_genericPoint_mem hD Z hZ
  have h1 : IsGenericPoint (D.subschemeι (_root_.genericPoint D.subscheme))
      ((D.support : Closeds X) : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι D]
    calc closure ({D.subschemeι (_root_.genericPoint D.subscheme)} : Set X)
        = closure (D.subschemeι '' ({_root_.genericPoint D.subscheme} : Set _)) := by
          rw [Set.image_singleton]
      _ = D.subschemeι '' closure ({_root_.genericPoint D.subscheme} : Set _) :=
          D.subschemeι.isClosedEmbedding.closure_image_eq _
      _ = Set.range D.subschemeι := by rw [genericPoint_closure]; simp
  have h2 : IsGenericPoint Z.genericPoint ((D.support : Closeds X) : Set X) :=
    (Z.support_eq_closure_genericPoint).symm.trans hsupp.symm
  exact h1.eq h2

/-! ### The stalk at the generic point -/

/-- The quotient of the local ring of `X` by the stalk of an ideal sheaf, at the image of the
generic point of its integral subscheme, is a field: it is the local ring of that subscheme at
its generic point, which is the function field. -/
theorem isField_quotient_stalk_subschemeι_genericPoint {D : X.IdealSheafData}
    [IsIntegral D.subscheme] :
    IsField (X.presheaf.stalk (D.subschemeι (_root_.genericPoint D.subscheme)) ⧸
      IdealSheafData.stalk D (D.subschemeι (_root_.genericPoint D.subscheme))) :=
  (IdealSheafData.subschemeStalkQuotEquiv D
    (_root_.genericPoint D.subscheme)).toMulEquiv.isField (Field.toIsField _)

/-- **The stalk of an integral effective Cartier divisor at the generic point of a prime
divisor supported on it is the maximal ideal.** -/
theorem IdealSheafData.stalk_eq_maximalIdeal_genericPoint [IsIntegral X]
    {D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [IsIntegral D.subscheme] (Z : PrimeDivisor X)
    (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X)) :
    IdealSheafData.stalk D Z.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk Z.genericPoint) :=
  IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _
    (subschemeι_genericPoint_eq_genericPoint hD Z hZ ▸
      isField_quotient_stalk_subschemeι_genericPoint (D := D)))

/-- **The multiplicity of a power of an integral effective Cartier divisor** at a prime divisor
supported on it is the exponent: the local ring there is a discrete valuation ring by
[Stacks, Tag 0AG9], and the stalk of `D ^ k` is the `k`-th power of its maximal ideal. -/
theorem effectiveCartierMultiplicity_pow [IsLocallyNoetherian X] [IsIntegral X]
    {D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [IsIntegral D.subscheme] (Z : PrimeDivisor X)
    (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X)) (k : ℕ) :
    effectiveCartierMultiplicity (D ^ k) Z = k := by
  obtain ⟨hdom, hdvr⟩ := isDiscreteValuationRing_stalk_genericPoint D hD
  rw [effectiveCartierMultiplicity, IdealSheafData.stalk_pow,
    IdealSheafData.stalk_eq_maximalIdeal_genericPoint hD Z hZ,
    ← subschemeι_genericPoint_eq_genericPoint hD Z hZ]
  have := hdom
  have := hdvr
  rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp

end AlgebraicGeometry

end
