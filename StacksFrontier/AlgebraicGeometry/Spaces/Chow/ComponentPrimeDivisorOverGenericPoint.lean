module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentHenselianIdealIncidence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients

/-!
# A prime divisor on each irreducible component through the generic point of a prime divisor

In Situation 0EDT let `Y/B` be good, let `Z ⊆ Y` be a prime divisor with generic point `ξ`, and
let `W` be an irreducible component of `|Y|` through `ξ`, cut out by the reduced induced closed
subspace `Y_W ⊆ Y`.  The point `ξ` lies on `Y_W`, and the reduced induced closed subspace of
`Y_W` on the closure of `ξ` there is a prime divisor of `Y_W` **as soon as**
`dim_δ(Y_W) = dim_δ(Z) + 1`.

The δ-dimension hypothesis cannot be dropped: `ξ` has codimension one in `|Y|`, but codimension
`0` in a component of which it is itself the generic point, as happens when `Y` has a component
of δ-dimension `dim_δ(Z)`.

## Main results

* `AlgebraicGeometry.Space.exists_primeDivisor_pointsMap_genericPoint_eq_of_deltaDimension`:
  the prime divisor `Z_W` of `Y_W` with generic point over `ξ`.
* `AlgebraicGeometry.Space.exists_natCast_ord_sub_eq_finsum_components_mul_of_isGood`: the
  additivity of the order of vanishing over the irreducible components at `A = 𝒪^h_{Y, ξ}`, for
  `Y` good over the base and every component through `ξ` of δ-dimension `dim_δ(Z) + 1`, together
  with prime divisors of the components whose generic points lie over `ξ`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A prime divisor on a component through the generic point -/

section ComponentPrimeDivisor

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hYdec : IsDecentSpace D.site D.base D.base_mem Y)

include hY hYdec in
/-- **A prime divisor on an irreducible component through the generic point of a prime
divisor.** In Situation 0EDT let `Y/B` be good and decent, let `Z` be a prime divisor of `Y`
with generic point `ξ`, and let `W` be an irreducible component of `|Y|` containing `ξ`, cut out
by the reduced induced closed subspace `Y_W`.  If `dim_δ(Y_W) = dim_δ(Z) + 1` then `Y_W` carries
a prime divisor whose generic point lies over `ξ`. -/
theorem exists_primeDivisor_pointsMap_genericPoint_eq_of_deltaDimension
    (Z : PrimeDivisor D.site D.base D.base_mem Y)
    (W : irreducibleComponents (points D.site D.base D.base_mem Y))
    (hW : Z.genericPoint D.site D.base D.base_mem Y ∈
      (W : Set (points D.site D.base D.base_mem Y)))
    (hdim : deltaDimension D sY
        (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY.1 hYdec W) =
      deltaDimension D sY (Z.toIntegralClosedSubspace D.site D.base D.base_mem) + 1) :
    ∃ ZW : PrimeDivisor D.site D.base D.base_mem
        (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY.1 hYdec
          W).subspace.toFunctor,
      pointsMap D.site D.base D.base_mem
          (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY.1 hYdec
            W).subspace.toFunctor
          (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY.1 hYdec
            W).subspace.ι
          (ZW.genericPoint D.site D.base D.base_mem _) =
        Z.genericPoint D.site D.base D.base_mem Y := by
  set YW := integralClosedSubspaceOfComponent D.site D.base D.base_mem hY.1 hYdec W with hYW
  set ξ := Z.genericPoint D.site D.base D.base_mem Y with hξ
  have hmem : ξ ∈ subspacePointSet D.site D.base D.base_mem Y YW.subspace := by
    rwa [hYW, subspacePointSet_integralClosedSubspaceOfComponent]
  obtain ⟨ξW, hξW⟩ := hmem
  have hWgood : D.IsGood (YW.subspace.ι ≫ sY) := isGood_integralClosedSubspace D sY hY YW
  have hWdec : IsDecentSpace D.site D.base D.base_mem YW.subspace.toFunctor :=
    YW.isIntegralSpace.isDecentSpace
  set ZW' := integralClosedSubspaceOfPoint D.site D.base D.base_mem YW.isClosedSubspace.1
    hWdec ξW with hZW'
  have hamb : ZW'.ambientGenericPoint D.site D.base D.base_mem = ξW :=
    pointsMap_genericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem
      YW.isClosedSubspace.1 hWdec ξW
  have hpush : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1
        YW.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) YW.isClosedSubspace.2
        ZW').subspace) := by
    have h := (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1
      YW.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) YW.isClosedSubspace.2
      ZW').isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1
    rwa [IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hY.1
      YW.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) YW.isClosedSubspace.2 ZW',
      hamb, hξW] at h
  have hZdim : deltaDimension D sY (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      D.deltaValue sY ξ :=
    deltaDimension_eq_of_isGenericPoint D sY hY.1 _ ξ
      (Z.isGenericPoint_genericPoint D.site D.base D.base_mem Y)
  have hpushdim : deltaDimension D sY (IntegralClosedSubspace.pushforward D.site D.base
      D.base_mem hY.1 YW.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY)
      YW.isClosedSubspace.2 ZW') = D.deltaValue sY ξ :=
    deltaDimension_eq_of_isGenericPoint D sY hY.1 _ ξ hpush
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sY hY YW).1 ZW') = 1 :=
    codimension_eq_one_of_deltaDimension_pushforward D sY hY YW
      (by rw [hdim, hZdim]) ZW' hpushdim
  refine ⟨ZW'.toPrimeDivisor D.site D.base D.base_mem YW.isClosedSubspace.1 hcod, ?_⟩
  have _ht0 : T0Space (points D.site D.base D.base_mem YW.subspace.toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem YW.isClosedSubspace.1 hWdec
  have hgenW : IsGenericPoint ξW
      (subspacePointSet D.site D.base D.base_mem YW.subspace.toFunctor
        (ZW'.toPrimeDivisor D.site D.base D.base_mem YW.isClosedSubspace.1 hcod).subspace) := by
    rw [IntegralClosedSubspace.subspace_toPrimeDivisor]
    exact isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem
      YW.isClosedSubspace.1 hWdec ξW
  have heq : (ZW'.toPrimeDivisor D.site D.base D.base_mem YW.isClosedSubspace.1
      hcod).genericPoint D.site D.base D.base_mem _ = ξW :=
    IsGenericPoint.eq
      ((ZW'.toPrimeDivisor D.site D.base D.base_mem YW.isClosedSubspace.1
        hcod).isGenericPoint_genericPoint D.site D.base D.base_mem _) hgenW
  rwa [heq]

end ComponentPrimeDivisor

/-! ### The additivity over the components, with the prime divisors of the components supplied -/

section Additivity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (sY : Y ⟶ D.space) (hYg : D.IsGood sY)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (Z : PrimeDivisor D.site D.base D.base_mem Y)

include hY hYg hYdec in
/-- **The additivity of the order of vanishing over the irreducible components, at
`A = 𝒪^h_{Y, ξ}`, for `Y` good over the base.** Let `Y` be an algebraic space (for
instance a closed subspace of an ambient space) which is good over the base of Situation 0EDT, let
`Z` be a prime divisor of `Y` with generic point `ξ`, and assume every irreducible component of
`|Y|` through `ξ` has δ-dimension `dim_δ(Z) + 1`. Write `A = 𝒪^h_{Y, ξ}` for the henselian local
ring of Stacks 0ENK there. Then for nonzerodivisors `a`, `b` of `A` of finite colength there are
ideals `I i` of `A`, indexed by the components `Y_i` of `|Y|` through `ξ`, together with prime
divisors `Z_i` of `Y_i` whose generic points lie over `ξ`, such that `A ⧸ I i ≅ 𝒪^h_{Y_i, ξ_i}` and

  `ord_A(a) - ord_A(b) = ∑_i m_{Y_i, Y} · (ord_{A ⧸ I i}(a) - ord_{A ⧸ I i}(b))`,

`m_{Y_i, Y}` being the multiplicity of Stacks 0EE9 of the `i`-th component. -/
theorem exists_natCast_ord_sub_eq_finsum_components_mul_of_isGood
    (hdim : ∀ W : irreducibleComponents (points D.site D.base D.base_mem Y),
      Z.genericPoint D.site D.base D.base_mem Y ∈
          (W : Set (points D.site D.base D.base_mem Y)) →
        deltaDimension D sY
            (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec W) =
          deltaDimension D sY (Z.toIntegralClosedSubspace D.site D.base D.base_mem) + 1)
    (a b : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))
    (ha : IsSMulRegular ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) a)
    (hb : IsSMulRegular ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) b)
    (hfa : Module.length ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸
        Ideal.span {a}) ≠ ⊤)
    (hfb : Module.length ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸
        Ideal.span {b}) ≠ ⊤) :
    ∃ (Zc : ∀ i : Z.genericComponentIndex D Y hY hYdec,
          PrimeDivisor D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor)
        (_ : ∀ i, pointsMap D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.ι
            ((Zc i).genericPoint D.site D.base D.base_mem
              (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor) =
          Z.genericPoint D.site D.base D.base_mem Y)
        (I : Z.genericComponentIndex D Y hY hYdec →
          Ideal ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)),
      (∀ i, Nonempty
        ((↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸ I i) ≃+*
          ↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace))) ) ∧
      ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
            a).toNat : ℤ) -
          ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
            b).toNat : ℤ) =
        ∑ᶠ i : Z.genericComponentIndex D Y hY hYdec,
          irreducibleComponentMultiplicity D Y hY hYdec i.1 *
            (((Ring.ord
                (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸ I i)
                (Ideal.Quotient.mk (I i) a)).toNat : ℤ) -
              ((Ring.ord
                (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸ I i)
                (Ideal.Quotient.mk (I i) b)).toNat : ℤ)) := by
  have hmem : ∀ i : Z.genericComponentIndex D Y hY hYdec,
      Z.genericPoint D.site D.base D.base_mem Y ∈
        (i.1 : Set (points D.site D.base D.base_mem Y)) := by
    intro i
    exact (Z.chartSchemeToPoints_genericEtaleChart_point D.site D.base D.base_mem hY
      hYdec).subst
      (motive := fun p => p ∈ (i.1 : Set (points D.site D.base D.base_mem Y))) i.2
  choose Zc hZc using fun i : Z.genericComponentIndex D Y hY hYdec =>
    exists_primeDivisor_pointsMap_genericPoint_eq_of_deltaDimension D sY hYg hYdec Z i.1
      (hmem i) (hdim i.1 (hmem i))
  exact ⟨Zc, hZc, exists_natCast_ord_sub_eq_finsum_components_mul D Y hY hYdec
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hYg) Z
    (fun i => hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
      ((Z.genericComponentSubspace D Y hY hYdec i).subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hYg (Z.genericComponentSubspace D Y hY hYdec i)))
    Zc hZc a b ha hb hfa hfb⟩

end Additivity

end AlgebraicGeometry.Space

end
