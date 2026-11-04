module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaStatement

/-!
# The key formula, Stacks 0EQV, coefficient by coefficient

Both sides of the key formula are sums `∑ (Z_i → X)_* c_i` over the locally finite family of
prime divisors `{Z_i}` (`AlgebraicGeometry.Space.keyFormulaDivisorSum`,
`AlgebraicGeometry.Space.keyFormulaTameSum`). Both are `k`-cycles, so they agree as soon as they
have the same coefficient at every integral closed subspace `Y` of δ-dimension `k`, and there the
difference of the coefficients is the (finite) sum over `i` of the differences of the coefficients
of the pushforwards.

## Main results

* `AlgebraicGeometry.Space.CycleGroup.apply_eq_zero_of_deltaDimension_ne`: a `k`-cycle vanishes
  off δ-dimension `k`.
* `AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum_of_finsum_sub_eq_zero`: the
  reduction of the key formula to the vanishing of the sum over `i` of the coefficient
  differences at each `Y` of δ-dimension `k`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)

/-- A `k`-cycle has coefficient zero at an integral closed subspace of δ-dimension other than
`k`. -/
theorem CycleGroup.apply_eq_zero_of_deltaDimension_ne {k : ℤ} (c : CycleGroup D sX k)
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X) (hY : deltaDimension D sX Y ≠ k) :
    c.1 Y = 0 := by
  by_contra h
  exact hY (c.2.2 Y h)

variable (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {k : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    {I : Type*} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

/-- **The coefficient difference of the `i`-th terms of the key formula at `Y`**: the coefficient
at `Y` of `(Z_i → X)_*(ord_{B_i}(f_i) div(t_i|_{Z_i}) - ord_{B_i}(g_i) div(s_i|_{Z_i}))` minus that
of `(Z_i → X)_* div(∂_{B_i}(f_i, g_i))`. -/
def keyFormulaCoeffDiff (Y : IntegralClosedSubspace D.site D.base D.base_mem X) (i : I) : ℤ :=
  (integralClosedSubspacePushforward D sX hX
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) k
      ((Zf i).keyFormulaDivisorCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i))).1 Y -
    (integralClosedSubspacePushforward D sX hX
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) k
      ((Zf i).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i))).1 Y

/-- **Stacks 0EQV, reduced to coefficients.** If at every integral closed subspace `Y` of
δ-dimension `k` the coefficient differences of the terms of the two sides sum to zero, the two
sides of the key formula agree. -/
theorem keyFormulaDivisorSum_eq_keyFormulaTameSum_of_finsum_sub_eq_zero
    (h : ∀ Y : IntegralClosedSubspace D.site D.base D.base_mem X, deltaDimension D sX Y = k →
      ∑ᶠ i, keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w Y i = 0) :
    keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w := by
  refine Subtype.ext (funext fun Y => ?_)
  by_cases hY : deltaDimension D sX Y = k
  · refine sub_eq_zero.mp (Eq.trans (finsum_sub_distrib ?_ ?_).symm (h Y hY)) <;>
      exact finite_support_cycleFamilyCoeff D sX hX
        (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k _ Y
  · simp only [CycleGroup.apply_eq_zero_of_deltaDimension_ne D sX _ Y hY]

/-- The coefficient difference vanishes at an integral closed subspace which is not the image of
one of `Z_i`. -/
theorem keyFormulaCoeffDiff_of_forall_ne (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (i : I)
    (hY : ∀ Y', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX)
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y' ≠ Y) :
    keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w Y i = 0 := by
  unfold keyFormulaCoeffDiff
  simp only [integralClosedSubspacePushforward_apply_of_forall_ne D sX hX _ _ Y hY, sub_zero]

/-- **The coefficient difference at the image of an integral closed subspace `Y'` of `Z_i`**:
`ord_{B_i}(f_i) div(t_i|_{Z_i})(Y') - ord_{B_i}(g_i) div(s_i|_{Z_i})(Y')`
`- div(∂_{B_i}(f_i, g_i))(Y')`. -/
theorem keyFormulaCoeffDiff_pushforward (i : I)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor) :
    keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y') i =
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
        W.isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
      haveI := (Zf i).krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      haveI := (Zf i).nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          ((Zf i).sectionRatio D sX hX hint L hL s hs (v i) : _) (Units.isUnit _) *
          ((Zf i).restrictedGeneratorDivisor D sX hX hint N hN hn (w i)).1 Y' -
        (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          ((Zf i).sectionRatio D sX hX hint N hN t ht (w i) : _) (Units.isUnit _) *
          ((Zf i).restrictedGeneratorDivisor D sX hX hint L hL hn (v i)).1 Y' -
        ((Zf i).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i)).1 Y' := by
  unfold keyFormulaCoeffDiff
  rw [integralClosedSubspacePushforward_apply_pushforward,
    integralClosedSubspacePushforward_apply_pushforward]
  unfold PrimeDivisor.keyFormulaDivisorCycle
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]

section Orders

variable (Z : PrimeDivisor D.site D.base D.base_mem X)
    (P : IntegralClosedSubspace D.site D.base D.base_mem
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor)
    (hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX (Z.toIntegralClosedSubspace D.site D.base
        D.base_mem)).1 P) = 1)

/-- The coefficient of `div_{ℒ|_Z}((v s_ξ)|_Z)` at a prime divisor `P` of `Z` is the order of
vanishing of `(v s_ξ)|_Z` along `P` at the canonical ratio. -/
theorem PrimeDivisor.restrictedGeneratorDivisor_apply
    (v : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    (Z.restrictedGeneratorDivisor D sX hX hint L hL hn v).1 P =
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor =>
        W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX _).1
          (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX _))
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
            (isGood_integralClosedSubspace D sX hX _))
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor =>
        W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX _).1
          (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX _))
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
            (isGood_integralClosedSubspace D sX hX _))
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor =>
        W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX _).1
          (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX _))
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
            (isGood_integralClosedSubspace D sX hX _))
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX _).1
        (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX _))
        (P.toPrimeDivisor D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX _).1 hP)
        (Z.restrictModule D.site D.base D.base_mem hX.1 L)
        (Z.henselianUnitRestriction D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL v)
        ((P.toPrimeDivisor D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX _).1 hP).canonicalLocalRatio D.site D.base
          D.base_mem (isGood_integralClosedSubspace D sX hX _).1
          (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX _))
          (Z.restrictModule D.site D.base D.base_mem hX.1 L)
          (Z.isInvertibleModule_restrictModule D.site D.base D.base_mem hX.1 L hL)
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
            (isGood_integralClosedSubspace D sX hX _))) :=
  canonicalDivisorCycleAt_apply_of_codimension_eq_one D _ (isGood_integralClosedSubspace D sX hX _)
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _ _ _ _ P hP

/-- The coefficient of `div(∂_B(f, g))` at a prime divisor `P` of `Z` is the order of vanishing
of the tame symbol along `P`. -/
theorem PrimeDivisor.keyFormulaTameCycle_apply
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    (Z.keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn v w).1 P =
      ordRationalFunction D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX _).1
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
          (isGood_integralClosedSubspace D sX hX _))
        (Z.keyFormulaTameSymbol D sX hX hint L hL s hs N hN t ht v w)
        (P.toPrimeDivisor D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX _).1
          hP) :=
  canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D _
    (isGood_integralClosedSubspace D sX hX _)
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _ P hP

end Orders

end AlgebraicGeometry.Space

end
