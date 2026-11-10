module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Branch

/-!
# The contribution of one member of the family to the key formula

Let `Z ⊂ X` be a prime divisor (a member `Z_i` of the family of Stacks 0EQV), `P ⊂ Z` a prime
divisor of `Z` with image `Y` of δ-dimension `n - 2`, `V` an affine étale chart of `X` on which
`ℒ`, `𝒩` are free, and `y` a point of `W' = V ×_X Z` over the generic point of `P`, with
`A = 𝒪_{V, π y}` of dimension two. This file computes the contribution of `Z` at `Y`:

`ord_B(f) ord_P(t_ξ'|_Z) - ord_B(g) ord_P(s_ξ'|_Z) - ord_P(∂_B(f, g))
  = -∑_{𝔮 ⊂ A height one over ξ} ord_{A/𝔮}(∂_{A_𝔮}(a, b))`

(`AlgebraicGeometry.Space.PrimeDivisor.keyFormula_member_eq_neg_finsum`): the orders along `P` are
sums over the branches of `W'` at `y` (Stacks 0EQV, chart computation, `PZ`), the branches are the
height-one primes of `A` over `ξ`, and along each branch the identity is
`AlgebraicGeometry.Space.PrimeDivisor.branch_keyFormula_identity`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing Stacks.Chow
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (V : SmallEtale B S hS X)

/-- The scheme of the base change `V ×_X Z` of an affine chart is affine, the projection to `V`
being a closed immersion. -/
theorem PrimeDivisor.isAffine_chartScheme_baseChangeChart (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)) := by
  have := Z.isClosedImmersion_baseChangeChartProj B S hS hX V
  exact isAffine_of_isAffineHom (Z.baseChangeChartProj B S hS hX V)

/-- The scheme of `V ×_X Z` is locally Noetherian when `Z` is. -/
theorem PrimeDivisor.isLocallyNoetherian_chartScheme_baseChangeChart
    (hNZ : HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    IsLocallyNoetherian (chartScheme (Z.baseChangeChart B S hS hX V)) :=
  (exists_atlas_iff_forall_etale B S hS Z.subspace.toFunctor
    (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y) Z.closed.1).mp hNZ
    (Z.baseChangeChart B S hS hX V).obj.left (Z.baseChangeChart B S hS hX V).obj.hom
    (Z.baseChangeChart B S hS hX V).property

/-- A finite sum over a finite type of a pointwise combination `o₁ x - o₂ y - z` is the same
combination of the sums. -/
theorem finsum_mul_sub_mul_sub {ι : Type*} [Finite ι] (o₁ o₂ : ℤ) (x y z : ι → ℤ) :
    o₁ * ∑ᶠ i, x i - o₂ * ∑ᶠ i, y i - ∑ᶠ i, z i = ∑ᶠ i, (o₁ * x i - o₂ * y i - z i) := by
  rw [mul_finsum, mul_finsum, ← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _),
    ← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]

/-! ### The orders along a prime divisor of `Z`, on the chart `V ×_X Z` -/

section Orders

variable (hdec : IsDecentSpace B S hS X)
    (hNX : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hdecZ : IsDecentSpace B S hS Z.subspace.toFunctor)
    (hNZ : HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hV : IsAffine (chartScheme V))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)

/-- **The branch fraction of a restricted generator**: the coefficient of `(v s_ξ)|_Z` against the
restriction of the free generator `e` to `V ×_X Z`, read in `Q(𝒪_{V ×_X Z, y})`. -/
def PrimeDivisor.restrictedGeneratorBranchFraction
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (y : chartScheme (Z.baseChangeChart B S hS hX V)) :
    FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) :=
  chartPointMeromorphicMap B S hS (Z.space B S hS) (Z.baseChangeChart B S hS hX V)
    (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV)
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.space B S hS)
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
        B S hS Z.closed.1 Z.integral)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Z.subspace.toFunctor
        Z.closed.1 hNZ) _ (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV)) y
    (Z.baseChangeChartSectionCoefficient B S hS hX L hL V e hecompat hebij
      (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v))

/-- The branch fraction of a restricted generator is a unit. -/
theorem PrimeDivisor.isUnit_restrictedGeneratorBranchFraction
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (y : chartScheme (Z.baseChangeChart B S hS hX V)) :
    IsUnit (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
      v y) :=
  (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS (Z.space B S hS)
    (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
      B S hS Z.closed.1 Z.integral)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Z.subspace.toFunctor
      Z.closed.1 hNZ) _ _ (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV) _ _ _ _
    (Z.isRegularMeromorphicSection_henselianUnitRestriction B S hS hX hdec hNX L hL v)).map _

include hdecZ in
/-- **The order of `(v s_ξ)|_Z` along a prime divisor `P` of `Z`, as a sum over the branches of
`V ×_X Z` at a point `y` over the generic point of `P`** (Stacks 0EQV, chart computation). -/
theorem PrimeDivisor.orderOfVanishingSection_henselianUnitRestriction_eq_finsum
    (P : PrimeDivisor B S hS Z.subspace.toFunctor)
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (hy : chartSchemeToPoints B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX V) y =
      P.genericPoint B S hS Z.subspace.toFunctor)
    [IsNoetherianRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    [Ring.KrullDimLE 1 ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)] :
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    orderOfVanishingSection.{u, u} B S hS Z.closed.1 hdecZ P (Z.restrictModule B S hS hX L)
        (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v)
        (P.canonicalLocalRatio B S hS Z.closed.1 hdecZ (Z.restrictModule B S hS hX L)
          (Z.isInvertibleModule_restrictModule B S hS hX L hL) Z.integral hNZ) =
      ∑ᶠ p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y),
        Ring.minimalPrimeOrd p
          (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
            v y)
          (Z.isUnit_restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat
            hebij v y) :=
  P.orderOfVanishingSection_canonicalLocalRatio_eq_finsum_minimalPrimeOrd B S hS
    (X := Z.space B S hS) hdecZ Z.integral hNZ
    (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
      B S hS Z.closed.1 Z.integral)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Z.subspace.toFunctor
      Z.closed.1 hNZ) (Z.restrictModule B S hS hX L)
    (Z.isInvertibleModule_restrictModule B S hS hX L hL)
    (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v)
    (Z.isRegularMeromorphicSection_henselianUnitRestriction B S hS hX hdec hNX L hL v)
    (Z.baseChangeChart B S hS hX V) (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV)
    (Z.baseChangeChartGenerator B S hS hX L V e)
    (Z.baseChangeChartGenerator_compat B S hS hX L V e hecompat)
    (Z.bijective_smul_baseChangeChartGenerator B S hS hX L hL V e hecompat hebij) y hy _

/-- **The order of a rational function of `Z` along a prime divisor `P` of `Z`, as a sum over the
branches of `V ×_X Z` at a point `y` over the generic point of `P`.** -/
theorem PrimeDivisor.ordRationalFunction_eq_finsum_branch
    [IsAffine (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsReduced (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsLocallyNoetherian (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    (P : PrimeDivisor B S hS Z.subspace.toFunctor)
    (y : (Z.baseChangeChart B S hS hX V).obj.left.left.1)
    (hy : chartSchemeToPoints B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX V) y =
      P.genericPoint B S hS Z.subspace.toFunctor)
    [Ring.KrullDimLE 1 ((Z.baseChangeChart B S hS hX V).obj.left.left.1.presheaf.stalk y)]
    (f : (rationalFunctions B S hS Z.closed.1)ˣ) :
    ordRationalFunction B S hS Z.closed.1 Z.integral hNZ f P =
      ∑ᶠ p : minimalPrimes ((Z.baseChangeChart B S hS hX V).obj.left.left.1.presheaf.stalk y),
        Ring.minimalPrimeOrd p
          (chartPointRationalFunctionMap B S hS Z.closed.1 (Z.baseChangeChart B S hS hX V) y
            (f : rationalFunctions B S hS Z.closed.1)) (f.isUnit.map _) :=
  P.ord_eq_finsum_minimalPrimeOrd B S hS Z.closed.1 Z.integral.isDecentSpace Z.integral hNZ
    (Z.baseChangeChart B S hS hX V) y hy f

/-- **(G2) along a branch**: the statement (G2) at the generic point of a branch of `V ×_X Z` at
`y`, moved to the point of the height-one prime `𝔮` of the branch, gives the reading of the
branch fraction of `(v s_ξ)|_Z` in `κ(𝒪_{X, x̄})`: `v̄ μ̄⁻¹`. -/
theorem PrimeDivisor.residueFieldMap_branchReading_restrictedGeneratorBranchFraction
    (hInt : IsIntegralSpace B S hS X) (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hG2 : Z.UnitRestrictionReading B S hS hX hdec hInt hNX V hV L hL e hecompat hebij hNZ
      (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV) v)
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) (μ)
    (hμ : Z.IsChartRatioUnit B S hS hX hdec hInt hNX V hV L hL e hecompat hebij _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 μ) :
    haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
    ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
        (Z.branchReading B S hS hX V hdec y p
          (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
            v y)) =
      residue _ (Z.henselianToEtaleLocalRing B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2) v) *
      (residue _ μ.val)⁻¹ := by
  have hq' := Z.chartSchemeToPoints_baseChangeChartProj_fromSpecStalk B S hS hX V hdec y p
  have hip := Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y
    ⟨p.1, p.2.1.1⟩ (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 rfl
  have step1 : Z.heightOneResidueFieldEquiv B S hS hX V _
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 _ hip
      (Z.branchReading B S hS hX V hdec y p
        (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
          v y)) =
      Z.baseChangeChartSectionReading B S hS hX L hL V e hecompat hebij
        (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV)
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.space B S hS)
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS Z.closed.1 Z.integral)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS
            Z.subspace.toFunctor Z.closed.1 hNZ) _
          (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV)) _
        (Z.isField_stalk_baseChangeChart B S hS hX V _ hq')
        (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v) :=
    ((Z.heightOneResidueFieldEquiv B S hS hX V _ _ _ hip).apply_symm_apply _).trans
      (totalFractionToResidueFieldOfSpecializes_chartPointMeromorphicMap B S hS (Z.space B S hS)
        (Z.baseChangeChart B S hS hX V) (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV) _
        _ (Z.isField_stalk_fromSpecStalk_minimalPrime B S hS hX V hdec y p)
        (Stacks.Chow.specializes_fromSpecStalk y ⟨p.1, p.2.1.1⟩) _)
  have hq : chartSchemeToPoints B S hS X V (Stacks.Chow.intermediatePointOfHeightOnePrime
      (Z.baseChangeChartProj B S hS hX V y)
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1) =
      Z.genericPoint B S hS X :=
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2
  have step2 := (Z.baseChangeChartResidueFieldEquiv_symm_heightOneResidueFieldEquiv B S hS hX V _
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 _ hip
    (Z.branchReading B S hS hX V hdec y p
        (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
          v y))).symm.trans
    (congrArg (Z.baseChangeChartResidueFieldEquiv B S hS hX V _).symm step1)
  have h2 := Z.chartResidueFieldToEtale_eq_mul_of_eq B S hS hX hdec hInt hNX V hV L hL e hecompat
    hebij hip hq hq'
    (ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv _
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
      (Z.branchReading B S hS hX V hdec y p
        (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
          v y)))
    (@IsLocalRing.residue _ _ (henselianLocalRing_isLocalRing B S hS X hX
      (Z.genericPoint B S hS X) hdec) (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)))
    (fun μ' hμ' => (congrArg (chartResidueFieldToEtale B S hS hX V _) step2).trans
      (hG2 _ hq' μ' hμ')) μ hμ
  refine Eq.trans ?_ (h2.trans ?_)
  · exact (chartResidueFieldToEtale_mapEquiv_stalkLocalizationAtPrimeEquiv B S hS hX V _ _ _).symm
  · rfl

end Orders

/-! ### The contribution of `Z` -/

section Member

variable (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hNX : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hdecZ : IsDecentSpace B S hS Z.subspace.toFunctor)
    (hNZ : HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hV : IsAffine (chartScheme V))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (N : Modules.{u, u} B S hS X hX) (hN' : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (e' : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat' : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (e' W k) = e' W' (g ≫ k))
    (hebij' : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e' W k)
    (P : PrimeDivisor B S hS Z.subspace.toFunctor)
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    [IsNoetherianRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))]
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) = 2)
    (hy : chartSchemeToPoints B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX V) y =
      P.genericPoint B S hS Z.subspace.toFunctor)

include hInt hy in
/-- **The contribution of a member `Z` of the family at a prime divisor `P` of `Z`, computed on a
chart.** With `s = f (v₁ s_ξ)`, `t = g (v₂ t_ξ)` at the generic point of `Z`, `s = a e_ℒ`,
`t = b e_𝒩` on `V`, and the readings (G2) of `(v₁ s_ξ)|_Z`, `(v₂ t_ξ)|_Z` along the branches of
`V ×_X Z` at `y`:

`ord_B(f) ord_P((v₂ t_ξ)|_Z) - ord_B(g) ord_P((v₁ s_ξ)|_Z) - ord_P(∂_B(f, g))
  = -∑_{𝔮 ⊂ A height one over ξ} ord_{A/𝔮}(∂_{A_𝔮}(a, b))`, `A = 𝒪_{V, π y}`. -/
theorem PrimeDivisor.keyFormula_member_eq_neg_finsum
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)))ˣ)
    (ha : (a : FractionRing
        ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNX) V hV) _
        (chartRatio B S hS X hX L V e hecompat hebij s))
    (hb : (b : FractionRing
        ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNX) V hV) _
        (chartRatio B S hS X hX N V e' hecompat' hebij' t))
    (f g : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (v₁ v₂ : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hfv : (f : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₁ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hNX s)
    (hgv : (g : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₂ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec N hN' hInt hNX t)
    (hRL : ∀ p μ, Z.IsChartRatioUnit B S hS hX hdec hInt hNX V hV L hL e hecompat hebij _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 μ →
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
          (Z.branchReading B S hS hX V hdec y p
            (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
              v₁ y)) =
        residue _ (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V _).trans
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2) v₁) *
        (residue _ μ.val)⁻¹)
    (hRN : ∀ p μ, Z.IsChartRatioUnit B S hS hX hdec hInt hNX V hV N hN' e' hecompat' hebij' _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 μ →
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
          (Z.branchReading B S hS hX V hdec y p
            (Z.restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV N hN' e' hecompat'
              hebij' v₂ y)) =
        residue _ (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V _).trans
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2) v₂) *
        (residue _ μ.val)⁻¹) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNX
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit *
        orderOfVanishingSection.{u, u} B S hS Z.closed.1 hdecZ P (Z.restrictModule B S hS hX N)
          (Z.henselianUnitRestriction B S hS hX hdec hNX N hN' v₂)
          (P.canonicalLocalRatio B S hS Z.closed.1 hdecZ (Z.restrictModule B S hS hX N)
            (Z.isInvertibleModule_restrictModule B S hS hX N hN') Z.integral hNZ) -
      Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (g : Z.genericTotalFractionRing B S hS hX hdec) g.isUnit *
        orderOfVanishingSection.{u, u} B S hS Z.closed.1 hdecZ P (Z.restrictModule B S hS hX L)
          (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v₁)
          (P.canonicalLocalRatio B S hS Z.closed.1 hdecZ (Z.restrictModule B S hS hX L)
            (Z.isInvertibleModule_restrictModule B S hS hX L hL) Z.integral hNZ) -
      ordRationalFunction B S hS Z.closed.1 Z.integral hNZ
        (Units.map (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).toRingHom.toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
            (Z.genericTotalFractionRing B S hS hX hdec) f g)) P =
      -∑ᶠ 𝔮 : Z.HeightOnePrimeOver B S hS V (Z.baseChangeChartProj B S hS hX V y),
        heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)
          (tameSymbolOfKrullDimOne
            (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V _ 𝔮.1))
            (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V _ 𝔮.1).1.asIdeal))
            (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)).toMonoidHom a)
            (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)).toMonoidHom
              b)) := by
  have : IsAffine (Z.baseChangeChart B S hS hX V).obj.left.left.1 :=
    Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV
  have : IsReduced (Z.baseChangeChart B S hS hX V).obj.left.left.1 :=
    Z.isReduced_chartScheme_baseChangeChart B S hS hX V
  have : IsLocallyNoetherian (Z.baseChangeChart B S hS hX V).obj.left.left.1 :=
    Z.isLocallyNoetherian_chartScheme_baseChangeChart B S hS hX V hNZ
  have : IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)) :=
    Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV
  have : IsLocallyNoetherian (chartScheme (Z.baseChangeChart B S hS hX V)) :=
    Z.isLocallyNoetherian_chartScheme_baseChangeChart B S hS hX V hNZ
  have := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNX
  have := P.krullDimLE_chartStalk B S hS Z.closed.1 hdecZ (Z.baseChangeChart B S hS hX V) y hy
  have : Ring.KrullDimLE 1 ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) :=
    P.krullDimLE_chartStalk B S hS Z.closed.1 hdecZ (Z.baseChangeChart B S hS hX V) y hy
  have : IsNoetherianRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) :=
    inferInstance
  have e1 := Z.orderOfVanishingSection_henselianUnitRestriction_eq_finsum B S hS hX V hdec hNX
    hdecZ hNZ hV N hN' e' hecompat' hebij' P v₂ y hy
  have e2 := Z.orderOfVanishingSection_henselianUnitRestriction_eq_finsum B S hS hX V hdec hNX
    hdecZ hNZ hV L hL e hecompat hebij P v₁ y hy
  have e3 := Z.ordRationalFunction_eq_finsum_branch B S hS hX V hNZ P y hy
    (Units.map (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).toRingHom.toMonoidHom
      (tameSymbolOfKrullDimOne
        (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
        (Z.genericTotalFractionRing B S hS hX hdec) f g))
  have : Finite (minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) :=
    (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
  refine (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg (_ * ·) e1) (congrArg (_ * ·) e2))
    e3).trans ((finsum_mul_sub_mul_sub _ _ _ _ _).trans ?_)
  refine Eq.trans ?_ (congrArg (fun z => -z)
    (finsum_comp_equiv (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y)))
  refine Eq.trans ?_ (finsum_neg_distrib _)
  refine finsum_congr fun p => ?_
  have hRd := Z.residueFieldMap_branchReading_henselianResidueFieldEquivFunctionField B S hS hX
    hdec V y p (tameSymbolOfKrullDimOne
        (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
        (Z.genericTotalFractionRing B S hS hX hdec) f g).val
  exact Z.branch_keyFormula_identity B S hS hX hdec hInt hNX V hV L hL e hecompat hebij y hdim p
    N hN' e' hecompat' hebij' s t a b ha hb f g v₁ v₂ hfv hgv _ _ _
    (Z.isUnit_restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV L hL e hecompat hebij
      v₁ y)
    (Z.isUnit_restrictedGeneratorBranchFraction B S hS hX V hdec hNX hNZ hV N hN' e' hecompat'
      hebij' v₂ y)
    ((Units.map (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).toRingHom.toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
            (Z.genericTotalFractionRing B S hS hX hdec) f g)).isUnit.map _) (hRL p) (hRN p) hRd


include hInt hy in
/-- **The contribution of a member `Z` of the family**, with the readings of the restricted
generators supplied by the statement (G2)
(`AlgebraicGeometry.Space.PrimeDivisor.UnitRestrictionReading`). -/
theorem PrimeDivisor.keyFormula_member_eq_neg_finsum_of_unitRestrictionReading
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)))ˣ)
    (ha : (a : FractionRing
        ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNX) V hV) _
        (chartRatio B S hS X hX L V e hecompat hebij s))
    (hb : (b : FractionRing
        ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNX) V hV) _
        (chartRatio B S hS X hX N V e' hecompat' hebij' t))
    (f g : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (v₁ v₂ : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hfv : (f : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₁ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hNX s)
    (hgv : (g : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₂ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec N hN' hInt hNX t)
    (hG2L : Z.UnitRestrictionReading B S hS hX hdec hInt hNX V hV L hL e hecompat hebij hNZ
      (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV) v₁)
    (hG2N : Z.UnitRestrictionReading B S hS hX hdec hInt hNX V hV N hN' e' hecompat' hebij' hNZ
      (Z.isAffine_chartScheme_baseChangeChart B S hS hX V hV) v₂) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNX
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    haveI : ∀ W : PrimeDivisor B S hS Z.subspace.toFunctor,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Z.closed.1 hdecZ) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Z.closed.1 hdecZ Z.integral hNZ
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit *
        orderOfVanishingSection.{u, u} B S hS Z.closed.1 hdecZ P (Z.restrictModule B S hS hX N)
          (Z.henselianUnitRestriction B S hS hX hdec hNX N hN' v₂)
          (P.canonicalLocalRatio B S hS Z.closed.1 hdecZ (Z.restrictModule B S hS hX N)
            (Z.isInvertibleModule_restrictModule B S hS hX N hN') Z.integral hNZ) -
      Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (g : Z.genericTotalFractionRing B S hS hX hdec) g.isUnit *
        orderOfVanishingSection.{u, u} B S hS Z.closed.1 hdecZ P (Z.restrictModule B S hS hX L)
          (Z.henselianUnitRestriction B S hS hX hdec hNX L hL v₁)
          (P.canonicalLocalRatio B S hS Z.closed.1 hdecZ (Z.restrictModule B S hS hX L)
            (Z.isInvertibleModule_restrictModule B S hS hX L hL) Z.integral hNZ) -
      ordRationalFunction B S hS Z.closed.1 Z.integral hNZ
        (Units.map (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).toRingHom.toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hNX)
            (Z.genericTotalFractionRing B S hS hX hdec) f g)) P =
      -∑ᶠ 𝔮 : Z.HeightOnePrimeOver B S hS V (Z.baseChangeChartProj B S hS hX V y),
        heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)
          (tameSymbolOfKrullDimOne
            (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V _ 𝔮.1))
            (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V _ 𝔮.1).1.asIdeal))
            (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)).toMonoidHom a)
            (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _ 𝔮.1)).toMonoidHom
              b)) :=
  Z.keyFormula_member_eq_neg_finsum B S hS hX V hdec hInt hNX hdecZ hNZ hV L hL e hecompat hebij
    N hN' e' hecompat' hebij' P y hdim hy s t a b ha hb f g v₁ v₂ hfv hgv
    (fun p μ hμ => Z.residueFieldMap_branchReading_restrictedGeneratorBranchFraction B S hS hX V
      hdec hNX hNZ hV L hL e hecompat hebij hInt v₁ hG2L y p μ hμ)
    (fun p μ hμ => Z.residueFieldMap_branchReading_restrictedGeneratorBranchFraction B S hS hX V
      hdec hNX hNZ hV N hN' e' hecompat' hebij' hInt v₂ hG2N y p μ hμ)

end Member

end AlgebraicGeometry.Space

end
