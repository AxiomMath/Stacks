module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Hub
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Reading

/-!
# The identity of the key formula along one branch

Let `V` be an affine étale chart of `X`, `Z ⊂ X` a prime divisor with generic point `ξ`,
`W' = V ×_X Z` and `y ∈ W'` with `A = 𝒪_{V, π y}` of dimension two. A branch of `W'` at `y` (a
minimal prime `𝔭` of `𝒪_{W', y}`) has a generic point `q'` and determines a height-one prime
`𝔮 = 𝔭 ∩ A` over `ξ`. This file combines

* the order transport along the branch
  (`AlgebraicGeometry.Space.PrimeDivisor.minimalPrimeOrd_eq_heightOneOrd_branchReading`),
* the readings at `q'` in the residue field of the étale local ring (Stacks 0EMZ, H3, G1', G2),
  moved to the point of `𝔮`, and
* the comparison of tame symbols at `𝔮`
  (`AlgebraicGeometry.Space.heightOnePrime_keyFormula_identity`)

into the identity of Stacks 0EQV along the branch
(`AlgebraicGeometry.Space.PrimeDivisor.branch_keyFormula_identity`):

`ord_B(f) ord_𝔭(t̄) - ord_B(g) ord_𝔭(s̄) - ord_𝔭(∂_B(f, g)) = -ord_{A/𝔮}(∂_{A_𝔮}(a, b))`.

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
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) (V : SmallEtale B S hS X) (hV : IsAffine (chartScheme V))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)

/-- **The relation of the ratio comparison (H3) at a point `q` of `V` over `ξ`**: `μ` is a unit of
the étale local ring at the geometric point over `q` with `s / s_ξ = (s / e) · μ` in `Q(𝒪_{X, x̄})`
for every meromorphic section `s` of `ℒ`. -/
def PrimeDivisor.IsChartRatioUnit (q : chartScheme V)
    (hq : chartSchemeToPoints B S hS X V q = Z.genericPoint B S hS X)
    (μ : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V q) : Type (u + 1))ˣ) : Prop :=
  ∀ s : MeromorphicSection.{u, u} B S hS X hX L,
    Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
        (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V q).trans hq))
        (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V q).trans hq) hr)
        (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s) =
      affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
          (chartNeighborhoodAt B S hS hX V q) hV (chartRatio B S hS X hX L V e hecompat hebij s) *
        algebraMap _ _ μ.val

/-- The unit of the ratio comparison exists at every point of `V` over `ξ` (H3). -/
theorem PrimeDivisor.exists_isChartRatioUnit (q : chartScheme V)
    (hq : chartSchemeToPoints B S hS X V q = Z.genericPoint B S hS X) :
    ∃ μ, Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij q hq μ :=
  Z.exists_unit_canonicalGenericRatio_eq B S hS hX hdec hInt hN L hL
    ((chartGeometricPointAt_liesOver B S hS hX V q).trans hq) (chartNeighborhoodAt B S hS hX V q)
    hV e hecompat hebij

/-- A reading identity of the shape of (G2) transports along an equality of points of `V`. -/
theorem PrimeDivisor.chartResidueFieldToEtale_eq_mul_of_eq {q₁ q₂ : chartScheme V}
    (h12 : q₁ = q₂) (h₁ : chartSchemeToPoints B S hS X V q₁ = Z.genericPoint B S hS X)
    (h₂ : chartSchemeToPoints B S hS X V q₂ = Z.genericPoint B S hS X)
    (r : (chartScheme V).residueField q₁)
    (c : letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (h : ∀ μ, Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij q₂ h₂ μ →
      chartResidueFieldToEtale B S hS hX V q₂ (((chartScheme V).residueFieldCongr h12).hom r) =
        Z.henselianResidueFieldToEtale B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V q₂).trans h₂) c *
        (@IsLocalRing.residue _ _ (isLocalRing_etaleLocalRing B S hS X hX
          (chartGeometricPointAt B S hS hX V q₂)) μ.val)⁻¹)
    (μ : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V q₁) : Type (u + 1))ˣ)
    (hμ : Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij q₁ h₁ μ) :
    chartResidueFieldToEtale B S hS hX V q₁ r =
      Z.henselianResidueFieldToEtale B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V q₁).trans h₁) c *
      (@IsLocalRing.residue _ _ (isLocalRing_etaleLocalRing B S hS X hX
        (chartGeometricPointAt B S hS hX V q₁)) μ.val)⁻¹ := by
  subst h12
  exact h μ hμ

/-! ### The reading of a rational function of `Z` along a branch (G1' and B4) -/

section Rational

variable [IsAffine (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsReduced (Z.baseChangeChart B S hS hX V).obj.left.left.1]
    [IsLocallyNoetherian (Z.baseChangeChart B S hS hX V).obj.left.left.1]

/-- **The branch reading of a rational function `f` of `Z`, in `κ(𝒪_{X, x̄})`, is the residue of
`θ⁻¹ f`**: (B4) identifies the branch reading with the value of `f` at the generic point `q'` of
the branch, and (G1') reads that value in `κ(𝒪_{X, x̄})`. -/
theorem PrimeDivisor.residueFieldMap_branchReading_chartPointRationalFunctionMap
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (f : rationalFunctions B S hS Z.closed.1) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
    haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      ((chartGeometricPointAt_liesOver B S hS hX V _).trans
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2)
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
    ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
        (Z.branchReading B S hS hX V hdec y p
          (chartPointRationalFunctionMap B S hS Z.closed.1 (Z.baseChangeChart B S hS hX V) y f)) =
      ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2))
        ((Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).symm f) := by
  have hq' := Z.chartSchemeToPoints_baseChangeChartProj_fromSpecStalk B S hS hX V hdec y p
  have hz := Z.isField_stalk_fromSpecStalk_minimalPrime B S hS hX V hdec y p
  have hB4 := Z.totalFractionToResidueFieldOfSpecializes_chartPointRationalFunctionMap B S hS hX V
    _ hq' hz (Stacks.Chow.specializes_fromSpecStalk y ⟨p.1, p.2.1.1⟩) f
  have hG1 := Z.chartResidueFieldToEtale_baseChangeChartRationalReading B S hS hX hdec V _ hq' f
  refine Z.residueFieldMap_heightOnePrimeToEtaleLocalRing_eq B S hS hX V _
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
    ((chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecStalk y ⟨p.1, p.2.1.1⟩)
    (Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y ⟨p.1, p.2.1.1⟩
      _ rfl) hdec
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 hq' _ _ (Eq.trans ?_ hG1)
  congr 2
  refine Eq.trans ?_ hB4
  exact RingEquiv.apply_symm_apply _ _

/-- The branch reading of `θ(c)`, for `c ∈ κ(𝒪^h_{X, ξ})`, in `κ(𝒪_{X, x̄})` is the residue of
`c`. -/
theorem PrimeDivisor.residueFieldMap_branchReading_henselianResidueFieldEquivFunctionField
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (c : letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
    haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      ((chartGeometricPointAt_liesOver B S hS hX V _).trans
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2)
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
    ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
        (Z.branchReading B S hS hX V hdec y p
          (chartPointRationalFunctionMap B S hS Z.closed.1 (Z.baseChangeChart B S hS hX V) y
            (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec c))) =
      ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2)) c :=
  (Z.residueFieldMap_branchReading_chartPointRationalFunctionMap B S hS hX hdec V y p _).trans
    (congrArg _ ((Z.henselianResidueFieldEquivFunctionField B S hS hX hdec).symm_apply_apply c))

end Rational

/-! ### The identity along a branch -/

section Identity

variable (y : chartScheme (Z.baseChangeChart B S hS hX V))
    [IsNoetherianRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))]
    [IsNoetherianRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    [Ring.KrullDimLE 1 ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) = 2)
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))

include hInt hN in
/-- **The identity of Stacks 0EQV along a branch.** Let `𝔭` be a branch of `W'` at `y`, with
height-one prime `𝔮` of `A = 𝒪_{V, π y}` over `ξ`. Let `F_ℒ, F_𝒩, F_∂` be units of `Q(𝒪_{W', y})`
whose branch readings, in `κ(𝒪_{X, x̄})`, are `v̄₁ μ̄⁻¹` and `v̄₂ μ̄'⁻¹` for every unit `μ`, `μ'`
of the ratio comparison of `ℒ`, `𝒩`, and `∂_B(f, g)`. Then
`ord_B(f) ord_𝔭(F_𝒩) - ord_B(g) ord_𝔭(F_ℒ) - ord_𝔭(F_∂) = -ord_{A/𝔮}(∂_{A_𝔮}(a, b))`. -/
theorem PrimeDivisor.branch_keyFormula_identity
    (N : Modules.{u, u} B S hS X hX) (hN' : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (e' : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat' : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (e' W k) = e' W' (g ≫ k))
    (hebij' : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e' W k)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk
        (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) _
        (chartRatio B S hS X hX L V e hecompat hebij s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk
        (Z.baseChangeChartProj B S hS hX V y))) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) _
        (chartRatio B S hS X hX N V e' hecompat' hebij' t))
    (f g : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (v₁ v₂ : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hfv : (f : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₁ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s)
    (hgv : (g : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v₂ : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec N hN' hInt hN t)
    (FL FN Fd : FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (hFL : IsUnit FL) (hFN : IsUnit FN) (hFd : IsUnit Fd)
    (hRL : ∀ μ, Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 μ →
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
          (Z.branchReading B S hS hX V hdec y p FL) =
        residue _ (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V _).trans
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2) v₁) *
        (residue _ μ.val)⁻¹)
    (hRN : ∀ μ, Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV N hN' e' hecompat' hebij' _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2 μ →
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
          (Z.branchReading B S hS hX V hdec y p FN) =
        residue _ (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V _).trans
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2) v₂) *
        (residue _ μ.val)⁻¹)
    (hRd : haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
      haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2)
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V _
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
          (Z.branchReading B S hS hX V hdec y p Fd) =
        ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          ((chartGeometricPointAt_liesOver B S hS hX V _).trans
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2))
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
            (Z.genericTotalFractionRing B S hS hX hdec) f g).val) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit * Ring.minimalPrimeOrd p FN hFN -
        Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (g : Z.genericTotalFractionRing B S hS hX hdec) g.isUnit * Ring.minimalPrimeOrd p FL hFL -
        Ring.minimalPrimeOrd p Fd hFd =
      -heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V _
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
        (tameSymbolOfKrullDimOne
          (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V _
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1))
          (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V _
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1).1.asIdeal))
          (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)).toMonoidHom a)
          (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V _
            (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)).toMonoidHom b)) := by
  have hq : chartSchemeToPoints B S hS X V (Stacks.Chow.intermediatePointOfHeightOnePrime
      (Z.baseChangeChartProj B S hS hX V y)
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1) =
      Z.genericPoint B S hS X :=
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2
  have hexL := Z.exists_isChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij _ hq
  have hexN := Z.exists_isChartRatioUnit B S hS hX hdec hInt hN V hV N hN' e' hecompat' hebij' _ hq
  have hμL := hexL.choose_spec
  have hμN := hexN.choose_spec
  have e1 := Z.minimalPrimeOrd_eq_heightOneOrd_branchReading B S hS hX V hdec y hdim p FL hFL
  have e2 := Z.minimalPrimeOrd_eq_heightOneOrd_branchReading B S hS hX V hdec y hdim p FN hFN
  have e3 := Z.minimalPrimeOrd_eq_heightOneOrd_branchReading B S hS hX V hdec y hdim p Fd hFd
  have key := heightOnePrime_keyFormula_identity B S hS hX hdec hInt hN Z V hV _
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 hq L hL e hecompat hebij hdim
    N hN' e' hecompat' hebij' s t a b ha hb hexL.choose hexN.choose (hμL s) (hμN t)
    f g v₁ v₂ hfv hgv
    (hFL.map (Z.branchReading B S hS hX V hdec y p)).unit
    (hFN.map (Z.branchReading B S hS hX V hdec y p)).unit
    (hFd.map (Z.branchReading B S hS hX V hdec y p)).unit
  refine Eq.trans ?_ (key (Units.ext ((hRL _ hμL).trans (by simp)))
    (Units.ext ((hRN _ hμN).trans (by simp))) (Units.ext hRd))
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg (_ * ·) e2) (congrArg (_ * ·) e1)) e3

end Identity

/-! ### The reading of a restricted generator along a branch (G2) -/

section UnitReading

variable (hNZ : HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hV' : IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)))

/-- **The statement (G2)**: at every point `q'` of `V ×_X Z` over the generic point of `Z`, the
value at `q'` of the coefficient of `(v s_ξ)|_Z` against the restricted generator, moved to
`κ(q) = κ(q')` and read in `κ(𝒪_{X, x̄})`, is `v̄ μ̄⁻¹` for every unit `μ` of the ratio comparison
(H3) at `q`. -/
def PrimeDivisor.UnitRestrictionReading (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ) :
    Prop :=
  ∀ (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hq' : chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V q') =
      Z.genericPoint B S hS X) (μ),
    Z.IsChartRatioUnit B S hS hX hdec hInt hN V hV L hL e hecompat hebij _ hq' μ →
      chartResidueFieldToEtale B S hS hX V (Z.baseChangeChartProj B S hS hX V q')
          ((Z.baseChangeChartResidueFieldEquiv B S hS hX V q').symm
            (Z.baseChangeChartSectionReading B S hS hX L hL V e hecompat hebij hV'
              (isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.space B S hS)
                (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
                  B S hS Z.closed.1 Z.integral)
                (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS
                  Z.subspace.toFunctor Z.closed.1 hNZ) _ hV') q'
              (Z.isField_stalk_baseChangeChart B S hS hX V q' hq')
              (Z.henselianUnitRestriction B S hS hX hdec hN L hL v))) =
        Z.henselianResidueFieldToEtale B S hS hX hdec
            (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq')
            (@IsLocalRing.residue _ _ (henselianLocalRing_isLocalRing B S hS X hX
              (Z.genericPoint B S hS X) hdec) (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec))) *
          (@IsLocalRing.residue _ _ (isLocalRing_etaleLocalRing B S hS X hX
            (chartGeometricPointAt B S hS hX V (Z.baseChangeChartProj B S hS hX V q'))) μ.val)⁻¹

end UnitReading

end AlgebraicGeometry.Space

end
