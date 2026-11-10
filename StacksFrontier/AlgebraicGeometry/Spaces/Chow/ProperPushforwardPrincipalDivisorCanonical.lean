module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorFibreData
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor

/-!
# Stacks 0EQ4: the proper pushforward of a principal divisor

In Situation 0EDT let `X/B` and `Y/B` be good and integral with `dim_δ(X) = dim_δ(Y) = n`, let
`p : X ⟶ Y` be dominant and proper, `f ∈ R(X)^*` and `g = Nm_{R(X)/R(Y)}(f)`. Then

`p_* div(f) = div(g)` in `Z_{n-1}(Y)`.

## Main results

* `AlgebraicGeometry.Space.evalRingHom_rationalFunctionNorm`: the norm `Nm_{R(X)/R(Y)}` read at
  the generic points is `Algebra.norm` of the extension of residue fields.
* `AlgebraicGeometry.Space.finsum_rationalFunctionPrincipalDivisorCycle_mul_properCycleMult_eq`:
  the identity at one prime divisor `W` of `Y`, `∑_Z ord_Z(f) deg(Z/W) = ord_W(g)`.
* `AlgebraicGeometry.Space.properCyclePushforward_rationalFunctionPrincipalDivisorCycle`:
  **Stacks 0EQ4**.

## Implementation notes

The proof is the source's. At a prime divisor `W` of `Y` with generic point `η`, the fibre of
`p` over `η` is finite, so `p` is finite over an affine elementary étale neighbourhood `V` of
`η`, with `U = X ×_Y V` affine (`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`).
With `A = Γ(V)`, `C = Γ(U)` and `𝔭 ⊂ A` the prime of the point `e` of `V` over `η`, the points of
`X` over `η` are the primes of `C` over `𝔭`, with residue degrees `[κ(𝔮) : κ(𝔭)]`, and the orders
of vanishing are read on `A_𝔭` and the `C_𝔮` (Stacks 0ENM). The identity is then the algebraic
`Stacks.NormBranches.ordTotalFracInt_atPrime_eq_finsum` (Stacks 02MJ along the branches of
`A_𝔭`), whose norm hypothesis is the generic fibre of the chart
(`AlgebraicGeometry.Space.exists_fibreData`): over every minimal prime of `A_𝔭` the generic
fibre of `C_𝔭` is the base change of `R(X)/R(Y)`.

## References

* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The norm read at the generic points -/

section Norm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (p : X ⟶ Y)
    (hgen : pointsMap B S hS X p (genericPoint B S hS hX hintX) = genericPoint B S hS hY hintY)

/-- **The norm `Nm_{R(X)/R(Y)}` read at the generic points.** Evaluated at the residue field of
`Y` at the image of the generic point of `X`, the norm of a rational function `f` of `X` is the
norm, along the extension of residue fields, of the value of `f` at the generic point. -/
theorem evalRingHom_rationalFunctionNorm (f : rationalFunctions B S hS hX) :
    letI := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
      (genericPoint B S hS hX hintX)).toAlgebra
    evalRingHom B S hS hY hintY
        (residueFieldRepresentative B S hS Y hintY.2.1
          (pointsMap B S hS X p (genericPoint B S hS hX hintX))).1
        ((residueFieldRepresentative B S hS Y hintY.2.1 _).2.1.trans hgen)
        (rationalFunctionNorm B S hS hX hY hintX hintY p hgen f) =
      Algebra.norm (residueField B S hS Y hintY.2.1
          (pointsMap B S hS X p (genericPoint B S hS hX hintX)))
        (evalRingHom B S hS hX hintX
          (residueFieldRepresentative B S hS X hintX.2.1 (genericPoint B S hS hX hintX)).1
          (residueFieldRepresentative B S hS X hintX.2.1 _).2.1 f) := by
  let := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
    (genericPoint B S hS hX hintX)).toAlgebra
  apply (residueFieldCongr B S hS hintY.2.1 hgen).injective
  refine (residueFieldCongr_evalRingHom B S hS hY hintY hgen _
    (genericRep_class B S hS hY hintY) _).trans ?_
  change rationalFunctionsRingEquiv B S hS hY hintY
      (rationalFunctionNorm B S hS hX hY hintX hintY p hgen f) = _
  unfold rationalFunctionNorm
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The norm `Nm_{R(X)/R(Y)}` of an invertible rational function, as a unit of `R(Y)`. -/
def rationalFunctionNormUnit (f : (rationalFunctions B S hS hX)ˣ) :
    (rationalFunctions B S hS hY)ˣ where
  val := rationalFunctionNorm B S hS hX hY hintX hintY p hgen f
  inv := rationalFunctionNorm B S hS hX hY hintX hintY p hgen ↑f⁻¹
  val_inv := by
    let := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
      (genericPoint B S hS hX hintX)).toAlgebra
    unfold rationalFunctionNorm
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one,
      map_one]
  inv_val := by
    let := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
      (genericPoint B S hS hX hintX)).toAlgebra
    unfold rationalFunctionNorm
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one,
      map_one]

/-- The underlying function of `rationalFunctionNormUnit f` is `rationalFunctionNorm f`. -/
@[simp]
theorem coe_rationalFunctionNormUnit (f : (rationalFunctions B S hS hX)ˣ) :
    (rationalFunctionNormUnit B S hS hX hY hintX hintY p hgen f : rationalFunctions B S hS hY) =
      rationalFunctionNorm B S hS hX hY hintX hintY p hgen f :=
  rfl

end Norm

/-! ### Orders of vanishing at a point of an affine chart, read at the prime of the point -/

section ChartOrder

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1] (v : V.obj.left.left.1)
    [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)]
    [IsNoetherianRing (chartRing B S hS F hF V)]

/-- **The order of vanishing of a rational function at a point of an affine chart, read in the
localization of the ring of the chart at the prime of the point.** -/
theorem ordTotalFracInt_chartPointRationalFunctionMap_eq_localization
    (g : (rationalFunctions B S hS hF)ˣ) :
    haveI := @krullDimLE_localization_chartPrimeAt B S hS F hF V ‹IsAffine V.obj.left.left.1› v 1
      ‹Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)›
    Ring.ordTotalFracInt (V.obj.left.left.1.presheaf.stalk v)
        (chartPointRationalFunctionMap B S hS hF V v (g : rationalFunctions B S hS hF))
        (g.isUnit.map _) =
      Ring.ordTotalFracInt (Localization.AtPrime (chartPrimeAt B S hS hF V v))
        (Stacks.NormBranches.fracMapOfLocalization (chartPrimeAt B S hS hF V v).primeCompl
          (Localization.AtPrime (chartPrimeAt B S hS hF V v))
          (rationalFunctionsToTotalFractionRing B S hS hF V.obj.left V.obj.hom
            ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property)
            (g : rationalFunctions B S hS hF)))
        ((g.isUnit.map _).map _) := by
  have := @krullDimLE_localization_chartPrimeAt B S hS F hF V ‹IsAffine V.obj.left.left.1› v 1
      ‹Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)›
  let : Algebra (chartRing B S hS F hF V) (V.obj.left.left.1.presheaf.stalk v) :=
    (chartGermHom B S hS hF V v).toAlgebra
  have : IsLocalization (chartPrimeAt B S hS hF V v).primeCompl
      (V.obj.left.left.1.presheaf.stalk v) :=
    isLocalization_stalk_chartPrimeAt B S hS hF V ‹IsAffine V.obj.left.left.1› v
  have key := Stacks.NormBranches.ordTotalFracInt_eq_of_isLocalization_atPrime
    (R := chartRing B S hS F hF V) (R₁ := V.obj.left.left.1.presheaf.stalk v)
    (R₂ := Localization.AtPrime (chartPrimeAt B S hS hF V v)) (chartPrimeAt B S hS hF V v)
    (rationalFunctionsToTotalFractionRing B S hS hF V.obj.left V.obj.hom
      ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property) ↑g)
    ((g.isUnit.map _).map _) ((g.isUnit.map _).map _)
  exact key

omit [IsReduced V.obj.left.left.1] [IsLocallyNoetherian V.obj.left.left.1]
  [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)]
  [IsNoetherianRing (chartRing B S hS F hF V)] in
/-- At a point of an affine chart over the generic point of a prime divisor, the localization of
the ring of the chart at the prime of the point has dimension one. -/
theorem ringKrullDim_localization_chartPrimeAt_eq_one (hdec : IsDecentSpace B S hS F)
    (W : PrimeDivisor B S hS F)
    (hv : chartSchemeToPoints B S hS F V v = W.genericPoint B S hS F) :
    ringKrullDim (Localization.AtPrime (chartPrimeAt B S hS hF V v)) = 1 := by
  let : Algebra (chartRing B S hS F hF V) (V.obj.left.left.1.presheaf.stalk v) :=
    (chartGermHom B S hS hF V v).toAlgebra
  have : IsLocalization (chartPrimeAt B S hS hF V v).primeCompl
      (V.obj.left.left.1.presheaf.stalk v) :=
    isLocalization_stalk_chartPrimeAt B S hS hF V ‹IsAffine V.obj.left.left.1› v
  rw [ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv
    (chartPrimeAt B S hS hF V v).primeCompl (Localization.AtPrime (chartPrimeAt B S hS hF V v))
    (V.obj.left.left.1.presheaf.stalk v)).toRingEquiv]
  exact W.ringKrullDim_chartStalk B S hS hF hdec V v hv

/-- **The order of vanishing of a rational function at a point of an affine chart is
`Stacks.NormBranches.ordAtPrime` at the prime of the point.** -/
theorem ordTotalFracInt_chartPointRationalFunctionMap_eq_ordAtPrime
    (g : (rationalFunctions B S hS hF)ˣ) :
    Ring.ordTotalFracInt (V.obj.left.left.1.presheaf.stalk v)
        (chartPointRationalFunctionMap B S hS hF V v (g : rationalFunctions B S hS hF))
        (g.isUnit.map _) =
      Stacks.NormBranches.ordAtPrime ⟨chartPrimeAt B S hS hF V v, inferInstance⟩
        (rationalFunctionsToTotalFractionRing B S hS hF V.obj.left V.obj.hom
          ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property)
          (g : rationalFunctions B S hS hF)) := by
  have := @krullDimLE_localization_chartPrimeAt B S hS F hF V ‹IsAffine V.obj.left.left.1› v 1
      ‹Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)›
  unfold Stacks.NormBranches.ordAtPrime
  rw [dite_eq_left ⟨inferInstance, (g.isUnit.map _).map _⟩]
  exact ordTotalFracInt_chartPointRationalFunctionMap_eq_localization B S hS hF V v g

end ChartOrder

/-! ### The coefficients of `div(f)` and `div(g)` read on the charts -/

section Coefficients

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **The coefficient of `div(g)` at a prime divisor, read on an affine chart.** At a point `e`
of an affine étale chart `V` of `Y` over the generic point of a prime divisor `W`, the coefficient
`ord_W(g)` of `div(g)` is the order of vanishing of the reading of `g` in the localization of
`Γ(V)` at the prime of `e` (Stacks 0ENM). -/
theorem rationalFunctionPrincipalDivisorCycle_primeDivisor_eq_localization {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (W : PrimeDivisor D.site D.base D.base_mem Y) (V : SmallEtale D.site D.base D.base_mem Y)
    [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1]
    [IsNoetherianRing (chartRing D.site D.base D.base_mem Y hY.1 V)] (e : V.obj.left.left.1)
    (he : chartSchemeToPoints D.site D.base D.base_mem Y V e =
      W.genericPoint D.site D.base D.base_mem Y)
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    haveI := W.krullDimLE_chartStalk D.site D.base D.base_mem hY.1 hintY.isDecentSpace V e he
    haveI := @krullDimLE_localization_chartPrimeAt D.site D.base D.base_mem Y hY.1 V
      ‹IsAffine V.obj.left.left.1› e 1
      (W.krullDimLE_chartStalk D.site D.base D.base_mem hY.1 hintY.isDecentSpace V e he)
    (rationalFunctionPrincipalDivisorCycle D sY hY hintY hnY g).1
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      Ring.ordTotalFracInt (Localization.AtPrime (chartPrimeAt D.site D.base D.base_mem hY.1 V e))
        (Stacks.NormBranches.fracMapOfLocalization
          (chartPrimeAt D.site D.base D.base_mem hY.1 V e).primeCompl
          (Localization.AtPrime (chartPrimeAt D.site D.base D.base_mem hY.1 V e))
          (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 V.obj.left V.obj.hom
            ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem V.obj.hom).2 V.property)
            (g : rationalFunctions D.site D.base D.base_mem hY.1)))
        ((g.isUnit.map _).map _) := by
  have := W.krullDimLE_chartStalk D.site D.base D.base_mem hY.1 hintY.isDecentSpace V e he
  rw [rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace,
    W.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap D.site D.base D.base_mem hY.1
      hintY.isDecentSpace hintY (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) V e
      he g]
  exact ordTotalFracInt_chartPointRationalFunctionMap_eq_localization D.site D.base D.base_mem
    hY.1 V e g

include hintY in
/-- **The coefficient of `div(f)` at a point over the generic point of a prime divisor of `Y`,
read on an affine chart.** For `p` proper carrying the generic point to the generic point with
`dim_δ(X) = dim_δ(Y) = n`, a point `x` of `X` over the generic point of a prime divisor of `Y` is
the generic point of a prime divisor of `X`; at a point `v` of an affine étale chart of `X`
over `x` the coefficient of `div(f)` there is `Stacks.NormBranches.ordAtPrime` at the prime of
`v` (Stacks 0ENM). -/
theorem rationalFunctionPrincipalDivisorCycle_integralClosedSubspaceOfPoint_eq_ordAtPrime
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (W : PrimeDivisor D.site D.base D.base_mem Y) (V : SmallEtale D.site D.base D.base_mem X)
    [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1]
    [IsNoetherianRing (chartRing D.site D.base D.base_mem X hX.1 V)]
    [_root_.IsReduced (chartRing D.site D.base D.base_mem X hX.1 V)] (v : V.obj.left.left.1)
    (hv : pointsMap D.site D.base D.base_mem X p
        (chartSchemeToPoints D.site D.base D.base_mem X V v) =
      W.genericPoint D.site D.base D.base_mem Y)
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    (rationalFunctionPrincipalDivisorCycle D sX hX hintX hnX f).1
        (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) (chartSchemeToPoints D.site D.base D.base_mem X V v)) =
      Stacks.NormBranches.ordAtPrime ⟨chartPrimeAt D.site D.base D.base_mem hX.1 V v, inferInstance⟩
        (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hX.1 V.obj.left V.obj.hom
          ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem V.obj.hom).2 V.property)
          (f : rationalFunctions D.site D.base D.base_mem hX.1)) := by
  have hδ := deltaDimension_integralClosedSubspaceOfPoint_of_pointsMap_eq_genericPoint D sX hX sY
    hY hintX hintY hpB hproper hgen hnX hnY W _ hv
  have hcod := ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hintX
    (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX) hnX
    (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX)
      (chartSchemeToPoints D.site D.base D.base_mem X V v))).out 3 2).mp hδ
  set P := (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX)
      (chartSchemeToPoints D.site D.base D.base_mem X V v)).toPrimeDivisor
      D.site D.base D.base_mem hX.1 hcod with hP
  have : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX)
  have hPgen : chartSchemeToPoints D.site D.base D.base_mem X V v =
      P.genericPoint D.site D.base D.base_mem X :=
    ((P.isGenericPoint_genericPoint D.site D.base D.base_mem).eq
      (isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) _)).symm
  have := P.krullDimLE_chartStalk D.site D.base D.base_mem hX.1 hintX.isDecentSpace V v hPgen
  rw [← IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
      hX.1 _ hcod, ← hP, rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace,
    P.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap D.site D.base D.base_mem hX.1
      hintX.isDecentSpace hintX (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V v
      hPgen f]
  exact ordTotalFracInt_chartPointRationalFunctionMap_eq_ordAtPrime D.site D.base D.base_mem
    hX.1 V v f

end Coefficients

/-! ### The points of a finite chart over a point, as primes -/

section ChartPrimes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The points of a chart over a point of the base chart are the primes over its prime.** For
a diagram of affine étale charts over `φ`, the points `w` of `U` over a point `e` of `V`
correspond, through their primes, to the primes of `Γ(U)` contracting to the prime of `e`. -/
theorem finsum_mem_chartScheme_fibre_eq_finsum_mem_primeSpectrum {Z Y : AlgebraicSpaces B S hS}
    (φ : Z ⟶ Y) (d : ChartDiagram B S hS Z.1 Y.1 φ.hom) (hU : IsAffine (chartScheme d.U))
    (hV : IsAffine (chartScheme d.V)) (e : chartScheme d.V)
    (G : PrimeSpectrum (chartRing B S hS Z.1 Z.2 d.U) → ℤ) :
    ∑ᶠ w ∈ {w : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base w = e},
        G ⟨chartPrimeAt B S hS Z.2 d.U w, inferInstance⟩ =
      ∑ᶠ 𝔮 ∈ {𝔮 : PrimeSpectrum (chartRing B S hS Z.1 Z.2 d.U) |
          𝔮.asIdeal.comap (chartDiagramRestrict B S hS φ d) = chartPrimeAt B S hS Y.2 d.V e},
        G 𝔮 := by
  have hbij := bijective_chartPrimeAt B S hS Z.2 d.U hU
  have hbijV := bijective_chartPrimeAt B S hS Y.2 d.V hV
  refine finsum_mem_eq_of_bijOn (fun w => ⟨chartPrimeAt B S hS Z.2 d.U w, inferInstance⟩)
    ⟨fun w hw => ?_, hbij.1.injOn, fun Q hQ => ?_⟩ (fun w _ => rfl)
  · change (chartPrimeAt B S hS Z.2 d.U w).comap (chartDiagramRestrict B S hS φ d) = _
    rw [comap_chartPrimeAt B S hS φ d w, show ((BigFppfOver.toScheme B S hS).map d.g).base w = e
      from hw]
  · obtain ⟨w, rfl⟩ := hbij.2 Q
    refine ⟨w, ?_, rfl⟩
    have hQ' : chartPrimeAt B S hS Y.2 d.V (((BigFppfOver.toScheme B S hS).map d.g).base w) =
        chartPrimeAt B S hS Y.2 d.V e := by
      rw [← comap_chartPrimeAt B S hS φ d w]
      exact hQ
    exact hbijV.1 (PrimeSpectrum.ext hQ')

end ChartPrimes

/-! ### The identity on one chart -/

section ChartIdentity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    {p : X ⟶ Y} (d : ChartDiagram D.site D.base D.base_mem X Y p)

attribute [local instance] chartRingAlgebra

variable [IsAffine d.U.obj.left.left.1] [IsAffine d.V.obj.left.left.1]
  [IsReduced d.U.obj.left.left.1] [IsReduced d.V.obj.left.left.1]
  [IsLocallyNoetherian d.U.obj.left.left.1] [IsLocallyNoetherian d.V.obj.left.left.1]

/-- **Stacks 0EQ4 on one chart, in the rings of the chart.** Let `d` be a cartesian square of
affine étale charts of `p` with `Γ(U)` finite over `Γ(V)`, both reduced and Noetherian, the
minimal primes of `Γ(U)` lying over minimal primes of `Γ(V)`, and `𝔭` a prime of `Γ(V)` with
`Γ(V)_𝔭` of dimension one. Then for `f ∈ R(X)^*`

`ord_{Γ(V)_𝔭}(Nm_{R(X)/R(Y)}(f)) = ∑_{𝔮 ∩ Γ(V) = 𝔭} [κ(𝔮) : κ(𝔭)] · ord_{Γ(U)_𝔮}(f)`.

This is `Stacks.NormBranches.ordTotalFracInt_atPrime_eq_finsum`, its generic fibres being the
base change of `R(X)/R(Y)` by `AlgebraicGeometry.Space.exists_fibreData`; the extension
`R(X)/R(Y)` is finite by Stacks 0AD5, its transcendence degree being zero as
`dim_δ(X) = dim_δ(Y)`. -/
theorem ordTotalFracInt_rationalFunctionNorm_eq_finsum_ordAtPrime (hpB : p ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem p) (hdom : IsDominant D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) p d.V.1.hom)
    [Module.Finite Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)]
    [IsNoetherianRing Γ(chartScheme d.V, ⊤)] [IsNoetherianRing Γ(chartScheme d.U, ⊤)]
    [_root_.IsReduced Γ(chartScheme d.V, ⊤)] [_root_.IsReduced Γ(chartScheme d.U, ⊤)]
    (htf : ∀ P ∈ minimalPrimes Γ(chartScheme d.U, ⊤),
      P.comap (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)) ∈
        minimalPrimes Γ(chartScheme d.V, ⊤))
    (𝔭 : Ideal Γ(chartScheme d.V, ⊤)) [𝔭.IsPrime]
    (h𝔭 : ringKrullDim (Localization.AtPrime 𝔭) = 1)
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    haveI : Ring.KrullDimLE 1 (Localization.AtPrime 𝔭) := Ring.krullDimLE_iff.mpr h𝔭.le
    Ring.ordTotalFracInt (Localization.AtPrime 𝔭)
        (Stacks.NormBranches.fracMapOfLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭)
          (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 d.V.obj.left
            d.V.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
              d.V.obj.hom).2 d.V.property)
            (rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p hgen f :
              rationalFunctions D.site D.base D.base_mem hY.1)))
        (((rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p hgen
          f).isUnit.map _).map _) =
      ∑ᶠ 𝔮 ∈ {𝔮 : PrimeSpectrum Γ(chartScheme d.U, ⊤) |
          𝔮.asIdeal.comap (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)) = 𝔭},
        (Stacks.Length.primeResidueDegree
            (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)) 𝔭 𝔮.asIdeal : ℤ) *
          Stacks.NormBranches.ordAtPrime 𝔮
            (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hX.1 d.U.obj.left
              d.U.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
                d.U.obj.hom).2 d.U.property)
              (f : rationalFunctions D.site D.base D.base_mem hX.1)) := by
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔭) := Ring.krullDimLE_iff.mpr h𝔭.le
  have hfd := fun Q => exists_fibreData D sX hX sY hY hintX hintY d hpB hproper hgen hdim hd htf
    𝔭 Q
  choose κ lam hpush hσ hτ using hfd
  let := (residueFieldHom D.site D.base D.base_mem X Y hY.1 hintX.2.1 hintY.2.1 p
    (genericPoint D.site D.base D.base_mem hX.1 hintX)).toAlgebra
  have := finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero D.site D.base
    D.base_mem hX.1 hY.1 hintX hintY p hproper.2.1.1 hdom
    (hasTranscendenceDegreeAt_genericPoint_eq_zero D sX sY hX hY hintX hintY p hpB hgen hdim)
  refine Stacks.NormBranches.ordTotalFracInt_atPrime_eq_finsum 𝔭 h𝔭 htf _ _ κ lam hpush _
    ((rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p hgen
      f).isUnit.map _) _ (f.isUnit.map _) _ (fun Q => ?_) (fun Q => hτ Q f)
  refine (hσ Q _).trans ?_
  congr 1
  exact evalRingHom_rationalFunctionNorm D.site D.base D.base_mem hX.1 hY.1 hintX hintY p hgen f

include hintY in
/-- **The identity of Stacks 0EQ4 at a prime divisor, on one finite chart.** Let `d` be a
cartesian square of affine étale charts of `p` with finite `U → V`, and `e` the only point of `V`
over the generic point of a prime divisor `W` of `Y`, with `Spec κ(e) ⟶ Y` a monomorphism. Then
the sum over the points `w` of `U` over `e` of `ord(f)` at the integral closed subspace with
generic point the image of `w`, weighted by the degree of the residue field extension there, is
the coefficient of `div(Nm_{R(X)/R(Y)}(f))` at `W`. -/
theorem finsum_chartFibre_mul_cycleResidueDegree_eq (hpB : p ≫ sY = sX)
    (hproper : IsProper D.site D.base D.base_mem p) (hdom : IsDominant D.site D.base D.base_mem p)
    (hgen : pointsMap D.site D.base D.base_mem X p
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) p d.V.1.hom)
    (hfinite : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g))
    (W : PrimeDivisor D.site D.base D.base_mem Y) (e : chartScheme d.V)
    (he : chartSchemeToPoints D.site D.base D.base_mem Y d.V e =
      W.genericPoint D.site D.base D.base_mem Y)
    (huniq : ∀ e' : chartScheme d.V, chartSchemeToPoints D.site D.base D.base_mem Y d.V e' =
      W.genericPoint D.site D.base D.base_mem Y → e' = e)
    (hmono : Mono (fieldMorphism D.site D.base D.base_mem Y
      (chartSchemeFieldValuedPoint D.site D.base D.base_mem Y d.V e)))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    ∑ᶠ w ∈ {w : chartScheme d.U |
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base w = e},
        (rationalFunctionPrincipalDivisorCycle D sX hX hintX hnX f).1
            (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX)
              (chartSchemeToPoints D.site D.base D.base_mem X d.U w)) *
          (cycleResidueDegree D sX hX sY hY p
              (chartSchemeToPoints D.site D.base D.base_mem X d.U w) : ℤ) =
      (rationalFunctionPrincipalDivisorCycle D sY hY hintY hnY
          (rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p hgen f)).1
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hdim := hnX.trans hnY.symm
  have hUa : IsAffine (chartScheme d.U) := ‹IsAffine d.U.obj.left.left.1›
  have hVa : IsAffine (chartScheme d.V) := ‹IsAffine d.V.obj.left.left.1›
  have : IsLocallyNoetherian (chartScheme d.U) := ‹IsLocallyNoetherian d.U.obj.left.left.1›
  have : IsLocallyNoetherian (chartScheme d.V) := ‹IsLocallyNoetherian d.V.obj.left.left.1›
  have := hfinite
  have : Module.Finite Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤) :=
    (Scheme.Hom.finite_appTop ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g) :
      (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤)).Finite)
  have hVN : IsNoetherianRing Γ(chartScheme d.V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hUN : IsNoetherianRing Γ(chartScheme d.U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hVR : _root_.IsReduced Γ(chartScheme d.V, ⊤) :=
    isReduced_chartRing_of_isIntegralSpace D.site D.base D.base_mem ⟨Y, hY.1⟩ hintY d.V
  have hUR : _root_.IsReduced Γ(chartScheme d.U, ⊤) :=
    isReduced_chartRing_of_isIntegralSpace D.site D.base D.base_mem ⟨X, hX.1⟩ hintX d.U
  have : IsNoetherianRing (chartRing D.site D.base D.base_mem Y hY.1 d.V) := hVN
  have : IsNoetherianRing (chartRing D.site D.base D.base_mem X hX.1 d.U) := hUN
  have : _root_.IsReduced (chartRing D.site D.base D.base_mem X hX.1 d.U) := hUR
  have htf := comap_mem_minimalPrimes_chartDiagramRestrict D.site D.base D.base_mem
    (Z := ⟨X, hX.1⟩) (Y := ⟨Y, hY.1⟩) hintX hintY (goodSpacesHom D sX hX sY hY p) hgen d hUa hVa
  have h𝔭 := ringKrullDim_localization_chartPrimeAt_eq_one D.site D.base D.base_mem hY.1 d.V e
    hintY.isDecentSpace W he
  have hbijOn := bijOn_chartSchemeToPoints_fibre D.site D.base D.base_mem
    (goodSpacesHom D sX hX sY hY p) d hd _ e he huniq hmono
  have : (show Ideal Γ(chartScheme d.V, ⊤) from
      chartPrimeAt D.site D.base D.base_mem hY.1 d.V e).IsPrime :=
    chartPrimeAt_isPrime D.site D.base D.base_mem hY.1 d.V e
  refine Eq.trans ?_ (rationalFunctionPrincipalDivisorCycle_primeDivisor_eq_localization D sY hY
    hintY hnY W d.V e he _).symm
  refine Eq.trans ?_ (ordTotalFracInt_rationalFunctionNorm_eq_finsum_ordAtPrime D sX hX sY hY
    hintX hintY d hpB hproper hdom hgen hdim hd htf
    (show Ideal Γ(chartScheme d.V, ⊤) from chartPrimeAt D.site D.base D.base_mem hY.1 d.V e) h𝔭
    f).symm
  refine Eq.trans ?_ (finsum_mem_chartScheme_fibre_eq_finsum_mem_primeSpectrum D.site D.base
    D.base_mem (goodSpacesHom D sX hX sY hY p) d hUa hVa e
    (fun 𝔮 : PrimeSpectrum Γ(chartScheme d.U, ⊤) =>
      (Stacks.Length.primeResidueDegree
          (algebraMap Γ(chartScheme d.V, ⊤) Γ(chartScheme d.U, ⊤))
          (chartPrimeAt D.site D.base D.base_mem hY.1 d.V e) 𝔮.asIdeal : ℤ) *
        Stacks.NormBranches.ordAtPrime 𝔮
          (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hX.1 d.U.obj.left
            d.U.obj.hom ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem
              d.U.obj.hom).2 d.U.property)
            (f : rationalFunctions D.site D.base D.base_mem hX.1))))
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [rationalFunctionPrincipalDivisorCycle_integralClosedSubspaceOfPoint_eq_ordAtPrime D sX hX sY
    hY hintX hintY hpB hproper hgen hnX hnY W d.U w (hbijOn.mapsTo hw) f, mul_comm]
  congr 2
  exact (primeResidueDegree_chartPrime_eq_finrank D.site D.base D.base_mem hXdec hYdec
    (goodSpacesHom D sX hX sY hY p) d hd _ e he huniq hmono w hw).symm

end ChartIdentity

/-! ### Stacks 0EQ4 -/

section Assembly

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- An étale-local property of schemes holding on an atlas of an algebraic space holds on every
étale chart. -/
private theorem property_of_hasEtaleLocalProperty (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (hF : IsAlgebraicSpace B S hS F)
    (hP : HasEtaleLocalProperty B S hS F P) (V : SmallEtale B S hS F) : P V.obj.left.left.1 :=
  (exists_atlas_iff_forall_etale B S hS F P hF).mp hP V.obj.left V.obj.hom V.property

/-- **Stacks 0EQ4 at one prime divisor of `Y`.** In Situation 0EDT let `X/B`, `Y/B` be good and
integral with `dim_δ(X) = dim_δ(Y) = n`, let `p : X ⟶ Y` be dominant and proper, and
`f ∈ R(X)^*`. For every prime divisor `W` of `Y`

`∑_Z ord_Z(f) · deg(Z/W) = ord_W(Nm_{R(X)/R(Y)}(f))`,

the sum over the integral closed subspaces `Z ⊆ X`, that is: the coefficient of `p_* div(f)` at
`W` is the coefficient of `div(g)` at `W` for `g = Nm_{R(X)/R(Y)}(f)`.

Only the points of `X` over the generic point `η` of `W` contribute; they are finitely many, so
`p` is finite over an affine elementary étale neighbourhood of `η`
(`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`), where the identity is
`AlgebraicGeometry.Space.finsum_chartFibre_mul_cycleResidueDegree_eq`. -/
theorem finsum_rationalFunctionPrincipalDivisorCycle_mul_properCycleMult_eq {p : X ⟶ Y}
    (hpB : p ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem p)
    (hdom : IsDominant D.site D.base D.base_mem p) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ)
    (W : PrimeDivisor D.site D.base D.base_mem Y) :
    ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (rationalFunctionPrincipalDivisorCycle D sX hX hintX hnX f).1 Z *
          properCycleMult D sX hX sY hY p Z (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (rationalFunctionPrincipalDivisorCycle D sY hY hintY hnY
          (rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p
            (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY
              p hdom) f)).1
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hgen := pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX
    hintY p hdom
  have hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ := hnX.trans hnY.symm
  have : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hYdec
  set c := rationalFunctionPrincipalDivisorCycle D sX hX hintX hnX f with hc
  have hα : ∀ Z, c.1 Z ≠ 0 → deltaDimension D sX Z = n - 1 := fun Z hZ => c.2.2 Z hZ
  set W' := W.toIntegralClosedSubspace D.site D.base D.base_mem with hW'def
  have hW'cod := W.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
  have hW' : deltaDimension D sY W' = n - 1 :=
    ((isPrimeDivisor_tfae_of_isIntegralSpace D sY hY hintY (deltaDimensionFunction D sY hY)
      (deltaDimensionFunction_apply D sY hY) hnY W').out 2 3).mp hW'cod
  have hamb : W'.ambientGenericPoint D.site D.base D.base_mem =
      W.genericPoint D.site D.base D.base_mem Y :=
    (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).eq
      (W.isGenericPoint_genericPoint D.site D.base D.base_mem)
  rw [finsum_mul_properCycleMult_eq_finsum_fibre D sX hX sY hY p (n - 1) c.1 hα W' hW', hamb]
  -- the condition `c ≠ 0` on the fibre can be dropped
  set G : points D.site D.base D.base_mem X → ℤ := fun x =>
    c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x) *
      (cycleResidueDegree D sX hX sY hY p x : ℤ) with hG
  have hdrop : (∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X p x =
          W.genericPoint D.site D.base D.base_mem Y ∧
        c.1 (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x) ≠ 0}, G x) =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X p x =
        W.genericPoint D.site D.base D.base_mem Y}, G x := by
    rw [← finsum_mem_inter_support G, ← finsum_mem_inter_support G {x |
      pointsMap D.site D.base D.base_mem X p x = W.genericPoint D.site D.base D.base_mem Y}]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, left_ne_zero_of_mul h.2⟩, h.2⟩⟩
  rw [hdrop]
  -- the chart at the generic point of `W`
  have hfib := finite_fibre_primeDivisor_genericPoint D sX hX sY hY hintX hintY hpB hproper hgen
    hdim W
  obtain ⟨d, e, hd, hV, hU, hfinite, he, huniq, hmono⟩ :=
    exists_finite_affine_chartDiagram D.site D.base D.base_mem hXdec hYdec
      (goodSpacesHom D sX hX sY hY p) hproper (W.genericPoint D.site D.base D.base_mem Y) hfib
  have : IsAffine d.U.obj.left.left.1 := hU
  have : IsAffine d.V.obj.left.left.1 := hV
  have : IsReduced d.U.obj.left.left.1 := property_of_hasEtaleLocalProperty D.site D.base
    D.base_mem (fun T : Scheme.{u} => IsReduced T) hX.1
    (IsIntegralSpace.hasEtaleLocalProperty_isReduced D.site D.base D.base_mem X hintX) d.U
  have : IsReduced d.V.obj.left.left.1 := property_of_hasEtaleLocalProperty D.site D.base
    D.base_mem (fun T : Scheme.{u} => IsReduced T) hY.1
    (IsIntegralSpace.hasEtaleLocalProperty_isReduced D.site D.base D.base_mem Y hintY) d.V
  have : IsLocallyNoetherian d.U.obj.left.left.1 := property_of_hasEtaleLocalProperty D.site
    D.base D.base_mem (fun T : Scheme.{u} => IsLocallyNoetherian T) hX.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) d.U
  have : IsLocallyNoetherian d.V.obj.left.left.1 := property_of_hasEtaleLocalProperty D.site
    D.base D.base_mem (fun T : Scheme.{u} => IsLocallyNoetherian T) hY.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) d.V
  have hbijOn := bijOn_chartSchemeToPoints_fibre D.site D.base D.base_mem
    (goodSpacesHom D sX hX sY hY p) d hd _ e he huniq hmono
  rw [← finsum_mem_eq_of_bijOn (chartSchemeToPoints D.site D.base D.base_mem X d.U) hbijOn
    (fun w _ => rfl)]
  exact finsum_chartFibre_mul_cycleResidueDegree_eq D sX hX sY hY hintX hintY d hpB hproper hdom
    hgen hnX hnY hd hfinite W e he huniq hmono f

include hintX hintY in
/-- **Stacks 0EQ4.** In Situation 0EDT let `X/B` and `Y/B` be good, let `X` and `Y` be integral
with `n = dim_δ(X) = dim_δ(Y)`, let `p : X ⟶ Y` be a dominant proper morphism, let `f ∈ R(X)^*`
and set `g = Nm_{R(X)/R(Y)}(f)`. Then

`p_* div(f) = div(g)` in `Z_{n-1}(Y)`.

Here `div` is the principal divisor of Stacks 0EQ1
(`AlgebraicGeometry.Space.rationalFunctionPrincipalDivisorCycle`, at the canonical embeddings of
Stacks 0ENK), `p_*` is proper pushforward of cycles (Stacks 0EP2) and `g` is the norm
`AlgebraicGeometry.Space.rationalFunctionNorm` along the extension of function fields `p`
induces, as a unit of `R(Y)` (`AlgebraicGeometry.Space.rationalFunctionNormUnit`); `R(X)/R(Y)`
is finite (Stacks 0AD5, from `dim_δ(X) = dim_δ(Y)`). Both sides are `(n-1)`-cycles on `Y`,
determined by their coefficients at the prime divisors of `Y`, where they agree by
`AlgebraicGeometry.Space.finsum_rationalFunctionPrincipalDivisorCycle_mul_properCycleMult_eq`. -/
@[stacks 0EQ4 "p_* div(f) = div(Nm_{R(X)/R(Y)}(f)) in Z_{n-1}(Y), for X/B, Y/B good and integral
with dim_δ X = dim_δ Y = n, p : X → Y dominant and proper, f ∈ R(X)^*; div is 0EQ1 at the
canonical embeddings, p_* is 0EP2, the norm is constructed; nothing carried"]
theorem properCyclePushforward_rationalFunctionPrincipalDivisorCycle {p : X ⟶ Y}
    (hpB : p ≫ sY = sX) (hproper : IsProper D.site D.base D.base_mem p)
    (hdom : IsDominant D.site D.base D.base_mem p) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    properCyclePushforward D sX hX sY hY hpB hproper.2.1.2 (n - 1)
        (rationalFunctionPrincipalDivisorCycle D sX hX hintX hnX f) =
      rationalFunctionPrincipalDivisorCycle D sY hY hintY hnY
        (rationalFunctionNormUnit D.site D.base D.base_mem hX.1 hY.1 hintX hintY p
          (pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY
            p hdom) f) := by
  have hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (((n - 1) + 1 : ℤ) : EInt) := by
    rw [sub_add_cancel]
    exact hnY
  rw [← one_smul ℤ (rationalFunctionPrincipalDivisorCycle D sY hY hintY hnY _)]
  exact properCyclePushforward_eq_zsmul_of_forall_primeDivisor D sX hX sY hY hintY hpB
    hproper.2.1.2 hk _ _ 1 fun W => by
      rw [one_mul]
      exact finsum_rationalFunctionPrincipalDivisorCycle_mul_properCycleMult_eq D sX hX sY hY
        hintX hintY hpB hproper hdom hnX hnY f W

end Assembly

end AlgebraicGeometry.Space

end
