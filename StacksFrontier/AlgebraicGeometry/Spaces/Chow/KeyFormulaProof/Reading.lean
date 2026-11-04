module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.EtaleResidueFieldComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericPointChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.HeightOneComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChartStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.OrderTransport

/-!
# Reading a branch of the base-change chart at a height-one prime of the chart stalk

Let `W` be an étale chart of `X`, `Z ⊂ X` a prime divisor, `W' = W ×_X Z` and `y ∈ W'`. A
generization `q' ⤳ y` with `𝒪_{W', q'}` a field cuts out the minimal prime `𝔭` of `O = 𝒪_{W', y}`
(`AlgebraicGeometry.Scheme.primeOfSpecializes`), and the height-one prime `𝔮 = 𝔭 ∩ A` of
`A = 𝒪_{W, π y}`, `π : W' → W`, cuts out the point `π q'` of `W`
(`AlgebraicGeometry.Space.PrimeDivisor.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj`).

This file identifies the residue field `κ(A_𝔮)` (where the Key Lemma, Stacks 0EAX, measures
orders) with `κ(q')` (where the restriction to `Z` is read)
(`AlgebraicGeometry.Space.PrimeDivisor.heightOneResidueFieldEquiv`) and proves that the order
along `O/𝔭` of a total fraction of `O` is the order along `A/𝔮` of its value in `κ(q')`
(`AlgebraicGeometry.Space.PrimeDivisor.minimalPrimeOrd_eq_heightOneOrd_baseChange`).

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}}

/-- The point cut out by the prime of a generization `z ⤳ y` is `z`. -/
theorem fromSpecStalk_primeOfSpecializes {y z : T} (h : z ⤳ y) :
    T.fromSpecStalk y ⟨primeOfSpecializes h, inferInstance⟩ = z := by
  have h1 : (Spec.map (T.presheaf.stalkSpecializes h) ≫ T.fromSpecStalk y)
      (closedPoint (T.presheaf.stalk z)) = z := by
    rw [SpecMap_stalkSpecializes_fromSpecStalk, fromSpecStalk_closedPoint]
  exact h1

/-- The prime of the generization `fromSpecStalk y 𝔭 ⤳ y` is `𝔭`. -/
theorem primeOfSpecializes_fromSpecStalk (y : T) (p : PrimeSpectrum (T.presheaf.stalk y)) :
    primeOfSpecializes (Stacks.Chow.specializes_fromSpecStalk y p) = p.asIdeal := by
  have h : PrimeSpectrum.comap
      (T.presheaf.stalkSpecializes (Stacks.Chow.specializes_fromSpecStalk y p)).hom
      (closedPoint (T.presheaf.stalk (T.fromSpecStalk y p))) = p := by
    apply (T.fromSpecStalk y).isEmbedding.injective
    change (Spec.map (T.presheaf.stalkSpecializes (Stacks.Chow.specializes_fromSpecStalk y p)) ≫
      T.fromSpecStalk y) (closedPoint _) = _
    rw [SpecMap_stalkSpecializes_fromSpecStalk, fromSpecStalk_closedPoint]
  exact congrArg PrimeSpectrum.asIdeal h

/-- `fromSpecStalk` commutes with a morphism of schemes: the image of the point cut out by a
prime `𝔭` of `𝒪_{T, y}` is the point cut out by the pullback of `𝔭` to `𝒪_{T', f y}`. -/
theorem Hom.apply_fromSpecStalk {T' : Scheme.{u}} (f : T ⟶ T') (y : T)
    (p : PrimeSpectrum (T.presheaf.stalk y)) :
    f (T.fromSpecStalk y p) =
      T'.fromSpecStalk (f y) (PrimeSpectrum.comap (f.stalkMap y).hom p) := by
  have h := congrArg (fun g : Spec (T.presheaf.stalk y) ⟶ T' => g p)
    (SpecMap_stalkMap_fromSpecStalk f (x := y))
  exact h.symm

/-- The residue field congruence along an equality of points carries the residue of a
generization germ to the residue of the generization germ. -/
theorem residueFieldCongr_residue_stalkSpecializes {x z w : T} (hxz : x = z) (hx : x ⤳ w)
    (hz : z ⤳ w) (a : T.presheaf.stalk w) :
    (T.residueFieldCongr hxz).hom (T.residue x (T.presheaf.stalkSpecializes hx a)) =
      T.residue z (T.presheaf.stalkSpecializes hz a) := by
  subst hxz
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (V : SmallEtale B S hS X)

/-- The stalk map `𝒪_{W, π y} → 𝒪_{W', y}` of the closed immersion `π : W' = W ×_X Z → W` is
surjective. -/
theorem PrimeDivisor.surjective_stalkMap_baseChangeChartProj
    (y : chartScheme (Z.baseChangeChart B S hS hX V)) :
    Function.Surjective ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom := by
  have := Z.isClosedImmersion_baseChangeChartProj B S hS hX V
  exact (Z.baseChangeChartProj B S hS hX V).stalkMap_surjective y

variable (w : chartScheme V)
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk w) // 𝔮.IsPrime ∧ 𝔮.height = 1})
    (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hip : Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮 = Z.baseChangeChartProj B S hS hX V q')

/-- **`κ(A_𝔮) ≃ κ(q')`** for a height-one prime `𝔮` of `A = 𝒪_{W, w}` cutting out the image of a
point `q'` of `W' = W ×_X Z`: `A_𝔮 = 𝒪_{W, π q'}`, then the residue field isomorphism of the
closed immersion `W' → W`. -/
def PrimeDivisor.heightOneResidueFieldEquiv :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    ResidueField (Localization.AtPrime 𝔮.1) ≃+*
      (chartScheme (Z.baseChangeChart B S hS hX V)).residueField q' :=
  letI : 𝔮.1.IsPrime := 𝔮.2.1
  ((ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮)).trans
    ((chartScheme V).residueFieldCongr hip).commRingCatIsoToRingEquiv).trans
    (Z.baseChangeChartResidueFieldEquiv B S hS hX V q')

/-- On residues of `A = 𝒪_{W, π y}`, `κ(A_𝔮) ≃ κ(q')` is the residue at `q'` of the image under
`A → 𝒪_{W', y}` followed by the generization from `y` to `q'`. -/
theorem PrimeDivisor.heightOneResidueFieldEquiv_residue
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) //
      𝔮.IsPrime ∧ 𝔮.height = 1})
    (hip : Stacks.Chow.intermediatePointOfHeightOnePrime _ 𝔮 = Z.baseChangeChartProj B S hS hX V q')
    (h : q' ⤳ y) (a : (chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    Z.heightOneResidueFieldEquiv B S hS hX V _ 𝔮 q' hip
        (residue (Localization.AtPrime 𝔮.1) (algebraMap _ (Localization.AtPrime 𝔮.1) a)) =
      Scheme.stalkToResidueFieldOfSpecializes h
        ((Z.baseChangeChartProj B S hS hX V).stalkMap y a) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  have h1 : ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv
      (Z.baseChangeChartProj B S hS hX V y) 𝔮)
      (residue (Localization.AtPrime 𝔮.1) (algebraMap _ (Localization.AtPrime 𝔮.1) a)) =
      (chartScheme V).residue _ ((chartScheme V).presheaf.stalkSpecializes
        (Stacks.Chow.specializes_intermediatePointOfHeightOnePrime _ 𝔮) a) := by
    rw [ResidueField.mapEquiv_apply, ResidueField.map_residue]
    exact congrArg (residue _) (Stacks.Chow.stalkLocalizationAtPrimeEquiv_algebraMap _ 𝔮 a)
  have hsp : Z.baseChangeChartProj B S hS hX V q' ⤳ Z.baseChangeChartProj B S hS hX V y :=
    h.map (Z.baseChangeChartProj B S hS hX V).continuous
  have h2 := Scheme.residueFieldCongr_residue_stalkSpecializes hip
    (Stacks.Chow.specializes_intermediatePointOfHeightOnePrime _ 𝔮) hsp a
  have h3 := Z.baseChangeChartResidueFieldEquiv_residue B S hS hX V q'
    ((chartScheme V).presheaf.stalkSpecializes hsp a)
  have h4 := Scheme.Hom.stalkSpecializes_stalkMap_apply (Z.baseChangeChartProj B S hS hX V) q' y h a
  have h5 : Z.heightOneResidueFieldEquiv B S hS hX V (Z.baseChangeChartProj B S hS hX V y) 𝔮 q' hip
      (residue (Localization.AtPrime 𝔮.1) (algebraMap _ (Localization.AtPrime 𝔮.1) a)) =
      Z.baseChangeChartResidueFieldEquiv B S hS hX V q'
        (((chartScheme V).residueFieldCongr hip).hom
          (ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv
            (Z.baseChangeChartProj B S hS hX V y) 𝔮)
            (residue (Localization.AtPrime 𝔮.1) (algebraMap _ (Localization.AtPrime 𝔮.1) a)))) :=
    rfl
  refine h5.trans ?_
  rw [h1, h2, h3, h4]
  rfl

/-- **The two identifications of `Frac(O/𝔭)` with `κ(q')` agree**: through `A/𝔮 ≃ O/𝔭` and
`κ(A_𝔮) ≃ κ(q')`, and directly (`AlgebraicGeometry.Scheme.fractionRingQuotientEquivResidueField`),
for `𝔭` the prime of a generization `q' ⤳ y` with `𝒪_{W', q'}` a field. -/
theorem PrimeDivisor.heightOneResidueFieldEquiv_comp_minimalPrimeResidueFieldEquiv
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) //
      𝔮.IsPrime ∧ 𝔮.height = 1})
    (hip : Stacks.Chow.intermediatePointOfHeightOnePrime _ 𝔮 = Z.baseChangeChartProj B S hS hX V q')
    (h : q' ⤳ y) (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk q'))
    (hP : 𝔮.1 = (Scheme.primeOfSpecializes h).comap
      ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    (Z.heightOneResidueFieldEquiv B S hS hX V _ 𝔮 q' hip).toRingHom.comp
        (Ring.minimalPrimeResidueFieldEquiv ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom
          (Z.surjective_stalkMap_baseChangeChartProj B S hS hX V y)
          (Scheme.primeOfSpecializes h) 𝔮.1 hP).toRingHom =
      (Scheme.fractionRingQuotientEquivResidueField h hz).toRingHom := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  refine IsLocalization.ringHom_ext (_ ⧸ Scheme.primeOfSpecializes h)⁰
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_))
  obtain ⟨a, rfl⟩ := Z.surjective_stalkMap_baseChangeChartProj B S hS hX V y o
  change Z.heightOneResidueFieldEquiv B S hS hX V _ 𝔮 q' hip
      (Ring.minimalPrimeResidueFieldEquiv _ _ _ _ hP (algebraMap _ _ (Ideal.Quotient.mk _ _))) =
    Scheme.fractionRingQuotientEquivResidueField h hz (algebraMap _ _ (Ideal.Quotient.mk _ _))
  rw [Ring.minimalPrimeResidueFieldEquiv_algebraMap_mk,
    Scheme.fractionRingQuotientEquivResidueField_algebraMap]
  exact Z.heightOneResidueFieldEquiv_residue B S hS hX V q' y 𝔮 hip h a

/-- **(B5) The value in `κ(A_𝔮)` of a total fraction `F` of `O`, read through `Frac(O/𝔭)`, is
its value in `κ(q')`** under `κ(A_𝔮) ≃ κ(q')`. -/
theorem PrimeDivisor.heightOneResidueFieldEquiv_minimalPrimeFractionMap
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) //
      𝔮.IsPrime ∧ 𝔮.height = 1})
    (hip : Stacks.Chow.intermediatePointOfHeightOnePrime _ 𝔮 = Z.baseChangeChartProj B S hS hX V q')
    (h : q' ⤳ y) (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk q'))
    (hP : 𝔮.1 = (Scheme.primeOfSpecializes h).comap
      ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom)
    (K : Type*) [CommRing K]
    [Algebra ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) K]
    [IsFractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) K] (F : K) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    Z.heightOneResidueFieldEquiv B S hS hX V _ 𝔮 q' hip
        (Ring.minimalPrimeResidueFieldEquiv ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom
          (Z.surjective_stalkMap_baseChangeChartProj B S hS hX V y)
          (Scheme.primeOfSpecializes h) 𝔮.1 hP
          (Ring.minimalPrimeFractionMap (K := K)
            ⟨Scheme.primeOfSpecializes h, Scheme.primeOfSpecializes_mem_minimalPrimes h hz⟩ F)) =
      Scheme.totalFractionToResidueFieldOfSpecializes h hz K F := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  refine (RingHom.congr_fun
    (Z.heightOneResidueFieldEquiv_comp_minimalPrimeResidueFieldEquiv B S hS hX V q' y 𝔮 hip h hz
      hP) _).trans ?_
  exact Scheme.fractionRingQuotientEquivResidueField_minimalPrimeFractionMap h hz K F

/-- The height-one prime `𝔮 = 𝔭 ∩ A` cuts out the image in `W` of the point of `W'` cut out by
`𝔭`. -/
theorem PrimeDivisor.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : PrimeSpectrum ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) //
      𝔮.IsPrime ∧ 𝔮.height = 1})
    (h𝔮 : 𝔮.1 = p.asIdeal.comap ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom) :
    Stacks.Chow.intermediatePointOfHeightOnePrime _ 𝔮 =
      Z.baseChangeChartProj B S hS hX V
        ((chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecStalk y p) := by
  refine Eq.trans ?_ (Scheme.Hom.apply_fromSpecStalk (Z.baseChangeChartProj B S hS hX V) y p).symm
  exact congrArg ((chartScheme V).fromSpecStalk (Z.baseChangeChartProj B S hS hX V y))
    (PrimeSpectrum.ext h𝔮 : (⟨𝔮.1, 𝔮.2.1⟩ : PrimeSpectrum _) =
      PrimeSpectrum.comap ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom p)

/-- **The order along a branch of `W'` at `y` is the order along the height-one prime of
`𝒪_{W, π y}` below it, of the value at the generic point of the branch.** For a minimal prime `𝔭`
of `O = 𝒪_{W', y}` cutting out `q'` with `𝒪_{W', q'}` a field, `𝔮 = 𝔭 ∩ A` of height one and a
unit `F` of `Q(O)`, `ord_{O/𝔭}(F) = ord_{A/𝔮}(x)`, where `x ∈ κ(A_𝔮)` corresponds to the value
of `F` in `κ(q')`. -/
theorem PrimeDivisor.minimalPrimeOrd_eq_heightOneOrd_baseChange
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    [IsNoetherianRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))]
    [IsNoetherianRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    [Ring.KrullDimLE 1 ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) = 2)
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk
      ((chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecStalk y ⟨p.1, p.2.1.1⟩)))
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) //
      𝔮.IsPrime ∧ 𝔮.height = 1})
    (h𝔮 : 𝔮.1 = p.1.comap ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom)
    (F : FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (hF : IsUnit F) :
    Ring.minimalPrimeOrd p F hF =
      Stacks.Chow.heightOneOrd hdim (Stacks.Chow.heightOnePrimeEquivIdeal.symm 𝔮)
        (hF.map (((Z.heightOneResidueFieldEquiv B S hS hX V _ 𝔮 _
          (Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y
            ⟨p.1, p.2.1.1⟩ 𝔮 h𝔮)).symm.toRingHom).comp
          (Scheme.totalFractionToResidueFieldOfSpecializes
            (Stacks.Chow.specializes_fromSpecStalk y ⟨p.1, p.2.1.1⟩) hz
            (FractionRing
              ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))))).unit := by
  have h := Stacks.Chow.specializes_fromSpecStalk y ⟨p.1, p.2.1.1⟩
  have hpp : Scheme.primeOfSpecializes h = p.1 := Scheme.primeOfSpecializes_fromSpecStalk y _
  let p' : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) :=
    ⟨Scheme.primeOfSpecializes h, Scheme.primeOfSpecializes_mem_minimalPrimes h hz⟩
  have hp' : p = p' := Subtype.ext hpp.symm
  have hP : (Stacks.Chow.heightOnePrimeEquivIdeal.symm 𝔮 : Stacks.Chow.HeightOnePrime _).1.asIdeal =
      (p' : Ideal _).comap ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom := by
    change 𝔮.1 = _
    rw [h𝔮]
    exact congrArg _ hpp.symm
  have e1 : Ring.minimalPrimeOrd p F hF = Ring.minimalPrimeOrd p' F hF :=
    congrArg (fun r => Ring.minimalPrimeOrd r F hF) hp'
  have e2 := Ring.minimalPrimeOrd_eq_heightOneOrd _
    (Z.surjective_stalkMap_baseChangeChartProj B S hS hX V y) hdim p' _ hP F hF
  have e3 := Z.heightOneResidueFieldEquiv_minimalPrimeFractionMap B S hS hX V _ y 𝔮
    (Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y
      ⟨p.1, p.2.1.1⟩ 𝔮 h𝔮) h hz hP _ F
  refine e1.trans (e2.trans (congrArg _ (Units.ext ?_)))
  exact (RingEquiv.eq_symm_apply _).mpr e3

/-! ### Moving readings in `κ(𝒪_{X, x̄})` from `π q'` to the point of `𝔮` -/

variable (hdec : IsDecentSpace B S hS X)

/-- A reading identity in the residue field of the étale local ring at the geometric point over a
point of `V` transports along an equality of points. -/
theorem chartResidueFieldToEtale_eq_of_eq {q₁ q₂ : chartScheme V} (h12 : q₁ = q₂)
    (h₁ : chartSchemeToPoints B S hS X V q₁ = Z.genericPoint B S hS X)
    (h₂ : chartSchemeToPoints B S hS X V q₂ = Z.genericPoint B S hS X)
    (r : (chartScheme V).residueField q₁)
    (c : letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (h : chartResidueFieldToEtale B S hS hX V q₂ (((chartScheme V).residueFieldCongr h12).hom r) =
      Z.henselianResidueFieldToEtale B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V q₂).trans h₂) c) :
    chartResidueFieldToEtale B S hS hX V q₁ r =
      Z.henselianResidueFieldToEtale B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V q₁).trans h₁) c := by
  subst h12
  exact h

/-- `κ(q') ≃ κ(π q')` undoes `κ(A_𝔮) ≃ κ(q')` up to the congruence `κ(q) = κ(π q')`. -/
theorem PrimeDivisor.baseChangeChartResidueFieldEquiv_symm_heightOneResidueFieldEquiv
    (x : letI : 𝔮.1.IsPrime := 𝔮.2.1; ResidueField (Localization.AtPrime 𝔮.1)) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    (Z.baseChangeChartResidueFieldEquiv B S hS hX V q').symm
        (Z.heightOneResidueFieldEquiv B S hS hX V w 𝔮 q' hip x) =
      ((chartScheme V).residueFieldCongr hip).hom
        (ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮) x) :=
  (Z.baseChangeChartResidueFieldEquiv B S hS hX V q').symm_apply_apply _

/-- At the point of `𝔮`, the residue map of the chart leg on `κ(A_𝔮) = κ(q)` is the residue map
of `A_𝔮 → 𝒪_{X, x̄}`. -/
theorem chartResidueFieldToEtale_mapEquiv_stalkLocalizationAtPrimeEquiv
    (x : letI : 𝔮.1.IsPrime := 𝔮.2.1; ResidueField (Localization.AtPrime 𝔮.1)) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    letI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
    chartResidueFieldToEtale B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)
        (ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮) x) =
      ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) x := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
    (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
  have : IsLocalHom (chartStalkAtToEtaleLocalRing B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) :=
    isLocalHom_chartStalkToEtaleLocalRing B S hS hX (chartNeighborhoodAt B S hS hX V _)
      (chartPoint_chartNeighborhoodAt B S hS hX V _)
  have : IsLocalHom (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮).toRingHom :=
    IsLocalHom.of_surjective _ (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮).surjective
  have := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  have e : ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) x =
      ResidueField.map (chartStalkAtToEtaleLocalRing B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
        (ResidueField.map (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮).toRingHom x) := by
    rw [ResidueField.map_map]
    rfl
  exact e.symm

/-- **A reading at `q'` in `κ(𝒪_{X, x̄})` gives the reading of the corresponding element of
`κ(A_𝔮)`** at the geometric point over the point of `𝔮`: if the image in `κ(q) → κ(𝒪_{X, x̄})`,
`q = π q'`, of `x ∈ κ(A_𝔮)` (moved to `κ(q') ≃ κ(q)`) is the image of `c ∈ κ(𝒪^h_{X, ξ})`, then the
image of `x` along `A_𝔮 → 𝒪_{X, x̄'}` is the image of `c` along `𝒪^h_{X, ξ} → 𝒪_{X, x̄'}`, `x̄'`
the geometric point over the point of `𝔮`. -/
theorem PrimeDivisor.residueFieldMap_heightOnePrimeToEtaleLocalRing_eq
    (hq : chartSchemeToPoints B S hS X V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮) =
      Z.genericPoint B S hS X)
    (hq' : chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V q') =
      Z.genericPoint B S hS X)
    (x : letI : 𝔮.1.IsPrime := 𝔮.2.1; ResidueField (Localization.AtPrime 𝔮.1))
    (c : letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (h : chartResidueFieldToEtale B S hS hX V (Z.baseChangeChartProj B S hS hX V q')
        ((Z.baseChangeChartResidueFieldEquiv B S hS hX V q').symm
          (Z.heightOneResidueFieldEquiv B S hS hX V w 𝔮 q' hip x)) =
      Z.henselianResidueFieldToEtale B S hS hX hdec
        (Z.liesOver_chartGeometricPointAt_baseChangeChartProj B S hS hX V q' hq') c) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
    haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      ((chartGeometricPointAt_liesOver B S hS hX V _).trans hq)
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
    ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) x =
      ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans hq)) c := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  have h' : chartResidueFieldToEtale B S hS hX V (Z.baseChangeChartProj B S hS hX V q')
      (((chartScheme V).residueFieldCongr hip).hom
        (ResidueField.mapEquiv (Stacks.Chow.stalkLocalizationAtPrimeEquiv w 𝔮) x)) =
      Z.henselianResidueFieldToEtale B S hS hX hdec
        ((chartGeometricPointAt_liesOver B S hS hX V _).trans hq') c := by
    refine Eq.trans ?_ h
    congr 1
    exact ((Z.baseChangeChartResidueFieldEquiv B S hS hX V q').symm_apply_apply _).symm
  have h2 := chartResidueFieldToEtale_eq_of_eq B S hS hX Z V hdec hip hq hq' _ c h'
  refine Eq.trans ?_ h2
  exact (chartResidueFieldToEtale_mapEquiv_stalkLocalizationAtPrimeEquiv B S hS hX V w 𝔮 x).symm

/-! ### The branches of `W'` at `y` and the height-one primes of `𝒪_{W, π y}` over `ξ` -/

/-- The height-one primes of `𝒪_{W, u}` whose point lies over the generic point of `Z`. -/
abbrev PrimeDivisor.HeightOnePrimeOver (u : chartScheme V) :=
  {𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk u) // 𝔮.IsPrime ∧ 𝔮.height = 1} //
    chartSchemeToPoints B S hS X V (Stacks.Chow.intermediatePointOfHeightOnePrime u 𝔮) =
      Z.genericPoint B S hS X}

include hdec in
/-- **The branches of `W' = V ×_X Z` at `y` are the height-one primes of `𝒪_{V, π y}` over the
generic point of `Z`**: `𝔭 ↦ 𝔭 ∩ 𝒪_{V, π y}`
(`AlgebraicGeometry.Space.PrimeDivisor.minimalPrimesStalkBaseChangeChartEquiv`). -/
def PrimeDivisor.minimalPrimesEquivHeightOnePrimeOver
    (y : chartScheme (Z.baseChangeChart B S hS hX V)) :
    minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) ≃
      Z.HeightOnePrimeOver B S hS V (Z.baseChangeChartProj B S hS hX V y) :=
  (Z.minimalPrimesStalkBaseChangeChartEquiv B S hS hX V y).trans
    { toFun := fun 𝔮 => ⟨⟨𝔮.1, 𝔮.2.1, by
          have := 𝔮.2.1
          exact Z.height_eq_one_of_fromSpecStalk_eq_genericPoint B S hS hX hdec V _ 𝔮.1
            𝔮.2.2⟩, 𝔮.2.2⟩
      invFun := fun P => ⟨P.1.1, P.1.2.1, P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The height-one prime of a branch is the pullback of its minimal prime. -/
theorem PrimeDivisor.minimalPrimesEquivHeightOnePrimeOver_asIdeal
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) :
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1.1 =
      p.1.comap ((Z.baseChangeChartProj B S hS hX V).stalkMap y).hom :=
  rfl

include hdec in
/-- The generic point of a branch lies over the generic point of `Z`. -/
theorem PrimeDivisor.chartSchemeToPoints_baseChangeChartProj_fromSpecStalk
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) :
    chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V
      ((chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecStalk y ⟨p.1, p.2.1.1⟩)) =
      Z.genericPoint B S hS X :=
  (congrArg (chartSchemeToPoints B S hS X V)
    (Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y ⟨p.1, p.2.1.1⟩
      (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 rfl).symm).trans
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).2

include hdec in
/-- The local ring of `W'` at the generic point of a branch is a field. -/
theorem PrimeDivisor.isField_stalk_fromSpecStalk_minimalPrime
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) :
    IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk
      ((chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecStalk y ⟨p.1, p.2.1.1⟩)) :=
  Z.isField_stalk_baseChangeChart B S hS hX V _
    (Z.chartSchemeToPoints_baseChangeChartProj_fromSpecStalk B S hS hX V hdec y p)

/-- **The reading at a branch, in `κ(A_𝔮)`**: a total fraction `F` of `𝒪_{W', y}`, read at the
generic point `q'` of the branch through `𝔭` and moved to `κ(A_𝔮)`, `𝔮 = 𝔭 ∩ A`. -/
def PrimeDivisor.branchReading (y : chartScheme (Z.baseChangeChart B S hS hX V))
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)) :
    FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y) →+*
      ResidueField (Localization.AtPrime (Stacks.Chow.heightOnePrimeEquivIdeal.symm
        (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1).1.asIdeal) :=
  ((Z.heightOneResidueFieldEquiv B S hS hX V _
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 _
    (Z.intermediatePointOfHeightOnePrime_eq_baseChangeChartProj B S hS hX V y ⟨p.1, p.2.1.1⟩
      _ rfl)).symm.toRingHom).comp
    (Scheme.totalFractionToResidueFieldOfSpecializes
      (Stacks.Chow.specializes_fromSpecStalk y ⟨p.1, p.2.1.1⟩)
      (Z.isField_stalk_fromSpecStalk_minimalPrime B S hS hX V hdec y p)
      (FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)))

/-- **The order along a branch is the order along the height-one prime below it of the branch
reading.** -/
theorem PrimeDivisor.minimalPrimeOrd_eq_heightOneOrd_branchReading
    (y : chartScheme (Z.baseChangeChart B S hS hX V))
    [IsNoetherianRing ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y))]
    [IsNoetherianRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    [Ring.KrullDimLE 1 ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y)]
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk (Z.baseChangeChartProj B S hS hX V y)) = 2)
    (p : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (F : FractionRing ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk y))
    (hF : IsUnit F) :
    Ring.minimalPrimeOrd p F hF =
      Stacks.Chow.heightOneOrd hdim (Stacks.Chow.heightOnePrimeEquivIdeal.symm
          (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1)
        (hF.map (Z.branchReading B S hS hX V hdec y p)).unit :=
  Z.minimalPrimeOrd_eq_heightOneOrd_baseChange B S hS hX V y hdim p
    (Z.isField_stalk_fromSpecStalk_minimalPrime B S hS hX V hdec y p)
    (Z.minimalPrimesEquivHeightOnePrimeOver B S hS hX V hdec y p).1 rfl F hF

end AlgebraicGeometry.Space

end
