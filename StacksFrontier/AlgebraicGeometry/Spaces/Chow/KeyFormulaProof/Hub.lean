module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.HubComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.HeightOneComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Algebra

/-!
# The comparison of the two tame symbols at a height-one prime of a chart stalk

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ` and henselian local ring `B = 𝒪^h_{X, ξ}`, `V` an étale chart of `X` with affine
scheme, `w ∈ V`, `A = 𝒪_{V, w}` and `𝔮 ⊂ A` a height-one prime cutting out a point `q` of `V` over
`ξ`. At the geometric point `x̄` over `q` (`AlgebraicGeometry.Space.chartGeometricPointAt`) the
étale local ring `R = 𝒪_{X, x̄}` receives both `B` (Stacks 0EMZ) and `A_𝔮` (Stacks 05VP), flatly,
locally and with maximal-ideal extension.

For an invertible module `ℒ` free on `e` over `V` and a meromorphic section `s` with
`s / e = a` on `V`, write `s = f · (v s_ξ)` at `ξ`. The ratio comparison
(`AlgebraicGeometry.Space.PrimeDivisor.exists_unit_canonicalGenericRatio_eq`) gives a unit `μ` of
`R` with `s / s_ξ = a · μ` in `Q(R)`, so `f = a · (μ v⁻¹)` in `Q(R)`
(`AlgebraicGeometry.Space.heightOnePrime_sectionRatio_eq`). Feeding this into the comparison of
tame symbols in a common extension (`Stacks.Chow.tameSymbol_hub_comparison`) gives
`ord_B(f) = ord_{A_𝔮}(a)` and
`∂_B(f, g) = ∂_{A_𝔮}(a, b) · m̄^{-ord(a)} · l̄^{ord(b)}` in `κ(R)`, `l = μ v⁻¹`, `m = μ' w⁻¹`
(`AlgebraicGeometry.Space.heightOnePrime_tameSymbol_hub`).

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing Stacks.Chow
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) (V : SmallEtale B S hS X) (hV : IsAffine (chartScheme V))
    (w : chartScheme V)
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk w) // 𝔮.IsPrime ∧ 𝔮.height = 1})
    (hq : chartSchemeToPoints B S hS X V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮) =
      Z.genericPoint B S hS X)

include hq in
/-- The geometric point over the point cut out by `𝔮` lies over the generic point of `Z`. -/
theorem heightOnePrime_liesOver :
    (chartGeometricPointAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)).LiesOver
      (Z.genericPoint B S hS X) :=
  (chartGeometricPointAt_liesOver B S hS hX V _).trans hq

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)

/-- **The ratio `f` of `s = f · (v s_ξ)`, read in `Q(𝒪_{X, x̄})`, is the chart ratio `s / e`, read
in `Q(A_𝔮)` and pushed to `Q(𝒪_{X, x̄})`, times the unit `μ v⁻¹`**, where `μ` is the unit of the
ratio comparison. -/
theorem heightOnePrime_sectionRatio_eq
    (μ : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hμ : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr)
          (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
            (chartNeighborhoodAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
            hV (chartRatio B S hS X hX L V e hecompat hebij s) *
          algebraMap _ _ (μ : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))))
    (f : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hfv : (f : Z.genericTotalFractionRing B S hS hX hdec) *
        algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s) :
    Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) f =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)
            (chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
              (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
                (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
                  B S hS hX hInt)
                (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
                V hV) w
              (chartRatio B S hS X hX L V e hecompat hebij s))) *
        algebraMap _ _ ((μ * (Units.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)).toMonoidHom v)⁻¹ :
            (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
              (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ) :
          (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))) := by
  set ψ := Z.henselianToEtaleLocalRing B S hS hX hdec (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
  set Θ := Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec ψ
    (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr)
  have hJ := affineChartMeromorphicToEtaleFractionRing_eq_heightOneFractionMap B S hS hX V w 𝔮
    (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
      B S hS hX hInt)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) hV
    (chartRatio B S hS X hX L V e hecompat hebij s)
  have h1 : Θ f * algebraMap _ (FractionRing _) (ψ v) =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)
            (chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
              (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
                (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
                  B S hS hX hInt)
                (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
                V hV) w
              (chartRatio B S hS X hX L V e hecompat hebij s))) * algebraMap _ _ μ.val := by
    rw [← Z.genericTotalFractionRingToEtaleFractionRing_algebraMap B S hS X hX hdec ψ
      (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
        (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr), ← map_mul, hfv, hμ, hJ]
  have hu : algebraMap (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))
        (FractionRing (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))) (ψ v) *
      algebraMap _ _ (Units.map ψ.toMonoidHom v)⁻¹.val = 1 := by
    rw [← map_mul, show ψ (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      (Units.map ψ.toMonoidHom v).val from rfl, Units.mul_inv, map_one]
  rw [Units.val_mul, map_mul, ← mul_assoc, ← h1, mul_assoc, hu, mul_one]

include hq in
/-- The map `Q(B) → Q(𝒪_{X, x̄})` of the hub comparison is the map induced by Stacks 0EMZ. -/
theorem heightOnePrime_isLocalizationMap_henselian_eq
    (x : Z.genericTotalFractionRing B S hS hX hdec) :
    letI := (Z.henselianToEtaleLocalRing B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)).toAlgebra
    haveI : Module.Flat ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
      Z.flat_henselianToEtaleLocalRing B S hS hX hdec (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
    IsLocalization.map (FractionRing (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
        (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
        (nonZeroDivisors_le_comap_of_flat (A := ↥(Z.genericHenselianLocalRing B S hS hX hdec))
          (A' := (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))) x =
      Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) x :=
  rfl

/-- The map `Q(A_𝔮) → Q(𝒪_{X, x̄})` of the hub comparison is the map induced by Stacks 05VP. -/
theorem heightOnePrime_isLocalizationMap_heightOne_eq
    (x : FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) :
    letI : Algebra (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
      (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
    haveI : Module.Flat (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
      flat_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
    IsLocalization.map (FractionRing (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
        (algebraMap (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
          (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
        (nonZeroDivisors_le_comap_of_flat
          (A := Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
          (A' := (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
            (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))) x =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮 x :=
  rfl

variable [IsNoetherianRing ((chartScheme V).presheaf.stalk w)]

omit [IsNoetherianRing ((chartScheme V).presheaf.stalk w)] in
/-- The instances of the hub comparison at a height-one prime. -/
theorem heightOnePrime_hub_instances :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
    letI := (Z.henselianToEtaleLocalRing B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)).toAlgebra
    letI : Algebra (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
      (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
    Module.Flat ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) ∧
      IsLocalHom (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))) ∧
      Module.Flat (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) ∧
      IsLocalHom (algebraMap
        (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))) :=
  ⟨Z.flat_henselianToEtaleLocalRing B S hS hX hdec (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq),
    Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq),
    flat_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮,
    isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮⟩

/-- The order and symbol parts of the hub comparison at a height-one prime. -/
private theorem heightOnePrime_hub_comparison
    (f g : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (l m : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ)
    (hf : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) f =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) a) * algebraMap _ _ l.val)
    (hg : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) g =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) b) * algebraMap _ _ m.val) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
    haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
    haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit =
      Ring.ordTotalFracInt (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a :
          (FractionRing (Localization.AtPrime
            (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
          FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
        (Units.isUnit _) ∧
    Units.map (ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))).toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
            (Z.genericTotalFractionRing B S hS hX hdec) f g) =
        Units.map (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)).toMonoidHom
            (tameSymbolOfKrullDimOne
              (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
              (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
              (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a)
              (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                b)) *
          (Units.map (residue _).toMonoidHom m ^
            Ring.ordTotalFracInt (Localization.AtPrime
              (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
              ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                a :
                (FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
                FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) (Units.isUnit _))⁻¹ *
          Units.map (residue _).toMonoidHom l ^
            Ring.ordTotalFracInt (Localization.AtPrime
              (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
              ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                b :
                (FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
                FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) (Units.isUnit _) := by
  have hxbar := heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  let := isLocalRing_etaleLocalRing B S hS X hX
    (chartGeometricPointAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
  let := isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X hX hN
    (chartGeometricPointAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
  let : Algebra ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
    (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let : Algebra (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
      (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
    (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
  obtain ⟨i1, i2, i3, i4⟩ := heightOnePrime_hub_instances B S hS hX hdec Z V w 𝔮 hq
  let : IsNoetherianRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal) :=
    IsLocalization.isNoetherianRing (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal.primeCompl _
      inferInstance
  have hf' := (heightOnePrime_isLocalizationMap_henselian_eq B S hS hX hdec Z V w 𝔮 hq
    (f : Z.genericTotalFractionRing B S hS hX hdec)).trans
    (hf.trans (congrArg (· * _)
      (heightOnePrime_isLocalizationMap_heightOne_eq B S hS hX V w 𝔮
        (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) a)).symm))
  have hg' := (heightOnePrime_isLocalizationMap_henselian_eq B S hS hX hdec Z V w 𝔮 hq
    (g : Z.genericTotalFractionRing B S hS hX hdec)).trans
    (hg.trans (congrArg (· * _)
      (heightOnePrime_isLocalizationMap_heightOne_eq B S hS hX V w 𝔮
        (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) b)).symm))
  rw [← MonoidHom.coe_coe (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)),
    ← Units.coe_map] at hf' hg'
  have hmB : Ideal.map (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
      (maximalIdeal ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      maximalIdeal (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
    Z.map_maximalIdeal_henselianToEtaleLocalRing B S hS hX hdec hxbar
  have hmC : Ideal.map (algebraMap
      (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
      (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)))
      (maximalIdeal (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) =
      maximalIdeal (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
        (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1)) :=
    map_maximalIdeal_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  exact tameSymbol_hub_comparison hmB hmC
    (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
    (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
    (Z.ringKrullDim_etaleLocalRing_eq_one B S hS hX hdec hxbar)
    (Z.genericTotalFractionRing B S hS hX hdec)
    (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
    (FractionRing (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))) f g
    (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a)
    (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom b) l m
    hf' hg'

include hInt hN in
/-- **The order part of the hub comparison at a height-one prime.** If `f = a · l` in
`Q(𝒪_{X, x̄})` with `l` a unit, then `ord_B(f) = ord_{A_𝔮}(a)`. -/
theorem heightOnePrime_ord_hub
    (f : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (a : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (l : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ)
    (hf : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) f =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) a) * algebraMap _ _ l.val) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit =
      Ring.ordTotalFracInt (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
        ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a :
          (FractionRing (Localization.AtPrime
            (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
          FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
        (Units.isUnit _) :=
  (heightOnePrime_hub_comparison B S hS hX hdec hInt hN Z V w 𝔮 hq f f a a l l hf hf).1

include hInt hN in
/-- **The symbol part of the hub comparison at a height-one prime.** If `f = a · l` and
`g = b · m` in `Q(𝒪_{X, x̄})` with `l, m` units, then
`∂_B(f, g) = ∂_{A_𝔮}(a, b) · m̄^{-ord(a)} · l̄^{ord(b)}` in `κ(𝒪_{X, x̄})`. -/
theorem heightOnePrime_tameSymbol_hub
    (f g : (Z.genericTotalFractionRing B S hS hX hdec)ˣ)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (l m : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ)
    (hf : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) f =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) a) * algebraMap _ _ l.val)
    (hg : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr) g =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
          (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) b) * algebraMap _ _ m.val) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
    haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
    haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
    haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
    Units.map (ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))).toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
            (Z.genericTotalFractionRing B S hS hX hdec) f g) =
        Units.map (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)).toMonoidHom
            (tameSymbolOfKrullDimOne
              (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
              (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
              (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a)
              (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                b)) *
          (Units.map (residue _).toMonoidHom m ^
            Ring.ordTotalFracInt (Localization.AtPrime
              (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
              ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                a :
                (FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
                FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) (Units.isUnit _))⁻¹ *
          Units.map (residue _).toMonoidHom l ^
            Ring.ordTotalFracInt (Localization.AtPrime
              (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)
              ((Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
                b :
                (FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ) :
                FractionRing (Localization.AtPrime
                  (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) (Units.isUnit _) :=
  (heightOnePrime_hub_comparison B S hS hX hdec hInt hN Z V w 𝔮 hq f g a b l m hf hg).2

include hInt hN in
/-- **The identity of Stacks 0EQV at a height-one prime `𝔮` of the chart stalk.** Let `s, t` be
meromorphic sections of `ℒ, 𝒩` with `s = a e_ℒ`, `t = b e_𝒩` on `V` (`a, b` units of `Q(A)`),
`s = f (v₁ s_ξ)`, `t = g (v₂ t_ξ)` at `ξ`, and let `μ_ℒ, μ_𝒩` be the units of the ratio comparison.
Let `x, y, z ∈ κ(A_𝔮)^*` be elements whose images in `κ(𝒪_{X, x̄})` are
`v̄₁ μ̄_ℒ⁻¹`, `v̄₂ μ̄_𝒩⁻¹` and `∂_B(f, g)` (the readings of `(v₁ s_ξ)|_Z`, `(v₂ t_ξ)|_Z` and of
`∂_B(f, g)` at `𝔮`). Then
`ord_B(f) ord_{A/𝔮}(y) - ord_B(g) ord_{A/𝔮}(x) - ord_{A/𝔮}(z) = -ord_{A/𝔮}(∂_{A_𝔮}(a, b))`. -/
theorem heightOnePrime_keyFormula_identity
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk w) = 2)
    (N : Modules.{u, u} B S hS X hX) (hN' : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (e' : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat' : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (e' W k) = e' W' (g ≫ k))
    (hebij' : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e' W k)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk w)) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) w
        (chartRatio B S hS X hX L V e hecompat hebij s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk w)) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) w
        (chartRatio B S hS X hX N V e' hecompat' hebij' t))
    (μL μN : (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V
      (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) : Type (u + 1))ˣ)
    (hμL : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr)
          (Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
            (chartNeighborhoodAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
            hV (chartRatio B S hS X hX L V e hecompat hebij s) * algebraMap _ _ μL.val)
    (hμN : Z.genericTotalFractionRingToEtaleFractionRing B S hS X hX hdec
          (Z.henselianToEtaleLocalRing B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))
          (fun _ hr ↦ Z.henselianToEtaleLocalRing_mem_nonZeroDivisors B S hS hX hdec
            (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) hr)
          (Z.canonicalGenericRatio B S hS hX hdec N hN' hInt hN t) =
        affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN)
            (chartNeighborhoodAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
            hV (chartRatio B S hS X hX N V e' hecompat' hebij' t) * algebraMap _ _ μN.val)
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
    (x y z : (ResidueField
      (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))ˣ)
    (hx : haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
      Units.map (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)).toMonoidHom x =
        Units.map (residue _).toMonoidHom (Units.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)).toMonoidHom v₁) *
        (Units.map (residue _).toMonoidHom μL)⁻¹)
    (hy : haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
      Units.map (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)).toMonoidHom y =
        Units.map (residue _).toMonoidHom (Units.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)).toMonoidHom v₂) *
        (Units.map (residue _).toMonoidHom μN)⁻¹)
    (hz : haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
      haveI := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
          (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
      haveI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec
        (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
      haveI := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
      Units.map (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)).toMonoidHom z =
        Units.map (ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq))).toMonoidHom
          (tameSymbolOfKrullDimOne
            (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
            (Z.genericTotalFractionRing B S hS hX hdec) f g)) :
    haveI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI := krullDimLE_one_of_ringKrullDim_eq_one
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN)
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (f : Z.genericTotalFractionRing B S hS hX hdec) f.isUnit *
          heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮) y -
        Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (g : Z.genericTotalFractionRing B S hS hX hdec) g.isUnit *
          heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮) x -
        heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮) z =
      -heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮)
        (tameSymbolOfKrullDimOne
          (ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮))
          (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
          (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a)
          (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom
            b)) := by
  have hf := heightOnePrime_sectionRatio_eq B S hS hX hdec hInt hN Z V hV w 𝔮 hq L hL e hecompat
    hebij μL s hμL f v₁ hfv
  have hg := heightOnePrime_sectionRatio_eq B S hS hX hdec hInt hN Z V hV w 𝔮 hq N hN' e'
    hecompat' hebij' μN t hμN g v₂ hgv
  rw [← ha] at hf
  rw [← hb] at hg
  have h1 := heightOnePrime_ord_hub B S hS hX hdec hInt hN Z V w 𝔮 hq f a _ hf
  have h2 := heightOnePrime_ord_hub B S hS hX hdec hInt hN Z V w 𝔮 hq g b _ hg
  have h3 := heightOnePrime_tameSymbol_hub B S hS hX hdec hInt hN Z V w 𝔮 hq f g a b _ _ hf hg
  let := isLocalRing_etaleLocalRing B S hS X hX (chartGeometricPointAt B S hS hX V
    (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮))
  let := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  have key := keyFormula_perPrime_identity
    (ResidueField.map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮))
    (heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮))
    (heightOneOrd_mul hdim (heightOnePrimeOfIdeal B S hS V w 𝔮)) _ _ x y z _ _ _ _
    (hx.trans ?_) (hy.trans ?_) hz h3
  · rw [h1, h2]
    exact key
  · simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  · simp only [map_mul, map_inv, mul_inv_rev, inv_inv]

include hInt hq in
/-- **The summand of the Key Lemma at `𝔮` vanishes when `s` and `t` generate at `ξ`.** If the
ratios `s / s_ξ` and `t / t_ξ` are units of `B = 𝒪^h_{X, ξ}` (`ξ` the point of `𝔮`), the chart
ratios `a = s / e_ℒ`, `b = t / e_𝒩` become units of `A_𝔮` (ratio comparison and unit descent),
so `ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = 0`. -/
theorem heightOnePrime_tameSymbolOrd_eq_zero_of_generates
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk w) = 2)
    (N : Modules.{u, u} B S hS X hX) (hN' : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (e' : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat' : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (e' W k) = e' W' (g ≫ k))
    (hebij' : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e' W k)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (t : MeromorphicSection.{u, u} B S hS X hX N)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk w)) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) w
        (chartRatio B S hS X hX L V e hecompat hebij s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk w)) =
      chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            B S hS hX hInt)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) w
        (chartRatio B S hS X hX N V e' hecompat' hebij' t))
    (hs : ∃ c : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit c ∧
      Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN s =
        algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) c)
    (ht : ∃ c : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit c ∧
      Z.canonicalGenericRatio B S hS hX hdec N hN' hInt hN t =
        algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) c) :
    heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮)
      (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime
          (heightOnePrimeOfIdeal B S hS V w 𝔮))
        (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
        (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom a)
        (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom b)) =
      0 := by
  have hdesc : ∀ (M : Modules.{u, u} B S hS X hX) (hM : IsInvertibleModule (B := B) ⟨X, hX⟩ M)
      (eM : (W : SmallEtale B S hS X) → (W ⟶ V) → M.val.obj (op W))
      (hcM : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
        (M.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
      (hbM : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS X hX W ↦ r • eM W k)
      (u : MeromorphicSection.{u, u} B S hS X hX M)
      (x : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
      (_ : (x : FractionRing ((chartScheme V).presheaf.stalk w)) =
        chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩
            (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
              B S hS hX hInt)
            (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) V hV) w
          (chartRatio B S hS X hX M V eM hcM hbM u))
      (_ : ∃ c : ↥(Z.genericHenselianLocalRing B S hS hX hdec), IsUnit c ∧
        Z.canonicalGenericRatio B S hS hX hdec M hM hInt hN u =
          algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) c),
      ∃ c : (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)ˣ,
        heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) x = algebraMap _ _
          (c : Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal) := by
    intro M hM eM hcM hbM u x hx hu
    obtain ⟨c, hc, hρ⟩ := hu
    obtain ⟨μ, hμ⟩ := Z.exists_unit_canonicalGenericRatio_eq B S hS hX hdec hInt hN M hM
      (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq)
      (chartNeighborhoodAt B S hS hX V (Stacks.Chow.intermediatePointOfHeightOnePrime w 𝔮)) hV
      eM hcM hbM
    have hJ := affineChartMeromorphicToEtaleFractionRing_eq_heightOneFractionMap B S hS hX V w 𝔮
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
        B S hS hX hInt)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN) hV
      (chartRatio B S hS X hX M V eM hcM hbM u)
    have h1 := hμ u
    rw [hρ, Z.genericTotalFractionRingToEtaleFractionRing_algebraMap] at h1
    have h2 : heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
        (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) x) =
        algebraMap _ _ (Z.henselianToEtaleLocalRing B S hS hX hdec
          (heightOnePrime_liesOver B S hS hX Z V w 𝔮 hq) c * (μ⁻¹ : _ˣ).val) := by
      rw [map_mul, h1, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one, hx]
      exact hJ.symm
    obtain ⟨d, hd, hxd⟩ := exists_isUnit_eq_algebraMap_of_heightOnePrimeFractionMap_eq B S hS hX V
      w 𝔮 (((hc.map _).mul (μ⁻¹).isUnit)) h2
    exact ⟨hd.unit, hxd⟩
  exact heightOneOrd_tameSymbol_eq_zero_of_isUnit B S hS V w 𝔮 hdim a b
    (hdesc L hL e hecompat hebij s a ha hs) (hdesc N hN' e' hecompat' hebij' t b hb ht)

end AlgebraicGeometry.Space

end
