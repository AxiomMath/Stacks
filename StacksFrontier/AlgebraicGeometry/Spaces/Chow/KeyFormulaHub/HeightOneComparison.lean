module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityTotalFraction
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureFractionFieldOrder
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.UnitCorrection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.RingTheory.FaithfullyFlatFractionUnit

/-!
# The étale local ring at a height-one prime of a chart stalk

Let `X` be a decent, locally Noetherian, integral algebraic space, let `V` be an étale chart of
`X` with affine scheme, `w` a point of `V`, `A = 𝒪_{V, w}` and `𝔮` a height-one prime of `A`,
cutting out the point `q` of `V`. At the geometric point `x̄` over `q` of
`AlgebraicGeometry.Space.chartGeometricPointAt` the étale local ring `R = 𝒪_{X, x̄}` receives
`A_𝔮 ≅ 𝒪_{V, q}` along the canonical map of Stacks 05VP. This file records:

* the reading of a meromorphic function of `V` in `Q(R)`
  (`AlgebraicGeometry.Space.affineChartMeromorphicToEtaleFractionRing`) factors through its
  germ in `Q(A)`, then `Q(A_𝔮)`; the map `A_𝔮 → R` is flat, local, extends the maximal ideal and
  `A_𝔮` has dimension one;
* a total fraction of `A_𝔮` which becomes a unit of `R` was a unit of `A_𝔮`, and the summand
  of the Key Lemma (Stacks 0EAX) at `𝔮` of two units of `A_𝔮` vanishes (Stacks 0EAN).

## Main definitions

* `AlgebraicGeometry.Space.heightOnePrimeToEtaleLocalRing`: the map `A_𝔮 → 𝒪_{X, x̄}`.

## Main results

* `AlgebraicGeometry.Space.affineChartMeromorphicToEtaleFractionRing_eq_heightOneFractionMap`:
  the factorization of the reading.
* `AlgebraicGeometry.Space.flat_heightOnePrimeToEtaleLocalRing`,
  `AlgebraicGeometry.Space.isLocalHom_heightOnePrimeToEtaleLocalRing`,
  `AlgebraicGeometry.Space.map_maximalIdeal_heightOnePrimeToEtaleLocalRing`,
  `AlgebraicGeometry.Space.faithfullyFlat_heightOnePrimeToEtaleLocalRing`.
* `AlgebraicGeometry.Space.exists_isUnit_eq_algebraMap_of_heightOnePrimeFractionMap_eq`: unit
  descent.
* `AlgebraicGeometry.Space.heightOneOrd_tameSymbol_eq_zero_of_isUnit`: the vanishing of the
  summand.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 0EAN](https://stacks.math.columbia.edu/tag/0EAN)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing Stacks.Chow
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : SmallEtale B S hS X) (w : chartScheme V)
    (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk w) // 𝔮.IsPrime ∧ 𝔮.height = 1})

/-- The height-one prime `𝔮` as a point of `Spec A` of height one, the indexing of
`Stacks.Chow.heightOneFractionMap`. -/
abbrev heightOnePrimeOfIdeal : HeightOnePrime ((chartScheme V).presheaf.stalk w) :=
  heightOnePrimeEquivIdeal.symm 𝔮

/-- **The map `A_𝔮 → 𝒪_{X, x̄}`.** The identification of `A_𝔮` with the local ring of `V` at the
point `q` cut out by `𝔮`, followed by the canonical map of Stacks 05VP at the geometric point
`AlgebraicGeometry.Space.chartGeometricPointAt` over `q`. -/
def heightOnePrimeToEtaleLocalRing :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    Localization.AtPrime 𝔮.1 →+* (etaleLocalRing B S hS X
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
        Type (u + 1)) :=
  letI : 𝔮.1.IsPrime := 𝔮.2.1
  (chartStalkAtToEtaleLocalRing B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)).comp
    (stalkLocalizationAtPrimeEquiv w 𝔮).toRingHom

/-- On `A` the map `A_𝔮 → 𝒪_{X, x̄}` is the germ at `x̄` after the specialization of germs from
`w` to `q`. -/
theorem heightOnePrimeToEtaleLocalRing_algebraMap (a : (chartScheme V).presheaf.stalk w) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
        (algebraMap ((chartScheme V).presheaf.stalk w) (Localization.AtPrime 𝔮.1) a) =
      chartStalkAtToEtaleLocalRing B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)
        (((chartScheme V).presheaf.stalkSpecializes
          (specializes_intermediatePointOfHeightOnePrime w 𝔮)).hom a) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  exact congrArg (chartStalkAtToEtaleLocalRing B S hS hX V
    (intermediatePointOfHeightOnePrime w 𝔮)) (stalkLocalizationAtPrimeEquiv_algebraMap w 𝔮 a)

/-- The map `A_𝔮 → 𝒪_{X, x̄}` is flat. -/
theorem flat_heightOnePrimeToEtaleLocalRing :
    (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).Flat :=
  let : 𝔮.1.IsPrime := 𝔮.2.1
  RingHom.Flat.comp (RingHom.Flat.of_bijective (stalkLocalizationAtPrimeEquiv w 𝔮).bijective)
    (flat_chartStalkToEtaleLocalRing B S hS hX _ _)

/-- The map `A_𝔮 → 𝒪_{X, x̄}` is a local homomorphism. -/
theorem isLocalHom_heightOnePrimeToEtaleLocalRing :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    letI := isLocalRing_etaleLocalRing B S hS X hX
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
    IsLocalHom (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := isLocalRing_etaleLocalRing B S hS X hX
    (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
  have : IsLocalHom (chartStalkAtToEtaleLocalRing B S hS hX V
      (intermediatePointOfHeightOnePrime w 𝔮)) :=
    isLocalHom_chartStalkToEtaleLocalRing B S hS hX
      (chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
      (chartPoint_chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
  have : IsLocalHom (stalkLocalizationAtPrimeEquiv w 𝔮).toRingHom :=
    IsLocalHom.of_surjective _ (stalkLocalizationAtPrimeEquiv w 𝔮).surjective
  exact RingHom.isLocalHom_comp _ _

/-- The map `A_𝔮 → 𝒪_{X, x̄}` extends the maximal ideal of `A_𝔮` to the maximal ideal of
`𝒪_{X, x̄}`. -/
theorem map_maximalIdeal_heightOnePrimeToEtaleLocalRing :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    letI := isLocalRing_etaleLocalRing B S hS X hX
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
    (maximalIdeal (Localization.AtPrime 𝔮.1)).map (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) =
      maximalIdeal (etaleLocalRing B S hS X
        (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
          Type (u + 1)) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := isLocalRing_etaleLocalRing B S hS X hX
    (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
  rw [heightOnePrimeToEtaleLocalRing, ← Ideal.map_map,
    map_maximalIdeal_of_surjective (stalkLocalizationAtPrimeEquiv w 𝔮).toRingHom
      (stalkLocalizationAtPrimeEquiv w 𝔮).surjective]
  exact map_maximalIdeal_chartStalkToEtaleLocalRing B S hS hX _ _

/-- The map `A_𝔮 → 𝒪_{X, x̄}` is faithfully flat, being flat and local. -/
theorem faithfullyFlat_heightOnePrimeToEtaleLocalRing :
    (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).FaithfullyFlat := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := isLocalRing_etaleLocalRing B S hS X hX
    (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))
  let := (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
  have : Module.Flat _ _ := flat_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  have := isLocalHom_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- `A_𝔮` has Krull dimension one. -/
theorem ringKrullDim_localization_heightOnePrimeOfIdeal :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    ringKrullDim (Localization.AtPrime 𝔮.1) = 1 :=
  ringKrullDim_localization_heightOnePrime (heightOnePrimeOfIdeal B S hS V w 𝔮)

/-- The map `A_𝔮 → 𝒪_{X, x̄}` carries nonzerodivisors to nonzerodivisors. -/
theorem heightOnePrimeToEtaleLocalRing_nonZeroDivisors_le :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    (Localization.AtPrime 𝔮.1)⁰ ≤ ((etaleLocalRing B S hS X
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
        Type (u + 1))⁰).comap (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
  have : Module.Flat _ _ := flat_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  exact fun _ hb ↦ mem_nonZeroDivisors_algebraMap_of_flat hb

/-- The map `Q(A_𝔮) → Q(𝒪_{X, x̄})` induced by `A_𝔮 → 𝒪_{X, x̄}`. -/
abbrev heightOnePrimeToEtaleFractionRing :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    FractionRing (Localization.AtPrime 𝔮.1) →+* FractionRing (etaleLocalRing B S hS X
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
        Type (u + 1)) :=
  letI : 𝔮.1.IsPrime := 𝔮.2.1
  IsLocalization.map _ (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮)
    (heightOnePrimeToEtaleLocalRing_nonZeroDivisors_le B S hS hX V w 𝔮)

/-! ### The reading of a meromorphic function factors through `Q(A_𝔮)` -/

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS ⟨X, hX⟩, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) (hV : IsAffine (chartScheme V))

/-- **The reading of a meromorphic function of `V` in `Q(𝒪_{X, x̄})` factors through
`Q(A_𝔮)`.** For `x̄` over the point `q` cut out by `𝔮`, it is the germ at `w` in `Q(A)`
(`AlgebraicGeometry.Space.chartPointMeromorphicMap`), then the map `Q(A) → Q(A_𝔮)`
(`Stacks.Chow.heightOneFractionMap`), then the map induced by `A_𝔮 → 𝒪_{X, x̄}`. -/
theorem affineChartMeromorphicToEtaleFractionRing_eq_heightOneFractionMap
    (c : (meromorphicFunctionSheaf B S hS X hX).obj.obj (op V)) :
    affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩ hwa hfin
        (chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) hV c =
      heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
        (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)
          (chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
            (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩ hwa hfin V hV) w c)) := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := chartMeromorphicFunctionAlgebra B S hS ⟨X, hX⟩ V
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩ hwa hfin V hV
  refine RingHom.congr_fun (IsLocalization.ringHom_ext ((structurePresheaf B S hS X).obj (op V))⁰
    (S := (meromorphicFunctionSheaf B S hS X hX).obj.obj (op V))
    (j := (affineChartMeromorphicToEtaleFractionRing B S hS ⟨X, hX⟩ hwa hfin
      (chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) hV :
        (meromorphicFunctionSheaf B S hS X hX).obj.obj (op V) →+* _))
    (k := ((heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮).comp
      (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮))).comp
        (chartPointMeromorphicMap B S hS ⟨X, hX⟩ V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩ hwa hfin V hV) w))
    (RingHom.ext fun s ↦ ?_)) c
  have h5 : heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
      (algebraMap ((chartScheme V).presheaf.stalk w) (Localization.AtPrime 𝔮.1)
        ((chartScheme V).presheaf.germ ⊤ w trivial s)) =
      etaleLocalRingGerm B S hS X _
        (op (chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮))) s := by
    refine (heightOnePrimeToEtaleLocalRing_algebraMap B S hS hX V w 𝔮 _).trans ?_
    refine Eq.trans ?_ (chartStalkToEtaleLocalRing_germ B S hS hX _
      (chartPoint_chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) s)
    exact congrArg (chartStalkAtToEtaleLocalRing B S hS hX V
      (intermediatePointOfHeightOnePrime w 𝔮))
      (ConcreteCategory.congr_hom ((chartScheme V).presheaf.germ_stalkSpecializes (U := ⊤) trivial
        (specializes_intermediatePointOfHeightOnePrime w 𝔮)) s)
  have h1 := affineChartMeromorphicToEtaleFractionRing_algebraMap B S hS ⟨X, hX⟩ hwa hfin
    (chartNeighborhoodAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) hV s
  have h2 := chartPointMeromorphicMap_algebraMap B S hS ⟨X, hX⟩ V hV
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS ⟨X, hX⟩ hwa hfin V hV) w s
  have h3 := heightOneFractionMap_algebraMap (heightOnePrimeOfIdeal B S hS V w 𝔮)
    ((chartScheme V).presheaf.germ ⊤ w trivial s)
  have h4 : heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
      (algebraMap (Localization.AtPrime 𝔮.1) (FractionRing (Localization.AtPrime 𝔮.1))
        (algebraMap ((chartScheme V).presheaf.stalk w) (Localization.AtPrime 𝔮.1)
          ((chartScheme V).presheaf.germ ⊤ w trivial s))) =
      algebraMap _ _ (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
        (algebraMap ((chartScheme V).presheaf.stalk w) (Localization.AtPrime 𝔮.1)
          ((chartScheme V).presheaf.germ ⊤ w trivial s))) :=
    IsLocalization.map_eq _ _
  refine h1.trans (Eq.trans ?_ (congrArg (fun z ↦ heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮
    (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) z)) h2).symm)
  refine Eq.trans ?_ (congrArg (heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮) h3).symm
  exact (h4.trans (congrArg (algebraMap _ _) h5)).symm

/-! ### Unit descent and the vanishing of the summand -/

/-- **Unit descent.** A total fraction of `A_𝔮` whose image in `Q(𝒪_{X, x̄})` is the image of
a unit of `𝒪_{X, x̄}` is the image of a unit of `A_𝔮`: the map `A_𝔮 → 𝒪_{X, x̄}` is faithfully
flat. -/
theorem exists_isUnit_eq_algebraMap_of_heightOnePrimeFractionMap_eq
    {x : letI : 𝔮.1.IsPrime := 𝔮.2.1; FractionRing (Localization.AtPrime 𝔮.1)}
    {r : (etaleLocalRing B S hS X
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
        Type (u + 1))} (hr : IsUnit r)
    (hx : heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮 x = algebraMap _ _ r) :
    letI : 𝔮.1.IsPrime := 𝔮.2.1
    ∃ a : Localization.AtPrime 𝔮.1, IsUnit a ∧ x = algebraMap _ _ a := by
  let : 𝔮.1.IsPrime := 𝔮.2.1
  let := (heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮).toAlgebra
  have : Module.FaithfullyFlat (Localization.AtPrime 𝔮.1) (etaleLocalRing B S hS X
      (chartGeometricPointAt B S hS hX V (intermediatePointOfHeightOnePrime w 𝔮)) :
        Type (u + 1)) :=
    faithfullyFlat_heightOnePrimeToEtaleLocalRing B S hS hX V w 𝔮
  exact exists_isUnit_eq_algebraMap_of_isUnit_of_faithfullyFlat
    (heightOnePrimeToEtaleFractionRing B S hS hX V w 𝔮) (fun a ↦ IsLocalization.map_eq _ _) hr hx

variable [IsNoetherianRing ((chartScheme V).presheaf.stalk w)]

omit hX in
/-- **The summand of the Key Lemma at `𝔮` of two units of `A_𝔮` vanishes.** If `f` and `g`
in `Q(A)^*` have images in `Q(A_𝔮)` which are images of units of `A_𝔮`, then the tame symbol
`∂_{A_𝔮}(f, g)` is `1` (Stacks 0EAN, the order of vanishing of a unit being zero), so its order of
vanishing along `A / 𝔮` is zero. -/
theorem heightOneOrd_tameSymbol_eq_zero_of_isUnit
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk w) = 2)
    (f g : (FractionRing ((chartScheme V).presheaf.stalk w))ˣ)
    (hf : ∃ a : (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)ˣ,
      heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) f = algebraMap _ _
        (a : Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
    (hg : ∃ b : (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)ˣ,
      heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮) g = algebraMap _ _
        (b : Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal)) :
    heightOneOrd hdim (heightOnePrimeOfIdeal B S hS V w 𝔮)
      (tameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime
          (heightOnePrimeOfIdeal B S hS V w 𝔮))
        (FractionRing (Localization.AtPrime (heightOnePrimeOfIdeal B S hS V w 𝔮).1.asIdeal))
        (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom f)
        (Units.map (heightOneFractionMap (heightOnePrimeOfIdeal B S hS V w 𝔮)).toMonoidHom g)) = 0
            := by
  set p := heightOnePrimeOfIdeal B S hS V w 𝔮
  set hd := ringKrullDim_localization_heightOnePrime p
  have := krullDimLE_one_of_ringKrullDim_eq_one hd
  have : Nontrivial (Localization.AtPrime p.1.asIdeal) := by
    rw [← zero_le_ringKrullDim_iff_nontrivial, hd]
    norm_num
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have hfa : Units.map (heightOneFractionMap p).toMonoidHom f =
      Units.map (algebraMap (Localization.AtPrime p.1.asIdeal)
        (FractionRing (Localization.AtPrime p.1.asIdeal))).toMonoidHom a :=
    Units.ext ha
  have hsymb : tameSymbolOfKrullDimOne hd (FractionRing (Localization.AtPrime p.1.asIdeal))
      (Units.map (heightOneFractionMap p).toMonoidHom f)
      (Units.map (heightOneFractionMap p).toMonoidHom g) = 1 := by
    rw [hfa]
    refine (RegularTameSymbol.extend_unit_left (regularTameSymbolOfKrullDimOne hd) _ a _).trans ?_
    have hord : Ring.ordTotalFracInt (Localization.AtPrime p.1.asIdeal)
        ((Units.map (heightOneFractionMap p).toMonoidHom g :
          (FractionRing (Localization.AtPrime p.1.asIdeal))ˣ) :
            FractionRing (Localization.AtPrime p.1.asIdeal)) (Units.isUnit _) = 0 := by
      have hgv : ((Units.map (heightOneFractionMap p).toMonoidHom g :
          (FractionRing (Localization.AtPrime p.1.asIdeal))ˣ) :
            FractionRing (Localization.AtPrime p.1.asIdeal)) =
          algebraMap _ _ (b : Localization.AtPrime p.1.asIdeal) := hb
      rw [Ring.ordTotalFracInt_congr _ (Units.isUnit _) (hgv ▸ Units.isUnit _) hgv]
      exact Ring.ordTotalFracInt_algebraMap_of_isUnit b.isUnit _
    rw [hord, zpow_zero]
  rw [hsymb, heightOneOrd_one]

end AlgebraicGeometry.Space

end
