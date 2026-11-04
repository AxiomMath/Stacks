module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatCartesianOfChartSquare
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveChartThickeningFlat
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveClassComparison

/-!
# The thickening realizing an extension is flat over `k[ε]`, with closed fibre `X`

Let `X ⊂ X'` be the thickening realizing an extension `P` of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by
`𝒪_X ⊗_k k` (`Deformation.Examples.spaceSurjAmbient`), with its morphism `g : X' ⟶ Spec k[ε]`
(`Deformation.Examples.spaceSurjToDual`). On the presenting chart `U` of `X`, the chart thickening
`U'` is an extension of `𝒪_U` by `𝒪_U · e`, `e = 1 ⊗ 1`, and `ε` pulls back to `e`; so
`U' ⟶ Spec k[ε]` is flat with `U = Spec k ×_{Spec k[ε]} U'`
(`AlgebraicGeometry.Space.SquareZeroExtension.flat_and_isPullback_of_generator`). Since `U' ⟶ X'`
is a surjective étale chart, `g` is flat and `X = Spec k ×_{Spec k[ε]} X'`
(`AlgebraicGeometry.Space.isFlat_and_isPullback_of_chartSquare`). So `(X' ⟶ Spec k[ε], X ⟶ X')` is
a deformation of `X` over the dual numbers.

## Main results

* `Deformation.Examples.isFlat_and_isPullback_spaceSurjToDual`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space AlgebraicGeometry.Space.SquareZeroExtension
open Deformation.AlgebraExtension CategoryTheory.Sheaf Deformation.Artin

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable (Λ k) in
/-- `k[ε] = TrivSqZeroExt k k` is the dual numbers object of `𝒞_Λ`. -/
def dualNumbersRingEquiv :
    TrivSqZeroExt k k ≃+* spaceDualNumbers (Λ := Λ) (k := k) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    refine TrivSqZeroExt.ext rfl ?_
    change x.fst * y.snd + x.snd * y.fst = x.fst * y.snd + y.fst * x.snd
    rw [mul_comm x.snd y.fst]

/-- `k[ε] ≅ Γ(Spec k[ε], 𝒪)`. -/
abbrev spaceDualEquiv :
    TrivSqZeroExt k k ≃+* baseRing B (Spec (.of Λ)) hΛ
      (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))) :=
  (dualNumbersRingEquiv Λ k).trans (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _)

/-- `Spec k ⊆ Spec k[ε]` is cut out by `ε`. -/
theorem spaceDualImmersion_appTop_eq_zero_iff (a : TrivSqZeroExt k k) :
    (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)).appTop).hom
        (spaceDualEquiv B hΛ hSpec a) = 0 ↔ a.fst = 0 := by
  have h := Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv B hΛ hSpec (spaceDualResidue Λ k)
    (dualNumbersRingEquiv Λ k a)
  refine (iff_of_eq (congrArg (· = 0) h)).trans ?_
  rw [map_eq_zero_iff _ (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _).injective]
  have hr : (spaceDualResidue Λ k).hom.toRingHom = residueMap _ :=
    hom_residueFieldBase_eq_residueMap _
  have h2 : (spaceDualResidue Λ k).hom (dualNumbersRingEquiv Λ k a) = a.fst :=
    (congrArg (fun φ : spaceDualNumbers (Λ := Λ) (k := k) →+* k => φ (dualNumbersRingEquiv Λ k a))
      hr).trans rfl
  rw [h2]

/-- `Spec k[ε]` has a single point. -/
instance subsingleton_spaceDualNumbers :
    Subsingleton ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)))) := by
  change Subsingleton (PrimeSpectrum (spaceDualNumbers (Λ := Λ) (k := k)))
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  have hp : p.asIdeal.IsMaximal := inferInstance
  have hq : q.asIdeal.IsMaximal := inferInstance
  exact (IsLocalRing.eq_maximalIdeal hp).trans (IsLocalRing.eq_maximalIdeal hq).symm

variable (k) in
/-- Ring maps out of the dual numbers agree when they agree on `k` and on `ε`. -/
theorem dualNumbers_ringHom_ext {R : Type*} [Semiring R] {φ ψ : TrivSqZeroExt k k →+* R}
    (h1 : ∀ a, φ (TrivSqZeroExt.inl a) = ψ (TrivSqZeroExt.inl a))
    (h2 : φ (TrivSqZeroExt.inr 1) = ψ (TrivSqZeroExt.inr 1)) : φ = ψ := by
  ext x
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
    rw [TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]
    exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  rw [hx, map_add, map_add, map_mul, map_mul, h1, h1, h2]

variable (P : AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
  (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
  (spaceRankOneCoefficient B hΛ hSpec X hX toK))

/-- Abbreviation for the square-zero extension `spaceSurjExtension`. -/
local notation "E" => spaceSurjExtension B hΛ hSpec X hX toK P
/-- Abbreviation for the presentation. -/
local notation "Pp" => spaceSurjPresentation B hΛ hSpec X hX toK
/-- Abbreviation for the containment of the chart thickening. -/
local notation "hU" => contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _
/-- Abbreviation for the presenting chart. -/
local notation "Wc" =>
  presentationChart (X := spaceOf B hΛ X hX) (spaceSurjPresentation B hΛ hSpec X hX toK)

/-- **The chart `U' ⟶ Spec k[ε]`** of `X' ⟶ Spec k[ε]` on the chart thickening `U'` of the
presenting chart. -/
def spaceSurjChartToDual :
    (E).chartRealizedSchemeOver hΛ Wc hU ⟶
      spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)) :=
  yoneda.preimage ((E).thickeningQuotientMap Pp hU hU ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom)

/-- The image under Yoneda of `U' ⟶ Spec k[ε]` is `U' ⟶ X' ⟶ Spec k[ε]`. -/
theorem yoneda_map_spaceSurjChartToDual :
    yoneda.map (spaceSurjChartToDual B hΛ hSpec X hX toK P) =
      (E).thickeningQuotientMap Pp hU hU ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom :=
  yoneda.map_preimage _

/-- The presenting chart, as a chart over itself. -/
abbrev spaceSurjOverChart : OverPresentation (X := spaceOf B hΛ X hX) Pp := ⟨Wc, ⟨𝟙 _⟩⟩

/-- The thickened chart of the presenting chart is `U' ⟶ X'`. -/
theorem spaceSurjThickenedChart_hom :
    (((E).thickenedChartFunctor Pp hU hU).obj (spaceSurjOverChart B hΛ hSpec X hX toK)).obj.hom =
      (E).thickeningQuotientMap Pp hU hU := by
  refine ((E).thickenedChartHom_eq Pp hU hU _ (𝟙 _)).trans ?_
  refine (congrArg (· ≫ (E).thickeningQuotientMap Pp hU hU)
    ((congrArg yoneda.map ((E).chartRealizedSchemeOverMap_id _ hU)).trans
      (yoneda.map_id _))).trans ?_
  exact Category.id_comp _

/-- **`ε` pulls back to `e = 1 ⊗ 1` on the chart thickening `U'`.** -/
theorem spaceSurjChartToDual_appTop :
    ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P)).appTop.hom
        (spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inr 1)) =
      ((E).chartRealizedSchemeΓIso Wc).hom
        ((E).ι (op Wc)
          ((spaceRankOneSection B hΛ hSpec X hX toK).val.app (op Wc)
            (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj
              (op Wc)))) := by
  let V := ((E).thickenedChartFunctor Pp hU hU).obj (spaceSurjOverChart B hΛ hSpec X hX toK)
  have hpre : yoneda.preimage (V.obj.hom ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom) =
      spaceSurjChartToDual B hΛ hSpec X hX toK P :=
    congrArg (fun m => yoneda.preimage (m ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom))
      (spaceSurjThickenedChart_hom B hΛ hSpec X hX toK P)
  have h1 : (globalFunctionsOfMap (spaceSurjToDual B hΛ hSpec X hX toK P)
      (spaceDualEps B hΛ hSpec)).1 (op V) =
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (yoneda.preimage (V.obj.hom ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom))).appTop.hom
        (spaceDualEps B hΛ hSpec) := rfl
  have h2 := congrArg (fun m : (E).chartRealizedSchemeOver hΛ Wc hU ⟶
      spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)) =>
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map m).appTop.hom
    (spaceDualEps B hΛ hSpec)) hpre
  show ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
    (spaceSurjChartToDual B hΛ hSpec X hX toK P)).appTop.hom (spaceDualEps B hΛ hSpec) = _
  refine h2.symm.trans (h1.symm.trans ?_)
  refine (globalFunctionsOfMap_spaceSurjToDual_val B hΛ hSpec X hX toK P (op V)).trans ?_
  refine (globalFunctionsOfSection_apply (spaceSurjEpsSet B hΛ hSpec X hX toK P) (op V)
    default).trans ?_
  exact (E).app_eq_of_globalSectionMap_comp_quotientSheafIso_hom Pp hU hU _ _
    (globalSectionMap_spaceSurjEpsSet B hΛ hSpec X hX toK P)
    (spaceSurjOverChart B hΛ hSpec X hX toK) default default

/-- The atlas of `X` to `Spec k`. -/
abbrev spaceSurjChartToBase :
    (spaceSurjPresentation B hΛ hSpec X hX toK).U ⟶
      spaceBaseOver B hΛ hSpec (residueFieldBase Λ k) :=
  yoneda.preimage ((spaceSurjPresentation B hΛ hSpec X hX toK).toSpace ≫ toK)

/-- `U ⟶ U' ⟶ Spec k[ε] ⟶ Spec k` is `U ⟶ Spec k`. -/
theorem spaceSurjChart_comp_retraction :
    (E).chartInclusionOver Wc hU ≫ spaceSurjChartToDual B hΛ hSpec X hX toK P ≫
        spaceDualRetraction B hΛ hSpec = spaceSurjChartToBase B hΛ hSpec X hX toK := by
  refine yoneda.map_injective ?_
  refine Eq.trans ?_
    (yoneda.map_preimage ((spaceSurjPresentation B hΛ hSpec X hX toK).toSpace ≫ toK)).symm
  rw [yoneda.map_comp, yoneda.map_comp, yoneda_map_spaceSurjChartToDual]
  have hg : (spaceSurjToDual B hΛ hSpec X hX toK P).hom ≫
      yoneda.map (spaceDualRetraction B hΛ hSpec) =
      (spaceSurjToBase B hΛ hSpec X hX toK P).hom :=
    congrArg (fun m => m.hom) (spaceSurjToDual_comp B hΛ hSpec X hX toK P)
  have hi : (spaceSurjImmersion B hΛ hSpec X hX toK P).hom ≫
      (spaceSurjToBase B hΛ hSpec X hX toK P).hom = toK :=
    congrArg (fun m => m.hom) (spaceSurjImmersion_comp_toBase B hΛ hSpec X hX toK P)
  have hw := ((E).isPullback_thickeningImmersion Pp hU hU).w
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hg))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hw.symm).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hi)

/-- `Spec k ⟶ Spec k[ε] ⟶ Spec k` is the identity. -/
theorem spaceDualImmersion_comp_retraction :
    spaceDualImmersion B hΛ hSpec ≫ spaceDualRetraction B hΛ hSpec = 𝟙 _ := by
  refine (spaceBaseOverMap_comp B hΛ hSpec _ _).symm.trans ?_
  exact (congrArg (spaceBaseOverMap B hΛ hSpec) (isTerminal_residueFieldBase.hom_ext _ _)).trans
    (spaceBaseOverMap_id B hΛ hSpec _)

/-- **`U ⟶ U' ⟶ Spec k[ε]` factors through `Spec k`**, as morphisms of schemes. -/
theorem spaceSurjChart_comm :
    (E).chartInclusion Wc ≫ (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P) =
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceSurjChartToBase B hΛ hSpec X hX toK) ≫
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec) := by
  have := isAffine_toScheme_spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))
  have hL : (E).chartInclusion Wc ≫ (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P) ≫
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualRetraction B hΛ hSpec) =
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToBase B hΛ hSpec X hX toK) := by
    refine (congrArg (· ≫ _) ((E).toScheme_map_chartInclusionOver Wc hU).symm).trans ?_
    refine (congrArg (_ ≫ ·)
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_comp _ _).symm).trans ?_
    refine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_comp _ _).symm.trans ?_
    exact congrArg (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceSurjChart_comp_retraction B hΛ hSpec X hX toK P)
  have hR : (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToBase B hΛ hSpec X hX toK) ≫
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec) ≫
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualRetraction B hΛ hSpec) =
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToBase B hΛ hSpec X hX toK) := by
    refine (congrArg (_ ≫ ·)
      (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_comp _ _).symm.trans
      ((congrArg (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceDualImmersion_comp_retraction B hΛ hSpec)).trans
        ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_id _)))).trans ?_
    exact Category.comp_id _
  refine ext_of_isAffine ?_
  refine CommRingCat.hom_ext ?_
  have key := dualNumbers_ringHom_ext k
    (φ := (((E).chartInclusion Wc ≫ (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P)).appTop.hom).comp
      (spaceDualEquiv B hΛ hSpec).toRingHom)
    (ψ := (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToBase B hΛ hSpec X hX toK) ≫
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceDualImmersion B hΛ hSpec)).appTop.hom).comp
        (spaceDualEquiv B hΛ hSpec).toRingHom)
    (fun a => ?_) ?_
  · ext x
    obtain ⟨a, rfl⟩ := (spaceDualEquiv B hΛ hSpec).surjective x
    exact DFunLike.congr_fun key a
  · have hinl : spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inl a) =
        (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceDualRetraction B hΛ hSpec)).op).hom
          (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k) a) :=
      (DFunLike.congr_fun (spaceConstants_Γ_comp Λ B hΛ hSpec (FGModuleCat.of k k)) a).symm
    show ((E).chartInclusion Wc ≫ (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P)).appTop.hom
      (spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inl a)) =
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceSurjChartToBase B hΛ hSpec X hX toK) ≫
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)).appTop.hom
          (spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inl a))
    rw [hinl]
    show (((E).chartInclusion Wc ≫ (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P)) ≫
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceDualRetraction B hΛ hSpec)).appTop.hom _ =
      (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToBase B hΛ hSpec X hX toK) ≫
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)) ≫
        (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceDualRetraction B hΛ hSpec)).appTop.hom _
    exact congrArg (fun m => (Scheme.Hom.appTop m).hom _)
      (((Category.assoc _ _ _).trans hL).trans ((Category.assoc _ _ _).trans hR).symm)
  · show ((E).chartInclusion Wc).appTop.hom (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToDual B hΛ hSpec X hX toK P)).appTop.hom
        (spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inr 1))) =
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToBase B hΛ hSpec X hX toK)).appTop.hom
        (((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)).appTop.hom
          (spaceDualEquiv B hΛ hSpec (TrivSqZeroExt.inr 1)))
    rw [spaceSurjChartToDual_appTop, (E).chartInclusion_appTop_chartRealizedSchemeΓIso,
      ((spaceDualImmersion_appTop_eq_zero_iff B hΛ hSpec _).2 rfl), map_zero]
    exact (E).mem_kernel _ _

omit P in
/-- `Spec k ⟶ Spec k[ε]` is a closed immersion. -/
theorem isClosedImmersion_spaceDualImmersion :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)) :=
  (isSquareZeroClosedImmersion_spaceBaseOverMap B hΛ hSpec (spaceDualResidue Λ k)
    (maximalIdeal_sq_squareZeroExtensionArtinian (FGModuleCat.of k k))).1

/-- **`U' ⟶ Spec k[ε]` is flat and `U = Spec k ×_{Spec k[ε]} U'`.** -/
theorem spaceSurjChart_flat_and_isPullback :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceSurjChartToDual B hΛ hSpec X hX toK P)) ∧
      IsPullback ((E).chartInclusion Wc)
        ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceSurjChartToBase B hΛ hSpec X hX toK))
        ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceSurjChartToDual B hΛ hSpec X hX toK P))
        ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)) :=
  have := isClosedImmersion_spaceDualImmersion B hΛ hSpec
  (E).flat_and_isPullback_of_generator Wc (spaceRankOneSection B hΛ hSpec X hX toK)
    (spaceRankOneSectionInv B hΛ hSpec X hX toK) (spaceRankOneSection_comp_inv B hΛ hSpec X hX toK)
    (spaceRankOneSectionInv_comp B hΛ hSpec X hX toK) _ _ _
    (spaceSurjChart_comm B hΛ hSpec X hX toK P) (spaceDualEquiv B hΛ hSpec)
    (spaceDualImmersion_appTop_eq_zero_iff B hΛ hSpec)
    (spaceSurjChartToDual_appTop B hΛ hSpec X hX toK P)

/-- **`X ⟶ X' ⟶ Spec k[ε]` factors through `Spec k`.** -/
theorem spaceSurjImmersion_comp_toDual :
    (spaceSurjImmersion B hΛ hSpec X hX toK P).hom ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom =
      toK ≫ yoneda.map (spaceDualImmersion B hΛ hSpec) := by
  have hc : (E).chartInclusionOver Wc hU ≫ spaceSurjChartToDual B hΛ hSpec X hX toK P =
      spaceSurjChartToBase B hΛ hSpec X hX toK ≫ spaceDualImmersion B hΛ hSpec := by
    refine BigFppfOver.map_toScheme_injective B (Spec (.of Λ)) hΛ ?_
    refine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_comp _ _).trans ?_
    refine (congrArg (· ≫ _) ((E).toScheme_map_chartInclusionOver Wc hU)).trans ?_
    exact (spaceSurjChart_comm B hΛ hSpec X hX toK P).trans
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map_comp _ _).symm
  refine presentation_toSpace_hom_ext (spaceSurjPresentation B hΛ hSpec X hX toK)
    (isAlgebraicSpace_yoneda B (Spec (.of Λ)) hΛ _).isSheaf ?_
  have hw := ((E).isPullback_thickeningImmersion Pp hU hU).w
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hw).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (yoneda_map_spaceSurjChartToDual B hΛ hSpec X hX toK P).symm).trans ?_
  refine (yoneda.map_comp _ _).symm.trans ?_
  refine (congrArg yoneda.map hc).trans ?_
  refine (yoneda.map_comp _ _).trans ?_
  refine (congrArg (· ≫ _) (yoneda.map_preimage _)).trans ?_
  exact Category.assoc _ _ _

/-- **`X' ⟶ Spec k[ε]` is flat and `X = Spec k ×_{Spec k[ε]} X'`.** -/
theorem isFlat_and_isPullback_spaceSurjToDual :
    Space.IsFlat B (Spec (.of Λ)) hΛ (spaceSurjToDual B hΛ hSpec X hX toK P).hom ∧
      IsPullback (spaceSurjImmersion B hΛ hSpec X hX toK P).hom toK
        (spaceSurjToDual B hΛ hSpec X hX toK P).hom
        (yoneda.map (spaceDualImmersion B hΛ hSpec)) := by
  have hic :
      Space.IsClosedImmersion B (Spec (.of Λ)) hΛ (spaceSurjImmersion B hΛ hSpec X hX toK P).hom :=
    (E).isClosedImmersion_thickeningImmersion Pp hU hU
  have : Mono (spaceSurjImmersion B hΛ hSpec X hX toK P).hom :=
    mono_of_isClosedImmersion B (Spec (.of Λ)) hΛ _ hic
  have ht := isClosedImmersion_spaceDualImmersion B hΛ hSpec
  let Xs : ClosedSubspaces B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P).1 :=
    ⟨Subfunctor.range (spaceSurjImmersion B hΛ hSpec X hX toK P).hom,
      isClosedSubspace_range_of_isClosedImmersion B (Spec (.of Λ)) hΛ _ hX hic⟩
  let Ys : ClosedSubspaces B (Spec (.of Λ)) hΛ
      (schemeSpace (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)))).1 :=
    closedSubspaceRange B (Spec (.of Λ)) hΛ (spaceDualImmersion B hΛ hSpec) ht
  let eX : X ≅ (Subfunctor.range (spaceSurjImmersion B hΛ hSpec X hX toK P).hom).toFunctor :=
    asIso (Subfunctor.toRange (spaceSurjImmersion B hΛ hSpec X hX toK P).hom)
  let eY := rangeIsoPresheaf B (Spec (.of Λ)) hΛ (spaceDualImmersion B hΛ hSpec) ht
  have hXι : eX.inv ≫ (spaceSurjImmersion B hΛ hSpec X hX toK P).hom = Xs.1.ι := by
    rw [Iso.inv_comp_eq]
    exact (Subfunctor.toRange_ι _).symm
  have hYι : eY.hom ≫ Ys.1.ι = yoneda.map (spaceDualImmersion B hΛ hSpec) :=
    Subfunctor.toRange_ι _
  let f : (⟨Xs.1.toFunctor, Xs.2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ⟶
      ⟨Ys.1.toFunctor, Ys.2.1⟩ := ObjectProperty.homMk (eX.inv ≫ toK ≫ eY.hom)
  have hsq : subspaceInclusion B (Spec (.of Λ)) hΛ _ Xs ≫ spaceSurjToDual B hΛ hSpec X hX toK P =
      f ≫ subspaceInclusion B (Spec (.of Λ)) hΛ _ Ys := by
    refine ObjectProperty.hom_ext _ ?_
    show Xs.1.ι ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom = (eX.inv ≫ toK ≫ eY.hom) ≫ Ys.1.ι
    rw [← hXι, Category.assoc, spaceSurjImmersion_comp_toDual]
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm
    exact congrArg (fun m => eX.inv ≫ toK ≫ m) hYι.symm
  have hα : (E).thickeningQuotientMap Pp hU hU ≫ (spaceSurjToDual B hΛ hSpec X hX toK P).hom =
      yoneda.map (spaceSurjChartToDual B hΛ hSpec X hX toK P) ≫
        yoneda.map (𝟙 (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)))) := by
    rw [yoneda.map_id, Category.comp_id, yoneda_map_spaceSurjChartToDual]
  have hpU : IsPullback ((spaceSurjPresentation B hΛ hSpec X hX toK).toSpace ≫ eX.hom)
      (yoneda.map ((E).chartInclusionOver Wc hU)) Xs.1.ι ((E).thickeningQuotientMap Pp hU hU) :=
    ((E).isPullback_thickeningImmersion Pp hU hU).of_iso (Iso.refl _) eX (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by rw [← hXι]; simp) (by simp)
  have hpV : IsPullback eY.hom (yoneda.map (spaceDualImmersion B hΛ hSpec)) Ys.1.ι
      (yoneda.map (𝟙 (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))))) := by
    rw [yoneda.map_id]
    exact (IsPullback.id_horiz (yoneda.map (spaceDualImmersion B hΛ hSpec))).of_iso (Iso.refl _) eY
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) ((Category.comp_id _).trans hYι.symm) (by simp)
  have hb'E : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ)).presheaf
        (yoneda.map (𝟙 (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))))) :=
    (presheaf_yoneda_map_iff B (Spec (.of Λ)) hΛ inferInstance _).mpr
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  obtain ⟨hflatα, hpbS⟩ := spaceSurjChart_flat_and_isPullback B hΛ hSpec X hX toK P
  have hpb : IsPullback
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map ((E).chartInclusionOver Wc hU))
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceSurjChartToBase B hΛ hSpec X hX toK))
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceSurjChartToDual B hΛ hSpec X hX toK P))
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceDualImmersion B hΛ hSpec)) := by
    rwa [(E).toScheme_map_chartInclusionOver Wc hU]
  obtain ⟨hflat, hcart⟩ := isFlat_and_isPullback_of_chartSquare B (Spec (.of Λ)) hΛ Xs Ys
    (spaceSurjToDual B hΛ hSpec X hX toK P) f hsq ((E).thickeningQuotientMap Pp hU hU)
    (yoneda.map (𝟙 _)) (spaceSurjChartToDual B hΛ hSpec X hX toK P)
    ((E).chartInclusionOver Wc hU) (spaceDualImmersion B hΛ hSpec)
    (spaceSurjChartToBase B hΛ hSpec X hX toK)
    ((spaceSurjPresentation B hΛ hSpec X hX toK).toSpace ≫ eX.hom) eY.hom
    (quotientMap_surjective_unconditional B (Spec (.of Λ)) hΛ _ _)
    (quotientMap_etale_unconditional B (Spec (.of Λ)) hΛ _ _) hb'E hα hpU hpV hflatα hpb
  refine ⟨hflat, ?_⟩
  have hc := AlgebraicSpaces.isPullback_hom B (Spec (.of Λ)) hΛ hcart
  exact hc.of_iso eX.symm (Iso.refl _) eY.symm (Iso.refl _) ((Category.comp_id _).trans hXι.symm)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) eY.hom_inv_id).trans (Category.comp_id _)))))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans ((Iso.eq_inv_comp eY).mpr hYι))

end Deformation.Examples

end
