module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Quot.ProperSupportAlongProper
public import StacksFrontier.AlgebraicGeometry.Quot.QuotValuativeAffineChart
public import StacksFrontier.AlgebraicGeometry.Quot.QuotValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleOfChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSectionsUnitAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria

/-!
# The existence part of the valuative criterion for the Quot functor (Stacks 0DM4)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
proper and of finite presentation, and let `F` be a quasi-coherent `𝒪_X`-module of finite type.
Stacks 0DM4 asserts that `Quot_{F/X/B} ⟶ B` satisfies the existence part of the valuative
criterion (Stacks 03IX).

A valuative square for `Quot_{F/X/B} ⟶ B` is a valuation ring `R` with fraction field `K`, a
morphism `Spec R ⟶ B` and a quotient `F_K ⟶ Q_K` over `X_K = X ×_B Spec K` lying over the
composite `Spec K ⟶ Spec R ⟶ B`.  A lift is a quotient `F_R ⟶ Q` in `Quot_{F/X/B}(Spec R)`
pulling back to `Q_K`.  With `j : X_K ⟶ X_R` the inclusion of the generic fibre, the lift is the
image of the adjoint transpose `F_R ⟶ j_*Q_K` of `j^*F_R = F_K ⟶ Q_K`
(`AlgebraicGeometry.Space.QuotSituation.extensionKernel`); on an affine chart `Spec A` of `X_R`,
with `F_R` given by `M`, it is the quotient of `M` by `{x ∈ M | x ⊗ 1 ↦ 0 in Q_K}`.  Then:

* it pulls back to `Q_K`, because `j` is flat and the counit `j^*j_*Q_K ⟶ Q_K` is invertible,
  `j` being an affine monomorphism (Stacks 07U8);
* it is quasi-coherent, as an image of a morphism of quasi-coherent modules, and of finite type,
  as a quotient of `F_R`;
* it is flat over `R`: it embeds into `j_*Q_K`, on which every nonzero element of `R` acts
  injectively since it becomes a unit on `X_K`, so its sections over an affine chart are torsion
  free and hence flat over the valuation ring `R` (Stacks 0539);
* it is of finite presentation, being flat and of finite type over `R` with `X_R ⟶ Spec R` of
  finite presentation (Stacks 0DLR);
* its support is proper over `R`, being closed in `X_R`, which is proper over `R`.

So every valuative square has a lift, with no extension of the valuation ring.

## Main results

* `AlgebraicGeometry.Space.QuotSitePresheafModel.valuativeCriterionExistence_toBase`:
  **Stacks 0DM4** — for every model of the Quot presheaf, its canonical morphism to `B`
  satisfies the existence part of the valuative criterion.
* `AlgebraicGeometry.Space.QuotSituation.exists_quotFamilyOver_baseChange_eq`: a quotient over
  the fraction field of a valuation ring extends over the valuation ring.
* `AlgebraicGeometry.Space.QuotSituation`'s
  `exists_mem_properlySupportedQuotients_quotientPullback_eq`: the same, on the quotients of `F_R`
  and `F_K`.
* `AlgebraicGeometry.Space.QuotSituation.isFlatOver_quotientModule_extensionKernel`: the extended
  quotient is flat over `R`.
* `AlgebraicGeometry.Space.QuotSitePresheafModel`'s
  `valuativeCriterionExistence_toBase_of_forall_exists_baseChange_eq`: the reduction of the
  existence part of the valuative criterion for a model of the Quot presheaf to the extension of
  quotients over valuation rings.

## Implementation notes

`Quot_{F/X/B}` is `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`, a presheaf of
`Type (u + 1)` on the big fppf site, together with its morphism to the universe lift of `B`.
The existence part of the valuative criterion of Stacks 03IX,
`AlgebraicGeometry.Space.ValuativeCriterion.Existence`, is stated for morphisms of presheaves of
`Type u`, so it is asserted of the canonical morphism to `B` of every model of the Quot presheaf
in `Type u` (`AlgebraicGeometry.Space.QuotSitePresheafModel`); such a model exists by the size
clause of Stacks 09TU, and the statement is the same for any two models.

The standing data `AlgebraicGeometry.Space.QuotSituation` records `f`, its finite presentation
and the quasi-coherent module `F`; properness of `f` and finite type of `F` are separate
hypotheses.

## References

* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (N : QuotSitePresheafModel D)

/-- **The existence part of the valuative criterion for a model of the Quot presheaf, from the
extension of quotients over valuation rings.**  If every quotient over the fraction field of a
valuation ring `R`, lying over a morphism `Spec K ⟶ B` that factors through `Spec R`, is the
base change of a quotient over `Spec R` lying over the given morphism `Spec R ⟶ B`, then the
canonical morphism of any model of the Quot presheaf to `B` satisfies the existence part of the
valuative criterion, with no extension of the valuation ring needed. -/
theorem valuativeCriterionExistence_toBase_of_forall_exists_baseChange_eq
    (hext : ∀ (q : ValuativeSquare N.toBase)
      (x : QuotFamilyOver D (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))),
      x.toBase = (schemeSpaceFunctor B S hS).map q.fracHom ≫ ObjectProperty.homMk q.special →
      ∃ y : QuotFamilyOver D (siteObject B S hS q.ring_mem q.base),
        y.toBase = ObjectProperty.homMk q.special ∧ y.baseChange q.fracHom = x) :
    ValuativeCriterion.Existence N.toBase := by
  refine valuativeCriterionExistence_of_forall_nonempty_lift _ fun q => ?_
  let z := yonedaEquiv q.generic
  let x : QuotFamilyOver D _ := N.iso.hom.app _ ⟨z⟩
  have hx : x.toBase = (schemeSpaceFunctor B S hS).map q.fracHom ≫
      ObjectProperty.homMk q.special := by
    refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
    show (D.quotSitePresheafToBase.app _ x).down = _
    refine (yonedaEquiv_comp q.generic N.toBase).symm.trans ?_
    rw [q.comm]
    rfl
  obtain ⟨y, hy, hyx⟩ := hext q x hx
  let w := (N.iso.inv.app _ y).down
  refine ⟨⟨yonedaEquiv.symm w, ?_, ?_⟩⟩
  · rw [yonedaEquiv_symm_naturality_left]
    refine yonedaEquiv.symm_apply_eq.mpr ?_
    have hnat := types_congr_hom (N.iso.inv.naturality q.fracHom.op) y
    change N.iso.inv.app _ (y.baseChange q.fracHom) = ULift.up (N.presheaf.map q.fracHom.op w)
      at hnat
    rw [hyx] at hnat
    have hz : N.iso.inv.app _ x = ⟨z⟩ := by
      show (N.iso.hom ≫ N.iso.inv).app _ ⟨z⟩ = _
      rw [Iso.hom_inv_id]
      rfl
    exact congrArg ULift.down (hnat.symm.trans hz)
  · rw [yonedaEquiv_symm_naturality_right]
    refine yonedaEquiv.symm_apply_eq.mpr ?_
    show (D.quotSitePresheafToBase.app _ (N.iso.hom.app _ ⟨w⟩)).down = _
    have hw : N.iso.hom.app _ ⟨w⟩ = y := by
      show (N.iso.inv ≫ N.iso.hom).app _ y = y
      rw [Iso.inv_hom_id]
      rfl
    rw [hw]
    show yonedaEquiv y.toBase.hom = _
    rw [hy]
    rfl

end QuotSitePresheafModel

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) (R K : Type u) [CommRing R] [Field K] [Algebra R K]
  (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) (b : Spec (.of R) ⟶ S)

/-- The morphism `Spec K ⟶ Spec R` of the big fppf site of a valuation ring and its fraction
field. -/
abbrev genericPoint :
    siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
      siteObject B S hS hR b :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    B.obj hK ⟶ B.obj hR)

variable {R K hR b}
variable (a : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hR b) ⟶ D.Y)

/-- The morphism `h : T' ⟶ T` of test schemes over `B` lying over `Spec K ⟶ Spec R`. -/
abbrev genericPointRestrict := QuotFamilyOver.restrict (genericPoint R K hR hK b) a

/-- The morphism `T' ⟶ T` of test schemes lies over `Spec K ⟶ Spec R`. -/
theorem isHomLift_genericPointRestrict :
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).IsHomLift
      (genericPoint R K hR hK b) (D.genericPointRestrict hK a) :=
  Functor.IsHomLift.map (p := CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)
    (D.genericPointRestrict hK a)

/-- The inclusion `X_K ⟶ X_R` of the generic fibre is affine. -/
private theorem isAffineHom_relativeMap_genericPointRestrict :
    IsAffineHom B S hS (D.relativeMap (D.genericPointRestrict hK a)).hom :=
  isAffineHom_baseChangeMap_of_isHomLift (hR := hR) (hA := hK) (b := b) D.f R K _
    (D.isHomLift_genericPointRestrict hK a)

/-- The extension of a quasi-coherent quotient over the generic fibre is quasi-coherent. -/
private theorem isQuasicoherentOnSite_extensionKernel_genericPointRestrict
    (K' : Subobject (D.baseChangeModule (CostructuredArrow.mk
      ((schemeSpaceFunctor B S hS).map (genericPoint R K hR hK b) ≫ a))))
    (hQ : (D.quotientModule _ K').IsQuasicoherentOnSite) :
    (D.quotientModule _
      (D.extensionKernel (D.genericPointRestrict hK a) K')).IsQuasicoherentOnSite :=
  D.isQuasicoherentOnSite_quotientModule_extensionKernel _ K'
    (isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS _
      (D.isAffineHom_relativeMap_genericPointRestrict hK a) _ hQ)

variable [IsFractionRing R K]

/-- The inverse image along the inclusion `X_K ⟶ X_R` of the generic fibre preserves
monomorphisms. -/
instance preservesMonomorphisms_modulePullback_relativeMap_genericPointRestrict :
    (modulePullback B S hS (D.relativeMap (D.genericPointRestrict hK a))).PreservesMonomorphisms :=
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS _
    (isFlat_baseChangeMap_of_isHomLift (hR := hR) (hA := hK) (b := b) D.f R K _
      (D.isHomLift_genericPointRestrict hK a))
  inferInstance

/-- **Every nonzero element of `R` becomes a unit on the generic fibre.**  For an affine étale
chart `U` of `X_R` with structure morphism `α : U ⟶ Spec R`, and a chart `W` of `X_K` above it,
the pullback to `W` of the image of `r ≠ 0` in the regular functions on `U` is a unit. -/
theorem isUnit_chartDiagramPullback_genericPoint (U : SmallEtale B S hS (D.space
      (CostructuredArrow.mk a)).1)
    (α : (SmallEtale.toOver B S hS _).obj U ⟶ siteObject B S hS hR b)
    (hα : U.1.hom ≫ (D.projection (CostructuredArrow.mk a)).hom = yoneda.map α)
    (W : SmallEtale B S hS (D.space (CostructuredArrow.mk
      ((schemeSpaceFunctor B S hS).map (genericPoint R K hR hK b) ≫ a))).1)
    (c : (SmallEtale.toOver B S hS _).obj W ⟶ (SmallEtale.toOver B S hS _).obj U)
    (hc : W.1.hom ≫ (D.relativeMap (D.genericPointRestrict hK a)).hom = yoneda.map c ≫ U.1.hom)
    {r : R} (hr : r ≠ 0) :
    IsUnit (chartDiagramPullback B S hS (D.relativeMap (D.genericPointRestrict hK a))
      ⟨W, U, c, hc⟩ (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        ((BigFppfOver.toScheme B S hS).map α).appTop).hom r)) := by
  obtain ⟨αW, hαW⟩ : ∃ αW : (SmallEtale.toOver B S hS _).obj W ⟶ siteObject B S hS hK
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b),
      W.1.hom ≫ (D.projection _).hom = yoneda.map αW :=
    ⟨Yoneda.fullyFaithful.preimage (W.1.hom ≫ (D.projection _).hom),
      (Yoneda.fullyFaithful.map_preimage _).symm⟩
  have hsq : (D.relativeMap (D.genericPointRestrict hK a)).hom ≫
      (D.projection (CostructuredArrow.mk a)).hom =
      (D.projection _).hom ≫ yoneda.map (genericPoint R K hR hK b) :=
    congrArg InducedCategory.Hom.hom
      (isPullback_baseChangeMap D.f (D.genericPointRestrict hK a)).w
  have heq : c ≫ α = αW ≫ genericPoint R K hR hK b := by
    apply Yoneda.fullyFaithful.map_injective
    have e1 : yoneda.map c ≫ yoneda.map α = (yoneda.map c ≫ U.1.hom) ≫
        (D.projection (CostructuredArrow.mk a)).hom :=
      (congrArg (yoneda.map c ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm
    have e2 : (yoneda.map c ≫ U.1.hom) ≫ (D.projection (CostructuredArrow.mk a)).hom =
        W.1.hom ≫ ((D.relativeMap (D.genericPointRestrict hK a)).hom ≫
          (D.projection (CostructuredArrow.mk a)).hom) :=
      (congrArg (· ≫ (D.projection (CostructuredArrow.mk a)).hom) hc.symm).trans
        (Category.assoc _ _ _)
    have e3 : W.1.hom ≫ ((D.relativeMap (D.genericPointRestrict hK a)).hom ≫
          (D.projection (CostructuredArrow.mk a)).hom) =
        yoneda.map αW ≫ yoneda.map (genericPoint R K hR hK b) :=
      (congrArg (W.1.hom ≫ ·) hsq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ yoneda.map (genericPoint R K hR hK b)) hαW))
    exact ((Functor.map_comp _ _ _).trans (e1.trans (e2.trans e3))).trans
      (Functor.map_comp _ _ _).symm
  have hsch : (BigFppfOver.toScheme B S hS).map c ≫ (BigFppfOver.toScheme B S hS).map α =
      (BigFppfOver.toScheme B S hS).map αW ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Functor.map_comp, heq, Functor.map_comp]
    rfl
  have hring : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      ((BigFppfOver.toScheme B S hS).map α).appTop ≫
        ((BigFppfOver.toScheme B S hS).map c).appTop =
      CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        ((BigFppfOver.toScheme B S hS).map αW).appTop := by
    rw [← Scheme.Hom.comp_appTop, hsch, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have key : chartDiagramPullback B S hS (D.relativeMap (D.genericPointRestrict hK a))
      ⟨W, U, c, hc⟩ (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        ((BigFppfOver.toScheme B S hS).map α).appTop).hom r) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        ((BigFppfOver.toScheme B S hS).map αW).appTop).hom (algebraMap R K r) :=
    congrArg (fun f => f.hom r) hring
  rw [key]
  exact ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr).isUnit.map _

variable [IsDomain R] [ValuationRing R]

/-- **The extended quotient is flat over the valuation ring.**  For `f` quasi-compact and a
quasi-coherent quotient over the fraction field `K`, its extension over `Spec R`
(`AlgebraicGeometry.Space.QuotSituation.extensionKernel`) is flat over `R`. -/
@[ega "IV 2.8.1" "Flatness clause"]
theorem isFlatOver_quotientModule_extensionKernel (hqc : IsQuasiCompact B S hS D.f.hom)
    (K' : Subobject (D.baseChangeModule (CostructuredArrow.mk
      ((schemeSpaceFunctor B S hS).map (genericPoint R K hR hK b) ≫ a))))
    (hQ : (D.quotientModule _ K').IsQuasicoherentOnSite) :
    IsFlatOver B S hS (D.space (CostructuredArrow.mk a)).2
      (D.projection (CostructuredArrow.mk a)).hom
      (D.quotientModule _ (D.extensionKernel (D.genericPointRestrict hK a) K')) := by
  have haff := D.isAffineHom_relativeMap_genericPointRestrict hK a
  have := D.isQuasicoherentOnSite_extensionKernel_genericPointRestrict hK a K' hQ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (CostructuredArrow.mk a).left) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  obtain ⟨U, hUa, hUs⟩ := exists_isAffine_isSurjective_chart_baseChangeSpace B S hS D.f hqc
    (CostructuredArrow.mk a) inferInstance
  have := hUa
  let α : (SmallEtale.toOver B S hS _).obj U ⟶ siteObject B S hS hR b :=
    Yoneda.fullyFaithful.preimage (U.1.hom ≫ (D.projection (CostructuredArrow.mk a)).hom)
  have hα : U.1.hom ≫ (D.projection (CostructuredArrow.mk a)).hom = yoneda.map α :=
    (Yoneda.fullyFaithful.map_preimage _).symm
  refine isFlatOver_of_flat_sections_of_isSurjective (R := CommRingCat.of R)
    (D.projection (CostructuredArrow.mk a)) _ U hUs α hα ?_
  let ρ := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    ((BigFppfOver.toScheme B S hS).map α).appTop).hom
  let : Module R ((D.quotientModule _
    (D.extensionKernel (D.genericPointRestrict hK a) K')).val.obj (op U)) := Module.compHom _ ρ
  let : Module R (((modulePushforward B S hS (D.relativeMap (D.genericPointRestrict hK a))).obj
    (D.quotientModule _ K')).val.obj (op U)) := Module.compHom _ ρ
  have : Module.IsTorsionFree R (((modulePushforward B S hS
      (D.relativeMap (D.genericPointRestrict hK a))).obj (D.quotientModule _ K')).val.obj
        (op U)) := by
    refine ⟨fun r hr => ?_⟩
    have hr0 : r ≠ 0 := fun h => not_isRegular_zero (h ▸ hr)
    exact injective_smul_modulePushforward_of_isUnit _ haff _ U hUa (ρ r)
      (fun W c hc => D.isUnit_chartDiagramPullback_genericPoint hK a U α hα W c hc hr0)
  have : Module.IsTorsionFree R ((D.quotientModule _
      (D.extensionKernel (D.genericPointRestrict hK a) K')).val.obj (op U)) :=
    Function.Injective.moduleIsTorsionFree
      ((D.extensionQuotientι (D.genericPointRestrict hK a) K').val.app (op U))
      (Stacks.SheafOfModules.injective_app_of_mono _ _)
      (fun r m => ((D.extensionQuotientι (D.genericPointRestrict hK a) K').val.app
        (op U)).hom.map_smul (ρ r) m)
  exact StacksDraft.GenericFibre.flat_of_isTorsionFree _ inferInstance

/-- **The extension of a quotient from the generic fibre lies in `Quot_{F/X/B}(R)` and pulls
back to the given quotient.** -/
theorem exists_mem_properlySupportedQuotients_quotientPullback_eq
    (hproper : IsProper B S hS D.f.hom) (hF : SheafOfModules.IsFiniteTypeOnSite D.F)
    (K' : Subobject (D.baseChangeModule (CostructuredArrow.mk
      ((schemeSpaceFunctor B S hS).map (genericPoint R K hR hK b) ≫ a))))
    (hK' : K' ∈ D.properlySupportedQuotients _) :
    ∃ L ∈ D.properlySupportedQuotients (CostructuredArrow.mk a),
      D.quotientPullback (D.genericPointRestrict hK a) L = K' := by
  have hQ : (D.quotientModule _ K').IsQuasicoherentOnSite := hK'.1.1.1
  have : Mono (D.relativeMap (D.genericPointRestrict hK a)) :=
    mono_baseChangeMap_of_isHomLift (hR := hR) (hA := hK) (b := b) D.f R K _
      (D.isHomLift_genericPointRestrict hK a)
  have haff := D.isAffineHom_relativeMap_genericPointRestrict hK a
  have := isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom
    (D.relativeMap (D.genericPointRestrict hK a)) haff (D.quotientModule _ K') hQ
  have hflat := D.isFlatOver_quotientModule_extensionKernel hK a hproper.2.1.2 K' hQ
  refine ⟨D.extensionKernel (D.genericPointRestrict hK a) K', ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩,
    D.quotientPullback_extensionKernel _ K'⟩
  · exact D.isQuasicoherentOnSite_extensionKernel_genericPointRestrict hK a K' hQ
  · exact hflat
  · have := D.isQuasicoherentOnSite_extensionKernel_genericPointRestrict hK a K' hQ
    have hlfp : IsLocallyOfFinitePresentation B S hS (D.projection (CostructuredArrow.mk a)).hom :=
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsFinitePresentation B S hS k.hom)
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f (CostructuredArrow.mk a).hom)
        D.finitePresentation).1
    exact isFinitePresentationOnSite_of_isFinitePresentationOnCharts _ _ inferInstance
      (isFinitePresentationOnCharts_of_isFlatOver_of_isDomain (R := R) (Iso.refl _)
        (D.projection (CostructuredArrow.mk a)) _ hlfp
        (D.isFiniteTypeOnSite_quotientModule_extensionKernel _ hF K')
        hflat)
  · have := D.isFiniteTypeOnSite_quotientModule_extensionKernel (D.genericPointRestrict hK a) hF K'
    exact D.isProperlySupportedOver_of_isProper hproper _ _

end QuotSituation

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {hR : B.Contains (Spec (.of R))}
  (hK : B.Contains (Spec (.of K))) {b : Spec (.of R) ⟶ S}
  (a : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hR b) ⟶ D.Y)

/-- **Quotients over the fraction field of a valuation ring extend over the valuation ring.**
For `f : X ⟶ B` proper and `F` of finite type, a section of the Quot presheaf over `Spec K`
lying over `Spec K ⟶ Spec R ⟶ B` is the base change of a section over `Spec R` lying over the
given morphism `Spec R ⟶ B`. -/
theorem exists_quotFamilyOver_baseChange_eq (hproper : IsProper B S hS D.f.hom)
    (hF : SheafOfModules.IsFiniteTypeOnSite D.F)
    (x : QuotFamilyOver D (siteObject B S hS hK
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)))
    (hx : x.toBase = (schemeSpaceFunctor B S hS).map (genericPoint R K hR hK b) ≫ a) :
    ∃ y : QuotFamilyOver D (siteObject B S hS hR b),
      y.toBase = a ∧ y.baseChange (genericPoint R K hR hK b) = x := by
  obtain ⟨xb, xs, xm⟩ := x
  dsimp only at hx
  subst hx
  obtain ⟨L, hL, hpull⟩ := D.exists_mem_properlySupportedQuotients_quotientPullback_eq hK a
    hproper hF xs xm
  exact ⟨⟨a, L, hL⟩, rfl, QuotFamilyOver.ext rfl (heq_of_eq hpull)⟩

end QuotSituation

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces which is proper and of finite
presentation, and let `F` be a quasi-coherent `𝒪_X`-module of finite type.  Then
`Quot_{F/X/B} ⟶ B` satisfies the existence part of the valuative criterion (Stacks 03IX): for
every model of the Quot presheaf, its canonical morphism to `B` has it.  Here the Quot situation
`D` (Stacks 09TR) records `f`, its finite presentation and the quasi-coherent module `F`. -/
@[stacks 0DM4]
theorem QuotSitePresheafModel.valuativeCriterionExistence_toBase (D : QuotSituation B S hS)
    (hproper : IsProper B S hS D.f.hom) (hF : SheafOfModules.IsFiniteTypeOnSite D.F)
    (N : QuotSitePresheafModel D) : ValuativeCriterion.Existence N.toBase :=
  N.valuativeCriterionExistence_toBase_of_forall_exists_baseChange_eq fun q x hx =>
    D.exists_quotFamilyOver_baseChange_eq q.field_mem (ObjectProperty.homMk q.special) hproper hF
      x hx

end AlgebraicGeometry.Space

end
