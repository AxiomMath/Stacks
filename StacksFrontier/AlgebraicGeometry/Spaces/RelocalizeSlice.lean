module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
import all StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport

/-!
# Algebraic spaces over a scheme of the site are relocalizations

Let `g : T ⟶ S` be a morphism of schemes of a big fppf site. An algebraic space `X` over `S`
with a morphism `f : X ⟶ h_{(T, g)}` is the lower-shriek extension `Λ X_T` of an algebraic space
`X_T` over `T`, compatibly with the structure morphisms (Stacks 04SG). Under this identification
finite presentation and flatness of `f` are those of `X_T ⟶ T`, and a module on `X` is of finite
presentation, flat over `h_{(T, g)}` and with support proper over `h_{(T, g)}` exactly when the
corresponding module on `X_T` is so over `T`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeBaseHom`: the isomorphism `Λ h_T ≅ h_{(T, g)}`.

## Main results

* `AlgebraicGeometry.Space.exists_relocalizeSpace_iso`: an algebraic space over `S` with a
  morphism `f` to `h_{(T, g)}` is `Λ X_T` for an algebraic space `X_T` over `T`.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_of_relocalizeSpace_iso`,
  `AlgebraicGeometry.Space.isFlat_iff_of_relocalizeSpace_iso`: `f` is of finite presentation,
  respectively flat, exactly when `X_T ⟶ T` is.
* `AlgebraicGeometry.Space.coefficientConditions_iff_of_relocalizeSpace_iso`: a module on `X` is
  of finite presentation, flat and with proper support over `h_{(T, g)}` exactly when the
  corresponding module on `X_T` is so over `T`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The relocalized base -/

section RelocalizeBase

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- The lower-shriek extension along `g : T ⟶ S` of the final object of the site over `T` is
the scheme `T` over `S`: the structure morphism `Λ h_T ⟶ h_{(T, g)}`. -/
def relocalizeBaseHom :
    relocalizeSpace B hT hS g (schemeSpace (Over.mk (𝟙 (B.obj hT)))) ⟶ schemeSpace (Over.mk g) :=
  ObjectProperty.homMk (OverShriek.viewStructureMap g (yoneda.obj (Over.mk (𝟙 (B.obj hT)))))

/-- The structure morphism `Λ h_T ⟶ h_{(T, g)}` is an isomorphism. -/
instance : IsIso (relocalizeBaseHom B hT hS g) := by
  have (W : (BigFppfOver B S hS)ᵒᵖ) : IsIso ((OverShriek.viewStructureMap g
      (yoneda.obj (Over.mk (𝟙 (B.obj hT))))).app W) := by
    rw [isIso_iff_bijective]
    refine ⟨fun x y hxy => ?_, fun α => ?_⟩
    · obtain ⟨⟨ψ, t⟩, hψ⟩ := x
      obtain ⟨⟨ψ', t'⟩, hψ'⟩ := y
      obtain rfl : ψ = ψ' := congrArg CommaMorphism.left hxy
      obtain rfl : t = t' := (OverShriek.subsingleton_yoneda_obj_mkId _).elim _ _
      rfl
    · exact ⟨⟨⟨α.left, Over.homMk α.left (Category.comp_id _)⟩, Over.w α⟩,
        Over.OverMorphism.ext rfl⟩
  have : IsIso ((ObjectProperty.ι _).map (relocalizeBaseHom B hT hS g)) :=
    NatIso.isIso_of_isIso_app (OverShriek.viewStructureMap g (yoneda.obj (Over.mk (𝟙 (B.obj hT)))))
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

variable {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B T hT X)

/-- The structure morphism of `Λ X` to `(T, g)` is `Λ` of the structure morphism of `X`. -/
theorem relocalizeHom_comp_relocalizeBaseHom
    (f : (⟨X, hX⟩ : AlgebraicSpaces B T hT) ⟶ schemeSpace (Over.mk (𝟙 (B.obj hT)))) :
    (relocalizeHom B hT hS g f ≫ relocalizeBaseHom B hT hS g).hom =
      OverShriek.viewStructureMap g X := by
  ext W x
  rfl

end RelocalizeBase

/-- The structure morphism of the lower-shriek extension of a restriction is the first projection
of the product with the base. -/
theorem OverShriek.relocalizeRestrictIsoProduct_hom_fst {C : Type*} [Category.{u} C] {U V : C}
    (f : V ⟶ U) (F : (Over U)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizeRestrictIsoProduct f F).hom ≫ prod.fst =
      OverShriek.viewStructureMap f ((OverShriek.relocalizeRestrict f).obj F) := by
  ext W x
  simp [OverShriek.relocalizeRestrictIsoProduct, OverShriek.viewStructureMap]
  rfl

/-- `Λ` of a morphism commutes with the structure morphisms. -/
theorem OverShriek.relocalize_map_viewStructureMap {C : Type*} [Category.{u} C] {U V : C}
    (f : V ⟶ U) {F G : (Over V)ᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor f).map α ≫ OverShriek.viewStructureMap f G =
      OverShriek.viewStructureMap f F := by
  ext W x
  rfl


/-! ### Algebraic spaces over `(T, g)` -/

section Slice

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- The structure morphism of an algebraic space over `T` to the final object `h_T`. -/
abbrev toFinalHom (X : AlgebraicSpaces B T hT) : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hT))) :=
  ObjectProperty.homMk (OverShriek.toYonedaMkId X.1)

/-- An algebraic space `X` over `S` with a morphism `f : X ⟶ h_{(T, g)}` is the lower-shriek
extension of an algebraic space `X_T` over `T`, by an isomorphism carrying `f` to `Λ` of the
structure morphism of `X_T`. -/
theorem exists_relocalizeSpace_iso (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (Over.mk g)) :
    ∃ (XT : AlgebraicSpaces B T hT) (e : relocalizeSpace B hT hS g XT ≅ X),
      e.hom ≫ f = relocalizeHom B hT hS g (toFinalHom B hT XT) ≫ relocalizeBaseHom B hT hS g := by
  obtain ⟨F, hF, ⟨e, he⟩⟩ := exists_viewOver_iso B S hS T hT g X.2 f.hom
  refine ⟨⟨F, hF⟩, ObjectProperty.isoMk _ e, ObjectProperty.hom_ext _ ?_⟩
  exact he.trans (relocalizeHom_comp_relocalizeBaseHom B hT hS g hF (toFinalHom B hT ⟨F, hF⟩)).symm

variable {B hT hS g} {X : AlgebraicSpaces B S hS} {f : X ⟶ schemeSpace (Over.mk g)}
  {XT : AlgebraicSpaces B T hT} {fT : XT ⟶ schemeSpace (Over.mk (𝟙 (B.obj hT)))}
  (e : relocalizeSpace B hT hS g XT ≅ X)
  (he : e.hom ≫ f = relocalizeHom B hT hS g fT ≫ relocalizeBaseHom B hT hS g)

include he in
/-- The underlying arrows of `f` and of `Λ fT` are isomorphic. -/
theorem arrowIso_of_relocalizeSpace_iso :
    (ObjectProperty.ι _).map e.hom ≫ f.hom =
      (relocalizeHom B hT hS g fT).hom ≫ (ObjectProperty.ι _).map (relocalizeBaseHom B hT hS g) :=
  congrArg (fun φ => φ.hom) he

/-- Under `Λ X_T ≅ X`, an étale chart property holds for `f` exactly when it holds for the
structure morphism of `X_T`. -/
private theorem holdsOnEveryEtaleChart_iff_of_relocalizeSpace_iso
    (Q : MorphismProperty Scheme.{u})
    (w : (ObjectProperty.ι _).map e.hom ≫ f.hom =
      (relocalizeHom B hT hS g fT).hom ≫ (ObjectProperty.ι _).map (relocalizeBaseHom B hT hS g)) :
    HoldsOnEveryEtaleChart B S hS Q f.hom ↔ HoldsOnEveryEtaleChart B T hT Q fT.hom := by
  refine (holdsOnEveryEtaleChart_iso_comp_iff B S hS _ ((ObjectProperty.ι _).map e.hom)
    f.hom).symm.trans ?_
  rw [w]
  exact (holdsOnEveryEtaleChart_comp_iso_iff B S hS _ _ _).trans
    (holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ fT.hom)

include he in
/-- Under `Λ X_T ≅ X`, the morphism `f` is of finite presentation exactly when the structure
morphism of `X_T` is. -/
theorem isFinitePresentation_iff_of_relocalizeSpace_iso :
    IsFinitePresentation B S hS f.hom ↔ IsFinitePresentation B T hT fT.hom := by
  have w := arrowIso_of_relocalizeSpace_iso e he
  have hΛ : IsFinitePresentation B S hS (relocalizeHom B hT hS g fT).hom ↔
      IsFinitePresentation B T hT fT.hom :=
    and_congr (holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ fT.hom)
      (and_congr (isQuasiCompact_relocalize_iff B T hT S hS g fT.hom)
        (isQuasiSeparated_relocalize_iff B T hT S hS g fT.hom))
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ hΛ
  · exact isFinitePresentation_of_arrowIso B S hS _ _ (inv ((ObjectProperty.ι _).map e.hom))
      (inv ((ObjectProperty.ι _).map (relocalizeBaseHom B hT hS g)))
      (by rw [IsIso.inv_comp_eq, ← Category.assoc, w, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]) h
  · exact isFinitePresentation_of_arrowIso B S hS _ _ ((ObjectProperty.ι _).map e.hom)
      ((ObjectProperty.ι _).map (relocalizeBaseHom B hT hS g)) w h

include he in
/-- Under `Λ X_T ≅ X`, the morphism `f` is flat exactly when the structure morphism of `X_T`
is. -/
theorem isFlat_iff_of_relocalizeSpace_iso :
    IsFlat B S hS f.hom ↔ IsFlat B T hT fT.hom :=
  holdsOnEveryEtaleChart_iff_of_relocalizeSpace_iso e _ (arrowIso_of_relocalizeSpace_iso e he)

include he in
/-- Under `Λ X_T ≅ X`, the morphism `f` is locally of finite type exactly when the structure
morphism of `X_T` is. -/
theorem isLocallyOfFiniteType_iff_of_relocalizeSpace_iso :
    IsLocallyOfFiniteType B S hS f.hom ↔ IsLocallyOfFiniteType B T hT fT.hom :=
  holdsOnEveryEtaleChart_iff_of_relocalizeSpace_iso e _ (arrowIso_of_relocalizeSpace_iso e he)

/-- The module on `X_T` attached to a module on `X` under `Λ X_T ≅ X`. -/
abbrev relocalizeSpaceModule (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B T hT XT.1 XT.2 :=
  (relocalizeModulesEquivalence B hT hS g XT.1 XT.2).inverse.obj
    ((modulePullback B S hS e.hom).obj F)

include he in
/-- A module on `X` is of finite presentation, flat over `h_{(T, g)}` and with support proper
over `h_{(T, g)}` exactly when the corresponding module on `X_T` under `Λ X_T ≅ X` is of finite
presentation, flat over `T` and with support proper over `T`. -/
theorem coefficientConditions_iff_of_relocalizeSpace_iso (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (F.IsFinitePresentation ∧ IsFlatOver B S hS X.2 f.hom F ∧
      HasProperSupport B S hS X.2 (schemeSpace (Over.mk g)).2 f.hom hf
        ((SheafOfModules.toSheaf _).obj F)) ↔
    ((relocalizeSpaceModule e F).IsFinitePresentation ∧
      IsFlatOver B T hT XT.2 fT.hom (relocalizeSpaceModule e F) ∧
      HasProperSupport B T hT XT.2 (schemeSpace (Over.mk (𝟙 (B.obj hT)))).2 fT.hom
        ((isLocallyOfFiniteType_iff_of_relocalizeSpace_iso e he).1 hf)
        ((SheafOfModules.toSheaf _).obj (relocalizeSpaceModule e F))) := by
  have hfT := (isLocallyOfFiniteType_iff_of_relocalizeSpace_iso e he).1 hf
  have hY := (schemeSpace (Over.mk (𝟙 (B.obj hT)))).2
  let E := relocalizeModulesEquivalence B hT hS g XT.1 XT.2
  have hlftrel : IsLocallyOfFiniteType B S hS (relocalizeHom B hT hS g fT).hom :=
    (isLocallyOfFiniteType_relocalize_iff B T hT S hS g fT.hom).2 hfT
  constructor
  · rintro ⟨hFfp, hFflat, hFsupp⟩
    have sq : IsPullback e.hom (relocalizeHom B hT hS g fT) f (relocalizeBaseHom B hT hS g) :=
      IsPullback.of_horiz_isIso ⟨he⟩
    obtain ⟨hMfp, hMflat, hMsupp⟩ :=
      modulePullback_coefficient_conditions sq hf F hFfp hFflat hFsupp
    exact ⟨isFinitePresentation_relocalizeModulesEquivalence_inverse B hT hS g XT.1 XT.2 _ hMfp,
      isFlatOver_relocalizeModulesEquivalence_inverse B hT hS g XT.2 hY fT.hom _ hMflat,
      (hasProperSupport_relocalizeModulesEquivalence_inverse_iff B hT hS g XT.2 hY fT.hom hfT
        _).2 hMsupp⟩
  · rintro ⟨hfp, hflat, hsupp⟩
    let N := E.functor.obj (relocalizeSpaceModule e F)
    have hNfp := isFinitePresentation_relocalizeModulesEquivalence_functor B hT hS g XT.1 XT.2 _ hfp
    have hNflat := isFlatOver_relocalizeModulesEquivalence_functor B hT hS g XT.2 hY fT.hom _ hflat
    have hNsupp := (hasProperSupport_relocalizeModulesEquivalence_functor_iff B hT hS g XT.2 hY
      fT.hom hfT _).2 hsupp
    have sq :
        IsPullback e.inv f (relocalizeHom B hT hS g fT) (inv (relocalizeBaseHom B hT hS g)) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [IsIso.eq_comp_inv, Category.assoc, ← he, Iso.inv_hom_id_assoc]
    obtain ⟨hPfp, hPflat, hPsupp⟩ :=
      modulePullback_coefficient_conditions sq hlftrel N hNfp hNflat hNsupp
    let ι : (modulePullback B S hS e.inv).obj N ≅ F :=
      (modulePullback B S hS e.inv).mapIso (E.counitIso.app _) ≪≫
        (modulePullbackCompIso B S hS e.inv e.hom).app F ≪≫
        eqToIso (congrArg (fun φ => (modulePullback B S hS φ).obj F) e.inv_hom_id) ≪≫
        (modulePullbackIdIso B S hS X).app F
    exact ⟨(SheafOfModules.isFinitePresentation _).prop_of_iso ι hPfp,
      IsFlatOver.of_iso B S hS _ ι hPflat, hasProperSupport_of_iso _ _ hf ι hPsupp⟩

end Slice

end AlgebraicGeometry.Space
