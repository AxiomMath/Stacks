module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectClosedFibre

/-!
# A polarization of stable curves from relatively ample modules

Let every stable family of curves `F` carry an invertible module `L_F` on its total space which is
ample relative to the structure morphism (Stacks 0D31), compatibly with the morphisms of stable
families: the pullback of `L_G` along a morphism `F ⟶ G` is isomorphic to `L_F`. Then stable
families carry a polarization compatible with all their morphisms
(`AlgebraicGeometry.StableCurvesPolarization`). The relative dualizing sheaf is such a choice.

The construction. By Stacks 0D32 the total space of `F` is a scheme `X`, represented by
`yoneda.obj X ≅ F.total`; the structure morphism of `F` is the Yoneda image of a morphism
`X ⟶ S` of schemes, which is proper, flat and of finite presentation because its Yoneda image is
(Stacks 03ZM, 03MJ). The restriction of `L_F` to `X` is invertible and ample relative to
`X ⟶ S` (Stacks 0D31 at the representing square), so `(X ⟶ S, L_F|_X)` is a polarized family
(Stacks 0D1M) whose underlying family of algebraic spaces is `F`. A morphism `F ⟶ G` of stable
families is the Yoneda image of a morphism of the representing schemes, whose square is cartesian
because Yoneda reflects pullbacks; the restriction of an invertible module commutes with base
change of the chart, and the compatibility of the modules supplies the comparison of the
polarizations.

## Main definitions

* `AlgebraicGeometry.CurveFamily.polarizedFamilyOfIsRelativelyAmple`: the polarized family of a
  family of curves carrying a relatively ample invertible module.
* `AlgebraicGeometry.stableCurvesPolarizationOfModules`: the polarization of stable families from
  relatively ample invertible modules compatible with morphisms.

## Main results

* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_modules`: the statement of
  Stacks 0E9A with relatively ample invertible modules compatible with morphisms in place of
  Stacks 0DSS.

## Implementation notes

The invertibility of `L_F` on the algebraic space is part of the setting of Stacks 0D31 (where `L`
is an invertible module); the repository's `AlgebraicGeometry.Space.IsRelativelyAmple` records only
the invertibility of the restrictions to schemes, and the invertibility on the space is what makes
the restriction to a scheme commute with base change
(`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`), so it is a binder
of its own.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A scheme of the site over `Spec(ℤ)` is the scheme of the site underlying it, read over
`Spec(ℤ)` through the terminal maps. -/
def schemeOverIntegersLeftIso (T : BigFppfOver B integerBase hZ) :
    (schemeOverIntegers B).obj T.left ≅ T :=
  Over.isoMk (Iso.refl _) ((siteIntegerBaseIsTerminal B hZ).hom_ext _ _)

/-- A scheme of the site over `Spec(ℤ)` is, on the nose, the scheme of the site underlying it read
over `Spec(ℤ)`: its structure morphism is the unique morphism to the terminal object. -/
theorem schemeOverIntegers_obj_left (T : BigFppfOver B integerBase hZ) :
    (schemeOverIntegers B).obj T.left = T := by
  obtain ⟨l, ⟨⟨⟩⟩, h⟩ := T
  obtain rfl : h = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  rfl

/-- The identification `AlgebraicGeometry.schemeOverIntegersLeftIso` is the transport along the
equality `AlgebraicGeometry.schemeOverIntegers_obj_left`. -/
theorem schemeOverIntegersLeftIso_hom (T : BigFppfOver B integerBase hZ) :
    (schemeOverIntegersLeftIso T).hom = eqToHom (schemeOverIntegers_obj_left T) := by
  apply Over.OverMorphism.ext
  rw [Over.eqToHom_left]
  exact (eqToHom_refl _ _).symm

/-- The identification `AlgebraicGeometry.schemeOverIntegersLeftIso` is natural. -/
theorem schemeOverIntegersLeftIso_inv_naturality {T T' : BigFppfOver B integerBase hZ}
    (b : T ⟶ T') :
    b ≫ (schemeOverIntegersLeftIso T').inv =
      (schemeOverIntegersLeftIso T).inv ≫ (schemeOverIntegers B).map b.left := by
  apply Over.OverMorphism.ext
  simp [schemeOverIntegersLeftIso, schemeOverIntegers]

/-- An isomorphism of finitely presented, flat and proper families of algebraic spaces is an
isomorphism of the underlying families: every isomorphism is strongly cartesian. -/
def cartesianProperFlatIsoMk {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : CartesianProperFlatSpaces B S hS} (e : X.obj.obj ≅ Y.obj.obj) : X ≅ Y where
  hom := ⟨ObjectProperty.homMk e.hom, by
    change (spacesProjection B S hS).IsStronglyCartesian ((spacesProjection B S hS).map e.hom) e.hom
    infer_instance⟩
  inv := ⟨ObjectProperty.homMk e.inv, by
    change (spacesProjection B S hS).IsStronglyCartesian ((spacesProjection B S hS).map e.inv) e.inv
    infer_instance⟩
  hom_inv_id := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ e.hom_inv_id)
  inv_hom_id := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ e.inv_hom_id)

namespace CurveFamily

section Ample

variable (F : CurveFamily B hZ) {L : Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2}
  (hL : Space.IsRelativelyAmple B integerBase hZ F.toBase L)

include hL in
/-- The total space of a family of curves carrying a relatively ample module is representable
(Stacks 0D32). -/
theorem isRepresentable_total_of_isRelativelyAmple : F.total.1.IsRepresentable := by
  have : (schemeSpace F.base).1.IsRepresentable :=
    inferInstanceAs (yoneda.obj F.base).IsRepresentable
  exact hL.isRepresentable

/-- The scheme of the site representing the total space of a family of curves carrying a
relatively ample module. -/
def ampleTotalScheme : B.Schemes :=
  haveI := F.isRepresentable_total_of_isRelativelyAmple hL
  F.total.1.reprX.left

/-- The representing isomorphism of the total space. -/
def ampleTotalIso :
    yoneda.obj ((schemeOverIntegers B).obj (F.ampleTotalScheme hL)) ≅ F.total.1 :=
  haveI := F.isRepresentable_total_of_isRelativelyAmple hL
  yoneda.mapIso (schemeOverIntegersLeftIso F.total.1.reprX) ≪≫ F.total.1.reprW

/-- The structure morphism of the representing scheme. -/
def ampleStructureMap :
    (schemeOverIntegers B).obj (F.ampleTotalScheme hL) ⟶ (schemeOverIntegers B).obj F.base.left :=
  yoneda.preimage ((F.ampleTotalIso hL).hom ≫ F.toBase.hom ≫
    yoneda.map (schemeOverIntegersLeftIso F.base).inv)

/-- The Yoneda image of the structure morphism of the representing scheme is the structure
morphism of the family, read through the representing isomorphisms. -/
theorem yoneda_map_ampleStructureMap :
    yoneda.map (F.ampleStructureMap hL) = (F.ampleTotalIso hL).hom ≫ F.toBase.hom ≫
      yoneda.map (schemeOverIntegersLeftIso F.base).inv :=
  yoneda.map_preimage _

/-- The representing square of the total space commutes. -/
theorem yoneda_map_ampleStructureMap_comp :
    yoneda.map (F.ampleStructureMap hL) ≫ yoneda.map (schemeOverIntegersLeftIso F.base).hom =
      (F.ampleTotalIso hL).hom ≫ F.toBase.hom := by
  have e : (F.toBase.hom ≫ yoneda.map (schemeOverIntegersLeftIso F.base).inv) ≫
      yoneda.map (schemeOverIntegersLeftIso F.base).hom = F.toBase.hom :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => F.toBase.hom ≫ k)
      (yoneda.mapIso (schemeOverIntegersLeftIso F.base)).inv_hom_id).trans (Category.comp_id _))
  rw [yoneda_map_ampleStructureMap]
  exact (Category.assoc _ _ _).trans (congrArg (fun k => (F.ampleTotalIso hL).hom ≫ k) e)

/-- The representing square of the total space, in algebraic spaces. -/
theorem isPullback_ampleStructureMap :
    IsPullback (ObjectProperty.isoMk _ (F.ampleTotalIso hL)).hom
      (schemeSpaceMap (F.ampleStructureMap hL)) F.toBase
      (schemeSpaceMap (schemeOverIntegersLeftIso F.base).hom) := by
  have : IsIso (schemeSpaceMap (schemeOverIntegersLeftIso F.base).hom) :=
    inferInstanceAs (IsIso (ObjectProperty.isoMk (fun G => IsAlgebraicSpace B integerBase hZ G)
      (X := schemeSpace ((schemeOverIntegers B).obj F.base.left)) (Y := schemeSpace F.base)
      (yoneda.mapIso (schemeOverIntegersLeftIso F.base))).hom)
  exact IsPullback.of_horiz_isIso
    ⟨ObjectProperty.hom_ext _ (F.yoneda_map_ampleStructureMap_comp hL).symm⟩

/-- The structure morphism of the representing scheme has a proper Yoneda image: it is a base
change of the structure morphism of the family. -/
theorem isProper_yoneda_map_ampleStructureMap :
    Space.IsProper B integerBase hZ (yoneda.map (F.ampleStructureMap hL)) :=
  (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (F.isPullback_ampleStructureMap hL) F.proper

/-- The structure morphism of the representing scheme has a flat Yoneda image. -/
theorem isFlat_yoneda_map_ampleStructureMap :
    Space.IsFlat B integerBase hZ (yoneda.map (F.ampleStructureMap hL)) :=
  (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (F.isPullback_ampleStructureMap hL) F.flat

/-- The structure morphism of the representing scheme has a finitely presented Yoneda image. -/
theorem isFinitePresentation_yoneda_map_ampleStructureMap :
    Space.IsFinitePresentation B integerBase hZ (yoneda.map (F.ampleStructureMap hL)) :=
  (Space.isFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (F.isPullback_ampleStructureMap hL) F.finitePresentation

/-- The restriction of the module to the representing scheme is invertible and ample relative to
its structure morphism (Stacks 0D31 at the representing square). -/
theorem exists_isRelativelyAmple_ampleStructureMap :
    ∃ hinv : Stacks.Ample.IsInvertibleModule
        ((BigFppfOver.toScheme B integerBase hZ).obj
          ((schemeOverIntegers B).obj (F.ampleTotalScheme hL)))
        (Space.baseChangeModule B integerBase hZ L _ (F.ampleTotalIso hL).hom),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _
        ((BigFppfOver.toScheme B integerBase hZ).map (F.ampleStructureMap hL))
        (Space.baseChangeModule B integerBase hZ L _ (F.ampleTotalIso hL).hom) hinv := by
  exact hL.2 _ _ (yoneda.map (schemeOverIntegersLeftIso F.base).hom) _ _
    (Space.isPullback_hom_of_isPullback B integerBase hZ (F.isPullback_ampleStructureMap hL))

/-- **The polarized family of a family of curves with a relatively ample module.** Its total
space is the scheme representing the total space of the family (Stacks 0D32), its structure
morphism the morphism of schemes whose Yoneda image is the structure morphism of the family, and
its polarization the restriction of the module. -/
def polarizedFamilyOfIsRelativelyAmple : PolarizedFamily B where
  base := F.base.left
  total := (F.ampleTotalScheme hL).obj
  toBase := (F.ampleStructureMap hL).left.hom
  proper := Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ _
    (F.isProper_yoneda_map_ampleStructureMap hL)
  flat := Space.flat_of_isFlat_yoneda B integerBase hZ _ _ _
    (F.isFlat_yoneda_map_ampleStructureMap hL)
  finitePresentation := Space.finitePresentation_toScheme_map_of_yoneda_map B integerBase hZ _
    (F.isFinitePresentation_yoneda_map_ampleStructureMap hL)
    (F.isProper_yoneda_map_ampleStructureMap hL)
  lineBundle := Space.baseChangeModule B integerBase hZ L
    ((schemeOverIntegers B).obj (F.ampleTotalScheme hL)) (F.ampleTotalIso hL).hom
  invertible := (F.exists_isRelativelyAmple_ampleStructureMap hL).fst
  relativelyAmple := (F.exists_isRelativelyAmple_ampleStructureMap hL).snd

/-- The underlying family of algebraic spaces of the polarized family of `F` is `F`. -/
def forgetPolarizationFamilyOfIsRelativelyAmpleIso :
    (forgetPolarization B).obj (F.polarizedFamilyOfIsRelativelyAmple hL) ≅
      (curvesToCartesianProperFlat B hZ).obj F :=
  cartesianProperFlatIsoMk
    (Comma.isoMk (ObjectProperty.isoMk _ (F.ampleTotalIso hL)) (schemeOverIntegersLeftIso F.base)
      (F.yoneda_map_ampleStructureMap_comp hL).symm)

/-- The identification of the underlying family lies over the identity of the base. -/
theorem isHomLift_forgetPolarizationFamilyOfIsRelativelyAmpleIso :
    (cartesianProperFlatProjection B integerBase hZ).IsHomLift (𝟙 F.base)
      (F.forgetPolarizationFamilyOfIsRelativelyAmpleIso hL).hom := by
  refine IsHomLift.of_fac _ _ _ (schemeOverIntegers_obj_left F.base) rfl ?_
  rw [show (cartesianProperFlatProjection B integerBase hZ).map
      (F.forgetPolarizationFamilyOfIsRelativelyAmpleIso hL).hom =
        eqToHom (schemeOverIntegers_obj_left F.base) from schemeOverIntegersLeftIso_hom F.base]
  have key : ∀ {a b c d : BigFppfOver B integerBase hZ} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d),
      eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ = eqToHom (h₁.trans (h₂.trans h₃)) := by
    intros
    subst_vars
    simp
  exact (eqToHom_refl _ _).symm.trans (key _ _ _).symm

end Ample

end CurveFamily

/-- **A polarization of stable families of curves from relatively ample invertible modules.** If
every stable family of curves `F` carries an invertible module `L F` on its total space (`hinv`)
which is ample relative to its structure morphism (`hamp`, Stacks 0D31), and for every morphism
`φ : F ⟶ G` of stable families the pullback of `L G` along the morphism of total spaces is
isomorphic to `L F` (`hcompat`), then stable families carry a polarization compatible with their
morphisms. -/
def stableCurvesPolarizationOfModules
    (L : ∀ F : CurveFamily B hZ, IsStableCurveFamily B hZ F →
      Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2)
    (hinv : ∀ (F : CurveFamily B hZ) (hF : IsStableCurveFamily B hZ F),
      Stacks.SheafOfModules.IsInvertible
        (Space.structurePresheaf B integerBase hZ F.total.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ F.total.1 F.total.2).O)).property (L F hF))
    (hamp : ∀ F hF, Space.IsRelativelyAmple B integerBase hZ F.toBase (L F hF))
    (hcompat : ∀ {F G : CurveFamily B hZ} (hF : IsStableCurveFamily B hZ F)
      (hG : IsStableCurveFamily B hZ G) (φ : F ⟶ G),
      Nonempty ((Space.modulePullback B integerBase hZ φ.totalMap).obj (L G hG) ≅ L F hF)) :
    StableCurvesPolarization B hZ where
  pol F hF := F.polarizedFamilyOfIsRelativelyAmple (hamp F hF)
  iso F hF := F.forgetPolarizationFamilyOfIsRelativelyAmpleIso (hamp F hF)
  isHomLift_iso F hF := F.isHomLift_forgetPolarizationFamilyOfIsRelativelyAmpleIso (hamp F hF)
  lift {F G} hF hG φ := by
    have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
    let eF := F.ampleTotalIso (hamp F hF)
    let eG := G.ampleTotalIso (hamp G hG)
    let qF := F.ampleStructureMap (hamp F hF)
    let qG := G.ampleStructureMap (hamp G hG)
    let h : (schemeOverIntegers B).obj (F.ampleTotalScheme (hamp F hF)) ⟶
        (schemeOverIntegers B).obj (G.ampleTotalScheme (hamp G hG)) :=
      yoneda.preimage (eF.hom ≫ φ.totalMap.hom ≫ eG.inv)
    have hh : yoneda.map h = eF.hom ≫ φ.totalMap.hom ≫ eG.inv := yoneda.map_preimage _
    have hqF : yoneda.map qF = eF.hom ≫ F.toBase.hom ≫
        yoneda.map (schemeOverIntegersLeftIso F.base).inv :=
      F.yoneda_map_ampleStructureMap (hamp F hF)
    have hqG : yoneda.map qG = eG.hom ≫ G.toBase.hom ≫
        yoneda.map (schemeOverIntegersLeftIso G.base).inv :=
      G.yoneda_map_ampleStructureMap (hamp G hG)
    have hsq₀ := Space.isPullback_hom_of_isPullback B integerBase hZ φ.cartesian
    have hsq₁ : IsPullback (yoneda.map h) (yoneda.map qF) (yoneda.map qG)
        (yoneda.map ((schemeOverIntegers B).map φ.baseMap.left)) :=
      hsq₀.of_iso eF.symm eG.symm (yoneda.mapIso (schemeOverIntegersLeftIso F.base).symm)
        (yoneda.mapIso (schemeOverIntegersLeftIso G.base).symm)
        (by rw [hh]; exact (Iso.inv_hom_id_assoc _ _).symm)
        (by rw [hqF]; exact (Iso.inv_hom_id_assoc _ _).symm)
        (by rw [hqG]; exact (Iso.inv_hom_id_assoc _ _).symm)
        ((Functor.map_comp _ _ _).symm.trans
          ((congrArg yoneda.map (schemeOverIntegersLeftIso_inv_naturality φ.baseMap)).trans
            (Functor.map_comp _ _ _)))
    have hsq₂ : IsPullback h qF qG ((schemeOverIntegers B).map φ.baseMap.left) :=
      IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hsq₁.w)) hsq₁
    obtain ⟨e₁⟩ := Space.nonempty_baseChangeModule_baseChange_of_isInvertible (L G hG) (hinv G hG)
      _ _ eG.hom h
    obtain ⟨e₄⟩ := hcompat hF hG φ
    have hcomp : yoneda.map h ≫ eG.hom = eF.hom ≫ φ.totalMap.hom := by simp [hh]
    rw [hcomp] at e₁
    let e₂ := Space.baseChangeModuleCompIso B integerBase hZ φ.totalMap (L G hG) _ eF.hom
    let e₃ := Space.baseChangeModuleMapIso B integerBase hZ e₄ _ eF.hom
    let ψ : F.polarizedFamilyOfIsRelativelyAmple (hamp F hF) ⟶
        G.polarizedFamilyOfIsRelativelyAmple (hamp G hG) :=
      { baseMap := φ.baseMap.left
        totalMap := h.left.hom
        cartesian := hsq₂.map (BigFppfOver.toScheme B integerBase hZ)
        lineBundleIso := e₁.symm ≪≫ e₂ ≪≫ e₃ }
    refine ⟨ψ, WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (CommaMorphism.ext (ObjectProperty.hom_ext _ hh) (Over.OverMorphism.ext ?_)))⟩
    change φ.baseMap.left = 𝟙 _ ≫ φ.baseMap.left ≫ 𝟙 _
    simp

/-- **The statement of Stacks 0E9A, from relatively ample invertible modules on stable families
compatible with their morphisms.** This is
`AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization` with the
polarization `AlgebraicGeometry.stableCurvesPolarizationOfModules`. -/
theorem isSeparated_moduliStableCurvesOfGenus_of_modules
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (g : ℕ) (hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (L : ∀ F : CurveFamily B hZ, IsStableCurveFamily B hZ F →
      Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2)
    (hinv : ∀ (F : CurveFamily B hZ) (hF : IsStableCurveFamily B hZ F),
      Stacks.SheafOfModules.IsInvertible
        (Space.structurePresheaf B integerBase hZ F.total.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ F.total.1 F.total.2).O)).property (L F hF))
    (hamp : ∀ F hF, Space.IsRelativelyAmple B integerBase hZ F.toBase (L F hF))
    (hcompat : ∀ {F G : CurveFamily B hZ} (hF : IsStableCurveFamily B hZ F)
      (hG : IsStableCurveFamily B hZ G) (φ : F ⟶ G),
      Nonempty ((Space.modulePullback B integerBase hZ φ.totalMap).obj (L G hG) ≅ L F hF))
    (h0E87 : @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ))
    (h0E97 : UniqueStableModels B hZ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization B hZ h g hg hP hQ hlim
    (stableCurvesPolarizationOfModules L hinv hamp hcompat) h0E87 h0E97

end AlgebraicGeometry

end
