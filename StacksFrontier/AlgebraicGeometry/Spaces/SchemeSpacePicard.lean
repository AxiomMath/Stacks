module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtalePicardIsomorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleFunctorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation

/-!
# The Picard group of a scheme read as an algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let `h_U` be
the algebraic space it represents (`AlgebraicGeometry.schemeSpace U`).  The comparison
`𝓕 ↦ 𝓕^a` from `𝒪_T`-modules to `𝒪`-modules on the small étale site of `h_U` — the associated
module of Stacks 03DU (4) on the small étale site of `T`, transported along the identification
of that site with the small étale site of `h_U` — carries invertible modules to invertible
modules, and induces an isomorphism of Picard groups `Pic(h_U) ≅ Pic(T)`, natural in `U`.

## Main definitions

* `AlgebraicGeometry.Space.schemeSpaceModule`: the comparison `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.Space.schemeSpacePicardHom`: the induced homomorphism `Pic(T) ⟶ Pic(h_U)`.
* `AlgebraicGeometry.Space.picardGroupSchemeSpaceEquiv`: **`Pic(h_U) ≅ Pic(T)`.**

## Main results

* `AlgebraicGeometry.Space.picardGroupSchemeSpaceEquiv_picardClass`: the isomorphism sends the
  class of `𝓛^a` to the class of `𝓛`.
* `AlgebraicGeometry.Space.picardGroupSchemeSpaceEquiv_picardPullback`: it intertwines pullback
  of Picard classes along `h_g : h_{U'} ⟶ h_U` with pullback along `g : T' ⟶ T`.
* `AlgebraicGeometry.Space.picardGroupSchemeSpaceEquiv_picardClass_eq_zero_iff`: the image of the
  class of an invertible module `M` on `h_U` vanishes exactly when `M` is trivial.
* `AlgebraicGeometry.Space.exists_picardClassOf_eq_picardGroupSchemeSpaceEquiv_of_ne_zero`: a
  nonzero section of an invertible module on `h_U` gives a nonzero section of an invertible
  `𝒪_T`-module with the corresponding class.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison `𝓕 ↦ 𝓕^a` from `𝒪_T`-modules on the scheme `T` underlying `U` to
`𝒪`-modules on the small étale site of the algebraic space `h_U`: the associated module on the
small étale site of `T`, transported along the identification of the two small étale sites.
On quasi-coherent modules it is `AlgebraicGeometry.Space.representedModuleFunctor`. -/
abbrev schemeSpaceModule (U : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules ⥤
      Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2 :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor

/-- On quasi-coherent modules the comparison is `representedModuleFunctor`. -/
theorem representedModuleFunctor_obj_eq (U : BigFppfOver B S hS)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (representedModuleFunctor B S hS U).obj M = (schemeSpaceModule U).obj M.obj := rfl

/-- **The comparison carries an invertible `𝒪_T`-module to an invertible module on `h_U`.** -/
theorem isInvertibleModule_schemeSpaceModule_obj (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L) :
    IsInvertibleModule (schemeSpace U) ((schemeSpaceModule U).obj L) :=
  isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule B S hS U L hL

/-- An invertible `𝒪_T`-module is quasi-coherent. -/
theorem isQuasicoherent_of_isInvertible_schemeSpace (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L) :
    SheafOfModules.IsQuasicoherent (R := ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) L :=
  _root_.AlgebraicGeometry.SmallEtale.zariskiIsQuasicoherent_of_isInvertible _ L hL

/-- **Every invertible module on `h_U` is the comparison of an invertible `𝒪_T`-module.** -/
theorem exists_schemeSpaceModule_obj_iso (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : IsInvertibleModule (schemeSpace U) M) :
    ∃ (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
      (_ : Stacks.SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf
          ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L),
      Nonempty ((schemeSpaceModule U).obj L ≅ M) := by
  obtain ⟨N, ⟨e⟩⟩ := exists_representedModuleFunctor_iso B S hS U M
    (isQuasicoherentOnSite_of_isInvertibleModule (schemeSpace U) M hM)
  have hN : IsInvertibleModule (schemeSpace U) ((schemeSpaceModule U).obj N.obj) :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
      (((Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit M).1 hM).imp
        fun P ⟨f⟩ => ⟨((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app P ≪≫ f⟩)
  exact ⟨N.obj, isInvertible_of_isInvertible_representedAssociatedModule B S hS U N.obj
    N.property hN, ⟨e⟩⟩

/-- The comparison reflects isomorphisms between invertible modules: two invertible
`𝒪_T`-modules with isomorphic comparisons are isomorphic, the comparison being fully faithful on
quasi-coherent modules. -/
theorem nonempty_iso_of_schemeSpaceModule_obj_iso (U : BigFppfOver B S hS)
    (L N : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L)
    (hN : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) N)
    (e : (schemeSpaceModule U).obj L ≅ (schemeSpaceModule U).obj N) : Nonempty (L ≅ N) :=
  ⟨(ObjectProperty.ι _).mapIso ((representedModuleFunctorFullyFaithful B S hS U).preimageIso
    (X := ⟨L, isQuasicoherent_of_isInvertible_schemeSpace U L hL⟩)
    (Y := ⟨N, isQuasicoherent_of_isInvertible_schemeSpace U N hN⟩) e)⟩

/-! ### The comparison of Picard groups -/

/-- The map `Pic(T) ⟶ Pic(h_U)` on classes, computed on the chosen representative. -/
def schemeSpacePicardFun (U : BigFppfOver B S hS)
    (x : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj U)) :
    picardGroup (schemeSpace U) :=
  picardClass (schemeSpace U)
    ((schemeSpaceModule U).obj (Stacks.Picard.picardRepresentative _ x).obj)
    (isInvertibleModule_schemeSpaceModule_obj U _ (Stacks.Picard.picardRepresentative _ x).property)

/-- The map on classes sends the class of `𝓛` to the class of `𝓛^a`. -/
theorem schemeSpacePicardFun_picardClass (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L) :
    schemeSpacePicardFun U (Stacks.SheafOfModules.picardClass _ _ L hL) =
      picardClass (schemeSpace U) ((schemeSpaceModule U).obj L)
        (isInvertibleModule_schemeSpaceModule_obj U L hL) := by
  refine (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨(schemeSpaceModule U).mapIso ?_⟩
  exact ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (Stacks.Picard.classOf_picardRepresentative _
      (Stacks.SheafOfModules.picardClass _ _ L hL))).some

/-- **The homomorphism `Pic(T) ⟶ Pic(h_U)` induced by `𝓕 ↦ 𝓕^a`.**  Additivity is the
compatibility of the comparison with tensor products. -/
def schemeSpacePicardHom (U : BigFppfOver B S hS) :
    Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj U) →+
      picardGroup (schemeSpace U) :=
  AddMonoidHom.mk' (schemeSpacePicardFun U) (by
    intro x y
    obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ x
    obtain ⟨N, hN, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ y
    have := hL
    have := hN
    have hLN := Stacks.SheafOfModules.isInvertible_tensorSheaf
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace)
      L N
    have hLa := isInvertibleModule_schemeSpaceModule_obj U L hL
    have hNa := isInvertibleModule_schemeSpaceModule_obj U N hN
    have := hLa
    have := hNa
    have hLNa := Stacks.SheafOfModules.isInvertible_tensorSheaf
      (structureSheaf B S hS (schemeSpace U).1 (schemeSpace U).2).obj
      (structureRingPresheaf_isSheaf B S hS (schemeSpace U).1 (schemeSpace U).2)
      ((schemeSpaceModule U).obj L) ((schemeSpaceModule U).obj N)
    refine (congrArg (schemeSpacePicardFun U)
      (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L N hL hN hLN)).trans ?_
    refine (schemeSpacePicardFun_picardClass U _ hLN).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·) (schemeSpacePicardFun_picardClass U L hL).symm
      (schemeSpacePicardFun_picardClass U N hN).symm)
    refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hLa hNa hLNa).symm
    exact (picardClass_eq_picardClass_iff _ _ _ _ _).2
      ⟨representedAssociatedModuleTensorIso B S hS U L N⟩)

/-- The homomorphism sends the class of `𝓛` to the class of `𝓛^a`. -/
theorem schemeSpacePicardHom_picardClass (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L) :
    schemeSpacePicardHom U (Stacks.SheafOfModules.picardClass _ _ L hL) =
      picardClass (schemeSpace U) ((schemeSpaceModule U).obj L)
        (isInvertibleModule_schemeSpaceModule_obj U L hL) :=
  schemeSpacePicardFun_picardClass U L hL

/-- **The homomorphism `Pic(T) ⟶ Pic(h_U)` is bijective.** -/
theorem bijective_schemeSpacePicardHom (U : BigFppfOver B S hS) :
    Function.Bijective (schemeSpacePicardHom U) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ x
    obtain ⟨N, hN, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ y
    obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1
      ((schemeSpacePicardHom_picardClass U L hL).symm.trans
        (hxy.trans (schemeSpacePicardHom_picardClass U N hN)))
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      (nonempty_iso_of_schemeSpaceModule_obj_iso U L N hL hN e)
  · obtain ⟨M, hM, rfl⟩ := exists_picardClass (schemeSpace U) z
    obtain ⟨L, hL, ⟨e⟩⟩ := exists_schemeSpaceModule_obj_iso U M hM
    exact ⟨_, (schemeSpacePicardHom_picardClass U L hL).trans
      ((picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨e⟩)⟩

/-- **The Picard group of the algebraic space of a scheme is the Picard group of the scheme**:
`Pic(h_U) ≅ Pic(T)`, inverse to the homomorphism induced by `𝓕 ↦ 𝓕^a`. -/
def picardGroupSchemeSpaceEquiv (U : BigFppfOver B S hS) :
    picardGroup (schemeSpace U) ≃+
      Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj U) :=
  (AddEquiv.ofBijective (schemeSpacePicardHom U) (bijective_schemeSpacePicardHom U)).symm

/-- `picardGroupSchemeSpaceEquiv` inverts `schemeSpacePicardHom`. -/
theorem picardGroupSchemeSpaceEquiv_schemeSpacePicardHom (U : BigFppfOver B S hS)
    (x : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj U)) :
    picardGroupSchemeSpaceEquiv U (schemeSpacePicardHom U x) = x :=
  (AddEquiv.ofBijective (schemeSpacePicardHom U)
    (bijective_schemeSpacePicardHom U)).symm_apply_apply x

/-- `schemeSpacePicardHom` inverts `picardGroupSchemeSpaceEquiv`. -/
theorem schemeSpacePicardHom_picardGroupSchemeSpaceEquiv (U : BigFppfOver B S hS)
    (x : picardGroup (schemeSpace U)) :
    schemeSpacePicardHom U (picardGroupSchemeSpaceEquiv U x) = x :=
  (AddEquiv.ofBijective (schemeSpacePicardHom U)
    (bijective_schemeSpacePicardHom U)).apply_symm_apply x

/-- **The isomorphism sends the class of `𝓛^a` to the class of `𝓛`**, at the spelling of
invertibility of `Stacks.SheafOfModules.picardClass`. -/
theorem picardGroupSchemeSpaceEquiv_picardClass' (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) L) :
    picardGroupSchemeSpaceEquiv U (picardClass (schemeSpace U) ((schemeSpaceModule U).obj L)
        (isInvertibleModule_schemeSpaceModule_obj U L hL)) =
      Stacks.SheafOfModules.picardClass _ _ L hL :=
  (congrArg (picardGroupSchemeSpaceEquiv U) (schemeSpacePicardHom_picardClass U L hL).symm).trans
    (picardGroupSchemeSpaceEquiv_schemeSpacePicardHom U _)

/-- **The isomorphism sends the class of `𝓛^a` to the class `picardClassOf T 𝓛` of `𝓛`.** -/
theorem picardGroupSchemeSpaceEquiv_picardClass (U : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L)
    (hLa : IsInvertibleModule (schemeSpace U) ((schemeSpaceModule U).obj L)) :
    picardGroupSchemeSpaceEquiv U (picardClass (schemeSpace U) ((schemeSpaceModule U).obj L) hLa) =
      Stacks.WeilCohomology.picardClassOf _ L hL :=
  picardGroupSchemeSpaceEquiv_picardClass' U L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL)

/-- The isomorphism sends the class of `(representedModuleFunctor B S hS U).obj 𝓛` to the class
`picardClassOf T 𝓛` of the invertible quasi-coherent `𝒪_T`-module `𝓛`. -/
theorem picardGroupSchemeSpaceEquiv_picardClass_representedModuleFunctor
    (U : BigFppfOver B S hS)
    (L : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).presheaf
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L.obj)
    (hLa : IsInvertibleModule (schemeSpace U) ((representedModuleFunctor B S hS U).obj L)) :
    picardGroupSchemeSpaceEquiv U
        (picardClass (schemeSpace U) ((representedModuleFunctor B S hS U).obj L) hLa) =
      Stacks.WeilCohomology.picardClassOf _ L.obj hL :=
  picardGroupSchemeSpaceEquiv_picardClass U L.obj hL hLa

/-! ### Naturality -/

/-- **Naturality of `Pic(h_U) ≅ Pic(T)`**: pullback of Picard classes along the morphism of
algebraic spaces `h_g : h_U ⟶ h_V` induced by `g : U ⟶ V` corresponds to pullback of Picard
classes along the underlying morphism of schemes. -/
theorem picardGroupSchemeSpaceEquiv_picardPullback {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : picardGroup (schemeSpace V)) :
    picardGroupSchemeSpaceEquiv U (picardPullback (schemeSpaceMap g) x) =
      Stacks.Picard.schemePullbackClassHom ((BigFppfOver.toScheme B S hS).map g)
        (picardGroupSchemeSpaceEquiv V x) := by
  obtain ⟨y, rfl⟩ := (bijective_schemeSpacePicardHom V).2 x
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ y
  have hfL := Stacks.RingedSpace.modulePullback_isInvertible_of
    ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom L hL
  have h₁ : picardPullback (schemeSpaceMap g)
      (schemeSpacePicardHom V (Stacks.SheafOfModules.picardClass _ _ L hL)) =
      schemeSpacePicardHom U (Stacks.SheafOfModules.picardClass _ _
        ((Stacks.RingedSpace.pullbackFunctor
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj L) hfL) :=
    (congrArg (picardPullback (schemeSpaceMap g)) (schemeSpacePicardHom_picardClass V L hL)).trans
      ((picardPullback_picardClass _ _ _).trans
        (((picardClass_eq_picardClass_iff _ _ _ _ _).2
          ⟨(representedModuleFunctorPullbackIso B S hS g).app
            ⟨L, isQuasicoherent_of_isInvertible_schemeSpace V L hL⟩⟩).trans
          (schemeSpacePicardHom_picardClass U _ hfL).symm))
  refine (congrArg (picardGroupSchemeSpaceEquiv U) h₁).trans ?_
  refine (picardGroupSchemeSpaceEquiv_schemeSpacePicardHom U _).trans ?_
  refine Eq.trans ?_ (congrArg (Stacks.Picard.schemePullbackClassHom
    ((BigFppfOver.toScheme B S hS).map g))
      (picardGroupSchemeSpaceEquiv_schemeSpacePicardHom V _).symm)
  exact (Stacks.Picard.pullbackClass_classOf _ L hL).symm

/-! ### Triviality -/

/-- **The image in `Pic(T)` of the class of an invertible module `M` on `h_U` vanishes exactly
when `M` is isomorphic to the structure sheaf.** -/
theorem picardGroupSchemeSpaceEquiv_picardClass_eq_zero_iff (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : IsInvertibleModule (schemeSpace U) M) :
    picardGroupSchemeSpaceEquiv U (picardClass (schemeSpace U) M hM) = 0 ↔
      Nonempty (M ≅ SheafOfModules.unit _) := by
  rw [AddEquivClass.map_eq_zero_iff]
  exact picardClass_eq_zero_iff (schemeSpace U) M hM

/-- The vanishing criterion at the spelling `AlgebraicGeometry.SheafOfModules.IsTrivial` of
triviality. -/
theorem picardGroupSchemeSpaceEquiv_picardClass_eq_zero_iff_isTrivial (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : IsInvertibleModule (schemeSpace U) M) :
    picardGroupSchemeSpaceEquiv U (picardClass (schemeSpace U) M hM) = 0 ↔
      AlgebraicGeometry.SheafOfModules.IsTrivial (structureCommRings B S hS (schemeSpace U))
        (structureRingSheaf B S hS (schemeSpace U)).property M :=
  picardGroupSchemeSpaceEquiv_picardClass_eq_zero_iff U M hM

/-! ### Sections -/

/-- **A nonzero section of an invertible module on `h_U` comes from a nonzero section of an
invertible `𝒪_T`-module with the corresponding class.**  The module is `𝓛` with `𝓛^a ≅ M`, and
the section is the preimage of the given one under the comparison, which is fully faithful on
quasi-coherent modules and carries `𝒪_T` to the structure sheaf of `h_U`.

The source of `t` is `𝒪_T` read as an object of `AlgebraicGeometry.Scheme.Modules` (through
`id`), so that `t` is a morphism of that category and `t ≠ 0` refers to its zero morphism: with
the source typed as a sheaf of modules and the target as an object of `Scheme.Modules`, instance
search does not find the zero morphism, `Scheme.Modules` being a definition rather than an
abbreviation. -/
theorem exists_picardClassOf_eq_picardGroupSchemeSpaceEquiv_of_ne_zero
    (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hM : IsInvertibleModule (schemeSpace U) M) (s : SheafOfModules.unit _ ⟶ M) (hs : s ≠ 0) :
    ∃ (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B S hS).obj U).presheaf
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.2 L),
      Stacks.WeilCohomology.picardClassOf _ L hL =
          picardGroupSchemeSpaceEquiv U (picardClass (schemeSpace U) M hM) ∧
        ∃ t : @id ((BigFppfOver.toScheme B S hS).obj U).Modules
          (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) ⟶ L,
          t ≠ 0 := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_schemeSpaceModule_obj_iso U M hM
  let L' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory :=
    ⟨L, isQuasicoherent_of_isInvertible_schemeSpace U L hL⟩
  let O' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit _,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _⟩
  let hF := representedModuleFunctorFullyFaithful B S hS U
  have := hF.full
  have : (representedModuleFunctor B S hS U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_full _
  let ι : (representedModuleFunctor B S hS U).obj O' ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O) :=
    representedAssociatedModuleUnitIso B S hS U
  let φ : (representedModuleFunctor B S hS U).obj O' ⟶ (representedModuleFunctor B S hS U).obj L' :=
    ι.hom ≫ s ≫ e.inv
  have hφ : φ ≠ 0 := by
    intro h
    apply hs
    have hs' : s = ι.inv ≫ φ ≫ e.hom := by
      simp [φ]
    rw [hs', h]
    simp
  refine ⟨L, Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL, ?_,
    (hF.preimage φ).hom, ?_⟩
  · exact (picardGroupSchemeSpaceEquiv_picardClass U L _
      (isInvertibleModule_schemeSpaceModule_obj U L hL)).symm.trans
        (congrArg _ ((picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨e⟩))
  · intro h0
    apply hφ
    have hp : hF.preimage φ = 0 := ObjectProperty.hom_ext _ (by exact h0)
    rw [← hF.map_preimage φ, hp]
    exact Functor.map_zero _ _ _

end AlgebraicGeometry.Space

end
