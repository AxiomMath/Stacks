module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.SchemeTheoreticImage

/-!
# The ideal sheaf of the scheme-theoretic image of a quasi-compact morphism

Let `f : X ⟶ Y` be a quasi-compact morphism of schemes. The kernel of the canonical map
`𝒪_Y ⟶ f_* 𝒪_X` of `𝒪_Y`-modules is quasi-coherent, so it cuts out a closed subscheme of `Y`:
the scheme-theoretic image of `f`. The construction is compatible with restriction to an open
subscheme of `Y`.

## Main definitions

* `AlgebraicGeometry.imageMorphismRestrictIso`: the scheme-theoretic image of `f ∣_ U` is
  canonically the intersection of the scheme-theoretic image of `f` with `U`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit`: the kernel of
  `𝒪_Y ⟶ f_* 𝒪_X` is quasi-coherent.
* `AlgebraicGeometry.ker_morphismRestrict_eq_comap`: the ideal sheaf of the image of `f ∣_ U`
  is the restriction to `U` of the ideal sheaf of the image of `f`.
* `AlgebraicGeometry.imageMorphismRestrictIso_hom_fst`: that canonical identification respects
  the two embeddings into `U`.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

add_to_stacks 01R8 "part (2): image as a closed subscheme" AlgebraicGeometry.Scheme.Hom.image
add_to_ega "I 9.5.1" AlgebraicGeometry.Scheme.Hom.image
add_to_ega "I 9.5.2" AlgebraicGeometry.Scheme.Hom.image
add_to_ega "I 9.5.3" AlgebraicGeometry.Scheme.Hom.image
add_to_ega "IV 2.3.2" AlgebraicGeometry.Scheme.Hom.image
add_to_stacks 01R8 "part (2): its ideal on affine opens" AlgebraicGeometry.Scheme.Hom.ker_apply
add_to_sga "3 VIIA 1.3" "special case" AlgebraicGeometry.Scheme.Hom.ker_apply
add_to_stacks 01R8 "part (4): dense underlying image" AlgebraicGeometry.Scheme.Hom.support_ker
add_to_ega "I 9.5.4" "partial" AlgebraicGeometry.Scheme.Hom.support_ker
add_to_stacks 01R8 "part (4): dominance"
  AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact
add_to_ega "I 9.5.4" "partial" AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact

/-- If every map on sections of `f` is injective, then `𝒪_Y ⟶ f_* 𝒪_X` is a monomorphism. -/
private lemma mono_unitToPushforwardObjUnit_of_app_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U, Function.Injective (f.app U)) :
    Mono (C := Y.Modules) (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let F := Scheme.Modules.toPresheaf Y
  let φ := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : ∀ U, Mono ((F.map φ).app U) := fun U ↦
    (AddCommGrpCat.mono_iff_injective _).2 fun _ _ hst ↦ hf U.unop hst
  exact F.mono_of_mono_map (NatTrans.mono_of_mono_app (F.map φ))

/-- The map `𝒪_Z ⟶ (f ≫ g)_* 𝒪_X` factors through `𝒪_Z ⟶ g_* 𝒪_Y`. -/
private lemma unitToPushforwardObjUnit_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit X.ringCatSheaf) := by
  ext U
  rfl

/-- If `𝒪_Y ⟶ p_* 𝒪_X` is a monomorphism and `q` is an affine morphism, then the kernel of
`𝒪_Z ⟶ (p ≫ q)_* 𝒪_X` is quasi-coherent. -/
private lemma isQuasicoherent_kernel_unitToPushforwardObjUnit_comp
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) [IsAffineHom q]
    (hp : Mono (C := Y.Modules)
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) :
    (kernel (C := Z.Modules) (SheafOfModules.unitToPushforwardObjUnit
      (p ≫ q).toRingCatSheafHom)).IsQuasicoherent := by
  have hqY : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent := inferInstance
  have hqZ : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent := inferInstance
  have hqc :=
    @Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
      Y Z q (SheafOfModules.unit Y.ringCatSheaf) ‹_› hqY
  have h1 : Mono (C := Z.Modules) ((Scheme.Modules.pushforward q).map
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.pushforward q) inferInstance _ _ _ hp
  have h2 : Mono (C := Z.Modules) ((Scheme.Modules.pushforwardComp p q).hom.app
      (SheafOfModules.unit X.ringCatSheaf)) :=
    @IsIso.mono_of_iso _ _ _ _ _ (NatIso.hom_app_isIso _ _)
  have hm := @mono_comp _ _ _ _ _ _ h1 _ h2
  have e : kernel (C := Z.Modules)
        (SheafOfModules.unitToPushforwardObjUnit (p ≫ q).toRingCatSheafHom) ≅
      kernel (C := Z.Modules)
        (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) :=
    kernelIsoOfEq (unitToPushforwardObjUnit_comp p q) ≪≫
      @kernelCompMono _ _ _ _ _ _ _ _ _ hm
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e.symm <|
    @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel Z _ _
      (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) hqZ hqc

/-- The sheaf of ideals cutting out the image of a quasi-compact morphism is quasi-coherent. -/
@[stacks 01R8 "part (1)"]
public instance isQuasicoherent_kernel_unitToPushforwardObjUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    (kernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).IsQuasicoherent := by
  have hdom : IsSchemeTheoreticallyDominant f.toImage :=
    AlgebraicGeometry.toImage_isSchemeTheoreticallyDominant f
  have key := isQuasicoherent_kernel_unitToPushforwardObjUnit_comp f.toImage f.imageι
    (mono_unitToPushforwardObjUnit_of_app_injective f.toImage
      (fun U ↦ @Scheme.Hom.app_injective _ _ f.toImage hdom inferInstance U))
  rwa [Scheme.Hom.toImage_imageι] at key

/-- Scheme-theoretic images commute with restriction to an open subscheme of the target. -/
@[stacks 01R8 "part (3)"]
public theorem ker_morphismRestrict_eq_comap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).ker = f.ker.comap U.ι := by
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (f ∣_ U)
    (f ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict f U) V

/-- The scheme-theoretic image restricted to an open target is canonically the
intersection of the original image with that open subscheme. -/
@[stacks 01R8 "part (3): canonical closed subscheme", ega "I 9.5.8"]
public noncomputable def imageMorphismRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).image ≅ pullback U.ι f.imageι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (ker_morphismRestrict_eq_comap f U)) ≪≫ f.ker.comapIso U.ι

/-- The canonical identification of restricted images respects their embeddings in `U`. -/
@[stacks 01R8 "part (3): compatibility with inclusions", ega "I 9.5.8" "identification over V"]
public theorem imageMorphismRestrictIso_hom_fst
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (imageMorphismRestrictIso f U).hom ≫ pullback.fst U.ι f.imageι =
      (f ∣_ U).imageι := by
  dsimp [imageMorphismRestrictIso, Scheme.Hom.imageι]
  rw [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  exact eqToHom_subscheme_comp_subschemeι _ _ (ker_morphismRestrict_eq_comap f U)

end AlgebraicGeometry

end
