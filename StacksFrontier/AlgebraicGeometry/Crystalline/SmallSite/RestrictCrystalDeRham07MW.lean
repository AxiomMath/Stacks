module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSectionsMoore07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictCrysAffineConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Transport07LMReduction

/-!
# The de Rham complex of a crystal restricts to the de Rham complex of the restriction

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], opens `W ⊆ S` and
`V ⊆ X` with `V` mapping into `W`, and a crystal in quasi-coherent modules `F` on `Cris(X/S)`.
Its restriction `F'` to `Cris(V/S|_W)` is again a crystal in quasi-coherent modules, and this
module proves that **the restriction to `Cris(V/S|_W)` of the de Rham complex
`F ⊗ Ω^*_{X/S}` of [Stacks, Tag 07LM] is the de Rham complex `F' ⊗ Ω^*_{V/S|_W}`, differentials
included**, as an isomorphism of `ℕ`-indexed cochain complexes of abelian sheaves on
`Cris(V/S|_W)`.

## The argument

The termwise isomorphisms are `...SmallSite.smallExtendAbelianRestrictionTensorSheafIso`, built
from the comparison `Ω_{V/S|_W} ≅ Ω_{X/S}|` of `...SmallSite.smallExtendCrysDifferentialsIso`.
Both differentials are sheafifications of morphisms determined on the cover-dense
affine-over-affine objects (`...SmallSite.crystalDeRhamDifferential_app_toSheafify`).  An
affine-over-affine object of `Cris(V/S|_W)` extends to one of `Cris(X/S)`
(`AffineOverAffineCrystallineThickening.smallExtend`), and there the two differentials, the
extensions `m ⊗ ω ↦ ∇ m ∧ ω + m ⊗ d ω` of the canonical connections, agree under the termwise
comparison: this is `...SmallSite.smallExtendTensorMap_extDiff` of
`SmallSite/RestrictCrysAffineConnection.lean`.  Restriction commutes with sheafification
([Stacks, Tag 00XR], `...SmallSite.toSheafify_smallExtendAbelianRestrictionCompPresheafToSheafIso`),
which transports the square of presheaves to the square of sheaves.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isQuasicoherentOnSite_smallExtendSheafRestriction` — the restriction of a crystal in
  quasi-coherent modules is quasi-coherent on the restricted site.
* `smallExtendCrystalDeRham_comm` — the termwise isomorphisms commute with the differentials.
* `smallExtendCrystalDeRhamIso` — **the isomorphism of complexes.**

## References

* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W) {F : SheafOfModules.{u} (structureSheaf S)}
  (hF : F.IsQuasicoherentOnSite)

include hF in
/-- **The restriction to `Cris(V/S|_W)` of a quasi-coherent sheaf of modules on `Cris(X/S)` is
quasi-coherent**: such a sheaf is a crystal ([Stacks, Tag 07IT],
`...SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`), and the restriction of a crystal in
quasi-coherent modules is one
(`...SmallSite.isQuasiCoherentCrystal_smallExtendSheafRestriction`). -/
theorem isQuasicoherentOnSite_smallExtendSheafRestriction :
    (smallExtendSheafRestriction S W V hVW F).IsQuasicoherentOnSite :=
  (isQuasiCoherentCrystal_smallExtendSheafRestriction S W V hVW F
    ⟨hF, isSheafCrystal_of_isQuasicoherentOnSite F hF⟩).1

/-! ### Affine-over-affine objects -/

/-- **The extension to `Cris(X/S)` of an affine-over-affine object of `Cris(V/S|_W)` is
affine-over-affine**: the ambient scheme is unchanged, and it lies over the image in `S` of the
affine open of `S|_W` over which the object lies, an affine open of `S`. -/
def AffineOverAffineCrystallineThickening.smallExtend
    (B : AffineOverAffineCrystallineThickening (restrict S W V hVW)) :
    AffineOverAffineCrystallineThickening S :=
  ⟨(GlobalCrystallineSituation.smallExtend S W V hVW).obj B.obj, B.property.1,
    ⟨(restrictSι S W V hVW).hom ''ᵁ B.baseOpen,
      B.isAffineOpen_baseOpen.image_of_isOpenImmersion _, by
        change (⊤ : B.obj.obj.thickening.target.scheme.Opens) ≤
          (B.obj.obj.toBase.hom ≫ (restrictSι S W V hVW).hom) ⁻¹ᵁ
            ((restrictSι S W V hVW).hom ''ᵁ B.baseOpen)
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
        exact B.top_le_preimage_baseOpen⟩⟩

/-- The underlying object of the extension of an affine-over-affine object. -/
@[simp]
theorem AffineOverAffineCrystallineThickening.smallExtend_obj
    (B : AffineOverAffineCrystallineThickening (restrict S W V hVW)) :
    (AffineOverAffineCrystallineThickening.smallExtend W V hVW B).obj =
      (GlobalCrystallineSituation.smallExtend S W V hVW).obj B.obj := rfl

/-! ### The termwise comparisons -/

variable (F) in
/-- The comparison of the degree-`i` coefficient presheaves of modules,
`...SmallSite.smallExtendModuleRestrictionTensorIso` at the comparison of differentials. -/
abbrev smallExtendTensorModuleIso (i : ℕ) :
    (smallExtendModuleRestriction S W V hVW).obj (tensorDifferentialForms
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ≅
      tensorDifferentialForms ((smallExtendSheafRestriction S W V hVW F).val :
        PresheafOfModules.{u}
          (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat)) i :=
  smallExtendModuleRestrictionTensorIso S W V hVW (smallExtendCrysDifferentialsIso S W V hVW)
    F.val i

variable (F) in
/-- The comparison of the degree-`i` coefficient abelian presheaves. -/
abbrev smallExtendTensorPresheafIso (i : ℕ) :
    (GlobalCrystallineSituation.smallExtend S W V hVW).op ⋙ tensorFormsULift F i ≅
      tensorFormsULift (smallExtendSheafRestriction S W V hVW F) i :=
  Functor.isoWhiskerRight ((PresheafOfModules.toPresheaf _).mapIso
    (smallExtendTensorModuleIso W V hVW F i)) AddCommGrpCat.uliftFunctor.{u + 1, u}

variable (F) in
/-- **The termwise comparison of the de Rham complexes**: the restriction of
`F ⊗ Ω^i_{X/S}` is `F' ⊗ Ω^i_{V/S|_W}`, `...SmallSite.smallExtendAbelianRestrictionTensorSheafIso`
at the comparison of differentials. -/
abbrev smallExtendTensorSheafIso (i : ℕ) :
    (smallExtendAbelianRestriction S W V hVW).obj (tensorDifferentialFormsSheaf F i) ≅
      tensorDifferentialFormsSheaf (smallExtendSheafRestriction S W V hVW F) i :=
  smallExtendAbelianRestrictionTensorSheafIso S W V hVW F (smallExtendSheafRestriction S W V hVW F)
    i (smallExtendTensorModuleIso W V hVW F i)

variable (F) in
/-- **The termwise comparison is compatible with the sheafification units**: restricting the unit
of `F ⊗ Ω^i_{X/S}` and following the comparison is the comparison of presheaves followed by the
unit of `F' ⊗ Ω^i_{V/S|_W}`. -/
theorem whiskerLeft_toSheafify_smallExtendTensorSheafIso (i : ℕ) :
    Functor.whiskerLeft (GlobalCrystallineSituation.smallExtend S W V hVW).op
        (toSheafify (smallTopology S) (tensorFormsULift F i)) ≫
        (smallExtendTensorSheafIso W V hVW F i).hom.hom =
      (smallExtendTensorPresheafIso W V hVW F i).hom ≫
        toSheafify (smallTopology (restrict S W V hVW))
          (tensorFormsULift (smallExtendSheafRestriction S W V hVW F) i) := by
  have h0 : (smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).hom.app
        (tensorFormsULift F i) ≫ (smallExtendTensorSheafIso W V hVW F i).hom =
      (presheafToSheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1}).map
        (smallExtendTensorPresheafIso W V hVW F i).hom :=
    Iso.hom_inv_id_assoc ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).app
      (tensorFormsULift F i)) _
  have h1 : ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).hom.app
        (tensorFormsULift F i)).hom ≫ (smallExtendTensorSheafIso W V hVW F i).hom.hom =
      ((presheafToSheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1}).map
        (smallExtendTensorPresheafIso W V hVW F i).hom).hom :=
    congrArg (fun f ↦ f.hom) h0
  exact (congrArg (· ≫ (smallExtendTensorSheafIso W V hVW F i).hom.hom)
    (toSheafify_smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW
      (tensorFormsULift F i)).symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (toSheafify (smallTopology (restrict S W V hVW))
          ((GlobalCrystallineSituation.smallExtend S W V hVW).op ⋙ tensorFormsULift F i) ≫ ·)
            h1).trans (toSheafify_naturality _ _).symm))

/-- The comparison of presheaves of modules on sections over an object, on a pure tensor. -/
theorem tensorFormsSectionsEquiv_smallExtendTensorModuleIso_tmul (i : ℕ)
    (B : CrystallineThickening (restrict S W V hVW))
    (m : F.val.obj (op ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)))
    (ω : (crysDifferentialForms S i).obj
      (op ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B))) :
    tensorFormsSectionsEquiv (smallExtendSheafRestriction S W V hVW F) i B
        ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B) (m ⊗ₜ ω)) =
      smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B i)
        (tensorFormsSectionsEquiv F i ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)
          (m ⊗ₜ ω)) :=
  rfl

/-- **The comparison of presheaves of modules on sections over an object**, read through the
identifications of sections with tensor products: it is `smallExtendTensorMap` at the comparison
of forms `smallExtendFormsMap`. -/
theorem tensorFormsSectionsEquiv_smallExtendTensorModuleIso (i : ℕ)
    (B : CrystallineThickening (restrict S W V hVW))
    (y : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj
          (op ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)))) :
    tensorFormsSectionsEquiv (smallExtendSheafRestriction S W V hVW F) i B
        ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B) y) =
      smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B i)
        (tensorFormsSectionsEquiv F i ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)
          y) := by
  induction y using TensorProduct.induction_on with
  | tmul m ω => exact tensorFormsSectionsEquiv_smallExtendTensorModuleIso_tmul W V hVW i B m ω
  | zero =>
    exact ((congrArg (tensorFormsSectionsEquiv (smallExtendSheafRestriction S W V hVW F) i B)
      (map_zero ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B)).hom)).trans
        (map_zero _)).trans ((congrArg (smallExtendTensorMap W V hVW F B
          (smallExtendFormsMap W V hVW B i)) (map_zero (tensorFormsSectionsEquiv F i
            ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)))).trans (map_zero _)).symm
  | add a b ha hb =>
    exact ((congrArg (tensorFormsSectionsEquiv (smallExtendSheafRestriction S W V hVW F) i B)
      (map_add ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B)).hom a b)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) ha hb))).trans
      ((congrArg (smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B i))
        (map_add (tensorFormsSectionsEquiv F i
          ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)) a b)).trans
        (map_add _ _ _)).symm

include hF

/-- **The differentials over an affine-over-affine object agree under the termwise
comparison**: the differential of `F'` at `B` is that of `F` at the extension of `B`. -/
theorem smallExtendTensorModuleIso_affineDeRhamDifferential (i : ℕ)
    (B : AffineOverAffineCrystallineThickening (restrict S W V hVW))
    (y : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj
          (op ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B.obj)))) :
    (smallExtendTensorModuleIso W V hVW F (i + 1)).hom.app (op B.obj)
        (affineDeRhamDifferential hF i (AffineOverAffineCrystallineThickening.smallExtend W V hVW B)
          y) =
      affineDeRhamDifferential (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i B
        ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B.obj) y) := by
  refine (tensorFormsSectionsEquiv (smallExtendSheafRestriction S W V hVW F) (i + 1)
    B.obj).injective ?_
  refine (tensorFormsSectionsEquiv_smallExtendTensorModuleIso W V hVW (i + 1) B.obj _).trans ?_
  refine (congrArg
    (smallExtendTensorMap W V hVW F B.obj (smallExtendFormsMap W V hVW B.obj (i + 1)))
    (tensorFormsSectionsEquiv_affineDeRhamDifferential hF i
      (AffineOverAffineCrystallineThickening.smallExtend W V hVW B) y)).trans ?_
  refine (smallExtendTensorMap_extDiff W V hVW F B.obj B.top_le_preimage_baseOpen
    B.isAffineOpen_baseOpen _ _ _
    (bijective_crysExtensionSectionsMap_affine
      (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) B) i _).trans ?_
  refine (congrArg (extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
    (bijective_crysExtensionSectionsMap_affine
      (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) B) i)
    (tensorFormsSectionsEquiv_smallExtendTensorModuleIso W V hVW i B.obj y).symm).trans ?_
  exact (tensorFormsSectionsEquiv_affineDeRhamDifferential
    (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i B _).symm

/-! ### The commuting squares and the isomorphism of complexes -/

omit hF in
/-- The lift of a morphism of abelian groups to the coefficient universe, on a lifted element. -/
theorem uliftFunctor_map_up {A A' : AddCommGrpCat.{u}} (f : A ⟶ A') (a : A) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map f (ULift.up a) = ULift.up (f a) := rfl

omit hF in
/-- The underlying morphism of abelian presheaves of a morphism of presheaves of modules, on
sections. -/
theorem toPresheaf_map_app_apply_aux {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (X : Cᵒᵖ) (m : M.obj X) :
    ((PresheafOfModules.toPresheaf R).map f).app X m = f.app X m := rfl

omit hF in
variable (F) in
/-- The comparison of abelian presheaves on a section lifted to the coefficient universe. -/
theorem smallExtendTensorPresheafIso_hom_app_up (i : ℕ)
    (B : CrystallineThickening (restrict S W V hVW))
    (z : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj
          (op ((GlobalCrystallineSituation.smallExtend S W V hVW).obj B)))) :
    (smallExtendTensorPresheafIso W V hVW F i).hom.app (op B) (ULift.up z) =
      ULift.up ((smallExtendTensorModuleIso W V hVW F i).hom.app (op B) z) :=
  (uliftFunctor_map_up _ _).trans (congrArg ULift.up (toPresheaf_map_app_apply_aux _ _ _))

omit hF in
/-- The differential on the affine-over-affine subsite on a section lifted to the coefficient
universe. -/
theorem affineDeRhamNat_app_up {S' : GlobalCrystallineSituation.{u}}
    {F' : SheafOfModules.{u} (structureSheaf S')} (hF' : F'.IsQuasicoherentOnSite) (i : ℕ)
    (B : AffineOverAffineCrystallineThickening S')
    (x : ↥((tensorDifferentialForms (F'.val : PresheafOfModules.{u}
      (structurePresheaf S' ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj))) :
    (affineDeRhamNat hF' i).app (op B) (ULift.up x) =
      ULift.up (affineDeRhamDifferential hF' i B x) := rfl

/-- **The differentials on the affine-over-affine subsites agree under the comparison of
presheaves**: the square of abelian groups over an affine-over-affine object `B` of
`Cris(V/S|_W)`, with the differential of `F` at the extension of `B` and that of `F'` at `B`. -/
theorem smallExtendCrystalDeRham_affine_comm (i : ℕ)
    (B : AffineOverAffineCrystallineThickening (restrict S W V hVW)) :
    (affineDeRhamNat hF i).app (op (AffineOverAffineCrystallineThickening.smallExtend W V hVW B)) ≫
        (smallExtendTensorPresheafIso W V hVW F (i + 1)).hom.app (op B.obj) =
      (smallExtendTensorPresheafIso W V hVW F i).hom.app (op B.obj) ≫
        (affineDeRhamNat (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i).app
          (op B) := by
  ext ⟨x⟩
  exact (congrArg (ConcreteCategory.hom ((smallExtendTensorPresheafIso W V hVW F (i + 1)).hom.app
      (op B.obj))) (affineDeRhamNat_app_up hF i
        (AffineOverAffineCrystallineThickening.smallExtend W V hVW B) x)).trans
    ((smallExtendTensorPresheafIso_hom_app_up W V hVW F (i + 1) B.obj _).trans
      ((congrArg ULift.up
        (smallExtendTensorModuleIso_affineDeRhamDifferential W V hVW hF i B x)).trans
        ((affineDeRhamNat_app_up (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i
          B _).symm.trans (congrArg (ConcreteCategory.hom ((affineDeRhamNat
            (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i).app (op B)))
            (smallExtendTensorPresheafIso_hom_app_up W V hVW F i B.obj x).symm))))

/-- The comparison of the presheaf-level differentials: restricting the differential of `F`,
viewed as a morphism from the presheaf `F ⊗ Ω^i_{X/S}` to the sheaf `F ⊗ Ω^{i+1}_{X/S}`, and
following the termwise comparison is the comparison of presheaves followed by the differential of
`F'`. -/
theorem smallExtendCrystalDeRham_presheaf_comm (i : ℕ) :
    Functor.whiskerLeft (GlobalCrystallineSituation.smallExtend S W V hVW).op
        (presheafDeRhamDifferential hF i) ≫ (smallExtendTensorSheafIso W V hVW F (i + 1)).hom.hom =
      (smallExtendTensorPresheafIso W V hVW F i).hom ≫
        presheafDeRhamDifferential (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF)
          i := by
  refine hom_ext_of_app (restrict S W V hVW) fun B ↦ ?_
  have hp := NatTrans.congr_app (sheafHom_restrict_eq S (affineDeRhamToSheaf hF i))
    (op (AffineOverAffineCrystallineThickening.smallExtend W V hVW B))
  have hp' := NatTrans.congr_app (sheafHom_restrict_eq (restrict S W V hVW)
    (affineDeRhamToSheaf (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i)) (op B)
  have hE := NatTrans.congr_app (whiskerLeft_toSheafify_smallExtendTensorSheafIso W V hVW F (i + 1))
    (op B.obj)
  have hA := smallExtendCrystalDeRham_affine_comm W V hVW hF i B
  exact (congrArg (· ≫ (smallExtendTensorSheafIso W V hVW F (i + 1)).hom.hom.app (op B.obj))
    hp).trans ((Category.assoc _ _ _).trans ((congrArg ((affineDeRhamNat hF i).app
      (op (AffineOverAffineCrystallineThickening.smallExtend W V hVW B)) ≫ ·) hE).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (toSheafify
          (smallTopology (restrict S W V hVW))
          (tensorFormsULift (smallExtendSheafRestriction S W V hVW F) (i + 1))).app (op B.obj))
            hA).trans ((Category.assoc _ _ _).trans
              (congrArg ((smallExtendTensorPresheafIso W V hVW F i).hom.app (op B.obj) ≫ ·)
                hp'.symm))))))

/-- **The termwise comparisons commute with the differentials**: restricting the differential of
the de Rham complex of `F` and following the comparison is the comparison followed by the
differential of the de Rham complex of the restriction `F'`. -/
theorem smallExtendCrystalDeRham_comm (i : ℕ) :
    (smallExtendAbelianRestriction S W V hVW).map (crystalDeRhamDifferential hF i) ≫
        (smallExtendTensorSheafIso W V hVW F (i + 1)).hom =
      (smallExtendTensorSheafIso W V hVW F i).hom ≫
        crystalDeRhamDifferential (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF)
          i := by
  have H := smallExtendCrystalDeRham_presheaf_comm W V hVW hF i
  refine (cancel_epi ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).app
    (tensorFormsULift F i)).hom).1 ?_
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology (restrict S W V hVW)) _ _
    (tensorDifferentialFormsSheaf (smallExtendSheafRestriction S W V hVW F) (i + 1)).property ?_)
  have hT := toSheafify_smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW
    (tensorFormsULift F i)
  have hL : (toSheafify (smallTopology (restrict S W V hVW))
        ((GlobalCrystallineSituation.smallExtend S W V hVW).op ⋙ tensorFormsULift F i) ≫
      ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).hom.app
        (tensorFormsULift F i)).hom) ≫
        (Functor.whiskerLeft (GlobalCrystallineSituation.smallExtend S W V hVW).op
          (crystalDeRhamDifferential hF i).hom ≫
        (smallExtendTensorSheafIso W V hVW F (i + 1)).hom.hom) =
      Functor.whiskerLeft (GlobalCrystallineSituation.smallExtend S W V hVW).op
        (presheafDeRhamDifferential hF i) ≫ (smallExtendTensorSheafIso W V hVW F (i + 1)).hom.hom :=
    (congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (smallExtendTensorSheafIso W V hVW F (i + 1)).hom.hom)
        ((Functor.whiskerLeft_comp _ _ _).symm.trans
          (congrArg (Functor.whiskerLeft (GlobalCrystallineSituation.smallExtend S W V hVW).op)
            (toSheafify_crystalDeRhamDifferential hF i)))))
  have hR : (toSheafify (smallTopology (restrict S W V hVW))
        ((GlobalCrystallineSituation.smallExtend S W V hVW).op ⋙ tensorFormsULift F i) ≫
      ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).hom.app
        (tensorFormsULift F i)).hom) ≫ ((smallExtendTensorSheafIso W V hVW F i).hom.hom ≫
        (crystalDeRhamDifferential (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF)
          i).hom) =
      (smallExtendTensorPresheafIso W V hVW F i).hom ≫
        presheafDeRhamDifferential (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF)
          i :=
    (congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (crystalDeRhamDifferential
          (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i).hom)
        (whiskerLeft_toSheafify_smallExtendTensorSheafIso W V hVW F i)).trans
        ((Category.assoc _ _ _).trans (congrArg ((smallExtendTensorPresheafIso W V hVW F i).hom ≫ ·)
          (toSheafify_crystalDeRhamDifferential
            (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF) i)))))
  exact hL.trans (H.trans hR.symm)

/-- **Stacks Project, Tag 07MW, part (3), the restriction of the de Rham complex.**  The
restriction to `Cris(V/S|_W)` of the de Rham complex `F ⊗ Ω^*_{X/S}` of a crystal in
quasi-coherent modules `F` on `Cris(X/S)` ([Stacks, Tag 07LM]) is the de Rham complex
`F' ⊗ Ω^*_{V/S|_W}` of its restriction `F'`, as an isomorphism of `ℕ`-indexed cochain complexes of
abelian sheaves on `Cris(V/S|_W)`: termwise it is `smallExtendTensorSheafIso`, and it commutes with
the differentials by `smallExtendCrystalDeRham_comm`. -/
def smallExtendCrystalDeRhamIso :
    ((smallExtendAbelianRestriction S W V hVW).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (crystalDeRhamSheafData hF).natComplex ≅
      (crystalDeRhamSheafData
        (isQuasicoherentOnSite_smallExtendSheafRestriction W V hVW hF)).natComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ smallExtendTensorSheafIso W V hVW F i) (by
    rintro i _ rfl
    simp only [Functor.mapHomologicalComplex_obj_d, CrystalDeRhamSheafData.natComplex,
      CochainComplex.of_d]
    exact (smallExtendCrystalDeRham_comm W V hVW hF i).symm)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
