module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealAffine.BaseChangeSplitting

/-!
# The comparison `p₀^* F_T ⟶ F_{T'}` on ambient schemes, and the two spellings of `D' ⊗_D Mod`

This file holds the comparison map of [Stacks, Tag 07IQ] along the morphism `p₀ : T' ⟶ T` of
ambient schemes, its normalisation on pullbacks of sections and its bijectivity for a crystal,
together with the additive equivalence
`Crystalline.GlobalCrystallineSituation.affineCrossEquiv` between the tensor product `D' ⊗_D Mod`
and the tensor product of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe v₁ u₁ u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-! ### Two further inputs of an affine proof -/

/-- **The sections of `F` over an object and over its restriction to the whole of its ambient
scheme agree.**  The structure morphism of the restriction to `⊤` is an isomorphism of the site,
by `Crystalline.GlobalCrystallineSituation.Thickening.isIso_restrictOpenHom_top`, so restriction
along it is a bijection, with inverse the restriction along its inverse.

This is one of the two bridges between the sections over an object, in which
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap` and
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` are written, and the sections of
the restricted sheaf `F_T` over the whole of `T`, in which the comparison maps of
[Stacks, Tag 07IQ] and the affine base-change comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` are written. -/
theorem bijective_moduleSiteRestrict_restrictOpenHom_top (A : Thickening S) :
    Function.Bijective (moduleSiteRestrict M (A.restrictOpenHom ⊤)) := by
  have := A.isIso_restrictOpenHom_top
  refine Function.bijective_iff_has_inverse.mpr
    ⟨moduleSiteRestrict M (inv (A.restrictOpenHom ⊤)), fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [moduleSiteRestrict_comp, IsIso.inv_hom_id, moduleSiteRestrict_id]
  · rw [moduleSiteRestrict_comp, IsIso.hom_inv_id, moduleSiteRestrict_id]

/-- **The restriction map of `𝒪_{X/S}` along `p₀` is the map on global sections of the morphism
of ambient schemes.**  Both are the comorphism of `p₀ : T' ⟶ T` read over `⊤`; the restriction
map of the structure sheaf of the site is that comorphism by definition, and
`AlgebraicGeometry.Scheme.Hom.appLE` at `⊤, ⊤` is it followed by a restriction map between two
spellings of `⊤`, which is the identity.

Stated pointwise rather than as an equation of ring homomorphisms: `crysSheafRingMap` carries the
ring structure of `Γ(T, 𝒪_T)` through `RingCat` and
`AlgebraicGeometry.Scheme.Hom.appLE` carries it through `CommRingCat`, so the two `RingHom` types
have different instance arguments and the equation of the two maps is not accepted at the
`instances` transparency level, the carriers being definitionally equal but the instance paths
not syntactically so.  The pointwise form is what the comparison of the two `Algebra` structures
on `Γ(T', 𝒪_{T'})` needs.

This is the second bridge the affine proof consumes:
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` extends the scalars along
`AlgebraicGeometry.Scheme.Hom.appLE`, while
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` extends them along
`crysSheafRingMap`. -/
theorem appLE_top_eq_crysSheafRingMap_siteP₀ (A : Thickening S)
    (hVU : (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens) ≤
      (firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤)
    (b : crysSheafRing S A) :
    ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤ hVU).hom b =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b := by
  have hid : ((firstOrderThickeningObject S A).thickening.target.scheme.presheaf.map
        (homOfLE hVU).op :
      Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) ⟶
        Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤)) =
      𝟙 Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) :=
    (firstOrderThickeningObject S A).thickening.target.scheme.presheaf.map_id _
  change ((firstOrderThickeningObject S A).thickening.target.scheme.presheaf.map
      (homOfLE hVU).op).hom
      (((firstOrderThickeningSiteP₀ S A).targetHom.hom.app ⊤).hom b) = _
  exact congrArg (fun k ↦ CommRingCat.Hom.hom k
    (((firstOrderThickeningSiteP₀ S A).targetHom.hom.app ⊤).hom b)) hid

/-! ### The two adjunctions behind the comparison of the two pullbacks -/

/-- **The pullback along the crystalline `f`-map of `p₀`, as a left adjoint on modules over the
structure sheaf of the ambient scheme.**  It is the restriction of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso` followed by
the pullback of sheaves of modules along the `f`-map of [Stacks, Tag 07IQ]. -/
def firstOrderCrysPullbackAdjunction (A : Thickening S) :
    SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).hom ⋙
        SheafOfModules.pullback.{u}
          (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)) ⊣
      SheafOfModules.pushforward.{u}
          (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)) ⋙
        SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).comp
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)))

/-- **The pullback along the morphism `p₀ : T' ⟶ T` of ambient schemes, as a left adjoint of the
same functor.**  Mathlib's pullback–pushforward adjunction of a morphism of schemes, composed
with the restriction of scalars over `T'` and transported along
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso`. -/
def firstOrderAmbientPullbackAdjunction (A : Thickening S) :
    Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom ⋙
        SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso
            (firstOrderThickeningObject S A)).hom ⊣
      SheafOfModules.pushforward.{u}
          (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)) ⋙
        SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
        (firstOrderThickeningSiteP₀ S A).targetHom.hom).comp
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso
          (firstOrderThickeningObject S A)))).ofNatIsoRight
    (Thickening.ambientSchemePushforwardIso (firstOrderThickeningSiteP₀ S A)).symm

/-- **The comparison of the two pushforwards is the identity on sections, read in the inverse
direction.**  The companion of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso_hom_app_val_app`:
the isomorphism is a `SheafOfModules.pushforwardCongr`, which is the identity on sections in both
directions. -/
theorem Thickening.ambientSchemePushforwardIso_inv_app_val_app {A B : Thickening S} (g : A ⟶ B)
    (N : SheafOfModules.{u} A.ringRestrictionSheaf)
    (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (x : N.val.obj (op (g.targetHom.hom ⁻¹ᵁ W.unop))) :
    ((Thickening.ambientSchemePushforwardIso g).inv.app N).val.app W x = x := rfl

/-- **The unit of
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction` is the unit of
Mathlib's pullback–pushforward adjunction of the morphism `p₀ : T' ⟶ T` of ambient schemes, on
sections.**  The two extra factors are the unit of a restriction of scalars along an isomorphism
and the comparison of the two pushforwards, and both are the identity on sections. -/
theorem firstOrderAmbientPullbackAdjunction_unit_app_val_app (A : Thickening S)
    (N : SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ) (a : N.val.obj W) :
    ((firstOrderAmbientPullbackAdjunction A).unit.app N).val.app W a =
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (firstOrderThickeningSiteP₀ S A).targetHom.hom).unit.app N).val.app W a := by
  change ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj N).val.map
      (𝟙 (op ((firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ W.unop)))
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (firstOrderThickeningSiteP₀ S A).targetHom.hom).unit.app N).val.app W a) = _
  rw [((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj N).val.map_id]
  rfl

/-- **The comparison of the two pullbacks of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` is the uniqueness of
left adjoints applied to the two adjunctions above.**  True by definition; the point of the
statement is that the two adjunctions are available as named objects, so that Mathlib's
compatibilities of `CategoryTheory.Adjunction.leftAdjointUniq` with the unit and with the adjoint
transposes can be used. -/
theorem ambientSchemePullbackIso_eq (A : Thickening S) :
    Thickening.ambientSchemePullbackIso (firstOrderThickeningSiteP₀ S A) =
      Adjunction.leftAdjointUniq (firstOrderCrysPullbackAdjunction A)
        (firstOrderAmbientPullbackAdjunction A) := rfl

/-! ### The comparison of the pullback along the morphism of ambient schemes with `F_{T'}` -/

/-- **The comparison map `p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], read along the morphism
`p₀ : T' ⟶ T` of ambient schemes.**  It is the adjoint transpose of the `f`-map of
[Stacks, Tag 07IQ] through
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction`, that is, the
comparison map of the crystalline `f`-map read through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso`. -/
def affineFirstOrderComparison (A : Thickening S) :
    (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso
            (firstOrderThickeningObject S A)).hom).obj
        ((Scheme.Modules.pullback (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
          (Thickening.ambientModuleRestriction M A)) ⟶
      Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A) :=
  ((firstOrderAmbientPullbackAdjunction A).homEquiv _ _).symm
    ((SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
      (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A)))

/-- **The normalisation of the comparison map: it carries the pullback of a section to the
restriction of that section along `p₀`.**  The adjoint transpose of a morphism is the unit
followed by the pushforward of the transpose, the unit of
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction` is on sections the
unit of Mathlib's pullback–pushforward adjunction of `p₀ : T' ⟶ T`, and that unit on sections
over the whole space is `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
theorem affineFirstOrderComparison_pullbackSection (A : Thickening S)
    (h : (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens) ≤
      (firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤)
    (a : (Thickening.ambientModuleRestriction M A).val.obj (op ⊤)) :
    (affineFirstOrderComparison M A).val.app
        (op ((firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤))
        (Scheme.Modules.pullbackSection (firstOrderThickeningSiteP₀ S A).targetHom.hom
          (Thickening.ambientModuleRestriction M A) ⊤ ⊤ h a) =
      M.val.map (Thickening.restrictOpenMap (firstOrderThickeningSiteP₀ S A) ⊤).op a := by
  have hθ : (firstOrderAmbientPullbackAdjunction A).unit.app
          (Thickening.ambientModuleRestriction M A) ≫
        (SheafOfModules.pushforward.{u}
            (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)) ⋙
          SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
          (affineFirstOrderComparison M A) =
      (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
        (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A)) := by
    change (firstOrderAmbientPullbackAdjunction A).homEquiv _ _
      (affineFirstOrderComparison M A) = _
    exact Equiv.apply_symm_apply _ _
  refine (congrArg (fun y ↦ (affineFirstOrderComparison M A).val.app
      (op ((firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤)) y) ?_).trans
    (congrArg (fun k ↦ k.val.app (op ⊤) a) hθ)
  exact (Scheme.Modules.pullbackSection_top _ _ h a).trans
    (firstOrderAmbientPullbackAdjunction_unit_app_val_app A
      (Thickening.ambientModuleRestriction M A) (op ⊤) a).symm

/-- **The same adjoint transpose, taken through the crystalline `f`-map, is the comparison map
`c_{p₀}` of [Stacks, Tag 07IQ].**  The transpose through
`Crystalline.GlobalCrystallineSituation.firstOrderCrysPullbackAdjunction` is taken in two steps:
through the restriction of scalars, where the counit and its naturality turn the restriction of
scalars of the `f`-map back into the `f`-map, and then through the pullback–pushforward
adjunction, where by definition the transpose of the `f`-map is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf`. -/
theorem crysPullbackAdjunction_homEquiv_symm_moduleFMapSheaf (A : Thickening S) :
    ((firstOrderCrysPullbackAdjunction A).homEquiv
        (Thickening.ambientModuleRestriction M A)
        (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A))).symm
      ((SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
        (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A))) =
      (SheafOfModules.pullback.{u}
            (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A))).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            (Thickening.moduleRestrictionSheaf M A)) ≫
        Thickening.moduleComparisonSheaf M (firstOrderThickeningSiteP₀ S A) := by
  have hinner : (SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
            (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A))) ≫
        (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          ((SheafOfModules.pushforward.{u}
              (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A))).obj
            (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A))) =
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          (Thickening.moduleRestrictionSheaf M A) ≫
        Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A) :=
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.naturality
        (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A))
  have hcounit : (firstOrderCrysPullbackAdjunction A).counit.app
        (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A)) =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
            (firstOrderThickeningSiteP₀ S A))).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap
                (firstOrderThickeningSiteP₀ S A))).obj
              (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A)))) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A))).counit.app
          (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A)) :=
    Adjunction.comp_counit_app
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A))
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A)))
      (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A))
  change (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningSiteP₀ S A))).map
        ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
            (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A)))) ≫
      (firstOrderCrysPullbackAdjunction A).counit.app
        (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A)) =
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningSiteP₀ S A))).map
        ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
          (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          (Thickening.moduleRestrictionSheaf M A)) ≫
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
            (firstOrderThickeningSiteP₀ S A))).map
          (Thickening.moduleFMapSheaf M (firstOrderThickeningSiteP₀ S A)) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap (firstOrderThickeningSiteP₀ S A))).counit.app
          (Thickening.moduleRestrictionSheaf M (firstOrderThickeningObject S A))
  rw [hcounit, ← Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp, Category.assoc]

/-- **The comparison map `p₀^* F_T ⟶ F_{T'}` of a crystal is an isomorphism.**  Through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` it is the comparison
map of [Stacks, Tag 07IQ] along the crystalline `f`-map of `p₀`, precomposed with the pullback of
the counit of a restriction of scalars along an isomorphism; the first is an isomorphism by the
crystal condition and the second is one because the counit is. -/
theorem isIso_affineFirstOrderComparison (hM : IsSheafCrystal M) (A : Thickening S) :
    IsIso (affineFirstOrderComparison M A) := by
  have : IsIso (Thickening.moduleComparisonSheaf M (firstOrderThickeningSiteP₀ S A)) := hM _ _ _
  have := Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app
    (Thickening.ringRestrictionSheafStructureIso A) (Thickening.moduleRestrictionSheaf M A)
  rw [← isIso_comp_left_iff
    ((Adjunction.leftAdjointUniq (firstOrderCrysPullbackAdjunction A)
      (firstOrderAmbientPullbackAdjunction A)).app
      (Thickening.ambientModuleRestriction M A)).hom]
  erw [(Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (firstOrderCrysPullbackAdjunction A)
    (firstOrderAmbientPullbackAdjunction A) _).trans
    (crysPullbackAdjunction_homEquiv_symm_moduleFMapSheaf M A)]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

/-- **The comparison map of a crystal is bijective on sections over every open of `T'`.**  This
is the form in which the comparison enters the affine computation of the base change: composed
with `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` over `⊤` it identifies the base
change of the global sections with `F(U, T', δ')`. -/
theorem bijective_affineFirstOrderComparison_val_app (hM : IsSheafCrystal M) (A : Thickening S)
    (W : ((firstOrderThickeningObject S A).thickening.target.scheme.Opens)ᵒᵖ) :
    Function.Bijective fun x ↦ (affineFirstOrderComparison M A).val.app W x := by
  have := isIso_affineFirstOrderComparison M hM A
  have := Stacks.SheafOfModules.isIso_val_app_of_isIso (affineFirstOrderComparison M A) W
  exact ConcreteCategory.bijective_of_isIso ((affineFirstOrderComparison M A).val.app W)


/-! ### The base change of the sections, read on the ambient schemes

The affine computation of the base change has to compare
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, which is written in the sections of
`F` over the *objects* `(U, T, δ)` and `(U, T', δ')` of the site, with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which is written in the sections of the
*restricted sheaf* `F_T` over the whole of the ambient scheme `T`.  The carriers agree, but each
of the types involved has two spellings whose heads are different symbols — `crysSheafRing S A` is
the value of the structure sheaf of the site at the object and `Γ(T, 𝒪_T)` is the value of the
structure sheaf of the ambient scheme at `⊤` — and an arithmetic operation with one operand in
each spelling does not elaborate.  The definitions below are the identity in each case and exist
only in order to name the spelling that is wanted; every lemma about them is closed by `rfl` or by
one `congrArg`.

The content of this section is the additive equivalence

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ≅ D' ⊗_D Mod`,

`Crystalline.GlobalCrystallineSituation.affineCrossEquiv`, between the tensor product over which
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is written and the one over which
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` is: the two have definitionally
equal carriers and definitionally equal ring structures, but their scalar actions are built from
the two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`, which are equal
only pointwise, so the two tensor products are *different types* and no `exact` or `rw` crosses
them.  The equivalence is built by hand from a pair of maps `t ⊗ s ↦ t ⊗ p^*s` and
`t ⊗ x ↦ t ⊗ (p^*)⁻¹x`, where `p^*` is the restriction
`Crystalline.GlobalCrystallineSituation.bijective_moduleSiteRestrict_restrictOpenHom_top` of
sections along the structure morphism of the restriction of the object to the whole of its ambient
scheme.  It is unconditional: no crystal hypothesis, no quasi-coherence, no affineness.
-/

/-- **The scalars of `Γ(T, 𝒪_T)` act on the sections of `F_T` through the restriction map of the
site along the structure morphism of the restriction of the object to the whole of its ambient
scheme.**  The action goes through
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`, whose
component over an open is `AlgebraicGeometry.Scheme.Opens.topIso` there; over `⊤` that component
is the comorphism of the structure morphism of the restriction, which is the restriction map of
the structure sheaf of the site.

Stated pointwise rather than as an equation of ring homomorphisms, for the reason recorded at
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`: `crysSheafRingMap`
carries the ring through `RingCat` and `AlgebraicGeometry.Scheme.Opens.topIso` through
`CommRingCat`, so the two `RingHom` types are not syntactically equal even though the carriers
are definitionally so. -/
theorem ringRestrictionSheafStructureIso_inv_app_top_eq_crysSheafRingMap_restrictOpenHom
    (A : Thickening S) (b : crysSheafRing S A) :
    ((Thickening.ringRestrictionSheafStructureIso A).inv.hom.app (op ⊤)).hom b =
      crysSheafRingMap (A.restrictOpenHom ⊤) b := rfl

/-- The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object, at
the type `AlgebraicGeometry.Scheme.Modules` of modules on that scheme.
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _.ringCatSheaf`, and the section
notation `Γ(-, U)` and the affine base-change comparison are stated at the former; this ascribes
`Crystalline.GlobalCrystallineSituation.Thickening.ambientModuleRestriction` there. -/
def ambientSchemeModules (A : Thickening S) : A.thickening.target.scheme.Modules :=
  Thickening.ambientModuleRestriction M A

variable (A : Thickening S)

/-- The whole of the ambient scheme of the first-order universal thickening is contained in the
preimage of the whole of the ambient scheme of the object, the two being equal.  Named because the
proof term has to carry this type and not the type of `le_top`, which is only definitionally
equal to it and which `rw` therefore refuses. -/
theorem top_le_preimage_siteP₀ :
    (⊤ : (firstOrderThickeningObject S A).thickening.target.scheme.Opens) ≤
      (firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ ⊤ := le_top

/-- A section of `𝒪_{X/S}` over an object, read as a section of the structure sheaf of its ambient
scheme over the whole scheme.  The identity; the two are the same type in two spellings. -/
def ambientRingSection (B : Thickening S) (b : crysSheafRing S B) :
    Γ(B.thickening.target.scheme, ⊤) := b

/-- The reading of `Crystalline.GlobalCrystallineSituation.ambientRingSection` in the other
direction. -/
def siteRingSection (B : Thickening S) (r : Γ(B.thickening.target.scheme, ⊤)) :
    crysSheafRing S B := r

/-- Reading a section of `𝒪_{X/S}` on the ambient scheme and back is the identity. -/
@[simp]
theorem siteRingSection_ambientRingSection (B : Thickening S) (b : crysSheafRing S B) :
    siteRingSection B (ambientRingSection B b) = b := rfl

/-- A section of `F` over the restriction of an object to the whole of its ambient scheme, read as
a section of the restricted sheaf `F_T` over the whole scheme.  The identity. -/
def ambientModuleSection (x : M.val.obj (op (A.restrictOpen ⊤))) :
    Γ(ambientSchemeModules M A, ⊤) := x

/-- The reading of `Crystalline.GlobalCrystallineSituation.ambientModuleSection` in the other
direction. -/
def siteModuleSection (x : Γ(ambientSchemeModules M A, ⊤)) :
    M.val.obj (op (A.restrictOpen ⊤)) := x

/-- Reading a section of `F` on the ambient scheme and back is the identity. -/
@[simp]
theorem siteModuleSection_ambientModuleSection (x : M.val.obj (op (A.restrictOpen ⊤))) :
    siteModuleSection M A (ambientModuleSection M A x) = x := rfl

/-- **The sections of `𝒪_{T'}` over the ambient scheme, as a module over the sections of `𝒪_T`
over the ambient scheme, through the morphism `p₀ : T' ⟶ T` of ambient schemes.**  This is the
scalar action over which `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` extends scalars,
and it is *not* the action of
`Crystalline.GlobalCrystallineSituation.algebraCrysSheafRingSiteP₀`: the two are built from the
two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`, which agree only
pointwise. -/
instance moduleAmbientSiteP₀ :
    Module Γ(A.thickening.target.scheme, ⊤)
      Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) :=
  Module.compHom _
    ((firstOrderThickeningSiteP₀ S A).targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_siteP₀ A)).hom

/-- **The two actions of the sections of `𝒪_T` on the sections of `𝒪_{T'}` agree** — the one
through the restriction map of the site along `p₀` and the one through the map on sections of the
morphism `p₀` of ambient schemes. -/
theorem ambientRingSection_smul (b : crysSheafRing S A)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    ambientRingSection A b • ambientRingSection (firstOrderThickeningObject S A) t =
      ambientRingSection (firstOrderThickeningObject S A) (b • t) :=
  congrArg (fun y ↦ y * ambientRingSection (firstOrderThickeningObject S A) t)
    (appLE_top_eq_crysSheafRingMap_siteP₀ A (top_le_preimage_siteP₀ A)
      (ambientRingSection A b))

/-- `Crystalline.GlobalCrystallineSituation.ambientRingSection_smul`, read with the scalar and the
section in the spelling of the ambient schemes. -/
theorem smul_eq_ambientRingSection (r : Γ(A.thickening.target.scheme, ⊤))
    (t : Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤)) :
    r • t = ambientRingSection (firstOrderThickeningObject S A)
      (siteRingSection A r • siteRingSection (firstOrderThickeningObject S A) t) :=
  ambientRingSection_smul A (siteRingSection A r)
    (siteRingSection (firstOrderThickeningObject S A) t)

/-- **The scalars of the sections of `𝒪_T` act on the sections of `F_T` through the restriction
map of the site**, which is
`ringRestrictionSheafStructureIso_inv_app_top_eq_crysSheafRingMap_restrictOpenHom`
read on a module. -/
theorem ambientModuleSection_smul (b : crysSheafRing S A)
    (x : M.val.obj (op (A.restrictOpen ⊤))) :
    ambientRingSection A b • ambientModuleSection M A x =
      ambientModuleSection M A (crysSheafRingMap (A.restrictOpenHom ⊤) b • x) := rfl

/-- `Crystalline.GlobalCrystallineSituation.ambientModuleSection_smul`, read with the scalar and
the section in the spelling of the ambient scheme. -/
theorem smul_eq_ambientModuleSection (r : Γ(A.thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    r • x = ambientModuleSection M A
      (crysSheafRingMap (A.restrictOpenHom ⊤) (siteRingSection A r) • siteModuleSection M A x) :=
  ambientModuleSection_smul M A (siteRingSection A r) (siteModuleSection M A x)

/-- **The sections of `F` over an object and over its restriction to the whole of its ambient
scheme, as an additive equivalence.**  This is
`Crystalline.GlobalCrystallineSituation.bijective_moduleSiteRestrict_restrictOpenHom_top` bundled;
the map is the restriction along the structure morphism of that restriction. -/
def restrictOpenTopEquiv : M.val.obj (op A) ≃+ M.val.obj (op (A.restrictOpen ⊤)) :=
  AddEquiv.ofBijective (moduleSiteRestrict M (A.restrictOpenHom ⊤)).toAddMonoidHom
    (bijective_moduleSiteRestrict_restrictOpenHom_top M A)

/-- `restrictOpenTopEquiv` is the restriction of sections along the structure morphism of the
restriction of the object to the whole of its ambient scheme. -/
@[simp]
theorem restrictOpenTopEquiv_apply (s : M.val.obj (op A)) :
    restrictOpenTopEquiv M A s = moduleSiteRestrict M (A.restrictOpenHom ⊤) s := rfl

/-- Restricting the preimage under `restrictOpenTopEquiv` of a section recovers that section. -/
@[simp]
theorem moduleSiteRestrict_restrictOpenTopEquiv_symm (x : M.val.obj (op (A.restrictOpen ⊤))) :
    moduleSiteRestrict M (A.restrictOpenHom ⊤) ((restrictOpenTopEquiv M A).symm x) = x :=
  (restrictOpenTopEquiv M A).apply_symm_apply x

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.affineCross`. -/
def affineCrossAux :
    crysSheafRing S (firstOrderThickeningObject S A) →+
      (M.val.obj (op A) →+
        Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
          Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s))
      (fun s s' ↦ (congrArg
          (fun y ↦ ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
            Γ(A.thickening.target.scheme, ⊤)] ambientModuleSection M A y)
          (map_add (moduleSiteRestrict M (A.restrictOpenHom ⊤)) s s')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `affineCrossAux` sends `t` and `s` to `t ⊗ p₀^* s`. -/
@[simp]
theorem affineCrossAux_apply (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCrossAux M A t s =
      ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) := rfl

/-- **The base change of the sections of `F` along `p₀`, carried into the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`**: the map
`D' ⊗_D Mod ⟶ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)` sending `t ⊗ s` to `t ⊗ p₀^* s`, the two
tensor products being over the two actions of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`.  No hypothesis. -/
def affineCross :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) :=
  TensorProduct.liftAddHom (affineCrossAux M A) (fun b t s ↦ by
    rw [affineCrossAux_apply, affineCrossAux_apply, ← ambientRingSection_smul,
      TensorProduct.smul_tmul, ambientModuleSection_smul, map_smulₛₗ])

/-- `affineCross` sends `t ⊗ s` to `t ⊗ p₀^* s`. -/
@[simp]
theorem affineCross_tmul (t : crysSheafRing S (firstOrderThickeningObject S A))
    (s : M.val.obj (op A)) :
    affineCross M A (t ⊗ₜ[crysSheafRing S A] s) =
      ambientRingSection (firstOrderThickeningObject S A) t ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤)]
        ambientModuleSection M A (moduleSiteRestrict M (A.restrictOpenHom ⊤) s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- The bilinear datum of `Crystalline.GlobalCrystallineSituation.affineCrossInv`. -/
def affineCrossInvAux :
    Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) →+
      (Γ(ambientSchemeModules M A, ⊤) →+
        crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A]
          M.val.obj (op A)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun x ↦ siteRingSection (firstOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x))
      (fun x y ↦ (congrArg
          (fun z ↦ siteRingSection (firstOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A] z)
          (map_add (restrictOpenTopEquiv M A).symm (siteModuleSection M A x)
            (siteModuleSection M A y))).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- `affineCrossInvAux` sends `t` and `x` to `t ⊗ (p₀^*)⁻¹ x`. -/
@[simp]
theorem affineCrossInvAux_apply
    (t : Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInvAux M A t x =
      siteRingSection (firstOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) := rfl

/-- **The inverse of the restriction of sections to the whole of the ambient scheme is semilinear
over the restriction map of the site.** -/
theorem restrictOpenTopEquiv_symm_smul (r : Γ(A.thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    siteRingSection A r • (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) =
      (restrictOpenTopEquiv M A).symm (siteModuleSection M A (r • x)) := by
  refine (restrictOpenTopEquiv M A).injective ?_
  rw [restrictOpenTopEquiv_apply, restrictOpenTopEquiv_apply, map_smulₛₗ,
    moduleSiteRestrict_restrictOpenTopEquiv_symm, moduleSiteRestrict_restrictOpenTopEquiv_symm,
    smul_eq_ambientModuleSection, siteModuleSection_ambientModuleSection]

/-- **The inverse of `Crystalline.GlobalCrystallineSituation.affineCross`**, the map
`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ⟶ D' ⊗_D Mod` sending `t ⊗ x` to `t ⊗ (p₀^*)⁻¹ x`. -/
def affineCrossInv :
    Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) →+
      crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) :=
  TensorProduct.liftAddHom (affineCrossInvAux M A) (fun r t x ↦ by
    rw [affineCrossInvAux_apply, affineCrossInvAux_apply, smul_eq_ambientRingSection,
      siteRingSection_ambientRingSection, TensorProduct.smul_tmul,
      restrictOpenTopEquiv_symm_smul])

/-- `affineCrossInv` sends `t ⊗ x` to `t ⊗ (p₀^*)⁻¹ x`. -/
@[simp]
theorem affineCrossInv_tmul
    (t : Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤))
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineCrossInv M A (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] x) =
      siteRingSection (firstOrderThickeningObject S A) t ⊗ₜ[crysSheafRing S A]
        (restrictOpenTopEquiv M A).symm (siteModuleSection M A x) :=
  TensorProduct.liftAddHom_tmul _ _ t x

/-- **The two tensor products of the affine computation of the base change agree**, as an additive
equivalence

`D' ⊗_D Mod ≅ Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)`

between the source of `Crystalline.GlobalCrystallineSituation.extensionSectionsMap` and the source
of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤`.  The two are different types
— their scalar actions are built from the two ring homomorphisms of
`Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`, equal only
pointwise — and this is the change of spelling between them.  It is unconditional: no crystal
hypothesis, no quasi-coherence, no affineness. -/
def affineCrossEquiv :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) ≃+
      Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) ⊗[
        Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeModules M A, ⊤) where
  toFun := affineCross M A
  invFun := affineCrossInv M A
  map_add' := map_add (affineCross M A)
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul t s =>
        rw [affineCross_tmul, affineCrossInv_tmul, siteRingSection_ambientRingSection,
          siteModuleSection_ambientModuleSection, ← restrictOpenTopEquiv_apply,
          AddEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
        rw [affineCrossInv_tmul, affineCross_tmul,
          moduleSiteRestrict_restrictOpenTopEquiv_symm]
        rfl
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

end Crystalline.GlobalCrystallineSituation

end

end
