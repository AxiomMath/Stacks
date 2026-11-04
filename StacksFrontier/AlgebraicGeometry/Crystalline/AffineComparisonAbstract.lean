module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineComparisonAlong

/-!
# The comparison map of [Stacks, Tag 07IQ] from the `f`-map alone

`StacksFrontier/AlgebraicGeometry/Crystalline/AffineComparisonAlong.lean` constructs, for an
arbitrary morphism `g : (U', T', δ') ⟶ (U, T, δ)` of the **big** crystalline site and a sheaf `F`
of `𝒪_{X/S}`-modules there, the comparison map

`c_g : g^* F_T ⟶ F_{T'}`

of [Stacks, Tag 07IQ] read along the morphism `g : T' ⟶ T` of ambient schemes, and shows it to be
an isomorphism when `F` is a crystal.

**Nothing in that construction uses `F`.**  It uses only the two restrictions `F_T` and `F_{T'}`,
which are sheaves of modules over the restricted structure sheaf
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the two objects, and
the `f`-map `F_T ⟶ g_* F_{T'}` between them.  This module is that construction with those three
carried as variables.

The point is that the **small** crystalline site produces exactly the same three: for
`ℱ : SheafOfModules (structureSheaf S)` and `k : A' ⟶ A` in `Cris(X/S)`,
`...SmallSite.CohomologyRestriction.moduleRestrictionSheaf ℱ A` is a sheaf of modules over
`...Thickening.ringRestrictionSheaf A.obj`, and
`...SmallSite.CohomologyRestriction.moduleFMapSheaf ℱ k` is an `f`-map over
`...Thickening.ringRestrictionSheafFMap k.hom` — the very same sheaf of rings
and the very same morphism of sheaves of rings as on the big site.  So the comparison map of a
small-site crystal, and its invertibility, are the statements below read at that data, with no
duplication of the argument.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ambientOf` — a module over the restriction of
  `𝒪_{X/S}` to the ambient scheme of an object, read over the structure sheaf of that scheme.
* `Crystalline.GlobalCrystallineSituation.comparisonAbstract` — the comparison map
  `g^* N_T ⟶ N_{T'}` over the restricted structure sheaves, the adjoint transpose of the `f`-map.
* `Crystalline.GlobalCrystallineSituation.affineComparisonAbstract` — the same read along the
  morphism `g : T' ⟶ T` of ambient schemes.
* `Crystalline.GlobalCrystallineSituation.ambientComparisonAbstract` — the same with both sides
  read over the structure sheaves of the ambient schemes.

## Main results

* `Crystalline.GlobalCrystallineSituation.isIso_affineComparisonAbstract` — the comparison map
  along the morphism of ambient schemes is an isomorphism as soon as the comparison map over the
  restricted structure sheaves is.
* `Crystalline.GlobalCrystallineSituation.ambientComparisonAbstract_pullbackSection` — the
  normalisation: the comparison carries the pullback of a section to the `f`-map of that section.
* `Crystalline.GlobalCrystallineSituation.bijective_ambientComparisonAbstractTop` — it is
  bijective on sections over the whole of `T'`.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {A A' : Thickening S} (g : A' ⟶ A)

/-- **A module over the restriction of `𝒪_{X/S}` to the ambient scheme of an object, read over
the structure sheaf of that scheme.**  A restriction of scalars along the isomorphism
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`; neither the
sections nor the restriction maps move.

Both `Crystalline.GlobalCrystallineSituation.Thickening.ambientModuleRestriction` and
`...SmallSite.ambientModuleRestriction` are this, at the restriction of the respective
coefficient sheaf. -/
def Thickening.ambientOf (B : Thickening S) (N : SheafOfModules.{u} B.ringRestrictionSheaf) :
    SheafOfModules.{u} B.thickening.target.scheme.ringCatSheaf :=
  (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso B).inv).obj N

/-- `Crystalline.GlobalCrystallineSituation.Thickening.ambientOf` at the type
`AlgebraicGeometry.Scheme.Modules` of modules on the ambient scheme, which is the type the
sections notation `Γ(-, U)` and `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` are
stated at. -/
def ambientSchemeOf (B : Thickening S) (N : SheafOfModules.{u} B.ringRestrictionSheaf) :
    B.thickening.target.scheme.Modules :=
  Thickening.ambientOf B N

variable (NA : SheafOfModules.{u} A.ringRestrictionSheaf)
  (NA' : SheafOfModules.{u} A'.ringRestrictionSheaf)
  (fmap : NA ⟶ (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')

/-- **The comparison map `g^* N_T ⟶ N_{T'}` of [Stacks, Tag 07IQ] over the restricted structure
sheaves**, the adjoint transpose of the `f`-map through the adjunction between pullback and
pushforward of sheaves of modules.  At the restriction of a coefficient sheaf this is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf`, respectively
`...SmallSite.CohomologyRestriction.moduleComparisonSheaf`. -/
def comparisonAbstract :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA ⟶ NA' :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (Thickening.ringRestrictionSheafFMap g)).homEquiv NA NA').symm fmap

/-- **The comparison map `g^* N_T ⟶ N_{T'}` read along the morphism `g : T' ⟶ T` of ambient
schemes.**  It is the adjoint transpose of the `f`-map through
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong`, that is, the comparison
map above read through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso`. -/
def affineComparisonAbstract :
    (SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso A').hom).obj
        ((Scheme.Modules.pullback g.targetHom.hom).obj (Thickening.ambientOf A NA)) ⟶ NA' :=
  ((ambientPullbackAdjunctionAlong g).homEquiv _ _).symm
    ((SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map fmap)

/-- **The normalisation of the comparison map: it carries the pullback of a section to the
`f`-map of that section.**  The adjoint transpose of a morphism is the unit followed by the
pushforward of the transpose, the unit of
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong` is on sections the unit of
Mathlib's pullback–pushforward adjunction of `g : T' ⟶ T`, and that unit on sections over the
whole space is `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
theorem affineComparisonAbstract_pullbackSection
    (h : (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤)
    (a : (Thickening.ambientOf A NA).val.obj (op ⊤)) :
    (affineComparisonAbstract g NA NA' fmap).val.app (op (g.targetHom.hom ⁻¹ᵁ ⊤))
        (Scheme.Modules.pullbackSection g.targetHom.hom
          (Thickening.ambientOf A NA) ⊤ ⊤ h a) =
      fmap.val.app (op ⊤) a := by
  have hθ : (ambientPullbackAdjunctionAlong g).unit.app (Thickening.ambientOf A NA) ≫
        (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g) ⋙
          SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
          (affineComparisonAbstract g NA NA' fmap) =
      (SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso A).inv).map fmap := by
    change (ambientPullbackAdjunctionAlong g).homEquiv _ _
      (affineComparisonAbstract g NA NA' fmap) = _
    exact Equiv.apply_symm_apply _ _
  refine (congrArg (fun y ↦ (affineComparisonAbstract g NA NA' fmap).val.app
      (op (g.targetHom.hom ⁻¹ᵁ ⊤)) y) ?_).trans (congrArg (fun k ↦ k.val.app (op ⊤) a) hθ)
  exact (Scheme.Modules.pullbackSection_top _ _ h a).trans
    (ambientPullbackAdjunctionAlong_unit_app_val_app g (Thickening.ambientOf A NA) (op ⊤) a).symm

/-- **The same adjoint transpose, taken through the crystalline `f`-map, is the comparison map
over the restricted structure sheaves.**  The transpose through
`Crystalline.GlobalCrystallineSituation.crysPullbackAdjunctionAlong` is taken in two steps:
through the restriction of scalars, where the counit and its naturality turn the restriction of
scalars of the `f`-map back into the `f`-map, and then through the pullback–pushforward
adjunction, where by definition the transpose of the `f`-map is
`Crystalline.GlobalCrystallineSituation.comparisonAbstract`. -/
theorem crysPullbackAdjunctionAlong_homEquiv_symm_fmap :
    ((crysPullbackAdjunctionAlong g).homEquiv (Thickening.ambientOf A NA) NA').symm
      ((SheafOfModules.restrictScalars
        (Thickening.ringRestrictionSheafStructureIso A).inv).map fmap) =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) ≫
        comparisonAbstract g NA NA' fmap := by
  have hinner : (SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map fmap) ≫
        (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA') =
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA ≫ fmap :=
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.naturality fmap
  have hcounit : (crysPullbackAdjunctionAlong g).counit.app NA' =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (Thickening.ringRestrictionSheafFMap g)).counit.app NA' :=
    Adjunction.comp_counit_app
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A))
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (Thickening.ringRestrictionSheafFMap g)) NA'
  change (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
        ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map fmap)) ≫
      (crysPullbackAdjunctionAlong g).counit.app NA' =
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
        ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
          (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) ≫
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map fmap ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g)).counit.app NA'
  rw [hcounit, ← Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp, Category.assoc]

/-- **The comparison map along the morphism of ambient schemes is an isomorphism as soon as the
comparison map over the restricted structure sheaves is.**  Through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` it is the latter
precomposed with the pullback of the counit of a restriction of scalars along an isomorphism, and
that counit is an isomorphism. -/
theorem isIso_affineComparisonAbstract (hc : IsIso (comparisonAbstract g NA NA' fmap)) :
    IsIso (affineComparisonAbstract g NA NA' fmap) := by
  have hε : IsIso ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) :=
    Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app _ _
  have hPε : IsIso ((SheafOfModules.pullback.{u}
        (Thickening.ringRestrictionSheafFMap g)).map
      ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA)) :=
    Functor.map_isIso _ _
  have : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _
  have : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
          (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA) ≫
        affineComparisonAbstract g NA NA' fmap) := by
    have h : (Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
            (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA) ≫
          affineComparisonAbstract g NA NA' fmap =
        (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
            ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
              (Thickening.ringRestrictionSheafStructureIso A)).counit.app NA) ≫
          comparisonAbstract g NA NA' fmap :=
      (Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (crysPullbackAdjunctionAlong g)
          (ambientPullbackAdjunctionAlong g) _).trans
        (crysPullbackAdjunctionAlong_homEquiv_symm_fmap g NA NA' fmap)
    rw [h]
    exact IsIso.comp_isIso' hPε hc
  exact IsIso.of_isIso_comp_left
    ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientOf A NA))
    (affineComparisonAbstract g NA NA' fmap)

/-- **The comparison map is bijective on sections over every open of `T'`** as soon as the
comparison map over the restricted structure sheaves is an isomorphism. -/
theorem bijective_affineComparisonAbstract_val_app (hc : IsIso (comparisonAbstract g NA NA' fmap))
    (W : (A'.thickening.target.scheme.Opens)ᵒᵖ) :
    Function.Bijective fun x ↦ (affineComparisonAbstract g NA NA' fmap).val.app W x := by
  have := isIso_affineComparisonAbstract g NA NA' fmap hc
  have := Stacks.SheafOfModules.isIso_val_app_of_isIso (affineComparisonAbstract g NA NA' fmap) W
  exact ConcreteCategory.bijective_of_isIso ((affineComparisonAbstract g NA NA' fmap).val.app W)

/-! ### The comparison map read over the structure sheaves of the ambient schemes -/

/-- **The comparison map `g^* N_T ⟶ N_{T'}` with both sides read over the structure sheaves of
the ambient schemes.**  It is the adjoint transpose of
`Crystalline.GlobalCrystallineSituation.affineComparisonAbstract` through the adjunction of
restrictions of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`; by
`Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app` it is the same map on
sections.  This is the spelling in which the comparison can be composed with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def ambientComparisonAbstract :
    (Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA) ⟶
      ambientSchemeOf A' NA' :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
    (Thickening.ringRestrictionSheafStructureIso A')).homEquiv _ _
      (affineComparisonAbstract g NA NA' fmap)

/-- **The change of spelling does not move sections.** -/
theorem ambientComparisonAbstract_val_app (W : (A'.thickening.target.scheme.Opens)ᵒᵖ)
    (y : ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA)).val.obj W) :
    (ambientComparisonAbstract g NA NA' fmap).val.app W y =
      (affineComparisonAbstract g NA NA' fmap).val.app W y :=
  Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app _ _ W y

/-- The comparison map on sections over the whole of `T'`, as an additive map. -/
def ambientComparisonAbstractTop :
    Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA), ⊤) →+
      Γ(ambientSchemeOf A' NA', ⊤) :=
  AddMonoidHom.mk' (fun y ↦ (ambientComparisonAbstract g NA NA' fmap).app ⊤ y)
    (fun y y' ↦ map_add _ y y')

/-- **That map is bijective** as soon as the comparison map over the restricted structure sheaves
is an isomorphism, being
`Crystalline.GlobalCrystallineSituation.affineComparisonAbstract` on sections. -/
theorem bijective_ambientComparisonAbstractTop
    (hc : IsIso (comparisonAbstract g NA NA' fmap)) :
    Function.Bijective (ambientComparisonAbstractTop g NA NA' fmap) := by
  have h : (ambientComparisonAbstractTop g NA NA' fmap : _ → _) =
      fun y ↦ (affineComparisonAbstract g NA NA' fmap).val.app (op ⊤) y :=
    funext fun y ↦ ambientComparisonAbstract_val_app g NA NA' fmap (op ⊤) y
  rw [h]
  exact bijective_affineComparisonAbstract_val_app g NA NA' fmap hc (op ⊤)

/-- The pullback along `g` of a section of `N_T` over the whole of `T`, as a section of `g^* N_T`
over the whole of `T'`, with its type named at the sections notation. -/
def ambientPullbackSectionTopAbstract (x : Γ(ambientSchemeOf A NA, ⊤)) :
    Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA), ⊤) :=
  Scheme.Modules.pullbackSection g.targetHom.hom (ambientSchemeOf A NA) ⊤ ⊤
    (top_le_preimage_ambient g) x

/-- **The normalisation in the ambient spelling**: the comparison carries the pullback of a
section to the `f`-map of that section.  This is
`Crystalline.GlobalCrystallineSituation.affineComparisonAbstract_pullbackSection` moved across the
change of spelling. -/
theorem ambientComparisonAbstract_pullbackSection
    (h : (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤)
    (x : Γ(ambientSchemeOf A NA, ⊤)) :
    (ambientComparisonAbstract g NA NA' fmap).app ⊤
        (Scheme.Modules.pullbackSection g.targetHom.hom (ambientSchemeOf A NA) ⊤ ⊤ h x) =
      fmap.val.app (op ⊤) x :=
  (ambientComparisonAbstract_val_app g NA NA' fmap (op ⊤) _).trans
    (affineComparisonAbstract_pullbackSection g NA NA' fmap h x)

/-- The same normalisation, with the pullback of the section named. -/
theorem ambientComparisonAbstract_ambientPullbackSectionTopAbstract
    (x : Γ(ambientSchemeOf A NA, ⊤)) :
    (ambientComparisonAbstract g NA NA' fmap).app ⊤
        (ambientPullbackSectionTopAbstract g NA x) = fmap.val.app (op ⊤) x :=
  ambientComparisonAbstract_pullbackSection g NA NA' fmap (top_le_preimage_ambient g) x

end Crystalline.GlobalCrystallineSituation

end

end
