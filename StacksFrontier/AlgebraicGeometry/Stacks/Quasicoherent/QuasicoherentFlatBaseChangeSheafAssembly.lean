module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentFlatBaseChangeSheaf

/-!
# Quasi-coherent modules have the flat base change property on sheaves of modules

Let `F` be a quasi-coherent module on the fppf site of a category `𝒳` fibred in groupoids over
the schemes over `S` (**Stacks 06WG**), and read it on the associated étale site.  For every
arrow `φ : z ⟶ x` of `𝒳` lying over `a : W ⟶ U`, the comparison map
`c_φ : a_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of **Stacks 06WC**, read on sheaves of modules, is an
isomorphism; flatness of `a` is not needed.  In particular the étale reading of `F` has the flat
base change property of **Stacks 0762** on sheaves of modules, the flat base change half of the
containment `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` of **Stacks 0778**.

## Main definitions

* `AlgebraicGeometry.Stack.objectInverseImageRestrictAlongSheafIso`: the restriction `F|_{W_ét}`
  as the restriction along `a` of the inverse image `x^*F`, on sheaves of modules.

## Main results

* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparisonApp_of_quasicoherent`: the
  comparison map of Stacks 06WC on sheaves of modules is an isomorphism for a quasi-coherent
  module and an arbitrary arrow.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_toSiteModules_etale`: the étale reading
  of a quasi-coherent module has the flat base change property of Stacks 0762 on sheaves of
  modules.
* `AlgebraicGeometry.Stack.forall_hasFlatBaseChangePropertySheaf_toSiteModules_etale`: the same,
  with the étale reading written through `AlgebraicGeometry.FibredSite.toSiteModules`.

## Implementation notes

The objects of the big and small étale sites of `U` appear in two spellings, `U` itself and the
underlying scheme of `U` regarded as an object of the étale site, which are definitionally but
not syntactically equal.  The identification of the transposed comparison map is therefore
stated in `AlgebraicGeometry.Stack.homEquiv_sheafifiedRestrictComparisonApp_eq_inv_comp` with
the intermediate object of the composite spelled explicitly as the source of
`AlgebraicGeometry.SmallEtale.bigRestrictComparison`, and the main theorem is assembled through
`Stacks.CategoryTheory.Adjunction.isIso_homEquiv_symm_of_eq_comp_conj`, so that no definitional
unfolding between the two spellings happens inside a large goal.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.CategoryTheory.Adjunction

/-- **Invertibility of a transpose conjugate to a comparison.**  Let `adj : L ⊣ R` and
`adj' : L' ⊣ R` share their right adjoint, and let `comp : bR ⟶ bRA ⋙ R` be identified at `A`
with the unit of `adj'` up to isomorphisms (`h3C`).  Then for an isomorphism `g : A ≅ G`, any
`t` equal to `comp` at `G` conjugated by isomorphisms `eU`, `eW` has an invertible transpose
along `adj`. -/
theorem isIso_homEquiv_symm_of_eq_comp_conj {C D D' : Type*} [Category C] [Category D]
    [Category D'] {L L' : D ⥤ D'} {R : D' ⥤ D} (adj : L ⊣ R) (adj' : L' ⊣ R)
    {bR : C ⥤ D} {bRA : C ⥤ D'} (comp : bR ⟶ bRA ⋙ R) {A G : C} (g : A ≅ G)
    {M M' : D} {P N : D'} (bc : P ≅ L'.obj M') (i1 : bR.obj A ≅ M')
    (i1' : bRA.obj A ≅ P) (eU : bR.obj G ≅ M) (eW : bRA.obj G ≅ N)
    (h3C : comp.app A ≫ R.map i1'.hom = i1.hom ≫ adj'.unit.app M' ≫ R.map bc.inv)
    (t : M ⟶ R.obj N) (ht : t = eU.inv ≫ comp.app G ≫ R.map eW.hom) :
    IsIso ((adj.homEquiv M N).symm t) :=
  isIso_homEquiv_symm_of_eq_unit adj adj' (eU.symm ≪≫ bR.mapIso g.symm ≪≫ i1)
    (bc.symm ≪≫ i1'.symm ≪≫ bRA.mapIso g ≪≫ eW) t
    (ht.trans (unit_conj_eq_comp_conj comp g (adj'.unit.app M') bc i1 i1' eU eW h3C).symm)

end Stacks.CategoryTheory.Adjunction

namespace Stacks.SheafOfModules

/-- A composite of morphisms of sheaves of modules on local sections, with the linear maps
written through `ModuleCat.Hom.hom`. -/
theorem moduleCatHom_comp_val_app_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M₁ M₂ M₃ : _root_.SheafOfModules.{u} R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (V : Cᵒᵖ)
    (m : M₁.val.obj V) : ModuleCat.Hom.hom ((f ≫ g).val.app V) m =
      ModuleCat.Hom.hom (g.val.app V) (ModuleCat.Hom.hom (f.val.app V) m) :=
  rfl

end Stacks.SheafOfModules

namespace Stacks.PresheafOfModules

/-- The reindexing `eqToIso` between pushforwards of presheaves of modules along equal maps of
presheaves of rings is the identity on sections. -/
theorem comp_eqToIso_pushforward_hom_app_app_apply {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {φ₁ φ₂ : S ⟶ F.op ⋙ R}
    {M : _root_.PresheafOfModules.{u} S} {N : _root_.PresheafOfModules.{u} R}
    (g : M ⟶ (_root_.PresheafOfModules.pushforward.{u} φ₁).obj N)
    (hφ : φ₁ = φ₂) (V : Cᵒᵖ) (m : M.obj V) :
    ModuleCat.Hom.hom ((g ≫ (eqToIso (congrArg
      (fun k => _root_.PresheafOfModules.pushforward.{u} (F := F) k) hφ)).hom.app N).app V) m =
      g.app V m := by
  subst hφ
  rfl

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **`AlgebraicGeometry.Stack.objectInverseImageRestrictAlongIso` on sheaves of modules**: for
`φ : z ⟶ x` lying over `a : W ⟶ U`, the restriction `F|_{W_ét}` of Stacks 06WJ is the
restriction to the small étale site of `W`, along `a`, of the inverse image `x^*F` of
Stacks 06WI. -/
def objectInverseImageRestrictAlongSheafIso
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x) :
    (SmallEtale.bigRestrictAlong B (associatedBigEtaleSite B) rfl
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
        (baseTopology_etale_le_fppf B)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F) ≅
      (restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp z).obj
        ((fppfToEtaleSheafOfModules B S hS p hp).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Iso.refl _ ≪≫ objectInverseImageRestrictAlongIso B S hS p hp F φ)

section Sections

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf
  AlgebraicGeometry.Stack.smallEtaleStructureComparison
  AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing

/-- **The transposed comparison map of Stacks 06WC on sections**: the transpose of `c_φ` along
the adjunction between the sheafified pullback and the pushforward along `ε_a` is, on sections
over `V` étale over `U`, the comparison `ℱ|_{U_ét}(V) ⟶ ℱ|_{W_ét}(V ×_U W)` of Stacks 06W2. -/
theorem homEquiv_sheafifiedRestrictComparisonApp_val_app_apply {x z : 𝒳} (φ : z ⟶ x)
    (ℱ : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))ᵒᵖ)
    (n : ((restrictModuleToSmallEtaleSheafFunctor B (associatedBigEtaleSite B) rfl S hS p hp
      x).obj ℱ).val.obj V) :
    ModuleCat.Hom.hom (((sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl
        S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ
          ℱ)).val.app V) n =
      (restrictionPushforwardComparison B (associatedBigEtaleSite B) rfl S hS p hp φ
        ℱ.val.presheaf).app V n := by
  rw [sheafifiedPullbackComparisonAdjunction_homEquiv_sheafifiedRestrictComparisonApp_val]
  exact Stacks.PresheafOfModules.comp_eqToIso_pushforward_hom_app_app_apply _
    (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B (associatedBigEtaleSite B) rfl
      S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ) V n

/-- **The transposed comparison map through the inverse image, on sections**: for `F` on the
fppf site, a section `m` of `x^*F` over `V` étale over `U`, read in `F|_{U_ét}`, is sent by the
transpose of `c_φ` to the restriction of `m` along the base-change projection `V ×_U W ⟶ V`,
read in `F|_{W_ét}`. -/
theorem homEquiv_sheafifiedRestrictComparisonApp_objectInverseImage_apply
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))ᵒᵖ)
    (m : ((SmallEtale.bigRestrict B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x) .fppf
        (baseTopology_etale_le_fppf B)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F)).val.obj V) :
    ModuleCat.Hom.hom (((sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl
        S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ
          ((fppfToEtaleSheafOfModules B S hS p hp).obj F))).val.app V)
        (ModuleCat.Hom.hom ((objectInverseImageRestrictSheafIso B S hS p hp F x).hom.val.app V)
          m) =
      (objectInverseImageRestrictAlongIso B S hS p hp F φ).hom.app
        (Opposite.op ((smallEtaleBaseChange (associatedBigEtaleSite B)
          (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V.unop))
        ((FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val.map
          ((SmallEtale.baseChangeProjection B (associatedBigEtaleSite B) rfl
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).app V.unop).op
          m) :=
  (homEquiv_sheafifiedRestrictComparisonApp_val_app_apply B S hS p hp φ _ V _).trans
    (restrictionPushforwardComparison_objectInverseImageRestrictIso B S hS p hp F φ V.unop _ rfl
      m)

/-- **The comparison of Stacks 06WC for the inverse image, on sections**: the comparison
`AlgebraicGeometry.SmallEtale.bigRestrictComparison` for `x^*F` on the big site of `U`, followed
by `AlgebraicGeometry.Stack.objectInverseImageRestrictAlongSheafIso`, sends a section `m` over
`V` to the restriction of `m` along the base-change projection `V ×_U W ⟶ V`, read in
`F|_{W_ét}`. -/
theorem bigRestrictComparison_comp_objectInverseImageRestrictAlongSheafIso_apply
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x)
    (V : (SmallEtale (associatedBigEtaleSite B) (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x))ᵒᵖ)
    (m : ((SmallEtale.bigRestrict B (associatedBigEtaleSite B) rfl (p.obj x).left.1
        (contains_base B (associatedBigEtaleSite B) rfl S hS p x) .fppf
        (baseTopology_etale_le_fppf B)).obj
        (FibredSite.objectInverseImageKind B S hS p hp .fppf x F)).val.obj V) :
    ModuleCat.Hom.hom ((((SmallEtale.bigRestrictComparison B (associatedBigEtaleSite B) rfl
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
        (baseTopology_etale_le_fppf B)).app
        (FibredSite.objectInverseImageKind B S hS p hp SiteKind.fppf x F)) ≫
      (SheafOfModules.pushforward (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ))).map
        (objectInverseImageRestrictAlongSheafIso B S hS p hp F φ).hom).val.app V) m =
      (objectInverseImageRestrictAlongIso B S hS p hp F φ).hom.app
        (Opposite.op ((smallEtaleBaseChange (associatedBigEtaleSite B)
          (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).obj V.unop))
        ((FibredSite.objectInverseImageKind B S hS p hp .fppf x F).val.map
          ((SmallEtale.baseChangeProjection B (associatedBigEtaleSite B) rfl
            (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)).app V.unop).op
          m) :=
  rfl

/-- **The transposed comparison map of Stacks 06WC is the comparison for the inverse image**:
under the identifications `AlgebraicGeometry.Stack.objectInverseImageRestrictSheafIso` and
`AlgebraicGeometry.Stack.objectInverseImageRestrictAlongSheafIso`, the transpose of `c_φ` along
the sheafified pullback-pushforward adjunction is the comparison
`AlgebraicGeometry.SmallEtale.bigRestrictComparison` for the inverse image `x^*F` on the big
site of `U`. -/
theorem objectInverseImageRestrictSheafIso_hom_comp_homEquiv_sheafifiedRestrictComparisonApp
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x) :
    (objectInverseImageRestrictSheafIso B S hS p hp F x).hom ≫
      (sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl
        S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ
          ((fppfToEtaleSheafOfModules B S hS p hp).obj F)) =
      (SmallEtale.bigRestrictComparison B (associatedBigEtaleSite B) rfl
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
        (baseTopology_etale_le_fppf B)).app
        (FibredSite.objectInverseImageKind B S hS p hp SiteKind.fppf x F) ≫
      (SheafOfModules.pushforward (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ))).map
        (objectInverseImageRestrictAlongSheafIso B S hS p hp F φ).hom := by
  ext V m
  exact ((Stacks.SheafOfModules.moduleCatHom_comp_val_app_apply
    (objectInverseImageRestrictSheafIso B S hS p hp F x).hom _ V m).trans
    (homEquiv_sheafifiedRestrictComparisonApp_objectInverseImage_apply B S hS p hp F φ V
      m)).trans
    (bigRestrictComparison_comp_objectInverseImageRestrictAlongSheafIso_apply B S hS p hp F φ V
      m).symm

/-- The transposed comparison map of Stacks 06WC is the inverse of
`AlgebraicGeometry.Stack.objectInverseImageRestrictSheafIso` followed by the comparison for the
inverse image, that is
`objectInverseImageRestrictSheafIso_hom_comp_homEquiv_sheafifiedRestrictComparisonApp`
solved for the transposed comparison map.  The intermediate object of the composite is spelled
as the source of `AlgebraicGeometry.SmallEtale.bigRestrictComparison`, with the scheme `U`
regarded as an object of the big étale site. -/
theorem homEquiv_sheafifiedRestrictComparisonApp_eq_inv_comp
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) {x z : 𝒳}
    (φ : z ⟶ x) :
    (sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl
        S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
        (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ
          ((fppfToEtaleSheafOfModules B S hS p hp).obj F)) =
      @CategoryStruct.comp _ _ _
        ((SmallEtale.bigRestrict B (associatedBigEtaleSite B) rfl
          ((associatedBigEtaleSite B).obj (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj
          ((associatedBigEtaleSite B).obj (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).property .fppf
          (baseTopology_etale_le_fppf B)).obj
          (FibredSite.objectInverseImageKind B S hS p hp SiteKind.fppf x F)) _
        (@Iso.inv (SheafOfModules.{u} (SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((associatedBigEtaleSite B).obj (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).obj
          ((associatedBigEtaleSite B).obj (p.obj x).left.1
            (contains_base B (associatedBigEtaleSite B) rfl S hS p x)).property)) _ _ _
          (objectInverseImageRestrictSheafIso B S hS p hp F x))
        ((SmallEtale.bigRestrictComparison B (associatedBigEtaleSite B) rfl
          (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
          (baseTopology_etale_le_fppf B)).app
          (FibredSite.objectInverseImageKind B S hS p hp SiteKind.fppf x F) ≫
        (SheafOfModules.pushforward (SmallEtale.smallEtaleStructureMapRing
          (associatedBigEtaleSite B)
          (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ))).map
          (objectInverseImageRestrictAlongSheafIso B S hS p hp F φ).hom) :=
  (Iso.eq_inv_comp _).2
    (objectInverseImageRestrictSheafIso_hom_comp_homEquiv_sheafifiedRestrictComparisonApp
      B S hS p hp F φ)

end Sections

section Assembly

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **The comparison map of Stacks 06WC is an isomorphism for a quasi-coherent module.**  For a
quasi-coherent module `F` on the fppf site of `𝒳` (Stacks 06WG) and *any* arrow `φ : z ⟶ x` of
`𝒳`, the comparison map `c_φ : a_{small}^*(F|_{U_ét}) ⟶ F|_{W_ét}` of the étale reading of `F`,
on sheaves of modules, is an isomorphism. -/
theorem isIso_sheafifiedRestrictComparisonApp_of_quasicoherent
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) {x z : 𝒳} (φ : z ⟶ x) :
    IsIso (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp φ
      ((fppfToEtaleSheafOfModules B S hS p hp).obj F.obj)) := by
  obtain ⟨𝓕, ⟨g⟩⟩ := exists_associatedModule_iso_objectInverseImage B S hS p hp F x
  have : 𝓕.obj.IsQuasicoherent := 𝓕.property
  rw [← ((sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl S hS p hp
    (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _).symm_apply_apply
    (sheafifiedRestrictComparisonApp B (associatedBigEtaleSite B) rfl S hS p hp
    φ ((fppfToEtaleSheafOfModules B S hS p hp).obj F.obj))]
  exact Stacks.CategoryTheory.Adjunction.isIso_homEquiv_symm_of_eq_comp_conj
    (sheafifiedPullbackComparisonAdjunction B (associatedBigEtaleSite B) rfl S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ)))
    (SmallEtale.bigRestrictComparison B (associatedBigEtaleSite B) rfl
      (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
      (baseTopology_etale_le_fppf B)) g
    (SmallEtale.associatedModuleObjBaseChangeIso (associatedBigEtaleSite B)
      (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) 𝓕.obj)
    (SmallEtale.bigRestrictAssociatedModuleIso B (associatedBigEtaleSite B) rfl (p.obj x).left.1
      (contains_base B (associatedBigEtaleSite B) rfl S hS p x) .fppf
      (baseTopology_etale_le_fppf B) 𝓕.obj)
    (SmallEtale.bigRestrictAlongAssociatedModuleIso B (associatedBigEtaleSite B) rfl
      (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
      (baseTopology_etale_le_fppf B) 𝓕.obj)
    (objectInverseImageRestrictSheafIso B S hS p hp F.obj x)
    (objectInverseImageRestrictAlongSheafIso B S hS p hp F.obj φ)
    (SmallEtale.bigRestrictComparison_app_associatedModule B (associatedBigEtaleSite B) rfl
      (smallEtaleBaseMorphism B (associatedBigEtaleSite B) rfl S hS p φ) .fppf
      (baseTopology_etale_le_fppf B) 𝓕.obj) _
    (homEquiv_sheafifiedRestrictComparisonApp_eq_inv_comp B S hS p hp F.obj φ)

end Assembly

/-- **The flat base change property of a quasi-coherent module, on sheaves of modules.**  The
étale reading of a quasi-coherent module on the fppf site of `𝒳` has the flat base change
property of **Stacks 0762** read on sheaves of modules. -/
theorem hasFlatBaseChangePropertySheaf_toSiteModules_etale
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
      ((fppfToEtaleSheafOfModules B S hS p hp).obj F.obj) :=
  fun φ _ => isIso_sheafifiedRestrictComparisonApp_of_quasicoherent B S hS p hp F φ

/-- `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_toSiteModules_etale` for every
quasi-coherent module, with the étale reading of `F` written through
`AlgebraicGeometry.FibredSite.toSiteModules`. -/
theorem forall_hasFlatBaseChangePropertySheaf_toSiteModules_etale :
    ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F) :=
  hasFlatBaseChangePropertySheaf_toSiteModules_etale B S hS p hp

end AlgebraicGeometry.Stack
