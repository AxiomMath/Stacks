module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelThickeningRingHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# The comparison map of [Stacks, Tag 07IQ] on `Cris(X/S)` along a morphism, on global sections

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `ℱ` be a sheaf
of `𝒪_{X/S}`-modules on the **small** crystalline site `Cris(X/S)` and let
`g : (U', T', δ') ⟶ (U, T, δ)` be a morphism of `Cris(X/S)`.  This module is the small-site
counterpart of `StacksFrontier/AlgebraicGeometry/Crystalline/AffineComparisonAlong.lean`: it isolates
the part of the affine computation of the base change of sections that does not mention a tensor
product — the comparison map

`c_g : g^* ℱ_T ⟶ ℱ_{T'}`

of [Stacks, Tag 07IQ] read along the morphism `g : T' ⟶ T` of ambient schemes, its bijectivity on
sections for a crystal, and the resulting identification of `Γ(T', g^* ℱ_T)` with `ℱ(U', T', δ')`.

## Why it is repeated and what is reused

A sheaf of modules on `Cris(X/S)` is in general **not** the restriction of one on `CRIS(X/S)` —
producing one is essential surjectivity of `...SmallSite.restrictSheafOfModules`, which the tree
does not have — so the big-site statements cannot be instantiated here; this is the same situation
as in `SmallSite/AmbientRestrictionLift.lean` and `SmallSite/AmbientPresentationLift.lean`.

What *is* reused is everything in the big-site development that does not mention the sheaf.  The
ambient scheme of an object of `Cris(X/S)`, the restriction of `𝒪_{X/S}` to its opens, the two
adjunctions `Crystalline.GlobalCrystallineSituation.crysPullbackAdjunctionAlong` and
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong`, the identification
`Crystalline.GlobalCrystallineSituation.ambientSchemePullbackIso_eq_leftAdjointUniq` of their
comparison of left adjoints, and the normalisation
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong_unit_app_val_app` of the
unit are all stated for the underlying morphism of `CRIS(X/S)` and for an arbitrary sheaf of
modules on the ambient scheme, and are applied here verbatim at `g.hom`.  Only the three
sheaf-dependent constructions — the `f`-map, the comparison map and the chain tail — are written
again.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysAmbientSchemeModules` — the restriction `ℱ_T` to the ambient scheme of an object, at the
  type `AlgebraicGeometry.Scheme.Modules` the section notation is stated at.
* `crysRestrictOpenTopEquiv` — the sections over an object and over its restriction to the whole
  of its ambient scheme, identified.
* `crysAffineComparisonAlong` — the comparison map `g^* ℱ_T ⟶ ℱ_{T'}` read along the morphism
  `g : T' ⟶ T` of ambient schemes.
* `crysAmbientComparisonAlong` — the same map with both sides read over the structure sheaf of the
  ambient scheme.
* `crysAffineChainTailAlong` — the tail of the affine chain: the sections of `g^* ℱ_T` over the
  whole of `T'` carried to the sections of `ℱ` over `(U', T', δ')`.

## Main results

* `isIso_crysAffineComparisonAlong` — the comparison map of a crystal on `Cris(X/S)` is an
  isomorphism.
* `bijective_crysAffineChainTailAlong` — the tail of the chain is bijective for a crystal.
* `crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong` — the tail on a scalar
  multiple of a pullback of a section, which is the whole of the computation that follows the
  affine base-change comparison.

**No `@[stacks]` attribute is placed**: this is the small-site transcription of one step and not a
tag of its own.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))

/-! ### The restriction to the ambient scheme, at the type of the section notation -/

/-- The restriction `ℱ_T` of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` to the ambient scheme of
an object, at the type `AlgebraicGeometry.Scheme.Modules` of modules on that scheme.
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _.ringCatSheaf`, and the section
notation `Γ(-, U)` and the affine base-change comparison are stated at the former; this ascribes
`...SmallSite.ambientModuleRestriction` there. -/
def crysAmbientSchemeModules (B : CrystallineThickening S) :
    B.obj.thickening.target.scheme.Modules :=
  ambientModuleRestriction F B

/-! ### The sections over an object and over its restriction to the whole ambient scheme -/

/-- **The restriction map of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` along a morphism of the
site**, on sections over the objects.  Written as a plain function, as
`...SmallSite.crysSectionsP₀` is: the two spellings of the section ring of an object are equal but
carry different instances, so the semilinearity is stated separately below. -/
abbrev crysSiteRestrict {A B : CrystallineThickening S} (g : A ⟶ B) :
    F.val.obj (op B) → F.val.obj (op A) :=
  F.val.map g.op

/-- Restriction along a morphism of `Cris(X/S)` is additive. -/
theorem crysSiteRestrict_add {A B : CrystallineThickening S} (g : A ⟶ B)
    (s s' : F.val.obj (op B)) :
    crysSiteRestrict F g (s + s') = crysSiteRestrict F g s + crysSiteRestrict F g s' :=
  map_add _ s s'

/-- Restriction along a morphism of `Cris(X/S)` is semilinear over the restriction map of the
section rings. -/
theorem crysSiteRestrict_smul {A B : CrystallineThickening S} (g : A ⟶ B)
    (b : crysSheafRing S B.obj) (s : F.val.obj (op B)) :
    crysSiteRestrict F g (b • s) = crysSheafRingMap g.hom b • crysSiteRestrict F g s :=
  F.val.map_smul g.op b s

/-- Restriction along `h` followed by restriction along `g` is restriction along `g ≫ h`. -/
theorem crysSiteRestrict_comp {A B C : CrystallineThickening S} (g : A ⟶ B) (h : B ⟶ C)
    (x : F.val.obj (op C)) :
    crysSiteRestrict F g (crysSiteRestrict F h x) = crysSiteRestrict F (g ≫ h) x := by
  have hx := F.val.map_comp_apply h.op g.op x
  rw [← op_comp] at hx
  exact hx.symm

/-- Restriction along the identity morphism is the identity. -/
theorem crysSiteRestrict_id (A : CrystallineThickening S) (x : F.val.obj (op A)) :
    crysSiteRestrict F (𝟙 A) x = x :=
  map_id_apply F.val (op A) x

/-- **The sections of `ℱ` over an object and over its restriction to the whole of its ambient
scheme agree.**  The structure morphism of the restriction to `⊤` is an isomorphism of
`Cris(X/S)`, by `...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`, so restriction
along it is a bijection, with inverse the restriction along its inverse. -/
theorem bijective_crysSiteRestrict_restrictOpenHom_top (B : CrystallineThickening S) :
    Function.Bijective (crysSiteRestrict F
      (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens))) := by
  have := CrystallineThickening.isIso_restrictOpenHom_top B
  refine Function.bijective_iff_has_inverse.mpr
    ⟨crysSiteRestrict F (inv (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens))),
      fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [crysSiteRestrict_comp, IsIso.inv_hom_id, crysSiteRestrict_id]
  · rw [crysSiteRestrict_comp, IsIso.hom_inv_id, crysSiteRestrict_id]

/-- **The sections of `ℱ` over an object and over its restriction to the whole of its ambient
scheme, as an additive equivalence.** -/
def crysRestrictOpenTopEquiv (B : CrystallineThickening S) :
    F.val.obj (op B) ≃+ F.val.obj (op (B.restrictOpen (⊤ :
      B.obj.thickening.target.scheme.Opens))) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (crysSiteRestrict F
        (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)))
      (crysSiteRestrict_add F _))
    (bijective_crysSiteRestrict_restrictOpenHom_top F B)

/-- `crysRestrictOpenTopEquiv` is restriction along the structure morphism of the restriction to
`⊤`. -/
@[simp]
theorem crysRestrictOpenTopEquiv_apply (B : CrystallineThickening S) (s : F.val.obj (op B)) :
    crysRestrictOpenTopEquiv F B s =
      crysSiteRestrict F (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)) s :=
  rfl

/-- Restricting to `⊤` a section obtained from the inverse of `crysRestrictOpenTopEquiv` returns
the original section. -/
@[simp]
theorem crysSiteRestrict_crysRestrictOpenTopEquiv_symm (B : CrystallineThickening S)
    (x : F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens)))) :
    crysSiteRestrict F (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens))
        ((crysRestrictOpenTopEquiv F B).symm x) = x :=
  (crysRestrictOpenTopEquiv F B).apply_symm_apply x

/-! ### The two readings of a section of the restriction to the ambient scheme -/

/-- A section of `ℱ` over the restriction of an object to the whole of its ambient scheme, read as
a section of the restricted sheaf `ℱ_T` over the whole scheme.  The identity. -/
def crysAmbientModuleSection (B : CrystallineThickening S)
    (x : F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens)))) :
    Γ(crysAmbientSchemeModules F B, ⊤) := x

/-- The reading of `...SmallSite.crysAmbientModuleSection` in the other direction. -/
def crysSiteModuleSection (B : CrystallineThickening S)
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens))) := x

/-- `crysSiteModuleSection` is a left inverse of `crysAmbientModuleSection`. -/
@[simp]
theorem crysSiteModuleSection_crysAmbientModuleSection (B : CrystallineThickening S)
    (x : F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens)))) :
    crysSiteModuleSection F B (crysAmbientModuleSection F B x) = x := rfl

/-- `crysSiteModuleSection` is additive. -/
theorem crysSiteModuleSection_add (B : CrystallineThickening S)
    (x y : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysSiteModuleSection F B (x + y) =
      crysSiteModuleSection F B x + crysSiteModuleSection F B y := rfl

/-- `...SmallSite.crysSiteModuleSection`, as an additive map. -/
def crysSiteModuleSectionHom (B : CrystallineThickening S) :
    Γ(crysAmbientSchemeModules F B, ⊤) →+
      F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens))) :=
  AddMonoidHom.mk' (crysSiteModuleSection F B) (crysSiteModuleSection_add F B)

/-- That reading is a bijection, being the identity. -/
theorem bijective_crysSiteModuleSectionHom (B : CrystallineThickening S) :
    Function.Bijective (crysSiteModuleSectionHom F B) :=
  ⟨fun _ _ h ↦ h, fun y ↦ ⟨crysAmbientModuleSection F B y, rfl⟩⟩

/-- **The scalars of the sections of `𝒪_T` act on the sections of `ℱ_T` through the restriction
map of the site.** -/
theorem crysAmbientModuleSection_smul (B : CrystallineThickening S) (b : crysSheafRing S B.obj)
    (x : F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens)))) :
    ambientRingSection B.obj b • crysAmbientModuleSection F B x =
      crysAmbientModuleSection F B (crysSheafRingMap
        (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).hom b • x) := rfl

/-- `...SmallSite.crysAmbientModuleSection_smul`, read with the scalar and the section in the
spelling of the ambient scheme. -/
theorem smul_eq_crysAmbientModuleSection (B : CrystallineThickening S)
    (r : Γ(B.obj.thickening.target.scheme, ⊤)) (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    r • x = crysAmbientModuleSection F B
      (crysSheafRingMap (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).hom
        (siteRingSection B.obj r) • crysSiteModuleSection F B x) :=
  crysAmbientModuleSection_smul F B (siteRingSection B.obj r) (crysSiteModuleSection F B x)

/-- **The inverse of the restriction of sections to the whole of the ambient scheme is semilinear
over the restriction map of the site.** -/
theorem crysRestrictOpenTopEquiv_symm_smul (B : CrystallineThickening S)
    (r : Γ(B.obj.thickening.target.scheme, ⊤)) (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    siteRingSection B.obj r • (crysRestrictOpenTopEquiv F B).symm
        (crysSiteModuleSection F B x) =
      (crysRestrictOpenTopEquiv F B).symm (crysSiteModuleSection F B (r • x)) := by
  refine (crysRestrictOpenTopEquiv F B).injective ?_
  rw [crysRestrictOpenTopEquiv_apply, crysRestrictOpenTopEquiv_apply, crysSiteRestrict_smul,
    crysSiteRestrict_crysRestrictOpenTopEquiv_symm,
    crysSiteRestrict_crysRestrictOpenTopEquiv_symm, smul_eq_crysAmbientModuleSection,
    crysSiteModuleSection_crysAmbientModuleSection]

/-- **The restriction of a morphism of `Cris(X/S)` to the whole of the two ambient schemes**, with
its source named at `⊤` rather than at the preimage of `⊤`, the two being equal. -/
def crysRestrictOpenMapTop {A B : CrystallineThickening S} (g : A ⟶ B) :
    A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens) ⟶
      B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens) :=
  CrystallineThickening.restrictOpenMap g ⊤

/-- **Restricting a section to the whole of the ambient scheme commutes with restricting along a
morphism of the site.** -/
theorem crysSiteRestrict_crysRestrictOpenMapTop {A B : CrystallineThickening S} (g : A ⟶ B)
    (t : F.val.obj (op B)) :
    crysSiteRestrict F (crysRestrictOpenMapTop g) (crysSiteRestrict F
        (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)) t) =
      crysSiteRestrict F (A.restrictOpenHom (⊤ : A.obj.thickening.target.scheme.Opens))
        (crysSiteRestrict F g t) := by
  rw [crysSiteRestrict_comp, crysSiteRestrict_comp]
  exact congrArg (fun k ↦ crysSiteRestrict F k t)
    (CrystallineThickening.restrictOpenMap_restrictOpenHom g ⊤)

/-- **The inverse of the restriction of sections to the whole of the ambient scheme is semilinear
over the restriction map of the site**, stated on a section of `𝒪_{X/S}` over the object. -/
theorem crysRestrictOpenTopEquiv_symm_smul_site (B : CrystallineThickening S)
    (b : crysSheafRing S B.obj)
    (z : F.val.obj (op (B.restrictOpen (⊤ : B.obj.thickening.target.scheme.Opens)))) :
    (crysRestrictOpenTopEquiv F B).symm (crysSheafRingMap
          (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).hom b • z) =
      b • (crysRestrictOpenTopEquiv F B).symm z := by
  refine (crysRestrictOpenTopEquiv F B).injective ?_
  rw [AddEquiv.apply_symm_apply, crysRestrictOpenTopEquiv_apply, crysSiteRestrict_smul,
    crysSiteRestrict_crysRestrictOpenTopEquiv_symm]

/-! ### The comparison of the pullback along the morphism of ambient schemes with `ℱ_{T'}` -/

variable {B B' : CrystallineThickening S} (g : B' ⟶ B)

/-- **The comparison map `g^* ℱ_T ⟶ ℱ_{T'}` of [Stacks, Tag 07IQ] on `Cris(X/S)`, read along the
morphism `g : T' ⟶ T` of ambient schemes.**  It is the adjoint transpose of the `f`-map of
[Stacks, Tag 07IQ] through
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong`, which is an adjunction of
the underlying morphism of `CRIS(X/S)` and mentions no sheaf on either site. -/
def crysAffineComparisonAlong :
    (SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso B'.obj).hom).obj
        ((Scheme.Modules.pullback g.hom.targetHom.hom).obj (crysAmbientSchemeModules F B)) ⟶
      moduleRestrictionSheaf F B' :=
  ((ambientPullbackAdjunctionAlong g.hom).homEquiv _ _).symm
    ((SheafOfModules.restrictScalars
      (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map (moduleFMapSheaf F g))

/-- **The normalisation of the comparison map: it carries the pullback of a section to the
restriction of that section along `g`.** -/
theorem crysAffineComparisonAlong_pullbackSection
    (h : (⊤ : B'.obj.thickening.target.scheme.Opens) ≤ g.hom.targetHom.hom ⁻¹ᵁ ⊤)
    (a : (crysAmbientSchemeModules F B).val.obj (op ⊤)) :
    (crysAffineComparisonAlong F g).val.app (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤))
        (Scheme.Modules.pullbackSection g.hom.targetHom.hom
          (crysAmbientSchemeModules F B) ⊤ ⊤ h a) =
      F.val.map (CrystallineThickening.restrictOpenMap g ⊤).op a := by
  have hθ : (ambientPullbackAdjunctionAlong g.hom).unit.app (crysAmbientSchemeModules F B) ≫
        (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g.hom) ⋙
          SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map
          (crysAffineComparisonAlong F g) =
      (SheafOfModules.restrictScalars
        (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map (moduleFMapSheaf F g) := by
    show (ambientPullbackAdjunctionAlong g.hom).homEquiv _ _
      (crysAffineComparisonAlong F g) = _
    exact Equiv.apply_symm_apply _ _
  refine (congrArg (fun y ↦ (crysAffineComparisonAlong F g).val.app
      (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤)) y) ?_).trans (congrArg (fun k ↦ k.val.app (op ⊤) a) hθ)
  exact (Scheme.Modules.pullbackSection_top _ _ h a).trans
    (ambientPullbackAdjunctionAlong_unit_app_val_app g.hom
      (crysAmbientSchemeModules F B) (op ⊤) a).symm

/-- **The same adjoint transpose, taken through the crystalline `f`-map, is the comparison map
`c_g` of [Stacks, Tag 07IQ] on `Cris(X/S)`.** -/
theorem crysPullbackAdjunctionAlong_homEquiv_symm_moduleFMapSheaf :
    ((crysPullbackAdjunctionAlong g.hom).homEquiv
        (crysAmbientSchemeModules F B) (moduleRestrictionSheaf F B')).symm
      ((SheafOfModules.restrictScalars
        (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map (moduleFMapSheaf F g)) =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
            (moduleRestrictionSheaf F B)) ≫
        moduleComparisonSheaf F g := by
  have hinner : (SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso B.obj).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map
            (moduleFMapSheaf F g)) ≫
        (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
          ((SheafOfModules.pushforward.{u}
              (Thickening.ringRestrictionSheafFMap g.hom)).obj
            (moduleRestrictionSheaf F B')) =
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
          (moduleRestrictionSheaf F B) ≫
        moduleFMapSheaf F g :=
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.naturality
        (moduleFMapSheaf F g)
  have hcounit : (crysPullbackAdjunctionAlong g.hom).counit.app
        (moduleRestrictionSheaf F B') =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
            ((SheafOfModules.pushforward.{u}
                (Thickening.ringRestrictionSheafFMap g.hom)).obj
              (moduleRestrictionSheaf F B'))) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (Thickening.ringRestrictionSheafFMap g.hom)).counit.app
          (moduleRestrictionSheaf F B') :=
    Adjunction.comp_counit_app
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso B.obj))
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (Thickening.ringRestrictionSheafFMap g.hom))
      (moduleRestrictionSheaf F B')
  show (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
        ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso B.obj).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso B.obj).inv).map
            (moduleFMapSheaf F g))) ≫
      (crysPullbackAdjunctionAlong g.hom).counit.app (moduleRestrictionSheaf F B') =
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
        ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
          (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
          (moduleRestrictionSheaf F B)) ≫
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          (moduleFMapSheaf F g) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).counit.app
          (moduleRestrictionSheaf F B')
  rw [hcounit, ← Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp, Category.assoc]

/-- **The comparison map `g^* ℱ_T ⟶ ℱ_{T'}` of a crystal on `Cris(X/S)` is an isomorphism.** -/
theorem isIso_crysAffineComparisonAlong (hF : IsSheafCrystal F) :
    IsIso (crysAffineComparisonAlong F g) := by
  have hc : IsIso (moduleComparisonSheaf F g) := hF _ _ _
  have hε : IsIso ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
      (moduleRestrictionSheaf F B)) :=
    Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app _ _
  have hPε : IsIso ((SheafOfModules.pullback.{u}
        (Thickening.ringRestrictionSheafFMap g.hom)).map
      ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
        (moduleRestrictionSheaf F B))) :=
    Functor.map_isIso _ _
  have : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g.hom)
      (ambientPullbackAdjunctionAlong g.hom)).hom.app (crysAmbientSchemeModules F B)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _
  have h : (Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g.hom)
          (ambientPullbackAdjunctionAlong g.hom)).hom.app (crysAmbientSchemeModules F B) ≫
        crysAffineComparisonAlong F g =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso B.obj)).counit.app
            (moduleRestrictionSheaf F B)) ≫
        moduleComparisonSheaf F g :=
    (Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (crysPullbackAdjunctionAlong g.hom)
        (ambientPullbackAdjunctionAlong g.hom) _).trans
      (crysPullbackAdjunctionAlong_homEquiv_symm_moduleFMapSheaf F g)
  rw [← isIso_comp_left_iff ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g.hom)
    (ambientPullbackAdjunctionAlong g.hom)).hom.app (crysAmbientSchemeModules F B)), h]
  exact IsIso.comp_isIso' hPε hc

/-- **The comparison map of a crystal on `Cris(X/S)` is bijective on sections over every open of
`T'`.** -/
theorem bijective_crysAffineComparisonAlong_val_app (hF : IsSheafCrystal F)
    (W : (B'.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Function.Bijective fun x ↦ (crysAffineComparisonAlong F g).val.app W x := by
  have := isIso_crysAffineComparisonAlong F g hF
  have := Stacks.SheafOfModules.isIso_val_app_of_isIso (crysAffineComparisonAlong F g) W
  exact ConcreteCategory.bijective_of_isIso ((crysAffineComparisonAlong F g).val.app W)

/-! ### The comparison map read over the structure sheaf of the ambient scheme -/

/-- **The comparison map `g^* ℱ_T ⟶ ℱ_{T'}` of [Stacks, Tag 07IQ] on `Cris(X/S)` with both sides
read over the structure sheaf of the ambient scheme.** -/
def crysAmbientComparisonAlong :
    (Scheme.Modules.pullback g.hom.targetHom.hom).obj (crysAmbientSchemeModules F B) ⟶
      crysAmbientSchemeModules F B' :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
    (Thickening.ringRestrictionSheafStructureIso B'.obj)).homEquiv _ _
      (crysAffineComparisonAlong F g)

/-- **The change of spelling does not move sections.** -/
theorem crysAmbientComparisonAlong_val_app (W : (B'.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (y : ((Scheme.Modules.pullback g.hom.targetHom.hom).obj
      (crysAmbientSchemeModules F B)).val.obj W) :
    (crysAmbientComparisonAlong F g).val.app W y =
      (crysAffineComparisonAlong F g).val.app W y :=
  Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app _ _ W y

/-- The comparison map on sections over the whole of `T'`, as an additive map. -/
def crysAmbientComparisonAlongTop :
    Γ((Scheme.Modules.pullback g.hom.targetHom.hom).obj (crysAmbientSchemeModules F B), ⊤) →+
      Γ(crysAmbientSchemeModules F B', ⊤) :=
  AddMonoidHom.mk' (fun y ↦ (crysAmbientComparisonAlong F g).app ⊤ y) (fun y y' ↦ map_add _ y y')

/-- **For a crystal that map is bijective.** -/
theorem bijective_crysAmbientComparisonAlongTop (hF : IsSheafCrystal F) :
    Function.Bijective (crysAmbientComparisonAlongTop F g) := by
  have h : (crysAmbientComparisonAlongTop F g : _ → _) =
      fun y ↦ (crysAffineComparisonAlong F g).val.app (op ⊤) y :=
    funext fun y ↦ crysAmbientComparisonAlong_val_app F g (op ⊤) y
  rw [h]
  exact bijective_crysAffineComparisonAlong_val_app F g hF (op ⊤)

/-- The pullback along `g` of a section of `ℱ_T` over the whole of `T`, as a section of `g^* ℱ_T`
over the whole of `T'`. -/
def crysAmbientPullbackSectionTopAlong (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    Γ((Scheme.Modules.pullback g.hom.targetHom.hom).obj (crysAmbientSchemeModules F B), ⊤) :=
  Scheme.Modules.pullbackSection g.hom.targetHom.hom (crysAmbientSchemeModules F B) ⊤ ⊤
    (top_le_preimage_ambient g.hom) x

/-- **The normalisation of the comparison map in the ambient spelling.** -/
theorem crysAmbientComparisonAlong_pullbackSection
    (h : (⊤ : B'.obj.thickening.target.scheme.Opens) ≤ g.hom.targetHom.hom ⁻¹ᵁ ⊤)
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    (crysAmbientComparisonAlong F g).app ⊤
        (Scheme.Modules.pullbackSection g.hom.targetHom.hom
          (crysAmbientSchemeModules F B) ⊤ ⊤ h x) =
      crysAmbientModuleSection F B'
        (crysSiteRestrict F (crysRestrictOpenMapTop g) (crysSiteModuleSection F B x)) :=
  (crysAmbientComparisonAlong_val_app F g (op ⊤) _).trans
    (crysAffineComparisonAlong_pullbackSection F g h (crysSiteModuleSection F B x))

/-- The same normalisation, with the pullback of the section named. -/
theorem crysAmbientComparisonAlong_crysAmbientPullbackSectionTopAlong
    (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    (crysAmbientComparisonAlong F g).app ⊤ (crysAmbientPullbackSectionTopAlong F g x) =
      crysAmbientModuleSection F B'
        (crysSiteRestrict F (crysRestrictOpenMapTop g) (crysSiteModuleSection F B x)) :=
  crysAmbientComparisonAlong_pullbackSection F g (top_le_preimage_ambient g.hom) x

/-- **The tail of the affine chain**, after the base-change comparison: the sections of `g^* ℱ_T`
over the whole of `T'` are carried to the sections of `ℱ` over `(U', T', δ')`. -/
def crysAffineChainTailAlong :
    Γ((Scheme.Modules.pullback g.hom.targetHom.hom).obj (crysAmbientSchemeModules F B), ⊤) →+
      F.val.obj (op B') :=
  ((crysRestrictOpenTopEquiv F B').symm.toAddMonoidHom.comp
    (crysSiteModuleSectionHom F B')).comp (crysAmbientComparisonAlongTop F g)

/-- The tail of the chain, written out. -/
theorem crysAffineChainTailAlong_apply
    (y : Γ((Scheme.Modules.pullback g.hom.targetHom.hom).obj
      (crysAmbientSchemeModules F B), ⊤)) :
    crysAffineChainTailAlong F g y =
      (crysRestrictOpenTopEquiv F B').symm
        (crysSiteModuleSection F B' ((crysAmbientComparisonAlong F g).app ⊤ y)) := rfl

/-- **The tail of the chain is bijective for a crystal**: each of its three factors is. -/
theorem bijective_crysAffineChainTailAlong (hF : IsSheafCrystal F) :
    Function.Bijective (crysAffineChainTailAlong F g) :=
  ((crysRestrictOpenTopEquiv F B').symm.bijective.comp
      (bijective_crysSiteModuleSectionHom F B')).comp
    (bijective_crysAmbientComparisonAlongTop F g hF)

/-- **The tail of the chain on a scalar multiple of a pullback of a section.**  This is the whole
of the computation that follows the base-change comparison. -/
theorem crysAffineChainTailAlong_smul_crysAmbientPullbackSectionTopAlong
    (t : crysSheafRing S B'.obj) (x : Γ(crysAmbientSchemeModules F B, ⊤)) :
    crysAffineChainTailAlong F g
        (ambientRingSection B'.obj t • crysAmbientPullbackSectionTopAlong F g x) =
      t • (crysRestrictOpenTopEquiv F B').symm
        (crysSiteRestrict F (crysRestrictOpenMapTop g) (crysSiteModuleSection F B x)) := by
  rw [crysAffineChainTailAlong_apply, Scheme.Modules.Hom.app_smul,
    crysAmbientComparisonAlong_crysAmbientPullbackSectionTopAlong,
    crysAmbientModuleSection_smul, crysSiteModuleSection_crysAmbientModuleSection,
    crysRestrictOpenTopEquiv_symm_smul_site]

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
