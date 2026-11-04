module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunctionCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModulePushforwardCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionTotalDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChangeAlgebraicStacks

/-!
# Direct images of sheaves of modules along 1-morphisms of categories fibred in groupoids

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`. It is continuous and cocontinuous for the étale topologies the two categories inherit
(Stacks 06NW), its inverse image carries `𝒪_𝒴` to `𝒪_𝒳`, and it induces a morphism of ringed topoi
(Stacks 06TW) whose direct image of sheaves of `𝒪_𝒳`-modules is computed, on underlying
presheaves, by the right Kan extension along `f.op`.

This file identifies that direct image with the direct image
`Stacks.SheafOfModules.pushforwardCocontinuous` along the cocontinuous functor `f` (Stacks 00XO),
for the structure map `𝒪_𝒴 ⟶ {}_s f 𝒪_𝒳` adjunct to the identification `f⁻¹𝒪_𝒴 = 𝒪_𝒳`, and
reads off its module structure on the legs of the limit cone computing the Kan extension: a
section `r` of `𝒪_𝒴` over `V` acts on the leg at `(U, ψ : V ⟶ f(U))` through its restriction
along `ψ`. In this form the direct image meets the base change of right Kan extensions of
`Stacks.SheafOfModules.directImageBaseChange`, and for the canonical 2-cartesian square

```
𝒴' ×_𝒴 𝒳 --g'--> 𝒳
    |            |
    f'           f
    v            v
    𝒴' ---g--->  𝒴
```

the base change `(g')^* ⋙ f'_* ≅ f_* ⋙ g^*` of Stacks 075B holds for sheaves of modules with
sections in the universe of the schemes, which is the module category of the étale ringed topoi
of Stacks 06TW and of the derived direct images of Stacks 075N.

## Main definitions

* `AlgebraicGeometry.FibredSite.canonicalStructureMap`: the structure map
  `𝒪_𝒴 ⟶ {}_s f 𝒪_𝒳`.
* `AlgebraicGeometry.FibredSite.pushforwardModulesIsoPushforwardCocontinuous`: the direct image
  of sheaves of modules along the morphism of ringed topoi of `f` is the cocontinuous direct
  image.
* `AlgebraicGeometry.FibredSite.pushforwardModulesBaseChangeIso`: Stacks 075B for these direct
  images and the inverse images `AlgebraicGeometry.Stack.modulePullback` of Stacks 06WE.

## Main results

* `AlgebraicGeometry.FibredSite.canonicalStructureMap_leg`: the structure map on the legs.
* `AlgebraicGeometry.FibredSite.pushforwardCocontinuous_leg_smul`: the module structure of the
  cocontinuous direct image on the legs.

## Implementation notes

`AlgebraicGeometry.Stack.moduleSheafPushforwardBaseChangeIso` is the same base change for the
direct image of `AlgebraicGeometry.Stack.ModuleSheafFunctoriality`, whose sections live in a
universe strictly above the objects of the site, as the limits of its construction require. The
direct image of a morphism of ringed topoi has sections in the universe of the schemes, so it is
compared here with the cocontinuous direct image instead, whose right Kan extensions exist at that
universe because the categories are essentially small.

## References

* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w v' w' v'' w''

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  Functor.hasPointwiseRightKanExtension_of_essentiallySmall_of_locallySmall

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]

/-- The component of the `eqToHom` of an equality of sheaves is the `eqToHom` of the equality
of its components. -/
theorem eqToHom_hom_app {F G : Sheaf J A} (h : F = G) (x : Cᵒᵖ) :
    (eqToHom h).hom.app x = eqToHom (by rw [h]) := by
  subst h
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q F) (τ : SiteKind)

include hp hq hF in
/-- A 1-morphism `F` of categories fibred in groupoids over `S` is cocontinuous for the topologies
the two categories inherit from the site of kind `τ`. -/
theorem isCocontinuous_associatedTopology :
    F.IsCocontinuous (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ) :=
  have := hp.isFibered
  have := hq.isFibered
  (hF.isContinuous_and_isCocontinuous_inheritedTopology ((B.baseTopology τ).over (B.obj hS))).2

include hp hq hF in
/-- A 1-morphism `F` of categories fibred in groupoids over `S` is continuous for the topologies
the two categories inherit from the site of kind `τ`. -/
theorem isContinuous_associatedTopology :
    F.IsContinuous (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ) :=
  have := hp.isFibered
  have := hq.isFibered
  (hF.isContinuous_and_isCocontinuous_inheritedTopology ((B.baseTopology τ).over (B.obj hS))).1

include hF in
/-- The inverse image `F⁻¹𝒪_𝒴` of the structure sheaf of rings of `𝒴` along a 1-morphism `F` of
categories fibred in groupoids is the structure sheaf `𝒪_𝒳`. -/
theorem ringStructureSheafCore_inverseImage_eq :
    letI := isContinuous_associatedTopology B S hS p q hp hq F hF τ
    (F.sheafPushforwardContinuous RingCat.{u} (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ)).obj (ringStructureSheafCore B S hS q hq τ) =
      ringStructureSheafCore B S hS p hp τ := by
  obtain ⟨h, -⟩ := hF
  subst h
  rfl

variable [EssentiallySmall.{u} 𝒳] [LocallySmall.{u} 𝒴]

/-- The structure map `𝒪_𝒴 ⟶ F_*𝒪_𝒳` of a 1-morphism `F` of categories fibred in groupoids, as
a map of sheaves of rings into the direct image along the cocontinuous functor `F`: the adjunct of
the identification `F⁻¹𝒪_𝒴 = 𝒪_𝒳` of the restricted structure sheaf. -/
def canonicalStructureMap :
    letI := isContinuous_associatedTopology B S hS p q hp hq F hF τ
    letI := isCocontinuous_associatedTopology B S hS p q hp hq F hF τ
    ringStructureSheafCore B S hS q hq τ ⟶
      (F.sheafPushforwardCocontinuous RingCat.{u} (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ)).obj (ringStructureSheafCore B S hS p hp τ) :=
  letI := isContinuous_associatedTopology B S hS p q hp hq F hF τ
  letI := isCocontinuous_associatedTopology B S hS p q hp hq F hF τ
  (F.sheafAdjunctionCocontinuous RingCat.{u} _ _).homEquiv _ _
    (eqToHom (ringStructureSheafCore_inverseImage_eq B S hS p q hp hq F hF τ))

/-- On the leg at `(U, ψ : V ⟶ F(U))`, the structure map acts as restriction along `ψ` followed by
the identification `F⁻¹𝒪_𝒴 = 𝒪_𝒳`: the defining property of the adjunct. -/
theorem canonicalStructureMap_leg (V : 𝒴ᵒᵖ) (j : StructuredArrow V F.op)
    (r : (ringStructureSheafCore B S hS q hq τ).obj.obj V) :
    (Stacks.SheafOfModules.ranπ F.op (ringStructureSheafCore B S hS p hp τ).obj V j).hom
      (((canonicalStructureMap B S hS p q hp hq F hF τ).hom.app V).hom r) =
    ((eqToHom (ringStructureSheafCore_inverseImage_eq B S hS p q hp hq F hF τ)).hom.app
      j.right).hom (((ringStructureSheafCore B S hS q hq τ).obj.map j.hom).hom r) := by
  let := isContinuous_associatedTopology B S hS p q hp hq F hF τ
  let := isCocontinuous_associatedTopology B S hS p q hp hq F hF τ
  have key : (canonicalStructureMap B S hS p q hp hq F hF τ).hom.app V ≫
        Stacks.SheafOfModules.ranπ F.op (ringStructureSheafCore B S hS p hp τ).obj V j =
      (ringStructureSheafCore B S hS q hq τ).obj.map j.hom ≫
        (eqToHom (ringStructureSheafCore_inverseImage_eq B S hS p q hp hq F hF τ)).hom.app
          j.right := by
    dsimp only [canonicalStructureMap]
    rw [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.sheafAdjunctionCocontinuous_unit_app_hom]
    exact (Category.assoc _ _ _).trans ((congrArg (fun z => _ ≫ z)
      (Stacks.SheafOfModules.ranπ_map_functor F.op
        (eqToHom (ringStructureSheafCore_inverseImage_eq B S hS p q hp hq F hF τ)).hom V j)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _)
        (Stacks.SheafOfModules.ranAdjunction_unit_app_ranπ F.op _ V j))))
  exact ConcreteCategory.congr_hom key r

/-- On the leg at `(U, ψ : V ⟶ F(U))` of the right Kan extension, the structure ring map of the
étale morphism of ringed topoi of `F` agrees with `canonicalStructureMap`. -/
theorem canonicalStructureMap_compat (V : 𝒴ᵒᵖ) (j : StructuredArrow V F.op)
    (r : (ringStructureSheafCore B S hS q hq .etale).obj.obj V) :
    Stacks.SheafOfModules.ranπ F.op
        (Sheaf.ringSheaf (ringStructureSheafCore B S hS p hp .etale)).obj V j
        (((RingedToposHom.structureRingMap
          (ringedToposMorphism B S hS p q hp hq F hF .etale)).hom.app V).hom r) =
      (Stacks.SheafOfModules.ranπ F.op (ringStructureSheafCore B S hS p hp .etale).obj V j).hom
        (((canonicalStructureMap B S hS p q hp hq F hF .etale).hom.app V).hom r) := by
  rw [canonicalStructureMap_leg]
  have h := Space.ranCounit_app_forgetFSharp_ringedToposMorphism B S hS p q hp hq F hF
    j.right.unop V.unop j.hom.unop r
  refine Eq.trans h ?_
  rw [Space.forgetRing_map_ringedToposMorphism_fSharpInverseImage]
  obtain ⟨hc, -⟩ := hF
  subst hc
  rfl

/-- **The direct image of sheaves of modules along a 1-morphism of categories fibred in
groupoids is the direct image along the cocontinuous functor.** The direct image of modules of
the morphism of ringed topoi of Stacks 06TW is identified with
`Stacks.SheafOfModules.pushforwardCocontinuous` over the canonical structure map, whose module
structure is described on the legs of the limit cone computing the right Kan extension. -/
def pushforwardModulesIsoPushforwardCocontinuous :
    letI : F.IsCocontinuous (C := 𝒳) (D := 𝒴) (associatedRingedTopos B S hS p hp .etale).J
        (associatedRingedTopos B S hS q hq .etale).J :=
      isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale
    RingedToposHom.pushforwardModules.{w, v, u, w', v', u}
        (ringedToposMorphism B S hS p q hp hq F hF .etale) ≅
      Stacks.SheafOfModules.pushforwardCocontinuous.{u} F
        (canonicalStructureMap B S hS p q hp hq F hF .etale) := by
  letI := isContinuous_associatedTopology B S hS p q hp hq F hF .etale
  letI := isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale
  have e1 := @Stacks.SheafOfModules.pushforwardCocontinuousModulesIso.{u, w, v, w', v'} _ _ _ _ F
    (associatedRingedTopos B S hS p hp .etale).J (associatedRingedTopos B S hS q hq .etale).J
    (isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale)
    (AlgebraicGeometry.hasSheafCompose_forget_ringCat (C := 𝒳) _)
    (inferInstanceAs ((BigFppfOver.associatedTopology B S hS p .etale).HasSheafCompose
      (forget AddCommGrpCat.{u})))
    (inferInstanceAs ((BigFppfOver.associatedTopology B S hS q .etale).HasSheafCompose
      (forget AddCommGrpCat.{u})))
    inferInstance inferInstance inferInstance
    (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp .etale).O)
    (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp .etale).O) (𝟙 _)
    (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS q hq .etale).O)
    (RingedToposHom.structureRingMap (ringedToposMorphism B S hS p q hp hq F hF .etale))
    (canonicalStructureMap B S hS p q hp hq F hF .etale)
    (fun V j r => by exact canonicalStructureMap_compat B S hS p q hp hq F hF V j r)
  exact e1

/-- **The module structure of the cocontinuous direct image, read on the legs.** A section `r`
of `𝒪_𝒴` over `V` acts on the leg at `(U, ψ : V ⟶ F(U))` of the right Kan extension through its
restriction along `ψ`, transported along `𝒪_𝒳 = F⁻¹𝒪_𝒴`. This is the leg hypothesis of
`Stacks.SheafOfModules.directImageBaseChange`. -/
theorem pushforwardCocontinuous_leg_smul
    (M : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS p hp (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale))) (V : 𝒴ᵒᵖ)
    (j : StructuredArrow V F.op) (r : (ringStructureSheafCore B S hS q hq .etale).obj.obj V)
    (s : (letI := isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale
      (Stacks.SheafOfModules.pushforwardCocontinuous.{u} F
        (canonicalStructureMap B S hS p q hp hq F hF .etale)).obj M).val.obj V) :
    letI := isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale
    Stacks.SheafOfModules.ranπ F.op M.val.presheaf V j (r • s) =
      (eqToHom (Stack.ringStructureSheafCore_obj_eq B S hS p q hp hq F hF.comp_eq
          (B.baseTopology .etale) (B.baseTopology_le_topology .etale)).symm).app j.right
          ((Stack.ringStructureSheafCore B S hS q hq (B.baseTopology .etale)
            (B.baseTopology_le_topology .etale)).obj.map j.hom r) •
        (show M.val.obj j.right from Stacks.SheafOfModules.ranπ F.op M.val.presheaf V j s) := by
  let := isContinuous_associatedTopology B S hS p q hp hq F hF .etale
  let := isCocontinuous_associatedTopology B S hS p q hp hq F hF .etale
  have h := ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranSMul_π F
    (Stacks.SheafOfModules.structureMapPresheaf F
      (canonicalStructureMap B S hS p q hp hq F hF .etale)) M.val V r j) s
  refine h.trans ?_
  have key : (Stacks.SheafOfModules.scalarπ F (Stacks.SheafOfModules.structureMapPresheaf F
      (canonicalStructureMap B S hS p q hp hq F hF .etale)) V j).hom r =
      (eqToHom (Stack.ringStructureSheafCore_obj_eq B S hS p q hp hq F hF.comp_eq
          (B.baseTopology .etale) (B.baseTopology_le_topology .etale)).symm).app j.right
          ((Stack.ringStructureSheafCore B S hS q hq (B.baseTopology .etale)
            (B.baseTopology_le_topology .etale)).obj.map j.hom r) := by
    refine (canonicalStructureMap_leg B S hS p q hp hq F hF .etale V j r).trans ?_
    rw [Sheaf.eqToHom_hom_app, eqToHom_app]
    rfl
  exact congrArg (fun (a : (Stack.ringStructureSheafCore B S hS p hp (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale)).obj.obj j.right) => a • (show M.val.obj j.right from
    Stacks.SheafOfModules.ranπ F.op M.val.presheaf V j s)) key

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.FibredSite

/-! ### The base change square -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
  [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)]

/-- **Stacks 075B for sheaves of modules at the module universe of the étale sites.** For the
canonical 2-cartesian square of categories fibred in groupoids, with `g' = fst` and `f' = snd`,
`(g')^* ⋙ f'_* ≅ f_* ⋙ g^*`, where `g^*`, `(g')^*` are the inverse images of Stacks 06WE and
`f_*`, `f'_*` the direct images of sheaves of modules along the morphisms of ringed topoi of
Stacks 06TW. It is `Stacks.SheafOfModules.directImageBaseChange`, read through
`pushforwardModulesIsoPushforwardCocontinuous`. -/
def pushforwardModulesBaseChangeIso :
    Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        (B.baseTopology .etale) (B.baseTopology_le_topology .etale) ⋙
      RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
        (ringedToposMorphism B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
          (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq) .etale) ≅
    RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
        (ringedToposMorphism B S hS p𝒳 p𝒴 h𝒳 h𝒴 f (h𝒴.isFibredOneMorphism hfc) .etale) ⋙
      Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
        (B.baseTopology .etale) (B.baseTopology_le_topology .etale) := by
  have hA := TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have hfst := h𝒳.isFibredOneMorphism (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴')
    (p𝒮 := p𝒴) (F := f) (G := g))
  have hsnd := h𝒴'.isFibredOneMorphism (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴')
    (p𝒮 := p𝒴) (F := f) (G := g))
  have hf := h𝒴.isFibredOneMorphism hfc
  have hg := h𝒴.isFibredOneMorphism hgc
  letI := isContinuous_associatedTopology B S hS _ _ hA h𝒳 _ hfst .etale
  letI := isContinuous_associatedTopology B S hS _ _ h𝒴' h𝒴 _ hg .etale
  letI := isCocontinuous_associatedTopology B S hS _ _ hA h𝒴' _ hsnd .etale
  letI := isCocontinuous_associatedTopology B S hS _ _ h𝒳 h𝒴 _ hf .etale
  have : (Stack.baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have : (Stack.baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.GuitartExact := inferInstance
  have hI := Stacks.SheafOfModules.isIso_directImageBaseChange.{u}
    (Stack.baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g)
    (Stack.ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale))
    (Stack.ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale))
    (Stack.ringStructureSheafCore_obj_eq B S hS _ p𝒴' hA h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
      (B.baseTopology .etale) (B.baseTopology_le_topology .etale))
    (Stack.ringStructureSheafCore_obj_eq B S hS _ p𝒳 hA h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
      (B.baseTopology .etale) (B.baseTopology_le_topology .etale))
    (Stacks.SheafOfModules.pushforwardCocontinuous.{u} f
      (canonicalStructureMap B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hf .etale))
    (Stacks.SheafOfModules.pushforwardCocontinuous.{u} (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
      (canonicalStructureMap B S hS _ p𝒴' hA h𝒴' _ hsnd .etale))
    (Iso.refl _) (Iso.refl _)
    (fun M y j r s => pushforwardCocontinuous_leg_smul B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hf M y j r s)
    (fun M y j r s => pushforwardCocontinuous_leg_smul B S hS _ p𝒴' hA h𝒴' _ hsnd M y j r s)
    (Stack.structureSheaf_baseChange_scalar B S hS p𝒳 p𝒴' p𝒴 f g (B.baseTopology .etale)
      (B.baseTopology_le_topology .etale) h𝒳 h𝒴' h𝒴 hfc hgc)
  have e1 := pushforwardModulesIsoPushforwardCocontinuous B S hS _ _ hA h𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hsnd
  have e2 := pushforwardModulesIsoPushforwardCocontinuous B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hf
  refine ?_ ≪≫ (@asIso _ _ _ _ _ hI).symm ≪≫ ?_
  · refine Functor.isoWhiskerLeft _ ?_
    exact e1
  · refine Functor.isoWhiskerRight ?_ _
    exact e2.symm

end AlgebraicGeometry.FibredSite

end
