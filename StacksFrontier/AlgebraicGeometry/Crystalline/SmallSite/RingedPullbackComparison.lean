module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedCrystallineTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The ringed-topos pullback along `f_cris` is the module-level `f_cris^{-1}` of the chapter

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes and `g : X ⟶ X'` a
morphism of schemes over their closed fibres, with no further hypothesis on `g`, as in
[Stacks, Tag 07MJ].  [Stacks, Tag 07IK] writes the morphism of small crystalline topoi as the
composite `f_cris = π_{X'} ∘ f_CRIS ∘ i_X`.  This file makes that composite a morphism of
**ringed** topoi in the sense of [Stacks, Tag 01D3] and identifies its pullback of sheaves of
modules (Stacks 03D6, `F' ↦ 𝒪_{X/S} ⊗_{f_cris^{-1}𝒪_{X'/S'}} f_cris^{-1}F'`) with the chapter's
`Crystalline.GlobalCrystallineSituation.SmallSite.crisModuleInverseImage`, the module-level
`i_{X', !}` of [Stacks, Tag 07IJ] followed by restriction along `Cris(X/S) ⥤ CRIS(X'/S')`.

## Main definitions

* `bigCrisRingedTopos` — the big crystalline topos `(X/S)_CRIS` as a ringed topos, its structure
  sheaf `𝒪_{X/S}` taken with sections raised to `CommRingCat.{u + 1}`.
* `bigCrisModuleEquivalence` — sheaves of modules on `bigCrisRingedTopos` are the chapter's
  sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)`.
* `smallChangeBaseRingedHom` — `f_CRIS ∘ i_X : (X/S)_cris ⟶ (X'/S')_CRIS` as a morphism of ringed
  topoi.
* `retractionRingedHom` — `π_{X'} : (X'/S')_CRIS ⟶ (X'/S')_cris` as a morphism of ringed topoi.
* `crisRingedHomComp` — their composite, `f_cris` as a morphism of ringed topoi.

## Main results

* `crisRingedHomComp_toToposHom` — the underlying morphism of topoi of `crisRingedHomComp` is
  `...SmallSite.crisMorphism`.
* `pullbackModulesSmallChangeBaseEquivIso` — the pullback of modules along `f_CRIS ∘ i_X` is the
  chapter's `...SmallSite.crisModulePullback`.
* `pullbackModulesRetractionEquivIso` — the pullback of modules along `π_{X'}` is the
  module-level `i_{X', !}`.
* `pullbackModulesCrisRingedHomCompIso` — `f_cris^* ≅ crisModuleInverseImage`, read through the
  two module equivalences.
* `crisModuleInverseImageIsoPullbackModules` — the same isomorphism at one module.
* `crisRingedHomComp_forgetFSharp_chain` — the structure map of `f_cris` restricts a section of
  `𝒪_{X'/S'}` along each domination `(ι ⋙ changeBase) A ⟶ ι A'`.

## References

* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The big crystalline topos as a ringed topos -/

/-- **`𝒪_{X/S}` on the big crystalline site with its sections raised to `CommRingCat.{u + 1}`**,
as a sheaf of commutative rings.  Its sections over `(U, T, δ)` are `ULift Γ(T, 𝒪_T)`. -/
def bigCommStructureSheafULift : Sheaf (topology S) CommRingCat.{u + 1} :=
  have : HasLimitsOfSize.{u, u + 1} CommRingCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  ⟨Stacks.Modules.ringULift.{u + 1, u, u, u} (GlobalCrystallineSituation.structureSheaf S),
    (Presheaf.isSheaf_iff_isSheaf_comp (topology S) _
      (CategoryTheory.forget CommRingCat.{u + 1})).mpr
      (Presheaf.isSheaf_comp_of_isSheaf (topology S) _
        CategoryTheory.uliftFunctor.{u + 1, u} (isSheafType_bigCrisRing S))⟩

/-- **The big crystalline topos `(X/S)_CRIS` as a ringed topos**: the big crystalline site with
the structure sheaf `𝒪_{X/S}`, its sections raised to the universe `u + 1` of the topos. -/
abbrev bigCrisRingedTopos : RingedTopos.{u, u + 1, u + 1} :=
  ⟨Thickening S, topology S, bigCommStructureSheafULift S⟩

/-- The sheaf condition for commutative rings on the big crystalline site is preserved by
forgetting commutativity. -/
instance : (bigCrisRingedTopos S).J.HasSheafCompose
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat.{u + 1} _

/-- The sheaf of rings underlying the structure sheaf of `bigCrisRingedTopos` is
`...SmallSite.bigStructureSheafULift`, on the nose. -/
theorem ringSheaf_bigCrisRingedTopos :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (bigCrisRingedTopos S).J))
        (bigCrisRingedTopos S).O =
      bigStructureSheafULift S :=
  rfl

/-- **Sheaves of modules on the big crystalline ringed topos are the chapter's sheaves of
`𝒪_{X/S}`-modules on `CRIS(X/S)`**: `Stacks.Modules.sheafRingULiftEquiv` at the big site, an
isomorphism of categories changing neither the sections nor the morphisms. -/
def bigCrisModuleEquivalence :
    BigModuleSheaf S ≌ SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (bigCrisRingedTopos S).J))
          (bigCrisRingedTopos S).O) :=
  (Stacks.Modules.sheafRingULiftEquiv.{u + 1, u, u, u, u + 1}
    (𝒪 := GlobalCrystallineSituation.structureSheaf S) (crisRing_isSheaf S)
    (isSheafType_bigCrisRing S)).symm

/-! ### `f_CRIS ∘ i_X` as a morphism of ringed topoi -/

variable {S} {S' : GlobalCrystallineSituation.{u}}

/-- **The morphism of topoi `f_CRIS ∘ i_X : (X/S)_cris ⟶ (X'/S')_CRIS`**, the inclusion morphism
of [Stacks, Tag 07IJ] followed by change of divided power base on the big crystalline topoi,
[Stacks, Tag 07IC]; it is defined for every `g`. -/
def crisToBigMorphism (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    MorphismOfTopoi (smallTopos S) (topos S') :=
  (changeBaseMorphism S S' f g h).comp (CrystallineThickening.smallToBigMorphism S)

/-- **The inverse image of `f_CRIS ∘ i_X` is restriction** along the continuous functor
`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`. -/
def crisToBigMorphismInverseImageIso (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisToBigMorphism f g h).inverseImage ≅
      (CrystallineThickening.ι S ⋙ changeBase S S' f g h).sheafPushforwardContinuous
        (Type (u + 1)) (smallTopology S) (topology S') :=
  (crisToBigMorphism f g h).adj.leftAdjointUniq
    (((changeBase S S' f g h).sheafAdjunctionCocontinuous (Type (u + 1)) (topology S)
        (topology S')).comp
      ((CrystallineThickening.ι S).sheafAdjunctionCocontinuous (Type (u + 1)) (smallTopology S)
        (topology S)))

/-- **Restricting the lifted structure sheaf of `CRIS(X'/S')` to `Cris(X/S)` gives the lifted
structure sheaf of `Cris(X/S)`**, on the nose. -/
def crisToBigStructureSheafIso (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((CrystallineThickening.ι S ⋙ changeBase S S' f g h).sheafPushforwardContinuous
        CommRingCat.{u + 1} (smallTopology S) (topology S')).obj (bigCommStructureSheafULift S') ≅
      commStructureSheafULift S :=
  Iso.refl _

/-- **`f_CRIS ∘ i_X` as a morphism of ringed topoi**
`((X/S)_cris, 𝒪_{X/S}) ⟶ ((X'/S')_CRIS, 𝒪_{X'/S'})`: its structure map in inverse-image form is
the identification of `(f_CRIS ∘ i_X)^{-1}𝒪_{X'/S'}`, a restriction, with `𝒪_{X/S}`. -/
def smallChangeBaseRingedHom (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    RingedToposHom (crisRingedTopos S) (bigCrisRingedTopos S') :=
  RingedToposHom.ofInverseImageIso (X := crisRingedTopos S) (Y := bigCrisRingedTopos S')
    (crisToBigMorphism f g h)
    (Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso
      (smallTopology S) (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
      (crisToBigMorphism f g h) (crisToBigMorphismInverseImageIso f g h)
      (bigCommStructureSheafULift S') ≪≫ crisToBigStructureSheafIso f g h)

variable (S') in
/-- **The retraction `π_{X'} : (X'/S')_CRIS ⟶ (X'/S')_cris` of [Stacks, Tag 07IJ] as a morphism
of ringed topoi**: its direct image is restriction `i^{-1}`, and its structure map
`𝒪_{X'/S'} ⟶ π_*𝒪_{X'/S'} = i^{-1}𝒪_{X'/S'}` is the identity on sections. -/
def retractionRingedHom : RingedToposHom (bigCrisRingedTopos S') (crisRingedTopos S') where
  toToposHom := CrystallineThickening.retractionMorphism S'
  fSharp := (Iso.refl _ : commStructureSheafULift S' ≅
      ((CrystallineThickening.ι S').sheafPushforwardContinuous CommRingCat.{u + 1}
        (smallTopology S') (topology S')).obj (bigCommStructureSheafULift S')).hom ≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (smallTopology S') (topology S')
      (CrystallineThickening.ι S') (bigCommStructureSheafULift S')).inv

/-- **Stacks Project, Tag 07IK, as a morphism of ringed topoi: `f_cris = π_{X'} ∘ f_CRIS ∘ i_X`**,
`((X/S)_cris, 𝒪_{X/S}) ⟶ ((X'/S')_cris, 𝒪_{X'/S'})`, for an arbitrary `g : X ⟶ X'`. -/
def crisRingedHomComp (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    RingedToposHom (crisRingedTopos S) (crisRingedTopos S') :=
  RingedToposHom.comp (X := crisRingedTopos S) (Y := bigCrisRingedTopos S')
    (Z := crisRingedTopos S') (retractionRingedHom S') (smallChangeBaseRingedHom f g h)

/-- The underlying morphism of topoi of `crisRingedHomComp` is `...crisMorphism`, the morphism of
small crystalline topoi of [Stacks, Tag 07IK], on the nose. -/
theorem crisRingedHomComp_toToposHom (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisRingedHomComp f g h).toToposHom = crisMorphism S S' f g h := rfl

/-- The identity of the lifted structure sheaf of `Cris(X/S)`, read as the comparison
`𝒪_{X/S} ⟶ (restriction of 𝒪_{X'/S'})` of sheaves of rings. -/
def crisToBigStructureRingMap (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
        (crisRingedTopos S).O ⟶
      ((CrystallineThickening.ι S ⋙ changeBase S S' f g h).sheafPushforwardContinuous
        RingCat.{u + 1} (smallTopology S) (topology S')).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (bigCrisRingedTopos S').J))
            (bigCrisRingedTopos S').O) :=
  𝟙 (structureSheafULift S)

/-- Restriction of modules along `Cris(X/S) ⥤ CRIS(X'/S')` at the lifted rings is the chapter's
`...SmallSite.crisModulePullback` read through the two module equivalences, on the nose. -/
theorem bigCrisModuleEquivalence_functor_comp_restriction (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (bigCrisModuleEquivalence S').functor ⋙
      Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S) (topology S')
        (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (bigCrisRingedTopos S').J))
            (bigCrisRingedTopos S').O) ⋙
      (SheafOfModules.restrictScalars (crisToBigStructureRingMap f g h) :
        SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _) =
    crisModulePullback.{u + 1} f g h ⋙ (crisModuleEquivalence S).functor := rfl

section UPiece

variable (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- The inverse image of `f_CRIS ∘ i_X` preserves finite products, being left exact. -/
instance : PreservesFiniteProducts (crisToBigMorphism f g h).inverseImage := by
  have := (crisToBigMorphism f g h).preservesFiniteLimits
  infer_instance

/-- The comparison of the inverse image of the lifted structure sheaf of `CRIS(X'/S')` along
`f_CRIS ∘ i_X` with its restriction, induced by `crisToBigMorphismInverseImageIso`. -/
abbrev crisToBigInverseImageRingMap :=
  Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans.{u + 1, u + 1, u, u + 1, u, u + 1}
    (smallTopology S)
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
        (bigCommStructureSheafULift S'))
    (crisToBigMorphismInverseImageIso f g h).hom

/-- The structure map of `smallChangeBaseRingedHom` in inverse-image form, followed by the identity
comparison, is the comparison of the inverse image with the restriction. -/
theorem smallChangeBaseRingedHom_fSharpInverseImageRing_comp :
    (smallChangeBaseRingedHom f g h).fSharpInverseImageRing ≫ crisToBigStructureRingMap f g h =
      crisToBigInverseImageRingMap f g h ≫
        (Stacks.Sheaves.ToposPullback.restrictionRingIso (smallTopology S) (topology S')
          (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
            (bigCommStructureSheafULift S'))).hom := by
  have h1 := RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
    (smallChangeBaseRingedHom f g h)
  have h2 := RingedToposHom.ofInverseImageIso_fSharpInverseImage (X := crisRingedTopos S)
    (Y := bigCrisRingedTopos S') (crisToBigMorphism f g h)
    (Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso
      (smallTopology S) (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
      (crisToBigMorphism f g h) (crisToBigMorphismInverseImageIso f g h)
      (bigCommStructureSheafULift S') ≪≫ crisToBigStructureSheafIso f g h)
  refine (congrArg (· ≫ crisToBigStructureRingMap f g h) h1.symm).trans ?_
  refine (congrArg (fun m =>
    (Stacks.forgetCommRingSheaf.{u, u + 1, u + 1} (smallTopology S)).map m ≫
      crisToBigStructureRingMap f g h) h2).trans ?_
  apply Sheaf.hom_ext
  ext X x
  rfl

/-- The structure map of `smallChangeBaseRingedHom` is invertible in inverse-image form. -/
instance : IsIso (smallChangeBaseRingedHom f g h).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso (X := crisRingedTopos S)
    (Y := bigCrisRingedTopos S') _ _

/-- The structure map of `smallChangeBaseRingedHom` is invertible in inverse-image form, at the
level of sheaves of rings. -/
instance : IsIso (smallChangeBaseRingedHom f g h).fSharpInverseImageRing :=
  RingedToposHom.isIso_fSharpInverseImageRing_of_hasSheafCompose_forgetCommRingCat
    (X := crisRingedTopos S) (Y := bigCrisRingedTopos S') _

/-- The same, at the spelling of the four-field morphism of ringed topoi. -/
instance : IsIso (smallChangeBaseRingedHom f g h).toModulesHom.fSharpInverseImage :=
  inferInstanceAs (IsIso (smallChangeBaseRingedHom f g h).fSharpInverseImageRing)

/-- The ring maps along which the pullback of `smallChangeBaseRingedHom` restricts scalars compose
to the identity comparison `crisToBigStructureRingMap`. -/
theorem smallChangeBaseRingedHom_inv_comp :
    (asIso (smallChangeBaseRingedHom f g h).toModulesHom.fSharpInverseImage).inv ≫
        crisToBigInverseImageRingMap f g h ≫
        (Stacks.Sheaves.ToposPullback.restrictionRingIso (smallTopology S) (topology S')
          (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
            (bigCommStructureSheafULift S'))).hom =
      crisToBigStructureRingMap f g h :=
  (Iso.inv_comp_eq _).2 (smallChangeBaseRingedHom_fSharpInverseImageRing_comp f g h).symm

/-- **The pullback of modules along `f_CRIS ∘ i_X` is restriction** of modules along
`Cris(X/S) ⥤ CRIS(X'/S')` followed by restriction of scalars along the identity comparison
`crisToBigStructureRingMap`. -/
def pullbackModulesSmallChangeBaseIso :
    (smallChangeBaseRingedHom f g h).toModulesHom.pullbackModules ≅
      Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S) (topology S')
        (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
            (bigCommStructureSheafULift S')) ⋙
      (SheafOfModules.restrictScalars (crisToBigStructureRingMap f g h) :
        SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _) :=
  Functor.isoWhiskerRight
      (Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso (smallTopology S)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
            (bigCommStructureSheafULift S'))
        (crisToBigMorphismInverseImageIso f g h) (crisToBigInverseImageRingMap f g h)
        (Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _) ≪≫
      Functor.isoWhiskerRight
        (Stacks.Sheaves.ToposPullback.restrictionModuleIso (smallTopology S) (topology S')
          (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
              (bigCommStructureSheafULift S')))
        _) _ ≪≫
    Functor.isoWhiskerLeft _
      (smallChangeBaseRingedHom f g h).toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫
    eqToIso ((Functor.assoc _ _ _).trans
      ((congrArg (fun F => (Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S)
          (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
              (bigCommStructureSheafULift S')) ⋙
          SheafOfModules.restrictScalars _) ⋙ F)
        (Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _)).trans
      ((Functor.assoc _ _ _).trans
      ((congrArg (fun F => Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S)
          (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
              (bigCommStructureSheafULift S')) ⋙ F)
        (Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _)).trans
      (congrArg (fun m => Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S)
          (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S')))
              (bigCommStructureSheafULift S')) ⋙
          (SheafOfModules.restrictScalars m : SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _))
        ((Category.assoc _ _ _).trans (smallChangeBaseRingedHom_inv_comp f g h)))))))

end UPiece

/-- **The pullback of modules along `f_CRIS ∘ i_X` is `...SmallSite.crisModulePullback`**, read
through the module equivalences of `CRIS(X'/S')` and `Cris(X/S)`. -/
def pullbackModulesSmallChangeBaseEquivIso (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (bigCrisModuleEquivalence S').functor ⋙
        (smallChangeBaseRingedHom f g h).toModulesHom.pullbackModules ≅
      crisModulePullback.{u + 1} f g h ⋙ (crisModuleEquivalence S).functor :=
  Functor.isoWhiskerLeft _ (pullbackModulesSmallChangeBaseIso f g h) ≪≫
    eqToIso (bigCrisModuleEquivalence_functor_comp_restriction f g h)

/-! ### The retraction `π` -/

section PiPiece

variable (S)

/-- The identity of the lifted structure sheaf of `Cris(X/S)`, read as the comparison with the
restriction of the lifted structure sheaf of `CRIS(X/S)`. -/
def retractionStructureRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (smallTopology S)))
        (commStructureSheafULift S) ⟶
      ((CrystallineThickening.ι S).sheafPushforwardContinuous
        RingCat.{u + 1} (smallTopology S) (topology S)).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
            (bigCommStructureSheafULift S)) :=
  𝟙 (structureSheafULift S)

/-- The structure map of `retractionRingedHom`, followed by the comparison of the transported ring
structure with the restricted one, is the identity comparison `retractionStructureRingMap`. -/
theorem retractionRingedHom_structureRingMap_comp :
    (retractionRingedHom S).structureRingMap ≫
        (Stacks.Sheaves.ToposPullback.restrictionRingIso (smallTopology S) (topology S)
          (CrystallineThickening.ι S)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
              (bigCommStructureSheafULift S))).hom =
      retractionStructureRingMap S := by
  apply Sheaf.hom_ext
  ext X x
  rfl

/-- **The direct image of modules along `π` is restriction** from `CRIS(X/S)` to `Cris(X/S)`. -/
def pushforwardModulesRetractionIso :
    RingedToposHom.pushforwardModules (X := bigCrisRingedTopos S) (Y := crisRingedTopos S)
        (retractionRingedHom S) ≅
      Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S) (topology S)
        (CrystallineThickening.ι S)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
            (bigCommStructureSheafULift S)) ⋙
      (SheafOfModules.restrictScalars (retractionStructureRingMap S) :
        SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _) :=
  Functor.isoWhiskerRight
      (Stacks.Sheaves.ToposPullback.restrictionModuleIso (smallTopology S) (topology S)
        (CrystallineThickening.ι S)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
            (bigCommStructureSheafULift S))) _ ≪≫
    eqToIso ((Functor.assoc _ _ _).trans
      ((congrArg (fun F => Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S)
          (topology S) (CrystallineThickening.ι S)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
              (bigCommStructureSheafULift S)) ⋙ F)
        (Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _)).trans
      (congrArg (fun m => Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S)
          (topology S) (CrystallineThickening.ι S)
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
              (bigCommStructureSheafULift S)) ⋙
          (SheafOfModules.restrictScalars m : SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _))
        (retractionRingedHom_structureRingMap_comp S))))

/-- Restriction of modules from `CRIS(X/S)` to `Cris(X/S)` at the lifted rings is the chapter's
`...SmallSite.crisRestrictModules` read through the two module equivalences, on the nose. -/
theorem restrictScalarsRetraction_comp_inverse :
    (Stacks.Sheaves.ToposPullback.restrictionModules (smallTopology S) (topology S)
        (CrystallineThickening.ι S)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (topology S)))
            (bigCommStructureSheafULift S)) ⋙
      (SheafOfModules.restrictScalars (retractionStructureRingMap S) :
        SheafOfModules.{u + 1} _ ⥤ SheafOfModules.{u + 1} _)) ⋙ (crisModuleEquivalence S).inverse =
    (bigCrisModuleEquivalence S).inverse ⋙ crisRestrictModules.{u + 1} S := rfl

/-- **The pullback of modules along `π` is the module-level `i_!` of [Stacks, Tag 07IJ]**, read
through the module equivalences. -/
def pullbackModulesRetractionEquivIso :
    (crisModuleEquivalence S).functor ⋙
        (retractionRingedHom S).toModulesHom.pullbackModules ≅
      moduleLowerShriek S ⋙ (bigCrisModuleEquivalence S).functor :=
  (((crisModuleEquivalence S).toAdjunction.comp
      (RingedToposHom.pullbackAdjPushforwardModules (retractionRingedHom S))).ofNatIsoRight
    (Functor.isoWhiskerRight (pushforwardModulesRetractionIso S) _ ≪≫
      eqToIso (restrictScalarsRetraction_comp_inverse S))).leftAdjointUniq
    ((moduleLowerShriekAdjunction S).comp (bigCrisModuleEquivalence S).toAdjunction)

end PiPiece

/-! ### The comparison for `f_cris` -/

/-- **The pullback of modules along the ringed-topos morphism `f_cris` of [Stacks, Tag 07IK] is
the chapter's `f_cris^{-1}`**: for an arbitrary `g : X ⟶ X'`,

`f_cris^* ≅ crisModuleInverseImage f g h`

as functors `Mod(𝒪_{X'/S'}) ⥤ Mod(𝒪_{X/S})`, read through the module equivalences
`...SmallSite.crisModuleEquivalence`. -/
def pullbackModulesCrisRingedHomCompIso (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisModuleEquivalence S').functor ⋙
        (crisRingedHomComp f g h).toModulesHom.pullbackModules ≅
      crisModuleInverseImage f g h ⋙ (crisModuleEquivalence S).functor :=
  Functor.isoWhiskerLeft _
      (RingedToposHom.pullbackModulesCompIso (X := crisRingedTopos S)
        (Y := bigCrisRingedTopos S') (Z := crisRingedTopos S')
        (smallChangeBaseRingedHom f g h) (retractionRingedHom S')) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackModulesRetractionEquivIso S') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleLowerShriek S') (pullbackModulesSmallChangeBaseEquivIso f g h) ≪≫
    (Functor.associator _ _ _).symm

/-- **The comparison at one module**: for a sheaf of `𝒪_{X'/S'}`-modules `F'` on `Cris(X'/S')`, the
module `crisModuleInverseImage f g h F'` of the chapter is the pullback of `F'` along the
ringed-topos morphism `f_cris`, read through the module equivalences. -/
def crisModuleInverseImageIsoPullbackModules (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (F' : ModuleSheaf S') :
    (crisModuleEquivalence S).functor.obj ((crisModuleInverseImage f g h).obj F') ≅
      ((crisRingedHomComp f g h).toModulesHom.pullbackModules).obj
        ((crisModuleEquivalence S').functor.obj F') :=
  ((pullbackModulesCrisRingedHomCompIso f g h).app F').symm


/-! ### A triangle identity for two right Kan extensions -/

section RanChain

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {H : Type*} [Category C₁] [Category C₂]
  [Category C₃] [Category H] (L₂ : C₂ ⥤ C₃) (L₁ : C₁ ⥤ C₂) (P : C₃ ⥤ H)
  [∀ F : C₂ ⥤ H, L₂.HasRightKanExtension F] [∀ F : C₁ ⥤ H, L₁.HasRightKanExtension F]

/-- The unit `P ⟶ L₂.ran (L₂ ⋙ P) ⟶ L₂.ran (L₁.ran (L₁ ⋙ L₂ ⋙ P))` of the composite of two
right Kan extension adjunctions, read at `Y`, restricted along `k : Y ⟶ L₂ (L₁ X)` and then
evaluated by the two counits, is the restriction `P.map k`. -/
theorem ranAdjunction_unit_comp_ranCounit_comp {X : C₁} {Y : C₃} (k : Y ⟶ L₂.obj (L₁.obj X)) :
    (((L₂.ranAdjunction H).unit.app P).app Y ≫
        (L₂.ran.map ((L₁.ranAdjunction H).unit.app (L₂ ⋙ P))).app Y) ≫
      (L₂.ran.obj (L₁.ran.obj (L₁ ⋙ L₂ ⋙ P))).map k ≫
      (L₂.ranCounit.app (L₁.ran.obj (L₁ ⋙ L₂ ⋙ P))).app (L₁.obj X) ≫
      (L₁.ranCounit.app (L₁ ⋙ L₂ ⋙ P)).app X = P.map k := by
  have nat := ((L₂.ranAdjunction H).unit.app P ≫
    L₂.ran.map ((L₁.ranAdjunction H).unit.app (L₂ ⋙ P))).naturality k
  have cn := congr_app (L₂.ranCounit.naturality ((L₁.ranAdjunction H).unit.app (L₂ ⋙ P)))
    (L₁.obj X)
  have t1 := L₂.ranCounit_app_app_ranAdjunction_unit_app_app P (L₁.obj X)
  have t2 := L₁.ranCounit_app_app_ranAdjunction_unit_app_app (L₂ ⋙ P) X
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
    Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
    NatTrans.comp_app] at nat cn t1 t2
  simp only [Category.assoc] at nat ⊢
  rw [← reassoc_of% nat, reassoc_of% cn, reassoc_of% t1, t2]
  exact Category.comp_id _

end RanChain

/-! ### The structure map of `f_cris` on sections -/

section ForgetFSharp

variable (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The structure map of `f_CRIS ∘ i_X` on underlying sheaves of sets is the unit** of the
composite adjunction `(ι ⋙ changeBase)^{-1} ⊣ changeBase_* ∘ ι_*` of restriction and right Kan
extension, at the underlying sheaf of `𝒪_{X'/S'}`. -/
theorem forgetFSharp_smallChangeBaseRingedHom :
    RingedToposHom.forgetFSharp (smallChangeBaseRingedHom f g h) =
      (((changeBase S S' f g h).sheafAdjunctionCocontinuous (Type (u + 1)) (topology S)
          (topology S')).comp
        ((CrystallineThickening.ι S).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallTopology S) (topology S))).unit.app
        ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O) := by
  set e₀ := Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso
    (smallTopology S) (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
    (crisToBigMorphism f g h) (crisToBigMorphismInverseImageIso f g h)
    (bigCommStructureSheafULift S') with he₀
  have e1 := Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv
    (crisToBigMorphism f g h) (bigCommStructureSheafULift S') (commStructureSheafULift S)
    (e₀ ≪≫ crisToBigStructureSheafIso f g h).hom
  have e2 := Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_hom_forget
      (smallTopology S) (topology S') (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
      (crisToBigMorphism f g h) (crisToBigMorphismInverseImageIso f g h)
      (bigCommStructureSheafULift S')
  have e3 : (sheafCompose (smallTopology S) (CategoryTheory.forget CommRingCat.{u + 1})).map
      (e₀ ≪≫ crisToBigStructureSheafIso f g h).hom =
      (crisToBigMorphismInverseImageIso f g h).hom.app
        ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O) :=
    (Functor.map_comp _ _ _).trans ((congrArg (· ≫ _) e2).trans (Category.comp_id _))
  exact e1.trans ((congrArg ((crisToBigMorphism f g h).adj.homEquiv _ _) e3).trans
    (((crisToBigMorphism f g h).adj.homEquiv_unit _ _ _).trans
      (Adjunction.unit_leftAdjointUniq_hom_app _ _ _)))

/-- The structure map of the retraction `π` is the identity on sections. -/
theorem forgetFSharp_retractionRingedHom_app (U : (CrystallineThickening S')ᵒᵖ) :
    (RingedToposHom.forgetFSharp (retractionRingedHom S')).hom.app U = 𝟙 _ :=
  rfl

/-- **The structure map of `f_cris` on sections over an object `A'` of `Cris(X'/S')`**: the unit of
the right Kan extension along change of base, followed by the right Kan extension of the unit of
the right Kan extension along the inclusion `Cris(X/S) ⥤ CRIS(X/S)`. -/
theorem crisRingedHomComp_forgetFSharp_app (A' : CrystallineThickening S') :
    (RingedToposHom.forgetFSharp (crisRingedHomComp f g h)).hom.app (op A') =
      (((changeBase S S' f g h).op.ranAdjunction (Type (u + 1))).unit.app
          ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj).app
          (op ((CrystallineThickening.ι S').obj A')) ≫
        ((changeBase S S' f g h).op.ran.map
          (((CrystallineThickening.ι S).op.ranAdjunction (Type (u + 1))).unit.app
            ((changeBase S S' f g h).op ⋙
              ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj))).app
          (op ((CrystallineThickening.ι S').obj A')) := by
  have h1 := RingedToposHom.forgetFSharp_comp (A := crisRingedTopos S)
    (B := bigCrisRingedTopos S') (C := crisRingedTopos S') (retractionRingedHom S')
    (smallChangeBaseRingedHom f g h)
  have h2 := congrArg (fun m => m.hom.app (op ((CrystallineThickening.ι S').obj A')))
    (forgetFSharp_smallChangeBaseRingedHom f g h)
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at h2
  refine (congrArg (fun m => m.hom.app (op A')) h1).trans ?_
  refine (Category.id_comp _).trans (h2.trans ?_)
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  congr 1
  exact congrArg (fun m => ((changeBase S S' f g h).op.ran.map m).app
      (op ((CrystallineThickening.ι S').obj A')))
    (Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _)

/-- **The structure map of `f_cris` restricts along dominations.**  For an object `A'` of
`Cris(X'/S')`, an object `A` of `Cris(X/S)` and a morphism `k : (ι ⋙ changeBase) A ⟶ ι A'` of
`CRIS(X'/S')`, the section of `f_{cris, *}𝒪_{X/S}` over `A'` that the structure map assigns to a
section of `𝒪_{X'/S'}` over `A'`, evaluated at the leg `(A, k)` of the iterated right Kan
extension, is the restriction of that section along `k`. -/
theorem crisRingedHomComp_forgetFSharp_chain (A' : CrystallineThickening S')
    (A : CrystallineThickening S)
    (k : (CrystallineThickening.ι S ⋙ changeBase S S' f g h).obj A ⟶
      (CrystallineThickening.ι S').obj A') :
    (RingedToposHom.forgetFSharp (crisRingedHomComp f g h)).hom.app (op A') ≫
        ((changeBase S S' f g h).op.ran.obj ((CrystallineThickening.ι S).op.ran.obj
          ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj)).map k.op ≫
        ((changeBase S S' f g h).op.ranCounit.app ((CrystallineThickening.ι S).op.ran.obj
          ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj)).app
          ((CrystallineThickening.ι S).op.obj (op A)) ≫
        ((CrystallineThickening.ι S).op.ranCounit.app
          ((crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O).obj).app (op A) =
      ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj.map k.op :=
  (congrArg (· ≫ _) (crisRingedHomComp_forgetFSharp_app f g h A')).trans
    (ranAdjunction_unit_comp_ranCounit_comp (changeBase S S' f g h).op
      (CrystallineThickening.ι S).op
      ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj k.op)

end ForgetFSharp

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
