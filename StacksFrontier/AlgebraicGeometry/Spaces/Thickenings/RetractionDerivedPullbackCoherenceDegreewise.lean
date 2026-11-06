module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackCoherenceAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionModulePullbackRightAdjointCoherence

/-!
# Coherence (`**`) of the proof of `toLift_pullback` in Stacks 0DLL, with no degreewise hypothesis

`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_degreewise` proves the
coherence (`**`) of `c2` with base change along `H : X_W ⟶ X_V` given its degreewise form `hMC`.
This file proves `hMC` (`AlgebraicGeometry.Space.squareZeroComplexPullbackIso_comp_coherence`)
from the underived identity `MC`
(`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_squareZeroPullbackIso`): applied
degreewise and localized, `MC` is `hMC`. So (`**`) holds given only `hg` and `hgp`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence`).

The degreewise step is proved for arbitrary additive functors
(`AlgebraicGeometry.Space.mapHomologicalComplexCompIso_coherence_of_comp`). Its preadditive
structures and additivity proofs are implicit arguments, so they are read off the goal: the
concrete goal carries the preadditive structures found when its terms were elaborated, and
naming them again is expensive.

As in the module
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackCoherenceAssembly`, the
sheafification instances of the small étale site are put first locally, and the derived categories
of sheaves of modules on `X` that the restated statements use are the standard ones (a local
instance of default priority: without it these instances are not found).

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d d' u

namespace AlgebraicGeometry.Space

section Generic

variable {CV : Type*} [Category* CV] {_ : Preadditive CV} {CW : Type*} [Category* CW]
  {_ : Preadditive CW} {DV : Type*} [Category* DV] {_ : Preadditive DV} {DW : Type*} [Category* DW]
  {_ : Preadditive DW} {A : Type*} [Category* A] {_ : Preadditive A} {T : Type*} [Category* T]
  {Eg : CV ⥤ CW} {extW : CW ⥤ A} {extV : CV ⥤ A} {EV : CV ⥤ DV} {EW : CW ⥤ DW}
  {pullW : DW ⥤ A} {pullH : DV ⥤ DW} {pullV : DV ⥤ A}
  {hEg : Eg.Additive} {hextW : extW.Additive} {hextV : extV.Additive} {hEV : EV.Additive}
  {hEW : EW.Additive} {hpullW : pullW.Additive} {hpullH : pullH.Additive} {hpullV : pullV.Additive}

/-- **A degreewise coherence of comparisons of extensions of scalars, read in the derived
category**: if the identification `e` of a composite of two extensions of scalars with a third is
`s_W⁻¹`, `G2⁻¹`, `τ` and `s_V` composed, then so is its image on localized complexes, with
`s_W`, `s_V` applied degreewise and localized. -/
theorem mapHomologicalComplexCompIso_coherence_of_comp (sW : EW ⋙ pullW ≅ extW)
    (sV : EV ⋙ pullV ≅ extV) (G2 : EV ⋙ pullH ≅ Eg ⋙ EW)
    (τ : pullH ⋙ pullW ⟶ pullV) (Q : CochainComplex A ℤ ⥤ T)
    (e : Eg ⋙ extW ≅ extV)
    (hMC : e.hom = Functor.whiskerLeft Eg sW.inv ≫ Functor.whiskerRight G2.inv pullW ≫
      Functor.whiskerLeft EV τ ≫ sV.hom)
    (M : CochainComplex CV ℤ) :
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso sW (ComplexShape.up ℤ)).symm
        Q ≪≫ Functor.associator _ _ _).hom.app
        ((Eg.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      Q.map ((pullW.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso G2 (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (Eg ⋙ EW))
            (ComplexShape.up ℤ)).symm).inv.app M)) ≫
      Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso sV (ComplexShape.up ℤ)).symm
        Q ≪≫ Functor.associator _ _ _).inv.app M =
    Q.map ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app M) := by
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Iso.symm_inv, Category.id_comp, Category.comp_id,
    ← Functor.map_comp]
  congr 1
  ext n
  have h := NatTrans.congr_app hMC (M.X n)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp [h]

/-- `AlgebraicGeometry.Space.mapHomologicalComplexCompIso_coherence_of_comp` with the two localized
degreewise comparisons and the degreewise `G2` given as isomorphisms equal to their expressions. -/
theorem mapHomologicalComplexCompIso_coherence_of_comp_of_eq (sW : EW ⋙ pullW ≅ extW)
    (sV : EV ⋙ pullV ≅ extV) (G2 : EV ⋙ pullH ≅ Eg ⋙ EW)
    (τ : pullH ⋙ pullW ⟶ pullV) (Q : CochainComplex A ℤ ⥤ T)
    (e : Eg ⋙ extW ≅ extV)
    (hMC : e.hom = Functor.whiskerLeft Eg sW.inv ≫ Functor.whiskerRight G2.inv pullW ≫
      Functor.whiskerLeft EV τ ≫ sV.hom)
    (cW : extW.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q ≅
      EW.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        pullW.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q)
    (hcW : cW = Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso sW (ComplexShape.up ℤ)).symm Q ≪≫
      Functor.associator _ _ _)
    (cV : extV.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q ≅
      EV.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        pullV.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q)
    (hcV : cV = Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso sV (ComplexShape.up ℤ)).symm Q ≪≫
      Functor.associator _ _ _)
    (G2c : EV.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        pullH.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Eg.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ EW.mapHomologicalComplex (ComplexShape.up ℤ))
    (hG2c : G2c = Functor.mapHomologicalComplexCompIso G2 (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (Eg ⋙ EW)) (ComplexShape.up ℤ)).symm)
    (M : CochainComplex CV ℤ) :
    cW.hom.app ((Eg.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      Q.map ((pullW.mapHomologicalComplex (ComplexShape.up ℤ)).map (G2c.inv.app M)) ≫
      Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      cV.inv.app M =
    Q.map ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app M) := by
  subst hcW hcV hG2c
  exact mapHomologicalComplexCompIso_coherence_of_comp (hEg := hEg) (hextW := hextW)
    (hextV := hextV) (hEV := hEV) (hEW := hEW) (hpullW := hpullW) (hpullH := hpullH)
    (hpullV := hpullV) sW sV G2 τ Q e hMC M

end Generic

section Single

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V : SiteModule k B}
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) {hq : yoneda.relativelyRepresentable q.hom}
  {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {p' : X'.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpb : IsPullback q.hom p' p (yoneda.map τ))
  (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _)

/-- `AlgebraicGeometry.Space.squareZeroPullbackIso` with the pullback along `i` spelled as the
pullback of `AlgebraicGeometry.Space.modulePullbackDataTopos`. -/
def squareZeroPullbackIsoTopos :
    (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor ⋙
        (modulePullbackDataTopos B S hS).pull i ≅
      extensionOfScalars (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) :=
  squareZeroPullbackIso (hq := hq) hi h hip hpb hβτ

/-- `AlgebraicGeometry.Space.squareZeroComplexPullbackIso` read through
`AlgebraicGeometry.Space.squareZeroPullbackIsoTopos`. -/
theorem squareZeroComplexPullbackIso_eq_topos :
    squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ =
      Functor.isoWhiskerRight (@Functor.mapHomologicalComplexCompIso ℤ _ _ _ _ _ _ _ _ _ _ _ _
        (squareZeroPullbackIsoTopos (hq := hq) hi h hip hpb hβτ)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ))
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (modulePullbackDataTopos_additive B S hS i))
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (additive_extensionOfScalars _))
        (ComplexShape.up ℤ)).symm (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)) ≪≫
        Functor.associator _ _ _ :=
  rfl

end Single

section Coherence

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hiV : IsThickeningHom B S hS (iW ≫ H))
  {qV : X'V ⟶ X} (hV : (iW ≫ H) ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : (iW ≫ H).hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  [hDV : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]
  [hDW : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))]

variable (hH : yoneda.relativelyRepresentable H.hom)
  {g : (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) ⟶
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))}

attribute [local instance] isContinuous_smallBaseChange

omit hDV hDW in
/-- **The degreewise coherence `hMC` of `G2` with
`AlgebraicGeometry.Space.squareZeroComplexPullbackIso` and the composition comparison**: `MC`
(`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_squareZeroPullbackIso`) applied
degreewise and localized
(`AlgebraicGeometry.Space.mapHomologicalComplexCompIso_coherence_of_comp_of_eq`). -/
theorem squareZeroComplexPullbackIso_comp_coherence
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) =
      (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
      (squareZeroComplexPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW).hom.app
          ((extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g).obj M) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
          ((((modulePullbackDataTopos B S hS).pull iW).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
              hH rfl hg).inv.app M)) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
          ((NatTrans.mapHomologicalComplex
              ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS iW)
                  (smallEtaleRingedToposHom B S hS H)).symm ≪≫
                pullbackModulesCompTransport B S hS iW H).hom (ComplexShape.up ℤ)).app
            (((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV
              hβτV).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).inv.app M =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (extensionOfScalarsCompIso g hgp) (ComplexShape.up ℤ)).hom.app M) := by
  apply mapHomologicalComplexCompIso_coherence_of_comp_of_eq
  case hEg => first | exact additive_extensionOfScalars _ | infer_instance
  case hextW => first | exact additive_extensionOfScalars _ | infer_instance
  case hextV => first | exact additive_extensionOfScalars _ | infer_instance
  case hEV => exact squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV
  case hEW => exact squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW
  case hpullW => exact modulePullbackDataTopos_additive B S hS iW
  case hpullH => exact modulePullbackDataTopos_additive B S hS H
  case hpullV => exact modulePullbackDataTopos_additive B S hS (iW ≫ H)
  case hcW => exact squareZeroComplexPullbackIso_eq_topos (hq := hqW) hiW hW hipW hpbW hβτW
  case hcV => exact squareZeroComplexPullbackIso_eq_topos (hq := hqV) hiV hV hipV hpbV hβτV
  case hG2c => exact rfl
  case hMC =>
    exact extensionOfScalarsCompIso_hom_eq_squareZeroPullbackIso hiW hW hipW hpbW hβτW
      hiV hV hipV hpbV hβτV hH hg hgp

/-- **Stacks 0DLL, the coherence (`**`) of `c2` with base change along `H`**: the identification
`c2` for `W` at `g^* K`, followed by the derived pullback along `i_W` of `χ` and the composition
comparison of derived pullbacks along `X ⟶ X_W ⟶ X_V`, is the identification of derived base change
along `g` and then along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with derived base change along
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`, followed by `c2` for `V`:
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_degreewise` with `hMC`
discharged by `AlgebraicGeometry.Space.squareZeroComplexPullbackIso_comp_coherence`. -/
theorem squareZeroDerivedPullbackIso_comp_coherence
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) =
      (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))) :
    (squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
        (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).hom.app
        ((derivedExtensionOfScalars.{d, d'} g).obj K) ≫
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW).map
        ((squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
          hg).hom.app K) ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app
        ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.obj K) =
    (derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp).hom.app K ≫
      (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))).hom.app K :=
  squareZeroDerivedPullbackIso_comp_coherence_of_degreewise hiW hW hipW hpbW hβτW hiV hV hipV hpbV
    hβτV hH hg hgp
    (squareZeroComplexPullbackIso_comp_coherence hiW hW hipW hpbW hβτW hiV hV hipV hpbV hβτV hH hg
      hgp) K

end Coherence

end AlgebraicGeometry.Space
