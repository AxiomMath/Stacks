module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionModulePullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.MateTransportedAdjunctions
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer

/-!
# The module-level coherence `MC` of the proof of `toLift_pullback` in Stacks 0DLL

Let `X ⟶ X_W ⟶ X_V` be the sections of two square-zero thickenings with retractions,
`H : X_W ⟶ X_V`, and `g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` a ring map over `𝒪_X` compatible with
`H`. The identification `AlgebraicGeometry.Space.squareZeroPullbackIso` for `W`, the identification
`G2` (`AlgebraicGeometry.Space.squareZeroPullbackNaturalityIso`) pushed along `X ⟶ X_W`, the
composition comparison of pullbacks of modules along `X ⟶ X_W ⟶ X_V`, and
`AlgebraicGeometry.Space.squareZeroPullbackIso` for `V` compose to the identification
`Deformation.ComplexLift.extensionOfScalarsCompIso` of extension of scalars along `g` and then
along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with extension of scalars along `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`, as soon as the
corresponding comparisons of right adjoints compose to the identification of the restrictions of
scalars (`AlgebraicGeometry.Space.extensionOfScalarsCompIso_hom_eq_of_rightAdjoint`). All five are
comparisons of left adjoints, so this is
`AlgebraicGeometry.Space.squareZeroLeftAdjoint_coherence_of_conjugateEquiv`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

/-- Solving `e⁻¹⁻¹ ≫ f = 𝟙` for `f`, with the objects abstract. -/
theorem eq_inv_of_symm_inv_comp_eq_id {E : Type*} [Category E] {A B : E} (e : A ≅ B) {f : B ⟶ A}
    (h : e.symm.inv ≫ f = 𝟙 A) : f = e.inv := by
  rw [← Iso.hom_comp_eq_id]
  exact h

section Retraction

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

/-- The comparison of right adjoints behind `AlgebraicGeometry.Space.squareZeroPullbackIso`: the
direct image along `i` followed by the inverse of the equivalence is restriction of scalars along
the projection. -/
def squareZeroPullbackRightAdjointIso :
    (smallEtaleRingedToposHom B S hS i).pushforwardModules ⋙
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).inverse ≅
      SheafOfModules.restrictScalars
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
              (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
              (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))) :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS i ≪≫
      modulePushforwardChartIso B S hS i hi.isClosedImmersion.rep ≪≫
      squareZeroPushforwardIso hi h hip hpb hβτ) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
        (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).unitIso.symm ≪≫
      Functor.rightUnitor _

/-- The conjugate of the inverse of `AlgebraicGeometry.Space.squareZeroPullbackIso` is
`AlgebraicGeometry.Space.squareZeroPullbackRightAdjointIso`. -/
theorem conjugateEquiv_squareZeroPullbackIso_inv :
    conjugateEquiv
        ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).toAdjunction.comp
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS i)))
        (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
        (squareZeroPullbackIso (hq := hq) hi h hip hpb hβτ).inv =
      (squareZeroPullbackRightAdjointIso (hq := hq) hi h hip hpb hβτ).hom :=
  CategoryTheory.Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv
    ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).toAdjunction.comp
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS i)))
    (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (squareZeroPullbackRightAdjointIso (hq := hq) hi h hip hpb hβτ)

/-- The conjugate of `AlgebraicGeometry.Space.squareZeroPullbackIso` is the inverse of
`AlgebraicGeometry.Space.squareZeroPullbackRightAdjointIso`. -/
theorem conjugateEquiv_squareZeroPullbackIso_hom :
    conjugateEquiv
        (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
        ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).toAdjunction.comp
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS i)))
        (squareZeroPullbackIso (hq := hq) hi h hip hpb hβτ).hom =
      (squareZeroPullbackRightAdjointIso (hq := hq) hi h hip hpb hβτ).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    ((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).toAdjunction.comp
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS i)))
    (squareZeroPullbackRightAdjointIso (hq := hq) hi h hip hpb hβτ)
    (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))

end Retraction

section Coherence

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
  (hH : yoneda.relativelyRepresentable H.hom)
  {g : (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)) ⟶
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))}

/-- The conjugate of the composition comparison of pullbacks of modules along `X ⟶ X_W ⟶ X_V`,
the inverse of the compositor of Stacks 03D6 followed by the transport: the inverse of the
transport of direct images followed by the compositor of direct images. -/
theorem conjugateEquiv_pullbackModulesCompIso_symm_trans_transport_hom :
    conjugateEquiv
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (iW ≫ H)))
        ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS H)).comp
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS iW)))
        ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS iW)
            (smallEtaleRingedToposHom B S hS H)).symm ≪≫
          pullbackModulesCompTransport B S hS iW H).hom =
      (pushforwardModulesCompTransport B S hS iW H).inv ≫
        (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
          (smallEtaleRingedToposHom B S hS H)).hom := by
  have h1 := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS iW H))
    ((RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS (iW ≫ H))).ofNatIsoRight
      (pushforwardModulesCompTransport B S hS iW H).symm)
  have h3 := eq_inv_of_symm_inv_comp_eq_id (pushforwardModulesCompTransport B S hS iW H)
    ((Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (iW ≫ H)))
      (pushforwardModulesCompTransport B S hS iW H).symm
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS iW H))
      (pullbackModulesCompTransport B S hS iW H).hom).symm.trans h1)
  have h2 := CategoryTheory.Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS iW H))
    ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS H)).comp
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS iW)))
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
      (smallEtaleRingedToposHom B S hS H))
  exact (conjugateEquiv_comp _
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS iW H))
      _ _ _).symm.trans
    (congrArg₂ (· ≫ ·) h3 h2)

/-- **`MC` from its version on right adjoints**: the identification of extension of scalars along
`g` and then along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with extension of scalars along `𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`
is `AlgebraicGeometry.Space.squareZeroPullbackIso` for `W` inverted, `G2` inverted and pushed along
`X ⟶ X_W`, the composition comparison of pullbacks along `X ⟶ X_W ⟶ X_V`, and
`AlgebraicGeometry.Space.squareZeroPullbackIso` for `V`, as soon as the comparisons of right
adjoints compose to the identification of the restrictions of scalars (`hR`). -/
theorem extensionOfScalarsCompIso_hom_eq_of_rightAdjoint
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
    (hR : (squareZeroPullbackRightAdjointIso (hq := hqV) hiV hV hipV hpbV hβτV).inv ≫
        Functor.whiskerRight ((pushforwardModulesCompTransport B S hS iW H).inv ≫
          (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS iW)
            (smallEtaleRingedToposHom B S hS H)).hom)
          (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).inverse ≫
        Functor.whiskerLeft (smallEtaleRingedToposHom B S hS iW).pushforwardModules
          (squareZeroPushforwardNaturalityRightAdjointIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW
            hβτW hH rfl hg).hom ≫
        Functor.whiskerRight
          (squareZeroPullbackRightAdjointIso (hq := hqW) hiW hW hipW hpbW hβτW).hom
          (SheafOfModules.restrictScalars
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (forget₂ CommRingCat.{u} RingCat.{u})).map g)) =
      (restrictScalarsCompIsoOf g hgp).inv) :
    (extensionOfScalarsCompIso g hgp).hom =
      Functor.whiskerLeft (extensionOfScalars g)
          (squareZeroPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW).inv ≫
        Functor.whiskerRight
          (squareZeroPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
            hH rfl hg).inv (smallEtaleRingedToposHom B S hS iW).toModulesHom.pullbackModules ≫
        Functor.whiskerLeft (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
          ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS iW)
              (smallEtaleRingedToposHom B S hS H)).symm ≪≫
            pullbackModulesCompTransport B S hS iW H).hom ≫
        (squareZeroPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).hom :=
  squareZeroLeftAdjoint_coherence_of_conjugateEquiv (extendRestrictAdjunction g)
    (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))
    (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).toAdjunction
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).toAdjunction
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS H))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS iW))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (iW ≫ H)))
    _ _ _ _ _
    (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      ((extendRestrictAdjunction g).comp (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))
      (restrictScalarsCompIsoOf g hgp)
      (extendRestrictAdjunction (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))
    (conjugateEquiv_squareZeroPullbackIso_inv (hq := hqW) hiW hW hipW hpbW hβτW)
    (CategoryTheory.Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv
      ((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).toAdjunction.comp
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS H)))
      (squareZeroExtensionOfScalarsAdjunction hiW hW hipW hpbW hβτW g)
      (squareZeroPushforwardNaturalityRightAdjointIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
        hH rfl hg))
    (conjugateEquiv_pullbackModulesCompIso_symm_trans_transport_hom (iW := iW) (H := H))
    (conjugateEquiv_squareZeroPullbackIso_hom (hq := hqV) hiV hV hipV hpbV hβτV)
    hR

end Coherence

end AlgebraicGeometry.Space

end
