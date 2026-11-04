module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackCoherenceDegreewise

/-!
# The coherence (`**`) of `c2` for any section of `X_V`

Let `X ⟶ X_V ⟶ X` and `X ⟶ X_W ⟶ X` be the base changes of `Spec k ⟶ Spec k[V] ⟶ Spec k` and
`Spec k ⟶ Spec k[W] ⟶ Spec k` along one `p : X ⟶ Spec k`, `H : X_W ⟶ X_V` a morphism under `X`
and `g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` a ring map over `𝒪_X` compatible with `H`. The
coherence (`**`) of Stacks 0DLL compares the identifications `c2` of derived base change with
derived pullback for `W` and for `V` through the comparison `χ` and the composition comparison of
derived pullbacks along `X ⟶ X_W ⟶ X_V`. Here it is proved for an arbitrary section `i_V` of `X_V`
with `i_W ≫ H = i_V`, and for data heterogeneously equal to those of the retractions.

## Main definitions

* `CategoryTheory.Functor.BaseChangePullbackCoherence`: the coherence (`**`) for abstract functors,
  as a proposition on its data.

## Main results

* `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_comp`: the coherence
  (`**`) for a section `i_V` of `X_V` with `i_W ≫ H = i_V`.
* `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_heq`: the coherence
  (`**`) for data heterogeneously equal to those of the retractions.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d d' u

namespace CategoryTheory.Functor

variable {CV CW YV YW Z : Type*} {_ : Category* CV} {_ : Category* CW} {_ : Category* YV}
  {_ : Category* YW} {_ : Category* Z}

/-- **The coherence (`**`) of Stacks 0DLL for abstract functors**: for `c2_W : T_W ≅ F_W ⋙ P_W`,
`c2_V : T_V ≅ F_V ⋙ P_V`, `χ : L ⋙ F_W ≅ F_V ⋙ P_H`, `τ : P_V ≅ P_H ⋙ P_W` and
`c : L ⋙ T_W ≅ T_V`, the identification `c2_W` at `L K`, followed by `P_W χ` and `τ⁻¹`, is `c`
followed by `c2_V`. -/
def BaseChangePullbackCoherence (L : CV ⥤ CW) (TW : CW ⥤ Z) (TV : CV ⥤ Z) (FV : CV ⥤ YV)
    (FW : CW ⥤ YW) (PH : YV ⥤ YW) (PW : YW ⥤ Z) (PV : YV ⥤ Z) (c2W : TW ≅ FW ⋙ PW)
    (c2V : TV ≅ FV ⋙ PV) (χ : L ⋙ FW ≅ FV ⋙ PH) (τ : PV ≅ PH ⋙ PW) (c : L ⋙ TW ≅ TV) (K : CV) :
    Prop :=
  c2W.hom.app (L.obj K) ≫ PW.map (χ.hom.app K) ≫ τ.inv.app (FV.obj K) =
    c.hom.app K ≫ c2V.hom.app K

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

section Coherence

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

attribute [local instance] isContinuous_smallBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {k : Type u} [CommRing k] {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))}
  {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iV : X ⟶ X'V} (hiV : IsThickeningHom B S hS iV)
  {qV : X'V ⟶ X} (hV : iV ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : iV.hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hH : yoneda.relativelyRepresentable H.hom) (hiH : iW ≫ H = iV)
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

/-- **Stacks 0DLL, the coherence (`**`) of `c2` with base change along `H`, for any section of
`X_V`**: `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence` for a section
`i_V` of `X_V` with `i_W ≫ H = i_V`, for a ring map `g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` over
`𝒪_X` compatible with `H`: the identification `c2`
for `W` at `g^* K`, followed by the derived pullback along `i_W` of `χ`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`) and the composition comparison of
derived pullbacks along `i_W ≫ H = i_V`, is the identification of the two derived base changes
followed by `c2` for `V`. -/
theorem squareZeroDerivedPullbackIso_comp_coherence_of_comp
    {g : sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj) ⟶
      sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)}
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj) = sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))
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
        ((squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
          hg).hom.app K) ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle hiH).inv.app
        ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.obj K) =
    (derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp).hom.app K ≫
      (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))).hom.app K := by
  subst hiH
  exact squareZeroDerivedPullbackIso_comp_coherence hiW hW hipW hpbW hβτW hiV hV hipV hpbV hβτV hH
    hg hgp K

omit hDV hDW in
/-- **The coherence (`**`) for data equal to those of the retractions**:
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_comp` for sheaves of
modules `M_V`, `M_W` equal to `𝒪_X ⊗_k V`, `𝒪_X ⊗_k W`, a ring map `g : 𝒪_X[M_V] ⟶ 𝒪_X[M_W]`
over `𝒪_X`, functors `F_V`, `F_W`, identifications `c2_V`, `c2_W` and a comparison `χ`, each
heterogeneously equal to the corresponding datum of the retractions (`F_V`, `F_W` the derived
equivalences, `c2_V`, `c2_W` the identifications
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso`, `χ` the comparison
`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`). -/
theorem squareZeroDerivedPullbackIso_comp_coherence_of_heq
    {MV MW : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2))}
    (hMV : ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj) = MV)
    (hMW : ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj) = MW)
    [hDVM : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MV)))]
    [hDWM : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MW)))]
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
    (hDVe : HEq hDVM hDV) (hDWe : HEq hDWM hDW)
    {g : sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MV ⟶
      sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MW}
    {g₀ : sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj) ⟶
      sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)}
    (hgg : HEq g g₀)
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g₀ =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ sqZeroExtSheafAnySiteProj MW = sqZeroExtSheafAnySiteProj MV)
    {FV : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MV))) ⥤ derivedModules B S hS X'V}
    {FW : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MW))) ⥤ derivedModules B S hS X'W}
    (hFV : HEq FV (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor)
    (hFW : HEq FW (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor)
    {c2V : (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj MV)).baseChange ≅
      FV ⋙ derivedPull B S hS (hasDerivedModulePullbacks B S hS) iV}
    {c2W : (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj MW)).baseChange ≅
      FW ⋙ derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW}
    (h2V : HEq c2V (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
      (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))))
    (h2W : HEq c2W (squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
      (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))))
    {χ : derivedExtensionOfScalars.{d, d'} g ⋙ FW ≅
      FV ⋙ derivedPull B S hS (hasDerivedModulePullbacks B S hS) H}
    (hχ : HEq χ (squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH
      hiH hg))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) MV)))) :
    Functor.BaseChangePullbackCoherence (derivedExtensionOfScalars.{d, d'} g)
      (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj MW)).baseChange
      (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj MV)).baseChange FV FW
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H)
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW)
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iV) c2W c2V χ
      ((smallEtaleDerivedPullbackData B S hS).triangle hiH)
      (derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp) K := by
  subst hMV hMW
  obtain rfl := eq_of_heq hDVe
  obtain rfl := eq_of_heq hDWe
  obtain rfl := eq_of_heq hgg
  obtain rfl := eq_of_heq hFV
  obtain rfl := eq_of_heq hFW
  obtain rfl := eq_of_heq h2V
  obtain rfl := eq_of_heq h2W
  obtain rfl := eq_of_heq hχ
  exact squareZeroDerivedPullbackIso_comp_coherence_of_comp hiV hV hipV hpbV hβτV hiW hW hipW
    hpbW hβτW hH hiH hg hgp K

end Coherence

end AlgebraicGeometry.Space

end
