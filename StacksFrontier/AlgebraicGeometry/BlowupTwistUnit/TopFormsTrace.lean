module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.ChainTopFormsDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceComp
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupComposition
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct

/-!
# The trace of the top forms along a sequence of blowups

Let `h : W ⟶ S` be a stage of a sequence of blowups in closed points of `S`, let `p : S ⟶ S₀`, and
let `ω_W` be normalized relative to `ω_S`, that is `n_W : h^×(ω_S[0]) ≅ ω_W[0]`. To a morphism
`φ : (Ω^r_{W/S₀})^{**} ⟶ ω_W` this file attaches the composite

`Ω^r_{S/S₀} ⟶ h_*((Ω^r_{W/S₀})^{**}) ⟶ Rh_*((Ω^r_{W/S₀})^{**}[0]) ⟶ Rh_*(ω_W[0]) ⟶ ω_S`

— pull the top forms back to `W` and into the reflexive hull, apply `φ`, and take the trace of
`h` (the counit of `Rh_* ⊣ h^×`) — and proves how it behaves under one more blowup.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `singleToDerivedPushforward`: the comparison `(f_*M)[0] ⟶ Rf_*(M[0])`.
* `formsToPushforwardHull`: `Ω^n_{W/S₀} ⟶ b_*((Ω^n_{W'/S₀})^{**})`, adjoint to the pullback of
  forms followed by the canonical map to the hull.
* `topFormsTraceAux`, `ChainTopFormData.topFormsTrace`: the composite above.

## Main results

* `singleToDerivedPushforward_comp`, `twistedInverseImageAdjunction_comp_counit_app`: the
  comparison and the trace along a composite.
* `topFormsTraceAux_comp`, `ChainTopFormData.topFormsTrace_step`: **one blowup**. If the duality
  bijection of the blowup `b` sends `ψ` to `π ≫ φ`, and `π` restricts along the pullback of forms
  to the canonical map followed by `a`, then the composite of `ψ` is the composite of `a ≫ φ`.
* `exists_topFormsTraceAux_id_eq`: **the bottom stage**. Over `S` every map `Ω^n_{S/S₀} ⟶ ω_S`
  is the composite of some `φ`, when the top forms of `S` are reflexive.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
-/

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

section Edge

variable {X Y Z : Scheme.{u}}

/-- `(f_*M)[0] ⟶ Rf_*(M[0])`. -/
def singleToDerivedPushforward (f : X ⟶ Y) (M : X.Modules) :
    (DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (derivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).hom.app _ ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.pushforward f).mapHomotopyCategorySingleFunctor 0).inv.app M) ≫
    ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))).app
        ((HomotopyCategory.singleFunctor X.Modules 0).obj M) ≫
    (derivedPushforward f).map ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).inv.app M)

theorem singleToDerivedPushforward_naturality (f : X ⟶ Y) {M N : X.Modules} (g : M ⟶ N) :
    (DerivedCategory.singleFunctor Y.Modules 0).map ((Scheme.Modules.pushforward f).map g) ≫
        singleToDerivedPushforward f N =
      singleToDerivedPushforward f M ≫
        (derivedPushforward f).map ((DerivedCategory.singleFunctor X.Modules 0).map g) := by
  have h1 := (DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).hom.naturality
    ((Scheme.Modules.pushforward f).map g)
  have h2 := ((Scheme.Modules.pushforward f).mapHomotopyCategorySingleFunctor 0).inv.naturality g
  have h3 := ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))).naturality
    ((HomotopyCategory.singleFunctor X.Modules 0).map g)
  have h4 := (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).inv.naturality g
  simp only [Functor.comp_map] at h1 h2 h3 h4
  simp only [singleToDerivedPushforward, Category.assoc]
  rw [reassoc_of% h1, ← Functor.map_comp_assoc, h2, Functor.map_comp_assoc, reassoc_of% h3,
    ← Functor.map_comp, ← Functor.map_comp, h4]

theorem mapHomotopyCategorySingleFunctor_pushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategorySingleFunctor 0).inv.app M ≫
      (Functor.mapHomotopyCategoryCompIso (Scheme.Modules.pushforwardComp f g)
        (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.singleFunctor _ 0).obj M) =
    (HomotopyCategory.singleFunctor _ 0).map ((Scheme.Modules.pushforwardComp f g).inv.app M) ≫
      ((Scheme.Modules.pushforward g).mapHomotopyCategorySingleFunctor 0).inv.app
        ((Scheme.Modules.pushforward f).obj M) ≫
      ((Scheme.Modules.pushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((Scheme.Modules.pushforward f).mapHomotopyCategorySingleFunctor 0).inv.app M) :=
  Stacks.DeRham.GysinCohomologyBaseChange.mapHomotopyCategorySingleFunctor_modulePushforwardComp
    (Stacks.SchemeCohomology.hom f) (Stacks.SchemeCohomology.hom g) 0 M

theorem singleToDerivedPushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    singleToDerivedPushforward (f ≫ g) M =
      (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.pushforwardComp f g).inv.app M) ≫
        singleToDerivedPushforward g ((Scheme.Modules.pushforward f).obj M) ≫
        (derivedPushforward g).map (singleToDerivedPushforward f M) ≫
        (derivedPushforwardCompIso f g).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.singleComparison_comp_of_unit_comp
    (DerivedCategory.singleFunctorIsoCompQh _ 0)
    (DerivedCategory.singleFunctorIsoCompQh _ 0) (DerivedCategory.singleFunctorIsoCompQh _ 0)
    ((Scheme.Modules.pushforward f).mapHomotopyCategorySingleFunctor 0)
    ((Scheme.Modules.pushforward g).mapHomotopyCategorySingleFunctor 0)
    ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategorySingleFunctor 0)
    ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    ((homotopyPushforward g).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)))
    ((homotopyPushforward (f ≫ g)).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (Functor.mapHomotopyCategoryCompIso (Scheme.Modules.pushforwardComp f g) (ComplexShape.up ℤ))
    (derivedPushforwardCompIso f g) M ((Scheme.Modules.pushforwardComp f g).inv.app M)
    (by
      simpa only [Category.assoc] using
        derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom f g
          ((HomotopyCategory.singleFunctor X.Modules 0).obj M))
    (mapHomotopyCategorySingleFunctor_pushforwardComp f g M)

end Edge

section Trace

variable {Z X Y : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Z ⟶ X) (f : X ⟶ Y)

/-- **The trace of a composite.** -/
theorem twistedInverseImageAdjunction_comp_counit_app (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageAdjunction (g ≫ f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).counit.app K =
      (quasiCoherentDerivedPushforward (g ≫ f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).map
          ((twistedInverseImageCompIso g f (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).hom.app K) ≫
        (quasiCoherentDerivedPushforwardCompIso g f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).inv.app _ ≫
        (quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((twistedInverseImageAdjunction g
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).counit.app
            ((twistedInverseImage f
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K)) ≫
        (twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K := by
  rw [← Adjunction.rightAdjointUniq_hom_app_counit _
    (((twistedInverseImageAdjunction g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).comp
        (twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardCompIso g f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))))]
  simp only [twistedInverseImageCompIso, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app,
    Functor.comp_map, Category.assoc]

end Trace

section NormalizedTrace

theorem quasiCoherentHomEquiv_symm_hom {X : Scheme.{u}} (K L : quasiCoherentDerivedCategory X)
    (x : K.obj ⟶ L.obj) : ((quasiCoherentHomEquiv K L).symm x).hom = x := by
  simp only [quasiCoherentHomEquiv, Functor.FullyFaithful.homEquiv_symm_apply]
  exact (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι _)).map_preimage (X := K)
    (Y := L) x

theorem quasiCoherentHomEquiv_symm_comp {X : Scheme.{u}} {K L M : quasiCoherentDerivedCategory X}
    (x : K.obj ⟶ L.obj) (g : L ⟶ M) :
    (quasiCoherentHomEquiv K M).symm (x ≫ g.hom) = (quasiCoherentHomEquiv K L).symm x ≫ g := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentHomEquiv_symm_hom,
    quasiCoherentHomEquiv_symm_hom]

variable {S X X' : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
  (b : X' ⟶ X) (h : X ⟶ S) (ωS : quasiCoherentDerivedCategory S)
  (ωX : X.Modules) (hωX : ωX.IsQuasicoherent)
  (ωX' : X'.Modules) (hωX' : ωX'.IsQuasicoherent)
  (nX : ((twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj ωX)
  (nX' : ((twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X'.Modules 0).obj ωX')
  (F : X'.Modules) (hF : F.IsQuasicoherent)

/-- The duality bijection of `normalizedDualityHomEquiv` is `Rb_*` followed by the trace. -/
theorem normalizedDualityHomEquiv_apply (ψ : F ⟶ ωX') :
    normalizedDualityHomEquiv b h ωS ωX hωX ωX' hωX' nX nX' F hF ψ =
      (quasiCoherentDerivedPushforward b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map
        ((quasiCoherentHomEquiv (singleQuasiCoherent F hF 0)
          ((twistedInverseImage b (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
            (singleQuasiCoherent ωX hωX 0))).symm
          ((DerivedCategory.singleFunctor X'.Modules 0).map ψ ≫
            (normalizedUpperShriekIso b h ωS ωX hωX ωX' hωX' nX nX').inv)) ≫
        (twistedInverseImageAdjunction b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).counit.app
          (singleQuasiCoherent ωX hωX 0) := by
  show ((twistedInverseImageAdjunction b
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).homEquiv _ _).symm
      ((quasiCoherentHomEquiv (singleQuasiCoherent F hF 0)
          ((twistedInverseImage b (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
            (singleQuasiCoherent ωX hωX 0))).symm
        (𝟙 _ ≫ (DerivedCategory.singleFunctor X'.Modules 0).map ψ ≫
            (normalizedUpperShriekIso b h ωS ωX hωX ωX' hωX' nX nX').inv)) = _
  rw [Category.id_comp]
  exact (twistedInverseImageAdjunction b
    (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).homEquiv_counit _ _ _

/-- **The trace along a composite, read through two normalizations.** For isomorphisms
`e₁ : ω_X ≅ h^×ω_S` and `e₂ : ω_{X'} ≅ (b ≫ h)^×ω_S`, the trace along `b ≫ h` of `y ≫ e₂` is the
trace along `h` of the image of `y` under the duality bijection of `b` that the two normalizations
induce. -/
theorem trace_comp_twistedInverseImageObjIsoOfNormalizedOfQcqs
    {ωX : quasiCoherentDerivedCategory X} {ωX' : quasiCoherentDerivedCategory X'}
    (e₁ : ωX ≅ (twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS)
    (e₂ : ωX' ≅ (twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj ωS)
    {G : quasiCoherentDerivedCategory X'} (y : G ⟶ ωX') :
    (quasiCoherentDerivedPushforward (b ≫ h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).map (y ≫ e₂.hom) ≫
      (twistedInverseImageAdjunction (b ≫ h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).counit.app ωS =
    (quasiCoherentDerivedPushforwardCompIso b h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).inv.app G ≫
      (quasiCoherentDerivedPushforward h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map
        ((quasiCoherentDerivedPushforward b
            (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map
          (y ≫ (twistedInverseImageObjIsoOfNormalizedOfQcqs b h ωS e₁ e₂).inv) ≫
          (twistedInverseImageAdjunction b
            (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).counit.app ωX ≫ e₁.hom) ≫
      (twistedInverseImageAdjunction h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).counit.app ωS := by
  rw [twistedInverseImageAdjunction_comp_counit_app]
  have hcounit := (twistedInverseImageAdjunction b
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).counit_naturality e₁.hom
  have hnat := (quasiCoherentDerivedPushforwardCompIso b h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).inv.naturality
    (y ≫ e₂.hom ≫ (twistedInverseImageCompIso b h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).hom.app ωS)
  have key : y ≫ e₂.hom ≫ (twistedInverseImageCompIso b h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs b)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).hom.app ωS =
      (y ≫ (twistedInverseImageObjIsoOfNormalizedOfQcqs b h ωS e₁ e₂).inv) ≫
        (twistedInverseImage b (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map
          e₁.hom := by
    simp only [twistedInverseImageObjIsoOfNormalizedOfQcqs, twistedInverseImageObjIsoOfNormalized,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
      Iso.map_inv_hom_id, Category.comp_id]
  simp only [Functor.comp_map] at hcounit hnat
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  have hnat' := reassoc_of% hnat
  refine (hnat' _).trans ?_
  rw [key]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (quasiCoherentDerivedPushforward h
    (isQuasicoherent_homology_derivedPushforward_of_qcqs h)) ((quasiCoherentDerivedPushforward b
    (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map ((twistedInverseImage b
    (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map e₁.hom)), hcounit,
    Functor.map_comp_assoc]

/-- `normalizedDualityHomEquiv_apply`, with the normalization read as an isomorphism of
`D_QCoh`. -/
theorem normalizedDualityHomEquiv_apply' (ψ : F ⟶ ωX') :
    normalizedDualityHomEquiv b h ωS ωX hωX ωX' hωX' nX nX' F hF ψ =
      (quasiCoherentDerivedPushforward b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).map
        ((quasiCoherentHomEquiv (singleQuasiCoherent F hF 0)
            (singleQuasiCoherent ωX' hωX' 0)).symm
          ((DerivedCategory.singleFunctor X'.Modules 0).map ψ) ≫
          (twistedInverseImageObjIsoOfNormalizedOfQcqs b h ωS (ObjectProperty.isoMk _ nX).symm
            (ObjectProperty.isoMk _ nX').symm).inv) ≫
        (twistedInverseImageAdjunction b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).counit.app
          (singleQuasiCoherent ωX hωX 0) := by
  rw [normalizedDualityHomEquiv_apply]
  congr 2
  exact (quasiCoherentHomEquiv_symm_comp _ (twistedInverseImageObjIsoOfNormalizedOfQcqs b h ωS
    (ObjectProperty.isoMk _ nX : (twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS ≅
        singleQuasiCoherent ωX hωX 0).symm
    (ObjectProperty.isoMk _ nX' : (twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj ωS ≅
        singleQuasiCoherent ωX' hωX' 0).symm).inv)

end NormalizedTrace

/-- `quasiCoherentHomEquiv_symm_comp` at the inverse of a normalization. -/
theorem quasiCoherentHomEquiv_symm_comp_normalization_inv {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y)
    (ωY : quasiCoherentDerivedCategory Y) (ωX : X.Modules) (hωX : ωX.IsQuasicoherent)
    (n : ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY).obj ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj ωX)
    {K : quasiCoherentDerivedCategory X}
    (x : K.obj ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj ωX) :
    (quasiCoherentHomEquiv K _).symm (x ≫ n.inv) =
      (quasiCoherentHomEquiv K (singleQuasiCoherent ωX hωX 0)).symm x ≫
        (ObjectProperty.isoMk _ n : (twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY ≅
            singleQuasiCoherent ωX hωX 0).symm.hom :=
  quasiCoherentHomEquiv_symm_comp x (ObjectProperty.isoMk _ n : (twistedInverseImage f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY ≅
      singleQuasiCoherent ωX hωX 0).symm.hom

theorem quasiCoherentDerivedPushforward_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    {K L : quasiCoherentDerivedCategory X} (g : K ⟶ L) :
    ((quasiCoherentDerivedPushforward f hpush).map g).hom = (derivedPushforward f).map g.hom :=
  rfl

theorem quasiCoherentDerivedPushforwardCompIso_inv_app_hom {Z X Y : Scheme.{u}} (g : Z ⟶ X)
    (f : X ⟶ Y)
    (hpushg : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hpushgf : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (g ≫ f)).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory Z) :
    ((quasiCoherentDerivedPushforwardCompIso g f hpushg hpushf hpushgf).inv.app K).hom =
      (derivedPushforwardCompIso g f).inv.app K.obj :=
  rfl

theorem singleQcohHom_hom {X : Scheme.{u}} {M N : X.Modules} (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (φ : M ⟶ N) :
    (singleQcohHom hM hN φ).hom = (DerivedCategory.singleFunctor X.Modules 0).map φ :=
  quasiCoherentHomEquiv_symm_hom _ _ _


section Chain

/-- **Pull back the forms, then take the reflexive hull**: the map
`Ω^n_{W/S₀} ⟶ b_*((Ω^n_{W'/S₀})^{**})` adjoint to
`b^*Ω^n_{W/S₀} ⟶ Ω^n_{W'/S₀} ⟶ (Ω^n_{W'/S₀})^{**}`. -/
def formsToPushforwardHull {W' W S₀ : Scheme.{u}} (b : W' ⟶ W) (q : W ⟶ S₀) (q' : W' ⟶ S₀)
    (w : b ≫ q = q' ≫ 𝟙 S₀) (n : ℤ) :
    Scheme.Hom.relativeDifferentialForms q n ⟶
      (Scheme.Modules.pushforward b).obj
        (reflexiveHull (Scheme.Hom.relativeDifferentialForms q' n)) :=
  Scheme.Hom.formsDirectImageComparisonOver b q q' (𝟙 S₀) w n ≫
    (Scheme.Modules.pushforward b).map
      (toReflexiveHull (Scheme.Hom.relativeDifferentialForms q' n)).1

/-- The composition law for `formsToPushforwardHull`. -/
theorem formsToPushforwardHull_comp {W'' W' W S₀ : Scheme.{u}} (b : W'' ⟶ W') (h : W' ⟶ W)
    (q : W ⟶ S₀) (q' : W' ⟶ S₀) (q'' : W'' ⟶ S₀) (w : h ≫ q = q' ≫ 𝟙 S₀)
    (w' : b ≫ q' = q'' ≫ 𝟙 S₀) (w'' : (b ≫ h) ≫ q = q'' ≫ 𝟙 S₀) (n : ℤ) :
    formsToPushforwardHull (b ≫ h) q q'' w'' n ≫
        (Scheme.Modules.pushforwardComp b h).inv.app _ =
      Scheme.Hom.formsDirectImageComparisonOver h q q' (𝟙 S₀) w n ≫
        (Scheme.Modules.pushforward h).map (formsToPushforwardHull b q' q'' w' n) := by
  rw [formsToPushforwardHull, Scheme.Hom.formsDirectImageComparisonOver_comp h b q q' q''
    (𝟙 S₀) (𝟙 S₀) (𝟙 S₀) w w' w'' n]
  simp only [formsToPushforwardHull, Category.assoc, Functor.map_comp]
  congr 2


/-- The pullback of forms through one blowup in the composite: if `π` restricts along the
pullback of forms to `a`, the pullback of forms along `b ≫ h` followed by `Rh_*π` is the pullback
of forms along `h` followed by `a`. -/
theorem formsToPushforwardHull_comp_singleToDerivedPushforward {S₀ S W W' : Scheme.{u}}
    (p : S ⟶ S₀) (r : ℤ) (b : W' ⟶ W) (h : W ⟶ S)
    (π : (derivedPushforward b).obj ((DerivedCategory.singleFunctor W'.Modules 0).obj
        (reflexiveHull (Scheme.Hom.relativeDifferentialForms ((b ≫ h) ≫ p) r))) ⟶
      (DerivedCategory.singleFunctor W.Modules 0).obj
        (reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) r)))
    (a : reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) r) ⟶
      reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) r))
    (hπ : (DerivedCategory.singleFunctor W.Modules 0).map
          (formsToPushforwardHull b (h ≫ p) ((b ≫ h) ≫ p) (by simp) r) ≫
        singleToDerivedPushforward b _ ≫ π =
      (DerivedCategory.singleFunctor W.Modules 0).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) r)).1 ≫ a)) :
    (DerivedCategory.singleFunctor S.Modules 0).map
        (formsToPushforwardHull (b ≫ h) (𝟙 S ≫ p) ((b ≫ h) ≫ p) (by simp) r) ≫
      singleToDerivedPushforward (b ≫ h) _ ≫
        (derivedPushforwardCompIso b h).inv.app _ ≫ (derivedPushforward h).map π =
    (DerivedCategory.singleFunctor S.Modules 0).map
        (formsToPushforwardHull h (𝟙 S ≫ p) (h ≫ p) (by simp) r) ≫
      singleToDerivedPushforward h _ ≫
        (derivedPushforward h).map ((DerivedCategory.singleFunctor W.Modules 0).map a) := by
  have hforms := formsToPushforwardHull_comp b h (𝟙 S ≫ p) (h ≫ p) ((b ≫ h) ≫ p) (by simp)
    (by simp) (by simp) r
  have hnat1 := singleToDerivedPushforward_naturality h
    (formsToPushforwardHull b (h ≫ p) ((b ≫ h) ≫ p) (by simp) r)
  have hnat2 := singleToDerivedPushforward_naturality h
    ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) r)).1)
  rw [singleToDerivedPushforward_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, hforms, Functor.map_comp, Category.assoc, reassoc_of% hnat1,
    ← Functor.map_comp, ← Functor.map_comp, hπ, Functor.map_comp,
    Functor.map_comp, ← reassoc_of% hnat2, ← Functor.map_comp_assoc]
  rfl

/-- An associativity shuffle, at bare morphisms. -/
theorem comp_eq_of_comp_eq_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B₁ B₂ B₃ G : D} {X₁ X₂ X₃ X₄ : C} (P₁ : A ⟶ B₁) (P₂ : B₁ ⟶ B₂) (P₃ : B₂ ⟶ F.obj X₁)
    (π : X₁ ⟶ X₂) (Q₁ : A ⟶ B₃) (Q₂ : B₃ ⟶ F.obj X₃) (sa : X₃ ⟶ X₂) (sφ : X₂ ⟶ X₄)
    (X : X₃ ⟶ X₄) (T : F.obj X₄ ⟶ G)
    (hP : P₁ ≫ P₂ ≫ P₃ ≫ F.map π = Q₁ ≫ Q₂ ≫ F.map sa) (hX : X = sa ≫ sφ) :
    P₁ ≫ P₂ ≫ P₃ ≫ F.map π ≫ F.map sφ ≫ T = Q₁ ≫ Q₂ ≫ F.map X ≫ T := by
  rw [hX, Functor.map_comp, Category.assoc, ← reassoc_of% hP]

section Identity

variable {X : Scheme.{u}}

/-- In any model, the comparison for the identity is invertible at a quasi-coherent module in
degree zero: direct image along the identity is exact. -/
theorem isIso_homotopyPushforward_id_totalRightDerivedUnit_standard
    [hX : HasDerivedCategory X.Modules] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (((homotopyPushforward (𝟙 X)).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor X.Modules 0).obj M))) := by
  refine (StacksDraft.DerivedModel.isIso_schemeDerivedPushforwardUnit_app_iff_model (𝟙 X)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) hX hX _).mp ?_
  clear hX
  letI := HasDerivedCategory.standard X.Modules
  have hqc : ∀ n, (((CochainComplex.singleFunctor X.Modules 0).obj M).X n).IsQuasicoherent := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm inferInstance
    · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
        (R := X.ringCatSheaf)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
  have hac : ∀ n, (Scheme.Modules.pushforward (𝟙 X)).rightAcyclic
      (((CochainComplex.singleFunctor X.Modules 0).obj M).X n) := fun n =>
    Functor.rightAcyclic_of_iso (Scheme.Modules.pushforwardId X).symm _
      (Functor.rightAcyclic_of_exact (𝟭 X.Modules) _)
  exact AlgebraicGeometry.isIso_to_rightDerived_of_termwise_acyclic (𝟙 X)
    ((CochainComplex.singleFunctor X.Modules 0).obj M) hqc hac _ _

/-- **The comparison `(𝟙_*M)[0] ⟶ R(𝟙)_*(M[0])` is an isomorphism** at a quasi-coherent `M`. -/
theorem isIso_singleToDerivedPushforward_id (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (singleToDerivedPushforward (𝟙 X) M) := by
  have h := (StacksDraft.DerivedModel.isIso_schemeDerivedPushforwardUnit_app_iff_model (𝟙 X)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
    ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor X.Modules 0).obj M))).mp
    (isIso_homotopyPushforward_id_totalRightDerivedUnit_standard
      (hX := HasDerivedCategory.standard _) M)
  rw [singleToDerivedPushforward]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h inferInstance))

end Identity

/-- An isomorphism followed by its inverse, at bare morphisms. -/
theorem comp_comp_asIso_inv_comp {C : Type*} [Category C] {A B D E : C} (P₁ : A ⟶ B)
    (P₂ : B ⟶ D) (h : IsIso (P₁ ≫ P₂)) (g : A ⟶ E) :
    P₁ ≫ P₂ ≫ (@asIso _ _ _ _ (P₁ ≫ P₂) h).inv ≫ g = g := by
  rw [asIso_inv, ← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

section Aux

variable {S₀ S W : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace W]
  [QuasiSeparatedSpace W]

/-- **The composite `Ω^n_{S/S₀} ⟶ ω_S` attached to `φ : (Ω^n_{W/S₀})^{**} ⟶ ω_W`**, for `ω_W`
normalized by `n_W : h^×(ω_S[0]) ≅ ω_W[0]`: pull the forms back to `W` and into the hull, apply
`φ`, and take the trace of `h` back to `S`. -/
def topFormsTraceAux (p : S ⟶ S₀) (n : ℤ) (h : W ⟶ S) (ωS : S.Modules)
    (hωS : ωS.IsQuasicoherent) (hL : (hullForms p n h).IsQuasicoherent) (ωW : W.Modules)
    (nW : ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
      (singleQuasiCoherent ωS hωS 0)).obj ≅ (DerivedCategory.singleFunctor W.Modules 0).obj ωW)
    (φ : hullForms p n h ⟶ ωW) :
    Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n ⟶ ωS :=
  (singleHomEquiv _ _).symm
    ((DerivedCategory.singleFunctor S.Modules 0).map
        (formsToPushforwardHull h (𝟙 S ≫ p) (h ≫ p) (by simp) n) ≫
      singleToDerivedPushforward h _ ≫
      ((quasiCoherentDerivedPushforward h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).map
        ((quasiCoherentHomEquiv (singleQuasiCoherent _ hL 0) _).symm
          ((DerivedCategory.singleFunctor W.Modules 0).map φ ≫ nW.inv)) ≫
      (twistedInverseImageAdjunction h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).counit.app
        (singleQuasiCoherent ωS hωS 0)).hom)

variable {W' : Scheme.{u}} [CompactSpace W'] [QuasiSeparatedSpace W']

/-- **One morphism in the composite**: the duality bijection of `b` carries `ψ` to `π ≫ φ`, and
`π` restricts along the pullback of forms to `a`, so the composite of `ψ` along `b ≫ h` is that
of `a ≫ φ` along `h`. -/
theorem topFormsTraceAux_comp (p : S ⟶ S₀) (n : ℤ) (b : W' ⟶ W) (h : W ⟶ S) (ωS : S.Modules)
    (hωS : ωS.IsQuasicoherent) (hL : (hullForms p n h).IsQuasicoherent)
    (hL' : (hullForms p n (b ≫ h)).IsQuasicoherent) (ωW : W.Modules)
    (hωW : ωW.IsQuasicoherent) (ωW' : W'.Modules) (hωW' : ωW'.IsQuasicoherent)
    (nW : ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
      (singleQuasiCoherent ωS hωS 0)).obj ≅ (DerivedCategory.singleFunctor W.Modules 0).obj ωW)
    (nW' : ((twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj
        (singleQuasiCoherent ωS hωS 0)).obj ≅
          (DerivedCategory.singleFunctor W'.Modules 0).obj ωW')
    (φ : hullForms p n h ⟶ ωW) (ψ : hullForms p n (b ≫ h) ⟶ ωW')
    (π : (quasiCoherentDerivedPushforward b
        (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
          (singleQuasiCoherent _ hL' 0) ⟶ singleQuasiCoherent _ hL 0)
    (a : hullForms p n h ⟶ hullForms p n h)
    (hπ : (DerivedCategory.singleFunctor W.Modules 0).map
          (formsToPushforwardHull b (h ≫ p) ((b ≫ h) ≫ p) (by simp) n) ≫
        singleToDerivedPushforward b _ ≫ π.hom =
      (DerivedCategory.singleFunctor W.Modules 0).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n)).1 ≫ a))
    (hψ : normalizedDualityHomEquiv b h (singleQuasiCoherent ωS hωS 0) ωW hωW ωW' hωW' nW nW'
      _ hL' ψ = π ≫ singleQcohHom hL hωW φ) :
    topFormsTraceAux p n (b ≫ h) ωS hωS hL' ωW' nW' ψ =
      topFormsTraceAux p n h ωS hωS hL ωW nW (a ≫ φ) := by
  have hdual := (normalizedDualityHomEquiv_apply' b h (singleQuasiCoherent ωS hωS 0) ωW hωW ωW'
    hωW' nW nW' _ hL' ψ).symm.trans hψ
  have htr := trace_comp_twistedInverseImageObjIsoOfNormalizedOfQcqs b h
    (singleQuasiCoherent ωS hωS 0)
    (ObjectProperty.isoMk _ nW : (twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj (singleQuasiCoherent ωS hωS 0) ≅
        singleQuasiCoherent ωW hωW 0).symm
    (ObjectProperty.isoMk _ nW' : (twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj
        (singleQuasiCoherent ωS hωS 0) ≅ singleQuasiCoherent ωW' hωW' 0).symm
    ((quasiCoherentHomEquiv (singleQuasiCoherent _ hL' 0) (singleQuasiCoherent ωW' hωW' 0)).symm
      ((DerivedCategory.singleFunctor W'.Modules 0).map ψ))
  rw [reassoc_of% hdual] at htr
  have hpre := quasiCoherentHomEquiv_symm_comp_normalization_inv (b ≫ h)
    (singleQuasiCoherent ωS hωS 0) ωW' hωW' nW' (K := singleQuasiCoherent _ hL' 0)
    ((DerivedCategory.singleFunctor W'.Modules 0).map ψ)
  have hpre' := quasiCoherentHomEquiv_symm_comp_normalization_inv h
    (singleQuasiCoherent ωS hωS 0) ωW hωW nW (K := singleQuasiCoherent _ hL 0)
    ((DerivedCategory.singleFunctor W.Modules 0).map (a ≫ φ))
  have hforms := formsToPushforwardHull_comp_singleToDerivedPushforward p n b h π.hom a hπ
  unfold topFormsTraceAux
  congr 1
  rw [hpre, htr, hpre']
  simp only [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedPushforward_map_hom,
    quasiCoherentDerivedPushforwardCompIso_inv_app_hom, quasiCoherentHomEquiv_symm_hom,
    singleQcohHom_hom, Functor.map_comp, Category.assoc]
  exact comp_eq_of_comp_eq_aux (derivedPushforward h) _ _ _ π.hom _ _
    ((DerivedCategory.singleFunctor W.Modules 0).map a) _ _ _ hforms
    (quasiCoherentHomEquiv_symm_hom _ _ _)

/-- **The bottom stage.** Over `S` itself every map `Ω^n_{S/S₀} ⟶ ω_S` is the composite of some
`φ : (Ω^n_{S/S₀})^{**} ⟶ ω_S`, as soon as the top forms are reflexive. -/
theorem exists_topFormsTraceAux_id_eq (p : S ⟶ S₀) (n : ℤ) (ωS : S.Modules)
    (hωS : ωS.IsQuasicoherent) (hL : (hullForms p n (𝟙 S)).IsQuasicoherent)
    (nS : ((twistedInverseImage (𝟙 S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).obj
        (singleQuasiCoherent ωS hωS 0)).obj ≅ (DerivedCategory.singleFunctor S.Modules 0).obj ωS)
    [IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1]
    (β : Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n ⟶ ωS) :
    ∃ φ, topFormsTraceAux p n (𝟙 S) ωS hωS hL ωS nS φ = β := by
  haveI := hL
  have hF : IsIso (formsToPushforwardHull (𝟙 S) (𝟙 S ≫ p) (𝟙 S ≫ p) (by simp) n) := by
    have : IsIso (Scheme.Hom.relativeDifferentialFormsMap (𝟙 S) (𝟙 S ≫ p) (𝟙 S ≫ p) (𝟙 S₀)
        (by simp) n) :=
      Scheme.Hom.isIso_relativeDifferentialFormsMap _ _ _ _ _
        (Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso _ _ _ _ _) n
    have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).unit.app
        (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)) := inferInstance
    unfold formsToPushforwardHull Scheme.Hom.formsDirectImageComparisonOver
    infer_instance
  have he := isIso_singleToDerivedPushforward_id (hullForms p n (𝟙 S))
  let P := (DerivedCategory.singleFunctor S.Modules 0).map
      (formsToPushforwardHull (𝟙 S) (𝟙 S ≫ p) (𝟙 S ≫ p) (by simp) n) ≫
    singleToDerivedPushforward (𝟙 S) (hullForms p n (𝟙 S))
  haveI hP : IsIso P := IsIso.comp_isIso' inferInstance he
  let y := (twistedInverseImageAdjunction (𝟙 S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).homEquiv _ _
    ((quasiCoherentHomEquiv ((quasiCoherentDerivedPushforward (𝟙 S)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).obj
          (singleQuasiCoherent _ hL 0)) (singleQuasiCoherent ωS hωS 0)).symm
      ((@asIso _ _ _ _ P hP).inv ≫ (DerivedCategory.singleFunctor S.Modules 0).map β))
  refine ⟨(singleHomEquiv _ _).symm (y.hom ≫ nS.hom), ?_⟩
  have hY : (quasiCoherentHomEquiv (singleQuasiCoherent _ hL 0) _).symm
      ((DerivedCategory.singleFunctor S.Modules 0).map
        ((singleHomEquiv _ _).symm (y.hom ≫ nS.hom)) ≫ nS.inv) = y := by
    apply (quasiCoherentHomEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    have : (DerivedCategory.singleFunctor S.Modules 0).map
        ((singleHomEquiv _ _).symm (y.hom ≫ nS.hom)) = y.hom ≫ nS.hom :=
      (singleHomEquiv _ _).apply_symm_apply _
    rw [this, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hZ : (quasiCoherentDerivedPushforward (𝟙 S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).map y ≫
      (twistedInverseImageAdjunction (𝟙 S)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).counit.app
          (singleQuasiCoherent ωS hωS 0) =
      (quasiCoherentHomEquiv _ _).symm ((@asIso _ _ _ _ P hP).inv ≫
        (DerivedCategory.singleFunctor S.Modules 0).map β) := by
    exact ((twistedInverseImageAdjunction (𝟙 S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).homEquiv_counit _ _ _).symm.trans
      (Equiv.symm_apply_apply _ _)
  unfold topFormsTraceAux
  rw [hY, hZ, quasiCoherentHomEquiv_symm_hom]
  apply (singleHomEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  exact comp_comp_asIso_inv_comp _ _ hP _

end Aux

variable {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀} {r : ℕ} {T : Set S}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}

/-- **The composite `Ω^r_{S/S₀} ⟶ ω_S` attached to `φ_W : (Ω^r_{W/S₀})^{**} ⟶ ω_W`** at a stage
of a sequence of blowups in closed points: pull the top forms back to `W` and into the hull, apply
`φ_W`, and take the trace of the normalized dualizing module `ω_W` back to `S`. -/
def ChainTopFormData.topFormsTrace (D : ChainTopFormData p r T ω) {W : Scheme.{u}}
    {h : W ⟶ S} (hc : PointBlowupChain S T W h) (φ : hullForms p (r : ℤ) h ⟶ ω W h) :
    Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ) ⟶ ω S (𝟙 S) :=
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  topFormsTraceAux p (r : ℤ) h (ω S (𝟙 S)) (D.isQuasicoherent_dualizing PointBlowupChain.refl)
    (D.isQuasicoherent_hull hc) (ω W h) (D.normalized hc) φ

/-- **One blowup in the composite.** -/
theorem ChainTopFormData.topFormsTrace_step (D : ChainTopFormData p r T ω) {W : Scheme.{u}}
    {h : W ⟶ S} (hc : PointBlowupChain S T W h) (w : W) (hw : IsClosed ({w} : Set W))
    (hwT : h.base w ∈ T) (φ : hullForms p (r : ℤ) h ⟶ ω W h)
    (π : haveI := compactSpace_of_pointBlowupChain hc
      haveI := quasiSeparatedSpace_of_pointBlowupChain hc
      haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
      haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
      (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
          (D.isQuasicoherent_hull (hc.step w hw hwT)) 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) (D.isQuasicoherent_hull hc) 0)
    (a : hullForms p (r : ℤ) h ⟶ hullForms p (r : ℤ) h)
    (hπ : (DerivedCategory.singleFunctor W.Modules 0).map
          (formsToPushforwardHull (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p)
            ((AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ≫ p) (by simp) (r : ℤ)) ≫
        singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) _ ≫
          π.hom =
      (DerivedCategory.singleFunctor W.Modules 0).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 ≫ a)) :
    D.topFormsTrace (hc.step w hw hwT) ((D.stepDualityEquiv hc w hw hwT).symm
        (π ≫ singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ)) =
      D.topFormsTrace hc (a ≫ φ) := by
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
  exact topFormsTraceAux_comp p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) h
    (ω S (𝟙 S)) (D.isQuasicoherent_dualizing PointBlowupChain.refl) (D.isQuasicoherent_hull hc)
    (D.isQuasicoherent_hull (hc.step w hw hwT)) (ω W h) (D.isQuasicoherent_dualizing hc) _
    (D.isQuasicoherent_dualizing (hc.step w hw hwT)) (D.normalized hc)
    (D.normalized (hc.step w hw hwT)) φ _ π a hπ (Equiv.apply_symm_apply _ _)

end Chain

end Stacks.BlowupTwistUnit
