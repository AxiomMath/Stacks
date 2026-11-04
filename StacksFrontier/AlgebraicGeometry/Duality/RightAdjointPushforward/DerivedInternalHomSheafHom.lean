module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.HomIntoCoextension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFromSingle
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is the derived internal Hom out of `f₊ 𝒪_Y`

Let `f : Y ⟶ X` be a morphism of schemes. The functor
`AlgebraicGeometry.derivedInternalHomPushforward f`, the derived extension of the left exact
functor `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of Stacks, Tag 0BUZ, agrees on every object with the value
`R ℰom_{𝒪_X}(f₊ 𝒪_Y[0], -)` of the derived internal Hom bifunctor
`Stacks.SheafOfModules.derivedSheafHom`.

On a K-injective complex `I` both sides are computed termwise: the first is `ℰom(f₊ 𝒪_Y, I)`
with `ℰom` the internal Hom sheaf of Stacks, Tag 0A6F, the second is the internal Hom complex
`ℋom^•(f₊ 𝒪_Y[0], I)`. These complexes are identified by Stacks, Tag 0996(2) at the complex
level (`AlgebraicGeometry.RingedSite.coextHomComplexIso`) applied to `L = 𝒪[0]` over `f₊ 𝒪_Y`,
together with `ℋom(𝒪, -) = id` and the uniqueness of right adjoints of restriction of scalars.

## Main results

* `AlgebraicGeometry.homSheafCompRestrictScalarsComplexIso`: the complex-level comparison.
* `AlgebraicGeometry.derivedInternalHomPushforwardObjIso`: the comparison in `D(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomologicalComplex
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

/-- `ℰom_{𝒪}(𝒪', -)` (Stacks, Tag 0A6F) is the coextension of scalars along `𝒪 ⟶ 𝒪'`: both are
right adjoint to restriction of scalars. -/
def RingedSpaceModuleAdjunction.homSheafIsoSheafCoextendScalars {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O O' : Sheaf J RingCat.{u}} (φ : O ⟶ O') :
    RingedSpaceModuleAdjunction.homSheaf φ ≅
      Stacks.SheafOfModules.CoextendScalars.coextendScalars.{u} φ :=
  Adjunction.rightAdjointUniq (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ)
    (Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction φ)

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u}) (O' : Sheaf Z.J CommRingCat.{u}) (φ₀ : Z.O ⟶ O')

/-- `ℰom_{𝒪}(𝒪', -)` followed by restriction of scalars is additive. -/
theorem homSheaf_comp_coeffRestrict_additive :
    (RingedSpaceModuleAdjunction.homSheaf (coeffHom Z O' φ₀) ⋙ coeffRestrict Z O' φ₀).Additive :=
  let := (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
    (coeffHom Z O' φ₀)).right_adjoint_additive
  inferInstance

/-- `ℰom_{𝒪}(𝒪', -)` read over `𝒪` is, termwise on a complex, coextension of scalars to `𝒪'` read
back over `𝒪`. -/
def homSheafCoeffComplexIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    letI := homSheaf_comp_coeffRestrict_additive Z O' φ₀
    ((RingedSpaceModuleAdjunction.homSheaf (coeffHom Z O' φ₀) ⋙
        coeffRestrict Z O' φ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      (coeffRestrictComplex Z O' φ₀).obj ((coeffCoextendComplex Z O' φ₀).obj I) :=
  letI := homSheaf_comp_coeffRestrict_additive Z O' φ₀
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coeffRestrict Z O' φ₀).mapIso
      ((RingedSpaceModuleAdjunction.homSheafIsoSheafCoextendScalars (coeffHom Z O' φ₀)).app
        (I.X n)))
    (fun n m _ => by
      change (coeffRestrict Z O' φ₀).map
          ((RingedSpaceModuleAdjunction.homSheafIsoSheafCoextendScalars
            (coeffHom Z O' φ₀)).hom.app (I.X n)) ≫
          (coeffRestrict Z O' φ₀).map ((coeffCoextend Z O' φ₀).map (I.d n m)) =
        (coeffRestrict Z O' φ₀).map
            ((RingedSpaceModuleAdjunction.homSheaf (coeffHom Z O' φ₀)).map (I.d n m)) ≫
          (coeffRestrict Z O' φ₀).map
            ((RingedSpaceModuleAdjunction.homSheafIsoSheafCoextendScalars
              (coeffHom Z O' φ₀)).hom.app (I.X m))
      rw [← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality])

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

section Complex

/-- `f₊ 𝒪_Y` as a sheaf of commutative rings on `X`. -/
abbrev pushforwardCommRingSheaf : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.sheaf

/-- **The complex-level comparison**, in the coefficient-site spelling: for a complex `I` of
`𝒪_X`-modules, the coextension of scalars to `f₊ 𝒪_Y` taken termwise, read back over `𝒪_X`, is
the internal Hom complex out of `f₊ 𝒪_Y` placed in degree zero. -/
def coeffCoextendRestrictComplexIso (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    (RingedSite.coeffRestrictComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
        (pushforwardCommRingSheaf f) ⟨f.c⟩).obj
        ((RingedSite.coeffCoextendComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
          (pushforwardCommRingSheaf f) ⟨f.c⟩).obj I) ≅
      (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
        ((single _ (ComplexShape.up ℤ) 0).obj
          ((RingedSite.coeffRestrict (Stacks.SheafOfModules.ringedSite X.sheaf)
            (pushforwardCommRingSheaf f) ⟨f.c⟩).obj (SheafOfModules.unit _))) I).obj := by
  let L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.coeffSite (Stacks.SheafOfModules.ringedSite X.sheaf)
        (pushforwardCommRingSheaf f)).O)) ℤ :=
    (single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _)
  let C := (RingedSite.coeffCoextendComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
    (pushforwardCommRingSheaf f) ⟨f.c⟩).obj I
  let e₂ : C ≅ (RingedSite.sheafHomComplex (RingedSite.coeffSite
      (Stacks.SheafOfModules.ringedSite X.sheaf) (pushforwardCommRingSheaf f)) L C).obj :=
    ((NatIso.mapHomologicalComplex
        (Stacks.SheafOfModules.InternalHom.unitInternalHomNatIso (Opens.grothendieckTopology X)
          (pushforwardCommRingSheaf f))
        (ComplexShape.up ℤ)).app C).symm ≪≫
      (RingedSite.sheafHomComplexSingleSourceIso (RingedSite.coeffSite
          (Stacks.SheafOfModules.ringedSite X.sheaf) (pushforwardCommRingSheaf f))
        (SheafOfModules.unit _) C).symm
  let s : (single _ (ComplexShape.up ℤ) 0).obj
        ((RingedSite.coeffRestrict (Stacks.SheafOfModules.ringedSite X.sheaf)
          (pushforwardCommRingSheaf f) ⟨f.c⟩).obj (SheafOfModules.unit _)) ≅
      (RingedSite.coeffRestrictComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
        (pushforwardCommRingSheaf f) ⟨f.c⟩).obj L :=
    ((HomologicalComplex.singleMapHomologicalComplex (RingedSite.coeffRestrict
        (Stacks.SheafOfModules.ringedSite X.sheaf) (pushforwardCommRingSheaf f) ⟨f.c⟩)
      (ComplexShape.up ℤ) 0).app (SheafOfModules.unit _)).symm
  exact (RingedSite.coeffRestrictComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
      (pushforwardCommRingSheaf f) ⟨f.c⟩).mapIso e₂ ≪≫
    RingedSite.coextHomComplexIso (Stacks.SheafOfModules.ringedSite X.sheaf)
      (pushforwardCommRingSheaf f) ⟨f.c⟩ L I ≪≫
    ((RingedSite.sheafHomComplexBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).mapIso
      s.op).app I


/-- **The complex-level comparison.** For a complex `I` of `𝒪_X`-modules, `ℰom_{𝒪_X}(f₊ 𝒪_Y, I)`
taken termwise is the internal Hom complex out of `f₊ 𝒪_Y` placed in degree zero. -/
def homSheafCompRestrictScalarsComplexIso
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    letI := homSheaf_comp_restrictScalars_additive f
    ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
        SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I ≅
      (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite X.sheaf)
        ((single _ (ComplexShape.up ℤ) 0).obj
          ((RingedSite.coeffRestrict (Stacks.SheafOfModules.ringedSite X.sheaf)
            (pushforwardCommRingSheaf f) ⟨f.c⟩).obj (SheafOfModules.unit _))) I).obj :=
  letI := homSheaf_comp_restrictScalars_additive f
  (RingedSite.homSheafCoeffComplexIso (Stacks.SheafOfModules.ringedSite X.sheaf)
      (pushforwardCommRingSheaf f) ⟨f.c⟩ I :) ≪≫ coeffCoextendRestrictComplexIso f I

/-- On a K-injective complex `I`, `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is `ℰom_{𝒪_X}(f₊ 𝒪_Y, I)` taken
termwise. -/
def derivedInternalHomPushforwardObjIsoOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (hI : I.IsKInjective) :
    letI := homSheaf_comp_restrictScalars_additive f
    (derivedInternalHomPushforward f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
        SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  letI := homSheaf_comp_restrictScalars_additive f
  have h := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (exists_isKInjective_quasiIso X)).2
    DerivedCategory.Qh (derivedInternalHomPushforward f) (derivedInternalHomPushforwardUnit f) I hI
  exact (derivedInternalHomPushforward f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
    (asIso ((derivedInternalHomPushforwardUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **`R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is the derived internal Hom out of `f₊ 𝒪_Y[0]`.** For every
`K ∈ D(𝒪_X)`, the derived extension of `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` takes at `K` the value
`R ℰom_{𝒪_X}(f₊ 𝒪_Y[0], K)` of the derived internal Hom bifunctor. -/
def derivedInternalHomPushforwardObjIso (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    (derivedInternalHomPushforward f).obj K ≅
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))))).obj K := by
  let R := Stacks.Injectives.functorialKInjectiveResolution (SheafOfModules.{u} X.ringCatSheaf)
  let K₀ := DerivedCategory.Q.objPreimage K
  let I := R.functor.obj K₀
  haveI : I.IsKInjective := R.isKInjective K₀
  haveI : QuasiIso (R.inclusion.app K₀) := R.quasiIso K₀
  let e : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map (R.inclusion.app K₀))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K
  let M := (RingedSite.coeffRestrict (Stacks.SheafOfModules.ringedSite X.sheaf)
    (pushforwardCommRingSheaf f) ⟨f.c⟩).obj (SheafOfModules.unit _)
  exact (derivedInternalHomPushforward f).mapIso e.symm ≪≫
    derivedInternalHomPushforwardObjIsoOfIsKInjective f I (R.isKInjective K₀) ≪≫
    DerivedCategory.Q.mapIso (homSheafCompRestrictScalarsComplexIso f I) ≪≫
    (@RingedSite.derivedSheafHomComparison (Stacks.SheafOfModules.ringedSite X.sheaf) _
      ((single _ (ComplexShape.up ℤ) 0).obj M) I (R.isKInjective K₀)).symm ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).op).app (DerivedCategory.Q.obj I) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj _).mapIso e

end Complex

end AlgebraicGeometry
