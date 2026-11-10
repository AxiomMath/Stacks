module

public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTrace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditionalModels
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The trace of a composite of affine morphisms

Let `h : T₃ ⟶ T₁` and `π : T₁ ⟶ Y` be affine morphisms of quasi-compact quasi-separated schemes
and `E ∈ D_QCoh(𝒪_Y)` with `a_π(E)`, `a_{h ≫ π}(E)` and `a_h(a_π(E))` in `D^{≥0}`. The degree-zero
trace `t_E : (h ≫ π)_*H⁰(a_{h ≫ π}(E)) ⟶ H⁰(E)` is the composite of the traces of `h` and `π`,
read through `a_{h ≫ π} ≅ a_h ∘ a_π`.

The proof compares the identifications `R⁰g_* = g_*` along the composite: the canonical maps
`w(X)[0] ⟶ Rw(X[0])` (`Stacks.DerivedFunctor.singleDerivedUnit`) of `h`, `π` and `h ≫ π` are
compatible with `R(h ≫ π)_* ≅ Rπ_* ∘ Rh_*`, because the units of the three derived direct images
are (`Stacks.Duality.derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom`).

## Main results

* `Stacks.DerivedFunctor.singleDerivedUnit_comp`: compatibility of `w(X)[0] ⟶ Rw(X[0])` with
  composition of functors.
* `Stacks.Duality.FiniteTrace.trace_comp`: the trace of `h ≫ π` is the composite of the traces.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (w : A ⥤ B) [w.Additive]

/-- The isomorphism `w.mapHC(X[0]) ≅ w(X)[0]` of homotopy categories, as a map
`w(X)[0] ⟶ w.mapHC(X[0])`. -/
def singleMapHomotopyCategoryInv (M : A) :
    (HomotopyCategory.singleFunctor B 0).obj (w.obj M) ⟶
      (w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor A 0).obj M) :=
  (HomotopyCategory.quotient B _).map
    ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app M)

omit [HasDerivedCategory A] in
/-- The inverse of `w.mapHC(X[0]) ⟶ w(X)[0]` in the derived category is the image of the
homotopy-category isomorphism `singleMapHomotopyCategoryInv`. -/
theorem mapSingleQhIso_inv_app (M : A) : (mapSingleQhIso w 0).inv.app M =
    (singleFunctorIsoCompQh B 0).hom.app (w.obj M) ≫ Qh.map (singleMapHomotopyCategoryInv w M) := by
  have h₁ : (HomotopyCategory.singleFunctorPostcompQuotientIso B 0).hom.app (w.obj M) = 𝟙 _ := rfl
  have h₂ : (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).inv.app M = 𝟙 _ := rfl
  have h₃ : (w.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((CochainComplex.singleFunctor A 0).obj M) = 𝟙 _ := rfl
  simp only [mapSingleQhIso, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv,
    Functor.comp_map, Category.assoc, h₁, h₂, h₃]
  refine congrArg (_ ≫ ·) ?_
  refine ((congrArg (· ≫ _) (Qh.map_id _)).trans (Category.id_comp _)).trans ?_
  refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) (Qh.map_id _)).trans
    ((Category.id_comp _).trans
      ((w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).map_id _)))).trans ?_
  exact Category.comp_id _

section Comp

universe wC vC uC
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] (H : A ⥤ C) [H.Additive] (e : F ⋙ G ≅ H)

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
/-- The identifications `w(X[0]) ≅ w(X)[0]` of complexes for `F`, `G` and `H ≅ F ⋙ G` are
compatible. -/
theorem singleMapHomologicalComplex_inv_app_comp (M : A) :
    (CochainComplex.singleFunctor C 0).map (e.inv.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app (F.obj M) ≫
          (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) =
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).inv.app M ≫
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app
          ((CochainComplex.singleFunctor A 0).obj M) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, Functor.mapHomologicalComplex_map_f, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_map_assoc, Functor.mapHomologicalComplexCompIso_inv_app_f]
    have := e.inv.naturality
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M 0 rfl).inv
    simp only [Functor.comp_map] at this
    refine Eq.trans ?_ (congrArg (_ ≫ ·) this).symm
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    change ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (e.inv.app M)).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  · simp [hn]

variable (RG : DerivedCategory B ⥤ DerivedCategory C)
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RG)

omit [HasDerivedCategory A] in
/-- The identifications `w.mapHC(X[0]) ≅ w(X)[0]` for `F`, `G` and `H ≅ F ⋙ G`, read through the
unit of a right derived functor of `G`, are compatible. -/
theorem mapSingleQhIso_inv_app_comp_unit (M : A) :
    (mapSingleQhIso H 0).inv.app M ≫
        Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.singleFunctor A 0).obj M)) ≫
        αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.singleFunctor A 0).obj M)) =
      (singleFunctor C 0).map (e.inv.app M) ≫ (mapSingleQhIso G 0).inv.app (F.obj M) ≫
        αG.app ((HomotopyCategory.singleFunctor B 0).obj (F.obj M)) ≫
          RG.map ((singleFunctorIsoCompQh B 0).inv.app (F.obj M) ≫
            (mapSingleQhIso F 0).inv.app M) := by
  rw [mapSingleQhIso_inv_app, mapSingleQhIso_inv_app G, mapSingleQhIso_inv_app F,
    Iso.inv_hom_id_app_assoc]
  have hα := αG.naturality (singleMapHomotopyCategoryInv F M)
  simp only [Functor.comp_map] at hα
  rw [← hα]
  have hs := (singleFunctorIsoCompQh C 0).hom.naturality (e.inv.app M)
  simp only [Functor.comp_map] at hs
  simp only [Category.assoc]
  rw [reassoc_of% hs]
  congr 1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  change (HomotopyCategory.quotient C _).map
      ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).inv.app M) ≫
      (HomotopyCategory.quotient C _).map ((Functor.mapHomologicalComplexCompIso e
        (ComplexShape.up ℤ)).inv.app ((CochainComplex.singleFunctor A 0).obj M)) =
    ((HomotopyCategory.quotient C _).map ((CochainComplex.singleFunctor C 0).map (e.inv.app M)) ≫
      (HomotopyCategory.quotient C _).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app
          (F.obj M))) ≫
      (HomotopyCategory.quotient C _).map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Category.assoc,
    singleMapHomologicalComplex_inv_app_comp]

/-- The canonical map `w(X)[0] ⟶ Rw(X[0])`: the unit of `Rw` at the complex `X[0]`. -/
def singleDerivedUnit {A' B' : Type*} [Category A'] [Abelian A'] [HasDerivedCategory A']
    [Category B'] [Abelian B'] [HasDerivedCategory B'] (w : A' ⥤ B') [w.Additive]
    (Rw : DerivedCategory A' ⥤ DerivedCategory B')
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw) (X : A') :
    (singleFunctor B' 0).obj (w.obj X) ⟶ Rw.obj ((singleFunctor A' 0).obj X) :=
  (mapSingleQhIso w 0).inv.app X ≫ α.app ((HomotopyCategory.singleFunctor A' 0).obj X) ≫
    Rw.map ((singleFunctorIsoCompQh A' 0).inv.app X)

variable (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF)
  (RH : DerivedCategory A ⥤ DerivedCategory C)
  (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RH) (Dpf : RF ⋙ RG ≅ RH)

/-- **The canonical maps `w(X)[0] ⟶ Rw(X[0])` are compatible with composition**: if
`RF ⋙ RG ≅ RH` is compatible with the units, then so are the maps for `F`, `G` and `H ≅ F ⋙ G`. -/
theorem singleDerivedUnit_comp
    (hU : ∀ K, (Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
      αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ RG.map (αF.app K)) ≫
        Dpf.hom.app (Qh.obj K) = αH.app K) (M : A) :
    (singleFunctor C 0).map (e.inv.app M) ≫ singleDerivedUnit G RG αG (F.obj M) ≫
        RG.map (singleDerivedUnit F RF αF M) ≫ Dpf.hom.app ((singleFunctor A 0).obj M) =
      singleDerivedUnit H RH αH M := by
  have hn := Dpf.hom.naturality ((singleFunctorIsoCompQh A 0).inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [singleDerivedUnit, singleDerivedUnit, singleDerivedUnit, ← hU]
  simp only [Category.assoc]
  rw [← hn, reassoc_of% (mapSingleQhIso_inv_app_comp_unit F G H e RG αG M)]
  simp only [Category.assoc, Functor.map_comp]

end Comp

section Zero
variable (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ Rw)
variable [Rw.CommShift ℤ] [Rw.IsTriangulated] [PreservesFiniteLimits w] [EnoughInjectives A]
  (hGE : ∀ X : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj X)).IsGE 0)
  (hinj : ∀ J : A, Injective J →
      IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj J)))

/-- `H⁰` of the canonical map `w(X)[0] ⟶ Rw(X[0])`, read through `R⁰w ≅ w`, is the identity of
`w(X)`. -/
theorem homologyFunctor_map_singleDerivedUnit_comp_derivedZeroNatIso (X : A) :
    (homologyFunctor B 0).map (singleDerivedUnit w Rw α X) ≫
        (derivedZeroNatIso w Rw α hGE hinj).hom.app X =
      (singleFunctorCompHomologyFunctorIso B 0).hom.app (w.obj X) := by
  have : ∀ X, IsIso ((singleUnitHomology w Rw α 0).app X) :=
    isIso_singleUnitHomology_app w Rw α hGE hinj
  have : IsIso (singleUnitHomology w Rw α 0) := NatIso.isIso_of_isIso_app _
  simp only [derivedZeroNatIso, singleDerivedUnit, singleUnitTargetIso, singleUnitSourceIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.comp_map, Functor.map_comp, Category.assoc,
    Iso.symm_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  have e := ((Rw ⋙ homologyFunctor B 0).mapIso ((singleFunctorIsoCompQh A 0).app X)).inv_hom_id
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Functor.comp_map, Iso.app_inv,
    Iso.app_hom] at e
  rw [reassoc_of% e, asIso_inv, NatIso.isIso_inv_app]
  change (homologyFunctor B 0).map _ ≫ (singleUnitHomology w Rw α 0).app X ≫
    inv ((singleUnitHomology w Rw α 0).app X) ≫ _ = _
  rw [IsIso.hom_inv_id_assoc, ← (homologyFunctor B 0).map_comp_assoc, Iso.inv_hom_id_app]
  simp
end Zero

end Stacks.DerivedFunctor

open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality

/-- Transposing along a composite of adjunctions, then comparing right adjoints, is transposing
along the given adjunction. -/
private theorem comp_homEquiv_rightAdjointUniq_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E]
    {Lf : D ⥤ C} {Rf : C ⥤ D} {Lg : E ⥤ D} {Rg : D ⥤ E} {Lgf : E ⥤ C} {Rgf : C ⥤ E}
    (Af : Lf ⊣ Rf) (Ag : Lg ⊣ Rg) (Agf : Lgf ⊣ Rgf) (Dpb : Lg ⋙ Lf ≅ Lgf)
    (M : E) (N : C) (φ : Lgf.obj M ⟶ N) :
    Ag.homEquiv _ _ (Af.homEquiv _ _ (Dpb.hom.app M ≫ φ)) ≫
        (Adjunction.rightAdjointUniq ((Ag.comp Af).ofNatIsoLeft Dpb) Agf).hom.app N =
      Agf.homEquiv M N φ := by
  have h : (((Ag.comp Af).ofNatIsoLeft Dpb).ofNatIsoRight
      (Adjunction.rightAdjointUniq ((Ag.comp Af).ofNatIsoLeft Dpb) Agf)) = Agf :=
    Adjunction.ext (Adjunction.unit_rightAdjointUniq_hom _ _)
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, Equiv.trans_apply] using congrArg (fun a => a.homEquiv M N φ) h

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

open Stacks.Cohomology.DerivedPushforwardComposition
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The units of derived direct image along `f`, `g` and `f ≫ g` are compatible** with
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`. -/
theorem derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Scheme.Modules.pushforwardComp f g) (ComplexShape.up ℤ)).inv.app K) ≫
      (Stacks.Duality.derivedPushforwardUnit g).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (Stacks.Duality.derivedPushforward g).map ((Stacks.Duality.derivedPushforwardUnit f).app K)) ≫
      (Stacks.Duality.derivedPushforwardCompIso f g).hom.app (DerivedCategory.Qh.obj K) =
    (Stacks.Duality.derivedPushforwardUnit (f ≫ g)).app K :=
  compUnit_comp_compIso_of_adjunctions
    (homotopyPullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (homotopyPullbackPushforwardAdjunction g.toLRSHom.toShHom)
    (homotopyPullbackPushforwardAdjunction (f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom))
    (Stacks.Duality.derivedAdjunction f) (Stacks.Duality.derivedAdjunction g)
    (Stacks.Duality.derivedAdjunction (f ≫ g))
    (Functor.mapHomotopyCategoryCompIso (Scheme.Modules.pushforwardComp f g) (ComplexShape.up ℤ))
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f.toLRSHom.toShHom
      g.toLRSHom.toShHom)
    (Stacks.Duality.derivedPullbackCompIso f g)
    (Stacks.Duality.derivedPushforwardCompIso f g)
    (derivedAdjunction_counit_fac f.toLRSHom.toShHom)
    (derivedAdjunction_counit_fac g.toLRSHom.toShHom)
    (derivedAdjunction_counit_fac (f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom))
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models f.toLRSHom.toShHom
      g.toLRSHom.toShHom)
    (comp_homEquiv_rightAdjointUniq_hom_app _ _ _ _)
    (mapHomotopyCategory_pullbackComp_hom_app_comp_counit f.toLRSHom.toShHom
      g.toLRSHom.toShHom) K

namespace FiniteTrace

variable {Y T₁ T₃ : Scheme.{u}} (h : T₃ ⟶ T₁) (π : T₁ ⟶ Y) [QuasiCompact h] [QuasiSeparated h]
  [QuasiCompact π] [QuasiSeparated π] [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace T₁]
  [QuasiSeparatedSpace T₁] [CompactSpace T₃] [QuasiSeparatedSpace T₃]

/-- `a_{h ≫ π} ≅ a_π ⋙ a_h`, the composition isomorphism of twisted inverse images. -/
abbrev twistedCompIso :=
  twistedInverseImageCompIso h π (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs π)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (h ≫ π))

/-- The counit of `R(h ≫ π)_* ⊣ a_{h ≫ π}` is the composite of the counits of `h` and `π`. -/
theorem twistedAdj_comp_counit_app_hom (E : quasiCoherentDerivedCategory Y) :
    ((twistedAdj (h ≫ π)).counit.app E).hom =
      (derivedPushforwardCompIso h π).inv.app ((twisted (h ≫ π)).obj E).obj ≫
        (derivedPushforward π).map
          ((derivedPushforward h).map ((twistedCompIso h π).hom.app E).hom) ≫
          (derivedPushforward π).map ((twistedAdj h).counit.app ((twisted π).obj E)).hom ≫
            ((twistedAdj π).counit.app E).hom := by
  have := Adjunction.rightAdjointUniq_hom_app_counit (twistedAdj (h ≫ π))
    (((twistedAdj h).comp (twistedAdj π)).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardCompIso h π
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs π)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (h ≫ π)))) E
  rw [← this]
  simp [Adjunction.ofNatIsoLeft, Adjunction.comp_counit_app]
  rfl

/-- `H⁰` of `g_*M[0] ⟶ Rg_*(M[0])`, read through `R⁰g_* = g_*`, is the identity of `g_*M`. -/
theorem homology_map_singleDerivedUnit_comp_singleDerivedPushforwardHomologyIso {A B : Scheme.{u}}
    (g : A ⟶ B) (M : A.Modules) :
    (homologyFunctor B.Modules 0).map (Stacks.DerivedFunctor.singleDerivedUnit
        (Scheme.Modules.pushforward g) (derivedPushforward g) (derivedPushforwardUnit g) M) ≫
      (singleDerivedPushforwardHomologyIso g).hom.app M =
    (singleFunctorCompHomologyFunctorIso B.Modules 0).hom.app
      ((Scheme.Modules.pushforward g).obj M) :=
  Stacks.DerivedFunctor.homologyFunctor_map_singleDerivedUnit_comp_derivedZeroNatIso _ _ _ _ _ M

/-- `H⁰` of `g_*M[0] ⟶ Rg_*(M[0])` is `g_*M[0] ≅ H⁰(g_*M[0])` followed by the inverse of
`R⁰g_* = g_*`. -/
private theorem homology_map_singleDerivedUnit_eq {A B : Scheme.{u}} (g : A ⟶ B) (M : A.Modules) :
    (homologyFunctor B.Modules 0).map (Stacks.DerivedFunctor.singleDerivedUnit
        (Scheme.Modules.pushforward g) (derivedPushforward g) (derivedPushforwardUnit g) M) =
      (singleFunctorCompHomologyFunctorIso B.Modules 0).hom.app
        ((Scheme.Modules.pushforward g).obj M) ≫
        ((singleDerivedPushforwardHomologyIso g).app M).inv :=
  (Iso.eq_comp_inv _).mpr
    (homology_map_singleDerivedUnit_comp_singleDerivedPushforwardHomologyIso g M)

/-- **`R⁰` of a composite**: the identifications `R⁰g_* = g_*` of `h`, `π` and `h ≫ π` are
compatible with `R(h ≫ π)_* ≅ Rπ_* ∘ Rh_*`, through `h_*M[0] ⟶ Rh_*(M[0])`. -/
theorem singleDerivedPushforwardHomologyIso_comp {A B C : Scheme.{u}} (h : A ⟶ B) (π : B ⟶ C)
    (M₃ : A.Modules) :
    (Scheme.Modules.pushforwardComp h π).inv.app M₃ ≫
      ((singleDerivedPushforwardHomologyIso π).app ((Scheme.Modules.pushforward h).obj M₃)).inv ≫
        (homologyFunctor C.Modules 0).map ((derivedPushforward π).map
          (Stacks.DerivedFunctor.singleDerivedUnit (Scheme.Modules.pushforward h)
            (derivedPushforward h) (derivedPushforwardUnit h) M₃)) =
      ((singleDerivedPushforwardHomologyIso (h ≫ π)).app M₃).inv ≫
        (homologyFunctor C.Modules 0).map
          ((derivedPushforwardCompIso h π).inv.app ((singleFunctor A.Modules 0).obj M₃)) := by
  have hS := Stacks.DerivedFunctor.singleDerivedUnit_comp (Scheme.Modules.pushforward h)
    (Scheme.Modules.pushforward π) (Scheme.Modules.pushforward (h ≫ π))
    (Scheme.Modules.pushforwardComp h π) (derivedPushforward π) (derivedPushforwardUnit π)
    (derivedPushforward h) (derivedPushforwardUnit h) (derivedPushforward (h ≫ π))
    (derivedPushforwardUnit (h ≫ π)) (derivedPushforwardCompIso h π)
    (derivedPushforwardUnit_comp_derivedPushforwardCompIso_hom h π) M₃
  have hH := congrArg (homologyFunctor C.Modules 0).map hS
  simp only [Functor.map_comp] at hH
  rw [homology_map_singleDerivedUnit_eq, homology_map_singleDerivedUnit_eq] at hH
  have hs := (singleFunctorCompHomologyFunctorIso C.Modules 0).hom.naturality
    ((Scheme.Modules.pushforwardComp h π).inv.app M₃)
  simp only [Functor.comp_map, Functor.id_map] at hs
  simp only [Category.assoc] at hH
  rw [reassoc_of% hs] at hH
  rw [← (Iso.cancel_iso_hom_left
    ((singleFunctorCompHomologyFunctorIso C.Modules 0).app _) _ _).mp hH]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg _ (Category.comp_id _).symm))

variable (E : quasiCoherentDerivedCategory Y) [((twisted π).obj E).obj.IsGE 0]
  [((twisted (h ≫ π)).obj E).obj.IsGE 0] [((twisted h).obj ((twisted π).obj E)).obj.IsGE 0]

/-- The trace of `h` at `a_π(E)`, read on `H⁰(a_{h ≫ π}(E))` through `a_{h ≫ π} ≅ a_h ∘ a_π`. -/
def compTrace : (Scheme.Modules.pushforward h).obj (zeroTwisted (h ≫ π) E) ⟶ zeroTwisted π E :=
  (Scheme.Modules.pushforward h).map
      ((homologyFunctor T₃.Modules 0).map ((twistedCompIso h π).hom.app E).hom) ≫
    trace (g := h) ((twisted π).obj E)

/-- **The trace of a composite is the composite of the traces**: `t_{h ≫ π} = t_π ∘ π_*(τ)`, with
`τ : h_*H⁰(a_{h ≫ π}E) ⟶ H⁰(a_π E)` the trace of `h` at `a_π(E)`. -/
theorem trace_comp :
    trace (g := h ≫ π) E =
      (Scheme.Modules.pushforwardComp h π).inv.app
          (zeroTwisted (h ≫ π) E) ≫
        (Scheme.Modules.pushforward π).map (compTrace h π E) ≫ trace (g := π) E := by
  let M₃ := zeroTwisted (h ≫ π) E
  let ℓ₃ := liftSingle (g := h ≫ π) E (𝟙 M₃)
  let c := ((twistedCompIso h π).hom.app E).hom
  let ψ := (derivedPushforward h).map (ℓ₃ ≫ c) ≫
    ((twistedAdj h).counit.app ((twisted π).obj E)).hom
  let ι := Stacks.DerivedFunctor.singleDerivedUnit (Scheme.Modules.pushforward h)
    (derivedPushforward h) (derivedPushforwardUnit h) M₃
  have hB : trace (g := h ≫ π) E = ((singleDerivedPushforwardHomologyIso (h ≫ π)).app M₃).inv ≫
      (homologyFunctor Y.Modules 0).map ((derivedPushforwardCompIso h π).inv.app _ ≫
        (derivedPushforward π).map ψ ≫ ((twistedAdj π).counit.app E).hom) := by
    refine congrArg (_ ≫ ·) (congrArg _ ?_)
    have hn := (derivedPushforwardCompIso h π).inv.naturality ℓ₃
    simp only [Functor.comp_map] at hn
    rw [twistedAdj_comp_counit_app_hom, reassoc_of% hn]
    simp only [ψ, Functor.map_comp, Category.assoc]
    rfl
  have hC : compTrace h π E = ((singleDerivedPushforwardHomologyIso h).app M₃).inv ≫
      (homologyFunctor T₁.Modules 0).map ψ := by
    have hlift :
        liftSingle ((twisted π).obj E) ((homologyFunctor T₃.Modules 0).map c) = ℓ₃ ≫ c := by
      apply (bijective_homologyFunctor_map_of_isLE_of_isGE ((singleFunctor T₃.Modules 0).obj M₃)
        ((twisted h).obj ((twisted π).obj E)).obj 0).1
      dsimp only
      rw [homology_map_liftSingle, Functor.map_comp, homology_map_liftSingle]
      exact congrArg (· ≫ _) (Category.comp_id _).symm
    rw [compTrace, ← dualityMap_eq, dualityMap, hlift]
  have hD : liftSingle (g := π) E (compTrace h π E) = ι ≫ ψ := by
    apply (bijective_homologyFunctor_map_of_isLE_of_isGE
      ((singleFunctor T₁.Modules 0).obj ((Scheme.Modules.pushforward h).obj M₃))
        ((twisted π).obj E).obj 0).1
    dsimp only
    rw [homology_map_liftSingle, hC, (homologyFunctor T₁.Modules 0).map_comp ι ψ]
    rw [homology_map_singleDerivedUnit_eq h M₃, Category.assoc]
  have hE : (Scheme.Modules.pushforward π).map (compTrace h π E) ≫ trace (g := π) E =
      ((singleDerivedPushforwardHomologyIso π).app ((Scheme.Modules.pushforward h).obj M₃)).inv ≫
        (homologyFunctor Y.Modules 0).map ((derivedPushforward π).map (ι ≫ ψ) ≫
          ((twistedAdj π).counit.app E).hom) := by
    rw [← dualityMap_eq, dualityMap, hD]
  refine hB.trans (Eq.trans ?_ (congrArg (_ ≫ ·) hE).symm)
  simp only [Functor.map_comp, Category.assoc]
  exact ((reassoc_of% (singleDerivedPushforwardHomologyIso_comp h π M₃)) _).symm

end FiniteTrace

end Stacks.Duality
