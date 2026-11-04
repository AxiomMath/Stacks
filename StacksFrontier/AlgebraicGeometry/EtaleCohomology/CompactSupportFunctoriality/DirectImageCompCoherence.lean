module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCochain
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the composition isomorphisms of derived direct images

For morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` of schemes and a ring `Λ`, the composition isomorphism
`R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` on `D(-_étale, Λ)` of Cohomology on Sites, Tag 0D6E, is
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedDerivedCompIso`. This file records
how it is computed on a complex and proves its associativity pentagon.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app` —
  precomposed with the derivation unit of `R(f ≫ g)_*`, the composition isomorphism is the
  iterated derivation unit.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedDerivedCompIso_assoc` — the
  associativity pentagon for three composable morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- Naturality of the derivation unit of `Rp_*` with respect to a morphism of complexes. -/
private theorem etaleModuleDerivedDirectImageUnboundedUnit_app_comp_map_Q_map {S T : Scheme.{u}}
    (p : S ⟶ T) {K L : CochainComplex (EtaleModules.{u, r} Λ S) ℤ} (φ : K ⟶ L) :
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p).app K ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p).map (DerivedCategory.Q.map φ) =
      DerivedCategory.Q.map (((etaleModuleDirectImage.{u, r} Λ p).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p).app L :=
  ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p).naturality φ).symm

section Fac

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)

/-- **The composition isomorphism on a complex.** Precomposed with the derivation unit of
`R(f ≫ g)_*`, the isomorphism `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` is the iterated derivation unit:
the comparison of direct images along the composite, the unit of `Rg_*` at `f_* K` and `Rg_*` of
the unit of `Rf_*`. -/
@[reassoc]
theorem etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg).app K ≫
        (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f g fg hfg).hom.app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) := by
  refine (Functor.rightDerivedNatTrans_app _ _
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg)
    (etaleModuleDerivedDirectImageUnboundedDerivedCompUnit.{u, r} Λ f g fg hfg)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) (𝟙 _) K).trans ?_
  simp [etaleModuleDerivedDirectImageUnboundedDerivedCompUnit]

/-- The inverse of the composition isomorphism on a complex: the iterated derivation unit,
followed by the inverse composition isomorphism, is the comparison of the direct images along the
composite followed by the derivation unit of `R(f ≫ g)_*`. -/
@[reassoc]
theorem etaleModuleDerivedDirectImageUnboundedDerivedCompIso_inv_fac_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f g fg hfg).inv.app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg).app K := by
  rw [← cancel_epi (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
      (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).inv.app K)),
    ← etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app_assoc,
    Iso.hom_inv_id_app, ← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Fac

section Assoc

variable {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y)
  (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h) (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h)
  (h₂ : fgh = f ≫ gh)

/-- **The associativity pentagon of the composition isomorphisms of derived direct images.** For
three composable morphisms `f`, `g`, `h`, the two identifications of `R(f ≫ g ≫ h)_*` with
`Rf_* ⋙ Rg_* ⋙ Rh_*` agree. Both are maps out of the right derived functor `R(f ≫ g ≫ h)_*`, so
it suffices to compare them precomposed with its derivation unit, where they are the iterated
units composed with the two routes of the associativity pentagon of the underived direct images
(`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`). -/
theorem etaleModuleDerivedDirectImageUnboundedDerivedCompIso_assoc :
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ fg h fgh h₁).hom ≫
        Functor.whiskerRight
          (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f g fg hfg).hom
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h) =
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f gh fgh h₂).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
          (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ g h gh hgh).hom ≫
        (Functor.associator _ _ _).inv := by
  refine Functor.rightDerived_ext _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fgh)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ T) (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.comp_id]
  have hnc :=
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ g h gh hgh).hom.naturality
      ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnc
  rw [etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app_assoc,
    etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app_assoc,
    ← Functor.map_comp, etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app, hnc,
    etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app_assoc]
  simp only [Functor.map_comp, Functor.comp_map]
  rw [reassoc_of% etaleModuleDerivedDirectImageUnboundedUnit_app_comp_map_Q_map,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext n : 1
  simpa [etaleModuleDirectImageComp] using
    smallEtalePushforwardComp'_inv_app_cocycle f g h fg hfg gh hgh fgh h₁ h₂
      (ModuleCat.{max (u + 1) r} Λ) (K.X n)

/-- The associativity pentagon of `etaleModuleDerivedDirectImageUnboundedDerivedCompIso_assoc`
for the inverse isomorphisms, objectwise: the two identifications of `Rf_* ⋙ Rg_* ⋙ Rh_*` with
`R(f ≫ g ≫ h)_*` agree. -/
@[reassoc]
theorem etaleModuleDerivedDirectImageUnboundedDerivedCompIso_assoc_inv_app
    (K : DerivedCategory (EtaleModules.{u, r} Λ T)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h).map
        ((etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f g fg hfg).inv.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ fg h fgh h₁).inv.app K =
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ g h gh hgh).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K) ≫
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f gh fgh h₂).inv.app K := by
  have p := congr_app (etaleModuleDerivedDirectImageUnboundedDerivedCompIso_assoc.{u, r} Λ
    f g h fg hfg gh hgh fgh h₁ h₂) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.comp_id] at p
  have pk := congrArg Iso.inv (Iso.ext p :
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ fg h fgh h₁).app K ≪≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h).mapIso
        ((etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f g fg hfg).app K) =
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ f gh fgh h₂).app K ≪≫
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ g h gh hgh).app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K))
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] using pk

end Assoc

/-! ### Vertical pasting of the underived base change maps -/

section SheafPaste

variable {X Y Z X' Y' Z' : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (hab : ab = a ≫ b)
  (g : Z' ⟶ Z) (g₁ : Y' ⟶ Y) (g₂ : X' ⟶ X) (a' : X' ⟶ Y') (b' : Y' ⟶ Z') (ab' : X' ⟶ Z')
  (hab' : ab' = a' ≫ b') (ha : g₂ ≫ a = a' ≫ g₁) (hb : g₁ ≫ b = b' ≫ g)
  (hc : g₂ ≫ ab = ab' ≫ g)

include hab hab' ha hb in
/-- The comparison of the two composite direct images around the outer rectangle of two
vertically stacked squares is the vertical composite of the comparisons of the two squares, read
through the composition isomorphisms of the direct images along the two vertical composites. -/
theorem smallEtaleDirectImageSquare_vComp (A : Type*) [Category* A] :
    smallEtaleDirectImageSquare ab g g₂ ab' hc A =
      ((TwoSquare.vComp (smallEtaleDirectImageSquare a g₁ g₂ a' ha A)
        (smallEtaleDirectImageSquare b g g₁ b' hb A)).whiskerRight
          (smallEtalePushforwardComp' a b ab hab A).inv).whiskerLeft
        (smallEtalePushforwardComp' a' b' ab' hab' A).hom := by
  subst hab hab'
  have hP : g₂ ≫ a ≫ b = a' ≫ g₁ ≫ b := by rw [← Category.assoc, ha, Category.assoc]
  have p₁ := smallEtalePushforwardComp'_assoc g₂ a b (g₂ ≫ a) rfl (a ≫ b) rfl (g₂ ≫ a ≫ b)
    (by simp) rfl A
  have p₂ := smallEtalePushforwardComp'_assoc a' g₁ b (g₂ ≫ a) ha (g₁ ≫ b) rfl (g₂ ≫ a ≫ b)
    (by simp) hP A
  have p₃ := smallEtalePushforwardComp'_assoc a' b' g (a' ≫ b') rfl (g₁ ≫ b) hb
    (g₂ ≫ a ≫ b) hc hP A
  refine TwoSquare.ext _ _ fun F => ?_
  have q₁ := congrArg (fun e => e.hom.app F) p₁
  have q₂ := congrArg (fun e => e.hom.app F) p₂
  have q₃ := congrArg (fun e => e.hom.app F) p₃
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at q₁ q₂ q₃
  have e₁ : (smallEtalePushforwardComp' g₂ (a ≫ b) (g₂ ≫ a ≫ b) rfl A).hom.app F =
      (smallEtalePushforwardComp' a b (a ≫ b) rfl A).inv.app _ ≫
        (smallEtalePushforward b A).map
          ((smallEtalePushforwardComp' g₂ a (g₂ ≫ a) rfl A).hom.app F) ≫
        (smallEtalePushforwardComp' (g₂ ≫ a) b (g₂ ≫ a ≫ b) (by simp) A).hom.app F := by
    rw [q₁, Iso.inv_hom_id_app_assoc]
  have e₂ : (smallEtalePushforward b A).map
        ((smallEtalePushforwardComp' a' g₁ (g₂ ≫ a) ha A).inv.app F) ≫
        (smallEtalePushforwardComp' g₁ b (g₁ ≫ b) rfl A).hom.app
          ((smallEtalePushforward a' A).obj F) =
      (smallEtalePushforwardComp' (g₂ ≫ a) b (g₂ ≫ a ≫ b) (by simp) A).hom.app F ≫
        (smallEtalePushforwardComp' a' (g₁ ≫ b) (g₂ ≫ a ≫ b) hP A).inv.app F := by
    rw [← cancel_mono ((smallEtalePushforwardComp' a' (g₁ ≫ b) (g₂ ≫ a ≫ b) hP A).hom.app F)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← q₂, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have e₃ : (smallEtalePushforwardComp' b' g (g₁ ≫ b) hb A).inv.app
        ((smallEtalePushforward a' A).obj F) ≫
        (smallEtalePushforward g A).map
          ((smallEtalePushforwardComp' a' b' (a' ≫ b') rfl A).hom.app F) =
      (smallEtalePushforwardComp' a' (g₁ ≫ b) (g₂ ≫ a ≫ b) hP A).hom.app F ≫
        (smallEtalePushforwardComp' (a' ≫ b') g (g₂ ≫ a ≫ b) hc A).inv.app F := by
    rw [← cancel_epi ((smallEtalePushforwardComp' b' g (g₁ ≫ b) hb A).hom.app
        ((smallEtalePushforward a' A).obj F)), Iso.hom_inv_id_app_assoc, ← reassoc_of% q₃]
    simp
  simp only [smallEtaleDirectImageSquare, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp]
  rw [e₁]
  simp only [Category.assoc]
  congr 2
  rw [reassoc_of% e₂, e₃, Iso.inv_hom_id_app_assoc]

variable (Λ : Type r) [Ring Λ]

include hab hab' ha hb in
/-- **Vertical pasting of the base change maps of sheaves of `Λ`-modules.** For two vertically
stacked commutative squares, with vertical composites `ab = a ≫ b` and `ab' = a' ≫ b'`, the base
change map `(ab)_* ⋙ g^{-1} ⟶ g₂^{-1} ⋙ (ab')_*` of the outer rectangle is the horizontal
composite of those of the two squares, read through the composition isomorphisms of the direct
images. -/
theorem etaleModuleBaseChange_vComp_app (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleBaseChangeGeneral.{u, r} Λ ab g g₂ ab' hc).app F =
      (etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleModuleDirectImageComp.{u, r} Λ a b ab hab).inv.app F) ≫
        (etaleModuleBaseChangeGeneral.{u, r} Λ b g g₁ b' hb).app
          ((etaleModuleDirectImage.{u, r} Λ a).obj F) ≫
        (etaleModuleDirectImage.{u, r} Λ b').map
          ((etaleModuleBaseChangeGeneral.{u, r} Λ a g₁ g₂ a' ha).app F) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a' b' ab' hab').hom.app
          ((etaleModuleInverseImage.{u, r} Λ g₂).obj F) := by
  let A₂ := etaleModuleInverseImageAdj.{u, r} Λ g₂
  let A₁ := etaleModuleInverseImageAdj.{u, r} Λ g₁
  let A₀ := etaleModuleInverseImageAdj.{u, r} Λ g
  let bca := (mateEquiv A₂ A₁).symm
    (smallEtaleDirectImageSquare a g₁ g₂ a' ha (ModuleCat.{max (u + 1) r} Λ))
  let bcb := (mateEquiv A₁ A₀).symm
    (smallEtaleDirectImageSquare b g g₁ b' hb (ModuleCat.{max (u + 1) r} Λ))
  let T := ((TwoSquare.hComp bca bcb).whiskerTop
    (etaleModuleDirectImageComp.{u, r} Λ a b ab hab).inv).whiskerBottom
      (etaleModuleDirectImageComp.{u, r} Λ a' b' ab' hab').hom
  have key : mateEquiv A₂ A₀ T =
      smallEtaleDirectImageSquare ab g g₂ ab' hc (ModuleCat.{max (u + 1) r} Λ) := by
    rw [Stacks.CategoryTheory.mateEquiv_whisker, mateEquiv_vcomp A₂ A₁ A₀]
    simp only [bca, bcb, Equiv.apply_symm_apply]
    exact (smallEtaleDirectImageSquare_vComp a b ab hab g g₁ g₂ a' b' ab' hab' ha hb hc _).symm
  have h : etaleModuleBaseChangeGeneral.{u, r} Λ ab g g₂ ab' hc = T.natTrans := by
    show ((mateEquiv A₂ A₀).symm _).natTrans = T.natTrans
    rw [← key, Equiv.symm_apply_apply]
  rw [h]
  simp only [T, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  rfl

end SheafPaste

/-! ### Vertical pasting of the derived base change maps -/

section DerivedPaste

section Fac

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The defining property of the derived base change map, with the exactness comparison of `g⁻¹`
moved to the other side. -/
@[reassoc]
theorem etaleModuleDerivedBaseChange_fac'
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) ≫
      (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' h).app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (ComplexShape.up ℤ)).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map
        ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K) := by
  rw [← etaleModuleDerivedBaseChange_fac_general.{u, r} Λ f g g' f' h K, Iso.hom_inv_id_app_assoc]

end Fac

variable {X Y Z X' Y' Z' : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (hab : ab = a ≫ b)
  (g : Z' ⟶ Z) (g₁ : Y' ⟶ Y) (g₂ : X' ⟶ X) (a' : X' ⟶ Y') (b' : Y' ⟶ Z') (ab' : X' ⟶ Z')
  (hab' : ab' = a' ≫ b') (ha : g₂ ≫ a = a' ≫ g₁) (hb : g₁ ≫ b = b' ≫ g)
  (hc : g₂ ≫ ab = ab' ≫ g)

include hab hab' ha hb in
/-- **Vertical pasting of the derived base change maps** on `D(-_étale, Λ)`. For two vertically
stacked commutative squares, with vertical composites `ab = a ≫ b` and `ab' = a' ≫ b'`, the
base change map `g⁻¹ R(ab)_* ⟶ R(ab')_* g₂⁻¹` of the outer rectangle is
```
g⁻¹ R(ab)_* ≅ g⁻¹ Rb_* Ra_* ⟶ Rb'_* g₁⁻¹ Ra_* ⟶ Rb'_* Ra'_* g₂⁻¹ ≅ R(ab')_* g₂⁻¹,
```
the composite of the base change maps of the two squares, read through the composition
isomorphisms of derived direct images (Tag 0D6E). -/
theorem etaleModuleDerivedBaseChange_vComp :
    etaleModuleDerivedBaseChangeGeneral.{u, r} Λ ab g g₂ ab' hc =
      Functor.whiskerRight
          (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ a b ab hab).hom
          (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a)
          (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ b g g₁ b' hb) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ a g₁ g₂ a' ha)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ b') ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g₂)
          (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ a' b' ab' hab').inv := by
  refine Functor.rightDerived_ext _
    (Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit
      (E' := etaleModuleInverseImage.{u, r} Λ g)
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ ab))
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  have hu₀ : (Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit
      (E' := etaleModuleInverseImage.{u, r} Λ g)
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ ab)).app K =
      (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ ab).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ ab).app K) := by
    have e₁ : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage.{u, r} Λ ab ⋙ etaleModuleInverseImage.{u, r} Λ g))
        (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by
      ext
      simp
    simp [Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit, e₁]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    hu₀, Category.assoc]
  congr 1
  have n₁ := (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ b g g₁ b' hb).naturality
    ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ a).app K)
  have n₂ := etaleModuleDerivedDirectImageUnboundedUnit_app_comp_map_Q_map.{u, r} Λ b'
    (K := ((etaleModuleInverseImage.{u, r} Λ g₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModuleDirectImage.{u, r} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (L := ((etaleModuleDirectImage.{u, r} Λ a').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModuleInverseImage.{u, r} Λ g₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ a g₁ g₂ a' ha)
      (ComplexShape.up ℤ)).app K)
  have n₃ :=
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ a' b' ab' hab').inv.naturality
      ((etaleModuleInverseImage.{u, r} Λ g₂).mapDerivedCategoryFactors.inv.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at n₁ n₃
  rw [etaleModuleDerivedBaseChange_fac', ← Functor.map_comp_assoc,
    etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% n₁,
    etaleModuleDerivedBaseChange_fac'_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, etaleModuleDerivedBaseChange_fac', Iso.inv_hom_id_app_assoc,
    Functor.map_comp_assoc, reassoc_of% n₂, Functor.map_comp, Category.assoc, n₃]
  rw [etaleModuleDerivedDirectImageUnboundedDerivedCompIso_inv_fac_app_assoc]
  have nf : (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).map (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ a b ab hab)
          (ComplexShape.up ℤ)).inv.app K)) ≫
      (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, r} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ ab).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((Functor.mapHomologicalComplexCompIso
            (etaleModuleDirectImageComp.{u, r} Λ a b ab hab) (ComplexShape.up ℤ)).inv.app K)) :=
    Functor.mapDerivedCategoryFactors_hom_naturality _ _
  rw [reassoc_of% nf]
  congr 1
  simp only [← DerivedCategory.Q.map_comp_assoc]
  congr 2
  ext n : 1
  simpa [etaleModuleDirectImageComp] using etaleModuleBaseChange_vComp_app.{u, r} a b ab hab g g₁ g₂
    a' b' ab' hab' ha hb hc Λ (K.X n)

end DerivedPaste

/-! ### Base change along identities -/

section Identity

/-- The comparison of the two composite direct images around a commutative square does not
depend on the name chosen for the common composite. -/
theorem smallEtalePushforwardComp'_hom_inv_congr {X₁ X₂ X₃ X₄ : Scheme.{u}} (f : X₁ ⟶ X₂)
    (g : X₂ ⟶ X₃) (f' : X₁ ⟶ X₄) (g' : X₄ ⟶ X₃) (fg₁ fg₂ : X₁ ⟶ X₃) (h₁ : fg₁ = f ≫ g)
    (h₂ : fg₂ = f ≫ g) (h₁' : fg₁ = f' ≫ g') (h₂' : fg₂ = f' ≫ g') (A : Type*) [Category* A] :
    (smallEtalePushforwardComp' f g fg₁ h₁ A).hom ≫
        (smallEtalePushforwardComp' f' g' fg₁ h₁' A).inv =
      (smallEtalePushforwardComp' f g fg₂ h₂ A).hom ≫
        (smallEtalePushforwardComp' f' g' fg₂ h₂' A).inv := by
  obtain rfl : fg₁ = fg₂ := h₁.trans h₂.symm
  rfl

variable {X X' : Scheme.{u}} (h' : X' ⟶ X)

/-- **The base change map of a square with identity horizontal arrows**, against the units of the
inverse images along the identities: `h'_*` of the unit `F ⟶ id_* id^{-1} F`, read through
`id_* ⋙ h'_* ≅ h'_*`, is the unit at `h'_* F` followed by `id_*` of the base change map and
`h'_* ⋙ id_* ≅ h'_*`. -/
theorem etaleModuleBaseChange_id_app (F : EtaleModules.{u, r} Λ X') (w : 𝟙 X' ≫ h' = h' ≫ 𝟙 X)
    (e₁ : h' = 𝟙 X' ≫ h') (e₂ : h' = h' ≫ 𝟙 X) :
    (etaleModuleDirectImage.{u, r} Λ h').map
        ((etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X')).unit.app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ (𝟙 X') h' h' e₁).hom.app
        ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F) =
    (etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X)).unit.app
        ((etaleModuleDirectImage.{u, r} Λ h').obj F) ≫
      (etaleModuleDirectImage.{u, r} Λ (𝟙 X)).map
        ((etaleModuleBaseChangeGeneral.{u, r} Λ h' (𝟙 X) (𝟙 X') h' w).app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ h' (𝟙 X) h' e₂).hom.app
        ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F) := by
  have hbc : (etaleModuleBaseChangeGeneral.{u, r} Λ h' (𝟙 X) (𝟙 X') h' w).app F =
      (etaleModuleInverseImage.{u, r} Λ (𝟙 X)).map ((etaleModuleDirectImage.{u, r} Λ h').map
          ((etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X')).unit.app F)) ≫
        (etaleModuleInverseImage.{u, r} Λ (𝟙 X)).map
          ((smallEtaleDirectImageSquare h' (𝟙 X) (𝟙 X') h' w (ModuleCat.{max (u + 1) r} Λ)).app
            ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F)) ≫
        (etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X)).counit.app _ := by
    simp [etaleModuleBaseChangeGeneral, mateEquiv]
  have hsq : smallEtaleDirectImageSquare h' (𝟙 X) (𝟙 X') h' w (ModuleCat.{max (u + 1) r} Λ) =
      (smallEtalePushforwardComp' (𝟙 X') h' h' e₁ _).hom ≫
        (smallEtalePushforwardComp' h' (𝟙 X) h' e₂ _).inv :=
    smallEtalePushforwardComp'_hom_inv_congr _ _ _ _ _ _ rfl e₁ w e₂ _
  rw [hsq] at hbc
  have nη := (etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X)).unit.naturality
    ((etaleModuleDirectImage.{u, r} Λ h').map
        ((etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X')).unit.app F) ≫
      (smallEtalePushforwardComp' (𝟙 X') h' h' e₁ _).hom.app
        ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F) ≫
      (smallEtalePushforwardComp' h' (𝟙 X) h' e₂ _).inv.app
        ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F))
  have tr := (etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X)).right_triangle_components
    ((etaleModuleDirectImage.{u, r} Λ h').obj ((etaleModuleInverseImage.{u, r} Λ (𝟙 X')).obj F))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at nη tr
  simp only [NatTrans.comp_app] at hbc
  rw [hbc, ← (etaleModuleInverseImage.{u, r} Λ (𝟙 X)).map_comp_assoc,
    (etaleModuleDirectImage.{u, r} Λ (𝟙 X)).map_comp, Category.assoc, ← reassoc_of% nη,
    reassoc_of% tr]
  simp [etaleModuleDirectImageComp]

end Identity

/-! ### The left unit law -/

section LeftUnit

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (hg : g = 𝟙 X ≫ g)

/-- **The left unit law for direct images.** The comparison `id_* ⋙ g_* ≅ g_*` is `g_*` of the
identification of the direct image along the identity with the identity functor. -/
theorem etaleModuleDirectImageComp_id_left_hom_app (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImageComp.{u, r} Λ (𝟙 X) g g hg).hom.app F =
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleDirectImageIdIso.{u, r} Λ X).hom.app F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  refine (etaleModuleDirectImageComp_hom_app_hom_app.{u, r} Λ (𝟙 X) g g hg F U).trans ?_
  refine (congrArg (fun z => F.obj.map (Opposite.op z))
    (smallEtaleBaseChangeComp'_id_left_hom_app (𝟙 X) rfl g hg U.unop)).trans ?_
  simp [etaleModuleDirectImageIdIso, smallEtaleBaseChangeIdOf]
  rfl

/-- The left unit law for direct images, inverted. -/
theorem etaleModuleDirectImageComp_id_left_inv_app (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImageComp.{u, r} Λ (𝟙 X) g g hg).inv.app F =
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleDirectImageIdIso.{u, r} Λ X).inv.app F) := by
  rw [← cancel_mono ((etaleModuleDirectImageComp.{u, r} Λ (𝟙 X) g g hg).hom.app F),
    Iso.inv_hom_id_app, etaleModuleDirectImageComp_id_left_hom_app, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  exact (CategoryTheory.Functor.map_id _ _).symm

/-- The derived direct image along the identity on a complex: the inverse of
`R(id)_* ≅ 𝟭` at `Q K` is the identification `K ≅ id_* K` followed by the derivation unit. -/
theorem etaleModuleDerivedDirectImageUnboundedIdIso_inv_app_Q
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedDirectImageUnboundedIdIso.{u, r} Λ X).inv.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv.app K ≫
          (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, r} Λ X)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 X)).app K := by
  have h' : (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 X)).app K ≫
      (etaleModuleDerivedDirectImageUnboundedIdIso.{u, r} Λ X).hom.app (DerivedCategory.Q.obj K) =
      (etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X).inv.app K :=
    (Functor.rightDerivedNatTrans_app _ _
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 X))
      (etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X).inv
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) (𝟙 _) K).trans
      (Category.id_comp _)
  have hι : DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv.app K ≫
      (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, r} Λ X)
        (ComplexShape.up ℤ)).inv.app K) =
      (etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X).hom.app K := by
    simp [etaleModuleDerivedDirectImageUnboundedIdFac]
  rw [hι, ← cancel_epi ((etaleModuleDerivedDirectImageUnboundedIdFac.{u, r} Λ X).inv.app K),
    Iso.inv_hom_id_app_assoc, ← h', Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The left unit law for the composition isomorphisms of derived direct images**:
`R(g)_* ≅ R(id)_* ⋙ Rg_*` is `Rg_*` of `𝟭 ≅ R(id)_*`. -/
theorem etaleModuleDerivedDirectImageUnboundedDerivedCompIso_id_left :
    (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, r} Λ (𝟙 X) g g hg).hom =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedIdIso.{u, r} Λ X).inv
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) := by
  refine Functor.rightDerived_ext _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp]
  rw [etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app,
    etaleModuleDerivedDirectImageUnboundedIdIso_inv_app_Q, Functor.map_comp]
  rw [reassoc_of% etaleModuleDerivedDirectImageUnboundedUnit_app_comp_map_Q_map]
  congr 2
  ext n : 1
  simp [etaleModuleDirectImageComp_id_left_inv_app]
end LeftUnit

end Stacks.EtaleCohomology

end
