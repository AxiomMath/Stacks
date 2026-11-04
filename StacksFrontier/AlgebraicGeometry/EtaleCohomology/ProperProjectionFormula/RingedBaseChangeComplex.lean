module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSquareBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangeUnbounded

/-!
# The étale and ringed degreewise base change maps followed by the unit, compared

For a commutative square of schemes `g' ≫ f = f' ≫ g`, the localized degreewise base change map
followed by the derived-functor unit of `Rf'_*` is invertible at a complex exactly when the
degreewise base change map followed by `f'_*` of a K-injective resolution is a quasi-isomorphism.
This holds on the side of sheaves of `Λ`-modules and on the side of the constant ringed topoi, and
the identifications `Ψ = etaleRingedForget Λ _` carry the second degreewise map to the first
(`Stacks.EtaleCohomology.etaleModuleBaseChange_etaleRingedForget`). So invertibility on the étale
side gives invertibility on the ringed side.

## Main results

* `Stacks.EtaleCohomology.isIso_degreewise_comp_unit_iff_quasiIso`: the étale criterion.
* `Stacks.EtaleCohomology.quasiIso_of_quasiIso_etaleRingedForget_map`: `Ψ` reflects
  quasi-isomorphisms.
* `Stacks.EtaleCohomology.isIso_etaleRingedBaseChangeUnitComposite_of_isIso`: invertibility of the
  étale composite at `Ψ I` gives invertibility of the ringed composite at `I`.

## Implementation notes

The comparison is first proved for functors that are variables
(`quasiIso_of_quasiIso_transport`), then instantiated. The étale base change map is made an opaque
variable `β` before anything is instantiated: with it written out, the kernel unfolds it while
comparing the two spellings of the zero morphisms of sheaves of `Λ`-modules, and times out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance high] instHasSheafifyCRingedToposEtaleRingedSiteJType
attribute [local instance] etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- **On sheaves of `Λ`-modules, the localized degreewise base change map followed by the unit is
invertible exactly when the degreewise base change map followed by `f'_*` of a K-injective
resolution is a quasi-isomorphism.** It is stated for an arbitrary transformation `β` in place of
the étale base change map, so that the latter can be kept opaque. -/
theorem isIso_degreewise_comp_unit_iff_quasiIso
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (J : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    {T : CochainComplex (EtaleModules.{u, r} Λ X') ℤ}
    (t : ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj J ⟶
      T)
    [QuasiIso t] (hT : T.IsKInjective) :
    IsIso (DerivedCategory.Q.map ((((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex β _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
          (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
          (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
          CochainComplex (EtaleModules.{u, r} Λ Y') ℤ))).app J) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ↔
    QuasiIso ((((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex β _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
          (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
          (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
          CochainComplex (EtaleModules.{u, r} Λ Y') ℤ))).app J ≫
      ((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  have : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).2 inferInstance
  have : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app T) :=
    Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective DerivedCategory.Q _ _
      (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
        (etaleModuleDirectImage.{u, r} Λ f')) T hT
  rw [Stacks.CategoryTheory.isIso_map_comp_app_iff
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f') _ t,
    DerivedCategory.isIso_Q_map_iff_quasiIso]

/-- `Ψ` reflects quasi-isomorphisms of complexes of sheaves of `Λ̲`-modules. -/
theorem quasiIso_of_quasiIso_etaleRingedForget_map {Z : Scheme.{u}}
    {K L : CochainComplex (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Z)).O)) ℤ} (φ : K ⟶ L)
    (h : QuasiIso
      (((etaleRingedForget.{u, r} Λ Z).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ :=
  (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ _).1 h

/-- The direct image of sheaves of modules along the morphism of constant ringed topoi is additive,
being a right adjoint. -/
local instance etaleRingedToposHom_pushforwardModules_additive {Z Z' : Scheme.{u}} (h : Z ⟶ Z') :
    (etaleRingedToposHom.{u, r} Λ h).pushforwardModules.Additive :=
  (RingedToposHom.pullbackAdjPushforwardModules
    (etaleRingedToposHom.{u, r} Λ h)).right_adjoint_additive


/-- **Transport of the quasi-isomorphism property along comparisons, over variables.** Two
squares of functors on abelian categories, related by comparisons `Ψ` and isomorphisms `cmpg`,
`cf`, `cmpg'`, `cf'`, carry degreewise base change maps `bcr` and `bcv` identified through the
comparisons (`H`). Then for a complex `I`, a map `s' : (g')^* I ⟶ T'` and complex maps `x`, `y`,
`t` with the expected components, `y ≫ f'_* t` a quasi-isomorphism makes `x ≫ f'_* s'` one,
provided `Ψ_{Y'}` preserves homology and reflects isomorphisms. -/
private theorem quasiIso_of_quasiIso_transport.{wR, vR, wV, vV}
    {RX RX' RY RY' : Type wR} {VX VX' VY VY' : Type wV} {_ : Category.{vR} RX}
    {_ : Category.{vR} RX'} {_ : Category.{vR} RY} {_ : Category.{vR} RY'} {_ : Category.{vV} VX}
    {_ : Category.{vV} VX'} {_ : Category.{vV} VY} {_ : Category.{vV} VY'}
    {_ : Preadditive RX} {_ : Preadditive RX'} {_ : Preadditive RY} {_ : Preadditive RY'}
    [Preadditive VX] [Preadditive VX'] [Preadditive VY] [Preadditive VY']
    [CategoryWithHomology RY'] [CategoryWithHomology VY']
    (ΨX : RX ⥤ VX) (ΨX' : RX' ⥤ VX') (ΨY : RY ⥤ VY) (ΨY' : RY' ⥤ VY')
    (qf : RX ⥤ RY) (pg : RY ⥤ RY') (pg' : RX ⥤ RX') (qf' : RX' ⥤ RY')
    (Rf : VX ⥤ VY) (Pg : VY ⥤ VY') (Pg' : VX ⥤ VX') (Rf' : VX' ⥤ VY')
    [ΨX.Additive] [ΨX'.Additive]
    {_ : qf.PreservesZeroMorphisms} {_ : pg.PreservesZeroMorphisms}
    {_ : pg'.PreservesZeroMorphisms} {_ : qf'.PreservesZeroMorphisms}
    [Rf.Additive] [Pg.Additive] [Pg'.Additive] [Rf'.Additive]
    {_ : ΨY'.PreservesZeroMorphisms}
    (cmpg : ΨY ⋙ Pg ≅ pg ⋙ ΨY') (cf : qf ⋙ ΨY ≅ ΨX ⋙ Rf) (cmpg' : ΨX ⋙ Pg' ≅ pg' ⋙ ΨX')
    (cf' : qf' ⋙ ΨY' ≅ ΨX' ⋙ Rf')
    (bcr : qf ⋙ pg ⟶ pg' ⋙ qf') (bcv : Rf ⋙ Pg ⟶ Pg' ⋙ Rf')
    (b : ∀ M, pg.obj (qf.obj M) ⟶ qf'.obj (pg'.obj M)) (he : ∀ M, bcr.app M = b M)
    (hA : ∀ M, Pg.map (cf.hom.app M) ≫ bcv.app (ΨX.obj M) ≫ Rf'.map (cmpg'.hom.app M) =
      cmpg.hom.app (qf.obj M) ≫ ΨY'.map (b M) ≫ cf'.hom.app (pg'.obj M))
    (I : CochainComplex RX ℤ) {T' : CochainComplex RX' ℤ}
    (s' : (pg'.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T')
    (x : (pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((qf.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (qf'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((pg'.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (hx : ∀ n, x.f n = bcr.app (I.X n))
    (t : (Pg'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ΨX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      (ΨX'.mapHomologicalComplex (ComplexShape.up ℤ)).obj T')
    (ht : ∀ n, t.f n = cmpg'.hom.app (I.X n) ≫ ΨX'.map (s'.f n))
    (hΨ : QuasiIso ((ΨY'.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (x ≫ (qf'.mapHomologicalComplex (ComplexShape.up ℤ)).map s')) →
      QuasiIso (x ≫ (qf'.mapHomologicalComplex (ComplexShape.up ℤ)).map s'))
    (hV : QuasiIso ((((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex bcv _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      (Rf.mapHomologicalComplex _ ⋙ Pg.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ) ⟶
      (Pg'.mapHomologicalComplex _ ⋙ Rf'.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ))).app
          ((ΨX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (Rf'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)) :
    QuasiIso (x ≫ (qf'.mapHomologicalComplex (ComplexShape.up ℤ)).map s') := by
  have H : ∀ M, Pg.map (cf.hom.app M) ≫ bcv.app (ΨX.obj M) ≫ Rf'.map (cmpg'.hom.app M) =
      cmpg.hom.app (qf.obj M) ≫ ΨY'.map (bcr.app M) ≫ cf'.hom.app (pg'.obj M) := fun M => by
    rw [he]
    exact hA M
  set y := (((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex bcv _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      (Rf.mapHomologicalComplex _ ⋙ Pg.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ) ⟶
      (Pg'.mapHomologicalComplex _ ⋙ Rf'.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ))).app
          ((ΨX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) with hydef
  have hy : ∀ n, y.f n = bcv.app (((ΨX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X n) := by
    intro n
    rw [hydef]
    simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f]
    exact (Category.id_comp _).trans (Category.comp_id _)
  refine hΨ ?_
  let Lc : (ΨY'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((qf.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ⟶
      (Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Rf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ΨX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    { f := fun n => cmpg.inv.app (qf.obj (I.X n)) ≫ Pg.map (cf.hom.app (I.X n))
      comm' := fun i j _ => by
        have h1 := cmpg.inv.naturality (qf.map (I.d i j))
        have h2 := cf.hom.naturality (I.d i j)
        dsimp at h1 h2 ⊢
        rw [Category.assoc, ← Pg.map_comp, ← h2, Pg.map_comp, reassoc_of% h1] }
  let Rc : (ΨY'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((qf'.mapHomologicalComplex (ComplexShape.up ℤ)).obj T') ⟶
      (Rf'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ΨX'.mapHomologicalComplex (ComplexShape.up ℤ)).obj T') :=
    { f := fun n => cf'.hom.app (T'.X n)
      comm' := fun i j _ => (cf'.hom.naturality (T'.d i j)).symm }
  have : ∀ n, IsIso (Lc.f n) := fun n => by dsimp [Lc]; infer_instance
  have : IsIso Lc := HomologicalComplex.Hom.isIso_of_components Lc
  have : ∀ n, IsIso (Rc.f n) := fun n => by dsimp [Rc]; infer_instance
  have : IsIso Rc := HomologicalComplex.Hom.isIso_of_components Rc
  have key : Lc ≫ (y ≫ (Rf'.mapHomologicalComplex (ComplexShape.up ℤ)).map t) =
      (ΨY'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (x ≫ (qf'.mapHomologicalComplex (ComplexShape.up ℤ)).map s') ≫ Rc := by
    ext n : 1
    have hn := cf'.hom.naturality (s'.f n)
    dsimp at hn
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_obj_X, hx, hy, ht, Lc, Rc, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (H (I.X n)), Iso.inv_hom_id_app_assoc, ← hn]
  rw [← quasiIso_iff_comp_right _ Rc, ← key, quasiIso_iff_comp_left]
  exact hV

/-- **Invertibility on the étale side gives invertibility on the ringed side.** For a complex `I`
of sheaves of `Λ̲`-modules on `X_étale`, if the localized étale degreewise base change map at
`Ψ I`, followed by the derived-functor unit of `Rf'_*`, is invertible, then so is the localized
module base change map of the square of constant ringed topoi at `I`, followed by the unit. -/
theorem isIso_etaleRingedBaseChangeUnitComposite_of_isIso
    (I : CochainComplex (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O)) ℤ)
    (hα : IsIso (DerivedCategory.Q.map
        ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w).app
          (((etaleRingedForget.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleRingedForget.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) :
    IsIso (etaleRingedBaseChangeUnitComposite Λ f g f' g' w I) := by
  have hA := etaleModuleBaseChange_etaleRingedForget.{u, r} Λ f g f' g' w
  have e : etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w =
      (((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex (etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm) _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
          (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
          (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
          CochainComplex (EtaleModules.{u, r} Λ Y') ℤ))) := rfl
  rw [e] at hα
  obtain ⟨β, hβ⟩ : ∃ β, β = etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm := ⟨_, rfl⟩
  rw [← hβ] at hα hA
  obtain ⟨T', s', hT', hs'⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _
      (((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
  refine
    (Cohomology.ProjectionFormulaOfToposHom.isIso_moduleBaseChangeComplex_comp_unit_iff_quasiIso
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) I s' hT').2 ?_
  obtain ⟨tc, htc⟩ : ∃ tc : ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((etaleRingedForget.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      ((etaleRingedForget.{u, r} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I),
      ∀ n, tc.f n = (etaleRingedPullbackComparison.{u, r} Λ g').hom.app (I.X n) :=
    ⟨{ f := fun n => (etaleRingedPullbackComparison.{u, r} Λ g').hom.app (I.X n),
        comm' := fun i j _ => ((etaleRingedPullbackComparison.{u, r} Λ g').hom.naturality
          (I.d i j)).symm }, fun _ => rfl⟩
  have : ∀ n, IsIso (tc.f n) := fun n => by rw [htc]; infer_instance
  have : IsIso tc := HomologicalComplex.Hom.isIso_of_components tc
  have hT : CochainComplex.IsKInjective
      (((etaleRingedForget.{u, r} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).obj T') :=
    have := hT'
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ T'
  have hV := (isIso_degreewise_comp_unit_iff_quasiIso.{u, r} Λ f g f' g' β
    (((etaleRingedForget.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (tc ≫ ((etaleRingedForget.{u, r} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map s')
      hT).1 hα
  refine quasiIso_of_quasiIso_transport.{max (r + 1) (u + 2), max r (u + 1),
      max (r + 1) (u + 2), max r (u + 1)}
    (etaleRingedForget.{u, r} Λ X) (etaleRingedForget.{u, r} Λ X')
    (etaleRingedForget.{u, r} Λ Y) (etaleRingedForget.{u, r} Λ Y')
    _ _ _ _ _ _ _ _
    (etaleRingedPullbackComparison.{u, r} Λ g) (etaleRingedPushforwardComparison.{u, r} Λ f)
    (etaleRingedPullbackComparison.{u, r} Λ g') (etaleRingedPushforwardComparison.{u, r} Λ f')
    (RingedToposHom.TwoIso.moduleBaseChange.{max r (u + 1)}
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w))
    β
    (fun M => Stacks.CategoryTheory.BaseChange.map
      (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
      (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
      (RingedToposHom.TwoIso.squarePullbackIso
        (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X')))
        (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X)))
        (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y')))
        (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y)))
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) M)
    ?_ ?_ I s'
    (RingedToposHom.TwoIso.moduleBaseChangeComplex
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) I)
    ?_
    (tc ≫ ((etaleRingedForget.{u, r} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map s')
    ?_ (quasiIso_of_quasiIso_etaleRingedForget_map.{u, r} Λ _) hV
  · intro M
    simp only [RingedToposHom.TwoIso.moduleBaseChange, Stacks.CategoryTheory.BaseChange.map,
      Stacks.CategoryTheory.BaseChange.twoSquare,
      Stacks.CategoryTheory.BaseChange.pullbackComparison,
      Iso.refl_inv, Category.comp_id]
  · exact hA
  · intro n
    simp only [RingedToposHom.TwoIso.moduleBaseChangeComplex_f]
  · intro n
    rw [HomologicalComplex.comp_f, htc, Functor.mapHomologicalComplex_map_f]

end Stacks.EtaleCohomology

end
