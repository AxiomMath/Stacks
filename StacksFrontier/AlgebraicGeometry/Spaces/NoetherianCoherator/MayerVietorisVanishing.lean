module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections

/-!
# Vanishing of higher direct images across an elementary distinguished square

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square of algebraic spaces with
intersection `P = U ×_W V`, and let `f : W ⟶ Z` be a morphism of algebraic spaces.  Write
`a = f|_U`, `b = f|_V` and `c = f|_P`.  The relative Mayer–Vietoris triangle of Stacks 08JK,

`Rf_*G ⟶ Ra_*(G|_U) ⊕ Rb_*(G|_V) ⟶ Rc_*(G|_P) ⟶ (Rf_*G)[1]`,

gives the exact segment `R^p c_*(G|_P) ⟶ R^{p+1} f_*G ⟶ R^{p+1} a_*(G|_U) ⊕ R^{p+1} b_*(G|_V)`
of its long exact cohomology sequence, so that `R^{p+1} f_*G` vanishes as soon as the two outer
terms do.  This is the inductive step by which a bound on the cohomological degree of the higher
direct images is propagated along the induction principle of Stacks 08GP.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_succ_of_eds`: the vanishing of `R^{p+1} f_*G`
  from that of `R^p c_*(G|_P)`, `R^{p+1} a_*(G|_U)` and `R^{p+1} b_*(G|_V)`.

## Implementation notes

The triangle is taken at the module `G` placed in degree `0`, for the chosen total right
derived functors of the four composites, in the standard model of the derived category; the
cohomology of those derived functors at a module placed in degree `0` is identified with the
classical right derived functors by
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, and restriction along an étale
morphism is pulled out of the classical derived functors by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, restriction being exact and
preserving injective objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback
  isGrothendieckAbelian_modules enoughInjectives_modules hasInjectiveResolutions_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `n`-th cohomology of the chosen total right derived functor of an additive functor out
of the modules of an algebraic space, at a module placed in degree `0`, is its `n`-th classical
right derived functor. -/
def homologyTotalRightDerivedSingleModulesIso {X Z : AlgebraicSpaces B S hS}
    (Φ : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2) [Φ.Additive]
    (G : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS Φ
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) n).obj
        (((Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Φ.rightDerived n).obj G :=
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS Φ
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso Φ _
    ((Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) G 0 n n (by omega)

/-- The classical right derived functors of `g_* ∘ (-)|_Y` are those of `g_*` applied after the
restriction `(-)|_Y` along an étale morphism, restriction being exact and preserving injective
objects. -/
def rightDerivedRestrictPushforwardIso {X Y Z : AlgebraicSpaces B S hS} (i : Y ⟶ X)
    (hi : IsEtale B S hS i.hom) (g : Y ⟶ Z) (G : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    ((etaleModulePullback.{u, u} B S hS i hi ⋙ modulePushforward B S hS g).rightDerived n).obj G ≅
      ((modulePushforward B S hS g).rightDerived n).obj
        ((etaleModulePullback.{u, u} B S hS i hi).obj G) :=
  have := preservesInjectiveObjects_etaleModulePullback B S hS i hi
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
    (etaleModulePullback.{u, u} B S hS i hi) (modulePushforward B S hS g) n).app G

/-- An additive functor carries a biproduct of two objects with zero images to a zero object. -/
theorem _root_.CategoryTheory.Functor.isZero_obj_biprod_of_isZero {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C}
    [HasBinaryBiproduct A B] (hA : IsZero (F.obj A)) (hB : IsZero (F.obj B)) :
    IsZero (F.obj (A ⊞ B)) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hA.eq_of_src (F.map biprod.inl) 0, hB.eq_of_src (F.map biprod.inr) 0, comp_zero, comp_zero,
    add_zero]

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {Z : AlgebraicSpaces B S hS} (f : W ⟶ Z)

/-- **The inductive step of a higher-direct-image bound across an elementary distinguished
square.**  For `f : W ⟶ Z` and a module `G` on `W`, `R^{p+1} f_*G` vanishes as soon as
`R^p c_*(G|_P)`, `R^{p+1} a_*(G|_U)` and `R^{p+1} b_*(G|_V)` do, where `a`, `b`, `c` are the
restrictions of `f` to the open subspace, the étale member and the intersection of the square.

This is the exact segment `R^p c_* ⟶ R^{p+1} f_* ⟶ R^{p+1} a_* ⊕ R^{p+1} b_*` of the long exact
cohomology sequence of the relative Mayer–Vietoris triangle of Stacks 08JK, at `G` placed in
degree `0`. -/
theorem isZero_rightDerived_succ_of_eds (G : Modules.{u, u} B S hS W.1 W.2) (p : ℕ)
    (hU : IsZero (((modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).rightDerived (p + 1)).obj
        ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj G)))
    (hV : IsZero (((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).rightDerived
          (p + 1)).obj
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj G)))
    (hP : IsZero (((modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).rightDerived p).obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj G))) :
    IsZero (((modulePushforward B S hS f).rightDerived (p + 1)).obj G) := by
  let ΦX := modulePushforward B S hS f
  let ΦU := etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) ⋙ modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)
  let ΦV := etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) ⋙ modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)
  let ΦP := etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq) ⋙ modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)
  let WW := HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS ΦX
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS ΦU
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS ΦV
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS ΦP
  let RX := (ΦX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh WW
  let RU := (ΦU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh WW
  let RV := (ΦV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh WW
  let RP := (ΦP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh WW
  let E := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS W.1 W.2) 0).obj G
  obtain ⟨fU, fV, gU, gV, δ, hT⟩ :=
    exists_mem_distTriang_edsRelativeMayerVietoris_unconditional B S hS hsq f RX RU RV RP
      ((ΦX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
        DerivedCategory.Qh WW)
      ((ΦU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
        DerivedCategory.Qh WW)
      ((ΦV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
        DerivedCategory.Qh WW)
      ((ΦP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
        DerivedCategory.Qh WW)
      inferInstance inferInstance inferInstance inferInstance E
  let H := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2) 0
  have hex := H.homologySequence_exact₁ _ hT (p : ℤ) ((p + 1 : ℕ) : ℤ) (by push_cast; ring)
  have h₁ : IsZero ((H.shift (p : ℤ)).obj (RP.obj E)) :=
    hP.of_iso (homologyTotalRightDerivedSingleModulesIso B S hS ΦP G p ≪≫
      rightDerivedRestrictPushforwardIso B S hS _ _ _ G p)
  have hUz : IsZero ((H.shift ((p + 1 : ℕ) : ℤ)).obj (RU.obj E)) :=
    hU.of_iso (homologyTotalRightDerivedSingleModulesIso B S hS ΦU G (p + 1) ≪≫
      rightDerivedRestrictPushforwardIso B S hS _ _ _ G (p + 1))
  have hVz : IsZero ((H.shift ((p + 1 : ℕ) : ℤ)).obj (RV.obj E)) :=
    hV.of_iso (homologyTotalRightDerivedSingleModulesIso B S hS ΦV G (p + 1) ≪≫
      rightDerivedRestrictPushforwardIso B S hS _ _ _ G (p + 1))
  have h₃ : IsZero ((H.shift ((p + 1 : ℕ) : ℤ)).obj (RU.obj E ⊞ RV.obj E)) :=
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Z.1 Z.2)
      ((p + 1 : ℕ) : ℤ)).isZero_obj_biprod_of_isZero hUz hVz
  have h₂ := hex.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  exact h₂.of_iso (homologyTotalRightDerivedSingleModulesIso B S hS ΦX G (p + 1)).symm

end Square

end AlgebraicGeometry.Space

end
