module

public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposPushforwardSingleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionUnitConjugate

/-!
# The map `(f_*F)[0] ⟶ Rf_*(F[0])` along a composite of algebraic spaces

Let `t : X₀ ⟶ X₁` and `i₁ : X₁ ⟶ X` be morphisms of algebraic spaces and `i₀ = t ≫ i₁`. The
derived direct images compose by the map `c : Rt_* ⋙ Ri₁,* ⟶ Ri₀,*` conjugate, under the
derived adjunctions, to the inverse of the composition law `Li₁^* ⋙ Lt^* ≅ Li₀^*` of derived
pullbacks (Stacks 0D6D). This file proves that the canonical maps `(f_*F)[0] ⟶ Rf_*(F[0])`
of `t`, `i₁` and `i₀` are compatible with `c` and with the composition isomorphism
`t_* ⋙ i₁,* ≅ i₀,*` of direct images of modules (Stacks 03LU).

## Main results

* `Stacks.DerivedFunctor.compUnit_comp_of_eq`: transport of the compatibility of three units
  with a composition map along equalities of the underived functors.
* `Stacks.DerivedFunctor.singleDerivedUnit_comp_of_eq`: the same for the maps
  `w(X)[0] ⟶ Rw(X[0])`.
* `AlgebraicGeometry.Space.modulePushforwardSingleToDerived_comp`: the compatibility of the maps
  `(f_*F)[0] ⟶ Rf_*(F[0])` with composition.

## Implementation notes

Every statement is over variable spaces and morphisms, so that its instances in a fixed
situation are elaborated against these statements and nothing is unfolded there. The concrete
proof only instantiates abstract lemmas: the identities between the site and ringed-topos
spellings are crossed as equalities of functors and natural transformations, and the remaining
manipulations (`Stacks.DerivedFunctor.singleUnit_app`,
`Stacks.DerivedFunctor.map_trans_eqToIso_hom_comp_of_inv_comp`) are proved for arbitrary data.
Rewriting with generic lemmas such as `Category.comp_id` directly in the concrete goal is
expensive: each candidate subterm is unfolded while matching.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)


namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB wC vC uC

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- If `Φ(i⁻¹) ≫ x = y` for an isomorphism `i`, then `Φ((i ≪≫ eqToIso p).hom) ≫ y = x`. -/
theorem map_trans_eqToIso_hom_comp_of_inv_comp {D E : Type*} [Category* D] [Category* E]
    (Φ : D ⥤ E) {a b : D} (i : a ≅ b) (p : b = b) {z : E} (x : Φ.obj a ⟶ z) (y : Φ.obj b ⟶ z)
    (h : Φ.map i.inv ≫ x = y) : Φ.map ((i ≪≫ eqToIso p).hom) ≫ y = x := by
  subst h
  rw [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- `Stacks.DerivedFunctor.singleUnit` at an object is `Stacks.DerivedFunctor.singleDerivedUnit`.
-/
theorem singleUnit_app (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw) (X : A) :
    (singleUnit w Rw α).app X = singleDerivedUnit w Rw α X :=
  rfl

/-- **Compatibility of three units with a composition map, transported along equalities of
functors.** Let `F' ⋙ G' ≅ H'` and `F ⋙ G ≅ H` be composition isomorphisms of additive functors
with `F' = F`, `G' = G`, `H' = H`, the second being the first read through these equalities, and
let the units `αF`, `αG`, `αH` of right derived functors of `F`, `G`, `H` be the units `αF'`,
`αG'`, `αH'` of `F'`, `G'`, `H'` read through the induced equalities on homotopy categories. If
the units of `F'`, `G'`, `H'` are compatible with `Dpf : RF ⋙ RG ≅ RH`, so are those of
`F`, `G`, `H`. -/
theorem compUnit_comp_of_eq {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : A ⥤ C}
    [hFa : F.Additive] [hF'a : F'.Additive] [hGa : G.Additive] [hG'a : G'.Additive]
    [hHa : H.Additive] [hH'a : H'.Additive]
    (hF : F' = F) (hG : G' = G) (hH : H' = H)
    (e' : F' ⋙ G' ≅ H') (e : F ⋙ G ≅ H) (hc : F ⋙ G = F' ⋙ G')
    (he : e = eqToIso hc ≪≫ e' ≪≫ eqToIso hH)
    {RF : DerivedCategory A ⥤ DerivedCategory B} {RG : DerivedCategory B ⥤ DerivedCategory C}
    {RH : DerivedCategory A ⥤ DerivedCategory C} (Dpf : RF ⋙ RG ≅ RH)
    (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG' : G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH' : H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (hqF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hqG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hqH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hαF : αF = eqToHom hqF ≫ αF') (hαG : αG = eqToHom hqG ≫ αG')
    (hαH : αH = eqToHom hqH ≫ αH')
    (hU' : ∀ K, (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e' (ComplexShape.up ℤ)).inv.app K) ≫
      αG'.app ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ RG.map (αF'.app K)) ≫
        Dpf.hom.app (DerivedCategory.Qh.obj K) = αH'.app K)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
      αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ RG.map (αF.app K)) ≫
        Dpf.hom.app (DerivedCategory.Qh.obj K) = αH.app K := by
  subst hF hG hH hαF hαG hαH he
  simpa using hU' K

/-- **The canonical maps `w(X)[0] ⟶ Rw(X[0])` along a composite, transported along equalities
of functors.** In the situation of `Stacks.DerivedFunctor.compUnit_comp_of_eq`, the maps
`w(X)[0] ⟶ Rw(X[0])` (`Stacks.DerivedFunctor.singleDerivedUnit`) of `F`, `G` and `H` are
compatible with `e` and `Dpf`. -/
theorem singleDerivedUnit_comp_of_eq {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : A ⥤ C}
    [hFa : F.Additive] [hF'a : F'.Additive] [hGa : G.Additive] [hG'a : G'.Additive]
    [hHa : H.Additive] [hH'a : H'.Additive]
    (hF : F' = F) (hG : G' = G) (hH : H' = H)
    (e' : F' ⋙ G' ≅ H') (e : F ⋙ G ≅ H) (hc : F ⋙ G = F' ⋙ G')
    (he : e = eqToIso hc ≪≫ e' ≪≫ eqToIso hH)
    {RF : DerivedCategory A ⥤ DerivedCategory B} {RG : DerivedCategory B ⥤ DerivedCategory C}
    {RH : DerivedCategory A ⥤ DerivedCategory C} (Dpf : RF ⋙ RG ≅ RH)
    (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG' : G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH' : H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (hqF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hqG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hqH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      H'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hαF : αF = eqToHom hqF ≫ αF') (hαG : αG = eqToHom hqG ≫ αG')
    (hαH : αH = eqToHom hqH ≫ αH')
    (hU' : ∀ K, (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e' (ComplexShape.up ℤ)).inv.app K) ≫
      αG'.app ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ RG.map (αF'.app K)) ≫
        Dpf.hom.app (DerivedCategory.Qh.obj K) = αH'.app K)
    (M : A) :
    (DerivedCategory.singleFunctor C 0).map (e.inv.app M) ≫ singleDerivedUnit G RG αG (F.obj M) ≫
        RG.map (singleDerivedUnit F RF αF M) ≫
          Dpf.hom.app ((DerivedCategory.singleFunctor A 0).obj M) =
      singleDerivedUnit H RH αH M :=
  singleDerivedUnit_comp F G H e RG αG RF αF RH αH Dpf
    (compUnit_comp_of_eq hF hG hH e' e hc he Dpf αF' αG' αH' αF αG αH hqF hqG hqH hαF hαG hαH
      hU') M

end Stacks.DerivedFunctor

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] SheafOfModules.hasDerivedCategory
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X₁ X₀ : AlgebraicSpaces B S hS}

/-- **The canonical maps `(f_*F)[0] ⟶ Rf_*(F[0])` are compatible with composition.** For
morphisms `t : X₀ ⟶ X₁`, `i₁ : X₁ ⟶ X` and `i₀ = t ≫ i₁` of algebraic spaces and a module `F` on
`X₀`, the composition isomorphism `i₁,*t_*F ≅ i₀,*F` placed in degree `0`, followed by the map of
`i₀`, is the map of `i₁` at `t_*F`, then `Ri₁,*` of the map of `t` at `F`, then the composition
map `Ri₁,*Rt_* ⟶ Ri₀,*` conjugate to the inverse of `Li₁^* ⋙ Lt^* ≅ Li₀^*` (Stacks 0D6D). -/
theorem modulePushforwardSingleToDerived_comp (t : X₀ ⟶ X₁) (i₁ : X₁ ⟶ X) (i₀ : X₀ ⟶ X)
    (hi : t ≫ i₁ = i₀) (F : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (DerivedCategory.singleFunctor _ 0).map
        ((modulePushforwardCompIso B S hS t i₁).app F ≪≫
          eqToIso (congrArg (fun φ => (modulePushforward B S hS φ).obj F) hi)).hom ≫
        (modulePushforwardSingleToDerived B S hS i₀).app F =
      (modulePushforwardSingleToDerived B S hS i₁).app ((modulePushforward B S hS t).obj F) ≫
        (derivedModulePushforward B S hS i₁).map
          ((modulePushforwardSingleToDerived B S hS t).app F) ≫
        (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS i₁).comp
            (smallEtaleDerivedModuleAdjunction B S hS t))
          (smallEtaleDerivedModuleAdjunction B S hS i₀)
          (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hi).inv).app
          ((DerivedCategory.singleFunctor _ 0).obj F) := by
  subst hi
  have hU' :=
    Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.compUnit_comp_conjugateEquiv_app
      (X := smallEtaleRingedTopos B S hS X₀) (Y := smallEtaleRingedTopos B S hS X₁)
      (Z := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS t)
      (smallEtaleRingedToposHom B S hS i₁) (smallEtaleRingedToposHom B S hS (t ≫ i₁))
      (pushforwardModulesCompTransport B S hS t i₁) (pullbackModulesCompTransport B S hS t i₁)
      rfl
  have key := Stacks.DerivedFunctor.singleDerivedUnit_comp_of_eq.{u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1, u + 1} (A := Modules.{u, u} B S hS X₀.1 X₀.2)
    (B := Modules.{u, u} B S hS X₁.1 X₁.2) (C := Modules.{u, u} B S hS X.1 X.2)
    (hFa := modulePushforward_additive B S hS t) (hGa := modulePushforward_additive B S hS i₁)
    (hHa := modulePushforward_additive B S hS (t ≫ i₁))
    (hF'a := additive_smallEtaleRingedToposHom_pushforwardModules B S hS t)
    (hG'a := additive_smallEtaleRingedToposHom_pushforwardModules B S hS i₁)
    (hH'a := additive_smallEtaleRingedToposHom_pushforwardModules B S hS (t ≫ i₁))
    (pushforwardModules_eq_modulePushforward B S hS t)
    (pushforwardModules_eq_modulePushforward B S hS i₁)
    (pushforwardModules_eq_modulePushforward B S hS (t ≫ i₁))
    ((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS t)
      (smallEtaleRingedToposHom B S hS i₁)).symm ≪≫ pushforwardModulesCompTransport B S hS t i₁)
    (modulePushforwardCompIso B S hS t i₁) (modulePushforward_comp_eq B S hS t i₁)
    (congrArg (eqToIso (modulePushforward_comp_eq B S hS t i₁) ≪≫ ·)
      (Iso.trans_assoc _ _ _).symm)
    ((conjugateIsoEquiv (smallEtaleDerivedModuleAdjunction B S hS (t ≫ i₁))
      ((smallEtaleDerivedModuleAdjunction B S hS i₁).comp
        (smallEtaleDerivedModuleAdjunction B S hS t))
      (smallEtaleDerivedModulePullbackCompIso B S hS t i₁)).symm)
    _ _ _ (derivedModulePushforwardUnit B S hS t) (derivedModulePushforwardUnit B S hS i₁)
    (derivedModulePushforwardUnit B S hS (t ≫ i₁))
    (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS t)
    (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS i₁)
    (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS (t ≫ i₁)) rfl rfl rfl hU' F
  have hσ : ∀ {Y₁ Y₂ : AlgebraicSpaces B S hS} (f : Y₁ ⟶ Y₂) (M : Modules.{u, u} B S hS Y₁.1 Y₁.2),
      (modulePushforwardSingleToDerived B S hS f).app M =
        Stacks.DerivedFunctor.singleDerivedUnit (modulePushforward B S hS f)
          (derivedModulePushforward B S hS f) (derivedModulePushforwardUnit B S hS f) M :=
    fun f M => (NatTrans.congr_app
      (modulePushforwardSingleToRightDerived_eq_singleUnit B S hS f _ _) M).trans
        (Stacks.DerivedFunctor.singleUnit_app _ _ _ M)
  have hcongr : smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS (rfl : t ≫ i₁ = t ≫ i₁) =
        smallEtaleDerivedModulePullbackCompIso B S hS t i₁ := by
    rw [smallEtaleDerivedModulePullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [hσ (t ≫ i₁) F, hσ i₁, hσ t F, hcongr]
  exact Stacks.DerivedFunctor.map_trans_eqToIso_hom_comp_of_inv_comp
    (DerivedCategory.singleFunctor _ 0) ((modulePushforwardCompIso B S hS t i₁).app F) _ _ _ key

end AlgebraicGeometry.Space
