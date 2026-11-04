module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackULift

/-!
# Pullback of sheaves of modules commutes with the universe lift

Let `F : C ⥤ D` be a continuous functor of sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings. The universe lift `SheafOfModules.uliftFunctor` commutes with the pushforward along `φ` on
the nose. This file shows that it commutes with the pullback as well: when the source site is
essentially small in the module universe `v`, the mate `pullback φ (M↑) ⟶ (pullback φ M)↑` of the
identity square of pushforwards is an isomorphism. This is the sheaf form of
`PresheafOfModules.isIso_pullbackULiftHom_app`.

## Main definitions

* `SheafOfModules.pushforwardULiftIso`: the universe lift commutes with pushforward.
* `SheafOfModules.pullbackULiftHom`: the comparison `pullback φ (M↑) ⟶ (pullback φ M)↑`.

## Main results

* `SheafOfModules.bijective_uliftMap_comp_val`: a universal arrow from a presheaf of modules to
  sheaves of modules stays universal after the universe lift.
* `SheafOfModules.bijective_pullbackUnit_comp_val`: the pullback of a sheaf of modules is
  universal among sheaves under the presheaf pullback.
* `SheafOfModules.isIso_pullbackULiftHom_app`: **the comparison is an isomorphism**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v t v₁ v₂ u₁ u₂ r

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}} [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)

/-- The universe lift commutes with the pushforward of sheaves of modules, on the nose. -/
def pushforwardULiftIso :
    SheafOfModules.pushforward.{v} φ ⋙ SheafOfModules.uliftFunctor.{_, _, _, _, t} ≅
      SheafOfModules.uliftFunctor.{_, _, _, _, t} ⋙ SheafOfModules.pushforward.{max v t} φ :=
  NatIso.ofComponents (fun _M => Iso.refl _) (fun _ => rfl)

section Mate

variable [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{max v t} φ).IsRightAdjoint]

/-- The comparison `pullback φ (M↑) ⟶ (pullback φ M)↑` between pulling back the universe lift
of a sheaf of modules and lifting its pullback: the mate of
`SheafOfModules.pushforwardULiftIso`. -/
def pullbackULiftHom :
    SheafOfModules.uliftFunctor.{_, _, _, _, t} ⋙ SheafOfModules.pullback.{max v t} φ ⟶
      SheafOfModules.pullback.{v} φ ⋙ SheafOfModules.uliftFunctor.{_, _, _, _, t} :=
  (mateEquiv (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{max v t} φ)).symm (pushforwardULiftIso.{v, t} φ).hom

/-- The adjoint transpose of `SheafOfModules.pullbackULiftHom` at `M` is the lift of the unit
at `M`. -/
theorem homEquiv_pullbackULiftHom_app (M : SheafOfModules.{v} S) :
    (pullbackPushforwardAdjunction.{max v t} φ).homEquiv _ _
        ((pullbackULiftHom.{v, t} φ).app M) =
      uliftFunctor.{_, _, _, _, t}.map ((pullbackPushforwardAdjunction.{v} φ).unit.app M) := by
  rw [Adjunction.homEquiv_unit]
  have h := unit_mateEquiv_symm (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{max v t} φ) (pushforwardULiftIso.{v, t} φ).hom M
  simp only [pushforwardULiftIso] at h
  exact h.symm

end Mate

section Universal

/-- Every `g : A ⟶ G B` is the unit at `A` followed by `G` of its adjoint transpose. -/
private theorem eq_unit_comp_map_homEquiv_symm {C' D' : Type*} [Category* C'] [Category* D']
    {F' : C' ⥤ D'} {G' : D' ⥤ C'} (adj : F' ⊣ G') {A : C'} {B : D'} (g : A ⟶ G'.obj B) :
    g = adj.unit.app A ≫ G'.map ((adj.homEquiv A B).symm g) :=
  ((adj.homEquiv A B).apply_symm_apply g).symm.trans (adj.homEquiv_unit A B _)

variable {R : Sheaf K RingCat.{r}}
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{max v t}] [K.WEqualsLocallyBijective AddCommGrpCat.{max v t}]

/-- **A universal arrow to sheaves stays universal after the universe lift.** If every morphism
from a presheaf of modules `Q` to a sheaf of modules factors uniquely through `σ : Q ⟶ N`, then
the same holds for the universe lift of `σ` among sheaves of modules in the larger universe. -/
theorem bijective_uliftMap_comp_val {Q : PresheafOfModules.{v} R.obj} {N : SheafOfModules.{v} R}
    (σ : Q ⟶ N.val)
    (hσ : ∀ N₀ : SheafOfModules.{v} R, Function.Bijective (fun h : N ⟶ N₀ => σ ≫ h.val))
    (N' : SheafOfModules.{max v t} R) :
    Function.Bijective (fun h : uliftFunctor.{_, _, _, _, t}.obj N ⟶ N' =>
      PresheafOfModules.uliftFunctor.{_, _, _, _, t}.map σ ≫ h.val) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  let adj' := PresheafOfModules.sheafificationAdjunction.{max v t} (𝟙 R.obj)
  let a : (PresheafOfModules.sheafification.{v} (𝟙 R.obj)).obj Q ⟶ N := (adj.homEquiv Q N).symm σ
  have ha : IsIso a := (Adjunction.isIso_homEquiv_symm_iff_bijective adj σ).mpr hσ
  have hu := (Adjunction.isIso_homEquiv_symm_iff_bijective adj' _).mp
    (PresheafOfModules.isIso_sheafifyULiftHom.{_, _, _, _, t} (𝟙 R.obj) Q) N'
  let σ' : Q ⟶ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj N := σ
  have hσa : σ' = adj.unit.app Q ≫ (SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).map a :=
    eq_unit_comp_map_homEquiv_symm adj σ'
  have h : (fun h : uliftFunctor.{_, _, _, _, t}.obj N ⟶ N' =>
      PresheafOfModules.uliftFunctor.{_, _, _, _, t}.map σ ≫ h.val) =
      (fun h => PresheafOfModules.uliftSheafifyUnit.{_, _, _, _, t} (𝟙 R.obj) Q ≫
        (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map h) ∘
        (fun h => uliftFunctor.{_, _, _, _, t}.map a ≫ h) := by
    funext h
    change PresheafOfModules.uliftMap.{_, _, _, _, t} σ' ≫ h.val = _
    rw [hσa]
    rfl
  rw [h]
  exact hu.comp (Adjunction.bijective_iso_hom_comp (asIso (uliftFunctor.{_, _, _, _, t}.map a)))

end Universal

section Main

variable [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [(PresheafOfModules.pushforward.{max v t} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [(PresheafOfModules.pushforward.{max v t} φ.hom).IsRightAdjoint] in
/-- The pullback of a sheaf of modules `M` is the sheafification of the presheaf pullback of `M`:
the presheaf transpose of the unit at `M` is universal among morphisms to sheaves. -/
theorem bijective_pullbackUnit_comp_val (M : SheafOfModules.{v} S) (N : SheafOfModules.{v} R) :
    Function.Bijective (fun h : (pullback.{v} φ).obj M ⟶ N =>
      ((PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom).homEquiv M.val
          ((pullback.{v} φ).obj M).val).symm
        ((pullbackPushforwardAdjunction.{v} φ).unit.app M).val ≫ h.val) := by
  let adj := pullbackPushforwardAdjunction.{v} φ
  let padj := PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom
  have e : (fun h : (pullback.{v} φ).obj M ⟶ N =>
      (padj.homEquiv M.val ((pullback.{v} φ).obj M).val).symm (adj.unit.app M).val ≫ h.val) =
      (padj.homEquiv M.val N.val).symm ∘
        (fun h : M ⟶ (pushforward.{v} φ).obj N =>
          (h.val : M.val ⟶ (PresheafOfModules.pushforward.{v} φ.hom).obj N.val)) ∘
        (adj.homEquiv M N) := by
    funext h
    exact (padj.homEquiv_naturality_right_symm _ _).symm.trans
      (congrArg (fun x : M ⟶ (pushforward.{v} φ).obj N =>
        (padj.homEquiv M.val N.val).symm x.val) (adj.homEquiv_unit M N h).symm)
  rw [e]
  exact (padj.homEquiv M.val N.val).symm.bijective.comp
    (((fullyFaithfulForget S).map_bijective _ _).comp (adj.homEquiv M N).bijective)

variable [HasWeakSheafify K AddCommGrpCat.{max v t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [∀ X, Small.{v} (S.obj.obj X)] [EssentiallySmall.{v} C] [∀ X, Small.{v} (R.obj.obj X)]
  [LocallySmall.{v} D]

/-- **The pullback of sheaves of modules commutes with the universe lift**: the comparison
`pullback φ (M↑) ⟶ (pullback φ M)↑` is an isomorphism for every sheaf of modules `M` over an
essentially small site. -/
theorem isIso_pullbackULiftHom_app (M : SheafOfModules.{v} S) :
    IsIso ((pullbackULiftHom.{v, t} φ).app M) := by
  let adj := pullbackPushforwardAdjunction.{v} φ
  let adj' := pullbackPushforwardAdjunction.{max v t} φ
  let padj := PresheafOfModules.pullbackPushforwardAdjunction.{v} φ.hom
  let padj' := PresheafOfModules.pullbackPushforwardAdjunction.{max v t} φ.hom
  have hθ : (pullbackULiftHom.{v, t} φ).app M =
      (adj'.homEquiv _ _).symm (uliftFunctor.{_, _, _, _, t}.map (adj.unit.app M)) := by
    rw [← homEquiv_pullbackULiftHom_app, Equiv.symm_apply_apply]
  rw [hθ]
  refine (Adjunction.isIso_homEquiv_symm_iff_bijective adj' _).mpr fun N' => ?_
  let σ := (padj.homEquiv M.val ((pullback.{v} φ).obj M).val).symm (adj.unit.app M).val
  have hB := bijective_uliftMap_comp_val.{v, t} σ (bijective_pullbackUnit_comp_val φ M) N'
  have : ∀ X, Small.{v} (((sheafToPresheaf K RingCat.{r}).obj R).obj X) := ‹_›
  have hP : IsIso ((PresheafOfModules.pullbackULiftHom.{v, t} φ.hom).app M.val) :=
    PresheafOfModules.isIso_pullbackULiftHom_app.{v, t} φ.hom M.val
  have h := (Equiv.eq_symm_apply (padj'.homEquiv _ _)).mpr
    (PresheafOfModules.homEquiv_pullbackULiftHom_app.{v, t} φ.hom M.val)
  rw [h] at hP
  have hP' := (Adjunction.isIso_homEquiv_symm_iff_bijective padj'
    (X := PresheafOfModules.uliftFunctor.{_, _, _, _, t}.obj M.val)
    (Y := PresheafOfModules.uliftFunctor.{_, _, _, _, t}.obj
      ((PresheafOfModules.pullback.{v} φ.hom).obj M.val))
    (PresheafOfModules.uliftFunctor.{_, _, _, _, t}.map (padj.unit.app M.val))).mp hP N'.val
  have hη : (adj.unit.app M).val =
      padj.unit.app M.val ≫ (PresheafOfModules.pushforward.{v} φ.hom).map σ :=
    eq_unit_comp_map_homEquiv_symm padj _
  have e : (fun h => (forget S).map h) ∘
      (fun h : uliftFunctor.{_, _, _, _, t}.obj ((pullback.{v} φ).obj M) ⟶ N' =>
        uliftFunctor.{_, _, _, _, t}.map (adj.unit.app M) ≫
          (pushforward.{max v t} φ).map h) =
      (fun k => PresheafOfModules.uliftFunctor.{_, _, _, _, t}.map (padj.unit.app M.val) ≫
          (PresheafOfModules.pushforward.{max v t} φ.hom).map k) ∘
        (fun h => PresheafOfModules.uliftFunctor.{_, _, _, _, t}.map σ ≫ h.val) := by
    funext h
    change PresheafOfModules.uliftMap.{_, _, _, _, t} (adj.unit.app M).val ≫
      (PresheafOfModules.pushforward.{max v t} φ.hom).map h.val = _
    rw [hη]
    rfl
  have hc := (congrArg Function.Bijective e).mpr (hP'.comp hB)
  exact (Function.Bijective.of_comp_iff' ((fullyFaithfulForget S).map_bijective _ _) _).mp hc

end Main

end SheafOfModules
