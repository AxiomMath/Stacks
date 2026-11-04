module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactLocallyFree
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassOpenFactor
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf

/-!
# Base change of the hypothesis of Stacks 0FEC

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions, and let `D` be a conormal-compatible triple of
virtual normal bundles for them, the hypothesis of Stacks 0FEC
(`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`). The proof of Stacks 0FEC begins: *the
assumptions remain satisfied after any base change by a morphism `X' ⟶ X` (the short exact
sequence of virtual normal sheaves is locally split hence remains exact after any base change)*.
This file proves that sentence, for arbitrary cartesian squares

```
  Z' --i'--> Y' --j'--> X'
  |gZ        |gY        |f
  Z  --i-->  Y  --j-->  X
```

The three virtual normal bundles are base changed by Stacks 0FBJ
(`Stacks.Chow.VirtualNormalBundle.baseChange`), the top row of duals is pulled back along `gZ`
and read through the dual base-change isomorphisms `g^*(𝒩^∨) ≅ (g^*𝒩)^∨` of Stacks 0GMX, and
the two squares against the conormal sequence commute by the functoriality of the canonical maps
of conormal sheaves (Stacks 04G2).

## Main definitions

* `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.baseChange` — the base-changed triple.

## Main results

* `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.baseChange_bundleZX`,
  `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.baseChange_bundleZY`,
  `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.baseChange_bundleYX` — its three virtual
  normal bundles are the base changes of those of `D`.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.Immersion Stacks.Thickenings

universe u

namespace Stacks.Chow

section BaseChange

variable {Z Y X Z' Y' X' : Scheme.{u}} {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
  (D : ConormalCompatibleVirtualNormalBundles i j) (i' : Z' ⟶ Y') (j' : Y' ⟶ X')
  [IsImmersion i'] [IsImmersion j'] (gZ : Z' ⟶ Z) (gY : Y' ⟶ Y) (f : X' ⟶ X)
  (sqY : IsPullback j' gY f j) (sqZ : IsPullback i' gZ gY i)

include sqZ in
/-- The isomorphism `i'^* gY^* ≅ gZ^* i^*` of pullback functors attached to the commutative
square `i' ≫ gY = gZ ≫ i`. -/
def squarePullbackIso :
    modulePullback gY.toLRSHom.toShHom ⋙ modulePullback i'.toLRSHom.toShHom ≅
      modulePullback i.toLRSHom.toShHom ⋙ modulePullback gZ.toLRSHom.toShHom :=
  (modulePullbackComp i'.toLRSHom.toShHom gY.toLRSHom.toShHom).symm ≪≫
    modulePullbackCongr (toShHom_square sqZ.w) ≪≫
      modulePullbackComp gZ.toLRSHom.toShHom i.toLRSHom.toShHom

/-- The left term of the base-changed top row compared with the pullback along `gZ` of the left
term of the top row: `gZ^* i^*(𝒩''^∨) ≅ i'^* gY^*(𝒩''^∨) ≅ i'^*((gY^*𝒩'')^∨)`. -/
def ConormalCompatibleVirtualNormalBundles.baseChangeLeftIso :
    (modulePullback gZ.toLRSHom.toShHom).obj
        ((modulePullback i.toLRSHom.toShHom).obj (dualSheaf D.bundleYX.bundle)) ≅
      (modulePullback i'.toLRSHom.toShHom).obj
        (dualSheaf ((modulePullback gY.toLRSHom.toShHom).obj D.bundleYX.bundle)) :=
  ((squarePullbackIso i' gZ gY sqZ).app (dualSheaf D.bundleYX.bundle)).symm ≪≫
    (modulePullback i'.toLRSHom.toShHom).mapIso
      (Stacks.FundamentalGroup.pullbackDualSheafIso gY D.bundleYX.bundle inferInstance)

/-- The left map of the base-changed top row:
`i'^*((gY^*𝒩'')^∨) ≅ gZ^* i^*(𝒩''^∨) ⟶ gZ^*(𝒩^∨) ≅ (gZ^*𝒩)^∨`. -/
def ConormalCompatibleVirtualNormalBundles.baseChangeDualLeft :
    (modulePullback i'.toLRSHom.toShHom).obj
        (dualSheaf ((modulePullback gY.toLRSHom.toShHom).obj D.bundleYX.bundle)) ⟶
      dualSheaf ((modulePullback gZ.toLRSHom.toShHom).obj D.bundleZX.bundle) :=
  (D.baseChangeLeftIso i' gZ gY sqZ).inv ≫ (modulePullback gZ.toLRSHom.toShHom).map D.dualLeft ≫
    (Stacks.FundamentalGroup.pullbackDualSheafIso gZ D.bundleZX.bundle inferInstance).hom

/-- The right map of the base-changed top row: `(gZ^*𝒩)^∨ ≅ gZ^*(𝒩^∨) ⟶ gZ^*(𝒩'^∨) ≅
(gZ^*𝒩')^∨`. -/
def ConormalCompatibleVirtualNormalBundles.baseChangeDualRight :
    dualSheaf ((modulePullback gZ.toLRSHom.toShHom).obj D.bundleZX.bundle) ⟶
      dualSheaf ((modulePullback gZ.toLRSHom.toShHom).obj D.bundleZY.bundle) :=
  (Stacks.FundamentalGroup.pullbackDualSheafIso gZ D.bundleZX.bundle inferInstance).inv ≫
    (modulePullback gZ.toLRSHom.toShHom).map D.dualRight ≫
      (Stacks.FundamentalGroup.pullbackDualSheafIso gZ D.bundleZY.bundle inferInstance).hom

/-- **The base-changed top row is short exact.** The top row of `D` is a short exact sequence
whose third term `𝒩'^∨` is finite locally free, so it stays short exact under pullback along
`gZ` (it is locally split), and the base-changed row is that pullback conjugated by
isomorphisms of its three terms. -/
theorem ConormalCompatibleVirtualNormalBundles.isShortExactSequenceOfModules_baseChange :
    IsShortExactSequenceOfModules (D.baseChangeDualLeft i' gZ gY sqZ)
      (D.baseChangeDualRight gZ) := by
  let : Preadditive Z.Modules := SheafOfModules.instPreadditive Z.ringCatSheaf
  let : HasZeroMorphisms Z.Modules := Preadditive.preadditiveHasZeroMorphisms
  obtain ⟨h, hse⟩ := D.shortExact
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf D.bundleZY.bundle) := D.bundleZY.isFiniteLocallyFree_dualSheaf
  have hse' := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree gZ _ hse
  exact isShortExactSequenceOfModules_conjugate _ hse' (D.baseChangeLeftIso i' gZ gY sqZ)
    (Stacks.FundamentalGroup.pullbackDualSheafIso gZ D.bundleZX.bundle inferInstance)
    (Stacks.FundamentalGroup.pullbackDualSheafIso gZ D.bundleZY.bundle inferInstance)

/-- Two transports along equalities of objects that compose to a loop cancel. -/
theorem eqToHom_comp_eqToHom_comp {C : Type*} [Category C] {A B D : C} (p : A = B) (q : B = A)
    (h : A ⟶ D) : eqToHom p ≫ eqToHom q ≫ h = h := by
  simp

/-- A functor preserves an equality of composites of two morphisms. -/
private theorem map_comp_eq_map_comp {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {A B B' D : C} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ B'} {d : B' ⟶ D} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simp only [← F.map_comp, h]

/-- The diagram chase behind the left square of the base-changed triple, in an arbitrary
category. -/
theorem leftSquare_aux {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ D E F G H : C}
    (a : A₀ ⟶ A₁) (s₁ : A₁ ⟶ B₀) (d : B₀ ⟶ D) (e : D ≅ E) (σ : D ⟶ F) (k : F ⟶ G)
    (u : B₀ ⟶ B₁) (l : B₁ ⟶ F) (hl : d ≫ σ = u ≫ l) (v : A₁ ⟶ A₂) (s₂ : A₂ ⟶ B₁)
    (hn : v ≫ s₂ = s₁ ≫ u) (w : A₂ ⟶ H) (k' : H ⟶ G) (hk : s₂ ≫ l ≫ k = w ≫ k') :
    ((a ≫ s₁) ≫ d ≫ e.hom) ≫ e.inv ≫ σ ≫ k = (a ≫ v ≫ w) ≫ k' := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hl, ← reassoc_of% hn, hk]

/-- A transport along an equality of an object with itself is the identity. -/
theorem eqToHom_comp_self {C : Type*} [Category C] {A D : C} (p : A = A) (h : A ⟶ D) :
    eqToHom p ≫ h = h := by
  simp

/-- The key identity behind the left square: the two ways of composing canonical maps of
conormal sheaves from `Z' ⟶ X'` to `Y ⟶ X` agree, through the comparison
`i'^* gY^* ≅ gZ^* i^*`. Both are the canonical map of the composite square (Stacks 04G2). -/
theorem squarePullbackIso_comp_immersionConormalSheafMap :
    (squarePullbackIso i' gZ gY sqZ).hom.app (immersionConormalSheaf j) ≫
        (modulePullback gZ.toLRSHom.toShHom).map
          (immersionConormalSheafMap (i ≫ j) j i (𝟙 X) (toShHom_square (by simp))) ≫
        immersionConormalSheafMap (i' ≫ j') (i ≫ j) gZ f
          (toShHom_square (IsPullback.paste_horiz sqZ sqY).w) =
      (modulePullback i'.toLRSHom.toShHom).map
          (immersionConormalSheafMap j' j gY f (toShHom_square sqY.w)) ≫
        immersionConormalSheafMap (i' ≫ j') j' i' (𝟙 X') (toShHom_square (by simp)) := by
  have c₁ : (i' ≫ j') ≫ f = gZ ≫ (i ≫ j) := (IsPullback.paste_horiz sqZ sqY).w
  have c₂ : (i ≫ j) ≫ 𝟙 X = i ≫ j := by simp
  have c₃ : (i' ≫ j') ≫ 𝟙 X' = i' ≫ j' := by simp
  have h₁ := immersionConormalSheafMap_comp (i' ≫ j') (i ≫ j) j gZ f c₁ i (𝟙 X) c₂
  have h₂ := immersionConormalSheafMap_comp (i' ≫ j') j' j i' (𝟙 X') c₃ gY f sqY.w
  have hc := immersionConormalSheafMap_congr (i' ≫ j') j sqZ.w
    (show 𝟙 X' ≫ f = f ≫ 𝟙 X by simp) (toShHom_square (square_comp c₃ sqY.w))
    (toShHom_square (square_comp c₁ c₂))
  rw [← Iso.cancel_iso_hom_left ((modulePullbackComp i'.toLRSHom.toShHom
    gY.toLRSHom.toShHom).app (immersionConormalSheaf j)), Iso.app_hom, ← h₂]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← h₁, hc]
  simp only [modulePullbackCongr, eqToIso.hom, eqToHom_app]
  exact eqToHom_comp_eqToHom_comp _ _ _

/-- **The left square of the base-changed triple commutes.** -/
theorem ConormalCompatibleVirtualNormalBundles.baseChange_leftSquare :
    D.baseChangeDualLeft i' gZ gY sqZ ≫
        (D.bundleZX.baseChange (i ≫ j) (i' ≫ j') gZ f
          (IsPullback.paste_horiz sqZ sqY)).surjection =
      (modulePullback i'.toLRSHom.toShHom).map
          (D.bundleYX.baseChange j j' gY f sqY).surjection ≫
        immersionConormalSheafMap (i' ≫ j') j' i' (𝟙 X') (toShHom_square (by simp)) := by
  have hL := map_comp_eq_map_comp (modulePullback gZ.toLRSHom.toShHom) D.leftSquare
  exact (leftSquare_aux _ _ _ _ _ _ _ _ hL _ _
    ((squarePullbackIso i' gZ gY sqZ).hom.naturality D.bundleYX.surjection) _ _
    (squarePullbackIso_comp_immersionConormalSheafMap i' j' gZ gY f sqY sqZ)).trans
    (congrArg (· ≫ _) ((Functor.map_comp (modulePullback i'.toLRSHom.toShHom) _ _).trans
      (congrArg (_ ≫ ·) (Functor.map_comp (modulePullback i'.toLRSHom.toShHom) _ _))).symm)

/-- The key identity behind the right square: the right-hand maps of the conormal sequences of
`Z ⟶ Y ⟶ X` and of its base change are intertwined by the canonical maps of conormal sheaves of
the base change. Both sides are the canonical map of the composite square from `Z' ⟶ Y'` to
`Z ⟶ X` (Stacks 04G2). -/
theorem map_conormalSequenceRightMap_comp_immersionConormalSheafMap :
    (modulePullback gZ.toLRSHom.toShHom).map (conormalSequenceRightMap i j) ≫
        immersionConormalSheafMap i' i gZ gY (toShHom_square sqZ.w) =
      immersionConormalSheafMap (i' ≫ j') (i ≫ j) gZ f
          (toShHom_square (IsPullback.paste_horiz sqZ sqY).w) ≫
        conormalSequenceRightMap i' j' := by
  have c₁ : (i' ≫ j') ≫ f = gZ ≫ (i ≫ j) := (IsPullback.paste_horiz sqZ sqY).w
  have c₂ : i ≫ j = 𝟙 Z ≫ (i ≫ j) := (Category.id_comp _).symm
  have c₃ : i' ≫ j' = 𝟙 Z' ≫ (i' ≫ j') := (Category.id_comp _).symm
  have h₁ := immersionConormalSheafMap_comp i' i (i ≫ j) gZ gY sqZ.w (𝟙 Z) j c₂
  have h₂ := immersionConormalSheafMap_comp i' (i' ≫ j') (i ≫ j) (𝟙 Z') j' c₃ gZ f c₁
  have hci : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp j.toLRSHom.toShHom (Scheme.Hom.toLRSHom (𝟙 B)).toShHom).hom.app M =
        (modulePullback j.toLRSHom.toShHom).map ((modulePullbackId B.toRingedSpace).inv.app M) :=
    fun j M ↦ modulePullbackComp_comp_id_hom_app j.toLRSHom.toShHom M
  have hic : ∀ {A B : Scheme.{u}} (j : A ⟶ B)
      (M : SheafOfModules.{u} (structureSheafRing B.toRingedSpace)),
      (modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom j.toLRSHom.toShHom).hom.app M =
        (modulePullbackId A.toRingedSpace).inv.app ((modulePullback j.toLRSHom.toShHom).obj M) := by
    intro A B j M
    exact (Iso.hom_eq_inv ((modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 A)).toShHom
      j.toLRSHom.toShHom).app M) ((modulePullbackId A.toRingedSpace).app _)).2
      (modulePullbackComp_id_inv_app j.toLRSHom.toShHom M).symm
  rw [hci] at h₁
  rw [hic] at h₂
  have hn := (modulePullbackId Z'.toRingedSpace).inv.naturality
    (immersionConormalSheafMap (i' ≫ j') (i ≫ j) gZ f (toShHom_square c₁))
  have hc := immersionConormalSheafMap_congr i' (i ≫ j) (show gZ ≫ 𝟙 Z = 𝟙 Z' ≫ gZ by simp)
    (show gY ≫ j = j' ≫ f from sqY.w.symm) (toShHom_square (square_comp sqZ.w c₂))
    (toShHom_square (square_comp c₃ c₁))
  simp only [Functor.id_map] at hn
  simp only [conormalSequenceRightMap, Iso.app_inv]
  exact ((Functor.map_comp (modulePullback gZ.toLRSHom.toShHom) _ _ =≫ _).trans
    ((Category.assoc _ _ _).trans h₁.symm)).trans
    ((eqToHom_comp_self _ _).symm.trans (hc.symm.trans (h₂.trans
      (((Category.assoc _ _ _).symm.trans (hn.symm =≫ _)).trans (Category.assoc _ _ _)))))

/-- The diagram chase behind the right square of the base-changed triple, in an arbitrary
category. -/
theorem rightSquare_aux {C : Type*} [Category C] {A B B' D D' F G H : C} (e : A ≅ B)
    (e' : D ≅ D') (d : A ⟶ D) (σ' : D ⟶ G) (σ : A ⟶ F) (c : F ⟶ G) (hr : d ≫ σ' = σ ≫ c)
    (k : G ⟶ H) (K : F ⟶ B') (r : B' ⟶ H) (hk : c ≫ k = K ≫ r) :
    (e.inv ≫ d ≫ e'.hom) ≫ e'.inv ≫ σ' ≫ k = (e.inv ≫ σ ≫ K) ≫ r := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hr, hk]

/-- **The right square of the base-changed triple commutes.** -/
theorem ConormalCompatibleVirtualNormalBundles.baseChange_rightSquare :
    D.baseChangeDualRight gZ ≫ (D.bundleZY.baseChange i i' gZ gY sqZ).surjection =
      (D.bundleZX.baseChange (i ≫ j) (i' ≫ j') gZ f
          (IsPullback.paste_horiz sqZ sqY)).surjection ≫
        conormalSequenceRightMap i' j' :=
  rightSquare_aux _ _ _ _ _ _
    (map_comp_eq_map_comp (modulePullback gZ.toLRSHom.toShHom) D.rightSquare) _ _ _
    (map_conormalSequenceRightMap_comp_immersionConormalSheafMap i' j' gZ gY f sqY sqZ)

/-- **Stacks 0FEC, the hypothesis is stable under base change.** For immersions
`i : Z ⟶ Y`, `j : Y ⟶ X`, a conormal-compatible triple `D` for them, and cartesian squares
`Y' = Y ×_X X'` and `Z' = Z ×_Y Y'` along any morphism `f : X' ⟶ X`, the base changes
(Stacks 0FBJ) of the three virtual normal bundles of `D`, with the pulled-back top row read
through the dual base-change isomorphisms, form a conormal-compatible triple for `i'` and `j'`.
The top row stays short exact because a short exact sequence of finite locally free modules is
locally split. -/
def ConormalCompatibleVirtualNormalBundles.baseChange :
    ConormalCompatibleVirtualNormalBundles i' j' where
  bundleZX := D.bundleZX.baseChange (i ≫ j) (i' ≫ j') gZ f
    (IsPullback.paste_horiz sqZ sqY)
  bundleZY := D.bundleZY.baseChange i i' gZ gY sqZ
  bundleYX := D.bundleYX.baseChange j j' gY f sqY
  dualLeft := D.baseChangeDualLeft i' gZ gY sqZ
  dualRight := D.baseChangeDualRight gZ
  shortExact := D.isShortExactSequenceOfModules_baseChange i' gZ gY sqZ
  leftSquare := D.baseChange_leftSquare i' j' gZ gY f sqY sqZ
  rightSquare := D.baseChange_rightSquare i' j' gZ gY f sqY sqZ

/-- The bundle on `Z' ⟶ X'` of the base-changed triple is the base change of `D.bundleZX`. -/
@[simp]
theorem ConormalCompatibleVirtualNormalBundles.baseChange_bundleZX :
    (D.baseChange i' j' gZ gY f sqY sqZ).bundleZX =
      D.bundleZX.baseChange (i ≫ j) (i' ≫ j') gZ f
        (IsPullback.paste_horiz sqZ sqY) :=
  rfl

/-- The bundle on `Z' ⟶ Y'` of the base-changed triple is the base change of `D.bundleZY`. -/
@[simp]
theorem ConormalCompatibleVirtualNormalBundles.baseChange_bundleZY :
    (D.baseChange i' j' gZ gY f sqY sqZ).bundleZY = D.bundleZY.baseChange i i' gZ gY sqZ :=
  rfl

/-- The bundle on `Y' ⟶ X'` of the base-changed triple is the base change of `D.bundleYX`. -/
@[simp]
theorem ConormalCompatibleVirtualNormalBundles.baseChange_bundleYX :
    (D.baseChange i' j' gZ gY f sqY sqZ).bundleYX = D.bundleYX.baseChange j j' gY f sqY :=
  rfl

end BaseChange

end Stacks.Chow

end
