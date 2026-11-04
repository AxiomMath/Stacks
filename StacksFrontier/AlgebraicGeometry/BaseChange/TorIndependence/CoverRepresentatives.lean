module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.CoverStep

/-!
# Pulling a base-change datum back along a square of morphisms

Let `K` be an object of `D(𝒪_X)`, `K'` one of `D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`.  A commutative
square

```
Z' --g_Z--> Z
|           |
j'          j
v           v
X' --g'---> X
```

pulls the datum `(K, K', φ)` back to the datum `(Lj^*K, L(j')^*K', φ_j)` on `Z`, where `φ_j` is
`L(g_Z)^*Lj^*K ≅ L(g_Z ≫ j)^*K = L(j' ≫ g')^*K ≅ L(j')^*L(g')^*K` followed by `L(j')^*φ`.  Pulling
back along two stacked squares agrees with pulling back along the outer rectangle, up to the
composition isomorphisms of Stacks 0D5S.

## Main definitions

* `Stacks.Cohomology.BaseChangeCover.pullDatum`: the pulled-back datum `φ_j`.

## Main results

* `Stacks.Cohomology.BaseChangeCover.pullDatum_comp`: pulling back along two stacked squares is
  pulling back along the outer rectangle.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChangeCover

/-- Cancelling three epimorphisms in front of two composites given by a factorization. -/
theorem paste_datum {C : Type*} [Category* C] {P Q R₁ S₁ T₁ V₁ W₁ : C}
    (m₁ : P ⟶ Q) (DR : R₁ ⟶ Q) (d1 : S₁ ⟶ P) (d2 : T₁ ⟶ S₁) (ci : R₁ ⟶ T₁)
    [IsIso d1] [IsIso d2] [IsIso ci] (hp : DR = ci ≫ d2 ≫ d1 ≫ m₁)
    (pR : Q ⟶ V₁) (Lφr : R₁ ⟶ V₁) (hR : DR ≫ pR = Lφr)
    (p1 : P ⟶ W₁) (Lp2 : S₁ ⟶ W₁) (h1 : d1 ≫ p1 = Lp2)
    (LLφ : T₁ ⟶ W₁) (h2 : d2 ≫ Lp2 = LLφ)
    (ch : W₁ ⟶ V₁) (hn : ci ≫ LLφ ≫ ch = Lφr) :
    m₁ ≫ pR = p1 ≫ ch := by
  rw [← cancel_epi d1, ← cancel_epi d2, ← cancel_epi ci]
  rw [hp, Category.assoc, Category.assoc, Category.assoc] at hR
  rw [hR, ← hn, ← h2, ← h1]
  simp only [Category.assoc]

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

section Datum

variable {Z' Z X' X : RingedSpace.{u, u}} (gZ : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X)
  (g' : X' ⟶ X) (w : gZ ≫ j = j' ≫ g')

/-- **The datum pulled back along a commutative square.** -/
def pullDatum (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullback gZ).obj ((derivedPullback j).obj K) ⟶ (derivedPullback j').obj K' :=
  (derivedPullbackCompIsoCanonical gZ j).hom.app K ≫
    (derivedPullbackCompIsoLeft gZ j' j g' w).inv.app K ≫ (derivedPullback j').map φ

/-- `pullDatum`, unfolded. -/
theorem pullDatum_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    pullDatum gZ j' j g' w K K' φ = (derivedPullbackCompIsoCanonical gZ j).hom.app K ≫
      ((derivedPullbackCompIsoLeft gZ j' j g' w).inv.app K ≫ (derivedPullback j').map φ) :=
  rfl

/-- The comparison of the two iterated derived pullbacks around the square, followed by the
pulled-back datum, is the derived pullback of the datum. -/
theorem derivedPullbackSquare_app_comp_pullDatum
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullbackSquare gZ j' j g' w).natTrans.app K ≫ pullDatum gZ j' j g' w K K' φ =
      (derivedPullback j').map φ := by
  show ((derivedPullbackCompIsoLeft gZ j' j g' w).hom.app K ≫
    (derivedPullbackCompIsoCanonical gZ j).inv.app K) ≫
      ((derivedPullbackCompIsoCanonical gZ j).hom.app K ≫
        (derivedPullbackCompIsoLeft gZ j' j g' w).inv.app K ≫ (derivedPullback j').map φ) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]

/-- The comparison of the two iterated derived pullbacks around a commutative square is an
isomorphism at every object. -/
instance isIso_derivedPullbackSquare_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPullbackSquare gZ j' j g' w).natTrans.app K) := by
  change IsIso ((derivedPullbackCompIsoLeft gZ j' j g' w).hom.app K ≫
    (derivedPullbackCompIsoCanonical gZ j).inv.app K)
  infer_instance

end Datum

section Paste

variable {W' W Z' Z X' X : RingedSpace.{u, u}} (gW : W' ⟶ W) (e' : W' ⟶ Z') (e : W ⟶ Z)
  (gZ : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X) (g' : X' ⟶ X)
  (w₁ : gW ≫ e = e' ≫ gZ) (w₂ : gZ ≫ j = j' ≫ g')

/-- **Pulling back along two stacked squares is pulling back along the rectangle.** -/
theorem pullDatum_comp (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullback gW).map ((derivedPullbackCompIsoCanonical e j).hom.app K) ≫
        pullDatum gW (e' ≫ j') (e ≫ j) g' (comp_square gW e' e gZ j' j g' w₁ w₂) K K' φ =
      pullDatum gW e' e gZ w₁ ((derivedPullback j).obj K) ((derivedPullback j').obj K')
          (pullDatum gZ j' j g' w₂ K K' φ) ≫
        (derivedPullbackCompIsoCanonical e' j').hom.app K' := by
  have hp := congrArg (fun t => TwoSquare.natTrans t |>.app K)
    (derivedPullbackSquare_paste gW e' e gZ j' j g' w₁ w₂ (comp_square gW e' e gZ j' j g' w₁ w₂))
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] at hp
  have hn := (derivedPullbackCompIsoCanonical e' j').hom.naturality φ
  simp only [Functor.comp_map] at hn
  exact paste_datum
    (P := (derivedPullback gW).obj ((derivedPullback e).obj ((derivedPullback j).obj K)))
    ((derivedPullback gW).map ((derivedPullbackCompIsoCanonical e j).hom.app K))
    ((derivedPullbackSquare gW (e' ≫ j') (e ≫ j) g'
      (comp_square gW e' e gZ j' j g' w₁ w₂)).natTrans.app K)
    ((derivedPullbackSquare gW e' e gZ w₁).natTrans.app ((derivedPullback j).obj K))
    ((derivedPullback e').map ((derivedPullbackSquare gZ j' j g' w₂).natTrans.app K))
    ((derivedPullbackCompIsoCanonical e' j').inv.app ((derivedPullback g').obj K)) hp
    (pullDatum gW (e' ≫ j') (e ≫ j) g' (comp_square gW e' e gZ j' j g' w₁ w₂) K K' φ)
    ((derivedPullback (e' ≫ j')).map φ)
    (derivedPullbackSquare_app_comp_pullDatum gW (e' ≫ j') (e ≫ j) g' _ K K' φ)
    (pullDatum gW e' e gZ w₁ ((derivedPullback j).obj K) ((derivedPullback j').obj K')
      (pullDatum gZ j' j g' w₂ K K' φ))
    ((derivedPullback e').map (pullDatum gZ j' j g' w₂ K K' φ))
    (derivedPullbackSquare_app_comp_pullDatum gW e' e gZ w₁ _ _ _)
    ((derivedPullback e').map ((derivedPullback j').map φ))
    (by rw [← Functor.map_comp, derivedPullbackSquare_app_comp_pullDatum gZ j' j g' w₂ K K' φ])
    ((derivedPullbackCompIsoCanonical e' j').hom.app K')
    (by rw [hn]; exact Iso.inv_hom_id_app_assoc _ _ _)

end Paste

/-- Invertibility of a composite is unchanged by composing with isomorphisms on both sides of a
commuting square. -/
theorem isIso_iff_of_comm {C : Type*} [Category* C] {P₀ P₁ Q₀ Q₂ : C}
    (x : P₀ ⟶ Q₀) (u : P₀ ⟶ P₁) (y : P₁ ⟶ Q₂) (v : Q₀ ⟶ Q₂) [IsIso u] [IsIso v]
    (h : x ≫ v = u ≫ y) : IsIso x ↔ IsIso y := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [show y = inv u ≫ x ≫ v by rw [h, IsIso.inv_hom_id_assoc]]
    infer_instance
  · rw [show x = u ≫ y ≫ inv v by rw [← reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance

/-- A naturality square glued to a commuting square. -/
theorem chase_of_naturality {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ Y₀ Y₁ : C}
    (b : X₀ ⟶ X₁) (Rφ : X₁ ⟶ X₂) (Ru' : X₂ ⟶ X₃) (Lu : X₀ ⟶ Y₀) (b₂ : Y₀ ⟶ Y₁)
    (Rg : Y₁ ⟶ X₃) (RLu : X₁ ⟶ Y₁) (hn : Lu ≫ b₂ = b ≫ RLu) (hu : RLu ≫ Rg = Rφ ≫ Ru') :
    (b ≫ Rφ) ≫ Ru' = Lu ≫ b₂ ≫ Rg := by
  rw [Category.assoc, ← hu, ← Category.assoc, ← hn, Category.assoc]

section General

variable {W' W Z' Z : RingedSpace.{u, u}} (gW : W' ⟶ W) (e' : W' ⟶ Z') (e : W ⟶ Z)
  (gZ : Z' ⟶ Z) (w₁ : gW ≫ e = e' ≫ gZ)

/-- **The comparison of `Re_*Le^*K` with `Re'_*L(e')^*K'`**: base change along the square
followed by the direct image of the pulled-back datum. -/
def genBaseChange (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z')))
    (φ : (derivedPullback gZ).obj K ⟶ K') :
    (derivedPullback gZ).obj ((derivedPushforward e).obj ((derivedPullback e).obj K)) ⟶
      (derivedPushforward e').obj ((derivedPullback e').obj K') :=
  derivedBaseChangeMap gW e' e gZ w₁ ((derivedPullback e).obj K) ≫
    (derivedPushforward e').map (pullDatum gW e' e gZ w₁ K K' φ)

/-- The comparison carries the unit to the unit. -/
theorem pullback_map_unit_comp_genBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z')))
    (φ : (derivedPullback gZ).obj K ⟶ K') :
    (derivedPullback gZ).map ((derivedAdjunction e).unit.app K) ≫
        genBaseChange gW e' e gZ w₁ K K' φ =
      φ ≫ (derivedAdjunction e').unit.app K' :=
  map_unit_comp_mate (derivedAdjunction e) (derivedAdjunction e')
    (derivedPullbackCompIsoLeft gW e' e gZ w₁) (derivedPullbackCompIsoCanonical gW e) K _
    (derivedBaseChangeMap_counit _ _ _ _ _ _) φ

variable {T' T : RingedSpace.{u, u}} (fZ : Z ⟶ T) (fZ' : Z' ⟶ T') (gT : T' ⟶ T)
  (w₂ : gZ ≫ fZ = fZ' ≫ gT)

/-- **Vertical pasting.** The comparison of the lower square at `Re_*Le^*K` followed by the direct
image of `genBaseChange` is invertible exactly when the composition over the rectangle is. -/
theorem isIso_genBaseChange_iff (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z')))
    (φ : (derivedPullback gZ).obj K ⟶ K') :
    IsIso (derivedBaseChangeMap gZ fZ' fZ gT w₂
        ((derivedPushforward e).obj ((derivedPullback e).obj K)) ≫
        (derivedPushforward fZ').map (genBaseChange gW e' e gZ w₁ K K' φ)) ↔
      IsIso (derivedBaseChangeMap gW (e' ≫ fZ') (e ≫ fZ) gT (comp_square gW e' e gZ fZ' fZ gT w₁ w₂)
          ((derivedPullback e).obj K) ≫
        (derivedPushforward (e' ≫ fZ')).map (pullDatum gW e' e gZ w₁ K K' φ)) :=
  isIso_comp_iff_of_paste _ _ _ _ _ _ _ _ _
    (derivedBaseChangeMap_comp gW e' e gZ fZ' fZ gT w₁ w₂ ((derivedPullback e).obj K))
    ((derivedPushforwardCompIso e' fZ').hom.naturality (pullDatum gW e' e gZ w₁ K K' φ)).symm
    ((derivedPushforward fZ').map_comp _ _)

/-- When the two units are invertible, the composition over the lower square is invertible
exactly when its version at `Re_*Le^*K` is. -/
theorem isIso_iff_of_isIso_unit (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z')))
    (φ : (derivedPullback gZ).obj K ⟶ K') [IsIso ((derivedAdjunction e).unit.app K)]
    [IsIso ((derivedAdjunction e').unit.app K')] :
    IsIso (derivedBaseChangeMap gZ fZ' fZ gT w₂ K ≫ (derivedPushforward fZ').map φ) ↔
      IsIso (derivedBaseChangeMap gZ fZ' fZ gT w₂
          ((derivedPushforward e).obj ((derivedPullback e).obj K)) ≫
        (derivedPushforward fZ').map (genBaseChange gW e' e gZ w₁ K K' φ)) := by
  refine isIso_iff_of_comm _
    ((derivedPullback gT).map ((derivedPushforward fZ).map ((derivedAdjunction e).unit.app K))) _
    ((derivedPushforward fZ').map ((derivedAdjunction e').unit.app K')) ?_
  exact chase_of_naturality _ _ _ _ _ _ _
    (derivedBaseChangeMap_naturality gZ fZ' fZ gT w₂ ((derivedAdjunction e).unit.app K))
    (((derivedPushforward fZ').map_comp _ _).symm.trans
      ((congrArg (derivedPushforward fZ').map
        (pullback_map_unit_comp_genBaseChange gW e' e gZ w₁ K K' φ)).trans
        ((derivedPushforward fZ').map_comp _ _)))

end General

end Stacks.Cohomology.BaseChangeCover
