module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.NatIso

/-!
# Diagram chases for the target identification of [Stacks, Tag 0G8K]

The identification
`AlgebraicGeometry.RelativeDualitySituation.exists_pushedPairing_eq_relativeCupProduct`
of the pushed pairings of the graded pieces is a composite of several commutative diagrams in
derived categories of modules. This file isolates the purely categorical steps: each lemma states
the outcome of a chase in an arbitrary category, with every morphism and every relation a
hypothesis, so that the concrete instances are obtained by application rather than by rewriting
inside derived categories.

It also records congruence lemmas for heterogeneous equality of images under functors, of
components of natural transformations and of the morphisms of `asIso`, which complement
`CategoryTheory.heq_comp`.

## Main results

* `Stacks.GradedTargetChase.relativeCupProduct_chase`
* `Stacks.GradedTargetChase.topPiece_chase`
* `Stacks.GradedTargetChase.trace_chase`
* `CategoryTheory.Functor.heq_map`, `CategoryTheory.NatTrans.heq_app`

## Implementation notes

The concrete derived categories involved admit several definitionally equal but syntactically
different descriptions. Stating each chase abstractly keeps every comparison of two descriptions
at the level of objects or of single morphisms, where it is cheap.

## References

* [Stacks, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.GradedTargetChase

/-- The diagram chase identifying the comparison of the degreewise and the derived direct image
with the shift isomorphisms of a single complex (used for
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardComparisonQ_singleShift`). -/
theorem singleShift_chase {CX CY DX DY : Type*} [Category CX] [Category CY] [Category DX]
    [Category DY] (P : CX ⥤ CY) (QX : CX ⥤ DX) (QY : CY ⥤ DY) (Rf : DX ⥤ DY)
    (ShCn ShC2n : CY ⥤ CY) (ShDn ShD2n : DY ⥤ DY)
    {W2 S0n : CX} {S0 Sn : CX} {S0' Sn' Tm : CY} {QS0n : DX}
    (σ : W2 ⟶ S0n) (csQX : QX.obj S0n ⟶ QS0n) (csRf : Rf.obj QS0n ⟶ ShDn.obj (Rf.obj (QX.obj S0)))
    (c : ∀ K : CX, QY.obj (P.obj K) ⟶ Rf.obj (QX.obj K))
    (csPn : P.obj S0n ⟶ ShCn.obj (P.obj S0)) (csP2n : P.obj W2 ⟶ ShC2n.obj (P.obj Sn))
    (m0 : P.obj S0 ⟶ S0') (m0inv : S0' ⟶ P.obj S0) (mn : P.obj Sn ⟶ Sn')
    (t1 : ShCn.obj S0' ⟶ Tm) (t2 : Tm ⟶ ShC2n.obj Sn')
    (csQn : QY.obj (ShCn.obj (P.obj S0)) ⟶ ShDn.obj (QY.obj (P.obj S0)))
    (csQn' : QY.obj (ShCn.obj S0') ⟶ ShDn.obj (QY.obj S0'))
    (csQn'inv : ShDn.obj (QY.obj S0') ⟶ QY.obj (ShCn.obj S0'))
    (csQ2n : QY.obj (ShC2n.obj (P.obj Sn)) ⟶ ShD2n.obj (QY.obj (P.obj Sn)))
    (csQ2n' : QY.obj (ShC2n.obj Sn') ⟶ ShD2n.obj (QY.obj Sn'))
    (sFQ0inv : QX.obj S0 ⟶ QX.obj S0) (sFQn : QY.obj Sn' ⟶ QY.obj Sn')
    (dhom : QY.obj S0' ⟶ Rf.obj (QX.obj S0)) (dinv : Rf.obj (QX.obj S0) ⟶ QY.obj S0')
    (shDhom : ShDn.obj (QY.obj S0') ⟶ QY.obj Tm) (shDinv : QY.obj Tm ⟶ ShD2n.obj (QY.obj Sn'))
    (F1 : QY.map (P.map σ) ≫ c S0n = c W2 ≫ Rf.map (QX.map σ))
    (F2 : c S0n ≫ Rf.map csQX ≫ csRf = QY.map csPn ≫ csQn ≫ ShDn.map (c S0))
    (F3 : dhom = QY.map m0inv ≫ c S0) (Hd : dhom ≫ dinv = 𝟙 _) (Hm : m0 ≫ m0inv = 𝟙 _)
    (h0 : Rf.map sFQ0inv = 𝟙 _) (h1 : sFQn = 𝟙 _)
    (F4 : QY.map (ShCn.map m0) ≫ csQn' = csQn ≫ ShDn.map (QY.map m0))
    (F5 : shDhom = csQn'inv ≫ QY.map t1) (Hcs : csQn' ≫ csQn'inv = 𝟙 _)
    (F6 : shDinv = QY.map t2 ≫ csQ2n')
    (F7 : P.map σ ≫ csPn ≫ ShCn.map m0 ≫ t1 ≫ t2 = csP2n ≫ ShC2n.map mn)
    (F8 : QY.map (ShC2n.map mn) ≫ csQ2n' = csQ2n ≫ ShD2n.map (QY.map mn)) :
    c W2 ≫ Rf.map (QX.map σ ≫ csQX) ≫ csRf ≫ ShDn.map (Rf.map sFQ0inv ≫ dinv) ≫ shDhom ≫
        shDinv ≫ ShD2n.map sFQn =
      QY.map csP2n ≫ csQ2n ≫ ShD2n.map (QY.map mn) := by
  have hc : c S0 ≫ dinv = QY.map m0 := by
    rw [← Category.id_comp (c S0), ← QY.map_id, ← Hm, QY.map_comp, Category.assoc,
      Category.assoc, ← reassoc_of% F3, Hd, Category.comp_id]
  subst F5 F6
  simp only [h0, h1, Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc]
  rw [← reassoc_of% F1, reassoc_of% F2, ← ShDn.map_comp_assoc, hc, ← reassoc_of% F4,
    reassoc_of% Hcs, ← F8]
  simp only [← Functor.map_comp_assoc, ← F7]

/-- The diagram chase rewriting the inclusion of the top piece along the factorization
`Rι ⋙ Rπ ≅ RF` (used for `AlgebraicGeometry.Scheme.Hom.map_singleShiftTwoMulIso_comp_topPiece`). -/
theorem topPiece_chase {DX DX' DS : Type*} [Category DX] [Category DX'] [Category DS]
    (Rι : DX ⥤ DX') (Rπ : DX' ⥤ DS) (RF : DX ⥤ DS) (cmpF : Rι ⋙ Rπ ≅ RF)
    (ShX'n : DX' ⥤ DX') (ShSn : DS ⥤ DS)
    {QW F0 F0n : DX} {B T E U V : DX'}
    (θ : QW ⟶ F0n) (csRF : RF.obj F0n ⟶ ShSn.obj (RF.obj F0))
    (csComp : Rπ.obj (Rι.obj F0n) ⟶ ShSn.obj (Rπ.obj (Rι.obj F0)))
    (csRι : Rι.obj F0n ⟶ ShX'n.obj (Rι.obj F0))
    (csRπ : ∀ K : DX', Rπ.obj (ShX'n.obj K) ⟶ ShSn.obj (Rπ.obj K))
    (csRπinv : ShSn.obj (Rπ.obj B) ⟶ Rπ.obj (ShX'n.obj B))
    (eh : RF.obj F0 ⟶ Rπ.obj (Rι.obj F0)) (y : Rι.obj F0 ⟶ B) (ρ : ShX'n.obj B ⟶ T)
    (τ : T ⟶ E) (cW : U ⟶ Rι.obj QW) (cWinv : Rι.obj QW ⟶ U) (q : U ⟶ T) (tq : U ⟶ V)
    (csQΩ : V ⟶ E) (topIncl : RF.obj F0n ⟶ Rπ.obj E)
    (G0 : topIncl = (csRF ≫ ShSn.map (eh ≫ Rπ.map y) ≫ csRπinv ≫ Rπ.map ρ) ≫ Rπ.map τ)
    (G2 : eh = cmpF.inv.app F0)
    (G1 : csComp ≫ ShSn.map (cmpF.hom.app F0) = cmpF.hom.app F0n ≫ csRF)
    (Gc : csComp = Rπ.map csRι ≫ csRπ (Rι.obj F0))
    (G4 : Rπ.map (ShX'n.map y) ≫ csRπ B = csRπ (Rι.obj F0) ≫ ShSn.map (Rπ.map y))
    (G4' : csRπ B ≫ csRπinv = 𝟙 _)
    (G5 : cW ≫ Rι.map θ ≫ csRι ≫ ShX'n.map y ≫ ρ = q) (hc : cWinv ≫ cW = 𝟙 _)
    (G6 : tq ≫ csQΩ = q ≫ τ) :
    RF.map θ ≫ topIncl = cmpF.inv.app QW ≫ Rπ.map (cWinv ≫ tq ≫ csQΩ) := by
  subst G0 Gc G2
  have G1' : csRF ≫ ShSn.map (cmpF.inv.app F0) = cmpF.inv.app F0n ≫
      Rπ.map csRι ≫ csRπ (Rι.obj F0) := by
    rw [← cancel_epi (cmpF.hom.app F0n), ← reassoc_of% G1, ← ShSn.map_comp,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    simp only [Functor.comp_obj, Functor.map_id, Category.comp_id]
  have hn : RF.map θ ≫ cmpF.inv.app F0n = cmpF.inv.app QW ≫ Rπ.map (Rι.map θ) :=
    cmpF.inv.naturality θ
  have key : Rι.map θ ≫ csRι ≫ ShX'n.map y ≫ ρ ≫ τ = cWinv ≫ tq ≫ csQΩ := by
    rw [G6, ← G5]
    simp only [Category.assoc, reassoc_of% hc]
  rw [← key]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% G1', reassoc_of% hn, ← reassoc_of% G4, reassoc_of% G4']

/-- A shifted composite under a functor commuting with the shifts, reassociated. -/
theorem shift_map_comp_chase {C D : Type*} [Category C] [Category D] (Q : C ⥤ D) (ShC : C ⥤ C)
    (ShD : D ⥤ D) {A₀ A B E : C} (a : A₀ ⟶ ShC.obj A) (b : A ⟶ B) (c : B ⟶ E)
    (csA : Q.obj (ShC.obj A) ⟶ ShD.obj (Q.obj A)) (csE : Q.obj (ShC.obj E) ⟶ ShD.obj (Q.obj E))
    (N : Q.map (ShC.map (b ≫ c)) ≫ csE = csA ≫ ShD.map (Q.map (b ≫ c))) :
    Q.map (a ≫ ShC.map (b ≫ c)) ≫ csE = (Q.map a ≫ csA ≫ ShD.map (Q.map b)) ≫ ShD.map (Q.map c) :=
        by
  rw [Q.map_comp, Category.assoc, N]
  simp only [Functor.map_comp, Category.assoc]

/-- Inserting an inverse pair `cW ≫ cWinv = 𝟙` into a composite rewritten by `S1`. -/
theorem key_chase {C : Type*} [Category C] {K' U1 U2 U3 V E1 RT RT2 RW : C}
    {x1 : K' ⟶ U1} {x2 : U1 ⟶ U2} {x3 : U2 ⟶ U3} {y1 : U1 ⟶ V}
    {y2 : V ⟶ U2} {cW : V ⟶ RW} {cWinv : RW ⟶ V} {AB : K' ⟶ E1} {μι : E1 ⟶ RT}
    {rt : RT ⟶ RT2} {rq : RT2 ⟶ RW} {rφ : RT ⟶ RW}
    (e12 : x2 = y1 ≫ y2) (hcW : cW ≫ cWinv = 𝟙 _) (S1 : x1 ≫ y1 ≫ cW = AB ≫ μι ≫ rt ≫ rq)
    (hφ : rt ≫ rq = rφ) :
    x1 ≫ x2 ≫ x3 = (AB ≫ μι) ≫ rφ ≫ cWinv ≫ y2 ≫ x3 := by
  rw [e12, ← hφ]
  calc x1 ≫ (y1 ≫ y2) ≫ x3 = (x1 ≫ y1 ≫ cW) ≫ cWinv ≫ y2 ≫ x3 := by
        simp only [Category.assoc, reassoc_of% hcW]
    _ = _ := by rw [S1]; simp only [Category.assoc]

/-- Congruence of the middle factor of a triple composite. -/
theorem comp_comp_congr {C : Type*} [Category C] {P Q R N : C} {μ : P ⟶ Q} {a b : Q ⟶ R}
    {s : R ⟶ N} (h : a = b) : μ ≫ a ≫ s = μ ≫ b ≫ s := by rw [h]

/-- Postcomposing an equation of the form `μ ≫ m = a ≫ b ≫ c ≫ d ≫ e ≫ f` with `s`. -/
theorem comp_tail_assoc {C : Type*} [Category C] {P Q R A1 A2 A3 A4 A5 N : C} {μ : P ⟶ Q}
    {m : Q ⟶ R} {a : P ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3} {d : A3 ⟶ A4} {e : A4 ⟶ A5}
    {f : A5 ⟶ R} (s : R ⟶ N) (h : μ ≫ m = a ≫ b ≫ c ≫ d ≫ e ≫ f) :
    μ ≫ m ≫ s = a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ s := by
  rw [← Category.assoc, h]; simp only [Category.assoc]

/-- The chase through the inclusion of the top piece and the trace: from `X = a ≫ b ≫ c`,
`t ≫ s = c ≫ Tr` and `b ≫ t = w ≫ v` one gets `X ≫ Tr = a ≫ w ≫ v ≫ s`. -/
theorem trace_chase {C : Type*} [Category C] {O0 O1 O2 O3 P Q N : C} {X : O0 ⟶ O3}
    {a : O0 ⟶ O1} {b : O1 ⟶ O2} {c : O2 ⟶ O3} {Tr : O3 ⟶ N} {t : O2 ⟶ P} {s : P ⟶ N}
    {w : O1 ⟶ Q} {v : Q ⟶ P}
    (H1 : X = a ≫ b ≫ c) (hs : t ≫ s = c ≫ Tr) (T3 : b ≫ t = w ≫ v) :
    X ≫ Tr = a ≫ w ≫ v ≫ s := by
  rw [H1, Category.assoc, Category.assoc, ← hs, reassoc_of% T3]

/-- Replacing the last factor of a composite by an equal morphism. -/
theorem comp_tail_swap {C : Type*} [Category C] {P0 P1 P2 P3 N : C} {L : P0 ⟶ N} {a : P0 ⟶ P1}
    {b : P1 ⟶ P2} {c : P2 ⟶ P3} {X X' Y : P3 ⟶ N} (G : L = a ≫ b ≫ c ≫ X) (H : Y = X')
    (e : X = X') : L = a ≫ b ≫ c ≫ Y := by
  rw [G, e, H]

/-- The reassociation used to combine the naive cup product with the comparison maps. -/
theorem naiveCup_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : C}
    {t : P₀ ⟶ P₁} {n : P₁ ⟶ P₂} {c : P₂ ⟶ Q₃} {m : Q₃ ⟶ Q₄} {nq : P₁ ⟶ P₃} {cW : P₃ ⟶ Q₄}
    {U : P₀ ⟶ Q₁} {a : P₀ ⟶ P₄} {b : P₄ ⟶ Q₁} {r : Q₁ ⟶ Q₂} {k : Q₂ ⟶ Q₃}
    (h3 : t ≫ n ≫ c = U ≫ r ≫ k) (e1 : nq ≫ cW = n ≫ c ≫ m) (hU : U = a ≫ b) :
    t ≫ nq ≫ cW = (a ≫ b) ≫ r ≫ k ≫ m := by
  rw [e1, reassoc_of% h3, hU]

/-- The relative cup product along `π ∘ ι`, transported along an isomorphism `Rι ⋙ Rπ ≅ Rg`
which is compatible with the relative cup products ([Stacks, Tag 0FP6]), applied to morphisms
into `Rι` and out of the tensor product. -/
theorem relativeCupProduct_chase {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
    (TX : CX ⥤ CX ⥤ CX) (TY : CY ⥤ CY ⥤ CY) (TZ : CZ ⥤ CZ ⥤ CZ) (Rι : CX ⥤ CY) (Rπ : CY ⥤ CZ)
    (Rg : CX ⥤ CZ)
    (μπ : ∀ K L : CY, (TZ.obj (Rπ.obj K)).obj (Rπ.obj L) ⟶ Rπ.obj ((TY.obj K).obj L))
    (μι : ∀ K L : CX, (TY.obj (Rι.obj K)).obj (Rι.obj L) ⟶ Rι.obj ((TX.obj K).obj L))
    (μg : ∀ K L : CX, (TZ.obj (Rg.obj K)).obj (Rg.obj L) ⟶ Rg.obj ((TX.obj K).obj L))
    (cmp : Rι ⋙ Rπ ≅ Rg)
    (hnat : ∀ {K K' L L' : CY} (k : K ⟶ K') (l : L ⟶ L'),
      (Functor.uncurry.obj TZ).map (Rπ.map k ×ₘ Rπ.map l) ≫ μπ K' L' =
        μπ K L ≫ Rπ.map ((Functor.uncurry.obj TY).map (k ×ₘ l)))
    (hcomp : ∀ K L : CX, (Functor.uncurry.obj TZ).map (cmp.hom.app K ×ₘ cmp.hom.app L) ≫ μg K L =
      μπ (Rι.obj K) (Rι.obj L) ≫ Rπ.map (μι K L) ≫ cmp.hom.app ((TX.obj K).obj L))
    {K₁ L₁ : CY} {K L M : CX} {N : CY} (a : K₁ ⟶ Rι.obj K) (b : L₁ ⟶ Rι.obj L)
    (φ : (TX.obj K).obj L ⟶ M) (z : Rι.obj M ⟶ N) :
    μπ K₁ L₁ ≫ Rπ.map ((((TY.map a).app L₁ ≫ (TY.obj (Rι.obj K)).map b) ≫ μι K L) ≫
        Rι.map φ ≫ z) =
      (TZ.map (Rπ.map a ≫ cmp.hom.app K)).app (Rπ.obj L₁) ≫
        (TZ.obj (Rg.obj K)).map (Rπ.map b ≫ cmp.hom.app L) ≫ μg K L ≫ Rg.map φ ≫
          cmp.inv.app M ≫ Rπ.map z := by
  have h1 := hnat a b
  have h2 := hcomp K L
  simp only [Functor.uncurry_obj_map, Functor.map_comp, Category.assoc] at h1 h2
  have h3 : cmp.inv.app ((TX.obj K).obj L) ≫ Rπ.map (Rι.map φ) = Rg.map φ ≫ cmp.inv.app M :=
    (cmp.inv.naturality φ).symm
  have hx : (TZ.obj (Rπ.obj (Rι.obj K))).map (Rπ.map b) ≫
      (TZ.map (cmp.hom.app K)).app (Rπ.obj (Rι.obj L)) =
      (TZ.map (cmp.hom.app K)).app (Rπ.obj L₁) ≫ (TZ.obj (Rg.obj K)).map (Rπ.map b) :=
    (TZ.map (cmp.hom.app K)).naturality (Rπ.map b)
  have h2' : μπ (Rι.obj K) (Rι.obj L) ≫ Rπ.map (μι K L) =
      (TZ.map (cmp.hom.app K)).app (Rπ.obj (Rι.obj L)) ≫
        (TZ.obj (Rg.obj K)).map (cmp.hom.app L) ≫ μg K L ≫ cmp.inv.app _ := by
    rw [reassoc_of% h2]; simp
  simp only [Functor.map_comp, Category.assoc, NatTrans.comp_app]
  rw [← reassoc_of% h1, reassoc_of% h2', reassoc_of% hx, reassoc_of% h3]


end Stacks.GradedTargetChase

namespace CategoryTheory

/-- Images of heterogeneously equal morphisms under equal functors are heterogeneously equal. -/
theorem Functor.heq_map {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D} (hF : F = F')
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') :
    F.map f ≍ F'.map f' := by
  subst hF hX hY; cases hf; rfl

/-- Components of heterogeneously equal natural transformations at equal objects are
heterogeneously equal. -/
theorem NatTrans.heq_app {C D : Type*} [Category* C] [Category* D] {F F' G G' : C ⥤ D}
    (hF : F = F') (hG : G = G') {α : F ⟶ G} {α' : F' ⟶ G'} (hα : α ≍ α') {X X' : C}
    (hX : X = X') : α.app X ≍ α'.app X' := by
  subst hF hG hX; cases hα; rfl

/-- The morphism of the isomorphism `asIso f` is `f`. -/
theorem asIso_hom_heq {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) {hf : IsIso f} :
    (asIso f).hom ≍ f := HEq.rfl

/-- The inverse of the inverse of the isomorphism `asIso f` is `f`. -/
theorem asIso_symm_inv_heq {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) {hf : IsIso f} :
    (asIso f).symm.inv ≍ f := HEq.rfl

end CategoryTheory
