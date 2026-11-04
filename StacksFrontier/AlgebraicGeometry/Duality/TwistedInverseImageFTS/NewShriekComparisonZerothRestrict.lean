module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictModels
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineChartsTransitivity
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# `H⁰(g_new^! 𝒪_Y) ≅ M|_X` restricted to an open

Let `g : X ⟶ Y` be a locally quasi-finite morphism of schemes of finite type over a Noetherian
base with a factorization `X ⟶ T ⟶ Y` (open immersion, then finite), and `h : X' ⟶ X` an open
immersion. The identification `H⁰(g^! 𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` of [Stacks, Tag 0BUL] restricts along
`h` to the one for `h ≫ g` and the restricted factorization; so does its composite with
`H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)` through an identification `g^! K ≅ ω`. The comparison of the
standard and the locally small model of `D(𝒪_X)` is the one of `DerivedRestrictModels`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.restrict_upperShriekStructureSheafZerothIso`.
* `Stacks.Duality.NormalizedOnOpens.restrict_upperShriekStructureSheafZerothIsoOfIso_trans'`.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)

section RestrictGeneric

variable {S₀ : Scheme.{u}} [IsNoetherian S₀] {A' A B : FTS S₀} (h : A' ⟶ A) [IsOpenImmersion h.left]
  {g : A ⟶ B}

namespace NormalizedOnOpens

open UpperShriekDuality TwistedInverseImageDuality
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

/-- `H⁰(g^! 𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` at the compactification of the factorization. -/
theorem upperShriekStructureSheafZerothIso_compactification_hom (F : OpenFiniteFactorization g) :
    (upperShriekStructureSheafZerothIso F F.compactification).hom =
      (DerivedCategory.homologyFunctor A.left.Modules 0).map
          ((derivedRestrictAdjointIso F.immersion).inv.app
            ((FiniteTrace.twisted F.toBase).obj
              (DerivedPushforward.derivedStructureSheaf B.left)).obj) ≫
        (((Scheme.Modules.restrictFunctor F.immersion).mapDerivedCategoryHomologyIso 0).app
          ((FiniteTrace.twisted F.toBase).obj
            (DerivedPushforward.derivedStructureSheaf B.left)).obj).hom := by
  rw [upperShriekStructureSheafZerothIso_hom, upperShriekPlusIso_refl,
    ← restrictedDerivedRestrictAdjointIso_inv_app_hom]
  exact congrArg (fun t => (DerivedCategory.homologyFunctor A.left.Modules 0).map t ≫ _)
    (Category.id_comp _)

/-- `G.map x.inv = y.hom` gives `G.map x.hom = y.inv`. -/
theorem map_hom_eq_inv_of_map_inv_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {a b : 𝒞} (x : a ≅ b) (y : G.obj b ≅ G.obj a) (h : G.map x.inv = y.hom) :
    G.map x.hom = y.inv := by
  rw [← cancel_mono y.hom, Iso.inv_hom_id, ← h, ← G.map_comp, Iso.hom_inv_id, G.map_id]

/-- `pullModelConj` read through the comparison of the models is `pullModelIso`. -/
theorem comparison_map_pullModelConj_hom_app {A₀ B₀ : Scheme.{u}} (g₀ : A₀ ⟶ B₀)
    (Q : DerivedCategory B₀.Modules) :
    (comparison A₀).functor.map ((pullModelConj g₀).hom.app Q) =
      (pullModelIso g₀).inv.app ((comparison B₀).inverse.obj Q) := by
  have h := pullModelConj_inv_app_comp_counit g₀ Q
  have h' : (comparison A₀).functor.map ((pullModelConj g₀).inv.app Q) =
      (pullModelIso g₀).hom.app ((comparison B₀).inverse.obj Q) :=
    (Category.comp_id _).symm.trans (h.trans ((congrArg (_ ≫ ·)
      ((Stacks.Duality.derivedPullback g₀).map_id _)).trans (Category.comp_id _)))
  exact map_hom_eq_inv_of_map_inv_eq (comparison A₀).functor ((pullModelConj g₀).app Q)
    ((pullModelIso g₀).app ((comparison B₀).inverse.obj Q)) h'

/-- `c.inv ≫ x ≫ s = y` from `x ≫ s = c.hom ≫ y`. -/
theorem inv_comp_comp_of_comp_eq {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (c₀ : a ≅ b)
    (x : a ⟶ c) (s : c ⟶ d) (y : b ⟶ d) (h : x ≫ s = c₀.hom ≫ y) : c₀.inv ≫ x ≫ s = y := by
  rw [h, Iso.inv_hom_id_assoc]

/-- `H⁰` of `pullModelConj` at the standard model, read at the locally small model. -/
theorem homology_map_pullModelConj_hom_app {A₀ B₀ : Scheme.{u}} (g₀ : A₀ ⟶ B₀)
    (Q : DerivedCategory B₀.Modules) :
    (PerfectApproximation.homologyStandardIso
        ((Stacks.Duality.derivedPullback g₀).obj Q) 0).inv ≫
      (DerivedCategory.homologyFunctor A₀.Modules 0).map
        ((pullModelIso g₀).inv.app ((comparison B₀).inverse.obj Q)) ≫
      (PerfectApproximation.homologyStandardIso ((pull g₀).obj ((comparison B₀).inverse.obj Q))
        0).hom =
    (@DerivedCategory.homologyFunctor A₀.Modules _ _ (PerfectApproximation.standardModel A₀) 0).map
      ((pullModelConj g₀).hom.app Q) := by
  have N := PerfectApproximation.homologyStandardIso_naturality ((pullModelConj g₀).hom.app Q) 0
  exact inv_comp_comp_of_comp_eq _ _ _ _ ((congrArg
    (fun t => (DerivedCategory.homologyFunctor A₀.Modules 0).map t ≫ _)
    (comparison_map_pullModelConj_hom_app g₀ Q)).symm.trans N)

/-- A functor on a composite of four morphisms. -/
theorem map_comp₄ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a b c d e : 𝒞}
    (x₁ : a ⟶ b) (x₂ : b ⟶ c) (x₃ : c ⟶ d) (x₄ : d ⟶ e) :
    G.map (x₁ ≫ x₂ ≫ x₃ ≫ x₄) = G.map x₁ ≫ G.map x₂ ≫ G.map x₃ ≫ G.map x₄ := by
  simp

/-- A functor on a composite of three morphisms. -/
theorem map_comp₃ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a b c d : 𝒞}
    (x₁ : a ⟶ b) (x₂ : b ⟶ c) (x₃ : c ⟶ d) :
    G.map (x₁ ≫ x₂ ≫ x₃) = G.map x₁ ≫ G.map x₂ ≫ G.map x₃ := by
  simp

/-- A functor on a composite `(x₁ ≫ x₂) ≫ x₃`. -/
theorem map_comp₃' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a b c d : 𝒞}
    (x₁ : a ⟶ b) (x₂ : b ⟶ c) (x₃ : c ⟶ d) :
    G.map ((x₁ ≫ x₂) ≫ x₃) = G.map x₁ ≫ G.map x₂ ≫ G.map x₃ := by
  simp

/-- Solving `hs ≫ p = m ≫ q ≫ t` for `q`. -/
theorem eq_inv_comp_comp_comp_inv {𝒞 : Type*} [Category 𝒞] {a b c d e : 𝒞} (hs : a ⟶ b)
    (p : b ⟶ e) (m : a ≅ c) (q : c ⟶ d) (t : d ≅ e) (h : hs ≫ p = m.hom ≫ q ≫ t.hom) :
    q = m.inv ≫ hs ≫ p ≫ t.inv := by
  rw [reassoc_of% h]; simp

/-- **`H⁰` and restriction along an open immersion, at the locally small model**, read through
the standard model. -/
theorem homology_derivedRestrictAdjointIso_inv_app {T X : Scheme.{u}} (i : X ⟶ T)
    [IsOpenImmersion i] (E : DerivedCategory T.Modules) :
    (DerivedCategory.homologyFunctor X.Modules 0).map ((derivedRestrictAdjointIso i).inv.app E) ≫
      ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).hom.app E =
    (DerivedCategory.homologyFunctor X.Modules 0).map
        ((StacksDraft.DerivedModel.derivedPullbackModelIso i.toLRSHom.toShHom).inv.app E) ≫
      (PerfectApproximation.homologyStandardIso ((pull i).obj E) 0).hom ≫
      (homologyPullIsoOfOpenImmersion i E).hom ≫
      (Scheme.Modules.restrictFunctor i).map
        (PerfectApproximation.homologyStandardIso E 0).inv := by
  have hX := homology_derivedRestrictIsoDerivedPullback_models i 0 E
  exact eq_inv_comp_comp_comp_inv _ _
    ((DerivedCategory.homologyFunctor X.Modules 0).mapIso
      ((StacksDraft.DerivedModel.derivedPullbackModelIso i.toLRSHom.toShHom).app E)) _
    ((Scheme.Modules.restrictFunctor i).mapIso (PerfectApproximation.homologyStandardIso E 0))
    (hX.trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm))

/-- The chase behind `restrict_upperShriekStructureSheafZerothIso`. -/
theorem restrict_upperShriekStructureSheafZerothIso_chase {𝒞 : Type*} [Category 𝒞]
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ y₁ y₂ y₃ y₄ y₆ y₇ z₀ : 𝒞}
    (rs : x₀ ⟶ x₁) (rl : x₁ ⟶ x₅) (c : x₅ ⟶ x₆) (rpi : x₁ ⟶ x₂) (rsP : x₂ ⟶ x₃) (rhi : x₃ ⟶ x₄)
    (rri : x₄ ⟶ x₅) (rφ : x₀ ⟶ x₃) (c' : x₄ ⟶ z₀) (rk : z₀ ⟶ x₆)
    (b1 : x₀ ⟶ y₁) (b1' : y₁ ⟶ x₀) (b2 : y₁ ⟶ y₂) (b3 : y₂ ⟶ y₃) (lk : y₃ ⟶ x₆)
    (pk : y₃ ⟶ y₄) (sk : y₄ ⟶ y₇) (hk : y₇ ⟶ z₀) (Hφk : y₂ ⟶ y₇) (Hpφ : y₁ ⟶ y₆) (Hc : y₆ ⟶ y₇)
    (Hm : y₇ ⟶ y₂) (Hci : y₇ ⟶ y₆) (hP : y₆ ⟶ x₃)
    (hrl : rl = rpi ≫ rsP ≫ rhi ≫ rri) (hF7 : rs ≫ rpi ≫ rsP = rφ)
    (hlk : lk = pk ≫ sk ≫ hk ≫ rk) (hF10 : b3 ≫ pk ≫ sk = Hφk) (hb2 : b2 = Hpφ ≫ Hc ≫ Hm)
    (hmφ : Hm ≫ Hφk = 𝟙 _) (htr : hk = Hci ≫ hP ≫ rhi ≫ c') (hci : Hc ≫ Hci = 𝟙 _)
    (hnat : Hpφ ≫ hP = b1' ≫ rφ) (hb1 : b1 ≫ b1' = 𝟙 _)
    (hrFC : rri ≫ c = c' ≫ rk) :
    rs ≫ rl ≫ c = b1 ≫ b2 ≫ b3 ≫ lk := by
  subst hrl hlk hb2 htr
  have e1 : b3 ≫ pk ≫ sk ≫ Hci ≫ hP ≫ rhi ≫ c' ≫ rk = Hφk ≫ Hci ≫ hP ≫ rhi ≫ c' ≫ rk := by
    rw [← hF10]; simp
  simp only [Category.assoc]
  rw [hrFC, reassoc_of% hF7, e1, reassoc_of% hmφ, reassoc_of% hci, reassoc_of% hnat,
    reassoc_of% hb1]

/-- A functor sends a composite equal to the identity to a composite equal to the identity. -/
private theorem map_comp_eq_id {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a b : 𝒞}
    {f : a ⟶ b} {g : b ⟶ a} (h : f ≫ g = 𝟙 a) : G.map f ≫ G.map g = 𝟙 (G.obj a) := by
  rw [← G.map_comp, h, G.map_id]

/-- **The `e`-free core of `restrict_upperShriekStructureSheafZerothIsoOfIso_trans`.** -/
theorem restrict_upperShriekStructureSheafZerothIso (F : OpenFiniteFactorization g) :
    (Scheme.Modules.restrictFunctor h.left).map
        (PerfectApproximation.homologyStandardIso
          ((upperShriekStd g F.compactification).obj
            ⟨structureStd B.left, plusCoh_structureStd B.left⟩) 0).inv ≫
      (Scheme.Modules.restrictFunctor h.left).map
        (upperShriekStructureSheafZerothIso F F.compactification).hom ≫
      (Scheme.Modules.restrictFunctorComp h.left F.immersion).inv.app (finiteZeroTwisted F) =
    (homologyPullIsoOfOpenImmersion h.left ((upperShriekStd g F.compactification).obj
        ⟨structureStd B.left, plusCoh_structureStd B.left⟩)).inv ≫
      (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).map
        ((upperShriekStdRestrictIso h g F.compactification).hom.app
          ⟨structureStd B.left, plusCoh_structureStd B.left⟩) ≫
      (PerfectApproximation.homologyStandardIso
          ((upperShriekStd (h ≫ g) (F.compactification.precompOpen h.left)).obj
            ⟨structureStd B.left, plusCoh_structureStd B.left⟩) 0).inv ≫
      (upperShriekStructureSheafZerothIso (F.precompOpen h rfl)
        (F.compactification.precompOpen h.left)).hom := by
  have hrl := (congrArg (Scheme.Modules.restrictFunctor h.left).map
    ((upperShriekStructureSheafZerothIso_compactification_hom F).trans
      (homology_derivedRestrictAdjointIso_inv_app F.immersion _))).trans (map_comp₄ _ _ _ _ _)
  have hF7 := (map_comp₃ _ _ _ _).symm.trans (congrArg (Scheme.Modules.restrictFunctor h.left).map
    (homology_map_pullModelConj_hom_app F.immersion
      ((FiniteTrace.twisted F.toBase).obj (DerivedPushforward.derivedStructureSheaf B.left)).obj))
  have hlk := (upperShriekStructureSheafZerothIso_compactification_hom (F.precompOpen h rfl)).trans
    (homology_derivedRestrictAdjointIso_inv_app (h.left ≫ F.immersion) _)
  have hF10 := homology_map_pullModelConj_hom_app (h.left ≫ F.immersion)
      ((FiniteTrace.twisted F.toBase).obj (DerivedPushforward.derivedStructureSheaf B.left)).obj
  have hb2 := congrArg (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).map
    (upperShriekStdRestrictIso_hom_app h g F.compactification
      ⟨structureStd B.left, plusCoh_structureStd B.left⟩) |>.trans (map_comp₃ _ _ _ _)
  have hmφ := map_comp_eq_id (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0)
    ((pullModelConj (h.left ≫ F.immersion)).inv_hom_id_app
      ((FiniteTrace.twisted F.toBase).obj
        (DerivedPushforward.derivedStructureSheaf B.left)).obj)
  have htr := (Iso.eq_comp_inv _).mpr (congrArg Iso.hom (homologyPullIsoOfOpenImmersion_comp h.left
    F.immersion ((comparison _).inverse.obj ((FiniteTrace.twisted F.toBase).obj
      (DerivedPushforward.derivedStructureSheaf B.left)).obj))) |>.trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
  have hci := map_comp_eq_id (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0)
    ((UpperShriekDuality.pullCompIso h.left F.immersion (h.left ≫ F.immersion) rfl).hom_inv_id_app
      ((comparison _).inverse.obj ((FiniteTrace.twisted F.toBase).obj
        (DerivedPushforward.derivedStructureSheaf B.left)).obj))
  have hnat := homologyPullIsoOfOpenImmersion_naturality h.left ((pullModelConj F.immersion).hom.app
      ((FiniteTrace.twisted F.toBase).obj (DerivedPushforward.derivedStructureSheaf B.left)).obj)
  have hb1 := (homologyPullIsoOfOpenImmersion h.left ((upperShriekStd g F.compactification).obj
        ⟨structureStd B.left, plusCoh_structureStd B.left⟩)).inv_hom_id
  have hrFC := ((Scheme.Modules.restrictFunctorComp h.left F.immersion).inv.naturality
    (PerfectApproximation.homologyStandardIso ((FiniteTrace.twisted F.toBase).obj
      (DerivedPushforward.derivedStructureSheaf B.left)).obj 0).inv)
  exact restrict_upperShriekStructureSheafZerothIso_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ hrl hF7 hlk hF10 hb2 hmφ htr hci hnat hb1 hrFC

/-- `f ≫ g' = Lh(Φ⁻¹) ≫ u` from `Lh(Φ) ≫ f = u ≫ Φ'`. -/
theorem pull_restrict_chase {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (p : a ≅ b)
    (f : b ⟶ c) (u : a ⟶ d) (φ : d ≅ c) (h : p.hom ≫ f = u ≫ φ.hom) :
    f ≫ φ.inv = p.inv ≫ u := by
  rw [← cancel_epi p.hom, ← Category.assoc, h]
  simp

/-- The chase behind `restrict_upperShriekStructureSheafZerothIsoOfIso_trans`. -/
theorem restrict_trans_chase {𝒞 : Type*} [Category 𝒞] {a b c d d' e e₂ x₁ x₂ z : 𝒞}
    (rp : a ⟶ b) (rs : b ⟶ x₁) (ru : x₁ ⟶ x₂) (cc : x₂ ⟶ z) (q : c ⟶ a) (qi : a ⟶ c)
    (f : c ⟶ d) (g' : d ⟶ e) (pp : c ⟶ d') (u : d' ⟶ e) (hE : d' ⟶ b) (hEi : b ⟶ d')
    (s : e ⟶ e₂) (t : e₂ ⟶ z)
    (H1 : f ≫ g' = pp ≫ u) (H2 : pp ≫ hE = q ≫ rp) (H3 : rs ≫ ru ≫ cc = hEi ≫ u ≫ s ≫ t)
    (hq : qi ≫ q = 𝟙 _) (hEE : hE ≫ hEi = 𝟙 _) :
    (rp ≫ rs ≫ ru) ≫ cc = (qi ≫ f) ≫ (g' ≫ s) ≫ t := by
  have hp : pp = q ≫ rp ≫ hEi := by rw [← reassoc_of% H2, hEE, Category.comp_id]
  simp only [Category.assoc]
  rw [reassoc_of% H1, H3, hp]
  simp only [Category.assoc]
  rw [reassoc_of% hq]

/-- **`H⁰(g_new^! 𝒪_Y) ≅ M|_X` restricts to opens** (R-core). -/
theorem restrict_upperShriekStructureSheafZerothIsoOfIso_trans (F : OpenFiniteFactorization g)
    {K : Std B.left} (hK : IsDualizing K) {ω : Std A.left}
    (e : upperShriekDualizing g F.compactification hK ≅ ω) :
    (Scheme.Modules.restrictFunctor h.left).mapIso
        (upperShriekStructureSheafZerothIsoOfIso g F.compactification hK e ≪≫
          upperShriekStructureSheafZerothIso F F.compactification) ≪≫
      ((Scheme.Modules.restrictFunctorComp h.left F.immersion).app (finiteZeroTwisted F)).symm =
    ((homologyPullIsoOfOpenImmersion h.left _).symm ≪≫
      (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).mapIso
        ((fNewShriekRestrictIso h.left g.left (h ≫ g).left rfl ω K).app (structureStd B.left))) ≪≫
      upperShriekStructureSheafZerothIsoOfIso (h ≫ g) (F.compactification.precompOpen h.left) hK
        ((upperShriekDualizingRestrictIso h g F.compactification hK).symm ≪≫
          (pull h.left).mapIso e) ≪≫
      upperShriekStructureSheafZerothIso (F.precompOpen h rfl)
        (F.compactification.precompOpen h.left) := by
  have H1 := upperShriekStdIsoFNewShriekOfIso_restrict h g F.compactification hK e
    ⟨structureStd B.left, plusCoh_structureStd B.left⟩
  have H1' := (Functor.map_comp _ _ _).symm.trans ((congrArg
      (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).map
      (pull_restrict_chase ((pull h.left).mapIso
        ((upperShriekStdIsoFNewShriekOfIso g F.compactification hK e).app
          ⟨structureStd B.left, plusCoh_structureStd B.left⟩)) _ _
        ((upperShriekStdIsoFNewShriekOfIso (h ≫ g) (F.compactification.precompOpen h.left) hK
          ((upperShriekDualizingRestrictIso h g F.compactification hK).symm ≪≫
            (pull h.left).mapIso e)).app
              ⟨structureStd B.left, plusCoh_structureStd B.left⟩) H1)).trans
      (Functor.map_comp _ _ _))
  have H2 := homologyPullIsoOfOpenImmersion_naturality h.left
    ((upperShriekStdIsoFNewShriekOfIso g F.compactification hK e).inv.app
      ⟨structureStd B.left, plusCoh_structureStd B.left⟩)
  have H3 := restrict_upperShriekStructureSheafZerothIso h F
  have key := restrict_trans_chase _ _ _ _
    (homologyPullIsoOfOpenImmersion h.left _).hom (homologyPullIsoOfOpenImmersion h.left _).inv
    _ _ _ _ (homologyPullIsoOfOpenImmersion h.left _).hom
    (homologyPullIsoOfOpenImmersion h.left _).inv _ _ H1' H2 H3 (Iso.inv_hom_id _)
    (Iso.hom_inv_id _)
  ext1
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

/-- Cancelling `F(w)` against `F(w⁻¹)`. -/
theorem mapIso_trans_cancel {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟) {a : 𝒟}
    {x y z : 𝒞} {t : 𝒟} (p : a ≅ G.obj x) (b : x ≅ y) (w : y ≅ z) {c : G.obj y ≅ t}
    {c'' : G.obj z ≅ t} (h : c'' = G.mapIso w.symm ≪≫ c) :
    (p ≪≫ G.mapIso b) ≪≫ c = (p ≪≫ G.mapIso (b ≪≫ w)) ≪≫ c'' := by
  subst h
  ext1
  simp

/-- An identity component read through a functor. -/
theorem mapIso_app_refl_trans {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ] (Fn : 𝒟 ⥤ ℰ)
    (G : 𝒞 ⥤ 𝒟) (X : 𝒞) {t : ℰ} (c : Fn.obj (G.obj X) ≅ t) :
    Fn.mapIso ((Iso.refl G).app X) ≪≫ c = c := by
  ext1
  simp

/-- **`H⁰(g_new^! 𝒪_Y) ≅ M|_X` restricts to opens**, for any `g' = h ≫ g` and any complex `ω'`
with `ω' ≅ Lh^* ω`. -/
theorem restrict_upperShriekStructureSheafZerothIsoOfIso_trans' (F : OpenFiniteFactorization g)
    {g' : A' ⟶ B} (w : h ≫ g = g') {K : Std B.left} (hK : IsDualizing K)
    (hKb : DerivedCategoryB.IsBoundedBelow (dualizingQCoh hK).obj) {ω : Std A.left}
    {ω' : Std A'.left} (σ : ω' ≅ (pull h.left).obj ω)
    (e : upperShriekDualizing g F.compactification hK ≅ ω)
    (e' : upperShriekDualizing g' (F.precompOpen h w).compactification hK ≅ ω')
    (he : e' = (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison A'.left).inverse).mapIso
        ((upperShriekPlusCongr w.symm (F.precompOpen h w).compactification
          (F.compactification.precompOpen h.left)).app ⟨dualizingQCoh hK, hKb⟩) ≪≫
      (upperShriekDualizingRestrictIso h g F.compactification hK).symm ≪≫
        (pull h.left).mapIso e ≪≫ σ.symm) :
    (Scheme.Modules.restrictFunctor h.left).mapIso
        (upperShriekStructureSheafZerothIsoOfIso g F.compactification hK e ≪≫
          upperShriekStructureSheafZerothIso F F.compactification) ≪≫
      ((Scheme.Modules.restrictFunctorComp h.left F.immersion).app (finiteZeroTwisted F)).symm =
    ((homologyPullIsoOfOpenImmersion h.left _).symm ≪≫
      (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).mapIso
        ((fNewShriekRestrictIso h.left g.left g'.left
            (show h.left ≫ g.left = g'.left from congrArg (fun φ : A' ⟶ B => φ.left) w) ω K).app
            (structureStd B.left) ≪≫
          (Functor.isoWhiskerLeft (dualInto K).rightOp (Functor.isoWhiskerLeft (pull g'.left).op
            (dualIntoMapIso σ.symm))).app (structureStd B.left))) ≪≫
      upperShriekStructureSheafZerothIsoOfIso g' (F.precompOpen h w).compactification hK e' ≪≫
      upperShriekStructureSheafZerothIso (F.precompOpen h w)
        (F.precompOpen h w).compactification := by
  subst w he
  have hrefl : upperShriekPlusCongr (rfl : h ≫ g = h ≫ g) (F.precompOpen h rfl).compactification
      (F.compactification.precompOpen h.left) = Iso.refl _ :=
    upperShriekPlusIso_refl _ _
  have key := upperShriekStructureSheafZerothIsoOfIso_trans_dualizing (h ≫ g)
    (F.compactification.precompOpen h.left) hK
    ((upperShriekDualizingRestrictIso h g F.compactification hK).symm ≪≫ (pull h.left).mapIso e)
    σ.symm
  rw [Iso.trans_assoc] at key
  rw [hrefl, restrict_upperShriekStructureSheafZerothIsoOfIso_trans h F hK e]
  have k2 := (congrArg (upperShriekStructureSheafZerothIsoOfIso (h ≫ g)
      (F.precompOpen h rfl).compactification hK) (mapIso_app_refl_trans
        (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison A'.left).inverse)
        (upperShriekPlus (h ≫ g) (F.precompOpen h rfl).compactification) ⟨dualizingQCoh hK, hKb⟩
        ((upperShriekDualizingRestrictIso h g F.compactification hK).symm ≪≫
          (pull h.left).mapIso e ≪≫ σ.symm))).trans key
  exact mapIso_trans_cancel _ _ _ _
    (((congrArg (· ≪≫ upperShriekStructureSheafZerothIso (F.precompOpen h rfl)
      (F.precompOpen h rfl).compactification) k2)).trans (Iso.trans_assoc _ _ _))

end NormalizedOnOpens

end RestrictGeneric

end Stacks.Duality
