module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.HomologyPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonComposition

/-!
# The Leray identification along a composite and around a commutative square

For a morphism of ringed spaces `f : X ⟶ Y`, the Leray identification
`H^n(Y, Rf_* K) ≅ H^n(X, K)` of [Stacks, Tag 0D5W] is
`Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso`. This file proves that it is compatible
with composition and with commutative squares of ringed spaces.

* Along `i : Z ⟶ X` and `p : X ⟶ Y`, the identification for `i ≫ p` is the composition
  isomorphism `R(i ≫ p)_* ≅ Rp_* Ri_*` of [Stacks, Tag 079W], followed by the identification for
  `p` and then the one for `i` (`lerayCohomologyIso_comp`).
* Around a commutative square `g₀ ≫ π = π' ≫ g`, the comparison `Rπ_* Rg₀_* ⟶ Rg_* Rπ'_*` of the
  two iterated derived direct images intertwines the two iterated identifications
  (`lerayCohomologyIso_square`).
* Around such a square, the derived base change map `Lg^* Rπ_* ⟶ Rπ'_* Lg₀^*` of
  [Stacks, Tag 08HY] carries the pullback along `g` of a class read on `W` through `π` to the
  pullback along `g₀` of the class
  (`lerayCohomologyIso_homologyPullback_derivedBaseChangeMap`).

## Main results

* `Stacks.Cohomology.LerayComposite.pushforwardComparisonQ_comp`: the comparisons `f_* ⟶ Rf_*`
  are compatible with the composition isomorphism.
* `Stacks.Cohomology.LerayComposite.lerayCohomologyIso_comp`.
* `Stacks.Cohomology.LerayComposite.lerayCohomologyIso_square`.
* `Stacks.Cohomology.LerayComposite.lerayCohomologyIso_homologyPullback_derivedBaseChangeMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
open Stacks.Cohomology.HomologyPullback (map_map_comp_apply)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv)
open Stacks.Cohomology.DerivedPushforwardComposition (derivedPushforwardCompUnit_app)

universe u

namespace Stacks.Cohomology.LerayComposite

attribute [local instance] HasDerivedCategory.standard

/-! ### Elementwise identities -/

/-- `H(F(e.hom))` followed by `H(F(e.inv))` is the identity on elements. -/
private theorem map_map_hom_inv_apply {C D : Type*} [Category* C] [Category* D] {R : Type u}
    [Ring R] (F : C ⥤ D) (H : D ⥤ ModuleCat.{u} R) {a b : C} (e : a ≅ b)
    (z : H.obj (F.obj a)) :
    (H.map (F.map e.inv)).hom ((H.map (F.map e.hom)).hom z) = z := by
  rw [← map_map_comp_apply, e.hom_inv_id, F.map_id, H.map_id]
  rfl

/-- Equal composites of morphisms act equally on elements through `H ∘ F`. -/
private theorem map_map_comp_congr_apply {C D : Type*} [Category* C] [Category* D] {R : Type u}
    [Ring R] (F : C ⥤ D) (H : D ⥤ ModuleCat.{u} R) {a b c d : C} {x : a ⟶ b} {y : b ⟶ c}
    {x' : a ⟶ d} {y' : d ⟶ c} (h : x ≫ y = x' ≫ y') (z : H.obj (F.obj a)) :
    (H.map (F.map y)).hom ((H.map (F.map x)).hom z) =
      (H.map (F.map y')).hom ((H.map (F.map x')).hom z) := by
  rw [← map_map_comp_apply, ← map_map_comp_apply, h]

/-- An isomorphism of modules is injective on elements. -/
private theorem iso_hom_injective {R : Type u} [Ring R] {A B : ModuleCat.{u} R} (e : A ≅ B)
    {x y : A} (h : e.hom x = e.hom y) : x = y :=
  (Iso.hom_inv_id_apply e x).symm.trans ((congrArg e.inv h).trans (Iso.hom_inv_id_apply e y))

/-- Pasting the identities `r ≫ v = w ≫ rr`, `u ≫ w = m ≫ up ≫ rpu`, `q₁ ≫ m = cq ≫ q₂`,
`P = s' ≫ rpu ≫ rr` and `s ≫ s' = 𝟙 _` gives `(q₁ ≫ u ≫ r) ≫ v = cq ≫ (q₂ ≫ up ≫ s) ≫ P`. -/
private theorem paste_comp {C : Type*} [Category* C] {A A' B B' C₁ D E C' F G : C}
    (q₁ : A ⟶ B) (u : B ⟶ C₁) (r : C₁ ⟶ D) (v : D ⟶ E) (w : C₁ ⟶ C') (rr : C' ⟶ E)
    (m : B ⟶ B') (up : B' ⟶ F) (rpu : F ⟶ C') (cq : A ⟶ A') (q₂ : A' ⟶ B')
    (s : F ⟶ G) (s' : G ⟶ F) (P : G ⟶ E)
    (h₁ : r ≫ v = w ≫ rr) (h₂ : u ≫ w = m ≫ up ≫ rpu) (hq : q₁ ≫ m = cq ≫ q₂)
    (hP : P = s' ≫ rpu ≫ rr) (hs : s ≫ s' = 𝟙 _) :
    (q₁ ≫ u ≫ r) ≫ v = cq ≫ (q₂ ≫ up ≫ s) ≫ P := by
  simp only [Category.assoc]
  rw [h₁, reassoc_of% h₂, reassoc_of% hq, hP, reassoc_of% hs]

/-- A degree-`n` element of a complex of modules killed by the differential is a cycle. -/
private theorem exists_cycle {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) (x : K.X n) (hx : (K.d n (n + 1)).hom x = 0) :
    ∃ c : K.cycles n, (K.iCycles n).hom c = x := by
  have hd : ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x) ≫ K.d n (n + 1) = 0 := by
    ext
    change (K.d n (n + 1)).hom ((LinearMap.toSpanSingleton R (K.X n) x) 1) = 0
    rwa [LinearMap.toSpanSingleton_apply, one_smul]
  refine ⟨(K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x)) (n + 1)
    (by simp) hd).hom 1, ?_⟩
  have := ConcreteCategory.congr_hom (K.liftCycles_i
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x)) (n + 1) (by simp) hd) (1 : R)
  exact this.trans (by
    change (LinearMap.toSpanSingleton R (K.X n) x) 1 = _
    rw [LinearMap.toSpanSingleton_apply, one_smul])

/-- A global cocycle of a complex `K` of `𝒪_X`-modules is a global cocycle of `f_* K`. -/
private theorem exists_cycles_pushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ)
    (s : (sectionsComplex X K).cycles n) :
    ∃ t : (sectionsComplex Y ((pushforwardComplex f).obj K)).cycles n,
      ((sectionsComplex Y ((pushforwardComplex f).obj K)).iCycles n).hom t =
        ((sectionsComplex X K).iCycles n).hom s :=
  exists_cycle (sectionsComplex Y ((pushforwardComplex f).obj K)) n
    (((sectionsComplex X K).iCycles n).hom s)
    (ConcreteCategory.congr_hom ((sectionsComplex X K).iCycles_d n (n + 1)) s)

/-- The transport between the derived direct images along two equal morphisms is compatible
with the two Leray identifications. -/
private theorem lerayCohomologyIso_eqToHom {A C : RingedSpace.{u, u}} {a b : A ⟶ C}
    (hab : a = b) (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))) (n : ℤ)
    (w : cohomologyModule ((derivedPushforward a).obj N) n) :
    ((lerayCohomologyIso b N n).hom (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections C).map
          (eqToHom (congrArg (fun k : A ⟶ C => (derivedPushforward k).obj N) hab)))).hom w) :
        cohomologyModule N n) =
      (lerayCohomologyIso a N n).hom w := by
  subst hab
  refine congrArg (lerayCohomologyIso a N n).hom ?_
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-! ### The Leray identification along a composite -/

section Composite

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y)

/-- The identity chain map `(i ≫ p)_* I ⟶ p_*(i_* I)`: in each degree the component of the
composition isomorphism `modulePushforwardComp`, which is the identity. -/
def pushforwardCompComplexHom (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (pushforwardComplex (i ≫ p)).obj I ⟶
      (pushforwardComplex p).obj ((pushforwardComplex i).obj I) where
  f j := (modulePushforwardComp i p).inv.app (I.X j)
  comm' j k _ := ((modulePushforwardComp i p).inv.naturality (I.d j k)).symm

/-- The composition isomorphism of degreewise pushforwards on the homotopy category is, at the
class of a complex, the class of `pushforwardCompComplexHom`. -/
private theorem mapHomotopyCategoryCompIso_inv_app_quotient
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p)
        (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (pushforwardCompComplexHom i p I) :=
  rfl

/-- `pushforwardCompComplexHom` is the identity on global sections. -/
private theorem pushforwardCompComplexHom_sections_apply
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (y : (sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).X n) :
    (((((globalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (pushforwardCompComplexHom i p I)).f n).hom y) = y :=
  rfl

/-- **The comparisons `f_* ⟶ Rf_*` are compatible with composition**: the comparison for
`i ≫ p` followed by the composition isomorphism `R(i ≫ p)_* ≅ Rp_* Ri_*` of
[Stacks, Tag 079W] is the identity `(i ≫ p)_* I = p_*(i_* I)`, the comparison for `p` at
`i_* I`, and `Rp_*` of the comparison for `i`. -/
theorem pushforwardComparisonQ_comp
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    pushforwardComparisonQ (i ≫ p) I ≫
        (derivedPushforwardCompIso i p).inv.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (pushforwardCompComplexHom i p I) ≫
        pushforwardComparisonQ p ((pushforwardComplex i).obj I) ≫
        (derivedPushforward p).map (pushforwardComparisonQ i I) := by
  have h₁ := (derivedPushforwardCompIso i p).inv.naturality
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z))).hom.app I)
  have h₂ := derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv
    i p ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have h₃ := derivedPushforwardCompUnit_app i p
    (derivedPushforward i) (derivedPushforward p) (derivedPushforwardUnit i)
    (derivedPushforwardUnit p) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have hq := (congrArg (fun t => (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Y))).inv.app ((pushforwardComplex (i ≫ p)).obj I) ≫
        DerivedCategory.Qh.map t) (mapHomotopyCategoryCompIso_inv_app_quotient i p I)).trans
    (DerivedCategory.quotientCompQhIso_inv_naturality (pushforwardCompComplexHom i p I)).symm
  have hs : (derivedPushforward p).map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).hom.app ((pushforwardComplex i).obj I)) ≫
      (derivedPushforward p).map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).inv.app ((pushforwardComplex i).obj I)) =
        𝟙 _ :=
    ((derivedPushforward p).map_comp _ _).symm.trans
      ((congrArg (derivedPushforward p).map (Iso.hom_inv_id_app _ _)).trans
        ((derivedPushforward p).map_id _))
  have hP : (derivedPushforward p).map (pushforwardComparisonQ i I) =
      (derivedPushforward p).map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).inv.app ((pushforwardComplex i).obj I)) ≫
        (derivedPushforward p).map ((derivedPushforwardUnit i).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (derivedPushforward p).map ((derivedPushforward i).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (structureSheafRing Z))).hom.app I)) :=
    ((derivedPushforward p).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((derivedPushforward p).map_comp _ _))
  exact paste_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ (h₂.trans h₃) hq hP hs

/-- The global cocycle of `p_*(i_* I)` obtained from one of `(i ≫ p)_* I` through
`pushforwardCompComplexHom` is the same section. -/
private theorem iCycles_cyclesMap_pushforwardCompComplexHom
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (sY : (sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).cycles n) :
    ((sectionsComplex Y ((pushforwardComplex p).obj ((pushforwardComplex i).obj I))).iCycles
        n).hom
        ((HomologicalComplex.cyclesMap (((globalSections Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (pushforwardCompComplexHom i p I)) n).hom sY) =
      ((sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).iCycles n).hom sY :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((globalSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (pushforwardCompComplexHom i p I)) n) sY).trans
    ((ConcreteCategory.comp_apply _ _ _).trans
      (pushforwardCompComplexHom_sections_apply i p I n _))

/-- The composite of the Leray identifications for `p` and `i`, read through the composition
isomorphism, sends the image of the class of a global cocycle of `(i ≫ p)_* I` to the class on
`Z` of the same cocycle. -/
theorem lerayCohomologyIso_comp_globalClass
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (sY : (sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).cycles n)
    (sZ : (sectionsComplex Z I).cycles n)
    (h : ((sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).iCycles n).hom sY =
      ((sectionsComplex Z I).iCycles n).hom sZ) :
    (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app (DerivedCategory.Q.obj I)))).hom
            (((DerivedCategory.homologyFunctor _ n).map
              ((baseSections Y).map (pushforwardComparisonQ (i ≫ p) I))).hom
                (globalClass ((pushforwardComplex (i ≫ p)).obj I) n sY)))) =
      globalClass I n sZ := by
  obtain ⟨sX, hX⟩ := exists_cycles_pushforward i I n sZ
  have step₁ := (map_map_comp_congr_apply (baseSections Y) (DerivedCategory.homologyFunctor _ n)
    (pushforwardComparisonQ_comp i p I)
    (globalClass ((pushforwardComplex (i ≫ p)).obj I) n sY)).trans
    (map_map_comp_apply (baseSections Y) (DerivedCategory.homologyFunctor _ n) _ _ _)
  have step₀ := globalClass_map Y (pushforwardCompComplexHom i p I) n sY
  have step₂ := lerayCohomologyIso_naturality_apply p (pushforwardComparisonQ i I) n
    (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Y).map (pushforwardComparisonQ p ((pushforwardComplex i).obj I)))).hom
        (globalClass ((pushforwardComplex p).obj ((pushforwardComplex i).obj I)) n
          ((HomologicalComplex.cyclesMap (((globalSections Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (pushforwardCompComplexHom i p I)) n).hom sY)))
  have step₃ := lerayCohomologyIso_globalClass p ((pushforwardComplex i).obj I) n _ sX
    ((iCycles_cyclesMap_pushforwardCompComplexHom i p I n sY).trans (h.trans hX.symm))
  have step₄ := lerayCohomologyIso_globalClass i I n sX sZ hX
  refine (congrArg (fun t => (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
    ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom t))
    step₁).trans ?_
  refine (congrArg (fun t => (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
    ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
        ((derivedPushforward p).map (pushforwardComparisonQ i I)))).hom
      (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Y).map (pushforwardComparisonQ p ((pushforwardComplex i).obj I)))).hom t))))
    step₀).trans ?_
  refine (congrArg (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom step₂).trans ?_
  refine (congrArg (fun t => (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
    (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections X).map (pushforwardComparisonQ i I))).hom t)) step₃).trans ?_
  exact step₄

/-- The composite of the Leray identifications for `p` and `i`, read through the composition
isomorphism, is natural in the object. -/
theorem lerayCohomologyIso_comp_naturality
    {N N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (φ : N ⟶ N') (n : ℤ)
    (z : cohomologyModule ((derivedPushforward (i ≫ p)).obj N) n) :
    ((lerayCohomologyIso i N' n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj N') n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app N'))).hom
            (((DerivedCategory.homologyFunctor _ n).map
              ((baseSections Y).map ((derivedPushforward (i ≫ p)).map φ))).hom z))) :
        cohomologyModule N' n) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map φ)).hom
        ((lerayCohomologyIso i N n).hom
          ((lerayCohomologyIso p ((derivedPushforward i).obj N) n).hom
            (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
              ((derivedPushforwardCompIso i p).inv.app N))).hom z))) := by
  have hnat : (derivedPushforward (i ≫ p)).map φ ≫ (derivedPushforwardCompIso i p).inv.app N' =
      (derivedPushforwardCompIso i p).inv.app N ≫
        (derivedPushforward p).map ((derivedPushforward i).map φ) :=
    (derivedPushforwardCompIso i p).inv.naturality φ
  have step₁ := map_map_comp_congr_apply (baseSections Y) (DerivedCategory.homologyFunctor _ n)
    hnat z
  refine (congrArg (fun t => (lerayCohomologyIso i N' n).hom
    ((lerayCohomologyIso p ((derivedPushforward i).obj N') n).hom t)) step₁).trans ?_
  refine (congrArg (lerayCohomologyIso i N' n).hom
    (lerayCohomologyIso_naturality_apply p ((derivedPushforward i).map φ) n _)).trans ?_
  exact lerayCohomologyIso_naturality_apply i φ n _

/-- `lerayCohomologyIso_comp` at the object `Q(I)`, for an element `z` that is the image under the
comparison `(i ≫ p)_* ⟶ R(i ≫ p)_*` of the class of a global cocycle of `(i ≫ p)_* I`. -/
private theorem lerayCohomologyIso_comp_of_eq_globalClass
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (z : cohomologyModule ((derivedPushforward (i ≫ p)).obj (DerivedCategory.Q.obj I)) n)
    (sZ : (sectionsComplex Z I).cycles n)
    (sY : (sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).cycles n)
    (hY : ((sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).iCycles n).hom sY =
        ((sectionsComplex Z I).iCycles n).hom sZ)
    (hz : ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Y).map (pushforwardComparisonQ (i ≫ p) I))).hom
        (globalClass ((pushforwardComplex (i ≫ p)).obj I) n sY) = z) :
    ((lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app (DerivedCategory.Q.obj I)))).hom z)) :
        cohomologyModule (DerivedCategory.Q.obj I) n) =
      (lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n).hom z := by
  have e₁ := lerayCohomologyIso_globalClass (i ≫ p) I n sY sZ hY
  refine (congrArg (fun t => (lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app (DerivedCategory.Q.obj I)))).hom t)))
      hz.symm).trans ?_
  refine (lerayCohomologyIso_comp_globalClass i p I n sY sZ hY).trans ?_
  exact e₁.symm.trans (congrArg (lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n).hom hz)

/-- A class of `H^n(Y, R(i ≫ p)_* Q(I))` whose Leray image is the class of a global cocycle of
`I` is the image of the class of the same cocycle of `(i ≫ p)_* I`. -/
private theorem comparison_globalClass_eq
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (z : cohomologyModule ((derivedPushforward (i ≫ p)).obj (DerivedCategory.Q.obj I)) n)
    (sZ : (sectionsComplex Z I).cycles n)
    (hZ : globalClass I n sZ = (lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n).hom z)
    (sY : (sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).cycles n)
    (hY : ((sectionsComplex Y ((pushforwardComplex (i ≫ p)).obj I)).iCycles n).hom sY =
        ((sectionsComplex Z I).iCycles n).hom sZ) :
    ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Y).map (pushforwardComparisonQ (i ≫ p) I))).hom
        (globalClass ((pushforwardComplex (i ≫ p)).obj I) n sY) = z :=
  iso_hom_injective (lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n)
    ((lerayCohomologyIso_globalClass (i ≫ p) I n sY sZ hY).trans hZ)

/-- `lerayCohomologyIso_comp` at the image `Q(I)` of a K-injective complex `I`. -/
theorem lerayCohomologyIso_comp_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (hI : I.IsKInjective)
    (n : ℤ) (z : cohomologyModule ((derivedPushforward (i ≫ p)).obj (DerivedCategory.Q.obj I)) n) :
    ((lerayCohomologyIso i (DerivedCategory.Q.obj I) n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj (DerivedCategory.Q.obj I)) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app (DerivedCategory.Q.obj I)))).hom z)) :
        cohomologyModule (DerivedCategory.Q.obj I) n) =
      (lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n).hom z :=
  (exists_globalClass_of_isKInjective I hI n
    ((lerayCohomologyIso (i ≫ p) (DerivedCategory.Q.obj I) n).hom z)).elim fun sZ hZ =>
  (exists_cycles_pushforward (i ≫ p) I n sZ).elim fun sY hY =>
  lerayCohomologyIso_comp_of_eq_globalClass i p I n z sZ sY hY
    (comparison_globalClass_eq i p I n z sZ hZ sY hY)

/-- **The Leray identification along a composite** ([Stacks, Tag 0D5W] for `i ≫ p`): for
`i : Z ⟶ X`, `p : X ⟶ Y`, `N ∈ D(𝒪_Z)` and `z ∈ H^n(Y, R(i ≫ p)_* N)`, the identification
`H^n(Y, R(i ≫ p)_* N) ≅ H^n(Z, N)` is the composition isomorphism
`R(i ≫ p)_* N ≅ Rp_* Ri_* N` of [Stacks, Tag 079W], followed by the identification for `p` and
then the one for `i`. -/
theorem lerayCohomologyIso_comp (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (n : ℤ) (z : cohomologyModule ((derivedPushforward (i ≫ p)).obj N) n) :
    ((lerayCohomologyIso i N n).hom
        ((lerayCohomologyIso p ((derivedPushforward i).obj N) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Y).map
            ((derivedPushforwardCompIso i p).inv.app N))).hom z)) : cohomologyModule N n) =
      (lerayCohomologyIso (i ≫ p) N n).hom z := by
  have := Localization.essSurj
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Z)))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  obtain ⟨I, φ, hI, _⟩ := exists_quasiIso_isKInjective Z (DerivedCategory.Q.objPreimage N)
  have : IsIso (DerivedCategory.Q.map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : DerivedCategory.Q.obj I ≅ N :=
    (asIso (DerivedCategory.Q.map φ)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨z₀, rfl⟩ : ∃ z₀, ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Y).map ((derivedPushforward (i ≫ p)).map e.hom))).hom z₀ = z :=
    ⟨_, map_map_hom_inv_apply (baseSections Y) (DerivedCategory.homologyFunctor _ n)
      ((derivedPushforward (i ≫ p)).mapIso e.symm) z⟩
  refine (lerayCohomologyIso_comp_naturality i p e.hom n z₀).trans ?_
  refine (congrArg _ (lerayCohomologyIso_comp_of_isKInjective i p I hI n z₀)).trans ?_
  exact (lerayCohomologyIso_naturality_apply (i ≫ p) e.hom n z₀).symm

end Composite

/-! ### The Leray identification around a commutative square -/

section Square

attribute [local instance high] CategoryTheory.instHasWeakSheafifyOfHasSheafify

variable {X' X Z W : RingedSpace.{u, u}} (g₀ : X' ⟶ X) (π' : X' ⟶ Z) (π : X ⟶ W) (g : Z ⟶ W)
  (sq : g₀ ≫ π = π' ≫ g)

/-- The comparison of the two iterated derived direct images on cohomology over `W`, written
through the two composition isomorphisms of [Stacks, Tag 079W] and the transport along the
square. -/
private theorem homology_derivedPushforwardComparisonSquare_apply
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) (n : ℤ)
    (z : cohomologyModule ((derivedPushforward π).obj ((derivedPushforward g₀).obj N)) n) :
    ((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
            ((Mate.derivedPushforwardComparisonSquare (derivedAdjunction π)
              (derivedAdjunction π') (derivedAdjunction g) (derivedAdjunction g₀)
              (derivedPullbackCompIsoLeft g₀ π' π g sq)
              (derivedPullbackCompIsoCanonical g₀ π)).app N))).hom z =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
        ((derivedPushforwardCompIso π' g).inv.app N))).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
        (eqToHom (congrArg (fun k : X' ⟶ W => (derivedPushforward k).obj N) sq)))).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
        ((derivedPushforwardCompIso g₀ π).hom.app N))).hom z)) :=
  (congrArg (fun t => ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections W).map t)).hom z)
      (derivedPushforwardComparisonSquare_app_eq_compIso g₀ π' π g sq N)).trans
    ((map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ n) _ _ z).trans
      (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ n) _ _ _))

/-- **The Leray identification around a commutative square**: for `g₀ ≫ π = π' ≫ g`,
`N ∈ D(𝒪_{X'})` and `z ∈ H^n(W, Rπ_* Rg₀_* N)`, the comparison `Rπ_* Rg₀_* N ⟶ Rg_* Rπ'_* N`
of the two iterated derived direct images intertwines the two iterated Leray identifications
`H^n(W, Rπ_* Rg₀_* N) ≅ H^n(X', N)` and `H^n(W, Rg_* Rπ'_* N) ≅ H^n(X', N)`. -/
theorem lerayCohomologyIso_square
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) (n : ℤ)
    (z : cohomologyModule ((derivedPushforward π).obj ((derivedPushforward g₀).obj N)) n) :
    ((lerayCohomologyIso π' N n).hom
        ((lerayCohomologyIso g ((derivedPushforward π').obj N) n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
            ((Mate.derivedPushforwardComparisonSquare (derivedAdjunction π)
              (derivedAdjunction π') (derivedAdjunction g) (derivedAdjunction g₀)
              (derivedPullbackCompIsoLeft g₀ π' π g sq)
              (derivedPullbackCompIsoCanonical g₀ π)).app N))).hom z)) :
        cohomologyModule N n) =
      (lerayCohomologyIso g₀ N n).hom
        ((lerayCohomologyIso π ((derivedPushforward g₀).obj N) n).hom z) :=
  (congrArg (fun t => (lerayCohomologyIso π' N n).hom
    ((lerayCohomologyIso g ((derivedPushforward π').obj N) n).hom t))
      (homology_derivedPushforwardComparisonSquare_apply g₀ π' π g sq N n z)).trans
  ((lerayCohomologyIso_comp π' g N n _).trans
  ((lerayCohomologyIso_eqToHom sq N n _).trans
  ((lerayCohomologyIso_comp g₀ π N n _).symm.trans
  (congrArg (fun t => (lerayCohomologyIso g₀ N n).hom
    ((lerayCohomologyIso π ((derivedPushforward g₀).obj N) n).hom t))
    (map_map_hom_inv_apply (baseSections W) (DerivedCategory.homologyFunctor _ n)
      ((derivedPushforwardCompIso g₀ π).app N) z)))))

/-- **Pullback of cohomology classes against derived base change** ([Stacks, Tag 08HY]): for a
commutative square `g₀ ≫ π = π' ≫ g`, `M ∈ D(𝒪_X)` and `x ∈ H^n(X, M)`, read `x` in
`H^n(W, Rπ_* M)` by the Leray identification for `π`, pull it back along `g`, carry it by the
derived base change map `Lg^* Rπ_* M ⟶ Rπ'_* Lg₀^* M` and read the result in
`H^n(X', Lg₀^* M)` by the Leray identification for `π'`: this is the pullback of `x` along
`g₀`. -/
theorem lerayCohomologyIso_homologyPullback_derivedBaseChangeMap
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ)
    (x : cohomologyModule M n) :
    (lerayCohomologyIso π' ((derivedPullback g₀).obj M) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
          ((Mate.derivedBaseChangeSquare (derivedAdjunction π) (derivedAdjunction π')
            (derivedPullbackCompIsoLeft g₀ π' π g sq)
            (derivedPullbackCompIsoCanonical g₀ π)).app M))).hom
          (HomologyPullback.homologyPullback g ((derivedPushforward π).obj M) n
            ((lerayCohomologyIso π M n).inv x))) =
      HomologyPullback.homologyPullback g₀ M n x := by
  have hfac := Mate.derivedBaseChangeMap_unit_fac (derivedAdjunction π) (derivedAdjunction π')
    (derivedAdjunction g) (derivedAdjunction g₀) (derivedPullbackCompIsoLeft g₀ π' π g sq)
    (derivedPullbackCompIsoCanonical g₀ π) M
  have step₁ := lerayCohomologyIso_naturality_apply g
    ((Mate.derivedBaseChangeSquare (derivedAdjunction π) (derivedAdjunction π')
      (derivedPullbackCompIsoLeft g₀ π' π g sq) (derivedPullbackCompIsoCanonical g₀ π)).app M) n
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
      ((derivedAdjunction g).unit.app ((derivedPushforward π).obj M)))).hom
        ((lerayCohomologyIso π M n).inv x))
  have step₂ := map_map_comp_congr_apply (baseSections W) (DerivedCategory.homologyFunctor _ n)
    hfac.symm ((lerayCohomologyIso π M n).inv x)
  have step₃ := (lerayCohomologyIso_naturality_apply π ((derivedAdjunction g₀).unit.app M) n
    ((lerayCohomologyIso π M n).inv x)).trans
    (congrArg (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections X).map ((derivedAdjunction g₀).unit.app M))).hom)
      (Iso.inv_hom_id_apply (lerayCohomologyIso π M n) x))
  refine (congrArg (lerayCohomologyIso π' ((derivedPullback g₀).obj M) n).hom
    step₁.symm).trans ?_
  refine (congrArg (fun t => (lerayCohomologyIso π' ((derivedPullback g₀).obj M) n).hom
    ((lerayCohomologyIso g ((derivedPushforward π').obj ((derivedPullback g₀).obj M)) n).hom t))
    step₂).trans ?_
  refine (lerayCohomologyIso_square g₀ π' π g sq ((derivedPullback g₀).obj M) n _).trans ?_
  exact congrArg (lerayCohomologyIso g₀ ((derivedPullback g₀).obj M) n).hom step₃

end Square

end Stacks.Cohomology.LerayComposite

end
