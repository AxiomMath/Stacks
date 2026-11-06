module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusCompositionCompatibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiRelativeCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SingleRightDerivedUnitComposition

/-!
# The pullback along a morphism of topoi and the derived comparison of a square

Let `f ⊣ g` be an adjunction between abelian categories `𝒟₀`, `𝒟`, with `f` exact and `g`
preserving injectives, and let `Δ₀`, `Δ` be "global sections" functors with an identification
`eΔ : g ⋙ Δ₀ ≅ Δ`.  The **pullback on derived sections** `lerayPullback : RΔ₀ ⟶ f̄ ⋙ RΔ` is `RΔ₀`
of the derived unit `𝟭 ⟶ f̄ ⋙ Rg` followed by the inverse of the Leray factorization
`RΔ ≅ Rg ⋙ RΔ₀` of [Stacks, Tag 015M].  At a single object it is the map
`...SmallSite.derivedCrisPullbackMap` the chapter builds for the morphism of crystalline topoi
(`lerayPullback_app_single`).

The second half of the file compares it with the derived comparison
`CategoryTheory.Functor.derivedSquareTrans'` of a square `α : Γ₀ ⟶ P ⋙ Γ ⋙ r` living on other
categories `𝒞₀`, `𝒞`, linked to `𝒟₀`, `𝒟` by exact functors `Q₀`, `Q` carrying injectives to
acyclic objects, through isomorphisms `e₀ : Γ₀ ⋙ φ₀ ≅ Q₀ ⋙ Δ₀`, `e₁ : Γ ⋙ r ⋙ φ₀ ≅ Q ⋙ Δ` and a
comparison `c : Q₀ ⋙ f ⟶ P ⋙ Q`.  If the two underived comparisons agree (`hU`), so do the two
derived ones (`comparisonViaPullback_eq_comparisonViaSquare`), and at a single object this reads
as `derivedSquareMap_comp_targetIso`.

## The argument

Both derived comparisons are transformations out of the right derived functor `R(Γ₀ ⋙ φ₀)`, so by
`CategoryTheory.Functor.rightDerived_ext` they agree as soon as they agree after its unit.  There
each is computed: `unit_comp_comparisonViaPullback_app` and `unit_comp_comparisonViaSquare_app`,
and both are `hU` applied degreewise followed by the unit of `RΔ`.

## Main results

* `lerayPullback_app_single` — the pullback on derived sections at a single object.
* `comparisonViaPullback_eq_comparisonViaSquare` — the two derived comparisons agree.
* `derivedSquareMap_comp_targetIso` — the same at a single object.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Stacks.LerayPullbackComparison

/-- An identity `a ≫ e.hom = n` solved for `a`, in an arbitrary category. -/
private lemma comp_inv_eq_of {𝒦 : Type*} [Category* 𝒦] {X Y Z : 𝒦} (a : X ⟶ Y) (e : Y ≅ Z)
    (n : X ⟶ Z) (h : a ≫ e.hom = n) : n ≫ e.inv = a := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

section Leray

variable {D₀ D A : Type*} [Category* D₀] [Category* D] [Category* A]
  [Abelian D₀] [Abelian D] [Abelian A]
  [HasDerivedCategory D₀] [HasDerivedCategory D] [HasDerivedCategory A]
  [EnoughInjectives D₀] [EnoughInjectives D]
  {f : D₀ ⥤ D} {g : D ⥤ D₀} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  (adj : f ⊣ g)

/-- The derived unit of `f ⊣ g`, before localization: the unit applied degreewise, followed by
the unit of `Rg` and the factorization of `f̄` through the localization. -/
def derivedUnitAux :
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus D₀ ⥤ DerivedCategory.Plus D₀) ⟶
      DerivedCategory.Plus.Qh ⋙ f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus where
  app K := DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
    g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj K) ≫
    g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.inv.app K)
  naturality K L φ := by
    have h1 := congrArg DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.naturality φ)
    have h2 := g.rightDerivedFunctorPlusUnith.naturality (f.mapHomotopyCategoryPlus.map φ)
    have h3 := f.mapDerivedCategoryPlusFactorsh.inv.naturality φ
    simp only [Functor.id_map, Functor.comp_map, Functor.map_comp] at h1 h2 h3 ⊢
    rw [reassoc_of% h1, reassoc_of% h2, ← Functor.map_comp, h3, Functor.map_comp]
    simp only [Category.assoc]

/-- **The derived unit `𝟭 ⟶ f̄ ⋙ Rg`** of an adjunction `f ⊣ g` with `f` exact. -/
def derivedUnit : 𝟭 (DerivedCategory.Plus D₀) ⟶
    f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus :=
  Localization.liftNatTrans DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D₀)
    DerivedCategory.Plus.Qh
    (DerivedCategory.Plus.Qh ⋙ f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus)
    (𝟭 _) (f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus) (derivedUnitAux adj)

omit [EnoughInjectives D₀] in
/-- The derived unit on the image of a bounded below complex. -/
theorem derivedUnit_app_Qh (K : HomotopyCategory.Plus D₀) :
    (derivedUnit adj).app (DerivedCategory.Plus.Qh.obj K) = (derivedUnitAux adj).app K := by
  rw [derivedUnit, Localization.liftNatTrans_app]
  simp


variable (Δ₀ : D₀ ⥤ A) (Δ : D ⥤ A) [Δ₀.Additive] [Δ.Additive] [PreservesFiniteLimits Δ₀]
  [g.PreservesInjectiveObjects] (eΔ : g ⋙ Δ₀ ≅ Δ)

/-- **The Leray factorization `RΔ ≅ Rg ⋙ RΔ₀`** of [Stacks, Tag 015M]. -/
def lerayIso : Δ.rightDerivedFunctorPlus ≅
    g.rightDerivedFunctorPlus ⋙ Δ₀.rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusNatIso eΔ).symm ≪≫
    Stacks.Cohomology.DerivedPushforwardSections.compIsoOfPreservesInjectives g Δ₀

/-- **The pullback on derived sections**, `RΔ₀ ⟶ f̄ ⋙ RΔ`. -/
def lerayPullback : Δ₀.rightDerivedFunctorPlus ⟶
    f.mapDerivedCategoryPlus ⋙ Δ.rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedUnit adj) Δ₀.rightDerivedFunctorPlus ≫
    Functor.whiskerLeft f.mapDerivedCategoryPlus (lerayIso Δ₀ Δ eΔ).inv

/-- **The pullback on derived sections is invertible wherever the derived unit is**: at `K`
it is `RΔ₀` of the derived unit at `K` followed by an inverse of the Leray factorization. So if
`K ⟶ Rg(f̄K)` is an isomorphism, then `RΔ₀(K) ≅ RΔ(f̄K)`. -/
theorem isIso_lerayPullback_app (K : DerivedCategory.Plus D₀)
    [IsIso ((derivedUnit adj).app K)] : IsIso ((lerayPullback adj Δ₀ Δ eΔ).app K) := by
  rw [lerayPullback, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- The identification of `(F ⋙ G).mapHomotopyCategoryPlus` with the composite of the induced
functors, for `Iso.refl (F ⋙ G)`, becomes the identity in the derived category. -/
private lemma Qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app {X Y Z : Type*} [Category* X]
    [Category* Y] [Category* Z] [Abelian X] [Abelian Y] [Abelian Z] [HasDerivedCategory Z]
    (F : X ⥤ Y) (G : Y ⥤ Z) [F.Additive] [G.Additive] (K : HomotopyCategory.Plus X) :
    DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) = 𝟙 _ :=
  (congrArg DerivedCategory.Plus.Qh.map (rfl : _ = 𝟙 _)).trans (DerivedCategory.Plus.Qh.map_id _)

/-- Bookkeeping for `unit_comp_lerayIso_inv_app`, in an arbitrary category. -/
private lemma cancelComp {𝒦 : Type*} [Category* 𝒦] {X Y Z W V U : 𝒦} (q : X ⟶ X) (a : X ⟶ Y)
    (b : Y ⟶ Z) (ηG : X ⟶ W) (ch : W ⟶ Z) (ci : Z ⟶ W) (d : W ⟶ V) (r : X ⟶ U) (t : U ⟶ V)
    (h1 : ηG ≫ ch = q ≫ a ≫ b) (h2 : ηG ≫ d = r ≫ t) (hq : q = 𝟙 X) (hc : ch ≫ ci = 𝟙 W) :
    a ≫ b ≫ ci ≫ d = r ≫ t := by
  subst hq
  rw [Category.id_comp] at h1
  rw [← h2, ← reassoc_of% h1, reassoc_of% hc]

/-- **The Leray factorization after the units**: at a bounded below complex `M`, the unit of
`RΔ₀` at `g(M)` followed by `RΔ₀` of the unit of `Rg` and by the inverse of the Leray
factorization is `eΔ` applied degreewise followed by the unit of `RΔ`. -/
theorem unit_comp_lerayIso_inv_app (M : HomotopyCategory.Plus D) :
    Δ₀.rightDerivedFunctorPlusUnith.app (g.mapHomotopyCategoryPlus.obj M) ≫
        Δ₀.rightDerivedFunctorPlus.map (g.rightDerivedFunctorPlusUnith.app M) ≫
        (lerayIso Δ₀ Δ eΔ).inv.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso eΔ).hom.app M) ≫
        Δ.rightDerivedFunctorPlusUnith.app M := by
  have h2 := Functor.rightDerivedNatTrans_app (Functor.rightDerivedFunctorPlus (g ⋙ Δ₀))
    Δ.rightDerivedFunctorPlus (g ⋙ Δ₀).rightDerivedFunctorPlusUnith Δ.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatIso eΔ).hom DerivedCategory.Plus.Qh) M
  exact cancelComp _ _ _ _ _ _ _ _ _ (Functor.rightDerivedFunctorPlusComp_fac_app g Δ₀ M) h2
    (Qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app _ _ M)
    ((Stacks.Cohomology.DerivedPushforwardSections.compIsoOfPreservesInjectives g Δ₀).hom_inv_id_app
      (DerivedCategory.Plus.Qh.obj M))

/-- Bookkeeping for `unit_comp_lerayPullback_app`, in an arbitrary category. -/
private lemma pasteLeray {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : 𝒦}
    (η : X₀ ⟶ X₁) (qu : X₁ ⟶ X₂) (ηg : X₂ ⟶ X₃) (rf : X₃ ⟶ X₄) (li : X₄ ⟶ Y₄)
    (du : X₀ ⟶ Y₁) (η' : Y₁ ⟶ X₂) (hη : du ≫ η' = η ≫ qu)
    (li' : X₃ ⟶ Y₃) (rf' : Y₃ ⟶ Y₄) (hli : rf ≫ li = li' ≫ rf')
    (e : Y₁ ⟶ Y₂) (ηΔ : Y₂ ⟶ Y₃) (due : X₀ ⟶ Y₂) (hdue : due = du ≫ e)
    (hL : η' ≫ ηg ≫ li' = e ≫ ηΔ) :
    η ≫ (qu ≫ ηg ≫ rf) ≫ li = due ≫ ηΔ ≫ rf' := by
  subst hdue
  simp only [Category.assoc]
  rw [hli, ← reassoc_of% hη, reassoc_of% hL]

/-- **The pullback on derived sections after the unit**: at a bounded below complex `L`, the
unit of `RΔ₀` followed by `lerayPullback` is the underived pullback `Δ₀(L) ⟶ Δ₀(g(f(L))) ≅ Δ(f(L))`
applied degreewise, followed by the unit of `RΔ` at `f(L)`. -/
theorem unit_comp_lerayPullback_app (L : HomotopyCategory.Plus D₀) :
    Δ₀.rightDerivedFunctorPlusUnith.app L ≫
        (lerayPullback adj Δ₀ Δ eΔ).app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map (Δ₀.mapHomotopyCategoryPlus.map
          (adj.mapHomotopyCategoryPlus.unit.app L) ≫
          (Functor.mapHomotopyCategoryPlusNatIso eΔ).hom.app (f.mapHomotopyCategoryPlus.obj L)) ≫
        Δ.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj L) ≫
        Δ.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.inv.app L) := by
  have hlp : (lerayPullback adj Δ₀ Δ eΔ).app (DerivedCategory.Plus.Qh.obj L) =
      (Δ₀.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app L)) ≫
        Δ₀.rightDerivedFunctorPlus.map
          (g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj L)) ≫
        Δ₀.rightDerivedFunctorPlus.map
          (g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.inv.app L))) ≫
        (lerayIso Δ₀ Δ eΔ).inv.app
          (f.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj L)) :=
    congrArg (· ≫ (lerayIso Δ₀ Δ eΔ).inv.app
        (f.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj L)))
      ((congrArg Δ₀.rightDerivedFunctorPlus.map (derivedUnit_app_Qh adj L)).trans
        ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))))
  rw [hlp]
  exact pasteLeray _ _ _ _ _ _ _
    (Δ₀.rightDerivedFunctorPlusUnith.naturality (adj.mapHomotopyCategoryPlus.unit.app L))
    _ _ ((lerayIso Δ₀ Δ eΔ).inv.naturality (f.mapDerivedCategoryPlusFactorsh.inv.app L))
    _ _ _ (DerivedCategory.Plus.Qh.map_comp _ _)
    (unit_comp_lerayIso_inv_app Δ₀ Δ eΔ (f.mapHomotopyCategoryPlus.obj L))

omit [HasDerivedCategory D₀] [HasDerivedCategory D] [EnoughInjectives D₀] [EnoughInjectives D]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f] in
omit [g.PreservesInjectiveObjects] in
/-- The degreewise unit at a complex in degree zero is the unit placed in degree zero, read
through the identifications `g(f(Y[0])) ≅ (g(f(Y)))[0]`. -/
private lemma unit_single_complex (Y : D₀) :
    (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single D₀ (ComplexShape.up ℤ) 0).obj Y) ≫
      (g.mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex f (ComplexShape.up ℤ) 0).hom.app Y) ≫
      (HomologicalComplex.singleMapHomologicalComplex g (ComplexShape.up ℤ) 0).hom.app
        (f.obj Y) =
    (HomologicalComplex.single D₀ (ComplexShape.up ℤ) 0).map (adj.unit.app Y) := by
  ext i
  by_cases h : i = 0
  · subst h
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

/-- Bookkeeping for `unit_single_plus`: identities after a morphism, in arbitrary categories. -/
private lemma comp_map_id_comp_id {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (G : 𝒦 ⥤ 𝒦')
    {X : 𝒦'} {Y : 𝒦} (a : X ⟶ G.obj Y) : a ≫ G.map (𝟙 Y) ≫ 𝟙 (G.obj Y) = a := by
  simp

/-- The bounded below homotopy category embedding sends the unit of the degreewise adjunction
to the class of the degreewise unit. -/
private lemma ι_map_mapHomotopyCategoryPlus_unit_app {X Y : Type*} [Category* X] [Category* Y]
    [Abelian X] [Abelian Y] {F : X ⥤ Y} {G : Y ⥤ X} [F.Additive] [G.Additive] (a : F ⊣ G)
    (K : HomotopyCategory.Plus X) :
    (HomotopyCategory.Plus.ι X).map (a.mapHomotopyCategoryPlus.unit.app K) =
      (HomotopyCategory.quotient X _).map
        ((NatTrans.mapHomologicalComplex a.unit (ComplexShape.up ℤ)).app K.obj.as) :=
  (Adjunction.map_restrictFullyFaithful_unit_app
    (adj := a.mapHomotopyCategory (ComplexShape.up ℤ))
    (hiC := HomotopyCategory.Plus.fullyFaithfulι X) (hiD := HomotopyCategory.Plus.fullyFaithfulι Y)
    (L := F.mapHomotopyCategoryPlus) (R := G.mapHomotopyCategoryPlus)
    (comm1 := Iso.refl _) (comm2 := Iso.refl _) K).trans
    ((comp_map_id_comp_id (G.mapHomotopyCategory (ComplexShape.up ℤ))
      ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app _)).trans rfl)

/-- The bounded below homotopy category embedding sends `F.mapHomotopyCategoryPlusObjSingleIso`
to the class of the degreewise comparison of `F` with the single complex. -/
private lemma ι_map_mapHomotopyCategoryPlusObjSingleIso_hom {X Y : Type*} [Category* X]
    [Category* Y] [Abelian X] [Abelian Y] (F : X ⥤ Y) [F.Additive] (Z : X) :
    (HomotopyCategory.Plus.ι Y).map (F.mapHomotopyCategoryPlusObjSingleIso 0 Z).hom =
      (HomotopyCategory.quotient Y _).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app Z) :=
  (HomotopyCategory.Plus.ι Y).map_preimage _

omit [HasDerivedCategory D₀] [HasDerivedCategory D] [EnoughInjectives D₀] [EnoughInjectives D]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f] in
omit [g.PreservesInjectiveObjects] in
/-- `unit_single_complex` in the bounded below homotopy category. -/
private lemma unit_single_plus (Y : D₀) :
    adj.mapHomotopyCategoryPlus.unit.app ((HomotopyCategory.Plus.singleFunctor D₀ 0).obj Y) ≫
      g.mapHomotopyCategoryPlus.map (f.mapHomotopyCategoryPlusObjSingleIso 0 Y).hom ≫
      (g.mapHomotopyCategoryPlusObjSingleIso 0 (f.obj Y)).hom =
    (HomotopyCategory.Plus.singleFunctor D₀ 0).map (adj.unit.app Y) := by
  refine (HomotopyCategory.Plus.ι D₀).map_injective ?_
  have t2 : (HomotopyCategory.Plus.ι D₀).map
      (g.mapHomotopyCategoryPlus.map (f.mapHomotopyCategoryPlusObjSingleIso 0 Y).hom) =
      (HomotopyCategory.quotient D₀ _).map ((g.mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex f (ComplexShape.up ℤ) 0).hom.app Y)) :=
    (congrArg (g.mapHomotopyCategory _).map
      (ι_map_mapHomotopyCategoryPlusObjSingleIso_hom f Y)).trans rfl
  rw [Functor.map_comp, Functor.map_comp, ι_map_mapHomotopyCategoryPlus_unit_app, t2,
    ι_map_mapHomotopyCategoryPlusObjSingleIso_hom g]
  refine Eq.trans ?_ (congrArg (HomotopyCategory.quotient D₀ _).map (unit_single_complex adj Y))
  simp only [Functor.map_comp]
  rfl

/-- Bookkeeping for `derivedUnit_app_single`, in an arbitrary category. -/
private lemma pasteUnitSingle {𝒦 : Type*} [Category* 𝒦]
    {A₀ B₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ A₁ B₁ : 𝒦}
    (sh : A₀ ⟶ B₀) (uQh : B₀ ⟶ X₃) (uS : A₀ ⟶ X₄) (Fsh : X₄ ⟶ X₃) (rsi : X₃ ⟶ X₄)
    (hnat : sh ≫ uQh = uS ≫ Fsh) (hFs : Fsh ≫ rsi = 𝟙 _)
    (uQ : B₀ ⟶ X₁) (ηf : X₁ ⟶ X₂) (rfi : X₂ ⟶ X₃) (huQ : uQh = uQ ≫ ηf ≫ rfi)
    (M : X₄ ⟶ X₆) (rsh : X₄ ⟶ X₃) (rfh : X₃ ⟶ X₂) (rqσ : X₂ ⟶ X₅) (rs'i : X₅ ⟶ X₆)
    (hm : M = rsh ≫ rfh ≫ rqσ ≫ rs'i) (hsr : rsi ≫ rsh = 𝟙 _) (hfr : rfi ≫ rfh = 𝟙 _)
    (gσ : X₁ ⟶ X₇) (η' : X₇ ⟶ X₅) (h4 : gσ ≫ η' = ηf ≫ rqσ)
    (su : A₀ ⟶ A₁) (R : A₁ ⟶ X₆) (mi : A₁ ⟶ X₇) (hR : R = mi ≫ η' ≫ rs'i)
    (s₂ : A₁ ⟶ B₁) (qσi : B₁ ⟶ X₇) (hmi : mi = s₂ ≫ qσi) (qsu : B₀ ⟶ B₁)
    (h7 : su ≫ s₂ = sh ≫ qsu) (h8 : uQ ≫ gσ = qsu ≫ qσi) :
    uS ≫ M = su ≫ R := by
  have huS : uS = sh ≫ uQh ≫ rsi := by
    rw [reassoc_of% hnat, hFs, Category.comp_id]
  rw [huS, hm, hR, hmi, huQ]
  simp only [Category.assoc]
  rw [reassoc_of% hsr, reassoc_of% hfr, ← reassoc_of% h4, reassoc_of% h8, ← reassoc_of% h7]

/-- An identity `a ≫ b ≫ c = d` with `c` invertible, solved for `a ≫ b` and carried by a
functor. -/
private lemma map_comp_eq_of_comp_hom {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X Y Z W : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ≅ W) (d : X ⟶ W) (h : a ≫ b ≫ c.hom = d) :
    F.map a ≫ F.map b = F.map d ≫ F.map c.inv := by
  rw [← h, ← F.map_comp, ← F.map_comp, Category.assoc, Category.assoc, c.hom_inv_id,
    Category.comp_id]

omit [g.PreservesInjectiveObjects] in
/-- **The derived unit on a single object** is the unit placed in degree zero followed by the
canonical map `g(f(Y))[0] ⟶ Rg(f(Y)[0])`, read through `f̄(Y[0]) ≅ f(Y)[0]`. -/
theorem derivedUnit_app_single (Y : D₀) :
    (derivedUnit adj).app ((DerivedCategory.Plus.singleFunctor D₀ 0).obj Y) ≫
        g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusObjSingleIso Y).hom =
      (DerivedCategory.Plus.singleFunctor D₀ 0).map (adj.unit.app Y) ≫
        (Stacks.Cohomology.singleRightDerivedUnit g).app (f.obj Y) := by
  let sY := (Functor.singleFunctorPlusIsoCompQh (A := D₀) 0).app Y
  let K := (HomotopyCategory.Plus.singleFunctor D₀ 0).obj Y
  have hσg : Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom g (f.obj Y) =
      (g.mapHomotopyCategoryPlusObjSingleIso 0 (f.obj Y)).hom := by
    refine (HomotopyCategory.Plus.ι D₀).map_injective ?_
    refine (Stacks.Cohomology.ModulePushforwardComparison.ι_map_singleMapPlusHom g _).trans ?_
    refine (Stacks.Cohomology.ModulePushforwardComparison.mapHomotopyCategorySingleFunctor_hom_app
      g _).trans ?_
    exact (ι_map_mapHomotopyCategoryPlusObjSingleIso_hom g _).symm
  have hmi : (Functor.mapSingleFunctorCompQhIso g).inv.app (f.obj Y) =
      (Functor.singleFunctorPlusIsoCompQh (A := D₀) 0).hom.app (g.obj (f.obj Y)) ≫
        DerivedCategory.Plus.Qh.map (g.mapHomotopyCategoryPlusObjSingleIso 0 (f.obj Y)).inv := by
    rw [← cancel_epi ((Functor.mapSingleFunctorCompQhIso g).hom.app (f.obj Y)),
      Iso.hom_inv_id_app, reassoc_of%
        (Stacks.Cohomology.ModulePushforwardComparison.mapSingleFunctorCompQhIso_hom_app_comp
          g (f.obj Y)), hσg, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hm : g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusObjSingleIso Y).hom =
      g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlus.map sY.hom) ≫
        g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        g.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map (f.mapHomotopyCategoryPlusObjSingleIso 0 Y).hom) ≫
        g.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).inv.app (f.obj Y)) := by
    rw [Functor.mapDerivedCategoryPlusObjSingleIso_hom]
    simp only [Functor.map_comp]
    rfl
  exact pasteUnitSingle sY.hom _ _ _ _ ((derivedUnit adj).naturality sY.hom)
    (((f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus).mapIso sY).hom_inv_id)
    _ _ _ (derivedUnit_app_Qh adj K) _ _ _ _ _ hm
    (((f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus).mapIso sY).inv_hom_id)
    ((g.rightDerivedFunctorPlus.mapIso (f.mapDerivedCategoryPlusFactorsh.app K)).inv_hom_id)
    _ _ (g.rightDerivedFunctorPlusUnith.naturality (f.mapHomotopyCategoryPlusObjSingleIso 0 Y).hom)
    _ _ _ (Stacks.Cohomology.singleRightDerivedUnit_app g (f.obj Y)) _ _ hmi _
    ((Functor.singleFunctorPlusIsoCompQh (A := D₀) 0).hom.naturality (adj.unit.app Y))
    (map_comp_eq_of_comp_hom DerivedCategory.Plus.Qh _ _
      (g.mapHomotopyCategoryPlusObjSingleIso 0 (f.obj Y)) _ (unit_single_plus adj Y))

/-- Bookkeeping for `lerayPullback_app_single`, in arbitrary categories. -/
private lemma pasteLeraySingle {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X Y Y' : 𝒦} {Z Z' : 𝒦'} (u : X ⟶ Y) (m' : Y ⟶ Y') (li : F.obj Y ⟶ Z) (m : Z ⟶ Z')
    (li' : F.obj Y' ⟶ Z') (b : X ⟶ Y') (hn : F.map m' ≫ li' = li ≫ m) (hb : u ≫ m' = b) :
    (F.map u ≫ li) ≫ m = F.map b ≫ li' := by
  rw [Category.assoc, ← hn, ← hb, F.map_comp, Category.assoc]

/-- **The pullback on derived sections at a single object** is `RΔ₀` of the derived unit
`Y[0] ⟶ Rg(f(Y)[0])` followed by the inverse of the Leray factorization, read through
`f̄(Y[0]) ≅ f(Y)[0]`.  At the crystalline topoi this is `...SmallSite.derivedCrisPullbackMap`. -/
theorem lerayPullback_app_single (Y : D₀) :
    (lerayPullback adj Δ₀ Δ eΔ).app ((DerivedCategory.Plus.singleFunctor D₀ 0).obj Y) ≫
        Δ.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusObjSingleIso Y).hom =
      Δ₀.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor D₀ 0).map
          (adj.unit.app Y) ≫ (Stacks.Cohomology.singleRightDerivedUnit g).app (f.obj Y)) ≫
        (lerayIso Δ₀ Δ eΔ).inv.app ((DerivedCategory.Plus.singleFunctor D 0).obj (f.obj Y)) :=
  pasteLeraySingle Δ₀.rightDerivedFunctorPlus _ _ _ _ _ _
    ((lerayIso Δ₀ Δ eΔ).inv.naturality (f.mapDerivedCategoryPlusObjSingleIso Y).hom)
    (derivedUnit_app_single adj Y)

end Leray

section Restriction

variable {C' D' A' : Type*} [Category* C'] [Category* D'] [Category* A']
  [Abelian C'] [Abelian D'] [Abelian A']
  [HasDerivedCategory C'] [HasDerivedCategory D'] [HasDerivedCategory A']
  [EnoughInjectives C'] [EnoughInjectives D']
  (G₁ : C' ⥤ A') (Q' : C' ⥤ D') (Δ' : D' ⥤ A') [G₁.Additive] [Q'.Additive] [Δ'.Additive]
  [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
  (h : ∀ I : C', Injective I → Δ'.rightAcyclic (Q'.obj I)) (e : G₁ ≅ Q' ⋙ Δ')

/-- **`RG₁ ≅ Q̄ ⋙ RΔ'`** for `G₁ ≅ Q ⋙ Δ'` with `Q` exact carrying injectives to `Δ'`-acyclic
objects: [Stacks, Tag 015M] followed by the replacement of `RQ` by the functor `Q` induces. -/
def restrictionIso : G₁.rightDerivedFunctorPlus ≅
    Q'.mapDerivedCategoryPlus ⋙ Δ'.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusNatIso e ≪≫
    Stacks.Cohomology.DerivedPushforwardSections.compIso Q' Δ' h ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus Q')
      Δ'.rightDerivedFunctorPlus

/-- Bookkeeping for `unit_comp_restrictionIso_hom_app`, in an arbitrary category. -/
private lemma pasteRestriction {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ : 𝒦}
    (η : X₀ ⟶ X₁) (n : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (ne : X₀ ⟶ Y₁) (η' : Y₁ ⟶ X₂)
    (hn : η ≫ n = ne ≫ η') (q : Y₁ ⟶ Y₁) (ηΔ : Y₁ ⟶ Y₂) (rη : Y₂ ⟶ X₃)
    (hc : η' ≫ c = q ≫ ηΔ ≫ rη) (hq : q = 𝟙 _) (rf : Y₂ ⟶ X₄) (hw : rη ≫ w = rf) :
    η ≫ n ≫ c ≫ w = ne ≫ ηΔ ≫ rf := by
  subst hq
  rw [Category.id_comp] at hc
  rw [reassoc_of% hn, reassoc_of% hc, hw]

/-- **`restrictionIso` after the unit**: `e` applied degreewise followed by the unit of `RΔ'` at
`Q(K)`. -/
theorem unit_comp_restrictionIso_hom_app (K : HomotopyCategory.Plus C') :
    G₁.rightDerivedFunctorPlusUnith.app K ≫
        (restrictionIso G₁ Q' Δ' h e).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        Δ'.rightDerivedFunctorPlusUnith.app (Q'.mapHomotopyCategoryPlus.obj K) ≫
        Δ'.rightDerivedFunctorPlus.map (Q'.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have hn := Functor.rightDerivedNatTrans_app G₁.rightDerivedFunctorPlus
    (Q' ⋙ Δ').rightDerivedFunctorPlus G₁.rightDerivedFunctorPlusUnith
    (Q' ⋙ Δ').rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C')
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatIso e).hom DerivedCategory.Plus.Qh) K
  exact pasteRestriction _ _ _ _ _ _ hn _ _ _ (Functor.rightDerivedFunctorPlusComp_fac_app Q' Δ' K)
    (Qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app _ _ K) _
    ((Δ'.rightDerivedFunctorPlus.map_comp _ _).symm.trans (congrArg Δ'.rightDerivedFunctorPlus.map
      (Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app Q' K)))

end Restriction

section Splitting

variable {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z] [Abelian X] [Abelian Y]
  [Abelian Z] [HasDerivedCategory X] [HasDerivedCategory Y] [HasDerivedCategory Z]
  [EnoughInjectives X] [EnoughInjectives Y] (F : X ⥤ Y) (G : Y ⥤ Z) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **`R(F ⋙ G) ≅ RF ⋙ Ḡ`** for an exact `G`, as an isomorphism; its `hom` is
`CategoryTheory.Functor.derivedSquareSplitting`. -/
def splitIso : (F ⋙ G).rightDerivedFunctorPlus ≅
    F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic F G
      (fun _ _ => Functor.rightAcyclic_of_exact _ _) ≪≫
    Functor.isoWhiskerLeft F.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus G)

/-- The `hom` of `splitIso` is `CategoryTheory.Functor.derivedSquareSplitting`. -/
theorem splitIso_hom : (splitIso F G).hom = Functor.derivedSquareSplitting F G := rfl

/-- `splitIso` after the unit. -/
theorem unit_comp_splitIso_hom_app (L : HomotopyCategory.Plus X) :
    (F ⋙ G).rightDerivedFunctorPlusUnith.app L ≫ (splitIso F G).hom.app
        (DerivedCategory.Plus.Qh.obj L) = Functor.derivedSquareNu F G L :=
  Functor.unit_comp_splitting_app F G L

/-- `splitIso` after the unit, solved for the unit. -/
theorem derivedSquareNu_comp_splitIso_inv_app (L : HomotopyCategory.Plus X) :
    Functor.derivedSquareNu F G L ≫ (splitIso F G).inv.app (DerivedCategory.Plus.Qh.obj L) =
      (F ⋙ G).rightDerivedFunctorPlusUnith.app L :=
  comp_inv_eq_of _ ((splitIso F G).app _) _ (unit_comp_splitIso_hom_app F G L)

end Splitting

section Degreewise

variable {X Y : Type*} [Category* X] [Category* Y] [Preadditive X] [Preadditive Y]

/-- The degreewise action of an isomorphism of additive functors is that of its `hom`. -/
theorem mapHomotopyCategoryPlusNatIso_hom_app {F G : X ⥤ Y} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus X) :
    (Functor.mapHomotopyCategoryPlusNatIso e).hom.app K =
      (Functor.mapHomotopyCategoryPlusNatTrans e.hom).app K := by
  have h := ((HomotopyCategory.plus Y).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus X)).map_preimage (X := F.mapHomotopyCategoryPlus)
    (Y := G.mapHomotopyCategoryPlus) (Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι X)
      (Functor.mapHomotopyCategoryNatIso e (ComplexShape.up ℤ))).hom
  ext
  exact congr_app h K

end Degreewise

section DegreewiseUnit

variable {X Y : Type*} [Category* X] [Category* Y] [Abelian X] [Abelian Y]

/-- The unit of the degreewise adjunction on bounded below homotopy categories is the degreewise
action of the unit. -/
theorem mapHomotopyCategoryPlus_unit_app {F : X ⥤ Y} {G : Y ⥤ X}
    [F.Additive] [G.Additive] (adj : F ⊣ G) (K : HomotopyCategory.Plus X) :
    adj.mapHomotopyCategoryPlus.unit.app K =
      (Functor.mapHomotopyCategoryPlusNatTrans adj.unit).app K := by
  ext
  exact ι_map_mapHomotopyCategoryPlus_unit_app adj K

end DegreewiseUnit

section Comparison

variable {C₀ C D₀ D M₀ M A : Type*} [Category* C₀] [Category* C] [Category* D₀] [Category* D]
  [Category* M₀] [Category* M] [Category* A] [Abelian C₀] [Abelian C] [Abelian D₀] [Abelian D]
  [Abelian M₀] [Abelian M] [Abelian A]
  [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory D₀] [HasDerivedCategory D]
  [HasDerivedCategory M₀] [HasDerivedCategory M] [HasDerivedCategory A]
  [EnoughInjectives C₀] [EnoughInjectives C] [EnoughInjectives D₀] [EnoughInjectives D]
  [EnoughInjectives M₀] [EnoughInjectives M]
  {Γ₀ : C₀ ⥤ M₀} {Γ : C ⥤ M} {P : C₀ ⥤ C} {r : M ⥤ M₀} {φ₀ : M₀ ⥤ A}
  [Γ₀.Additive] [Γ.Additive] [P.Additive] [r.Additive] [φ₀.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [PreservesFiniteLimits φ₀] [PreservesFiniteColimits φ₀]
  {f : D₀ ⥤ D} {g : D ⥤ D₀} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f] [g.PreservesInjectiveObjects]
  (adj : f ⊣ g)
  {Δ₀ : D₀ ⥤ A} {Δ : D ⥤ A} [Δ₀.Additive] [Δ.Additive] [PreservesFiniteLimits Δ₀]
  (eΔ : g ⋙ Δ₀ ≅ Δ)
  {Q₀ : C₀ ⥤ D₀} {Q : C ⥤ D} [Q₀.Additive] [Q.Additive]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  (h₀ : ∀ I : C₀, Injective I → Δ₀.rightAcyclic (Q₀.obj I))
  (h₁ : ∀ I : C, Injective I → Δ.rightAcyclic (Q.obj I))
  (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) (e₀ : Γ₀ ⋙ φ₀ ≅ Q₀ ⋙ Δ₀) (e₁ : Γ ⋙ r ⋙ φ₀ ≅ Q ⋙ Δ)
  (c : Q₀ ⋙ f ⟶ P ⋙ Q)

variable (r φ₀) in
/-- **The comparison on the target**, `φ̄₀(r̄(RΓ(-))) ≅ RΔ(Q̄(-))`. -/
def targetIso : Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus ⋙ φ₀.mapDerivedCategoryPlus ≅
    Q.mapDerivedCategoryPlus ⋙ Δ.rightDerivedFunctorPlus :=
  (Functor.isoWhiskerRight (splitIso Γ r) φ₀.mapDerivedCategoryPlus).symm ≪≫
    (splitIso (Γ ⋙ r) φ₀).symm ≪≫ restrictionIso (Γ ⋙ r ⋙ φ₀) Q Δ h₁ e₁

/-- Bookkeeping for `targetIso_fac`, in arbitrary categories. -/
private lemma pasteTarget {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X W V : 𝒦'} {Y₀ Y₁ Y₂ : 𝒦} (a : X ⟶ F.obj Y₀) (ν : Y₀ ⟶ Y₁) (si : Y₁ ⟶ Y₂)
    (η : Y₀ ⟶ Y₂) (hν : ν ≫ si = η) (s'i : F.obj Y₂ ⟶ W) (η' : X ⟶ W)
    (hη' : (a ≫ F.map η) ≫ s'i = η') (rh : W ⟶ V) (R : X ⟶ V) (hR : η' ≫ rh = R) :
    a ≫ F.map ν ≫ F.map si ≫ s'i ≫ rh = R := by
  rw [← hR, ← hη', ← hν, F.map_comp]
  simp only [Category.assoc]

variable (r φ₀) in
/-- **`targetIso` after the unit**: at a bounded below complex `M`, the canonical map
`φ₀(r(Γ(M))) ⟶ φ̄₀(r̄(RΓ(M)))` followed by `targetIso` is `e₁` applied degreewise followed by the
unit of `RΔ` at `Q(M)`. -/
theorem targetIso_fac (L : HomotopyCategory.Plus C) :
    φ₀.mapDerivedCategoryPlusFactorsh.inv.app (r.mapHomotopyCategoryPlus.obj
        (Γ.mapHomotopyCategoryPlus.obj L)) ≫
      φ₀.mapDerivedCategoryPlus.map (Functor.derivedSquareNu Γ r L) ≫
      (targetIso r φ₀ h₁ e₁).hom.app (DerivedCategory.Plus.Qh.obj L) =
    DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso e₁).hom.app L) ≫
      Δ.rightDerivedFunctorPlusUnith.app (Q.mapHomotopyCategoryPlus.obj L) ≫
      Δ.rightDerivedFunctorPlus.map (Q.mapDerivedCategoryPlusFactorsh.inv.app L) :=
  pasteTarget φ₀.mapDerivedCategoryPlus _ _ _ _ (derivedSquareNu_comp_splitIso_inv_app Γ r L) _ _
    (derivedSquareNu_comp_splitIso_inv_app (Γ ⋙ r) φ₀ L) _ _
    (unit_comp_restrictionIso_hom_app (Γ ⋙ r ⋙ φ₀) Q Δ h₁ e₁ L)

/-- **The derived comparison `Q̄₀ ⋙ f̄ ⟶ P̄ ⋙ Q̄`** induced by `c : Q₀ ⋙ f ⟶ P ⋙ Q`. -/
def derivedComparison :
    Q₀.mapDerivedCategoryPlus ⋙ f.mapDerivedCategoryPlus ⟶
      P.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus :=
  (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso Q₀ f).hom ≫
    Functor.mapDerivedCategoryPlusCompTrans c

/-- Bookkeeping for `derivedComparison_fac`, in an arbitrary category. -/
private lemma pasteComparison {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₅ : 𝒦}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (b' : X₂ ⟶ X₁) (a' : X₁ ⟶ X₀) (x : X₀ ⟶ X₃) (x' : X₃ ⟶ X₀)
    (R : X₀ ⟶ X₅) (hb : b ≫ b' = 𝟙 _) (ha : a ≫ a' = 𝟙 _) (hx : x ≫ x' = 𝟙 _) :
    a ≫ b ≫ (b' ≫ a' ≫ x) ≫ x' ≫ R = R := by
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% ha, reassoc_of% hx]

omit [EnoughInjectives C₀] [EnoughInjectives C] [EnoughInjectives D₀] [EnoughInjectives D] in
/-- **`derivedComparison` on the image of a complex**: `c` applied degreewise. -/
theorem derivedComparison_fac (K : HomotopyCategory.Plus C₀) :
    f.mapDerivedCategoryPlusFactorsh.inv.app (Q₀.mapHomotopyCategoryPlus.obj K) ≫
        f.mapDerivedCategoryPlus.map (Q₀.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        (derivedComparison c).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans c).app K) ≫
        Q.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj K) ≫
        Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [derivedComparison, NatTrans.comp_app]
  rw [Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso_hom_app_Qh,
    Functor.mapDerivedCategoryPlusCompTrans_app]
  exact pasteComparison _ _ _ _ _ _ _
    ((f.mapDerivedCategoryPlus.mapIso (Q₀.mapDerivedCategoryPlusFactorsh.app K)).inv_hom_id)
    ((f.mapDerivedCategoryPlusFactorsh.app _).inv_hom_id)
    (((Q₀ ⋙ f).mapDerivedCategoryPlusFactorsh.app K).inv_hom_id)

/-- **The comparison through the restriction and the pullback on derived sections**:
`R(Γ₀ ⋙ φ₀) ≅ Q̄₀ ⋙ RΔ₀ ⟶ Q̄₀ ⋙ f̄ ⋙ RΔ ⟶ P̄ ⋙ Q̄ ⋙ RΔ`. -/
def comparisonViaPullback :
    (Γ₀ ⋙ φ₀).rightDerivedFunctorPlus ⟶
      P.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus ⋙ Δ.rightDerivedFunctorPlus :=
  (restrictionIso (Γ₀ ⋙ φ₀) Q₀ Δ₀ h₀ e₀).hom ≫
    Functor.whiskerLeft Q₀.mapDerivedCategoryPlus (lerayPullback adj Δ₀ Δ eΔ) ≫
    Functor.whiskerRight (derivedComparison c) Δ.rightDerivedFunctorPlus

variable (r φ₀) in
/-- **The comparison through the derived square**:
`R(Γ₀ ⋙ φ₀) ≅ RΓ₀ ⋙ φ̄₀ ⟶ P̄ ⋙ RΓ ⋙ r̄ ⋙ φ̄₀ ≅ P̄ ⋙ Q̄ ⋙ RΔ`. -/
def comparisonViaSquare :
    (Γ₀ ⋙ φ₀).rightDerivedFunctorPlus ⟶
      P.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus ⋙ Δ.rightDerivedFunctorPlus :=
  (splitIso Γ₀ φ₀).hom ≫
    Functor.whiskerRight (Functor.derivedSquareTrans' α) φ₀.mapDerivedCategoryPlus ≫
    Functor.whiskerLeft P.mapDerivedCategoryPlus (targetIso r φ₀ h₁ e₁).hom

/-- A functor carries an identity of threefold composites to one, in arbitrary categories. -/
private lemma map_eq_three {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X Y Z W Y' Z' : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (a' : X ⟶ Y') (b' : Y' ⟶ Z')
    (c' : Z' ⟶ W) (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp, F.map_comp]

/-- Bookkeeping for `unit_comp_comparisonViaPullback_app`, in an arbitrary category. -/
private lemma pasteViaPullback {𝒦 : Type*} [Category* 𝒦]
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ Y₇ : 𝒦}
    (η : X₀ ⟶ X₁) (rh : X₁ ⟶ X₂) (tl : X₂ ⟶ X₃) (dc : X₃ ⟶ X₄)
    (e : X₀ ⟶ Y₁) (ηΔ₀ : Y₁ ⟶ Y₂) (q₀ : Y₂ ⟶ X₂) (h1 : η ≫ rh = e ≫ ηΔ₀ ≫ q₀)
    (tq : Y₂ ⟶ Y₃) (fq : Y₃ ⟶ X₃) (h2 : q₀ ≫ tl = tq ≫ fq)
    (u : Y₁ ⟶ Y₄) (ηΔ : Y₄ ⟶ Y₅) (ffi : Y₅ ⟶ Y₃) (h3 : ηΔ₀ ≫ tq = u ≫ ηΔ ≫ ffi)
    (qc : Y₅ ⟶ Y₆) (qfi : Y₆ ⟶ Y₇) (qpf : Y₇ ⟶ X₄) (h4 : ffi ≫ fq ≫ dc = qc ≫ qfi ≫ qpf) :
    η ≫ rh ≫ tl ≫ dc = e ≫ u ≫ ηΔ ≫ qc ≫ qfi ≫ qpf := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4]

omit [HasDerivedCategory M₀] [EnoughInjectives C] [EnoughInjectives M₀] [PreservesFiniteLimits φ₀]
  [PreservesFiniteColimits φ₀] in
/-- **`comparisonViaPullback` after the unit.** -/
theorem unit_comp_comparisonViaPullback_app (K : HomotopyCategory.Plus C₀) :
    (Γ₀ ⋙ φ₀).rightDerivedFunctorPlusUnith.app K ≫
        (comparisonViaPullback adj eΔ h₀ e₀ c).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso e₀).hom.app K) ≫
        DerivedCategory.Plus.Qh.map (Δ₀.mapHomotopyCategoryPlus.map
          (adj.mapHomotopyCategoryPlus.unit.app (Q₀.mapHomotopyCategoryPlus.obj K)) ≫
          (Functor.mapHomotopyCategoryPlusNatIso eΔ).hom.app
            (f.mapHomotopyCategoryPlus.obj (Q₀.mapHomotopyCategoryPlus.obj K))) ≫
        Δ.rightDerivedFunctorPlusUnith.app
          (f.mapHomotopyCategoryPlus.obj (Q₀.mapHomotopyCategoryPlus.obj K)) ≫
        Δ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans c).app K)) ≫
        Δ.rightDerivedFunctorPlus.map
          (Q.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj K)) ≫
        Δ.rightDerivedFunctorPlus.map
          (Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) :=
  pasteViaPullback _ _ _ _ _ _ _ (unit_comp_restrictionIso_hom_app (Γ₀ ⋙ φ₀) Q₀ Δ₀ h₀ e₀ K)
    _ _ ((lerayPullback adj Δ₀ Δ eΔ).naturality (Q₀.mapDerivedCategoryPlusFactorsh.inv.app K))
    _ _ _ (unit_comp_lerayPullback_app adj Δ₀ Δ eΔ (Q₀.mapHomotopyCategoryPlus.obj K))
    _ _ _ (map_eq_three Δ.rightDerivedFunctorPlus _ _ _ _ _ _ (derivedComparison_fac c K))

/-- Bookkeeping for `unit_comp_comparisonViaSquare_app`, in arbitrary categories. -/
private lemma pasteViaSquare {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X₀ X₁ X₂ W W' : 𝒦'} {Y₀ Y₁ Z₀ Z₁ Z₂ : 𝒦}
    (η : X₀ ⟶ X₁) (sp : X₁ ⟶ F.obj Y₀) (a₀ : X₀ ⟶ F.obj Z₀) (ηΓ₀ : Z₀ ⟶ Y₀)
    (h1 : η ≫ sp = a₀ ≫ F.map ηΓ₀)
    (d : Y₀ ⟶ Y₁) (qα : Z₀ ⟶ Z₁) (ν : Z₁ ⟶ Z₂) (rp : Z₂ ⟶ Y₁) (h2 : ηΓ₀ ≫ d = qα ≫ ν ≫ rp)
    (qφα : X₀ ⟶ X₂) (a₁ : X₂ ⟶ F.obj Z₁) (h3 : a₀ ≫ F.map qα = qφα ≫ a₁)
    (ψ : F.obj Y₁ ⟶ W) (ψ' : F.obj Z₂ ⟶ W') (qp : W' ⟶ W) (h4 : F.map rp ≫ ψ = ψ' ≫ qp)
    (E : X₂ ⟶ W') (h5 : a₁ ≫ F.map ν ≫ ψ' = E) :
    η ≫ sp ≫ F.map d ≫ ψ = qφα ≫ E ≫ qp := by
  rw [reassoc_of% h1, ← F.map_comp_assoc, h2, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [h4, reassoc_of% h3, ← reassoc_of% h5]

/-- **`comparisonViaSquare` after the unit.** -/
theorem unit_comp_comparisonViaSquare_app (K : HomotopyCategory.Plus C₀) :
    (Γ₀ ⋙ φ₀).rightDerivedFunctorPlusUnith.app K ≫
        (comparisonViaSquare r φ₀ h₁ α e₁).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map (φ₀.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans α).app K)) ≫
        (DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusNatIso e₁).hom.app (P.mapHomotopyCategoryPlus.obj K)) ≫
          Δ.rightDerivedFunctorPlusUnith.app
            (Q.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) ≫
          Δ.rightDerivedFunctorPlus.map
            (Q.mapDerivedCategoryPlusFactorsh.inv.app (P.mapHomotopyCategoryPlus.obj K))) ≫
        Δ.rightDerivedFunctorPlus.map
          (Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) :=
  pasteViaSquare φ₀.mapDerivedCategoryPlus _ _ _ _ (unit_comp_splitIso_hom_app Γ₀ φ₀ K)
    _ _ _ _ (Functor.unit_comp_derivedSquareTrans'_app α K)
    _ _ (φ₀.mapDerivedCategoryPlusFactorsh.inv.naturality
      ((Functor.mapHomotopyCategoryPlusNatTrans α).app K)).symm
    _ _ _ ((targetIso r φ₀ h₁ e₁).hom.naturality (P.mapDerivedCategoryPlusFactorsh.inv.app K))
    _ (targetIso_fac r φ₀ h₁ e₁ (P.mapHomotopyCategoryPlus.obj K))

/-- Reassociation in the middle of a composite, in an arbitrary category. -/
private lemma assoc_mid {𝒦 : Type*} [Category* 𝒦] {X Y Z W V : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (d : W ⟶ V) (R : X ⟶ V) (h : a ≫ b ≫ c ≫ d = R) : a ≫ (b ≫ c) ≫ d = R := by
  rw [Category.assoc]
  exact h

omit [HasDerivedCategory C₀] [HasDerivedCategory C] [HasDerivedCategory D₀] [HasDerivedCategory D]
  [HasDerivedCategory M₀] [HasDerivedCategory M] [HasDerivedCategory A] [EnoughInjectives C₀]
  [EnoughInjectives C] [EnoughInjectives D₀] [EnoughInjectives D] [EnoughInjectives M₀]
  [EnoughInjectives M] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r] [PreservesFiniteLimits φ₀]
  [PreservesFiniteColimits φ₀] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [g.PreservesInjectiveObjects] [PreservesFiniteLimits Δ₀] [PreservesFiniteLimits Q₀]
  [PreservesFiniteColimits Q₀] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q] in
/-- **The underived hypothesis, applied degreewise.** -/
theorem degreewise_comparison
    (hU : ∀ X : C₀, φ₀.map (α.app X) ≫ e₁.hom.app (P.obj X) =
      e₀.hom.app X ≫ Δ₀.map (adj.unit.app (Q₀.obj X)) ≫ eΔ.hom.app (f.obj (Q₀.obj X)) ≫
        Δ.map (c.app X)) (K : HomotopyCategory.Plus C₀) :
    (Functor.mapHomotopyCategoryPlusNatIso e₀).hom.app K ≫
        (Δ₀.mapHomotopyCategoryPlus.map
          (adj.mapHomotopyCategoryPlus.unit.app (Q₀.mapHomotopyCategoryPlus.obj K)) ≫
          (Functor.mapHomotopyCategoryPlusNatIso eΔ).hom.app
            (f.mapHomotopyCategoryPlus.obj (Q₀.mapHomotopyCategoryPlus.obj K))) ≫
        Δ.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans c).app K) =
      φ₀.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫
        (Functor.mapHomotopyCategoryPlusNatIso e₁).hom.app (P.mapHomotopyCategoryPlus.obj K) := by
  have hU' : e₀.hom ≫ Functor.whiskerLeft Q₀ (Functor.whiskerRight adj.unit Δ₀) ≫
      Functor.whiskerLeft (Q₀ ⋙ f) eΔ.hom ≫ Functor.whiskerRight c Δ =
      Functor.whiskerRight α φ₀ ≫ Functor.whiskerLeft P e₁.hom :=
    NatTrans.ext (funext fun X => (hU X).symm)
  have key := congrArg (fun τ => (Functor.mapHomotopyCategoryPlusNatTrans τ).app K) hU'
  simp only [Functor.mapHomotopyCategoryPlusNatTrans_comp_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerLeft_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerRight_app] at key
  rw [mapHomotopyCategoryPlusNatIso_hom_app, mapHomotopyCategoryPlusNatIso_hom_app,
    mapHomotopyCategoryPlusNatIso_hom_app, mapHomotopyCategoryPlus_unit_app]
  exact assoc_mid _ _ _ _ _ key

/-- Bookkeeping for `comparisonViaPullback_eq_comparisonViaSquare`, in an arbitrary
category. -/
private lemma pasteMain {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ : 𝒦}
    (q₀ : X₀ ⟶ X₁) (q₁ : X₁ ⟶ X₂) (η : X₂ ⟶ X₃) (rc : X₃ ⟶ X₄) (rq : X₄ ⟶ X₅) (rp : X₅ ⟶ X₆)
    (qc : X₂ ⟶ Y₂) (η' : Y₂ ⟶ X₄) (hn : η ≫ rc = qc ≫ η') (qα : X₀ ⟶ Y₁) (qe : Y₁ ⟶ Y₂)
    (h6 : q₀ ≫ q₁ ≫ qc = qα ≫ qe) :
    q₀ ≫ q₁ ≫ η ≫ rc ≫ rq ≫ rp = qα ≫ (qe ≫ η' ≫ rq) ≫ rp := by
  rw [reassoc_of% hn, reassoc_of% h6]
  simp only [Category.assoc]

/-- A functor carries an identity `a ≫ b ≫ c = a' ≫ b'` to one, in arbitrary categories. -/
private lemma map_eq_three_two {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X Y Z W Y' : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (a' : X ⟶ Y') (b' : Y' ⟶ W)
    (h : a ≫ b ≫ c = a' ≫ b') : F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp]

/-- **The two comparisons agree**, as soon as the underived squares do. -/
theorem comparisonViaPullback_eq_comparisonViaSquare
    (hU : ∀ X : C₀, φ₀.map (α.app X) ≫ e₁.hom.app (P.obj X) =
      e₀.hom.app X ≫ Δ₀.map (adj.unit.app (Q₀.obj X)) ≫ eΔ.hom.app (f.obj (Q₀.obj X)) ≫
        Δ.map (c.app X)) :
    comparisonViaPullback adj eΔ h₀ e₀ c = comparisonViaSquare r φ₀ h₁ α e₁ := by
  refine Functor.rightDerived_ext (Γ₀ ⋙ φ₀).rightDerivedFunctorPlus
    (Γ₀ ⋙ φ₀).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C₀) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  refine (unit_comp_comparisonViaPullback_app adj eΔ h₀ e₀ c K).trans
    (Eq.trans ?_ (unit_comp_comparisonViaSquare_app h₁ α e₁ K).symm)
  exact pasteMain _ _ _ _ _ _ _ _
    (Δ.rightDerivedFunctorPlusUnith.naturality
      ((Functor.mapHomotopyCategoryPlusNatTrans c).app K)).symm
    _ _ (map_eq_three_two DerivedCategory.Plus.Qh _ _ _ _ _
      (degreewise_comparison adj eΔ α e₀ e₁ c hU K))

omit [HasDerivedCategory M₀] [HasDerivedCategory M] [EnoughInjectives M₀] [EnoughInjectives M]
  [g.PreservesInjectiveObjects] in
/-- Three cancellations, in an arbitrary category. -/
private lemma cancelSix {𝒦 : Type*} [Category* 𝒦] {X Y Z W : 𝒦} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (c' : W ⟶ Z) (i : Z ⟶ Z) (b' : Z ⟶ Y) (a' : Y ⟶ X) (hi : i = 𝟙 _)
    (ha : a ≫ a' = 𝟙 _) (hb : b ≫ b' = 𝟙 _) (hc : c ≫ c' = 𝟙 _) :
    (a ≫ b ≫ c) ≫ c' ≫ i ≫ b' ≫ a' = 𝟙 _ := by
  subst hi
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% hc, reassoc_of% hb, ha]

omit [EnoughInjectives C₀] [EnoughInjectives D₀] [EnoughInjectives D] in
/-- The composition comparison of `Q̄₀ ⋙ f̄` followed by the transformation induced by the
identity of `Q₀ ⋙ f` is the identity. -/
theorem mapDerivedCategoryPlusCompIso_hom_comp_compTrans_id :
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso Q₀ f).hom ≫
        Functor.mapDerivedCategoryPlusCompTrans (𝟙 (Q₀ ⋙ f)) = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₀)
    (fun K => ?_)
  have hid : (Functor.mapHomotopyCategoryPlusNatTrans (𝟙 (Q₀ ⋙ f))).app K = 𝟙 _ := by
    ext
    exact congr_app (NatTrans.mapHomotopyCategory_id (ComplexShape.up ℤ) (Q₀ ⋙ f)) K.obj
  simp only [NatTrans.comp_app, NatTrans.id_app]
  rw [Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso_hom_app_Qh,
    Functor.mapDerivedCategoryPlusCompTrans_app, hid]
  exact cancelSix _ _ _ _ _ _ _ (DerivedCategory.Plus.Qh.map_id _)
    ((f.mapDerivedCategoryPlus.mapIso (Q₀.mapDerivedCategoryPlusFactorsh.app K)).hom_inv_id)
    ((f.mapDerivedCategoryPlusFactorsh.app _).hom_inv_id)
    (((Q₀ ⋙ f).mapDerivedCategoryPlusFactorsh.app K).inv_hom_id)

/-- Bookkeeping for `derivedComparison_single`, in an arbitrary category. -/
private lemma pasteCompSingle {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₃ : 𝒦}
    (ch : X₀ ⟶ X₁) (ct : X₁ ⟶ X₂) (qp : X₂ ⟶ X₃) (qs : X₃ ⟶ X₄) (s : X₁ ⟶ Y₁) (sc : Y₁ ⟶ X₄)
    (hc : s ≫ sc = ct ≫ qp ≫ qs) (sid : Y₁ ⟶ Y₁) (hsid : sid = 𝟙 _) (ci : X₁ ⟶ X₀)
    (fq : X₀ ⟶ Y₃) (fs : Y₃ ⟶ Y₁) (hi : s ≫ sid = ci ≫ fq ≫ fs) (hci : ch ≫ ci = 𝟙 _) :
    (ch ≫ ct) ≫ qp ≫ qs = fq ≫ fs ≫ sc := by
  subst hsid
  rw [Category.comp_id] at hi
  rw [Category.assoc, ← hc, hi]
  simp only [Category.assoc]
  rw [reassoc_of% hci]

omit [EnoughInjectives D] in
/-- **`derivedComparison` on a single object** is `c` placed in degree zero. -/
theorem derivedComparison_single (X : C₀) :
    (derivedComparison c).app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
        Q.mapDerivedCategoryPlus.map (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (Q.mapDerivedCategoryPlusObjSingleIso (P.obj X)).hom =
      f.mapDerivedCategoryPlus.map (Q₀.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (f.mapDerivedCategoryPlusObjSingleIso (Q₀.obj X)).hom ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (c.app X) :=
  pasteCompSingle _ _ _ _ _ _ (Functor.mapDerivedCategoryPlusObjSingleIso_comp c X) _
    ((congrArg (DerivedCategory.Plus.singleFunctor D 0).map (NatTrans.id_app (Q₀ ⋙ f) X)).trans
      (CategoryTheory.Functor.map_id _ _)) _ _ _
    (Functor.mapDerivedCategoryPlusObjSingleIso_comp (𝟙 (Q₀ ⋙ f)) X)
    (congr_app (mapDerivedCategoryPlusCompIso_hom_comp_compTrans_id (Q₀ := Q₀) (f := f)) _)

/-- Bookkeeping for `derivedSquareMap_comp_targetIso`, in arbitrary categories. -/
private lemma pasteSingleMain {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {Y₀ Y₁ Y₂ : 𝒦} {X₀ X₁ X₂ X₃ X₅ Z₁ Z₂ Z₃ W : 𝒦'}
    (d : Y₀ ⟶ Y₁) (rp : Y₁ ⟶ Y₂) (ψY : F.obj Y₂ ⟶ X₅) (qs : X₅ ⟶ W)
    (si : F.obj Y₀ ⟶ X₀) (sh : X₀ ⟶ F.obj Y₀) (hsi : si ≫ sh = 𝟙 _)
    (rh : X₀ ⟶ X₁) (tl : X₁ ⟶ X₂) (dc : X₂ ⟶ X₃) (ψX : F.obj Y₁ ⟶ X₃)
    (hθ : rh ≫ tl ≫ dc = sh ≫ F.map d ≫ ψX) (qp : X₃ ⟶ X₅) (hb : F.map rp ≫ ψY = ψX ≫ qp)
    (q₀ : X₁ ⟶ Z₁) (tq : Z₁ ⟶ Z₂) (fq : X₂ ⟶ Z₂) (hc : q₀ ≫ tq = tl ≫ fq)
    (fs : Z₂ ⟶ Z₃) (LM : Z₁ ⟶ Z₃) (hd : tq ≫ fs = LM) (rc : Z₃ ⟶ W)
    (he : dc ≫ qp ≫ qs = fq ≫ fs ≫ rc) :
    F.map (d ≫ rp) ≫ ψY ≫ qs = si ≫ rh ≫ q₀ ≫ LM ≫ rc :=
  calc F.map (d ≫ rp) ≫ ψY ≫ qs = si ≫ sh ≫ F.map d ≫ F.map rp ≫ ψY ≫ qs := by
        rw [reassoc_of% hsi, F.map_comp, Category.assoc]
    _ = si ≫ sh ≫ F.map d ≫ ψX ≫ qp ≫ qs := by rw [reassoc_of% hb]
    _ = si ≫ (rh ≫ tl ≫ dc) ≫ qp ≫ qs := by rw [hθ]; simp only [Category.assoc]
    _ = si ≫ rh ≫ tl ≫ fq ≫ fs ≫ rc := by simp only [Category.assoc]; rw [he]
    _ = si ≫ rh ≫ q₀ ≫ tq ≫ fs ≫ rc := by rw [reassoc_of% hc]
    _ = si ≫ rh ≫ q₀ ≫ LM ≫ rc := by rw [reassoc_of% hd]

/-- **The comparison at a single object.**  Under the underived identity `hU`, the derived
comparison of the square `α` at `X[0]`, read through `φ̄₀` and `targetIso`, is the derived
pullback `lerayPullback` at `Q₀(X)[0]` followed by `c` placed in degree zero, read through
`splitIso` and `restrictionIso`. -/
theorem derivedSquareMap_comp_targetIso
    (hU : ∀ X : C₀, φ₀.map (α.app X) ≫ e₁.hom.app (P.obj X) =
      e₀.hom.app X ≫ Δ₀.map (adj.unit.app (Q₀.obj X)) ≫ eΔ.hom.app (f.obj (Q₀.obj X)) ≫
        Δ.map (c.app X)) (X : C₀) :
    φ₀.mapDerivedCategoryPlus.map (Functor.derivedSquareMap α X) ≫
        (targetIso r φ₀ h₁ e₁).hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj (P.obj X)) ≫
        Δ.rightDerivedFunctorPlus.map (Q.mapDerivedCategoryPlusObjSingleIso (P.obj X)).hom =
      (splitIso Γ₀ φ₀).inv.app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
        (restrictionIso (Γ₀ ⋙ φ₀) Q₀ Δ₀ h₀ e₀).hom.app
          ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
        Δ₀.rightDerivedFunctorPlus.map (Q₀.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (Δ₀.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor D₀ 0).map
            (adj.unit.app (Q₀.obj X)) ≫
            (Stacks.Cohomology.singleRightDerivedUnit g).app (f.obj (Q₀.obj X))) ≫
          (lerayIso Δ₀ Δ eΔ).inv.app ((DerivedCategory.Plus.singleFunctor D 0).obj
            (f.obj (Q₀.obj X)))) ≫
        Δ.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor D 0).map (c.app X)) :=
  pasteSingleMain φ₀.mapDerivedCategoryPlus _ _ _ _ _ _
    ((splitIso Γ₀ φ₀).inv_hom_id_app _) _ _ _ _
    (congr_app (comparisonViaPullback_eq_comparisonViaSquare adj eΔ h₀ h₁ α e₀ e₁ c hU) _) _
    ((targetIso r φ₀ h₁ e₁).hom.naturality (P.mapDerivedCategoryPlusObjSingleIso X).hom)
    _ _ _ ((lerayPullback adj Δ₀ Δ eΔ).naturality (Q₀.mapDerivedCategoryPlusObjSingleIso X).hom)
    _ _ (lerayPullback_app_single adj Δ₀ Δ eΔ (Q₀.obj X)) _
    (map_eq_three Δ.rightDerivedFunctorPlus _ _ _ _ _ _ (derivedComparison_single c X))

end Comparison

end Stacks.LerayPullbackComparison
