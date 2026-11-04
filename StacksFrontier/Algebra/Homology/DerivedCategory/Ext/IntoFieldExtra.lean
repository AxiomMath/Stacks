module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField

/-!
# Maps into an injective single complex, at an arbitrary model of the derived category

`StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField` states
`map_eq_zero_of_isGE_of_injective_single` and `homologyMapToInjectiveEquiv` for the standard
model `HasDerivedCategory.{max v uA}`. This file proves the same statements, with their
naturality and postcomposition compatibilities, at an arbitrary model `HasDerivedCategory.{w}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits CategoryTheory.Pretriangulated

universe uA uk v w

namespace DerivedCategory


/-- Maps from an object of the derived category bounded below by `b` to an injective object placed
in a degree `a < b` vanish, at an arbitrary model of the derived category. -/
lemma map_eq_zero_of_isGE_of_injective_single_anyModel
    {C : Type uA} [Category.{v, uA} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X : DerivedCategory C} (a b : ℤ) [X.IsGE b] (hab : a < b)
    {I : C} [Injective I] (f : X ⟶ (DerivedCategory.singleFunctor C a).obj I) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE X b
  let eS := (DerivedCategory.singleFunctorIsoCompQ C a).app I
  have hf : e.inv ≫ f ≫ eS.hom = 0 :=
    DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective (e.inv ≫ f ≫ eS.hom) b hab
  apply (cancel_epi e.inv).mp
  apply (cancel_mono eS.hom).mp
  simpa using hf

/-- For an injective coefficient object, maps into its single complex are exactly maps on
homology, at an arbitrary model `HasDerivedCategory.{w}` of `D(k)`. The source need not be bounded
below. -/
noncomputable def homologyMapToInjectiveEquivAnyModel
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) :
    DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (-i)).obj X ⟶ I) := by
  let C := ModuleCat.{v} k
  let a := -i
  let Y := (DerivedCategory.singleFunctor C 0).obj I
  let H := DerivedCategory.homologyFunctor C 0
  letI : (H.shift a).Additive := inferInstance
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGE a (a + 1) rfl).obj X
  let L := T.obj₁
  let U := T.obj₃
  let inc := T.mor₁
  letI : L.IsLE a := by
    change T.obj₁.IsLE a
    rw [t.triangleLEGE_obj_obj₁ a (a + 1) rfl X]
    exact t.isLE_truncLE_obj X a a
  letI : U.IsGE (a + 1) := by
    change T.obj₃.IsGE (a + 1)
    rw [t.triangleLEGE_obj_obj₃ a (a + 1) rfl X]
    exact t.isGE_truncGE_obj X (a + 1) (a + 1)
  let hY : Y.IsGE 0 := inferInstance
  let eK := (eqToIso (DerivedCategory.shift_homologyFunctor C 0)).app Y ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app I
  let mapH : DerivedCategory.Ext X Y i →+
      ((H.shift a).obj X ⟶ I) := {
    toFun := fun f => (H.shiftMap f a 0 (by dsimp [a]; omega)) ≫ eK.hom
    map_zero' := by simp [Functor.shiftMap, zero_comp]
    map_add' := by
      intro f g
      simp only [Functor.shiftMap]
      rw [Functor.map_add, Preadditive.add_comp, Preadditive.add_comp] }
  have hT : T ∈ Pretriangulated.distinguishedTriangles :=
    t.triangleLEGE_distinguished a (a + 1) rfl X
  have hobj₂ : T.obj₂ = X := t.triangleLEGE_obj_obj₂ a (a + 1) rfl X
  let e₂ : T.obj₂ ≅ X := eqToIso hobj₂
  let incX : L ⟶ X := inc ≫ e₂.hom
  have vanishU : ∀ f : U ⟶ Y⟦i⟧, f = 0 := by
    intro f
    let e := ((DerivedCategory.singleFunctors C).shiftIso i a 0 (by dsimp [a]; omega)).hom.app I
    have hf := map_eq_zero_of_isGE_of_injective_single_anyModel a (a + 1) (by omega) (f ≫ e)
    apply (cancel_mono e).mp
    simpa using hf
  have vanishUminus : ∀ f : U⟦(-1 : ℤ)⟧ ⟶ Y⟦i⟧, f = 0 := by
    intro f
    let e := ((DerivedCategory.singleFunctors C).shiftIso i a 0 (by dsimp [a]; omega)).hom.app I
    let : (U⟦(-1 : ℤ)⟧).IsGE (a + 2) := t.isGE_shift U (a + 1) (-1) (a + 2) (by omega)
    have hf := map_eq_zero_of_isGE_of_injective_single_anyModel a (a + 2) (by omega) (f ≫ e)
    apply (cancel_mono e).mp
    simpa using hf
  have hinc : IsIso ((H.shift a).map inc) := by
    have h₀ : Limits.IsZero ((DerivedCategory.homologyFunctor C a).obj U) :=
      DerivedCategory.isZero_of_isGE U (a + 1) a (by omega)
    have h₁ : Limits.IsZero ((DerivedCategory.homologyFunctor C (a - 1)).obj U) :=
      DerivedCategory.isZero_of_isGE U (a + 1) (a - 1) (by omega)
    have hepi : Epi ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT a).2
        (h₀.eq_of_tgt _ _)
    have hmono : Mono ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2
        (h₁.eq_of_src _ _)
    have hIso : IsIso ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C a).map T.mor₁)
    simpa only [← DerivedCategory.shift_homologyFunctor C a] using hIso
  have hincX : IsIso ((H.shift a).map incX) := by
    have hc : IsIso (((H.shift a).map inc) ≫ ((H.shift a).map e₂.hom)) :=
      IsIso.comp_isIso
    simpa only [incX, Functor.map_comp] using hc
  have hbij : Function.Bijective (fun f : L ⟶ Y⟦i⟧ =>
      (H.shiftMap f a 0 (by dsimp [a]; omega)) ≫ eK.hom) := by
    have hb := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      L Y a 0 i 0 (by dsimp [a]; omega) (by rfl)
    have htarget : Function.Bijective
        (fun g : ((DerivedCategory.homologyFunctor C a).obj L ⟶
          (H.shift 0).obj Y) => g ≫ eK.hom) :=
      ⟨fun _ _ h => by simpa using h, fun g => ⟨g ≫ eK.inv, by simp⟩⟩
    exact htarget.comp hb
  have hmap_bij : Function.Bijective mapH.toFun := by
    constructor
    · intro f g hfg
      change X ⟶ Y⟦i⟧ at f
      change X ⟶ Y⟦i⟧ at g
      let fT : T.obj₂ ⟶ Y⟦i⟧ := e₂.hom ≫ f
      let gT : T.obj₂ ⟶ Y⟦i⟧ := e₂.hom ≫ g
      have hfg0 := (cancel_mono eK.hom).mp hfg
      have hfg0T : H.shiftMap fT a 0 (by dsimp [a]; omega) =
          H.shiftMap gT a 0 (by dsimp [a]; omega) := by
        simp only [fT, gT, Functor.shiftMap_comp', hfg0]
      have hfg' : (H.shiftMap (T.mor₁ ≫ fT) a 0 (by dsimp [a]; omega)) ≫ eK.hom =
          (H.shiftMap (T.mor₁ ≫ gT) a 0 (by dsimp [a]; omega)) ≫ eK.hom := by
        rw [Functor.shiftMap_comp' _ T.mor₁ fT, Functor.shiftMap_comp' _ T.mor₁ gT, hfg0T]
      have hrestrT : T.mor₁ ≫ fT = T.mor₁ ≫ gT := hbij.injective hfg'
      have hfT : T.mor₁ ≫ (fT - gT) = 0 := by
        rw [Preadditive.comp_sub, hrestrT, sub_self]
      obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT (fT - gT) hfT
      have hq0 : q = 0 := vanishU q
      have hfgT : fT = gT := sub_eq_zero.mp (by simpa [hq0] using hq)
      dsimp [fT, gT] at hfgT
      exact (cancel_epi e₂.hom).mp hfgT
    · intro g
      let : IsIso ((H.shift a).map incX) := hincX
      let eH := asIso ((H.shift a).map incX)
      obtain ⟨gL, hgL⟩ := hbij.surjective (eH.hom ≫ g)
      let T' := T.invRotate
      have hT' : T' ∈ Pretriangulated.distinguishedTriangles :=
        inv_rot_of_distTriang _ hT
      have hobj2' : T'.obj₂ = T.obj₁ := by
        dsimp [T', Triangle.invRotate]
      let gL' : T'.obj₂ ⟶ Y⟦i⟧ := eqToHom hobj2' ≫ gL
      have hobs : T'.mor₁ ≫ gL' = 0 := vanishUminus (T'.mor₁ ≫ gL')
      obtain ⟨fT, hf⟩ := T'.yoneda_exact₂ hT' gL' hobs
      have hobj3 : T'.obj₃ = T.obj₂ := by
        dsimp [T', Triangle.invRotate]
      have hmor₂ : (eqToHom hobj2'.symm ≫ T'.mor₂) ≫ eqToHom hobj3 = inc := by
        dsimp [T', Triangle.invRotate, inc]
        simp
      let f : X ⟶ Y⟦i⟧ := e₂.inv ≫ eqToHom hobj3.symm ≫ fT
      refine ⟨f, ?_⟩
      dsimp [mapH]
      have hf' : incX ≫ f = gL := by
        simp only [incX, f, Category.assoc, Iso.hom_inv_id_assoc]
        rw [← hmor₂]
        simp [← hf, gL']
      rw [← hf'] at hgL
      change (H.shiftMap (incX ≫ f) a 0 (by dsimp [a]; omega)) ≫ eK.hom = _ at hgL
      rw [Functor.shiftMap_comp', Category.assoc] at hgL
      exact (cancel_epi eH.hom).mp hgL
  change DerivedCategory.Ext X Y i ≃+ ((H.shift a).obj X ⟶ I)
  exact AddEquiv.ofBijective mapH hmap_bij

/-- Naturality of `homologyMapToInjectiveEquivAnyModel` in the source. -/
theorem homologyMapToInjectiveEquivAnyModel_naturality
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X X' : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (g : X' ⟶ X)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquivAnyModel X' I i (g ≫ α) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (-i)).map g) ≫
        homologyMapToInjectiveEquivAnyModel X I i α := by
  show (DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      (g ≫ α) (-i) 0 (by omega) ≫ _ =
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shift (-i)).map g ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
        α (-i) 0 (by omega) ≫ _)
  rw [Functor.shiftMap_comp']
  simp only [Category.assoc]

/-- Compatibility of `homologyMapToInjectiveEquivAnyModel` with an endomorphism of the
coefficient object. -/
theorem homologyMapToInjectiveEquivAnyModel_postcomp
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (m : I ⟶ I)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquivAnyModel X I i
        (α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)⟦i⟧') =
      homologyMapToInjectiveEquivAnyModel X I i α ≫ m := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0
  let a := -i
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I
  let eK := (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{v} k) 0)).app Y ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} k) 0).app I
  let β := ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)⟦i⟧'
  have hnat : (H.shift 0).map ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m) ≫ eK.hom =
      eK.hom ≫ m := by
    dsimp [H, eK]
    simp only [DerivedCategory.shift_homologyFunctor]
    exact (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} k) 0).hom.naturality m
  show ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      (α ≫ β) a 0 (by omega)) ≫ eK.hom =
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      α a 0 (by omega)) ≫ eK.hom) ≫ m
  rw [Functor.shiftMap_comp']
  show (H.shift a).map α ≫ (H.shift a).map β ≫
      ((H.shiftIso i a 0 (by omega)).hom.app Y) ≫ eK.hom =
    (H.shift a).map α ≫ ((H.shiftIso i a 0 (by omega)).hom.app Y) ≫ eK.hom ≫ m
  have hshift : (H.shift a).map β ≫ (H.shiftIso i a 0 (by omega)).hom.app Y =
      (H.shiftIso i a 0 (by omega)).hom.app Y ≫
        (H.shift 0).map ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m) := by
    dsimp [β]
    exact Functor.shiftIso_hom_naturality (F := H) (n := i) (a := a) (a' := 0)
      (ha' := by omega) ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)
  rw [reassoc_of% hshift, hnat]


end DerivedCategory
