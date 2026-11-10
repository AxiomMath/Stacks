module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoFieldExtra

/-!
# Ext into an injective module over a field

For a field `k`, an object `X` of the derived category of `k`-modules and an injective `k`-module
`I`, the group `Ext^i(X, I)` is identified with the group of linear maps from the homology of `X`
in degree `-i` to `I`, naturally in `X` and compatibly with endomorphisms of `I`.

## Main definitions

* `DerivedCategory.homologyMapToInjectiveEquivAtModel`: the additive equivalence between
  `Ext^i(X, I)` and maps from the homology of `X` in degree `-i` to `I`.

## Main results

* `DerivedCategory.homologyMapToInjectiveEquivAtModel_naturality`: the equivalence is natural in
  `X`.
* `DerivedCategory.homologyMapToInjectiveEquivAtModel_postcomp`: the equivalence commutes with
  postcomposition by an endomorphism of `I`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars

universe uA uk v uB w

namespace DerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- For an injective coefficient object, maps into its single complex are exactly maps on
homology. The source need not be bounded below. -/
noncomputable def homologyMapToInjectiveEquivAtModel
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) :
    DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (-i)).obj X ⟶ I) := by
  let C := ModuleCat.{v} k
  let a := -i
  let Y := (DerivedCategory.singleFunctor C 0).obj I
  let H := DerivedCategory.homologyFunctor C 0
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
  let eK := (eqToIso (DerivedCategory.shift_homologyFunctor C 0)).app Y ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app I
  let mapH : DerivedCategory.Ext X Y i →+ ((H.shift a).obj X ⟶ I) := {
    toFun := fun f => (H.shiftMap f a 0 (by omega)) ≫ eK.hom
    map_zero' := by simp [Functor.shiftMap, zero_comp]
    map_add' := by
      intro f g
      simp only [Functor.shiftMap]
      rw [Functor.map_add, Preadditive.add_comp, Preadditive.add_comp] }
  have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished a (a + 1) rfl X
  let e₂ : T.obj₂ ≅ X := eqToIso (t.triangleLEGE_obj_obj₂ a (a + 1) rfl X)
  let incX : L ⟶ X := inc ≫ e₂.hom
  have vanish : ∀ (V : DerivedCategory C) (n : ℤ) [V.IsGE n], a < n → ∀ f : V ⟶ Y⟦i⟧, f = 0 := by
    intro V n _ hn f
    let e := ((DerivedCategory.singleFunctors C).shiftIso i a 0 (by omega)).hom.app I
    apply (cancel_mono e).mp
    simpa using DerivedCategory.map_eq_zero_of_isGE_of_injective_single_anyModel a n hn (f ≫ e)
  have : (T.obj₃⟦(-1 : ℤ)⟧).IsGE (a + 2) := t.isGE_shift U (a + 1) (-1) (a + 2) (by omega)
  have hres : Function.Bijective (fun f : T.obj₂ ⟶ Y⟦i⟧ => T.mor₁ ≫ f) := by
    refine ⟨fun f g hfg => ?_, fun g => ?_⟩
    · obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT (f - g) (by simpa [sub_eq_zero] using hfg)
      simpa [vanish U (a + 1) (by omega) q, sub_eq_zero] using hq
    · obtain ⟨f, hf⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang _ hT) g
        (vanish (T.obj₃⟦(-1 : ℤ)⟧) (a + 2) (by omega) _)
      exact ⟨f, hf.symm⟩
  have hinc : IsIso ((H.shift a).map inc) := by
    have : Epi ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT a).2
        ((DerivedCategory.isZero_of_isGE U (a + 1) a (by omega)).eq_of_tgt _ _)
    have : Mono ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2
        ((DerivedCategory.isZero_of_isGE U (a + 1) (a - 1) (by omega)).eq_of_src _ _)
    have hIso : IsIso ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      isIso_of_mono_of_epi _
    simpa only [← DerivedCategory.shift_homologyFunctor C a] using hIso
  have hincX : IsIso ((H.shift a).map incX) := by
    simp only [incX, Functor.map_comp]
    infer_instance
  have hbij : Function.Bijective (fun f : L ⟶ Y⟦i⟧ =>
      (H.shiftMap f a 0 (by omega)) ≫ eK.hom) := by
    have hb := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      L Y a 0 i 0 (by omega) (by rfl)
    have htarget : Function.Bijective
        (fun g : ((DerivedCategory.homologyFunctor C a).obj L ⟶ (H.shift 0).obj Y) =>
          g ≫ eK.hom) :=
      ⟨fun _ _ h => by simpa using h, fun g => ⟨g ≫ eK.inv, by simp⟩⟩
    exact htarget.comp hb
  have he₂ : Function.Bijective (fun f : X ⟶ Y⟦i⟧ => e₂.hom ≫ f) :=
    ⟨fun _ _ h => by simpa using h, fun g => ⟨e₂.inv ≫ g, by simp⟩⟩
  have hpre : Function.Bijective (fun g : (H.shift a).obj X ⟶ I => (H.shift a).map incX ≫ g) :=
    ⟨fun _ _ h => (cancel_epi ((H.shift a).map incX)).mp h,
      fun g => ⟨inv ((H.shift a).map incX) ≫ g, by simp⟩⟩
  have hcomp : (fun g => (H.shift a).map incX ≫ g) ∘ mapH =
      (fun f : L ⟶ Y⟦i⟧ => H.shiftMap f a 0 (by omega) ≫ eK.hom) ∘
        (fun f : T.obj₂ ⟶ Y⟦i⟧ => T.mor₁ ≫ f) ∘ (fun f : X ⟶ Y⟦i⟧ => e₂.hom ≫ f) := by
    funext f
    simp [mapH, incX, inc, Functor.shiftMap_comp']
  have hmap_bij : Function.Bijective mapH :=
    (hpre.of_comp_iff' mapH).mp (hcomp ▸ hbij.comp (hres.comp he₂))
  exact AddEquiv.ofBijective mapH hmap_bij

/-- The equivalence `homologyMapToInjectiveEquivAtModel` is natural in the source: precomposing an
Ext class with `g : X' ⟶ X` corresponds to precomposing with the map induced by `g` on homology in
degree `-i`. -/
theorem homologyMapToInjectiveEquivAtModel_naturality
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X X' : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (g : X' ⟶ X)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquivAtModel X' I i (g ≫ α) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (-i)).map g) ≫
        homologyMapToInjectiveEquivAtModel X I i α := by
  change (DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      (g ≫ α) (-i) 0 (by omega) ≫ _ =
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shift (-i)).map g ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
        α (-i) 0 (by omega) ≫ _)
  rw [Functor.shiftMap_comp']
  simp only [Category.assoc]

/-- The equivalence `homologyMapToInjectiveEquivAtModel` commutes with postcomposition by an
endomorphism `m : I ⟶ I`, acting on Ext classes through the single complex functor. -/
theorem homologyMapToInjectiveEquivAtModel_postcomp
    {k : Type uk} [Field k] [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    (X : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (m : I ⟶ I)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquivAtModel X I i
        (α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)⟦i⟧') =
      homologyMapToInjectiveEquivAtModel X I i α ≫ m := by
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
  change ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      (α ≫ β) a 0 (by omega)) ≫ eK.hom =
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      α a 0 (by omega)) ≫ eK.hom) ≫ m
  rw [Functor.shiftMap_comp']
  change (H.shift a).map α ≫ (H.shift a).map β ≫
      ((H.shiftIso i a 0 (by omega)).hom.app Y) ≫ eK.hom =
    (H.shift a).map α ≫ ((H.shiftIso i a 0 (by omega)).hom.app Y) ≫ eK.hom ≫ m
  have hshift : (H.shift a).map β ≫ (H.shiftIso i a 0 (by omega)).hom.app Y =
      (H.shiftIso i a 0 (by omega)).hom.app Y ≫
        (H.shift 0).map ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m) :=
    Functor.shiftIso_hom_naturality (F := H) (n := i) (a := a) (a' := 0)
      (ha' := by omega) ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)
  rw [reassoc_of% hshift, hnat]

end DerivedCategory
