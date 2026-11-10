module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Ext into a field

Let `A → k` be a homomorphism of commutative rings with `k` a field.  For a bounded-above
object `E` of the derived category of `A`-modules, its Ext groups into `k` are the linear duals
of the cohomology groups of its derived base change to `k`.

## Main definitions

* `extIntoFieldSMul` is the intrinsic action of `k` on `Ext_A(E,k)`, obtained by
  postcomposing with scalar multiplication on `k`.

## Main results

* `extIntoFieldEquivDualBaseChangeHomology` identifies `Extⁱ_A(E, k)` with the `k`-linear
  dual of `H⁻ⁱ(E ⊗ᴸ_A k)`.
* `extIntoFieldEquivDualBaseChangeHomology_smul` records that this identification is
  `k`-linear, and `extIntoFieldEquivDualBaseChangeHomology_naturality` records its
  naturality in `E`.
* `extIntoFieldEquivDualBaseChangeHomology_restrictScalars` identifies cross-ring Ext
  pullback with the dual of `derivedBaseChangeMap` for a tower of ring maps.

## Implementation notes

Derived base change is the total left derived extension-of-scalars functor. Projective
presentations are needed only in the proof and are not part of the statement. The ring,
field, and module universes are independent. Modules live in a common universe above the
rings, with `ULift k` representing the field coefficient there. The cross-ring comparison
uses the canonical derived extension/restriction adjunction and imposes no flatness assumption.
The equivalence states the displayed equality as an additive-group isomorphism;
`extIntoFieldEquivDualBaseChangeHomology_smul` supplies its field-linearity.
The two naturality lemmas separately cover morphisms over one ring and compatible
morphisms over a tower of rings.

## References

* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars

universe uA uk v uB

namespace DerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- Restricting along a tower of ring maps agrees with restricting along its composite,
also on derived categories. -/
public noncomputable def derivedRestrictScalarsComp
    {A : Type uA} {B : Type uB} {k : Type uk}
    [CommRing A] [CommRing B] [Field k] (f : A →+* B) (g : B →+* k) :
    (ModuleCat.restrictScalars.{max v uA uB uk} g).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max v uA uB uk} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max v uA uB uk} (g.comp f)).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{max v uA uB uk} g
  let G := ModuleCat.restrictScalars.{max v uA uB uk} f
  let H := ModuleCat.restrictScalars.{max v uA uB uk} (g.comp f)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uA uB uk} k) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)) _ ≪≫
      H.mapDerivedCategoryFactors.symm)

/-- The canonical map `E ⊗ᴸ_A k ⟶ F ⊗ᴸ_B k` induced by a morphism
`E ⟶ Res_A^B F`. It is the adjoint of that morphism followed by the base-change unit. -/
public noncomputable def derivedBaseChangeMap
    {A : Type uA} {B : Type uB} {k : Type uk}
    [CommRing A] [CommRing B] [Field k] (f : A →+* B) (g : B →+* k)
    (E : DerivedCategory (ModuleCat.{max v uA uB uk} A))
    (F : DerivedCategory (ModuleCat.{max v uA uB uk} B))
    (h : E ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F) :
    (totalDerivedExtensionScalars.{uA, uk, max v uB} (g.comp f)).functor.obj E ⟶
      (totalDerivedExtensionScalars.{uB, uk, max v uA} g).functor.obj F := by
  let Dg := totalDerivedExtensionScalars.{uB, uk, max v uA} g
  let Dgf := totalDerivedExtensionScalars.{uA, uk, max v uB} (g.comp f)
  let ag := @derivedExtensionScalarsAdjunction.{uB, uk, max v uA}
    B k _ _ g _ _ Dg.functor Dg.comparison Dg.isLeftDerived
  let agf := @derivedExtensionScalarsAdjunction.{uA, uk, max v uB}
    A k _ _ (g.comp f) _ _ Dgf.functor Dgf.comparison Dgf.isLeftDerived
  exact (agf.homEquiv E (Dg.functor.obj F)).symm
    (h ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map (ag.unit.app F) ≫
      (derivedRestrictScalarsComp.{uA, uk, v, uB} f g).hom.app (Dg.functor.obj F))

/-- Pullback of Ext classes along a morphism over a change of rings. The field coefficient
is identified by the canonical single-object, shift, and restriction-of-scalars isomorphisms. -/
public noncomputable def extIntoFieldRestriction
    {A : Type uA} {B : Type uB} {k : Type uk}
    [CommRing A] [CommRing B] [Field k] (f : A →+* B) (g : B →+* k)
    (E : DerivedCategory (ModuleCat.{max v uA uB uk} A))
    (F : DerivedCategory (ModuleCat.{max v uA uB uk} B))
    (h : E ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F) (i : ℤ)
    (α : DerivedCategory.Ext F
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} B) 0).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{max v uA uB} k)))) i) :
    DerivedCategory.Ext E
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} A) 0).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj
          (ModuleCat.of k (ULift.{max v uA uB} k)))) i := by
  let K := ModuleCat.of k (ULift.{max v uA uB} k)
  let S := ModuleCat.restrictScalars.{max v uA uB uk} f
  let T := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} B) 0).obj
    ((ModuleCat.restrictScalars g).obj K)
  let e := (S.mapDerivedCategorySingleFunctor 0).app ((ModuleCat.restrictScalars g).obj K) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} A) 0).mapIso
      ((ModuleCat.restrictScalarsComp f g).app K).symm
  exact h ≫ S.mapDerivedCategory.map α ≫
    ((S.mapDerivedCategory.commShiftIso i).app T).hom ≫ e.hom⟦i⟧'

/-- The scalar action on `Ext_A(E,k)` induced by the action of `k` on its second argument. -/
public noncomputable instance extIntoFieldSMul
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E : DerivedCategory (ModuleCat.{max v uA uk} A)) (i : ℤ) :
    SMul k (DerivedCategory.Ext E
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i) where
  smul x α :=
    let lm := LinearMap.lsmul k (ULift.{max v uA} k) x
    let m := (ModuleCat.restrictScalars f).map (ModuleCat.ofHom lm)
    α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map m)⟦i⟧'

/-- Cancelling an inverse-then-forward pair of components of a natural isomorphism after
applying a functor. Stated over abstract categories: at the concrete derived-category sites
below the two spellings of the identity carry different instance paths, so neither `rw` nor
`simp` matches `Category.comp_id` there. -/
private theorem map_inv_hom_app_comp {C B A : Type*} [Category C] [Category B] [Category A]
    {F G : C ⥤ B} (η : F ≅ G) (S : B ⥤ A) (X : C) {Z : A} (w : S.obj (G.obj X) ⟶ Z) :
    S.map (η.inv.app X) ≫ S.map (η.hom.app X) ≫ w = w := by
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- If `X` is concentrated in degrees `≥ b` and `a < b`, then every morphism from `X` to the
single complex on an injective object `I` in degree `a` is zero. -/
lemma map_eq_zero_of_isGE_of_injective_single
    {C : Type uA} [Category.{v, uA} C] [Abelian C] [HasDerivedCategory.{max v uA} C]
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
homology. The source need not be bounded below. -/
noncomputable def homologyMapToInjectiveEquiv
    {k : Type uk} [Field k] (X : DerivedCategory (ModuleCat.{v} k))
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
  have hobj₂ : T.obj₂ = X := by
    change ((t.triangleLEGE a (a + 1) rfl).obj X).obj₂ = X
    exact t.triangleLEGE_obj_obj₂ a (a + 1) rfl X
  let e₂ : T.obj₂ ≅ X := eqToIso hobj₂
  let incX : L ⟶ X := inc ≫ e₂.hom
  have vanishU : ∀ f : U ⟶ Y⟦i⟧, f = 0 := by
    intro f
    let e := ((DerivedCategory.singleFunctors C).shiftIso i a 0 (by dsimp [a]; omega)).hom.app I
    have hf := map_eq_zero_of_isGE_of_injective_single a (a + 1) (by omega) (f ≫ e)
    apply (cancel_mono e).mp
    simpa using hf
  have vanishUminus : ∀ f : U⟦(-1 : ℤ)⟧ ⟶ Y⟦i⟧, f = 0 := by
    intro f
    let e := ((DerivedCategory.singleFunctors C).shiftIso i a 0 (by dsimp [a]; omega)).hom.app I
    let : (U⟦(-1 : ℤ)⟧).IsGE (a + 2) := t.isGE_shift U (a + 1) (-1) (a + 2) (by omega)
    have hf := map_eq_zero_of_isGE_of_injective_single a (a + 2) (by omega) (f ≫ e)
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
    let : Mono ((DerivedCategory.homologyFunctor C a).map T.mor₁) := hmono
    let : Epi ((DerivedCategory.homologyFunctor C a).map T.mor₁) := hepi
    have hIso : IsIso ((DerivedCategory.homologyFunctor C a).map T.mor₁) :=
      isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C a).map T.mor₁)
    simpa only [← DerivedCategory.shift_homologyFunctor C a] using hIso
  have hincX : IsIso ((H.shift a).map incX) := by
    let : IsIso ((H.shift a).map inc) := hinc
    let : IsIso ((H.shift a).map e₂.hom) := inferInstance
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
        dsimp [fT, gT]
        rw [Functor.shiftMap_comp', Functor.shiftMap_comp']
        exact congrArg (fun q => ((H.shift a).map e₂.hom) ≫ q) hfg0
      have hfg' : (H.shiftMap (T.mor₁ ≫ fT) a 0 (by dsimp [a]; omega)) ≫ eK.hom =
          (H.shiftMap (T.mor₁ ≫ gT) a 0 (by dsimp [a]; omega)) ≫ eK.hom := by
        calc
          (H.shiftMap (T.mor₁ ≫ fT) a 0 (by dsimp [a]; omega)) ≫ eK.hom =
              (((H.shift a).map T.mor₁ ≫ H.shiftMap fT a 0 (by dsimp [a]; omega)) ≫
                eK.hom) := by rw [Functor.shiftMap_comp']
          _ = (((H.shift a).map T.mor₁ ≫ H.shiftMap gT a 0 (by dsimp [a]; omega)) ≫
                eK.hom) := congrArg (fun q => (((H.shift a).map T.mor₁ ≫ q) ≫ eK.hom)) hfg0T
          _ = (H.shiftMap (T.mor₁ ≫ gT) a 0 (by dsimp [a]; omega)) ≫ eK.hom := by
            rw [← Functor.shiftMap_comp']
      have hrestrT : T.mor₁ ≫ fT = T.mor₁ ≫ gT := hbij.injective hfg'
      have hfT : T.mor₁ ≫ (fT - gT) = 0 := by
        rw [Preadditive.comp_sub, hrestrT, sub_self]
      obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT (fT - gT) hfT
      have hq0 : q = 0 := vanishU q
      have : fT - gT = 0 := by simpa [hq0] using hq
      have hfgT : fT = gT := sub_eq_zero.mp this
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
      have h2id : eqToHom hobj2'.symm ≫ eqToHom hobj2' = 𝟙 _ := by
        simp
      have h3f : eqToHom hobj3 ≫ (eqToHom hobj3.symm ≫ fT) = fT := by
        simp
      let f : X ⟶ Y⟦i⟧ := e₂.inv ≫ eqToHom hobj3.symm ≫ fT
      refine ⟨f, ?_⟩
      dsimp [mapH]
      have hf' : incX ≫ f = gL := by
        change (inc ≫ e₂.hom) ≫ (e₂.inv ≫ (eqToHom hobj3.symm ≫ fT)) = gL
        calc
          (inc ≫ e₂.hom) ≫ (e₂.inv ≫ (eqToHom hobj3.symm ≫ fT)) =
              inc ≫ (eqToHom hobj3.symm ≫ fT) := by simp [Category.assoc]
          _ = (eqToHom hobj2'.symm ≫ T'.mor₂) ≫
                (eqToHom hobj3 ≫ (eqToHom hobj3.symm ≫ fT)) := by
                  simpa [Category.assoc] using
                    (congrArg (fun q => q ≫ (eqToHom hobj3.symm ≫ fT)) hmor₂).symm
          _ = eqToHom hobj2'.symm ≫ (T'.mor₂ ≫ fT) := by
                simp only [Category.assoc, h3f]
          _ = eqToHom hobj2'.symm ≫ gL' := by rw [hf]
          _ = gL := by
                dsimp [gL']
                rw [← Category.assoc, h2id, Category.id_comp]
      have hcomp := hgL
      rw [← hf'] at hcomp
      change (H.shiftMap (incX ≫ f) a 0 (by dsimp [a]; omega)) ≫ eK.hom = _ at hcomp
      rw [Functor.shiftMap_comp'] at hcomp
      change ((H.shift a).map incX ≫ H.shiftMap f a 0 (by dsimp [a]; omega)) ≫ eK.hom =
        eH.hom ≫ g at hcomp
      have hcomp' : eH.hom ≫ (H.shiftMap f a 0 (by dsimp [a]; omega) ≫ eK.hom) =
          eH.hom ≫ g := by
        change (eH.hom ≫ H.shiftMap f a 0 (by dsimp [a]; omega)) ≫ eK.hom =
          eH.hom ≫ g at hcomp
        rw [← Category.assoc]
        exact hcomp
      exact (cancel_epi eH.hom).mp hcomp'
  let e := AddEquiv.ofBijective mapH hmap_bij
  change DerivedCategory.Ext X Y i ≃+ ((H.shift a).obj X ⟶ I)
  exact e

/-- Derived extension–restriction adjunction for `A → k`: `Extⁱ_A(E, k)` is isomorphic to
`Extⁱ_k(E ⊗ᴸ_A k, k)`. -/
noncomputable def derivedExtRestrictionEquiv
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E : DerivedCategory (ModuleCat.{max v uA uk} A)) (i : ℤ) :
    DerivedCategory.Ext E
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
          ((ModuleCat.restrictScalars f).obj
            (ModuleCat.of k (ULift.{max v uA} k)))) i ≃+
      DerivedCategory.Ext
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (f := f)).functor.obj E)
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).obj
          (ModuleCat.of k (ULift.{max v uA} k))) i := by
  let K := ModuleCat.of k (ULift.{max v uA} k)
  let S := ModuleCat.restrictScalars.{max v uA uk} f
  let R := S.mapDerivedCategory
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uk, v} f
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).obj K
  let e₀ := (S.mapDerivedCategorySingleFunctor 0).app K
  let e : R.obj (Y⟦i⟧) ≅
      ((S ⋙ DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj K)⟦i⟧ :=
    (R.commShiftIso i).app Y ≪≫ (shiftFunctor _ i).mapIso e₀
  let adj := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uA, uk, v}
    A k _ _ f _ _
    D.functor D.comparison D.isLeftDerived
  let adjE := adj.homAddEquiv E (Y⟦i⟧)
  let postEquiv : AddEquiv (E ⟶ R.obj (Y⟦i⟧)) (E ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj (S.obj K))⟦i⟧) := {
    toFun q := q ≫ e.hom
    invFun q := q ≫ e.inv
    left_inv q := by simp [Category.assoc]
    right_inv q := by simp [Category.assoc]
    map_add' q q' := by simp [Preadditive.add_comp] }
  exact postEquiv.symm.trans adjE.symm

/-- `derivedExtRestrictionEquiv` is natural in `E`: precomposing with `g : E' ⟶ E` corresponds
to precomposing with the derived base change of `g`. -/
theorem derivedExtRestrictionEquiv_naturality
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E E' : DerivedCategory (ModuleCat.{max v uA uk} A)) (i : ℤ)
    (g : E' ⟶ E) (α : DerivedCategory.Ext E
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i) :
    derivedExtRestrictionEquiv f E' i (g ≫ α) =
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uk, v}
        f).functor.map g) ≫ derivedExtRestrictionEquiv f E i α := by
  simp [derivedExtRestrictionEquiv, Category.assoc,
    Adjunction.homEquiv_naturality_left_symm]

/-- `derivedExtRestrictionEquiv` commutes with postcomposition by an endomorphism `m` of the
coefficient `k`. -/
theorem derivedExtRestrictionEquiv_postcomp
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E : DerivedCategory (ModuleCat.{max v uA uk} A)) (i : ℤ)
    (α : DerivedCategory.Ext E
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i)
    (m : ModuleCat.of k (ULift.{max v uA} k) ⟶
      ModuleCat.of k (ULift.{max v uA} k)) :
    derivedExtRestrictionEquiv f E i
        (α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map
          ((ModuleCat.restrictScalars f).map m))⟦i⟧') =
    derivedExtRestrictionEquiv f E i α ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m)⟦i⟧' := by
  let K := ModuleCat.of k (ULift.{max v uA} k)
  let S := ModuleCat.restrictScalars.{max v uA uk} f
  let R := S.mapDerivedCategory
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uk, v} f
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).obj K
  let e₀ := (S.mapDerivedCategorySingleFunctor 0).app K
  let e : R.obj (Y⟦i⟧) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj (S.obj K))⟦i⟧ :=
    (R.commShiftIso i).app Y ≪≫ (shiftFunctor _ i).mapIso e₀
  let adj := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uA, uk, v}
    A k _ _ f _ _ D.functor D.comparison D.isLeftDerived
  change (adj.homEquiv E (Y⟦i⟧)).symm
      ((α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map
        (S.map m))⟦i⟧') ≫ e.inv) =
    (adj.homEquiv E (Y⟦i⟧)).symm (α ≫ e.inv) ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m)⟦i⟧'
  have hsquare :
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map
        (S.map m))⟦i⟧' ≫ e.inv = e.inv ≫
          R.map (((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m)⟦i⟧') := by
    apply (cancel_mono e.hom).mp
    dsimp [e]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    let mK := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m
    have hc : (R.commShiftIso i).inv.app Y ≫ R.map (((DerivedCategory.singleFunctor
        (ModuleCat.{max v uA uk} k) 0).map m)⟦i⟧') ≫ (R.commShiftIso i).hom.app Y =
        (R.map ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m))⟦i⟧' := by
      rw [Functor.commShiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]
    have h₀ : (DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map
          (S.map m) = e₀.inv ≫ R.map mK ≫ e₀.hom :=
      (Iso.eq_inv_comp e₀).2 ((S.mapDerivedCategorySingleFunctor 0).hom.naturality m).symm
    calc
      _ = (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map (S.map m)) := by
          rw [Iso.inv_hom_id_map]; exact Category.comp_id _
      _ = (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map
            (e₀.inv ≫ R.map mK ≫ e₀.hom) :=
          congrArg ((shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map) h₀
      _ = (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map e₀.inv ≫
            (Functor.commShiftIso R i).inv.app Y ≫
            R.map (((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} k) 0).map m)⟦i⟧') ≫
            (Functor.commShiftIso R i).hom.app Y ≫
            (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map e₀.hom := by
          have hcc := congrArg (fun q =>
            (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map e₀.inv ≫
              q ≫ (shiftFunctor (DerivedCategory (ModuleCat.{max v uA uk} A)) i).map e₀.hom) hc
          simpa [Functor.map_comp, Category.assoc] using hcc.symm
  rw [← adj.homEquiv_naturality_right_symm]
  congr 1
  simp only [Category.assoc]
  rw [hsquare]

/-- `homologyMapToInjectiveEquiv` is natural in `X`: precomposing with `g : X' ⟶ X` corresponds
to precomposing with the map induced by `g` on `H⁻ⁱ`. -/
theorem homologyMapToInjectiveEquiv_naturality
    {k : Type uk} [Field k] (X X' : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (g : X' ⟶ X)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquiv X' I i (g ≫ α) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (-i)).map g) ≫
        homologyMapToInjectiveEquiv X I i α := by
  change (DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
      (g ≫ α) (-i) 0 (by omega) ≫ _ =
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shift (-i)).map g ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0).shiftMap
        α (-i) 0 (by omega) ≫ _)
  rw [Functor.shiftMap_comp']
  simp only [Category.assoc]

/-- `homologyMapToInjectiveEquiv` commutes with postcomposition by an endomorphism `m` of `I`. -/
theorem homologyMapToInjectiveEquiv_postcomp
    {k : Type uk} [Field k] (X : DerivedCategory (ModuleCat.{v} k))
    (I : ModuleCat.{v} k) [Injective I] (i : ℤ) (m : I ⟶ I)
    (α : DerivedCategory.Ext X ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).obj I) i) :
    homologyMapToInjectiveEquiv X I i
        (α ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)⟦i⟧') =
      homologyMapToInjectiveEquiv X I i α ≫ m := by
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
        (H.shift 0).map ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m) := by
    dsimp [β]
    exact Functor.shiftIso_hom_naturality (F := H) (n := i) (a := a) (a' := 0)
      (ha' := by omega) ((DerivedCategory.singleFunctor (ModuleCat.{v} k) 0).map m)
  rw [reassoc_of% hshift, hnat]

private theorem adjunction_comp_right_mate
    {C : Type uA} {D : Type uB} {T : Type uk}
    [Category.{v} C] [Category.{v} D] [Category.{v} T]
    {L : D ⥤ T} {R : T ⥤ D} {L' : C ⥤ T} {R' : T ⥤ C}
    {S : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ⋙ S ≅ R')
    {X : C} {Y : D} {Z : T} (h : X ⟶ S.obj Y) (q : Y ⟶ R.obj Z) :
    (a'.homEquiv X Z).symm (h ≫ S.map q ≫ e.hom.app Z) =
      (a'.homEquiv X (L.obj Y)).symm
        (h ≫ S.map (a.unit.app Y) ≫ e.hom.app (L.obj Y)) ≫
          (a.homEquiv Y Z).symm q := by
  rw [← a'.homEquiv_naturality_right_symm]
  apply congrArg (a'.homEquiv X Z).symm
  calc
    h ≫ S.map q ≫ e.hom.app Z =
        h ≫ S.map (a.unit.app Y ≫ R.map ((a.homEquiv Y Z).symm q)) ≫
          e.hom.app Z := by rw [← Adjunction.homEquiv_apply, Equiv.apply_symm_apply]
    _ = h ≫ S.map (a.unit.app Y) ≫ e.hom.app (L.obj Y) ≫
          R'.map ((a.homEquiv Y Z).symm q) := by
      rw [S.map_comp]
      simpa only [Functor.comp_map, Category.assoc] using congrArg
        (fun t => h ≫ S.map (a.unit.app Y) ≫ t) (e.hom.naturality ((a.homEquiv Y Z).symm q))
  all_goals simp only [Category.assoc]

/-- Ext into a field is the linear dual of the cohomology of canonical derived base change. -/
@[stacks 07YK "equivalence"]
public noncomputable def extIntoFieldEquivDualBaseChangeHomology
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E : DerivedCategory.Minus (ModuleCat.{max v uA uk} A)) (i : ℤ) :
    DerivedCategory.Ext E.1
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v uA uk} k) (-i)).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uk, v}
          f).functor.obj E.1) ⟶ ModuleCat.of k (ULift.{max v uA} k)) :=
  by
   letI : Module.Injective k (ULift.{max v uA} k) :=
     Module.injective_of_isSemisimpleRing k _
   letI : CategoryTheory.Injective (ModuleCat.of k (ULift.{max v uA} k)) :=
     Module.injective_object_of_injective_module k _
   exact (derivedExtRestrictionEquiv f E.1 i).trans
    (homologyMapToInjectiveEquiv
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
        (f := f)).functor.obj E.1)
      (ModuleCat.of k (ULift.{max v uA} k)) i)

/-- The Ext/base-change duality equivalence respects the intrinsic scalar action of `k`. -/
@[stacks 07YK "k-linearity"]
public theorem extIntoFieldEquivDualBaseChangeHomology_smul
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E : DerivedCategory.Minus (ModuleCat.{max v uA uk} A)) (i : ℤ)
    (x : k) (α : DerivedCategory.Ext E.1
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i) :
  extIntoFieldEquivDualBaseChangeHomology f E i (x • α) =
      x • extIntoFieldEquivDualBaseChangeHomology f E i α :=
  by
    let K := ModuleCat.of k (ULift.{max v uA} k)
    let lm : ULift.{max v uA} k →ₗ[k] ULift.{max v uA} k :=
      LinearMap.lsmul k (ULift.{max v uA} k) x
    let m : K ⟶ K := ModuleCat.ofHom lm
    let : Module.Injective k (ULift.{max v uA} k) :=
      Module.injective_of_isSemisimpleRing k _
    let : CategoryTheory.Injective (ModuleCat.of k (ULift.{max v uA} k)) :=
      Module.injective_object_of_injective_module k _
    simp only [extIntoFieldEquivDualBaseChangeHomology, AddEquiv.trans_apply]
    rw [show x • α = α ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).map
          ((ModuleCat.restrictScalars f).map m))⟦i⟧' by rfl]
    rw [derivedExtRestrictionEquiv_postcomp, homologyMapToInjectiveEquiv_postcomp]
    change _ = x • _
    ext z; rfl

/-- The Ext/base-change duality equivalence is contravariantly natural in derived objects. -/
@[stacks 07YK "naturality in the derived object"]
public theorem extIntoFieldEquivDualBaseChangeHomology_naturality
    {A : Type uA} {k : Type uk} [CommRing A] [Field k] (f : A →+* k)
    (E E' : DerivedCategory.Minus (ModuleCat.{max v uA uk} A)) (i : ℤ)
    (g : E'.1 ⟶ E.1)
    (α : DerivedCategory.Ext E.1
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uk} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{max v uA} k)))) i) :
    extIntoFieldEquivDualBaseChangeHomology f E' i (g ≫ α) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max v uA uk} k) (-i)).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uk, v}
          f).functor.map g) ≫
        extIntoFieldEquivDualBaseChangeHomology f E i α :=
  by
    simp only [extIntoFieldEquivDualBaseChangeHomology, AddEquiv.trans_apply]
    rw [derivedExtRestrictionEquiv_naturality, homologyMapToInjectiveEquiv_naturality]

/-- The duality intertwines pullback of Ext classes across `A → B` with the dual of the
canonical map `E ⊗ᴸ_A k ⟶ F ⊗ᴸ_B k`. -/
@[stacks 07YK "naturality under change of source ring"]
public theorem extIntoFieldEquivDualBaseChangeHomology_restrictScalars
    {A : Type uA} {B : Type uB} {k : Type uk}
    [CommRing A] [CommRing B] [Field k] (f : A →+* B) (g : B →+* k)
    (E : DerivedCategory.Minus (ModuleCat.{max v uA uB uk} A))
    (F : DerivedCategory.Minus (ModuleCat.{max v uA uB uk} B))
    (h : E.1 ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F.1) (i : ℤ)
    (α : DerivedCategory.Ext F.1
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} B) 0).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{max v uA uB} k)))) i) :
    extIntoFieldEquivDualBaseChangeHomology.{uA, uk, max v uB} (g.comp f) E i
        (extIntoFieldRestriction.{uA, uk, v, uB} f g E.1 F.1 h i α) =
        (DerivedCategory.homologyFunctor (ModuleCat.{max v uA uB uk} k) (-i)).map
        (derivedBaseChangeMap.{uA, uk, v, uB} f g E.1 F.1 h) ≫
        extIntoFieldEquivDualBaseChangeHomology.{uB, uk, max v uA} g F i α :=
  by
    let : Module.Injective k (ULift.{max v uA uB} k) :=
      Module.injective_of_isSemisimpleRing k _
    let : CategoryTheory.Injective (ModuleCat.of k (ULift.{max v uA uB} k)) :=
      Module.injective_object_of_injective_module k _
    let b := derivedBaseChangeMap.{uA, uk, v, uB} f g E.1 F.1 h
    have hbridge :
        derivedExtRestrictionEquiv.{uA, uk, max v uB} (g.comp f) E.1 i
            (extIntoFieldRestriction f g E.1 F.1 h i α) =
          b ≫ derivedExtRestrictionEquiv.{uB, uk, max v uA} g F.1 i α := by
      let K := ModuleCat.of k (ULift.{max v uA uB} k)
      let Y₀ := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} k) 0).obj K
      let Y := Y₀⟦i⟧
      let S := ModuleCat.restrictScalars.{max v uA uB uk} f
      let G := ModuleCat.restrictScalars.{max v uA uB uk} g
      let H := ModuleCat.restrictScalars.{max v uA uB uk} (g.comp f)
      let e := derivedRestrictScalarsComp.{uA, uk, v, uB} f g
      let τ := ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight G.mapDerivedCategoryFactors _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ S.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
          (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)) _ ≪≫
        H.mapDerivedCategoryFactors.symm).hom
      have : NatTrans.CommShift
          (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)).hom ℤ := by
        constructor
        intro n
        ext X j
        simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
          CochainComplex.shiftFunctor_map_f', Functor.commShiftIso_comp_hom_app,
          Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
      have hτ : NatTrans.CommShift τ ℤ := by
        dsimp only [τ]
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
          Functor.isoWhiskerLeft_hom]
        infer_instance
      let eg := (G.mapDerivedCategory.commShiftIso i).app Y₀ ≪≫
        (shiftFunctor _ i).mapIso ((G.mapDerivedCategorySingleFunctor 0).app K)
      let eh := (H.mapDerivedCategory.commShiftIso i).app Y₀ ≪≫
        (shiftFunctor _ i).mapIso ((H.mapDerivedCategorySingleFunctor 0).app K)
      let q : F.1 ⟶ G.mapDerivedCategory.obj Y := α ≫ eg.inv
      let C := (CochainComplex.singleFunctor
        (ModuleCat.{max v uA uB uk} k) 0).obj K
      have hc :
          (S.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((G.mapCochainComplexSingleFunctor 0).hom.app K) ≫
            (S.mapCochainComplexSingleFunctor 0).hom.app (G.obj K) ≫
              (CochainComplex.singleFunctor (ModuleCat.{max v uA uB uk} A) 0).map
                ((ModuleCat.restrictScalarsComp f g).app K).inv =
          (Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp f g).symm (ComplexShape.up ℤ)).hom.app C ≫
            (H.mapCochainComplexSingleFunctor 0).hom.app K := by
        refine HomologicalComplex.hom_ext _ _ fun n => ?_
        by_cases hn : n = 0
        · subst n
          simp [Functor.mapCochainComplexSingleFunctor,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
            Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex]
          rfl
        · simp [Functor.mapCochainComplexSingleFunctor,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_ne G
              (ComplexShape.up ℤ) hn K,
            HomologicalComplex.singleMapHomologicalComplex_hom_app_ne S
              (ComplexShape.up ℤ) hn (G.obj K),
            HomologicalComplex.singleMapHomologicalComplex_hom_app_ne H
              (ComplexShape.up ℤ) hn K,
            Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex]
      have hbase :
          S.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app K) ≫
            (S.mapDerivedCategorySingleFunctor 0).hom.app (G.obj K) ≫
              (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} A) 0).map
                ((ModuleCat.restrictScalarsComp f g).app K).inv =
          e.hom.app Y₀ ≫ (H.mapDerivedCategorySingleFunctor 0).hom.app K := by
        let ξ := (DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat.{max v uA uB uk} k) 0).app K
        have he : e.hom.app Y₀ =
            S.mapDerivedCategory.map (G.mapDerivedCategory.map ξ.hom) ≫
              e.hom.app (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (ModuleCat.{max v uA uB uk} k) 0).obj K)) ≫
              H.mapDerivedCategory.map ξ.inv := by
          calc
            e.hom.app Y₀ =
                (e.hom.app Y₀ ≫ H.mapDerivedCategory.map ξ.hom) ≫
                  H.mapDerivedCategory.map ξ.inv := by
                    simp [Category.assoc, ← Functor.map_comp, H]
            _ = _ := by
                  rw [← e.hom.naturality ξ.hom]
                  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
                  rfl
        rw [he]
        simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
          HomologicalComplex.singleMapHomologicalComplex, Functor.mapHomologicalComplex_obj_X,
          Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
          Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
          Q_obj_single_obj, NatIso.ofComponents_hom_app, Category.id_comp, Functor.map_comp,
          Iso.app_inv, ModuleCat.restrictScalarsComp'_inv_app, Category.assoc, Iso.app_hom,
          derivedRestrictScalarsComp, Functor.mapHomologicalComplexCompIso,
          Localization.liftNatIso_hom, Localization.liftNatTrans_app,
          Localization.Lifting.compLeft_iso, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
          Category.comp_id, cancelIso, Y₀, ξ, e]
        have hnat := (DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat.{max v uA uB uk} A) 0).inv.naturality
          ((ModuleCat.restrictScalarsComp f g).app K).inv
        simp only [Functor.comp_obj, ModuleCat.restrictScalarsComp,
          ModuleCat.restrictScalarsComp', NatIso.ofComponents.app] at hnat
        rw [← hnat]
        rw [map_inv_hom_app_comp]
        refine Eq.trans (congrArg
          (fun t => S.mapDerivedCategory.map (G.mapDerivedCategory.map
              ((DerivedCategory.singleFunctorIsoCompQ
                (ModuleCat.{max v uA uB uk} k) 0).hom.app K)) ≫
            S.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
              ((CochainComplex.singleFunctor (ModuleCat.{max v uA uB uk} k) 0).obj K)) ≫ t)
          (S.mapDerivedCategoryFactors_hom_naturality_assoc _ _)) ?_
        simp only [← Functor.map_comp_assoc]
        simp only [Functor.map_comp, Category.assoc]
        simp only [← Category.assoc]
        have hqc := congrArg (DerivedCategory.Q.map) hc
        simp only [Functor.map_comp] at hqc
        let P := S.mapDerivedCategory.map (G.mapDerivedCategory.map ξ.hom) ≫
          S.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app C) ≫
          S.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
        let z := (DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat.{max v uA uB uk} A) 0).inv.app (H.obj K)
        have hqc' := congrArg (fun t => P ≫ t ≫ z) hqc
        convert hqc' using 1 <;> simp only [P, z, Category.assoc] <;> try rfl
        all_goals simp [Functor.mapHomologicalComplexCompIso]
        all_goals simp only [H, C, ← Category.assoc, Iso.inv_hom_id_app]
        all_goals simp only [Category.assoc]
        all_goals simp []
        all_goals simp [Functor.mapCochainComplexSingleFunctor,
          HomologicalComplex.singleMapHomologicalComplex]
        all_goals congr 1
      have : NatTrans.CommShift e.hom ℤ := by
        let := hτ
        have hlift : ∀ (F : DerivedCategory (ModuleCat.{max v uA uB uk} k) ⥤
            DerivedCategory (ModuleCat.{max v uA uB uk} A)) [F.CommShift ℤ],
            NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
              (HomologicalComplex.quasiIso (ModuleCat.{max v uA uB uk} k) (ComplexShape.up ℤ))
              (DerivedCategory.Q ⋙ F) F).hom ℤ := by
          intro F _
          constructor
          intro n
          ext X
          simp [Functor.commShiftIso_comp_hom_app]
        have := hlift (G.mapDerivedCategory ⋙ S.mapDerivedCategory)
        have := hlift H.mapDerivedCategory
        change NatTrans.CommShift
          (Localization.liftNatTrans DerivedCategory.Q
            (HomologicalComplex.quasiIso (ModuleCat.{max v uA uB uk} k)
              (ComplexShape.up ℤ))
            (DerivedCategory.Q ⋙ G.mapDerivedCategory ⋙ S.mapDerivedCategory)
            (DerivedCategory.Q ⋙ H.mapDerivedCategory)
            (G.mapDerivedCategory ⋙ S.mapDerivedCategory) H.mapDerivedCategory τ) ℤ
        exact Stacks.DerivedCategoryComparisons.localization_liftNatTrans_commShift
          _ _ _ _ _ _ τ
      have hcoef :
          extIntoFieldRestriction f g E.1 F.1 h i α ≫ eh.inv =
            h ≫ S.mapDerivedCategory.map q ≫ e.hom.app Y := by
        let T := (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} B) 0).obj
          (G.obj K)
        let uG := (G.mapDerivedCategorySingleFunctor 0).app K
        let uH := (H.mapDerivedCategorySingleFunctor 0).app K
        let d := (S.mapDerivedCategorySingleFunctor 0).hom.app (G.obj K) ≫
          (DerivedCategory.singleFunctor (ModuleCat.{max v uA uB uk} A) 0).map
            ((ModuleCat.restrictScalarsComp f g).app K).inv
        have hd : d = S.mapDerivedCategory.map uG.inv ≫ e.hom.app Y₀ ≫ uH.hom := by
          apply (cancel_epi (S.mapDerivedCategory.map uG.hom)).mp
          simpa [d, uG, uH, Category.assoc] using hbase
        have htail :
            (S.mapDerivedCategory.commShiftIso i).hom.app T ≫
              (shiftFunctor _ i).map d ≫
                (shiftFunctor _ i).map uH.inv ≫
                  (H.mapDerivedCategory.commShiftIso i).inv.app Y₀ =
              S.mapDerivedCategory.map ((shiftFunctor _ i).map uG.inv) ≫
                S.mapDerivedCategory.map
                  ((G.mapDerivedCategory.commShiftIso i).inv.app Y₀) ≫
                    e.hom.app Y := by
          rw [hd]
          simp only [Functor.map_comp, Category.assoc, 
            ]
          dsimp only [T]
          simp only [← Category.assoc]
          have hcs := S.mapDerivedCategory.commShiftIso_hom_naturality uG.inv i
          simp only [Functor.comp_obj] at hcs
          rw [← hcs]
          have hs := NatTrans.shift_app_comm e.hom i Y₀
          simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hs
          have hs' :
              (S.mapDerivedCategory.commShiftIso i).hom.app (G.mapDerivedCategory.obj Y₀) ≫
                (shiftFunctor _ i).map (e.hom.app Y₀) ≫
                  (H.mapDerivedCategory.commShiftIso i).inv.app Y₀ =
                S.mapDerivedCategory.map ((G.mapDerivedCategory.commShiftIso i).inv.app Y₀) ≫
                  e.hom.app Y := by
            have hs0 := congrArg (fun t => t ≫
              (H.mapDerivedCategory.commShiftIso i).inv.app Y₀) hs
            have hs1 := congrArg (fun t =>
              S.mapDerivedCategory.map
                ((G.mapDerivedCategory.commShiftIso i).inv.app Y₀) ≫ t) hs0
            simpa [Y, H, Category.assoc, ← Functor.map_comp] using hs1
          simp only [Category.assoc, ← Functor.map_comp, 
            ]
          have hh : e.hom.app Y₀ ≫ uH.hom ≫ uH.inv = e.hom.app Y₀ := by
            simp []
          rw [hh]
          dsimp only [Y₀, Functor.comp_obj] at hs' ⊢
          rw [hs']
          simp [Category.assoc]
        simpa [q, eg, eh, extIntoFieldRestriction, d, uG, uH,
          Category.assoc] using
          congrArg (fun t => h ≫ S.mapDerivedCategory.map α ≫ t) htail
      let Dg := totalDerivedExtensionScalars.{uB, uk, max v uA} g
      let Dgf := totalDerivedExtensionScalars.{uA, uk, max v uB} (g.comp f)
      let ag := @derivedExtensionScalarsAdjunction.{uB, uk, max v uA}
        B k _ _ g _ _ Dg.functor Dg.comparison Dg.isLeftDerived
      let agf := @derivedExtensionScalarsAdjunction.{uA, uk, max v uB}
        A k _ _ (g.comp f) _ _ Dgf.functor Dgf.comparison Dgf.isLeftDerived
      change (agf.homEquiv E.1 Y).symm
          (extIntoFieldRestriction f g E.1 F.1 h i α ≫ eh.inv) =
        (agf.homEquiv E.1 (Dg.functor.obj F.1)).symm
          (h ≫ S.mapDerivedCategory.map (ag.unit.app F.1) ≫
            e.hom.app (Dg.functor.obj F.1)) ≫
          (ag.homEquiv F.1 Y).symm q
      rw [hcoef]
      exact adjunction_comp_right_mate ag agf e h q
    simp only [extIntoFieldEquivDualBaseChangeHomology, AddEquiv.trans_apply]
    rw [hbridge]
    exact homologyMapToInjectiveEquiv_naturality.{uk, max v uA uB uk}
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
        (f := g)).functor.obj F.1)
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
        (f := g.comp f)).functor.obj E.1)
      (ModuleCat.of k (ULift.{max v uA uB} k)) i b
      (derivedExtRestrictionEquiv.{uB, uk, max v uA} g F.1 i α)

end DerivedCategory
