module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPowerEndo

/-!
# The Frobenius of a finite extension of the base field on cohomology

Let `k` be a finite field with `q = p ^ f` elements, `Y` a scheme over `k`, `k'` an extension of
`k` with `q ^ m` elements and `k̄` an extension of `k'`. Write `Y' = Y ×_k k'`, a scheme over `k'`,
and `gl : Y' ⟶ Y` for the projection. For a bounded below complex `C` of sheaves of `Λ`-modules on
`Y_étale` the geometric fibres agree, `Y'_{k̄} = Y_{k̄}`, and this identifies
`RΓ(Y'_{k̄}, (gl⁻¹ C)|_{Y'_{k̄}})` with `RΓ(Y_{k̄}, C|_{Y_{k̄}})`. This file proves that the
identification carries the canonical Frobenius action of `Y'` over `k'` to the `m`-th power of the
canonical Frobenius action of `Y` over `k`. This is the cohomological half of the reduction, in the
proof of [Stacks, Tag 03V0], of the trace formula for `π_X^m` to the trace formula of Tag 03V2 for
`X ×_k k_m` over `k_m`.

## Main definitions

* `Stacks.EtaleCohomology.extensionBaseChangeMap`: the base change map
  `pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L` along the identification `e : Y'_{k̄} ≅ Y_{k̄}`.
* `Stacks.EtaleCohomology.frobeniusExtensionCohomologyIso`:
  `RΓ(Y'_{k̄}, (gl⁻¹ C)|_{Y'_{k̄}}) ≅ RΓ(Y_{k̄}, C|_{Y_{k̄}})`.

## Main results

* `Stacks.EtaleCohomology.extensionBaseChangeMap_comp_frobeniusBaseChangeTwist`: the base change
  map intertwines the Frobenius twist of `Y'` with the twist of `π̄ ^ m`.
* `Stacks.EtaleCohomology.frobeniusExtensionCohomologyIso_comm`: the identification carries the
  Frobenius of `Y'` to the `m`-th power of the Frobenius of `Y`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]

/-! ### The base change map along `Y'_{k̄} ≅ Y_{k̄}` -/

/-- The square `pr' ≫ gl = e ≫ pr` of the two geometric fibres over `Y' ⟶ Y`. -/
lemma fieldBaseChangeProj_extension_comp :
    fieldBaseChangeProj (extensionOver Y k') kbar ≫ extensionProj Y k' =
      (fieldBaseChangeExtensionIso Y k' kbar).hom ≫ fieldBaseChangeProj Y kbar :=
  (fieldBaseChangeExtensionIso_hom_fst Y k' kbar).symm

/-- **The base change map** `pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L` along the identification
`e : Y'_{k̄} ≅ Y_{k̄}` of the geometric fibres; it is an isomorphism. -/
abbrev extensionBaseChangeMap :=
  etaleModuleBaseChangeMap Λ (fieldBaseChangeProj Y kbar)
    (fieldBaseChangeProj (extensionOver Y k') kbar) (extensionProj Y k')
    (fieldBaseChangeExtensionIso Y k' kbar).hom
    (fieldBaseChangeProj (extensionOver Y k') kbar ≫ extensionProj Y k') rfl
    (fieldBaseChangeProj_extension_comp Y k' kbar)

/-- The base change map `pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L` is an isomorphism. -/
instance (L : EtaleModules.{u, r} Λ Y.left) :
    IsIso ((extensionBaseChangeMap Λ Y k' kbar).app L) :=
  isIso_etaleModuleBaseChangeMap_app Λ _ _ _ _ _ _ _ L

/-! ### The Frobenius instance of the twist comparison -/

section Twist

variable [Fintype k] [Fintype k'] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * m))

include hcard' in
omit [Fact p.Prime] [CharP k' p] in
/-- `q m ≠ 0`, since `k'` has more than one element. -/
lemma mul_ne_zero_of_card_extension : q * m ≠ 0 := by
  rintro h
  rw [h, pow_zero] at hcard'
  exact Nat.ne_of_gt Fintype.one_lt_card hcard'

omit [Fintype k] in
/-- The Frobenius descent isomorphisms of `Y'` and of `Y` for the `q m`-fold absolute Frobenius are
compatible with the direct image along `gl : Y' ⟶ Y`. -/
lemma map_geometricFrobeniusPushforwardIso_extension
    (M : EtaleModules.{u, r} Λ (extensionOver Y k').left) :
    (etaleModuleDirectImage.{u, r} Λ (extensionProj Y k')).map
        ((geometricFrobeniusPushforwardIso (extensionOver Y k') p (q * m) hcard'
          (ModuleCat.{max (u + 1) r} Λ)).hom.app M) ≫
      (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobenius (extensionOver Y k') p (q * m)
        hcard').left (extensionProj Y k')
        (extensionProj Y k' ≫ absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) (q * m))
        (absoluteFrobeniusPow_naturality (extensionProj Y k') p _ _ (q * m)).symm).hom.app M =
    (frobeniusPowDescent Λ Y p (q * m) (mul_ne_zero_of_card_extension k' p q m hcard')).app
        ((etaleModuleDirectImage.{u, r} Λ (extensionProj Y k')).obj M) ≫
      (etaleModuleDirectImageComp.{u, r} Λ (extensionProj Y k')
        (absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) (q * m))
        (extensionProj Y k' ≫ absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) (q * m))
        rfl).hom.app M :=
  smallEtalePushforward_map_etaleSheafPushforwardComparison (extensionProj Y k') p
    (isInCharacteristic_of_over Y) (isInCharacteristic_of_over (extensionOver Y k'))
    (mul_ne_zero_of_card_extension k' p q m hcard') _
    (absoluteFrobeniusPow_naturality (extensionProj Y k') p _ _ (q * m)).symm rfl
    (ModuleCat.{max (u + 1) r} Λ) M

/-- **The base change map intertwines the Frobenius twists.**  Under the base change map
`pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L`, the Frobenius twist of `Y'` over `k'` at `gl⁻¹ L`, followed by
`e_* π̄'_* = π̄^m_* e_*`, is the base change twist of `π̄ ^ m` over the `q m`-fold absolute
Frobenius of `Y`. -/
theorem extensionBaseChangeMap_comp_frobeniusBaseChangeTwist (L : EtaleModules.{u, r} Λ Y.left) :
    (extensionBaseChangeMap Λ Y k' kbar).app L ≫
        (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom).map
          ((frobeniusBaseChangeTwist.{u, r} Λ (extensionOver Y k') kbar p (q * m) hcard').app
            ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).obj L)) ≫
        ((etaleModuleDirectImageComp.{u, r} Λ
            (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * m) hcard')
            (fieldBaseChangeExtensionIso Y k' kbar).hom
            (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * m) hcard' ≫
              (fieldBaseChangeExtensionIso Y k' kbar).hom) rfl).hom.app
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj (extensionOver Y k') kbar)).obj
              ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).obj L)) ≫
          (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom
            (geometricFrobeniusBaseChangePow Y kbar p q hcard m)
            (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * m) hcard' ≫
              (fieldBaseChangeExtensionIso Y k' kbar).hom)
            (geometricFrobeniusBaseChange_extension_comp_hom Y kbar p q hcard k' m hcard')).inv.app
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj (extensionOver Y k') kbar)).obj
              ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).obj L))) =
      (etaleModuleBaseChangeTwist.{u, r} Λ (fieldBaseChangeProj Y kbar)
          (geometricFrobeniusBaseChangePow Y kbar p q hcard m)
          (absoluteFrobeniusPow Y.left p (isInCharacteristic_of_over Y) (q * m))
          (geometricFrobeniusBaseChangePow_fst Y kbar p q hcard m)
          (frobeniusPowDescent Λ Y p (q * m)
            (mul_ne_zero_of_card_extension k' p q m hcard'))).app L ≫
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChangePow Y kbar p q hcard m)).map
          ((extensionBaseChangeMap Λ Y k' kbar).app L) :=
  etaleModuleBaseChangeMap_comp_twist Λ _ _ _ _ _ rfl
    (fieldBaseChangeProj_extension_comp Y k' kbar) _ _ _ _ _ _ _ rfl _ _ _ rfl _ _
    (map_geometricFrobeniusPushforwardIso_extension Λ Y k' p q m hcard') L

end Twist

/-! ### The comparison of the cohomology of the two geometric fibres -/

section Cohomology

/-- Two maps `s_* e_* A'_* X ⟶ s'_* X` assembled from the composition isomorphisms of direct
images agree. -/
lemma map_transportTwist_comp_overDirectImageComp {Yb' Yb S : Scheme.{u}} (A' : Yb' ⟶ Yb')
    (e : Yb' ⟶ Yb) (A : Yb ⟶ Yb) (s : Yb ⟶ S) (s' : Yb' ⟶ S) (eA : Yb' ⟶ Yb)
    (heA : eA = A' ≫ e) (heA' : eA = e ≫ A) (hs : s = A ≫ s) (hs' : s' = A' ≫ s')
    (hes : s' = e ≫ s) (X : EtaleModules.{u, r} Λ Yb') :
    (etaleModuleDirectImage.{u, r} Λ s).map
        ((etaleModuleDirectImageComp.{u, r} Λ A' e eA heA).hom.app X ≫
          (etaleModuleDirectImageComp.{u, r} Λ e A eA heA').inv.app X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ A s s hs).hom.app
          ((etaleModuleDirectImage.{u, r} Λ e).obj X) ≫
        (etaleModuleDirectImageComp.{u, r} Λ e s s' hes).hom.app X =
    (etaleModuleDirectImageComp.{u, r} Λ e s s' hes).hom.app
        ((etaleModuleDirectImage.{u, r} Λ A').obj X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ A' s' s' hs').hom.app X := by
  have h₁ : s' = eA ≫ s := by rw [heA', Category.assoc, ← hs, hes]
  have k₁ : (etaleModuleDirectImage.{u, r} Λ s).map
        ((etaleModuleDirectImageComp.{u, r} Λ A' e eA heA).hom.app X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ eA s s' h₁).hom.app X =
      (etaleModuleDirectImageComp.{u, r} Λ e s s' hes).hom.app
          ((etaleModuleDirectImage.{u, r} Λ A').obj X) ≫
        (etaleModuleDirectImageComp.{u, r} Λ A' s' s' hs').hom.app X := by
    have h := congrArg (fun z => z.hom.app X) (smallEtalePushforwardComp'_assoc A' e s eA heA s'
      hes s' h₁ hs' (ModuleCat.{max (u + 1) r} Λ))
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp] at h
    exact h
  have k₂ : (etaleModuleDirectImage.{u, r} Λ s).map
        ((etaleModuleDirectImageComp.{u, r} Λ e A eA heA').hom.app X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ eA s s' h₁).hom.app X =
      (etaleModuleDirectImageComp.{u, r} Λ A s s hs).hom.app
          ((etaleModuleDirectImage.{u, r} Λ e).obj X) ≫
        (etaleModuleDirectImageComp.{u, r} Λ e s s' hes).hom.app X := by
    have h := congrArg (fun z => z.hom.app X) (smallEtalePushforwardComp'_assoc e A s eA heA' s
      hs s' h₁ hes (ModuleCat.{max (u + 1) r} Λ))
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp] at h
    exact h
  rw [← k₂, ← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id, k₁]

/-- The base change map applied degreewise to the restriction of a bounded below complex, as an
isomorphism `C|_{Y_k̄} ≅ e_* ((gl⁻¹ C)|_{Y'_k̄})` of bounded below complexes. -/
def extensionBaseChangeComplexIso (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C ≅
      (etaleModuleDirectImage.{u, r} Λ
          (fieldBaseChangeExtensionIso Y k' kbar).hom).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C)) :=
  have : IsIso (extensionBaseChangeMap Λ Y k' kbar) := NatIso.isIso_of_isIso_app _
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex (asIso (extensionBaseChangeMap Λ Y k' kbar)) _).app C.obj)

/-- The structure morphisms of the two geometric fibres agree under `e`. -/
lemma fieldBaseChangeExtensionIso_snd :
    pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar) =
      (fieldBaseChangeExtensionIso Y k' kbar).hom ≫ pullback.snd Y.hom (specAlgebraMap k kbar) :=
  (fieldBaseChangeExtensionIso_hom_snd Y k' kbar).symm

/-- **`RΓ(Y'_{k̄}, (gl⁻¹ C)|_{Y'_{k̄}}) ≅ RΓ(Y_{k̄}, C|_{Y_{k̄}})`**: the direct image along the
identification `e : Y'_{k̄} ≅ Y_{k̄}` of the geometric fibres, over `Spec k̄`, followed by the
inverse of the base change map. -/
def frobeniusExtensionCohomologyIso (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ
            (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ (extensionOver Y k') kbar
            ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj
              C))) ≅
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)) :=
  Functor.twistTransportIso
      (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
      (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom)
      (etaleModuleDirectImage.{u, r} Λ
        (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar)))
      (etaleModuleDirectImageComp.{u, r} Λ _ _ _ (fieldBaseChangeExtensionIso_snd Y k' kbar)) _ ≪≫
    ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso (extensionBaseChangeComplexIso Λ Y k' kbar C)))).symm

/-- Pasting two naturality squares through an inverse. -/
private lemma comp_comp_inv_naturality {D : Type*} [Category* D] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : D}
    (tC : X₀ ⟶ X₁) (rC : X₂ ≅ X₁) (tD : Y₀ ⟶ Y₁) (rD : Y₂ ≅ Y₁) (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁)
    (c : X₂ ⟶ Y₂) (h₁ : a ≫ tD = tC ≫ b) (h₂ : c ≫ rD.hom = rC.hom ≫ b) :
    a ≫ tD ≫ rD.inv = (tC ≫ rC.inv) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, h₂, Iso.inv_hom_id_assoc]

/-- The identification `e_* π̄'_* ≅ (π̄ ^ m)_* e_*` of the direct images along the two sides of
`π̄' ≫ e = e ≫ π̄ ^ m`. -/
abbrev extensionFrobeniusTwistIso [Fintype k] [Fintype k'] (p q : ℕ) [Fact p.Prime] [CharP k p]
    [CharP k' p] (hcard : Fintype.card k = p ^ q) (m : ℕ)
    (hcard' : Fintype.card k' = p ^ (q * m)) :
    etaleModuleDirectImage.{u, r} Λ
        (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * m) hcard') ⋙
      etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom ≅
      etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom ⋙
        etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChangePow Y kbar p q hcard m) :=
  etaleModuleDirectImageComp.{u, r} Λ _ _ _ rfl ≪≫
    (etaleModuleDirectImageComp.{u, r} Λ _ _ _
      (geometricFrobeniusBaseChange_extension_comp_hom Y kbar p q hcard k' m hcard')).symm


/-- **The identification of the cohomology of the two geometric fibres is natural** in the
complex. -/
theorem frobeniusExtensionCohomologyIso_hom_naturality
    {C D : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)} (φ : C ⟶ D) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, r} Λ
            (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
                (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.map
              ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.map
                φ)))) ≫
      (frobeniusExtensionCohomologyIso Λ Y k' kbar D).hom =
    (frobeniusExtensionCohomologyIso Λ Y k' kbar C).hom ≫
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ))) := by
  have hT := Functor.twistTransportIso_hom_naturality
    (F₁ := etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom)
    (F₁' := etaleModuleDirectImage.{u, r} Λ
      (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar)))
    (κ := etaleModuleDirectImageComp.{u, r} Λ _ _ _ (fieldBaseChangeExtensionIso_snd Y k' kbar))
    ((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.map
      ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.map φ))
  have hB : (etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ ≫
      (extensionBaseChangeComplexIso Λ Y k' kbar D).hom =
      (extensionBaseChangeComplexIso Λ Y k' kbar C).hom ≫
        (etaleModuleDirectImage.{u, r} Λ
            (fieldBaseChangeExtensionIso Y k' kbar).hom).mapCochainComplexPlus.map
          ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.map
              φ)) := by
    ext n : 2
    exact (extensionBaseChangeMap Λ Y k' kbar).naturality (φ.hom.f n)
  refine comp_comp_inv_naturality _ _ _ _ _ _ _ hT ?_
  show (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map _ =
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  rw [hB]

variable [Fintype k] [Fintype k'] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius of the extension is the power of the Frobenius on cohomology.**  If `k'` has
`q ^ (m + 1)` elements, the identification
`RΓ(Y'_{k̄}, (gl⁻¹ C)|_{Y'_{k̄}}) ≅ RΓ(Y_{k̄}, C|_{Y_{k̄}})` carries the canonical Frobenius action
of `Y' = Y ×_k k'` over `k'` to the `(m + 1)`-st power of the canonical Frobenius action of `Y`
over `k`. -/
theorem frobeniusExtensionCohomologyIso_comm (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    frobeniusRestrictionCohomologyEndo.{u, r} Λ (extensionOver Y k') kbar p (q * (m + 1)) hcard'
        ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C) ≫
      (frobeniusExtensionCohomologyIso Λ Y k' kbar C).hom =
    (frobeniusExtensionCohomologyIso Λ Y k' kbar C).hom ≫
      ((End.of (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) ^ (m + 1)).asHom := by
  have hqm := mul_ne_zero_of_card_extension k' p q (m + 1) hcard'
  rw [frobeniusRestrictionCohomologyEndo_pow Λ Y kbar p q hcard C m (q * (m + 1)) hqm rfl
    (geometricFrobeniusBaseChangePow_fst Y kbar p q hcard (m + 1))
    (geometricFrobeniusBaseChangePow_snd Y kbar p q hcard (m + 1)).symm,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  have hT := Functor.derivedTwistEndo_transport
    (P := etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1)))
    (F₁ := etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom)
    (F₁' := etaleModuleDirectImage.{u, r} Λ
      (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar)))
    (κ := etaleModuleDirectImageComp.{u, r} Λ _ _ _ (fieldBaseChangeExtensionIso_snd Y k' kbar))
    (P' := etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * (m + 1)) hcard'))
    (θ := overDirectImageComp Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) _
      (geometricFrobeniusBaseChangePow_snd Y kbar p q hcard (m + 1)).symm)
    (θ' := etaleModuleDirectImageComp.{u, r} Λ
      (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * (m + 1)) hcard')
      (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))
      (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar))
      (geometricFrobeniusBaseChange_comp_toBase (extensionOver Y k') kbar p (q * (m + 1))
        hcard').symm)
    (ρ := extensionFrobeniusTwistIso Λ Y k' kbar p q hcard (m + 1) hcard')
    (fun X => map_transportTwist_comp_overDirectImageComp Λ _ _ _ _ _ _ rfl _ _ _ _ X)
    ((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C))
    (baseChangeTwistComplex Λ (fieldBaseChangeProj (extensionOver Y k') kbar)
      (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * (m + 1)) hcard')
      (geometricFrobenius (extensionOver Y k') p (q * (m + 1)) hcard').left
      (geometricFrobeniusBaseChange_comp_fst (extensionOver Y k') kbar p (q * (m + 1)) hcard')
      (geometricFrobeniusPushforwardIso (extensionOver Y k') p (q * (m + 1)) hcard'
        (ModuleCat.{max (u + 1) r} Λ)).hom
      ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C))
  have hN := Functor.derivedTwistEndo_naturality
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1)))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (overDirectImageComp Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) _
      (geometricFrobeniusBaseChangePow_snd Y kbar p q hcard (m + 1)).symm)
    (extensionBaseChangeComplexIso Λ Y k' kbar C).hom
    (baseChangeTwistComplex Λ (fieldBaseChangeProj Y kbar) _ _
      (geometricFrobeniusBaseChangePow_fst Y kbar p q hcard (m + 1))
      (frobeniusPowDescent Λ Y p (q * (m + 1)) hqm) C)
    ((etaleModuleDirectImage.{u, r} Λ
          (fieldBaseChangeExtensionIso Y k' kbar).hom).mapCochainComplexPlus.map
        (baseChangeTwistComplex Λ (fieldBaseChangeProj (extensionOver Y k') kbar)
          (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * (m + 1)) hcard')
          (geometricFrobenius (extensionOver Y k') p (q * (m + 1)) hcard').left
          (geometricFrobeniusBaseChange_comp_fst (extensionOver Y k') kbar p (q * (m + 1)) hcard')
          (geometricFrobeniusPushforwardIso (extensionOver Y k') p (q * (m + 1)) hcard'
            (ModuleCat.{max (u + 1) r} Λ)).hom
          ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C)) ≫
      Functor.transportTwistMap
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChangePow Y kbar p q hcard (m + 1)))
        (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeExtensionIso Y k' kbar).hom)
        (etaleModuleDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange (extensionOver Y k') kbar p (q * (m + 1)) hcard'))
        (extensionFrobeniusTwistIso Λ Y k' kbar p q hcard (m + 1) hcard')
        ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj (extensionOver Y k') kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, r} Λ (extensionProj Y k')).mapCochainComplexPlus.obj C)))
    (congrArg DerivedCategory.Plus.Q.map (by
        ext n : 2
        exact (extensionBaseChangeMap_comp_frobeniusBaseChangeTwist Λ Y k' kbar p q hcard (m + 1)
          hcard' (C.obj.X n)).symm))
  exact comp_comp_inv_naturality _ _ _ _ _ _ _ hT hN

end Cohomology

end Stacks.EtaleCohomology

end
