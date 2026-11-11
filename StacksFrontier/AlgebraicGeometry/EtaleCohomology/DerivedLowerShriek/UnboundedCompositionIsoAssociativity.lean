module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnboundedCompositionIsoTower

/-!
# The associativity of the composition isomorphisms of `Rf_!` on `D(X_étale, Λ)`
([Stacks, Tag 0F7K])

Let `Λ` be a torsion ring and let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` be separated
morphisms of finite type of quasi-compact and quasi-separated schemes. The two isomorphisms
`R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` on unbounded derived categories built from the isomorphisms
of [Stacks, Tag 0F7J] (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) agree.

Following [Stacks, Tag 0F7K], choose a compactification `Z̄` of `Z`, a compactification `Ȳ` of
`Y` over `Z̄` and a compactification `X̄` of `X` over `Ȳ`, and put `W = Ȳ ×_Z̄ Z`. Both
isomorphisms are then read in `D(Z̄)` through the maps of [Stacks, Tag 0F7B] of the cartesian
squares `X̄ ×_Z̄ Z ⟶ X̄` over `W ⟶ Ȳ` and `W ⟶ Ȳ` over `Z ⟶ Z̄`, whose vertical pasting is
`X̄ ×_Z̄ Z ⟶ X̄` over `Z ⟶ Z̄` ([Stacks, Tag 0F7C]); the comparison over `Ȳ` is
`Stacks.EtaleCohomology.tower_ZC`. The independence of the isomorphisms of [Stacks, Tag 0F7J] of
the compactifications (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_first`,
`..._second` and `..._third`) gives the statement for arbitrary compactifications.

## Main results

* `Stacks.EtaleCohomology.towerUnbounded_Zbar`: the comparison over `Z̄`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_assoc`: **Stacks 0F7K** on
  `D(X_étale, Λ)` for a torsion ring `Λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

variable (Λ : Type) [Ring Λ]

/-! ### Chases over plain objects -/

section Chain

/-- Inverting an associativity square of isomorphisms, over plain objects. -/
private lemma inv_assoc_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {a e : 𝒟} {c d : 𝒞} (x : a ⟶ F.obj c) (y : c ⟶ d) (z : a ⟶ e) (w : e ⟶ F.obj d)
    (zi : e ⟶ a) (yi : d ⟶ c) (A : x ≫ F.map y = z ≫ w) (hz : zi ≫ z = 𝟙 _)
    (hy : y ≫ yi = 𝟙 _) : zi ≫ x = w ≫ F.map yi := by
  calc zi ≫ x = zi ≫ (x ≫ F.map y) ≫ F.map yi := by
        rw [Category.assoc, ← F.map_comp, hy, F.map_id, Category.comp_id]
    _ = w ≫ F.map yi := by rw [A, Category.assoc, reassoc_of% hz]

/-- The chase behind `Stacks.EtaleCohomology.tower_phi`, over plain objects. -/
private lemma phi_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (R : 𝒞 ⥤ 𝒟) {a b : 𝒟}
    {c0 c1 c3 c4 : 𝒞} (Hc : a ⟶ b) (CO : b ⟶ R.obj c3) (L : a ⟶ R.obj c0) (Hc' : c0 ⟶ c1)
    (Li : R.obj c1 ⟶ b) (L' : b ⟶ R.obj c1) (Ψ : c1 ⟶ c3) (e : c3 ⟶ c4)
    (hHc : Hc = L ≫ R.map Hc' ≫ Li) (hCO : CO = L' ≫ R.map Ψ) (hi : Li ≫ L' = 𝟙 _) :
    Hc ≫ CO ≫ R.map e = L ≫ R.map (Hc' ≫ Ψ ≫ e) := by
  rw [hHc, hCO]
  simp only [Category.assoc, R.map_comp]
  rw [reassoc_of% hi]

/-- A functor applied to a chase ending in an isomorphism, over plain objects. -/
private lemma map_zc_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {x0 x1 x2 x3 x4 x5 : 𝒞} (a : x0 ⟶ x1) (b : x1 ⟶ x2) (c : x2 ⟶ x3) (d : x3 ⟶ x4)
    (e : x4 ⟶ x5) (r : x0 ⟶ x5) (eh : x5 ⟶ x4) (h : a ≫ b ≫ c ≫ d ≫ e = r)
    (he : e ≫ eh = 𝟙 _) : F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map r ≫ F.map eh := by
  have he' : F.map e ≫ F.map eh = 𝟙 _ := by rw [← F.map_comp, he, F.map_id]
  rw [← h]
  simp only [F.map_comp, Category.assoc, he', Category.comp_id]

/-- The chase behind `Stacks.EtaleCohomology.towerUnbounded_Zbar`, over plain objects. -/
private lemma zbar_chain {𝒞 : Type*} [Category* 𝒞]
    {o0 o1 o2 o3 o4 o5 p1 p2 p3 p4 q1 q2 q3 : 𝒞}
    (HU13 : o0 ⟶ o1) (Lpg : o1 ⟶ o2) (RgΨ : o2 ⟶ o3) (ΨY : o3 ⟶ o4) (ΨZ : o0 ⟶ o5)
    (EΦ : o5 ⟶ o4) (RpfEci : o0 ⟶ p1) (IZ : p1 ⟶ o5) (sqZ : o5 ⟶ p1) (RpfEc : p1 ⟶ o0)
    (Rpfm : p1 ⟶ p2) (Rpfρ : o0 ⟶ p2) (L13Zi : p2 ⟶ o1) (LpgC : p2 ⟶ p3) (RgL13i : p3 ⟶ o2)
    (LpgN : p1 ⟶ p4) (Rgm : p4 ⟶ p3) (EjhL : o5 ⟶ q1) (sqY : q1 ⟶ q2) (Rgsq : q2 ⟶ p4)
    (REΦ' : q2 ⟶ q3) (REYh : q3 ⟶ o3) (REYi : o3 ⟶ q3) (IY : q3 ⟶ o4) (ERΦ' : q1 ⟶ o4)
    (sqY' : o4 ⟶ q3)
    (h1 : ΨZ = RpfEci ≫ IZ) (h2 : IZ ≫ sqZ = 𝟙 _) (h3 : RpfEci ≫ RpfEc = 𝟙 _)
    (h4 : HU13 = Rpfρ ≫ L13Zi) (h5 : RpfEc ≫ Rpfρ = Rpfm) (h6 : L13Zi ≫ Lpg = LpgC ≫ RgL13i)
    (h7 : Rpfm ≫ LpgC = LpgN ≫ Rgm) (h8 : sqZ ≫ LpgN = EjhL ≫ sqY ≫ Rgsq)
    (h9 : Rgsq ≫ Rgm ≫ RgL13i ≫ RgΨ = REΦ' ≫ REYh) (h10 : ΨY = REYi ≫ IY)
    (h11 : REYh ≫ REYi = 𝟙 _) (h12 : sqY ≫ REΦ' = ERΦ' ≫ sqY') (h13 : sqY' ≫ IY = 𝟙 _)
    (h14 : EΦ = EjhL ≫ ERΦ') :
    HU13 ≫ Lpg ≫ RgΨ ≫ ΨY = ΨZ ≫ EΦ := by
  have key : sqZ ≫ RpfEc ≫ HU13 ≫ Lpg ≫ RgΨ ≫ ΨY = EΦ := by
    rw [h4, h10, h14]
    simp only [Category.assoc]
    rw [reassoc_of% h5, reassoc_of% h6, reassoc_of% h7, reassoc_of% h8, reassoc_of% h9,
      reassoc_of% h11, reassoc_of% h12, h13, Category.comp_id]
  calc HU13 ≫ Lpg ≫ RgΨ ≫ ΨY = RpfEci ≫ IZ ≫ sqZ ≫ RpfEc ≫ HU13 ≫ Lpg ≫ RgΨ ≫ ΨY := by
        rw [reassoc_of% h2, reassoc_of% h3]
    _ = ΨZ ≫ EΦ := by rw [key, h1, Category.assoc]

end Chain

/-- The unbounded Leray isomorphisms along `A ⟶ B ⟶ C ⟶ S`, with the first inverted. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_inv_hom_app {A B C S : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (q : C ⟶ S) (ab : A ⟶ C) (hab : ab = a ≫ b) (bq : B ⟶ S)
    (hbq : bq = b ≫ q) (abq : A ⟶ S) (h₁ : abq = ab ≫ q) (h₂ : abq = a ≫ bq)
    (M : DerivedCategory (EtaleModules.{u, 0} Λ A)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ a bq abq h₂).inv.app M ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ ab q abq h₁).hom.app M =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ b q bq hbq).hom.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ a).obj M) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).map
        ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ a b ab hab).inv.app M) :=
  inv_assoc_chain _ _ _ _ _ _ _
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ a b q ab hab bq hbq abq h₁ h₂ M)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)

/-! ### The comparison over `Z̄` -/

section TowerZbar

open CompactificationOf CompactificationOf.Tower

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {h : Z ⟶ T} (jh : CompactificationOf (Over.mk h))
  (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
  (jX : CompactificationOf (Over.mk (f ≫ (compOver jh jY).immersion)))
  [CompactSpace (jg jh jY).space]

/-- Over `Z`, the comparison of [Stacks, Tag 0F7I] along `compOver jg jXW ⟶ jfg₃` followed by
the isomorphism of [Stacks, Tag 0F7J] through `X̄ ×_Z̄ Z` is the Leray isomorphism followed by
`Rḡ_*` of the comparison along `overBar jg jXW ⟶ jXW` and of `Ψ`. -/
theorem tower_phi (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄ jh jY jX)).app K ≫
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
      (derivedLowerShriekUnbounded.{u, 0} g (jg jh jY) Λ).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K) =
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (jXW jh jY jX).toBase
        (jg jh jY).toBase (snd₃ jh jY jX) (jfg₃_toBase_eq jh jY jX)).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jXW jh jY jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jg jh jY).toBase).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K ≫
          (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jg jh jY) (jXW jh jY jX)).hom.app K ≫
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jg jh jY).immersion).map
            ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)) :=
  phi_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jg jh jY).toBase) _ _ _ _ _ _ _ _
    (derivedLowerShriekUnboundedHomUniv_ofFactorHom Λ (jg jh jY).toBase (f ≫ g) (c₃₄' jh jY jX)
      ((overBar (jg jh jY) (jXW jh jY jX)).toBase ≫ (jg jh jY).toBase) rfl (snd₃ jh jY jX)
      (jfg₃_toBase_eq jh jY jX) (immersion_toBase (jfg₄ jh jY jX))
      (immersion_toBase (jfg₃ jh jY jX)) K)
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ (jg jh jY) (jXW jh jY jX) K)
    (Iso.inv_hom_id_app _ _)

/-- **The comparison over `Z̄`** ([Stacks, Tag 0F7K]): the two isomorphisms
`R(f̄ ≫ ḡ)_* (X ⟶ X̄)_! ≅ i_{Z!} Rg_! Rf_!` in `D(Z̄)`, through `Ȳ` and through `X̄ ×_Z̄ Z`,
agree, read through the comparisons of [Stacks, Tag 0F7I]. -/
theorem towerUnbounded_Zbar [CompactSpace jh.space] [CompactSpace (jgh jh jY).space]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₁₃' jh jY jX)).app K ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (overBar (jgh jh jY) jX).toBase
          (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (overBar (jgh jh jY) jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (gbar jh jY)).map
        ((derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jgh jh jY) jX).hom.app K) ≫
      (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jh jY).hom.app
        ((derivedLowerShriekUnbounded.{u, 0} f (jf₁ jh jY jX) Λ).obj K) =
    (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jh (jXZ jh jY jX)).hom.app K ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jh.immersion).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄ jh jY jX)).app K ≫
          (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
          (derivedLowerShriekUnbounded.{u, 0} g (jg jh jY) Λ).map
            ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)) := by
  let N := (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jfg₃ jh jY jX).immersion).obj K
  let L := (derivedLowerShriekUnbounded.{u, 0} f (jf₁ jh jY jX) Λ).obj K
  have hVP := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (fst₃ jh jY jX) (iW jh jY) jh.immersion (pmap jh jY jX) (overBar (jgh jh jY) jX).toBase
    (jg jh jY).toBase (gbar jh jY) (snd₃ jh jY jX) (jXZ jh jY jX).toBase
    (jfg₃_toBase_eq jh jY jX) rfl (towerSheafT Λ hΛ jh jY jX)
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jY.toBase jh.immersion (restrictBaseι jh jY)
      (restrictBase jh jY).toBase (IsPullback.of_hasPullback jY.toBase jh.immersion))
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (jXZ jh jY jX).toBase jh.immersion
      (restrictBaseι jh (jXZ jh jY jX)) (restrictBase jh (jXZ jh jY jX)).toBase
      (IsPullback.of_hasPullback (jXZ jh jY jX).toBase jh.immersion))
    (fun F => IsExtensionByZeroBaseChange.vertical_paste _ _
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (overBar (jgh jh jY) jX).toBase (iW jh jY) (fst₃ jh jY jX) (pmap jh jY jX)
        (isPullback_pmap jh jY jX))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ jY.toBase
        jh.immersion (restrictBaseι jh jY) (restrictBase jh jY).toBase
        (IsPullback.of_hasPullback jY.toBase jh.immersion))
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (jXZ jh jY jX).toBase jh.immersion (restrictBaseι jh (jXZ jh jY jX))
        (restrictBase jh (jXZ jh jY jX)).toBase
        (IsPullback.of_hasPullback (jXZ jh jY jX).toBase jh.immersion)) F)) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hVP
  have h7 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
    (overBar (jgh jh jY) jX).toBase (gbar jh jY) ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY)
    rfl).hom.naturality
    ((derivedExtensionByZeroUnboundedCompIso Λ (jfg₃ jh jY jX).immersion
        (fst₃ jh jY jX)).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₁₃' jh jY jX)).app K)
  have h12 := (derivedExtensionByZeroSquareMap Λ (restrictBaseι jh jY) jh.immersion
    (restrictBase jh jY).toBase jY.toBase
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jY.toBase jh.immersion (restrictBaseι jh jY)
      (restrictBase jh jY).toBase (IsPullback.of_hasPullback jY.toBase jh.immersion))).naturality
    ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄' jh jY jX)).app K ≫
      (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jg jh jY) (jXW jh jY jX)).hom.app K ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jg jh jY).immersion).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K))
  exact zbar_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ jh (jXZ jh jY jX) K)
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom_app_squareMap Λ hΛ
      (jXZ jh jY jX).toBase jh.immersion (restrictBaseι jh (jXZ jh jY jX))
      (restrictBase jh (jXZ jh jY jX)).toBase
      (IsPullback.of_hasPullback (jXZ jh jY jX).toBase jh.immersion) N)
    (map_inv_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (jXZ jh jY jX).toBase) _ _
      (Iso.inv_hom_id_app _ _))
    (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ (c₁₃' jh jY jX) K)
    (Functor.map_comp _ _ _).symm
    (etaleModuleDerivedDirectImageUnboundedLerayIso_inv_hom_app Λ (Hom.map (c₁₃' jh jY jX))
      (overBar (jgh jh jY) jX).toBase (gbar jh jY) (overBar (jgh jh jY) jX).toBase
      (Category.id_comp _).symm (overBar jh (jXZ jh jY jX)).toBase rfl (jXZ jh jY jX).toBase rfl
      (map_comp_toBase (c₁₃' jh jY jX)).symm
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jXZ jh jY jX).immersion).obj K))
    h7 hVP
    (map_zc_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (gbar jh jY)) _ _ _ _ _ _ _
      (tower_ZC Λ hΛ jh jY jX K) (Iso.inv_hom_id_app _ _))
    (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ jh jY L)
    (map_inv_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (gbar jh jY)) _ _
      (Iso.hom_inv_id_app _ _))
    h12.symm
    (squareMap_app_etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom Λ hΛ jY.toBase
      jh.immersion (restrictBaseι jh jY) (restrictBase jh jY).toBase
      (IsPullback.of_hasPullback jY.toBase jh.immersion)
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (jg jh jY).immersion).obj L))
    ((congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jh.immersion).map
      (tower_phi Λ hΛ jh jY jX K)).trans (Functor.map_comp _ _ _))

/-- For the tower `X̄ ⟶ Ȳ ⟶ Z̄`, on `D(X_étale, Λ)`: the isomorphism of [Stacks, Tag 0F7J] for
`f ≫ g` and `h` through `X̄`, followed by `Rh_!` of that for `f` and `g` through `X̄ ×_Z̄ Z`, is
the isomorphism for `f` and `g ≫ h` through `X̄`, followed by that for `g` and `h` through `Ȳ`,
read through the comparisons of [Stacks, Tag 0F7I]. -/
theorem towerUnbounded_core [CompactSpace jh.space] [CompactSpace (jgh jh jY).space]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompOverIso Λ hΛ (f ≫ g) h jh (jXZ jh jY jX)).hom.app K ≫
      (derivedLowerShriekUnbounded.{u, 0} h jh Λ).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₃₄ jh jY jX)).app K ≫
          (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g (jg jh jY) (jXW jh jY jX)).hom.app K ≫
          (derivedLowerShriekUnbounded.{u, 0} g (jg jh jY) Λ).map
            ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r₁₄ jh jY jX)).app K)) =
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₁₃ jh jY jX)).app K ≫
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f (g ≫ h) (jgh jh jY) jX).hom.app K ≫
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ g h jh jY).hom.app
        ((derivedLowerShriekUnbounded.{u, 0} f (jf₁ jh jY jX) Λ).obj K) := by
  have nat := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jY.toBase jh.toBase
    (jY.toBase ≫ jh.toBase) rfl).hom.naturality
      ((derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ (jgh jh jY) jX).hom.app K)
  have A := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ
    (overBar (jgh jh jY) jX).toBase (gbar jh jY) jh.toBase
    ((overBar (jgh jh jY) jX).toBase ≫ gbar jh jY) rfl (jgh jh jY).toBase rfl
    ((jXZ jh jY jX).toBase ≫ jh.toBase) rfl rfl
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      (overBar (jgh jh jY) jX).immersion).obj K)
  exact core_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jh.toBase) _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ jh (jXZ jh jY jX) K) rfl
    (towerUnbounded_Zbar Λ hΛ jh jY jX K)
    (derivedLowerShriekUnboundedHomUniv_ofFactorHom Λ jh.toBase (f ≫ g ≫ h) (c₁₃' jh jY jX)
      ((jXZ jh jY jX).toBase ≫ jh.toBase) rfl ((overBar jh (jXZ jh jY jX)).toBase ≫ jh.toBase)
      rfl (immersion_toBase (jfgh₁ jh jY jX)) (immersion_toBase (jfgh₃ jh jY jX)) K)
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ (jgh jh jY) jX K)
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ jh jY _) nat A (Iso.inv_hom_id_app _ _)

end TowerZbar

/-! ### [Stacks, Tag 0F7K] on `D(X_étale, Λ)` -/

section ThroughApp

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g]
  [LocallyOfFiniteType g]

/-- The isomorphism of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` for the compactifications
`X̄ ×_Ȳ Y` of `f` and `X̄` of `f ≫ g` is that of
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`. -/
lemma derivedLowerShriekUnboundedCompIso_restrictBase_compOver
    (jg : CompactificationOf (Over.mk g)) [CompactSpace jg.space]
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g (CompactificationOf.restrictBase jg jX) jg
      (CompactificationOf.compOver jg jX)).hom.app K =
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  rw [derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g _ jg _ jX K,
    derivedLowerShriekUnboundedCompactificationIsoUniv_self,
    derivedLowerShriekUnboundedCompactificationIsoUniv_self]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact (whisker_eq ((derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K)
    (CategoryTheory.Functor.map_id (derivedLowerShriekUnbounded.{u, 0} g jg Λ) _)).trans
      (Category.comp_id _)

end ThroughApp

section Tower

open CompactificationOf.Tower

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (h : Z ⟶ T) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace T] [QuasiSeparatedSpace T]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h]
  [LocallyOfFiniteType h]

/-- For a compactification `Z̄` of `h` and a compactification `Ȳ` of `Y` over `Z̄`, with `Rg_!`
and `R(h ∘ g)_!` computed through `Ȳ ×_Z̄ Z` and `Ȳ`, the two isomorphisms
`R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` on `D(X_étale, Λ)` built from [Stacks, Tag 0F7J] agree. -/
theorem derivedLowerShriekUnboundedCompIso_assoc_of_tower (jf : CompactificationOf (Over.mk f))
    (jfg : CompactificationOf (Over.mk (f ≫ g))) (jfgh : CompactificationOf (Over.mk (f ≫ g ≫ h)))
    (jh : CompactificationOf (Over.mk h)) (jY : CompactificationOf (Over.mk (g ≫ jh.immersion)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompIso Λ hΛ f (g ≫ h) jf (jgh jh jY) jfgh).hom.app K ≫
        (derivedLowerShriekUnboundedCompIso Λ hΛ g h (jg jh jY) jh (jgh jh jY)).hom.app
          ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) =
      (derivedLowerShriekUnboundedCompIso Λ hΛ (f ≫ g) h jfg jh jfgh).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} h jh Λ).map
          ((derivedLowerShriekUnboundedCompIso Λ hΛ f g jf (jg jh jY) jfg).hom.app K) := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : QuasiCompact (g ≫ h) := quasiCompact_of_compactSpace _
  have : QuasiCompact h := quasiCompact_of_compactSpace h
  have : QuasiCompact (f ≫ g ≫ h) := quasiCompact_of_compactSpace _
  have : QuasiCompact ((f ≫ g) ≫ h) := quasiCompact_of_compactSpace _
  have : CompactSpace jh.space := compactSpace_compactificationOf_space jh
  have : CompactSpace (jgh jh jY).space := compactSpace_compactificationOf_space (jgh jh jY)
  have : CompactSpace (jg jh jY).space := compactSpace_compactificationOf_space (jg jh jY)
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f (g ≫ h) (jgh jh jY)
  have nCO := (derivedLowerShriekUnboundedCompOverIso Λ hΛ g h jh jY).hom.naturality
    ((derivedLowerShriekUnboundedCompactificationIsoUniv f (jf₁ jh jY jX) jf Λ hΛ).hom.app K)
  have L1 := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f (g ≫ h) jf (jgh jh jY) jfgh jX K
  have L2 := derivedLowerShriekUnboundedCompIso_restrictBase_compOver Λ hΛ g h jh jY
    ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K)
  have R1 := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ (f ≫ g) h jfg jh jfgh
    (jXZ jh jY jX) K
  have R2 := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf (jg jh jY) jfg
    (jXW jh jY jX) K
  exact asm_chain (derivedLowerShriekUnbounded.{u, 0} h jh Λ)
    (derivedLowerShriekUnbounded.{u, 0} g (jg jh jY) Λ)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L1 L2 R1 R2 nCO
    (derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_target Λ hΛ (f ≫ g ≫ h) K
      (c₁₃ jh jY jX))
    (derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_comp_of_hom Λ hΛ (f ≫ g) K
      (c₃₄ jh jY jX))
    (derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_source Λ hΛ f K
      (r₁₄ jh jY jX))
    (towerUnbounded_core Λ hΛ jh jY jX K)
    (Iso.inv_hom_id_app (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ (c₁₃ jh jY jX) hΛ) K)

/-- **Stacks Project, Tag 0F7K, on unbounded derived categories.** Let `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ T` be separated morphisms of finite type of quasi-compact and quasi-separated
schemes, and let `Λ` be a torsion ring. Then the two isomorphisms
`R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` on `D(X_étale, Λ)` built from the isomorphisms of
[Stacks, Tag 0F7J] (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) agree: through
`R(h ∘ g)_! ∘ Rf_!` and through `Rh_! ∘ R(g ∘ f)_!`. Each of `Rf_!`, `Rg_!`, `Rh_!`, `R(g ∘ f)_!`,
`R(h ∘ g)_!` and `R(h ∘ g ∘ f)_!` is computed through an arbitrary compactification.

The proof follows [Stacks, Tag 0F7K]: choosing a compactification `Ȳ` of `Y` over the
compactification `Z̄` of `Z` (and of `X` over `Ȳ`) the statement is
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_assoc_of_tower`, and the isomorphisms
of [Stacks, Tag 0F7J] do not depend on the compactifications
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_second` and its first and
third slot companions). The case of `D⁺_tors(X_étale, Λ)` for an arbitrary ring is
`Stacks.EtaleCohomology.derivedLowerShriekCompIso_assoc`. -/
@[stacks 0F7K "unbounded D(X_et, Λ), Λ torsion"]
theorem derivedLowerShriekUnboundedCompIso_assoc (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (jh : CompactificationOf (Over.mk h))
    (jfg : CompactificationOf (Over.mk (f ≫ g))) (jgh : CompactificationOf (Over.mk (g ≫ h)))
    (jfgh : CompactificationOf (Over.mk (f ≫ g ≫ h)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompIso Λ hΛ f (g ≫ h) jf jgh jfgh).hom.app K ≫
        (derivedLowerShriekUnboundedCompIso Λ hΛ g h jg jh jgh).hom.app
          ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) =
      (derivedLowerShriekUnboundedCompIso Λ hΛ (f ≫ g) h jfg jh jfgh).hom.app K ≫
        (derivedLowerShriekUnbounded.{u, 0} h jh Λ).map
          ((derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg jfg).hom.app K) := by
  have : QuasiCompact (g ≫ h) := quasiCompact_of_compactSpace _
  obtain ⟨jY⟩ := nonempty_compactificationOf_comp_immersion g h jh
  let N := (derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K
  let jgh₀ := CompactificationOf.compOver jh jY
  let jg₀ := CompactificationOf.restrictBase jh jY
  have S1 := derivedLowerShriekUnboundedCompIso_hom_app_second Λ hΛ f (g ≫ h) jf jgh₀ jgh jfgh K
  have S2 := derivedLowerShriekUnboundedCompIso_hom_app_second Λ hΛ f g jf jg₀ jg jfg K
  have T3 := derivedLowerShriekUnboundedCompIso_hom_app_third Λ hΛ g h jg jh jgh₀ jgh N
  have F1 := derivedLowerShriekUnboundedCompIso_hom_app_first Λ hΛ g h jg₀ jh jgh₀ jg N
  have II : (derivedLowerShriekUnboundedCompactificationIsoUniv (g ≫ h) jgh₀ jgh Λ hΛ).hom.app N ≫
      (derivedLowerShriekUnboundedCompactificationIsoUniv (g ≫ h) jgh jgh₀ Λ hΛ).hom.app N =
        𝟙 _ := by
    rw [← derivedLowerShriekUnboundedCompactificationIsoUniv_symm Λ hΛ (g ≫ h) jgh₀ jgh]
    exact Iso.hom_inv_id_app _ _
  exact assoc_final_chain (derivedLowerShriekUnbounded.{u, 0} h jh Λ) _ _ _ _ _ _ _ _ _ _ _ S1 T3
    F1 S2 (derivedLowerShriekUnboundedCompIso_assoc_of_tower Λ hΛ f g h jf jfg jfgh jh jY K) II

end Tower

end Stacks.EtaleCohomology

end
