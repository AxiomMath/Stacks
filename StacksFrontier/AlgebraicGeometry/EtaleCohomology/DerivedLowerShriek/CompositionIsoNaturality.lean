module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactificationMorphisms
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeTorsion
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroValues
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroRestrict
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso

/-!
# The isomorphism of [Stacks, Tag 0F7J] does not depend on the auxiliary compactification

The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of `Stacks.EtaleCohomology.derivedLowerShriekCompIso`
is computed through a compactification `X ⟶ X̄` of `X` over the compactification `Ȳ` of `Y`
chosen by Nagata's theorem. This file proves that every such compactification gives the same
isomorphism, as the source implicitly asserts.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageComp_assoc`: the composition
  isomorphisms of derived direct images are associative.
* `Stacks.EtaleCohomology.eq_of_etaleModuleDerivedInverseImagePlus_map_eq`: isomorphisms into an
  extension by zero along an open immersion are determined by their restrictions to the open.
* `Stacks.EtaleCohomology.derivedLowerShriekCompOverIso_naturality`: the isomorphism of
  `derivedLowerShriekCompOverIso` is natural in morphisms of the auxiliary compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekCompIso_eq_compOver`: the isomorphism of
  [Stacks, Tag 0F7J] through an arbitrary auxiliary compactification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {X₀ : Over S}

/-- A morphism of compactifications from a morphism of ambient schemes compatible with the open
immersions and with the structure morphisms. -/
def homOfSpaceMap (j k : CompactificationOf X₀) (p : j.space ⟶ k.space)
    (h₁ : j.immersion ≫ p = k.immersion) (h₂ : p ≫ k.toBase = j.toBase) : j ⟶ k :=
  ObjectProperty.homMk (StructuredArrow.homMk (Over.homMk p h₂) (Over.OverMorphism.ext h₁))

/-- The morphism of ambient schemes of `homOfSpaceMap j k p h₁ h₂` is `p`. -/
@[simp]
lemma homOfSpaceMap_map (j k : CompactificationOf X₀) (p : j.space ⟶ k.space)
    (h₁ : j.immersion ≫ p = k.immersion) (h₂ : p ≫ k.toBase = j.toBase) :
    Hom.map (homOfSpaceMap j k p h₁ h₂) = p := rfl

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  {jX jX' : CompactificationOf (Over.mk (f ≫ jg.immersion))}

/-- The open immersion of the induced compactification over `Y`, followed by the projection to
`X̄`, is the open immersion of `X̄`. -/
@[reassoc (attr := simp)]
lemma restrictBase_immersion_restrictBaseι (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    (restrictBase jg jX).immersion ≫ restrictBaseι jg jX = jX.immersion := by
  simp [restrictBase, restrictBaseι]

/-- A morphism of compactifications of `X` over `Ȳ` induces a morphism of the compactifications
`X ⟶ X̄` over `Z`. -/
def compOverHom (φ : jX ⟶ jX') : compOver jg jX ⟶ compOver jg jX' :=
  homOfSpaceMap _ _ (Hom.map (j := jX) (k := jX') φ)
    (by
      change ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX) ≫ Hom.map φ =
        (restrictBase jg jX').immersion ≫ restrictBaseι jg jX'
      rw [restrictBase_immersion_restrictBaseι, restrictBase_immersion_restrictBaseι,
        immersion_comp_map])
    (by
      change Hom.map φ ≫ jX'.toBase ≫ jg.toBase = jX.toBase ≫ jg.toBase
      rw [← Category.assoc, map_comp_toBase])

/-- A morphism of compactifications of `X` over `Ȳ` induces a morphism of the compactifications
`overBar` of `X` over `Ȳ`. -/
def overBarHom (φ : jX ⟶ jX') : overBar jg jX ⟶ overBar jg jX' :=
  homOfSpaceMap _ _ (Hom.map (j := jX) (k := jX') φ)
    (by
      change ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX) ≫ Hom.map φ =
        (restrictBase jg jX').immersion ≫ restrictBaseι jg jX'
      rw [restrictBase_immersion_restrictBaseι, restrictBase_immersion_restrictBaseι,
        immersion_comp_map])
    (by
      change Hom.map φ ≫ jX'.toBase = jX.toBase
      rw [map_comp_toBase])

/-- A morphism of compactifications of `X` over `Ȳ` induces a morphism of the induced
compactifications of `X` over `Y`. -/
abbrev restrictBaseHom (φ : jX ⟶ jX') : restrictBase jg jX ⟶ restrictBase jg jX' :=
  baseChangeHom (isPullback_id_comp_immersion jg) φ

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-! ### Associativity of the composition of derived direct images -/

section Assoc

/-- The composition isomorphism of derived direct images is the composition comparison of
[Stacks, Tag 05T2] after the invariance comparison of the underived composition isomorphism. -/
lemma etaleModuleDerivedDirectImageComp_hom_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom =
      (Functor.rightDerivedFunctorPlusNatIso
          (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv ≫
        Functor.rightDerivedFunctorPlusComp _ _ := by
  dsimp only [etaleModuleDerivedDirectImageComp, rightDerivedFunctorPlusCompIsoOfIso]
  simp only [rightDerivedFunctorPlusIsoOfCompIso_eq, Iso.trans_hom, Iso.symm_hom,
    Functor.rightDerivedFunctorPlusCompIso_hom]

/-- **The composition comparisons of derived direct images are associative**, in the form of
the composition comparison of [Stacks, Tag 05T2] after the invariance comparison: along
`T ⟶ X ⟶ Y ⟶ Z`, taking `R(fgh)_*` apart through `R(fg)_* ⋙ Rh_*` or through
`Rf_* ⋙ R(gh)_*` gives the same map to `Rf_* ⋙ Rg_* ⋙ Rh_*`. -/
theorem rightDerivedFunctorPlusComp_etaleModuleDirectImageComp_assoc {T X Y Z : Scheme.{u}}
    (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z)
    (hgh : gh = g ≫ h) (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    ((Functor.rightDerivedFunctorPlusNatIso
          (etaleModuleDirectImageComp.{u, 0} Λ fg h fgh h₁)).inv ≫
        Functor.rightDerivedFunctorPlusComp _ _) ≫
      Functor.whiskerRight ((Functor.rightDerivedFunctorPlusNatIso
          (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg)).inv ≫
        Functor.rightDerivedFunctorPlusComp _ _) (etaleModuleDerivedDirectImage.{u, 0} Λ h) =
      ((Functor.rightDerivedFunctorPlusNatIso
          (etaleModuleDirectImageComp.{u, 0} Λ f gh fgh h₂)).inv ≫
        Functor.rightDerivedFunctorPlusComp _ _) ≫
      Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ f)
        ((Functor.rightDerivedFunctorPlusNatIso
          (etaleModuleDirectImageComp.{u, 0} Λ g h gh hgh)).inv ≫
        Functor.rightDerivedFunctorPlusComp _ _) := by
  have hc : (etaleModuleDirectImageComp.{u, 0} Λ fg h fgh h₁).symm.hom ≫
      Functor.whiskerRight (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg).symm.hom
        (etaleModuleDirectImage.{u, 0} Λ h) =
      (etaleModuleDirectImageComp.{u, 0} Λ f gh fgh h₂).symm.hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ f)
          (etaleModuleDirectImageComp.{u, 0} Λ g h gh hgh).inv := by
    ext F : 2
    exact smallEtalePushforwardComp'_inv_app_cocycle f g h fg hfg gh hgh fgh h₁ h₂
      (ModuleCat.{u + 1} Λ) F
  have := Functor.rightDerivedFunctorPlusComp_paste _ _ _ _ hc
  simpa only [Functor.rightDerivedFunctorPlusNatIso_symm, Iso.symm_hom, Category.assoc] using this

/-- **The composition isomorphisms of derived direct images are associative**: along
`T ⟶ X ⟶ Y ⟶ Z`, taking `R(fgh)_*` apart through `R(fg)_* ⋙ Rh_*` or through
`Rf_* ⋙ R(gh)_*` gives the same isomorphism with `Rf_* ⋙ Rg_* ⋙ Rh_*`. -/
theorem etaleModuleDerivedDirectImageComp_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ fg h fgh h₁).hom ≫
        Functor.whiskerRight (etaleModuleDerivedDirectImageComp.{u, 0} Λ f g fg hfg).hom
          (etaleModuleDerivedDirectImage.{u, 0} Λ h) =
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ f gh fgh h₂).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ f)
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ g h gh hgh).hom := by
  simp only [etaleModuleDerivedDirectImageComp_hom_eq]
  exact rightDerivedFunctorPlusComp_etaleModuleDirectImageComp_assoc Λ f g h fg hfg gh hgh fgh
    h₁ h₂

end Assoc

/-! ### Maps into an extension by zero are determined over the open -/

section Restriction

variable {Y Yb : Scheme.{u}} (i : Y ⟶ Yb) [IsOpenImmersion i]

/-- **Maps out of an extension by zero along an open immersion are determined by their
restrictions to the open**: the unit of `Ri_! ⊣ i^{-1}` is invertible. -/
theorem eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source
    {B : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)}
    {A : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Yb)}
    (α β : (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj B ⟶ A)
    (h : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map α =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map β) : α = β := by
  let adj := etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i
  have hr : (etaleModuleDerivedRestriction.{u, 0} Λ i).map α =
      (etaleModuleDerivedRestriction.{u, 0} Λ i).map β := by
    have nα := (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.naturality α
    have nβ := (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.naturality β
    rw [← cancel_mono ((etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.app A), nα, nβ,
      h]
  apply (adj.homEquiv B A).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hr]

/-- **Isomorphisms into an extension by zero along an open immersion are determined by their
restrictions to the open.** -/
theorem eq_of_etaleModuleDerivedInverseImagePlus_map_eq
    {B : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)}
    {A : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Yb)}
    (α β : A ⟶ (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj B) [IsIso α] [IsIso β]
    (h : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map α =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map β) : α = β := by
  have : inv α = inv β := eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source Λ i _ _
    (by rw [Functor.map_inv, Functor.map_inv]; exact IsIso.inv_eq_inv.mpr h)
  exact IsIso.inv_eq_inv.mp this

/-- **Maps into an extension by zero along an open immersion, one of them invertible, are
determined by their restrictions to the open.** -/
theorem eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_isIso
    {B : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)}
    {A : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Yb)}
    (α β : A ⟶ (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj B) [IsIso α]
    (h : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map α =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map β) : α = β := by
  have : inv α ≫ β = 𝟙 _ := eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source Λ i _ _
    (by rw [Functor.map_comp, Functor.map_inv, ← h, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id])
  rw [← Category.id_comp β, ← IsIso.hom_inv_id α, Category.assoc, this, Category.comp_id]

end Restriction

/-! ### Cancellation patterns over plain objects -/

section Chain

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)

/-- The cancellation pattern of
`Stacks.EtaleCohomology.derivedLowerShriekCompOverIso_naturality`, over plain objects. -/
lemma compOver_naturality_chain {A₀ A₁ A₂ : D} {P₀ P₁ P₂ Q Q' : C} (t : A₀ ⟶ A₁)
    (ibc : A₁ ⟶ A₂) (bc : A₂ ⟶ A₁) (e : A₂ ⟶ G.obj P₂) (ψ : P₂ ⟶ Q) (eN : A₀ ⟶ G.obj P₀)
    (ψ' : P₀ ⟶ Q') (r : Q' ⟶ Q) (tθ : P₀ ⟶ P₁) (ibb : P₁ ⟶ P₂) (bb : P₂ ⟶ P₁)
    (eM : A₁ ⟶ G.obj P₁)
    (hY : (tθ ≫ ibb) ≫ ψ = ψ' ≫ r) (hn : t ≫ eM = eN ≫ G.map tθ)
    (hA : e ≫ G.map bb = bc ≫ eM) (hbc : ibc ≫ bc = 𝟙 _) (hbb : bb ≫ ibb = 𝟙 _) :
    (t ≫ ibc) ≫ e ≫ G.map ψ = (eN ≫ G.map ψ') ≫ G.map r := by
  have hA' : ibc ≫ e = eM ≫ G.map ibb := by
    calc ibc ≫ e = ibc ≫ e ≫ G.map (bb ≫ ibb) := by rw [hbb, G.map_id, Category.comp_id]
      _ = ibc ≫ bc ≫ eM ≫ G.map ibb := by rw [G.map_comp, reassoc_of% hA]
      _ = eM ≫ G.map ibb := by rw [reassoc_of% hbc]
  rw [Category.assoc, reassoc_of% hA', reassoc_of% hn, Category.assoc, ← G.map_comp,
    ← G.map_comp, ← G.map_comp, ← Category.assoc tθ, hY]

/-- `p ≫ F (c ≫ a ≫ 𝟙) = (p ≫ F c) ≫ F a`, over plain objects. -/
lemma comp_map_comp_comp_id (F : C ⥤ D) {X : D} {A B B' : C} (p : X ⟶ F.obj A) (c : A ⟶ B)
    (a : B ⟶ B') : p ≫ F.map (c ≫ a ≫ 𝟙 B') = (p ≫ F.map c) ≫ F.map a := by
  simp

/-- The cancellation pattern of
`Stacks.EtaleCohomology.derivedLowerShriekRestrictBaseIso_naturality`, over plain objects. -/
lemma restrict_naturality_chain {A B P P' : C} {Q Q' W W' : D} (H : A ⟶ B) (Ψ : B ⟶ P)
    (Ψ' : A ⟶ P') (iR : P' ⟶ P) (ε₁ : G.obj P ⟶ Q) (ε₂ : G.obj P' ⟶ Q') (R : Q' ⟶ Q)
    (cube₁ : G.obj B ⟶ W) (cube₂ : G.obj A ⟶ W') (ι₁ : W ⟶ Q) (ι₂ : W' ⟶ Q') (R' : W' ⟶ W)
    (c1 : G.map Ψ ≫ ε₁ = cube₁ ≫ ι₁) (c2 : G.map Ψ' ≫ ε₂ = cube₂ ≫ ι₂)
    (hε : G.map iR ≫ ε₁ = ε₂ ≫ R) (hN : G.map H ≫ cube₁ = cube₂ ≫ R')
    (hι : ι₂ ≫ R = R' ≫ ι₁) :
    G.map (H ≫ Ψ) ≫ ε₁ = G.map (Ψ' ≫ iR) ≫ ε₁ := by
  rw [G.map_comp, G.map_comp, Category.assoc, Category.assoc, c1, reassoc_of% hN, ← hι, hε,
    reassoc_of% c2]

end Chain

/-! ### Naturality of the composition isomorphism in the auxiliary compactification -/

section Naturality

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  {jX jX' : CompactificationOf (Over.mk (f ≫ jg.immersion))} (φ : jX ⟶ jX')

/-- The square `X = X ×_{X̄} (X̄ ×_Ȳ Y)` of the open immersions of `restrictBase` and `overBar`. -/
theorem isPullback_restrictBase_overBar (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    IsPullback (𝟙 X) (CompactificationOf.restrictBase jg jX).immersion
      (CompactificationOf.overBar jg jX).immersion (CompactificationOf.restrictBaseι jg jX) := by
  have h := CompactificationOf.isPullback_baseChange
    (CompactificationOf.isPullback_id_comp_immersion jg) jX
  rw [← CompactificationOf.restrictBase_immersion_restrictBaseι jg jX] at h
  exact h

/-- `b^{-1} (b ∘ a)_! ≅ a_!` for `a = X ⟶ X̄ ×_Ȳ Y` and `b = X̄ ×_Ȳ Y ⟶ X̄` is the isomorphism of
[Stacks, Tag 03S6] for the cartesian square `X = X ×_{X̄} (X̄ ×_Ȳ Y)`, read through
`(𝟙_X)^{-1} ≅ 𝟭`. -/
theorem restrictBaseExtensionByZeroIso_hom_eq_cube
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    (restrictBaseExtensionByZeroIso Λ jg jX).hom =
      (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_restrictBase_overBar jg jX)).inv ≫
        Functor.whiskerRight (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom _ ≫
        (Functor.leftUnitor _).hom := by
  have := CompactificationOf.isOpenImmersion_restrictBaseι jg jX
  rw [restrictBaseExtensionByZeroIso_eq]
  exact etaleModuleDerivedExtensionByZeroRestrictIso_hom Λ
    (CompactificationOf.restrictBase jg jX).immersion
    (CompactificationOf.restrictBaseι jg jX) (isPullback_restrictBase_overBar jg jX)

/-- **`Ψ` restricted to `Y` is the base change map of the cube of `overBar` and
`restrictBase`**, read through `(𝟙_X)^{-1} ≅ 𝟭`. -/
theorem derivedLowerShriekRestrictBaseIso_restrict_cube
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
        ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app
        ((derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ).obj K.obj) =
    (derivedLowerShriekBaseChangeCube Λ (CompactificationOf.overBar jg jX)
        (CompactificationOf.restrictBase jg jX) (CompactificationOf.restrictBaseι jg jX)
        (isPullback_restrictBase_overBar jg jX) pullback.condition.symm).app K.obj ≫
      (derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj) := by
  rw [derivedLowerShriekRestrictBaseIso_restrict, restrictBaseExtensionByZeroIso_hom_eq_cube]
  simp only [derivedLowerShriekBaseChangeCube, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact comp_map_comp_comp_id
    (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase) _ _ _

/-- **`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!` is natural in the compactification of `X` over `Ȳ`**: along a
morphism `φ : jX ⟶ jX'`, the comparisons of [Stacks, Tag 0F7I] for `f ≫ i` and for `f`
intertwine the two isomorphisms. Both sides are isomorphisms into an extension by zero along
`i`, so it suffices to compare them over `Y`, where `Ψ` is the base change map of a cube and the
statement is the naturality of those maps. -/
theorem derivedLowerShriekRestrictBaseIso_naturality
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekHom Λ (CompactificationOf.overBarHom jg φ)).app K.obj ≫
        (derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K =
      (derivedLowerShriekRestrictBaseIso Λ jg jX').hom.app K ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map
          ((derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).app K.obj) := by
  have := isIso_derivedLowerShriekHom_app Λ (CompactificationOf.overBarHom jg φ) K.obj K.property
  have := isIso_derivedLowerShriekHom_app Λ (CompactificationOf.restrictBaseHom jg φ) K.obj
    K.property
  refine eq_of_etaleModuleDerivedInverseImagePlus_map_eq Λ jg.immersion _ _ ?_
  let ε := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom
  rw [← cancel_mono (ε.app ((derivedLowerShriek.{u, 0} f
    (CompactificationOf.restrictBase jg jX) Λ).obj K.obj))]
  have hε := ε.naturality ((derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).app
    K.obj)
  have hN := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ
    (CompactificationOf.overBarHom jg φ) (CompactificationOf.restrictBaseHom jg φ)
    (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBaseι jg jX')
    (isPullback_restrictBase_overBar jg jX) (isPullback_restrictBase_overBar jg jX')
    (CompactificationOf.baseChangeHom_map_fst _ φ) pullback.condition.symm
    pullback.condition.symm) K.obj
  have hι := (derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).naturality
    ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj)
  exact restrict_naturality_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion)
    _ _ _ _ _ _ _ _ _ _ _ _ (derivedLowerShriekRestrictBaseIso_restrict_cube Λ jg jX K)
    (derivedLowerShriekRestrictBaseIso_restrict_cube Λ jg jX' K) hε hN hι

/-- **The isomorphism of `derivedLowerShriekCompOverIso` is natural in the compactification of
`X` over `Ȳ`**: along a morphism `φ : jX ⟶ jX'`, the comparisons of [Stacks, Tag 0F7I] for
`f ≫ g` and for `f` intertwine the two isomorphisms `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!`. -/
theorem derivedLowerShriekCompOverIso_naturality
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekHom Λ (CompactificationOf.compOverHom jg φ)).app K.obj ≫
        (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K =
      (derivedLowerShriekCompOverIso Λ f g jg jX').hom.app K ≫
        (derivedLowerShriek.{u, 0} g jg Λ).map
          ((derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).app K.obj) := by
  let M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ jX.space) :=
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ
      (CompactificationOf.overBar jg jX).immersion).obj K.obj
  let Rg := etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase
  let Rφ := etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map φ)
  let e := etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl
  let e' := etaleModuleDerivedDirectImageComp.{u, 0} Λ jX'.toBase jg.toBase
    (jX'.toBase ≫ jg.toBase) rfl
  let bb := derivedBaseComparison Λ (CompactificationOf.overBarHom jg φ)
  let bc := derivedBaseComparison Λ (CompactificationOf.compOverHom jg φ)
  let θ := derivedRefinementComparison Λ (CompactificationOf.overBarHom jg φ)
  -- associativity of the composition isomorphisms along `X̄ ⟶ X̄' ⟶ Ȳ ⟶ Z`
  have hA := congrArg (fun t => NatTrans.app t M)
    (rightDerivedFunctorPlusComp_etaleModuleDirectImageComp_assoc Λ
      (CompactificationOf.Hom.map φ) jX'.toBase jg.toBase jX.toBase
      (CompactificationOf.map_comp_toBase φ).symm (jX'.toBase ≫ jg.toBase) rfl
      (jX.toBase ≫ jg.toBase) rfl
      (by rw [← Category.assoc, CompactificationOf.map_comp_toBase]))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA
  have hbc : (inv bc).app _ ≫ bc.app _ = 𝟙 _ := NatTrans.congr_app (IsIso.inv_hom_id bc)
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
      (CompactificationOf.compOver jg jX).immersion).obj K.obj)
  have hbb : bb.app M ≫ (inv bb).app M = 𝟙 _ := NatTrans.congr_app (IsIso.hom_inv_id bb) M
  have hY := derivedLowerShriekRestrictBaseIso_naturality Λ jg φ K
  have hn := e'.hom.naturality (θ.app K.obj)
  rw [derivedLowerShriekCompOverIso_hom_app, derivedLowerShriekCompOverIso_hom_app,
    derivedLowerShriekHom_app, etaleModuleDerivedDirectImageComp_hom_eq,
    etaleModuleDerivedDirectImageComp_hom_eq]
  rw [derivedLowerShriekHom_app] at hY
  rw [etaleModuleDerivedDirectImageComp_hom_eq] at hn
  exact compOver_naturality_chain Rg _ _ _ _ _ _ _ _ _ _ _ _ hY hn hA hbc hbb

end Naturality

/-! ### Independence of the auxiliary compactification -/

section Independence

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
  (j : CompactificationOf (Over.mk (f ≫ g)))

/-- The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` computed through a compactification `jX` of `X`
over `Ȳ`: the isomorphism of `derivedLowerShriekCompOverIso`, transported to the compactifications
`j` and `jf` by the comparisons of [Stacks, Tag 0F7I]. -/
def derivedLowerShriekCompIsoThrough (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} (f ≫ g) j Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f jf Λ ⋙
        derivedLowerShriek.{u, 0} g jg Λ :=
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX) Λ ≪≫
    derivedLowerShriekCompOverIso Λ f g jg jX ≪≫
    Functor.isoWhiskerRight
      (derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX) jf Λ)
      (derivedLowerShriek.{u, 0} g jg Λ)

omit [QuasiSeparatedSpace X] in
/-- Along a morphism of auxiliary compactifications the two isomorphisms agree. -/
theorem derivedLowerShriekCompIsoThrough_eq_of_hom
    {jX jX' : CompactificationOf (Over.mk (f ≫ jg.immersion))} (φ : jX ⟶ jX') :
    derivedLowerShriekCompIsoThrough Λ f g jf jg j jX =
      derivedLowerShriekCompIsoThrough Λ f g jf jg j jX' := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have hC : derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX) Λ =
      derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX') Λ ≪≫
        derivedLowerShriekHomIso Λ (CompactificationOf.compOverHom jg φ) := by
    rw [← derivedLowerShriekCompactificationIso_of_hom,
      derivedLowerShriekCompactificationIso_trans]
  have hR : derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX) jf Λ =
      (derivedLowerShriekHomIso Λ (CompactificationOf.restrictBaseHom jg φ)).symm ≪≫
        derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX') jf Λ := by
    rw [← derivedLowerShriekCompactificationIso_of_hom, derivedLowerShriekCompactificationIso_symm,
      derivedLowerShriekCompactificationIso_trans]
  dsimp only [derivedLowerShriekCompIsoThrough]
  rw [hC, hR]
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  have h := derivedLowerShriekCompOverIso_naturality Λ jg φ K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, derivedLowerShriekHomIso_hom_app, Category.assoc,
    Functor.map_comp]
  have hinv : (derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).app K.obj ≫
      (derivedLowerShriekHomIso Λ (CompactificationOf.restrictBaseHom jg φ)).inv.app K = 𝟙 _ :=
    (derivedLowerShriekHomIso Λ (CompactificationOf.restrictBaseHom jg φ)).hom_inv_id_app K
  have e1 : (derivedLowerShriek.{u, 0} g jg Λ).map
        ((derivedLowerShriekHom Λ (CompactificationOf.restrictBaseHom jg φ)).app K.obj) ≫
      (derivedLowerShriek.{u, 0} g jg Λ).map
        ((derivedLowerShriekHomIso Λ (CompactificationOf.restrictBaseHom jg φ)).inv.app K) =
      𝟙 _ := by
    rw [← Functor.map_comp, hinv, CategoryTheory.Functor.map_id]
  rw [reassoc_of% h]
  congr 2
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker e1 _).trans (Category.id_comp _))

/-- **The isomorphism of [Stacks, Tag 0F7J] through an arbitrary auxiliary compactification**:
`Stacks.EtaleCohomology.derivedLowerShriekCompIso` is computed through any compactification `jX`
of `X` over the compactification `Ȳ` of `Y`, not only the one chosen by Nagata's theorem. -/
theorem derivedLowerShriekCompIso_eq_compOver
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    derivedLowerShriekCompIso Λ f g jf jg j =
      derivedLowerShriekCompIsoThrough Λ f g jf jg j jX := by
  have : UniversallyClosed jg.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact jg.toBase := instQuasiCompactOfUniversallyClosed jg.toBase
  have : IsSeparated jg.toBase := IsProper.toIsSeparated
  have : QuasiSeparated jg.toBase := IsSeparated.instQuasiSeparated jg.toBase
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  have : QuasiSeparatedSpace jg.space := quasiSeparatedSpace_of_quasiSeparated jg.toBase
  have : QuasiCompact (f ≫ jg.immersion) := quasiCompact_of_compactSpace _
  let jX₀ := (nonempty_compactificationOf_comp_immersion f g jg).some
  show derivedLowerShriekCompIsoThrough Λ f g jf jg j jX₀ = _
  exact (derivedLowerShriekCompIsoThrough_eq_of_hom Λ f g jf jg j
    (IsCofiltered.minToLeft jX₀ jX)).symm.trans
      (derivedLowerShriekCompIsoThrough_eq_of_hom Λ f g jf jg j (IsCofiltered.minToRight jX₀ jX))

end Independence

end Stacks.EtaleCohomology

end
