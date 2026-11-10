module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence

/-!
# Flat base change for derived global sections over an affine base

Let `f : X ⟶ Spec A` be flat, quasi-compact and quasi-separated, let `φ : A ⟶ B` be a ring map
and let `X' = X ×_{Spec A} Spec B`, with projections `g : X' ⟶ X` and `f' : X' ⟶ Spec B`. For
`F ∈ D_QCoh(𝒪_X)` the pullback map `RΓ(X, F) ⟶ RΓ(X', Lg^* F)` of
`AlgebraicGeometry.LerayOver.pullbackSectionsMap` has an adjoint
`RΓ(X, F) ⊗ᴸ_A B ⟶ RΓ(X', Lg^* F)`, and this adjoint is an isomorphism.

## Main results

* `AlgebraicGeometry.LerayOver.lerayIso_comp_structure` and
  `AlgebraicGeometry.LerayOver.lerayIso_structure_comp`: the Leray isomorphism over `φ` along a
  composite `X' ⟶ X ⟶ Spec A` or `X' ⟶ Spec B ⟶ Spec A` is the composite of the Leray
  isomorphisms along the two factors, up to the composition isomorphism of derived direct images.
* `AlgebraicGeometry.LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap`: **flat base
  change for derived global sections over an affine base.**

## Implementation notes

The Leray isomorphism of a scheme over `A` with itself is the instance of
`AlgebraicGeometry.LerayOver.lerayIso` along the identity of `A`, read through
`AlgebraicGeometry.restrictScalarsIdDerivedIso`. Every chase is carried out over variables or
with each library equation instantiated whole, because the derived functors are abbreviations the
kernel must not unfold.

The standard model of the derived category is used throughout; the locally small instances and
the site-module abelian instance are switched off so that every derived category below is the one
the Leray isomorphisms are stated at.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPullback derivedAdjunction derivedPushforwardUnit
    derivedPushforwardCompIso)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.LerayOver

/-! ### Derived restriction of scalars along the identity -/

section RestrictScalarsId

variable {R : Type u} [CommRing R]

/-- Derived restriction of scalars along the identity, read on the homotopy category: at the
class of a complex it is the localization of the degreewise identification. -/
theorem restrictScalarsIdDerivedIso_hom_app_comp_factorsh_quotient
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrictScalarsIdDerivedIso (RingHom.id R) rfl).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((restrictScalarsIdComplexIso (RingHom.id R) rfl).inv.app C) ≫
        ((ModuleCat.restrictScalars (RingHom.id R)).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app C) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, ← Category.assoc,
    ← (restrictScalarsIdDerivedIso (RingHom.id R) rfl).hom.naturality,
    Functor.id_map, Category.assoc, restrictScalarsIdDerivedIso_hom_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Category.assoc, ← Category.assoc,
    ← DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp]

/-- `restrictScalarsIdDerivedIso_hom_app_comp_factorsh_quotient` at an arbitrary object of the
homotopy category. -/
theorem restrictScalarsIdDerivedIso_hom_app_comp_factorsh
    (M : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :
    (restrictScalarsIdDerivedIso (RingHom.id R) rfl).hom.app (DerivedCategory.Qh.obj M) ≫
      (ModuleCat.restrictScalars (RingHom.id R)).mapDerivedCategoryFactorsh.hom.app M =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((restrictScalarsIdComplexIso (RingHom.id R) rfl).inv.app M.as) ≫
        ((ModuleCat.restrictScalars (RingHom.id R)).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app M.as) :=
  restrictScalarsIdDerivedIso_hom_app_comp_factorsh_quotient M.as

end RestrictScalarsId

/-! ### A chase in an arbitrary category -/

/-- In an arbitrary category, `r ≫ F = z` may be substituted for `z` inside the composite
`y₁ ≫ y₂ ≫ z ≫ y₃ ≫ y₄`. -/
private theorem chase₅ {𝒞 : Type*} [Category 𝒞] {P Q₁ Q₂ Q₃ Q₄ Q₅ V : 𝒞}
    (x : P ⟶ V) (y₁ : P ⟶ Q₁) (y₂ : Q₁ ⟶ Q₂) (r : Q₂ ⟶ Q₃) (F : Q₃ ⟶ Q₄) (z : Q₂ ⟶ Q₄)
    (y₃ : Q₄ ⟶ Q₅) (y₄ : Q₅ ⟶ V) (hρ : r ≫ F = z) (h : x = y₁ ≫ y₂ ≫ z ≫ y₃ ≫ y₄) :
    x = y₁ ≫ y₂ ≫ r ≫ F ≫ y₃ ≫ y₄ := by
  rw [h, ← hρ, Category.assoc]

private theorem map_comp₃_eq_map_comp₅ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {P Q₁ Q₂ Q₁' Q₂' Q₃' Q₄' V : 𝒞} (a : P ⟶ Q₁) (b : Q₁ ⟶ Q₂) (c : Q₂ ⟶ V) (a' : P ⟶ Q₁')
    (b' : Q₁' ⟶ Q₂') (z : Q₂' ⟶ Q₃') (d : Q₃' ⟶ Q₄') (e : Q₄' ⟶ V)
    (h : a ≫ b ≫ c = a' ≫ b' ≫ z ≫ d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map z ≫ F.map d ≫ F.map e := by
  simp only [← F.map_comp, h]

private theorem chase₇ {𝒞 : Type*} [Category 𝒞] {P X₁ X₂ X₃ Q₀ Q₁ Q₂ Q₃ Y₁ Y₂ V : 𝒞}
    (FX : P ⟶ X₁) (l₁ : X₁ ⟶ X₂) (l₂ : X₂ ⟶ X₃) (N' : X₃ ⟶ V)
    (Gρ : P ⟶ Q₀) (GFh : Q₀ ⟶ Q₁) (Gm₁ : Q₁ ⟶ Q₂) (Gm₂ : Q₂ ⟶ Q₃) (FY : Q₃ ⟶ Y₁)
    (n₁ : Y₁ ⟶ Y₂) (n₂ : Y₂ ⟶ V) (Gz : P ⟶ Q₁) (a : X₁ ⟶ Y₁)
    (h₁ : Gρ ≫ GFh = Gz) (h₂ : Gz ≫ Gm₁ ≫ Gm₂ ≫ FY = FX ≫ a)
    (h₃ : l₁ ≫ l₂ ≫ N' = a ≫ n₁ ≫ n₂) :
    FX ≫ l₁ ≫ l₂ ≫ N' = Gρ ≫ GFh ≫ Gm₁ ≫ Gm₂ ≫ FY ≫ n₁ ≫ n₂ := by
  rw [h₃, reassoc_of% h₁, reassoc_of% h₂]

private theorem map_comp₃_eq_map_comp₃ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {P Q₁ Q₂ Q₁' Q₂' V : 𝒞} (a : P ⟶ Q₁) (b : Q₁ ⟶ Q₂) (c : Q₂ ⟶ V) (a' : P ⟶ Q₁')
    (b' : Q₁' ⟶ Q₂') (c' : Q₂' ⟶ V) (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
  simp only [← F.map_comp, h]

/-- The factorization of an exact functor on derived categories through homotopy categories is
natural, with three morphisms composed. -/
private theorem mapDerivedCategoryFactorsh_naturality₃ {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X₀ X₁ X₂ X₃ : HomotopyCategory C₁ (ComplexShape.up ℤ)} (x₁ : X₀ ⟶ X₁) (x₂ : X₁ ⟶ X₂)
    (x₃ : X₂ ⟶ X₃) :
    F.mapDerivedCategory.map (DerivedCategory.Qh.map x₁) ≫
        F.mapDerivedCategory.map (DerivedCategory.Qh.map x₂) ≫
        F.mapDerivedCategory.map (DerivedCategory.Qh.map x₃) ≫
        F.mapDerivedCategoryFactorsh.hom.app X₃ =
      F.mapDerivedCategoryFactorsh.hom.app X₀ ≫
        DerivedCategory.Qh.map
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (x₁ ≫ x₂ ≫ x₃)) := by
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  exact F.mapDerivedCategoryFactorsh.hom.naturality (x₁ ≫ x₂ ≫ x₃)

private theorem chase₈ {𝒞 : Type*} [Category 𝒞] {Q P₁ R₁ R₁' R₁'' R₄ N : 𝒞}
    (Λσ : Q ⟶ P₁) (m : P₁ ⟶ R₁) (ch : R₁ ⟶ R₁') (e : R₁' ⟶ R₁'')
    (ci' : R₁'' ⟶ R₄) (Λgf : Q ⟶ R₁') (ci : R₁' ⟶ R₁) (Λf'b : Q ⟶ R₁'')
    (ν : Q ⟶ N) (Λτ : N ⟶ R₄)
    (h3a : Λσ ≫ m = Λgf ≫ ci) (hcancel : ci ≫ ch = 𝟙 _) (htr : Λgf ≫ e = Λf'b)
    (h3b : Λf'b ≫ ci' = ν ≫ Λτ) :
    Λσ ≫ m ≫ ch ≫ e ≫ ci' = ν ≫ Λτ := by
  rw [reassoc_of% h3a, reassoc_of% hcancel, reassoc_of% htr, h3b]

private theorem chase₆ {𝒞 : Type*} [Category 𝒞]
    {P P' Q₀ Q₁ Q₂ S V E₁ E₂ E₃ Z₀ Z₁ Z₂ Z₃ W₁ W₂ : 𝒞}
    (L₁ : P ⟶ P') (L₂ : P' ⟶ Q₀) (σ₁ : Q₀ ⟶ Q₁) (C : Q₁ ⟶ Q₂) (U : Q₂ ⟶ S) (T : S ⟶ V)
    (Gσ : P ⟶ E₁) (GρZ : E₁ ⟶ E₂) (GlZ : E₂ ⟶ E₃) (lZ : E₃ ⟶ V)
    (Gρ₀ : P ⟶ Z₀) (GM₁ : Z₀ ⟶ Z₁) (GM₂ : Z₁ ⟶ Z₂) (GσB : Z₂ ⟶ Z₃) (GSu : Z₃ ⟶ E₃)
    (lY : Z₃ ⟶ S) (N₁ : Z₂ ⟶ W₁) (N₂ : W₁ ⟶ W₂) (σA' : W₂ ⟶ Q₂) (N : Q₀ ⟶ W₂)
    (f₁ : Gσ ≫ GρZ ≫ GlZ = Gρ₀ ≫ GM₁ ≫ GM₂ ≫ GσB ≫ GSu)
    (f₂ : GSu ≫ lZ = lY ≫ T) (f₃ : GσB ≫ lY = N₁ ≫ N₂ ≫ σA' ≫ U)
    (f₄ : σ₁ ≫ C = N ≫ σA') (f₅ : L₁ ≫ L₂ ≫ N = Gρ₀ ≫ GM₁ ≫ GM₂ ≫ N₁ ≫ N₂) :
    L₁ ≫ L₂ ≫ σ₁ ≫ C ≫ U ≫ T = Gσ ≫ GρZ ≫ GlZ ≫ lZ := by
  rw [reassoc_of% f₁, f₂, reassoc_of% f₃, reassoc_of% f₄, reassoc_of% f₅]

private theorem chase₄ {𝒞 : Type*} [Category 𝒞]
    {P P' P'' Q₀ Q₁ Q₂ S S₀ T₀ T₁ T₂ T₃ V Y₀ I₁ I₂ : 𝒞}
    (L₁ : P ⟶ P') (L₂ : P' ⟶ Q₀) (σ₁ : Q₀ ⟶ Q₁) (C : Q₁ ⟶ Q₂) (U : Q₂ ⟶ S) (T : S ⟶ V)
    (R₁ : P ⟶ P'') (R₂ : P'' ⟶ T₀) (σf : T₀ ⟶ T₁) (s : T₁ ⟶ T₂) (ρZ : T₂ ⟶ T₃) (lZ : T₃ ⟶ V)
    (ρY : T₁ ⟶ Y₀) (lY : Y₀ ⟶ S) (ι₁ : T₀ ⟶ I₁) (ι₂ : I₁ ⟶ I₂) (ι₃ : I₂ ⟶ S₀)
    (σ₁' : S₀ ⟶ Q₂) (N : Q₀ ⟶ S₀)
    (e₁ : s ≫ ρZ ≫ lZ = ρY ≫ lY ≫ T) (e₂ : σf ≫ ρY ≫ lY = ι₁ ≫ ι₂ ≫ ι₃ ≫ σ₁' ≫ U)
    (e₃ : σ₁ ≫ C = N ≫ σ₁') (e₄ : L₁ ≫ L₂ ≫ N = R₁ ≫ R₂ ≫ ι₁ ≫ ι₂ ≫ ι₃) :
    L₁ ≫ L₂ ≫ σ₁ ≫ C ≫ U ≫ T = R₁ ≫ R₂ ≫ σf ≫ s ≫ ρZ ≫ lZ := by
  rw [e₁, reassoc_of% e₂, reassoc_of% e₃, reassoc_of% e₄]

/-! ### The characterizing equation of the Leray isomorphism, pointwise -/

section Pointwise

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- `lerayHom_fac` at an object of the homotopy category. -/
theorem lerayIso_hom_app_fac
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map ((sectionsUnit f').app K) ≫
        (lerayIso φ f f' g w).hom.app (DerivedCategory.Qh.obj K) =
      (lerayUnit φ f f' g w).app K :=
  congrArg (fun t => t.app K) (lerayHom_fac φ f f' g w)

end Pointwise

/-- The unit of the derived pushforward along a composite, followed by the inverse composition
isomorphism, is the composite of the units, after applying the sections. -/
private theorem sections_map_unit_comp_compIso_inv {A : Type u} [CommRing A] {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : X' ⟶ X)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (sections (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforwardUnit (g ≫ f).toLRSHom.toShHom).app K) ≫
      (sections (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforwardCompIso g.toLRSHom.toShHom f.toLRSHom.toShHom).inv.app
          (DerivedCategory.Qh.obj K)) =
      (sections (𝟙 (Spec (CommRingCat.of A)))).map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (modulePushforwardComp g.toLRSHom.toShHom f.toLRSHom.toShHom)
            (ComplexShape.up ℤ)).inv.app K)) ≫
        (sections (𝟙 (Spec (CommRingCat.of A)))).map
          ((derivedPushforwardUnit f.toLRSHom.toShHom).app
            (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (sections (𝟙 (Spec (CommRingCat.of A)))).map
          ((derivedPushforward f.toLRSHom.toShHom).map
            ((derivedPushforwardUnit g.toLRSHom.toShHom).app K)) := by
  have h := (derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv
    g.toLRSHom.toShHom f.toLRSHom.toShHom K).trans
    (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit_app
      g.toLRSHom.toShHom f.toLRSHom.toShHom (derivedPushforward g.toLRSHom.toShHom)
      (derivedPushforward f.toLRSHom.toShHom) (derivedPushforwardUnit g.toLRSHom.toShHom)
      (derivedPushforwardUnit f.toLRSHom.toShHom) K)
  have h' := congrArg (sections (𝟙 (Spec (CommRingCat.of A)))).map h
  simp only [Functor.map_comp] at h'
  exact h'

/-! ### Leray isomorphisms along a composite with a structure morphism -/

section Composite

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- The identifications of degreewise sections along `g ≫ f` and along `g` and `f` agree at the
class of a complex: both routes are the identity on underlying modules. -/
theorem lerayIso_comp_structure_identifications
    (wgf : (g ≫ f) ≫ 𝟙 (Spec (CommRingCat.of A)) = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (wid : f ≫ 𝟙 (Spec (CommRingCat.of A)) = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) ℤ) :
    (homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars φ)
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) (g ≫ f))
        (baseSectionsRestrictIso φ (𝟙 _) f' (g ≫ f) wgf)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso (𝟙 _) (g ≫ f))
          (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).map
        ((Functor.mapHomotopyCategoryCompIso
          (modulePushforwardComp g.toLRSHom.toShHom f.toLRSHom.toShHom)
          (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) =
    (homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars φ) (compositeSections f g)
        (baseSectionsRestrictIso φ f f' g w)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f g)
          (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.app
        (DerivedCategory.Qh.obj (((baseSections f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)))) ≫
      (homotopyCompBaseIso (baseSections f) (ModuleCat.restrictScalars (RingHom.id A))
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) f)
        (baseSectionsRestrictIso (RingHom.id A) (𝟙 _) f f wid)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso (𝟙 _) f)
          (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C))) := by
  simp only [homotopyCompBaseIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Iso.symm_hom,
    Category.assoc]
  refine congrArg (fun t => _ ≫ t) ?_
  refine chase₅ _ _ _ _ _ _ _ _
    (restrictScalarsIdDerivedIso_hom_app_comp_factorsh _) ?_
  refine map_comp₃_eq_map_comp₅ DerivedCategory.Qh _ _ _ _ _ _ _ _ ?_
  rfl

/-- The Leray isomorphism over `φ` along `g ≫ f : X' ⟶ Spec A` is the Leray isomorphism along
`g`, followed by the Leray isomorphism of `f` over `A` (the latter read through derived
restriction of scalars along the identity), up to the composition isomorphism of derived direct
images. -/
theorem lerayIso_comp_structure
    (wgf : (g ≫ f) ≫ 𝟙 (Spec (CommRingCat.of A)) = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (wid : f ≫ 𝟙 (Spec (CommRingCat.of A)) = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id A))) :
    (lerayIso φ (𝟙 _) f' (g ≫ f) wgf).hom ≫
        Functor.whiskerRight
          (derivedPushforwardCompIso g.toLRSHom.toShHom f.toLRSHom.toShHom).inv
          (sections (𝟙 (Spec (CommRingCat.of A)))) =
      (lerayIso φ f f' g w).hom ≫
        Functor.whiskerLeft (derivedPushforward g.toLRSHom.toShHom)
          ((Functor.rightUnitor (sections f)).inv ≫
            Functor.whiskerLeft (sections f) (restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom ≫
            (lerayIso (RingHom.id A) (𝟙 _) f f wid).hom) := by
  apply (sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory).rightDerived_ext
    (Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (qis X')
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change _ ≫ (lerayIso φ (𝟙 _) f' (g ≫ f) wgf).hom.app _ ≫
      (sections (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforwardCompIso g.toLRSHom.toShHom f.toLRSHom.toShHom).inv.app _) = _
  rw [← Category.assoc, lerayIso_hom_app_fac, ← Category.assoc, lerayIso_hom_app_fac]
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app]
  simp only [Category.assoc, Category.id_comp]
  have hcomp := sections_map_unit_comp_compIso_inv f g K
  rw [hcomp]
  have hId : ∀ {Y Z : DerivedCategory (ModuleCat.{u} A)} (u : Y ⟶ Z) {W}
      (h : (ModuleCat.restrictScalars (RingHom.id A)).mapDerivedCategory.obj Z ⟶ W),
      u ≫ (restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.app Z ≫ h =
        (restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.app Y ≫
          (ModuleCat.restrictScalars (RingHom.id A)).mapDerivedCategory.map u ≫ h := by
    intro Y Z u W h
    exact (reassoc_of% ((restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.naturality u)) h
  have hL : ∀ {Y Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
      (u : Y ⟶ Z) {W} (h : (sections (𝟙 (Spec (CommRingCat.of A)))).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj Z) ⟶ W),
      (ModuleCat.restrictScalars (RingHom.id A)).mapDerivedCategory.map ((sections f).map u) ≫
          (lerayIso (RingHom.id A) (𝟙 _) f f wid).hom.app Z ≫ h =
        (lerayIso (RingHom.id A) (𝟙 _) f f wid).hom.app Y ≫
          (sections (𝟙 (Spec (CommRingCat.of A)))).map
            ((derivedPushforward f.toLRSHom.toShHom).map u) ≫ h := by
    intro Y Z u W h
    exact (reassoc_of% ((lerayIso (RingHom.id A) (𝟙 _) f f wid).hom.naturality u)) h
  refine chase₄ _ _ _ _ _ _ _ _ _ _ _ _
    ((restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.app ((sections f).obj
      (DerivedCategory.Qh.obj (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K))))
    ((lerayIso (RingHom.id A) (𝟙 _) f f wid).hom.app
      (DerivedCategory.Qh.obj (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K)))
    ((restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom.app _)
    ((homotopyCompBaseIso (baseSections f) (ModuleCat.restrictScalars (RingHom.id A))
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) f)
        (baseSectionsRestrictIso (RingHom.id A) (𝟙 _) f f wid)).hom.app
          (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso (𝟙 _) f)
          (ComplexShape.up ℤ)).inv.app
          (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((sectionsUnit (𝟙 (Spec (CommRingCat.of A)))).app
      (((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).map
      ((Functor.mapHomotopyCategoryCompIso
        (modulePushforwardComp g.toLRSHom.toShHom f.toLRSHom.toShHom)
        (ComplexShape.up ℤ)).inv.app K))
    ?_ ?_ ?_ ?_
  · exact (hId _ _).trans
      (congrArg (_ ≫ ·) ((lerayIso (RingHom.id A) (𝟙 _) f f wid).hom.naturality _))
  · exact (hId _ _).trans (congrArg (_ ≫ ·) (lerayIso_hom_app_fac (RingHom.id A) (𝟙 _) f f wid _))
  · exact ((sectionsUnit (𝟙 (Spec (CommRingCat.of A)))).naturality _).symm
  · exact lerayIso_comp_structure_identifications φ f f' g w wgf wid K.as

/-- The identifications of degreewise sections along `f' ≫ Spec φ` and along `f'` and `Spec φ`
agree: both routes are the identity on underlying modules. -/
theorem lerayIso_structure_comp_identifications
    (w' : (f' ≫ Spec.map (CommRingCat.ofHom φ)) ≫ 𝟙 (Spec (CommRingCat.of A)) =
      f' ≫ Spec.map (CommRingCat.ofHom φ))
    (wid' : f' ≫ 𝟙 (Spec (CommRingCat.of B)) = f' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)))
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars φ)
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) (f' ≫ Spec.map (CommRingCat.ofHom φ)))
        (baseSectionsRestrictIso φ (𝟙 _) f' (f' ≫ Spec.map (CommRingCat.ofHom φ)) w')).hom.app K ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (pushforwardSectionsIso (𝟙 (Spec (CommRingCat.of A)))
            (f' ≫ Spec.map (CommRingCat.ofHom φ)))
          (ComplexShape.up ℤ)).inv.app K) ≫
      (homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).map
        ((Functor.mapHomotopyCategoryCompIso
          (modulePushforwardComp f'.toLRSHom.toShHom
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
          (ComplexShape.up ℤ)).inv.app K) =
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom.app
          (DerivedCategory.Qh.obj
            (((baseSections f').mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars (RingHom.id B))
          (compositeSections (𝟙 (Spec (CommRingCat.of B))) f')
          (baseSectionsRestrictIso (RingHom.id B) (𝟙 _) f' f' wid')).hom.app K) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (pushforwardSectionsIso (𝟙 (Spec (CommRingCat.of B))) f')
          (ComplexShape.up ℤ)).inv.app K)) ≫
      (homotopyCompBaseIso (baseSections (𝟙 (Spec (CommRingCat.of B))))
        (ModuleCat.restrictScalars φ)
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) (Spec.map (CommRingCat.ofHom φ)))
        (baseSectionsRestrictIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
          (specMap_comp_id φ))).hom.app
        (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsIso (𝟙 (Spec (CommRingCat.of A))) (Spec.map (CommRingCat.ofHom φ)))
        (ComplexShape.up ℤ)).inv.app
          (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) := by
  simp only [homotopyCompBaseIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  refine chase₇ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (ModuleCat.restrictScalars φ).mapDerivedCategory.map
      (restrictScalarsIdDerivedIso_hom_app_comp_factorsh _)))
    (mapDerivedCategoryFactorsh_naturality₃ (ModuleCat.restrictScalars φ) _ _ _) ?_
  refine map_comp₃_eq_map_comp₃ DerivedCategory.Qh _ _ _ _ _ _ ?_
  rfl

/-- The Leray isomorphism over `φ` along `f' ≫ Spec φ : X' ⟶ Spec A` is the Leray isomorphism of
`f'` over `B` (read through derived restriction of scalars along the identity), restricted to `A`,
followed by the Leray isomorphism of `Spec φ`, up to the composition isomorphism of derived direct
images. -/
theorem lerayIso_structure_comp
    (w' : (f' ≫ Spec.map (CommRingCat.ofHom φ)) ≫ 𝟙 (Spec (CommRingCat.of A)) =
      f' ≫ Spec.map (CommRingCat.ofHom φ))
    (wid' : f' ≫ 𝟙 (Spec (CommRingCat.of B)) = f' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) :
    (lerayIso φ (𝟙 _) f' (f' ≫ Spec.map (CommRingCat.ofHom φ)) w').hom ≫
        Functor.whiskerRight
          (derivedPushforwardCompIso f'.toLRSHom.toShHom
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).inv
          (sections (𝟙 (Spec (CommRingCat.of A)))) =
      Functor.whiskerRight
          ((Functor.rightUnitor (sections f')).inv ≫
            Functor.whiskerLeft (sections f') (restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom ≫
            (lerayIso (RingHom.id B) (𝟙 _) f' f' wid').hom)
          (ModuleCat.restrictScalars φ).mapDerivedCategory ≫
        Functor.whiskerLeft (derivedPushforward f'.toLRSHom.toShHom)
          (lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)).hom := by
  apply (sections f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory).rightDerived_ext
    (Functor.whiskerRight (sectionsUnit f') (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (qis X')
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change _ ≫ (lerayIso φ (𝟙 _) f' (f' ≫ Spec.map (CommRingCat.ofHom φ)) w').hom.app _ ≫
      (sections (𝟙 (Spec (CommRingCat.of A)))).map
        ((derivedPushforwardCompIso f'.toLRSHom.toShHom
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).inv.app _) = _
  rw [← Category.assoc, lerayIso_hom_app_fac]
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app]
  simp only [Category.assoc, Category.id_comp, Functor.map_comp]
  have hcomp := sections_map_unit_comp_compIso_inv (Spec.map (CommRingCat.ofHom φ)) f' K
  rw [hcomp]
  have hB : (sectionsUnit f').app K ≫
      (restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom.app
        ((sections f').obj (DerivedCategory.Qh.obj K)) ≫
      (lerayIso (RingHom.id B) (𝟙 _) f' f' wid').hom.app (DerivedCategory.Qh.obj K) =
      (restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom.app _ ≫
        (lerayUnit (RingHom.id B) (𝟙 _) f' f' wid').app K :=
    (reassoc_of% ((restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom.naturality
      ((sectionsUnit f').app K))) _ |>.trans
      (congrArg (_ ≫ ·) (lerayIso_hom_app_fac (RingHom.id B) (𝟙 _) f' f' wid' K))
  refine chase₆ _ _ _ _ _ _ _ _ _ _
    ((ModuleCat.restrictScalars φ).mapDerivedCategory.map
      ((restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom.app _))
    ((ModuleCat.restrictScalars φ).mapDerivedCategory.map
      ((homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars (RingHom.id B))
        (compositeSections (𝟙 (Spec (CommRingCat.of B))) f')
        (baseSectionsRestrictIso (RingHom.id B) (𝟙 _) f' f' wid')).hom.app K))
    ((ModuleCat.restrictScalars φ).mapDerivedCategory.map
      (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsIso (𝟙 (Spec (CommRingCat.of B))) f') (ComplexShape.up ℤ)).inv.app K)))
    ((ModuleCat.restrictScalars φ).mapDerivedCategory.map
      ((sectionsUnit (𝟙 (Spec (CommRingCat.of B)))).app
        (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((ModuleCat.restrictScalars φ).mapDerivedCategory.map
      ((sections (𝟙 (Spec (CommRingCat.of B)))).map
        ((derivedPushforwardUnit f'.toLRSHom.toShHom).app K)))
    ((lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)).hom.app
      (DerivedCategory.Qh.obj
        (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((homotopyCompBaseIso (baseSections (𝟙 (Spec (CommRingCat.of B))))
        (ModuleCat.restrictScalars φ)
        (compositeSections (𝟙 (Spec (CommRingCat.of A))) (Spec.map (CommRingCat.ofHom φ)))
        (baseSectionsRestrictIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
          (specMap_comp_id φ))).hom.app
      (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsIso (𝟙 (Spec (CommRingCat.of A))) (Spec.map (CommRingCat.ofHom φ)))
        (ComplexShape.up ℤ)).inv.app
      (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((sectionsUnit (𝟙 (Spec (CommRingCat.of A)))).app
      (((modulePushforward (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        (((modulePushforward f'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    ((homotopyBaseSections (𝟙 (Spec (CommRingCat.of A)))).map
      ((Functor.mapHomotopyCategoryCompIso
        (modulePushforwardComp f'.toLRSHom.toShHom
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
        (ComplexShape.up ℤ)).inv.app K))
    ?_ ?_ ?_ ?_ ?_
  · have h := congrArg (ModuleCat.restrictScalars φ).mapDerivedCategory.map hB
    simp only [Functor.map_comp, lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h
    exact h
  · exact (lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
      (specMap_comp_id φ)).hom.naturality _
  · exact lerayIso_hom_app_fac φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ) _
  · exact ((sectionsUnit (𝟙 (Spec (CommRingCat.of A)))).naturality _).symm
  · exact lerayIso_structure_comp_identifications φ f' w' wid' K

end Composite

/-! ### Transport along an equality of structure morphisms -/

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X' : Scheme.{u}}
  (f' : X' ⟶ Spec (CommRingCat.of B))

/-- The Leray isomorphisms along two equal morphisms `k = k' : X' ⟶ Spec A` agree, up to the
transport between the two derived direct images. -/
theorem lerayIso_hom_app_comp_eqToHom {k k' : X' ⟶ Spec (CommRingCat.of A)} (hk : k = k')
    (wk : k ≫ 𝟙 _ = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (wk' : k' ≫ 𝟙 _ = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (h : (derivedPushforward k.toLRSHom.toShHom).obj G =
      (derivedPushforward k'.toLRSHom.toShHom).obj G) :
    (lerayIso φ (𝟙 _) f' k wk).hom.app G ≫ (sections (𝟙 (Spec (CommRingCat.of A)))).map
      (eqToHom h) = (lerayIso φ (𝟙 _) f' k' wk').hom.app G := by
  subst hk
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Transport

/-! ### Flat base change for derived global sections over an affine base -/

section FlatBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)

/-- **Derived global sections commute with flat base change over an affine base.** Let
`f : X ⟶ Spec A` be flat, quasi-compact and quasi-separated, let `φ : A ⟶ B` be a ring map and
let `X' = X ×_{Spec A} Spec B` with projections `g : X' ⟶ X` and `f' : X' ⟶ Spec B`. For every
`F ∈ D_QCoh(𝒪_X)` the adjoint `RΓ(X, F) ⊗ᴸ_A B ⟶ RΓ(X', Lg^* F)` of the pullback map of
`AlgebraicGeometry.LerayOver.pullbackSectionsMap` is an isomorphism. -/
theorem isIso_derivedBaseChangeComparison_pullbackSectionsMap
    (sq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hF : IsQuasicoherentDerived F) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      (pullbackSectionsMap φ f f' g sq.w F)) := by
  have wid : f ≫ 𝟙 (Spec (CommRingCat.of A)) =
      f ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)) := by simp
  have wid' : f' ≫ 𝟙 (Spec (CommRingCat.of B)) =
      f' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)) := by simp
  have wgf : (g ≫ f) ≫ 𝟙 (Spec (CommRingCat.of A)) =
      f' ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.comp_id, sq.w]
  have wfb : (f' ≫ Spec.map (CommRingCat.ofHom φ)) ≫ 𝟙 (Spec (CommRingCat.of A)) =
      f' ≫ Spec.map (CommRingCat.ofHom φ) := Category.comp_id _
  have sqRS : g.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom :=
    AlgebraicGeometry.comp_toShHom_of_comm sq.w
  let μ : sections f ⟶ derivedPushforward f.toLRSHom.toShHom ⋙ sections (𝟙 _) :=
    (Functor.rightUnitor (sections f)).inv ≫
      Functor.whiskerLeft (sections f) (restrictScalarsIdDerivedIso (RingHom.id A) rfl).hom ≫
      (lerayIso (RingHom.id A) (𝟙 _) f f wid).hom
  let μ' : sections f' ⟶ derivedPushforward f'.toLRSHom.toShHom ⋙ sections (𝟙 _) :=
    (Functor.rightUnitor (sections f')).inv ≫
      Functor.whiskerLeft (sections f') (restrictScalarsIdDerivedIso (RingHom.id B) rfl).hom ≫
      (lerayIso (RingHom.id B) (𝟙 _) f' f' wid').hom
  let G := (derivedPullback g.toLRSHom.toShHom).obj F
  let Λσ := (lerayIso φ f f' g sq.w).hom.app G
  let m := μ.app ((derivedPushforward g.toLRSHom.toShHom).obj G)
  let ch := (sections (𝟙 (Spec (CommRingCat.of A)))).map
      ((derivedPushforwardCompIso g.toLRSHom.toShHom f.toLRSHom.toShHom).hom.app G)
  have hobj : (derivedPushforward (g.toLRSHom.toShHom ≫ f.toLRSHom.toShHom)).obj G =
      (derivedPushforward (f'.toLRSHom.toShHom ≫
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).obj G := by rw [sqRS]
  let e := (sections (𝟙 (Spec (CommRingCat.of A)))).map (eqToHom hobj)
  let ci' := (sections (𝟙 (Spec (CommRingCat.of A)))).map
      ((derivedPushforwardCompIso f'.toLRSHom.toShHom
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).inv.app G)
  let Λgf := (lerayIso φ (𝟙 _) f' (g ≫ f) wgf).hom.app G
  let ci := (sections (𝟙 (Spec (CommRingCat.of A)))).map
      ((derivedPushforwardCompIso g.toLRSHom.toShHom f.toLRSHom.toShHom).inv.app G)
  let Λf'b := (lerayIso φ (𝟙 _) f' (f' ≫ Spec.map (CommRingCat.ofHom φ)) wfb).hom.app G
  let ν := (ModuleCat.restrictScalars φ).mapDerivedCategory.map (μ'.app G)
  let Λτ := (lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)).hom.app
      ((derivedPushforward f'.toLRSHom.toShHom).obj G)
  have hM₃ : Λσ ≫ m ≫ ch ≫ e ≫ ci' = ν ≫ Λτ := chase₈ Λσ m ch e ci' Λgf ci Λf'b ν Λτ
    (congrArg (fun t => t.app G) (lerayIso_comp_structure φ f f' g sq.w wgf wid)).symm
    (((sections _).map_comp _ _).symm.trans ((congrArg (sections _).map
      (Iso.inv_hom_id_app _ _)).trans ((sections _).map_id _)))
    (lerayIso_hom_app_comp_eqToHom φ f' sq.w wgf wfb G hobj)
    (congrArg (fun t => t.app G) (lerayIso_structure_comp φ f' wfb wid'))
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} φ
  have hD : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  let adjE := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    A B _ _ φ _ _ D.functor D.comparison hD
  have hqc : IsQuasicoherentDerived ((derivedPushforward f.toLRSHom.toShHom).obj F) :=
    isQuasicoherent_homologyFunctor_derivedPushforward f F hF
  have hbc := isIso_derivedBaseChangeMap_of_torIndependent sq
    (torIndependent_of_flat_left f (Spec.map (CommRingCat.ofHom φ))) F hF
  have hP₂ := isIso_derivedBaseChangeComparison_pullbackSectionsMap_spec φ _ hqc
  exact Stacks.Cohomology.DerivedBaseChange.isIso_homEquiv_symm_of_baseChange_canonical
    g.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom sqRS adjE (lerayIso φ f f' g sq.w)
    (lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)) μ μ' F
    hM₃ hP₂ hbc

end FlatBaseChange

end AlgebraicGeometry.LerayOver
