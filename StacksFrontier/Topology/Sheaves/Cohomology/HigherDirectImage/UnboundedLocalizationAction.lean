module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.UnboundedLocalization
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Local morphisms into a shift, read on the higher direct images restricted to an open

Let `φ : X ⟶ Y` be a morphism of ringed spaces and `U ⊆ Y` open, with `V = φ⁻¹U`. A morphism of
complexes `u : K₁|_V ⟶ (K₂|_V)[p]` defined only over `V` induces, through the identification
`(Rⁿφ_*K)|_U ≅ Rⁿ(φ|_V)_*(K|_V)` of
`Stacks.Cohomology.HigherDirectImage.derivedPushforwardHomologyRestrictIso`, a morphism
`(Rⁿφ_*K₁)|_U ⟶ (R^{n + p}φ_*K₂)|_U`. This file defines it and proves that it is computed by
global data whenever `u` is: if `c : K₀ ⟶ K₁` and `a : K₀ ⟶ K₂[p]` are global morphisms with
`c|_V ≫ u = a|_V`, then the action of `u` after `(Rⁿφ_*c)|_U` is `(Rⁿφ_*a)|_U` followed by the
shift.

## Main definitions

* `Stacks.Cohomology.HigherDirectImage.restrictedHigherDirectImageAction`.

## Main results

* `Stacks.Cohomology.HigherDirectImage.restrictedHigherDirectImageAction_of_global`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (φ : X ⟶ Y) (U : Opens Y)

/-- **The action on restricted higher direct images of a morphism into a shift of `D(𝒪_V)`.**
For objects `M₁, M₂` of `D(𝒪_X)`, a morphism `ψ : M₁|_V ⟶ (M₂|_V)[s]` and `s + n = n'`, the
morphism `(Rⁿφ_*M₁)|_U ⟶ (R^{n'}φ_*M₂)|_U`: the shift map of `R(φ|_V)_*ψ` on cohomology, read
through the identification `derivedPushforwardHomologyRestrictIso` at both ends. -/
def restrictedDerivedAction
    {M₁ M₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} {s : ℤ}
    (ψ : (derivedModuleRestriction X (preimageOpen φ U)).obj M₁ ⟶
      ((derivedModuleRestriction X (preimageOpen φ U)).obj M₂)⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    (moduleRestriction Y U).obj ((DerivedCategory.homologyFunctor _ n).obj
        ((totalDerivedPushforward φ).obj M₁)) ⟶
      (moduleRestriction Y U).obj ((DerivedCategory.homologyFunctor _ n').obj
        ((totalDerivedPushforward φ).obj M₂)) :=
  (derivedPushforwardHomologyRestrictIso φ U n).hom.app M₁ ≫
    (DerivedCategory.homologyFunctor _ 0).shiftMap
      ((totalDerivedPushforward (restrictedMorphism φ U)).map ψ ≫
        ((totalDerivedPushforward (restrictedMorphism φ U)).commShiftIso s).hom.app _) n n' h ≫
    (derivedPushforwardHomologyRestrictIso φ U n').inv.app M₂

example {X' Y' : RingedSpace.{u, u}} (ψ : X' ⟶ Y') :
    totalDerivedPushforward ψ =
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward ψ :=
  rfl

/-- The unbounded derived direct image is additive, being exact. -/
theorem additive_totalDerivedPushforward {X' Y' : RingedSpace.{u, u}} (ψ : X' ⟶ Y') :
    (totalDerivedPushforward ψ).Additive := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift ψ
  have := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated ψ
  exact Functor.IsTriangulated.instAdditive (F := totalDerivedPushforward ψ)

section Linear

-- `hasSheafifyOpensMax` leaves its second universe undetermined; instance search can pick it and
-- the kernel then rejects the resulting term.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

/-- `restrictedDerivedAction` is additive in the morphism. -/
theorem restrictedDerivedAction_add
    {M₁ M₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} {s : ℤ}
    (ψ ψ' : (derivedModuleRestriction X (preimageOpen φ U)).obj M₁ ⟶
      ((derivedModuleRestriction X (preimageOpen φ U)).obj M₂)⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    restrictedDerivedAction φ U (ψ + ψ') n n' h =
      restrictedDerivedAction φ U ψ n n' h + restrictedDerivedAction φ U ψ' n n' h := by
  have := additive_totalDerivedPushforward (restrictedMorphism φ U)
  dsimp only [restrictedDerivedAction]
  have hs : ∀ {A B : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y U)))} (x y : A ⟶ B⟦s⟧),
      (DerivedCategory.homologyFunctor _ 0).shiftMap (x + y) n n' h =
        (DerivedCategory.homologyFunctor _ 0).shiftMap x n n' h +
          (DerivedCategory.homologyFunctor _ 0).shiftMap y n n' h := fun x y => by
    simp only [Functor.shiftMap, Functor.map_add, Preadditive.add_comp]
  rw [Functor.map_add, Preadditive.add_comp, hs]
  exact (congrArg (_ ≫ ·) ((Preadditive.rightComp _ _).map_add _ _)).trans
    (Preadditive.comp_add _ _ _ _ _ _)

/-- `restrictedDerivedAction` commutes with the action of the units of `ℤ`. -/
theorem restrictedDerivedAction_units_smul
    {M₁ M₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} {s : ℤ}
    (ε : ℤˣ) (ψ : (derivedModuleRestriction X (preimageOpen φ U)).obj M₁ ⟶
      ((derivedModuleRestriction X (preimageOpen φ U)).obj M₂)⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    restrictedDerivedAction φ U (ε • ψ) n n' h = ε • restrictedDerivedAction φ U ψ n n' h := by
  have := additive_totalDerivedPushforward (restrictedMorphism φ U)
  dsimp only [restrictedDerivedAction]
  have hs : ∀ {A B : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (restrictToOpen Y U)))} (m : ℤ) (x : A ⟶ B⟦s⟧),
      (DerivedCategory.homologyFunctor _ 0).shiftMap (m • x) n n' h =
        m • (DerivedCategory.homologyFunctor _ 0).shiftMap x n n' h := fun m x => by
    simp only [Functor.shiftMap, Functor.map_zsmul, Preadditive.zsmul_comp]
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp, hs]
  exact (congrArg (_ ≫ ·) (Preadditive.zsmul_comp _ _ _)).trans (Preadditive.comp_zsmul _ _ _)

end Linear

/-- The pasting of two squares used for `restrictedDerivedAction_global`. -/
private theorem global_action_paste {C : Type*} [Category C] {A₀ A₁ B₀ B₁ B₂ B₃ T T' T₁ : C}
    (e : T ≅ T') {a : A₀ ⟶ A₁} {b : A₁ ⟶ B₁} {c : A₀ ⟶ B₀} {d : B₀ ⟶ B₁} {x : B₁ ⟶ B₂}
    {x' : B₂ ⟶ B₃} {y : B₃ ⟶ T'} {J : A₁ ⟶ T₁} {J' : T₁ ⟶ T}
    (h₁ : a ≫ b = c ≫ d) (h₂ : b ≫ ((x ≫ x') ≫ y) = (J ≫ J') ≫ e.hom) :
    c ≫ (d ≫ x ≫ x' ≫ y) ≫ e.inv = a ≫ J ≫ J' := by
  simp only [Category.assoc] at h₂ ⊢
  rw [← reassoc_of% h₁, reassoc_of% h₂, Iso.hom_inv_id, Category.comp_id]

/-- **A global morphism acts by its higher direct images**: for `δ : M₁ ⟶ M₂[s]` in `D(𝒪_X)`, the
action of its restriction `δ|_V` (read through the commutation of restriction with the shift) is
the restriction to `U` of the shift map of `Rφ_*δ` on cohomology. -/
theorem restrictedDerivedAction_global
    {M₁ M₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} {s : ℤ}
    (δ : M₁ ⟶ M₂⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    restrictedDerivedAction φ U ((derivedModuleRestriction X (preimageOpen φ U)).map δ ≫
        ((derivedModuleRestriction X (preimageOpen φ U)).commShiftIso s).hom.app M₂) n n' h =
      (moduleRestriction Y U).map ((DerivedCategory.homologyFunctor _ 0).shiftMap
        ((totalDerivedPushforward φ).map δ ≫
          ((totalDerivedPushforward φ).commShiftIso s).hom.app M₂)
        n n' h) := by
  have hI := (derivedPushforwardHomologyRestrictIso φ U n).hom.naturality δ
  have hsft := derivedPushforwardHomologyRestrictIso_shift φ U M₂ s n n' h
  dsimp only [restrictedDerivedAction, Functor.shiftMap]
  simp only [Functor.map_comp, Category.assoc] at hsft ⊢
  exact global_action_paste ((derivedPushforwardHomologyRestrictIso φ U n').app M₂) hI hsft

/-- A commutative square, followed by two morphisms. -/
private theorem square_comp_paste {C : Type*} [Category C] {A B B' D E F : C} {a : A ⟶ B}
    {b : B ⟶ D} {c : A ⟶ B'} {d : B' ⟶ D} {x : D ⟶ E} {y : E ⟶ F} (h : a ≫ b = c ≫ d) :
    c ≫ (d ≫ x) ≫ y = a ≫ b ≫ x ≫ y := by
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]

/-- **Precomposition with a global morphism.** For `g : M₀ ⟶ M₁` in `D(𝒪_X)`, the action of
`g|_V ≫ ψ` is `(Rⁿφ_*g)|_U` followed by the action of `ψ`. -/
theorem restrictedDerivedAction_map_comp
    {M₀ M₁ M₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} {s : ℤ}
    (g : M₀ ⟶ M₁) (ψ : (derivedModuleRestriction X (preimageOpen φ U)).obj M₁ ⟶
      ((derivedModuleRestriction X (preimageOpen φ U)).obj M₂)⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    restrictedDerivedAction φ U ((derivedModuleRestriction X (preimageOpen φ U)).map g ≫ ψ) n n' h =
      (moduleRestriction Y U).map ((DerivedCategory.homologyFunctor _ n).map
        ((totalDerivedPushforward φ).map g)) ≫ restrictedDerivedAction φ U ψ n n' h := by
  have hI := (derivedPushforwardHomologyRestrictIso φ U n).hom.naturality g
  dsimp only [restrictedDerivedAction]
  rw [Functor.map_comp, Category.assoc, Functor.shiftMap_comp']
  exact square_comp_paste hI

/-- **The action on restricted higher direct images of a morphism of complexes into a shift
defined over `φ⁻¹U`.** For `u : K₁|_V ⟶ (K₂|_V)[p]` and `p + n = n'`, `restrictedDerivedAction` of
the morphism `u` induces in `D(𝒪_V)`, read through the identification of the derived restriction
of a complex with the restriction of the complex. -/
def restrictedHigherDirectImageAction
    {K₁ K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {p : ℤ}
    (u : ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₁ ⟶
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₂)⟦p⟧) (n n' : ℤ) (h : p + n = n') :
    (moduleRestriction Y U).obj ((DerivedCategory.homologyFunctor _ n).obj
        ((totalDerivedPushforward φ).obj (DerivedCategory.Q.obj K₁))) ⟶
      (moduleRestriction Y U).obj ((DerivedCategory.homologyFunctor _ n').obj
        ((totalDerivedPushforward φ).obj (DerivedCategory.Q.obj K₂))) :=
  restrictedDerivedAction φ U
    ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.app K₁ ≫
      DerivedCategory.Q.map u ≫ (DerivedCategory.Q.commShiftIso p).hom.app _ ≫
      ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.inv.app K₂)⟦p⟧') n n' h

/-- **The action of a local morphism of complexes is computed by global data.** If `c : K₀ ⟶ K₁`
and `a : K₀ ⟶ K₂[p]` are global morphisms of complexes with `c|_V ≫ u = a|_V` (read through the
commutation of restriction with the shift), then `(Rⁿφ_*c)|_U` followed by the action of `u` is
the restriction of the shift map of `Rⁿφ_*a`. -/
theorem restrictedHigherDirectImageAction_of_global
    {K₀ K₁ K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {p : ℤ}
    (u : ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₁ ⟶
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₂)⟦p⟧)
    (c : K₀ ⟶ K₁) (a : K₀ ⟶ K₂⟦p⟧)
    (hca : ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map c ≫ u =
      ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫
        (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso p).hom.app K₂)
    (n n' : ℤ) (h : p + n = n') :
    (moduleRestriction Y U).map ((DerivedCategory.homologyFunctor _ n).map
        ((totalDerivedPushforward φ).map (DerivedCategory.Q.map c))) ≫
        restrictedHigherDirectImageAction φ U u n n' h =
      (moduleRestriction Y U).map ((DerivedCategory.homologyFunctor _ 0).shiftMap
        ((totalDerivedPushforward φ).map (DerivedCategory.Q.map a ≫
            (DerivedCategory.Q.commShiftIso p).hom.app K₂) ≫
          ((totalDerivedPushforward φ).commShiftIso p).hom.app (DerivedCategory.Q.obj K₂))
        n n' h) := by
  have hτc := (moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.naturality c
  have hτa := (moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.naturality a
  have hsh := NatTrans.shift_app_comm
    (moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom p K₂
  simp only [Functor.comp_map, Functor.commShiftIso_comp_hom_app] at hτc hτa hsh
  have hQ := congrArg DerivedCategory.Q.map hca
  simp only [Functor.map_comp] at hQ
  have inner : (derivedModuleRestriction X (preimageOpen φ U)).map (DerivedCategory.Q.map c) ≫
      (moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.app K₁ ≫
      DerivedCategory.Q.map u ≫ (DerivedCategory.Q.commShiftIso p).hom.app _ ≫
        ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.inv.app K₂)⟦p⟧' =
      (derivedModuleRestriction X (preimageOpen φ U)).map
          (DerivedCategory.Q.map a ≫ (DerivedCategory.Q.commShiftIso p).hom.app K₂) ≫
        ((derivedModuleRestriction X (preimageOpen φ U)).commShiftIso p).hom.app
          (DerivedCategory.Q.obj K₂) := by
    have hsh' := hsh =≫
      ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.inv.app K₂)⟦p⟧'
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id] at hsh'
    rw [reassoc_of% hτc, reassoc_of% hQ, ← reassoc_of% hτa, ← hsh', Functor.map_comp]
    simp only [Category.assoc, Functor.comp_obj, Category.comp_id]
  dsimp only [restrictedHigherDirectImageAction]
  rw [← restrictedDerivedAction_map_comp, inner, restrictedDerivedAction_global]

end Stacks.Cohomology.HigherDirectImage
