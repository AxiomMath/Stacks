module

public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulNested

/-!
# Pulling a section of a tensor power back, read on open subschemes

Let `q : X₁ ⟶ X₂` be a morphism of schemes, `ℒ₂`, `ℒ₁` invertible modules on `X₂`, `X₁` with
`ε : q^*ℒ₂ ≅ ℒ₁`, and `V₁ ≤ q^{-1}(V₂)` opens. A section `y` of `ℒ₂^{⊗ n}` over `V₂` gives two
global sections of tensor powers on the open subscheme `V₁`:

* pull `y` back along `q` and transport it along `ε`
  (`Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull`), then read the result on `V₁`
  (`Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection`);
* read `y` on `V₂` and pull the result back along `q|_{V₁} : V₁ ⟶ V₂`.

Both are, up to isomorphisms of the tensor powers, the inverse image of `y` along
`V₁ ⟶ X₁ ⟶ X₂`.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso`: the isomorphism
  `(ℒ₁|_{V₁})^{⊗ n} ≅ (V₁ ⟶ X₂)^*(ℒ₂^{⊗ n})`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso`: the isomorphism
  `(q|_{V₁})^*((ℒ₂|_{V₂})^{⊗ n}) ≅ (V₁ ⟶ X₂)^*(ℒ₂^{⊗ n})`.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso_sectionPull`: the first
  section is carried by `restrictPowSectionIso` to the inverse image of `y`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso_pullbackSection`: the
  second section is carried by `pullbackRestrictIso` to the inverse image of `y`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.TensorPowerPullback RingedSpaceModuleAdjunction
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (restrictPowSection hom_app_inv_app)
open Stacks.TensorSheafSpellingIso (pullbackCompIso)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X₁ X₂ : Scheme.{u}} (q : X₁ ⟶ X₂) (L₂ : X₂.Modules)
  [Stacks.Ample.IsInvertibleModule X₂ L₂]
  (L₁ : X₁.Modules) [Stacks.Ample.IsInvertibleModule X₁ L₁]
  (ε : (Scheme.Modules.pullback q).obj L₂ ≅ L₁) (V₂ : X₂.Opens) (V₁ : X₁.Opens)
  (h : V₁ ≤ q ⁻¹ᵁ V₂) (n : ℕ)

include h in
/-- The whole of `V₁` lies in the preimage of `V₂` under `V₁ ⟶ X₁ ⟶ X₂`. -/
theorem top_le_preimage_comp : (⊤ : V₁.toScheme.Opens) ≤ (V₁.ι ≫ q) ⁻¹ᵁ V₂ :=
  fun x _ => h x.2

/-- The isomorphism `(ℒ₁|_{V₁})^{⊗ n} ≅ (V₁ ⟶ X₂)^*(ℒ₂^{⊗ n})` composed of the comparisons of
tensor powers with inverse images of [Stacks, Tag 01CU] and of `ε^{⊗ n}`. -/
def restrictPowSectionIso :
    natTensorPow ((Scheme.Modules.pullback V₁.ι).obj L₁) n ≅
      (Scheme.Modules.pullback (V₁.ι ≫ q)).obj (tensorPowerModule X₂ L₂ (n : ℤ)) :=
  haveI := isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  haveI := isInvertible_tensorPower_of_isInvertibleModule X₁ ((Scheme.Modules.pullback q).obj L₂)
  powCompare ((Scheme.Modules.pullback V₁.ι).obj L₁) n ≪≫
    (pullbackIntPowIso V₁.ι.toLRSHom.toShHom L₁ (n : ℤ)).symm ≪≫
    (Scheme.Modules.pullback V₁.ι).mapIso
      ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε (n : ℤ)).symm ≪≫
        (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)).symm) ≪≫
    (pullbackCompIso V₁.ι q).app (tensorPowerModule X₂ L₂ (n : ℤ))

/-! ### Sections under morphisms of modules, restriction and inverse image -/

section Rules

variable {Z : Scheme.{u}}

/-- A morphism of modules commutes with restriction of sections. -/
theorem hom_app_map {A B : Z.Modules} (φ : A ⟶ B) {W W' : Z.Opens} (i : W ≤ W')
    (z : Γ(A, W')) :
    φ.app W (A.presheaf.map (homOfLE i).op z) = B.presheaf.map (homOfLE i).op (φ.app W' z) := by
  simpa using
    congrArg (fun k => (ConcreteCategory.hom k) z) (φ.mapPresheaf.naturality (homOfLE i).op)

/-- Restricting `e⁻¹ z` and applying `e` gives the restriction of `z`. -/
theorem iso_hom_app_map_inv_app {A B : Z.Modules} (e : A ≅ B) {W W' : Z.Opens} (i : W ≤ W')
    (z : Γ(B, W')) :
    e.hom.app W (A.presheaf.map (homOfLE i).op (e.inv.app W' z)) =
      B.presheaf.map (homOfLE i).op z := by
  rw [hom_app_map e.hom i, hom_app_inv_app]

/-- Restricting `e z` and applying `e⁻¹` gives the restriction of `z`. -/
theorem iso_inv_app_map_hom_app {A B : Z.Modules} (e : A ≅ B) {W W' : Z.Opens} (i : W ≤ W')
    (z : Γ(A, W')) :
    e.inv.app W (B.presheaf.map (homOfLE i).op (e.hom.app W' z)) =
      A.presheaf.map (homOfLE i).op z :=
  iso_hom_app_map_inv_app e.symm i z

/-- The unit of `k^* ⊣ k_*` on sections. -/
abbrev unitApp {Y : Scheme.{u}} (k : Z ⟶ Y) (F : Y.Modules) (W : Y.Opens) (x : Γ(F, W)) :
    Γ((Scheme.Modules.pullback k).obj F, k ⁻¹ᵁ W) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app F).app W x

/-- The unit of `k^* ⊣ k_*` on sections is natural in the module. -/
theorem unitApp_naturality {Y : Scheme.{u}} (k : Z ⟶ Y) {F G : Y.Modules} (φ : F ⟶ G)
    (W : Y.Opens) (x : Γ(F, W)) :
    ((Scheme.Modules.pullback k).map φ).app (k ⁻¹ᵁ W) (unitApp k F W x) =
      unitApp k G W (φ.app W x) :=
  Scheme.Modules.unit_app_val_app_naturality k φ W x

/-- The unit of `k^* ⊣ k_*` on sections commutes with restriction. -/
theorem unitApp_map {Y : Scheme.{u}} (k : Z ⟶ Y) (F : Y.Modules) {W W' : Y.Opens} (i : W ≤ W')
    (x : Γ(F, W')) :
    unitApp k F W (F.presheaf.map (homOfLE i).op x) =
      ((Scheme.Modules.pullback k).obj F).presheaf.map (homOfLE (k.preimage_mono i)).op
        (unitApp k F W' x) :=
  hom_app_map ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app F) i x

/-- The comparison `f^* g^* ≅ (f ≫ g)^*` carries the image of a section under the two units to
its image under the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`. -/
theorem pullbackCompIso_hom_app_unitApp {Y Y' : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ Y')
    (M : Y'.Modules) (W : Y'.Opens) (x : Γ(M, W)) :
    ((pullbackCompIso f g).hom.app M).app (f ⁻¹ᵁ g ⁻¹ᵁ W)
        (unitApp f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W) (unitApp g M W x)) =
      unitApp (f ≫ g) M W x := by
  have key : ((pullbackCompIso f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ W) (unitApp (f ≫ g) M W x) =
      unitApp f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W) (unitApp g M W x) :=
    Stacks.PullbackTensorCoherence.pullbackCompIso_app_inv_pullbackUnit
      f.toLRSHom.toShHom g.toLRSHom.toShHom M (op W) x
  rw [← key]
  exact hom_app_inv_app ((pullbackCompIso f g).app M) _ _

/-- Restricting a section in two steps is restricting it in one. -/
theorem map_map_homOfLE (F : Z.Modules) {W W' W'' : Z.Opens} (i : W ≤ W') (j : W' ≤ W'')
    (k : W ≤ W'') (x : Γ(F, W'')) :
    F.presheaf.map (homOfLE i).op (F.presheaf.map (homOfLE j).op x) =
      F.presheaf.map (homOfLE k).op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

end Rules

/-- `restrictPowSectionIso` on the reading of a section over `V₁` as a global section on `V₁`. -/
theorem restrictPowSectionIso_hom_app (z : Γ(tensorPowerModule X₁ L₁ (n : ℤ), V₁)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
    haveI := isInvertible_tensorPower_of_isInvertibleModule X₁ ((Scheme.Modules.pullback q).obj L₂)
    (restrictPowSectionIso q L₂ L₁ ε V₁ n).hom.app ⊤
        (restrictPowSection L₁ V₁ n ((powCompare L₁ n).inv.app V₁ z)) =
      ((pullbackCompIso V₁.ι q).hom.app (tensorPowerModule X₂ L₂ (n : ℤ))).app ⊤
        (((Scheme.Modules.pullback V₁.ι).obj ((Scheme.Modules.pullback q).obj
            (tensorPowerModule X₂ L₂ (n : ℤ)))).presheaf.map
          (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self V₁)).op
          (unitApp V₁.ι _ V₁
            (Scheme.Modules.Hom.app (X := X₁)
              (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)).inv V₁
              (Scheme.Modules.Hom.app (X := X₁)
                (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε (n : ℤ)).inv
                V₁ z)))) := by
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ ((Scheme.Modules.pullback q).obj L₂)
  have T1 := Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self V₁
  unfold restrictPowSection Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullPowSection
    restrictPowSectionIso
  rw [hom_app_inv_app (powCompare L₁ n) V₁ z]
  let φ := (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε (n : ℤ)).inv ≫
    (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)).inv
  let u := unitApp V₁.ι (tensorPowerModule X₁ L₁ (n : ℤ)) V₁ z
  have e2 := iso_hom_app_map_inv_app (powCompare ((Scheme.Modules.pullback V₁.ι).obj L₁) n) T1
    (Scheme.Modules.Hom.app (X := V₁.toScheme)
      (pullbackIntPowIso V₁.ι.toLRSHom.toShHom L₁ (n : ℤ)).hom (V₁.ι ⁻¹ᵁ V₁) u)
  have e3 := iso_inv_app_map_hom_app (pullbackIntPowIso V₁.ι.toLRSHom.toShHom L₁ (n : ℤ)) T1 u
  have e4 := hom_app_map ((Scheme.Modules.pullback V₁.ι).map φ) T1 u
  have e5 := unitApp_naturality V₁.ι φ V₁ z
  let C := (pullbackCompIso V₁.ι q).hom.app (tensorPowerModule X₂ L₂ (n : ℤ))
  refine (congrArg (fun t => C.app ⊤
    (((Scheme.Modules.pullback V₁.ι).map φ).app ⊤
      (Scheme.Modules.Hom.app (X := V₁.toScheme)
        (pullbackIntPowIso V₁.ι.toLRSHom.toShHom L₁ (n : ℤ)).inv ⊤ t))) e2).trans ?_
  refine (congrArg (fun t => C.app ⊤ (((Scheme.Modules.pullback V₁.ι).map φ).app ⊤ t)) e3).trans ?_
  refine (congrArg (fun t => C.app ⊤ t) e4).trans ?_
  refine congrArg (fun t => C.app ⊤
    (((Scheme.Modules.pullback V₁.ι).obj ((Scheme.Modules.pullback q).obj
            (tensorPowerModule X₂ L₂ (n : ℤ)))).presheaf.map (homOfLE T1).op t)) e5

/-- `restrictPowSectionIso` carries the reading on `V₁` of the transported inverse image
`sectionPull` of `y` to the inverse image of `y` along `V₁ ⟶ X₁ ⟶ X₂`. -/
theorem restrictPowSectionIso_sectionPull (y : Γ(tensorPowerModule X₂ L₂ (n : ℤ), V₂)) :
    (restrictPowSectionIso q L₂ L₁ ε V₁ n).hom.app ⊤
        (restrictPowSection L₁ V₁ n ((powCompare L₁ n).inv.app V₁
          (sectionPull q L₂ L₁ ε (n : ℤ) V₂ V₁ h y))) =
      pullbackSectionHom (V₁.ι ≫ q) (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ ⊤
        (top_le_preimage_comp q V₂ V₁ h) y := by
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ ((Scheme.Modules.pullback q).obj L₂)
  have T1 := Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self V₁
  have hW : V₁.ι ⁻¹ᵁ V₁ ≤ V₁.ι ⁻¹ᵁ q ⁻¹ᵁ V₂ := V₁.ι.preimage_mono h
  have hs : Scheme.Modules.Hom.app (X := X₁)
      (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)).inv V₁
      (Scheme.Modules.Hom.app (X := X₁)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε (n : ℤ)).inv V₁
        (sectionPull q L₂ L₁ ε (n : ℤ) V₂ V₁ h y)) =
      ((Scheme.Modules.pullback q).obj (tensorPowerModule X₂ L₂ (n : ℤ))).presheaf.map
        (homOfLE h).op (unitApp q (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y) := by
    have e1 : Scheme.Modules.Hom.app (X := X₁)
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε (n : ℤ)).inv V₁
        (sectionPull q L₂ L₁ ε (n : ℤ) V₂ V₁ h y) =
        (tensorPowerModule X₁ ((Scheme.Modules.pullback q).obj L₂) (n : ℤ)).presheaf.map
          (homOfLE h).op (Scheme.Modules.Hom.app (X := X₁)
            (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)).hom (q ⁻¹ᵁ V₂)
            (unitApp q (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y)) :=
      hom_app_inv_app (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε
        (n : ℤ)).symm V₁ _
    rw [e1]
    exact iso_inv_app_map_hom_app (pullbackIntPowIso q.toLRSHom.toShHom L₂ (n : ℤ)) h _
  refine (restrictPowSectionIso_hom_app q L₂ L₁ ε V₁ n _).trans ?_
  have htop := top_le_preimage_comp q V₂ V₁ h
  let N := tensorPowerModule X₂ L₂ (n : ℤ)
  let C := (pullbackCompIso V₁.ι q).hom.app N
  let F := (Scheme.Modules.pullback q).obj N
  let G := (Scheme.Modules.pullback V₁.ι).obj F
  refine (congrArg (fun t => C.app ⊤ (G.presheaf.map (homOfLE T1).op (unitApp V₁.ι F V₁ t)))
    hs).trans ?_
  refine (congrArg (fun t => C.app ⊤ (G.presheaf.map (homOfLE T1).op t))
    (unitApp_map V₁.ι F h (unitApp q N V₂ y))).trans ?_
  refine (congrArg (fun t => C.app ⊤ t) (map_map_homOfLE G T1 hW htop _)).trans ?_
  refine (hom_app_map C htop _).trans ?_
  exact congrArg (fun t => ((Scheme.Modules.pullback (V₁.ι ≫ q)).obj N).presheaf.map
    (homOfLE htop).op t) (pullbackCompIso_hom_app_unitApp V₁.ι q N V₂ y)

/-- The isomorphism `(q|_{V₁})^*((ℒ₂|_{V₂})^{⊗ n}) ≅ (V₁ ⟶ X₂)^*(ℒ₂^{⊗ n})`. -/
def pullbackRestrictIso :
    (Scheme.Modules.pullback (q.resLE V₂ V₁ h)).obj
        (natTensorPow ((Scheme.Modules.pullback V₂.ι).obj L₂) n) ≅
      (Scheme.Modules.pullback (V₁.ι ≫ q)).obj (tensorPowerModule X₂ L₂ (n : ℤ)) :=
  (Scheme.Modules.pullback (q.resLE V₂ V₁ h)).mapIso
      (powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n ≪≫
        (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).symm) ≪≫
    (pullbackCompIso (q.resLE V₂ V₁ h) V₂.ι).app (tensorPowerModule X₂ L₂ (n : ℤ)) ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι q h)).app
      (tensorPowerModule X₂ L₂ (n : ℤ))

/-- `pullbackRestrictIso` on the inverse image of a global section. -/
theorem pullbackRestrictIso_hom_app
    (z : Γ(natTensorPow ((Scheme.Modules.pullback V₂.ι).obj L₂) n, ⊤)) :
    (pullbackRestrictIso q L₂ V₂ V₁ h n).hom.app ⊤
        (pullbackSectionHom (q.resLE V₂ V₁ h)
          (natTensorPow ((Scheme.Modules.pullback V₂.ι).obj L₂) n) ⊤ ⊤ (by simp) z) =
      ((Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι q h)).hom.app
          (tensorPowerModule X₂ L₂ (n : ℤ))).app ⊤
        (((pullbackCompIso (q.resLE V₂ V₁ h) V₂.ι).hom.app
            (tensorPowerModule X₂ L₂ (n : ℤ))).app ⊤
          (((Scheme.Modules.pullback (q.resLE V₂ V₁ h)).obj
              ((Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ)))).presheaf.map
            (homOfLE (by simp)).op
            (unitApp (q.resLE V₂ V₁ h) ((Scheme.Modules.pullback V₂.ι).obj
                (tensorPowerModule X₂ L₂ (n : ℤ))) ⊤
              (Scheme.Modules.Hom.app (X := V₂.toScheme)
                (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).inv ⊤
                ((powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n).hom.app ⊤ z))))) := by
  have hT : (⊤ : V₁.toScheme.Opens) ≤ (q.resLE V₂ V₁ h) ⁻¹ᵁ ⊤ := by simp
  have e4 := hom_app_map ((Scheme.Modules.pullback (q.resLE V₂ V₁ h)).map
    ((powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n).hom ≫
      (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).inv)) hT
    (unitApp (q.resLE V₂ V₁ h) (natTensorPow ((Scheme.Modules.pullback V₂.ι).obj L₂) n) ⊤ z)
  have e5 := unitApp_naturality (q.resLE V₂ V₁ h)
    ((powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n).hom ≫
      (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).inv) ⊤ z
  exact congrArg (fun t => ((Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι q h)).hom.app
          (tensorPowerModule X₂ L₂ (n : ℤ))).app ⊤
        (((pullbackCompIso (q.resLE V₂ V₁ h) V₂.ι).hom.app
            (tensorPowerModule X₂ L₂ (n : ℤ))).app ⊤ t))
    (e4.trans (congrArg (fun t => ((Scheme.Modules.pullback (q.resLE V₂ V₁ h)).obj
              ((Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ)))).presheaf.map
            (homOfLE hT).op t) e5))

/-- `pullbackRestrictIso` carries the inverse image along `q|_{V₁}` of the reading of `y` on `V₂`
to the inverse image of `y` along `V₁ ⟶ X₁ ⟶ X₂`. -/
theorem pullbackRestrictIso_pullbackSection (y : Γ(tensorPowerModule X₂ L₂ (n : ℤ), V₂)) :
    (pullbackRestrictIso q L₂ V₂ V₁ h n).hom.app ⊤
        (pullbackSectionHom (q.resLE V₂ V₁ h)
          (natTensorPow ((Scheme.Modules.pullback V₂.ι).obj L₂) n) ⊤ ⊤ (by simp)
          (restrictPowSection L₂ V₂ n ((powCompare L₂ n).inv.app V₂ y))) =
      pullbackSectionHom (V₁.ι ≫ q) (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ ⊤
        (top_le_preimage_comp q V₂ V₁ h) y := by
  have T2 := Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self V₂
  have hJ := Scheme.Hom.resLE_comp_ι q h
  have hT : (⊤ : V₁.toScheme.Opens) ≤ (q.resLE V₂ V₁ h) ⁻¹ᵁ ⊤ := by simp
  have hle : (q.resLE V₂ V₁ h) ⁻¹ᵁ ⊤ ≤ (q.resLE V₂ V₁ h) ⁻¹ᵁ (V₂.ι ⁻¹ᵁ V₂) :=
    (q.resLE V₂ V₁ h).preimage_mono T2
  have hT2 : (⊤ : V₁.toScheme.Opens) ≤ (q.resLE V₂ V₁ h) ⁻¹ᵁ (V₂.ι ⁻¹ᵁ V₂) := hT.trans hle
  have hr : Scheme.Modules.Hom.app (X := V₂.toScheme)
        (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).inv ⊤
        ((powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n).hom.app ⊤
          (restrictPowSection L₂ V₂ n ((powCompare L₂ n).inv.app V₂ y))) =
      ((Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ))).presheaf.map
        (homOfLE T2).op (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y) := by
    unfold restrictPowSection Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullPowSection
    rw [hom_app_inv_app (powCompare L₂ n) V₂ y]
    have e2 := iso_hom_app_map_inv_app (powCompare ((Scheme.Modules.pullback V₂.ι).obj L₂) n) T2
      (Scheme.Modules.Hom.app (X := V₂.toScheme)
        (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).hom (V₂.ι ⁻¹ᵁ V₂)
        (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y))
    have e3 := iso_inv_app_map_hom_app (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)) T2
      (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y)
    exact (congrArg (fun t => Scheme.Modules.Hom.app (X := V₂.toScheme)
      (pullbackIntPowIso V₂.ι.toLRSHom.toShHom L₂ (n : ℤ)).inv ⊤ t) e2).trans e3
  refine (pullbackRestrictIso_hom_app q L₂ V₂ V₁ h n _).trans ?_
  have e6 := unitApp_map (q.resLE V₂ V₁ h)
    ((Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ))) T2
    (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y)
  have e7 := map_map_homOfLE ((Scheme.Modules.pullback (q.resLE V₂ V₁ h)).obj
    ((Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ)))) hT hle hT2
    (unitApp (q.resLE V₂ V₁ h) ((Scheme.Modules.pullback V₂.ι).obj
      (tensorPowerModule X₂ L₂ (n : ℤ))) (V₂.ι ⁻¹ᵁ V₂)
      (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y))
  have e8 := hom_app_map ((pullbackCompIso (q.resLE V₂ V₁ h) V₂.ι).hom.app
    (tensorPowerModule X₂ L₂ (n : ℤ))) hT2
    (unitApp (q.resLE V₂ V₁ h) ((Scheme.Modules.pullback V₂.ι).obj
      (tensorPowerModule X₂ L₂ (n : ℤ))) (V₂.ι ⁻¹ᵁ V₂)
      (unitApp V₂.ι (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y))
  have e9 := pullbackCompIso_hom_app_unitApp (q.resLE V₂ V₁ h) V₂.ι
    (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ y
  have e10 := (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullbackSectionHom_congr
    (tensorPowerModule X₂ L₂ (n : ℤ)) V₂ hJ ⊤ hT2 y).symm
  let C1 := (pullbackCompIso (q.resLE V₂ V₁ h) V₂.ι).hom.app (tensorPowerModule X₂ L₂ (n : ℤ))
  let C2 := (Scheme.Modules.pullbackCongr hJ).hom.app (tensorPowerModule X₂ L₂ (n : ℤ))
  let F := (Scheme.Modules.pullback V₂.ι).obj (tensorPowerModule X₂ L₂ (n : ℤ))
  let G := (Scheme.Modules.pullback (q.resLE V₂ V₁ h)).obj F
  refine (congrArg (fun t => C2.app ⊤ (C1.app ⊤ (G.presheaf.map (homOfLE hT).op
    (unitApp (q.resLE V₂ V₁ h) F ⊤ t)))) hr).trans ?_
  refine (congrArg (fun t => C2.app ⊤ (C1.app ⊤ (G.presheaf.map (homOfLE hT).op t))) e6).trans ?_
  refine (congrArg (fun t => C2.app ⊤ (C1.app ⊤ t)) e7).trans ?_
  refine (congrArg (fun t => C2.app ⊤ t) e8).trans ?_
  refine (congrArg (fun t => C2.app ⊤
    (((Scheme.Modules.pullback (q.resLE V₂ V₁ h ≫ V₂.ι)).obj
      (tensorPowerModule X₂ L₂ (n : ℤ))).presheaf.map (homOfLE hT2).op t)) e9).trans ?_
  exact e10

/-- `sectionPull` commutes with restriction to a smaller open of the source. -/
theorem map_sectionPull (n : ℤ) {W W' : X₁.Opens} (hW : W ≤ q ⁻¹ᵁ V₂) (i : W' ≤ W)
    (y : Γ(tensorPowerModule X₂ L₂ n, V₂)) :
    (tensorPowerModule X₁ L₁ n).presheaf.map (homOfLE i).op (sectionPull q L₂ L₁ ε n V₂ W hW y) =
      sectionPull q L₂ L₁ ε n V₂ W' (i.trans hW) y := by
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := isInvertible_tensorPower_of_isInvertibleModule X₁ ((Scheme.Modules.pullback q).obj L₂)
  have e1 := hom_app_map (Z := X₁)
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom i
    ((tensorPowerModule X₁ ((Scheme.Modules.pullback q).obj L₂) n).presheaf.map (homOfLE hW).op
      (Scheme.Modules.Hom.app (X := X₁) (pullbackIntPowIso q.toLRSHom.toShHom L₂ n).hom (q ⁻¹ᵁ V₂)
        (unitApp q (tensorPowerModule X₂ L₂ n) V₂ y)))
  refine e1.symm.trans ?_
  exact congrArg (fun t => Scheme.Modules.Hom.app (X := X₁)
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom W' t)
    (map_map_homOfLE _ i hW (i.trans hW) _)

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
