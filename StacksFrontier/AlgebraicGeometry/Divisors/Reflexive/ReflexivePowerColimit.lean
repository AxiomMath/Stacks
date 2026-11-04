module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerCoconeSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLeftUnitorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneInvertibleOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CodimTwoSectionRestrict
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimensionTwoOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusChart

/-!
# The colimit assertion of Tag 0EBN

Let `X` be an integral locally Noetherian normal scheme, `ℱ` a rank one coherent reflexive
`𝒪_X`-module and `s ∈ Γ(X, ℱ)`, and let `U` be the set of points at which `s : 𝒪_{X, x} → ℱ_x` is
an isomorphism.  [Stacks, Tag 0EBN] asserts that `U` is open and that

`j_*𝒪_U = colim (𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ℱ^{[3]} →ˢ ⋯)`

for the reflexive powers `ℱ^{[n + 1]} = (ℱ ⊗ ℱ^{[n]})^{**}`.  This file proves the colimit
assertion, and with it the tag.

## Main results

* `AlgebraicGeometry.exists_chart`: **an affine chart for the section on the invertible locus**:
  near a point of an open `V` on which `ℱ` is invertible there is an affine open `D` with
  `s|_D = g e` and `U ∩ D = D(g)`.
* `AlgebraicGeometry.CoherentReflexive.exists_step_app_eq_smul`: **multiplication by `s` is
  divisible by `g`** on every open on which `s = g e`.
* `AlgebraicGeometry.CoherentReflexive.exists_leg_app_eq_of_chart`: on such a chart every section
  of `j_*𝒪_U` is in the image of a leg.
* `AlgebraicGeometry.CoherentReflexive.exists_leg_app_eq_of_isAffineOpen` and
  `AlgebraicGeometry.CoherentReflexive.exists_map_app_eq_zero_of_leg_app_eq_zero`: the two
  conditions of the colimit criterion over affine opens.
* `AlgebraicGeometry.CoherentReflexive.isOpen_sectionIsomorphismLocus_and_nonempty_isColimit`:
  `U` is open and `j_*𝒪_U` is the colimit of the reflexive powers ([Stacks, Tag 0EBN]).

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual unitModule)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentReflexiveModules CoherentModules inclusion)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open scoped TensorProduct

universe u

section Charts

open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

/-- Multiplying a free generator of a module by a scalar gives a free generator exactly when the
scalar is a unit. -/
alias bijective_toSpanSingleton_smul_iff :=
  AlgebraicGeometry.bijective_toSpanSingleton_smul_iff_isUnit

variable {Y : Scheme.{u}}

/-- **A local chart for an invertible module and a global section.**  Near every point there is
an open `D`, a section `e` of `L` over `D` generating every stalk, and a function `g` with
`s|_D = g e`; the isomorphism locus of `s` meets `D` in `D(g)`. -/
alias exists_chart_of_isInvertible :=
  AlgebraicGeometry.exists_sectionLocusChart_of_isInvertible

/-- The module map attached to a section sends `1` over `Y` to the section over `Y`. -/
private theorem unitHomEquiv_symm_val_app_one {X : Scheme.{u}} (F : X.Modules) (s : F.sections)
    (Y : X.Opens) :
    (((F.unitHomEquiv.symm s).val.app (op Y)).hom (1 : Γ(X, Y))) = s.eval (op Y) := by
  have h := SheafOfModules.unitHomEquiv_apply_coe F (F.unitHomEquiv.symm s) (op Y)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The restricted section evaluates on an open of `V` as the section on its image. -/
theorem restrictSections_eval {X : Scheme.{u}} (V : X.Opens) (F : X.Modules) (s : F.sections)
    (D : V.toScheme.Opens) :
    (restrictSections V F s).eval (op D) = s.eval (op (V.ι ''ᵁ D)) := by
  have hhom : ((Scheme.Modules.restrictUnitIso V.ι).hom.val.app (op D)).hom
      (1 : Γ(X, V.ι ''ᵁ D)) = (1 : Γ(V, D)) :=
    map_one (V.ι.appIso D).hom.hom
  have hinv : ((Scheme.Modules.restrictUnitIso V.ι).inv.val.app (op D)).hom
      (1 : Γ(V, D)) = (1 : Γ(X, V.ι ''ᵁ D)) := by
    rw [← hhom]
    exact congrArg (fun f => (f.val.app (op D)).hom (1 : Γ(X, V.ι ''ᵁ D)))
      (Scheme.Modules.restrictUnitIso V.ι).hom_inv_id
  have h1 : (restrictSections V F s).eval (op D) =
      (((Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s)).val.app (op D)).hom
        (((Scheme.Modules.restrictUnitIso V.ι).inv.val.app (op D)).hom (1 : Γ(V, D))) := rfl
  rw [h1, hinv]
  exact unitHomEquiv_symm_val_app_one F s (V.ι ''ᵁ D)

/-- **An affine chart for the section on the invertible locus.** -/
theorem exists_chart {X : Scheme.{u}} (F : X.Modules) (s : F.sections) (V : X.Opens)
    (hV : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (F.restrict V.ι))
    {y : X} (hy : y ∈ V) {N : X.Opens} (hyN : y ∈ N) :
    ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧ D ≤ N ∧ ∃ (e : Γ(F, D)) (g : Γ(X, D)),
      s.eval (op D) = g • e ∧ ∀ x ∈ D, (x ∈ sectionIsomorphismLocus F s ↔ x ∈ X.basicOpen g) := by
  have : Stacks.SheafOfModules.IsInvertible V.toScheme.toRingedSpace.presheaf
      (structureSheafRing V.toScheme.toRingedSpace).property (F.restrict V.ι) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hV
  obtain ⟨D', hyD', e', g', hs', hloc'⟩ :=
    exists_chart_of_isInvertible (F.restrict V.ι) (restrictSections V F s) ⟨y, hy⟩
  have hyD₀ : y ∈ V.ι ''ᵁ D' := ⟨⟨y, hy⟩, hyD', rfl⟩
  obtain ⟨D, hDaff, hyD, hDle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show y ∈ (V.ι ''ᵁ D') ⊓ N from ⟨hyD₀, hyN⟩)
  have hDD₀ : D ≤ V.ι ''ᵁ D' := hDle.trans inf_le_left
  have hsm : (g' • e' : Γ(F.restrict V.ι, D')) =
      (@id Γ(X, V.ι ''ᵁ D') g') • (@id Γ(F, V.ι ''ᵁ D') e') := by
    have h := Scheme.Modules.smul_restrictAppIso_hom_apply V.ι F D' g' e'
    rwa [Scheme.Opens.ι_appIso] at h
  have hs₀ : s.eval (op (V.ι ''ᵁ D')) =
      (@id Γ(X, V.ι ''ᵁ D') g') • (@id Γ(F, V.ι ''ᵁ D') e') :=
    ((restrictSections_eval V F s D').symm.trans hs').trans hsm
  refine ⟨D, hDaff, hyD, hDle.trans inf_le_right,
    F.presheaf.map (homOfLE hDD₀).op (@id Γ(F, V.ι ''ᵁ D') e'),
    X.presheaf.map (homOfLE hDD₀).op (@id Γ(X, V.ι ''ᵁ D') g'), ?_, fun x hx => ?_⟩
  · refine Eq.trans ?_ ((congrArg (F.presheaf.map (homOfLE hDD₀).op) hs₀).trans
      (Scheme.Modules.map_smul F (homOfLE hDD₀) _ _))
    exact (PresheafOfModules.sections_property s (homOfLE hDD₀).op).symm
  · obtain ⟨x', hx'D', rfl⟩ := hDD₀ hx
    have hb : X.basicOpen (X.presheaf.map (homOfLE hDD₀).op (@id Γ(X, V.ι ''ᵁ D') g')) =
        D ⊓ X.basicOpen (@id Γ(X, V.ι ''ᵁ D') g') :=
      Scheme.basicOpen_res X _ _
    rw [hb]
    have hres := congrArg (fun S => x' ∈ S) (sectionIsomorphismLocus_restrict V F s)
    simp only [Set.mem_preimage] at hres
    refine hres.symm.to_iff.trans ((hloc' x' hx'D').trans ?_)
    exact Scheme.Opens.mem_basicOpen_toScheme.trans ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

/-- **A cocone on a sequence of `𝒪_X`-modules is a colimit** as soon as, over every affine open
`W`, its legs are jointly surjective on sections and kill only sections that some transition map
kills. -/
def isColimitOfForallIsAffineOpen {X : Scheme.{u}} {D : ℕ ⥤ X.Modules} (c : Cocone D)
    (hsurj : ∀ W : X.Opens, IsAffineOpen W → ∀ ξ : Γ(c.pt, W),
      ∃ (n : ℕ) (η : Γ(D.obj n, W)), (c.ι.app n).app W η = ξ)
    (hker : ∀ W : X.Opens, IsAffineOpen W → ∀ (n : ℕ) (η : Γ(D.obj n, W)),
      (c.ι.app n).app W η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).app W η = 0) :
    IsColimit c :=
  isColimitOfForallMemIsBasis c X.isBasis_affineOpens
    (fun W hW => hsurj W hW) fun W hW => hker W hW

end AlgebraicGeometry

end Charts

namespace AlgebraicGeometry.CoherentReflexive

section Instances

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The `𝒪_X(U)`-module structure on the sections of a coherent reflexive module. -/
instance instModuleSectionsCoherentReflexive (P : CoherentReflexiveModules X) (U : X.Opens) :
    Module Γ(X, U) Γ(P.obj.obj, U) :=
  (P.obj.obj.val.obj (op U)).isModule

/-- The `𝒪_X(U)`-module structure on the sections of a coherent module. -/
instance instModuleSectionsCoherent (P : CoherentModules X) (U : X.Opens) :
    Module Γ(X, U) Γ(P.obj, U) :=
  (P.obj.val.obj (op U)).isModule

variable [IsIntegral X] in
/-- A rank one coherent reflexive module is coherent. -/
instance instIsCoherentRankOne (F : RankOneReflexiveModules X) :
    _root_.SheafOfModules.IsCoherent F.obj.obj.obj :=
  F.isCoherent

end Instances

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (F : CoherentReflexiveModules X) (σ : unitObj X ⟶ F)

/-- The left unit constraint of the ordinary tensor product. -/
def ordLeftUnitor (P : CoherentReflexiveModules X) :
    (ordinaryTensor (unitObj X) P).obj ≅ P.obj.obj :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property P.obj.obj

omit [IsIntegral X] in
/-- The canonical map to the double dual of `𝒪_X ⊗ 𝒫` is an isomorphism. -/
theorem isIso_toDoubleDual_ordinaryTensor_unit (P : CoherentReflexiveModules X) :
    IsIso (toDoubleDual (ordinaryTensor (unitObj X) P).obj) :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_iso (ordLeftUnitor P).symm P.property

omit [IsIntegral X] in
/-- The inverse of the left unit constraint sends a section `c` to `1 ⊗ c`. -/
theorem ordLeftUnitor_inv_app (P : CoherentReflexiveModules X) (Y : X.Opens)
    (c : Γ(P.obj.obj, Y)) :
    ((ordLeftUnitor P).inv.val.app (op Y)).hom c =
      toTensorSheafSection X.toRingedSpace
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) P.obj.obj (op Y)
        ((1 : X.presheaf.obj (op Y)) ⊗ₜ c) := by
  have h := Stacks.SheafOfModules.tensorProductLeftUnitor_hom_val_app_toTensorSheafSection
    X.toRingedSpace P.obj.obj (op Y) 1 c
  replace h := h.trans (one_smul _ c)
  have h2 := congrArg (fun f => (f.val.app (op Y)).hom
    (toTensorSheafSection X.toRingedSpace
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) P.obj.obj (op Y)
        ((1 : X.presheaf.obj (op Y)) ⊗ₜ c))) (ordLeftUnitor P).hom_inv_id
  simp only at h2
  refine Eq.trans ?_ h2
  change _ = ((ordLeftUnitor P).inv.val.app (op Y)).hom
    (((ordLeftUnitor P).hom.val.app (op Y)).hom _)
  exact congrArg _ h.symm

/-- **Multiplication by `σ` is divisible by `g`** on an open `Y` on which `σ(1) = g e`: every
section of `ℱ^{[n]}` over `Y` is carried to `g` times a section of `ℱ^{[n + 1]}`. -/
theorem exists_step_app_eq_smul (n : ℕ) (Y : X.Opens) (e : Γ(F.obj.obj, Y)) (g : Γ(X, Y))
    (hσ : ((σ.hom.hom).val.app (op Y)).hom (1 : X.presheaf.obj (op Y)) = g • e)
    (b : Γ((reflexivePower F n).obj.obj, Y)) :
    ∃ b' : Γ((reflexivePower F (n + 1)).obj.obj, Y),
      Scheme.Modules.Hom.app (reflexivePowerStep F σ n).hom.hom Y b = g • b' := by
  let dd := @asIso _ _ _ _ _ (isIso_toDoubleDual_ordinaryTensor_unit (reflexivePower F n))
  have hT : (tensorObjMap σ (𝟙 (reflexivePower F n))).hom.hom =
      dd.inv ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := ((unitObj X).obj.obj, (reflexivePower F n).obj.obj))
              (Y := (F.obj.obj, (reflexivePower F n).obj.obj))
              (σ.hom.hom, 𝟙 (reflexivePower F n).obj.obj)) ≫
          toDoubleDual (ordinaryTensor F (reflexivePower F n)).obj :=
    (Iso.eq_inv_comp dd).mpr (toDoubleDual_naturality_tensorObjMap F σ (reflexivePower F n))
  set z := Scheme.Modules.Hom.app ((unitTensorObj (reflexivePower F n)).inv.hom.hom ≫
    dd.inv) Y b with hz
  set c := (((ordLeftUnitor (reflexivePower F n)).hom.val.app (op Y)).hom z) with hc
  have hzc : z = toTensorSheafSection X.toRingedSpace
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace))
        (reflexivePower F n).obj.obj (op Y) ((1 : X.presheaf.obj (op Y)) ⊗ₜ c) := by
    have h2 := congrArg (fun f => (f.val.app (op Y)).hom z)
      (ordLeftUnitor (reflexivePower F n)).hom_inv_id
    exact h2.symm.trans (ordLeftUnitor_inv_app (reflexivePower F n) Y c)
  refine ⟨Scheme.Modules.Hom.app (toDoubleDual (ordinaryTensor F (reflexivePower F n)).obj) Y
    (toTensorSheafSection X.toRingedSpace F.obj.obj (reflexivePower F n).obj.obj (op Y)
      (e ⊗ₜ c)), ?_⟩
  have hstep : Scheme.Modules.Hom.app (reflexivePowerStep F σ n).hom.hom Y b =
      Scheme.Modules.Hom.app (toDoubleDual (ordinaryTensor F (reflexivePower F n)).obj) Y
        (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := ((unitObj X).obj.obj, (reflexivePower F n).obj.obj))
              (Y := (F.obj.obj, (reflexivePower F n).obj.obj))
              (σ.hom.hom, 𝟙 (reflexivePower F n).obj.obj))).val.app
          (op Y)).hom z) := by
    rw [reflexivePowerStep_hom_hom, hT]
    rfl
  rw [hstep, hzc]
  have h1 := tensorSheafMap_app_toTensorSheafSection X.toRingedSpace _ _ _ _ σ.hom.hom
    (𝟙 (reflexivePower F n).obj.obj) Y (1 : X.presheaf.obj (op Y)) c
  let : Module (X.toRingedSpace.presheaf.obj (op Y))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F.obj.obj).obj
          (reflexivePower F n).obj.obj).val.obj (op Y)) :=
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F.obj.obj).obj
        (reflexivePower F n).obj.obj).val.obj (op Y)).isModule
  have h2 : toTensorSheafSection X.toRingedSpace F.obj.obj (reflexivePower F n).obj.obj (op Y)
      (((σ.hom.hom).val.app (op Y)).hom (1 : X.presheaf.obj (op Y)) ⊗ₜ c) =
      g • toTensorSheafSection X.toRingedSpace F.obj.obj (reflexivePower F n).obj.obj (op Y)
        (e ⊗ₜ c) := by
    rw [hσ]
    let : Module (X.toRingedSpace.presheaf.obj (op Y))
        ((reflexivePower F n).obj.obj.val.obj (op Y)) :=
      ((reflexivePower F n).obj.obj.val.obj (op Y)).isModule
    let : Module (X.toRingedSpace.presheaf.obj (op Y)) (F.obj.obj.val.obj (op Y)) :=
      (F.obj.obj.val.obj (op Y)).isModule
    have h3 : ((g • e) ⊗ₜ[X.toRingedSpace.presheaf.obj (op Y)] c) =
        g • (e ⊗ₜ[X.toRingedSpace.presheaf.obj (op Y)] c) :=
      (TensorProduct.smul_tmul' g e c).symm
    refine (congrArg (toTensorSheafSection X.toRingedSpace F.obj.obj (reflexivePower F n).obj.obj
      (op Y)) h3).trans ?_
    exact ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F.obj.obj.val)
        ((reflexivePower F n).obj.obj.val)))).app (op Y)).hom.map_smul g _
  refine (congrArg (Scheme.Modules.Hom.app
    (toDoubleDual (ordinaryTensor F (reflexivePower F n)).obj) Y) (h1.trans h2)).trans ?_
  exact Scheme.Modules.Hom.app_smul _ g _

/-! ### The local claim -/

/-- The image of the unit section under the transition map `𝒪_X ⟶ ℱ^{[k]}`, on `D`. -/
def unitPower (D : X.Opens) (k : ℕ) : Γ((reflexivePower F k).obj.obj, D) :=
  Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE (Nat.zero_le k))) D
    (1 : Γ(X, D))

/-- The images of the unit section are related by the transition maps. -/
theorem unitPower_succ (D : X.Opens) (k : ℕ) :
    unitPower F σ D (k + 1) =
      Scheme.Modules.Hom.app (reflexivePowerStep F σ k).hom.hom D (unitPower F σ D k) := by
  have h : (homOfLE (Nat.zero_le (k + 1)) : (0 : ℕ) ⟶ k + 1) =
      homOfLE (Nat.zero_le k) ≫ homOfLE (k.le_add_right 1) := rfl
  rw [unitPower, h, Functor.map_comp, reflexivePowerModules_map_succ]
  rfl

/-- On an open on which `σ(1) = g e`, the image of `1` in `ℱ^{[k]}` is divisible by `g^k`. -/
theorem exists_unitPower_eq_pow_smul (D : X.Opens) (e : Γ(F.obj.obj, D)) (g : Γ(X, D))
    (hσ : ((σ.hom.hom).val.app (op D)).hom (1 : X.presheaf.obj (op D)) = g • e) (k : ℕ) :
    ∃ b : Γ((reflexivePower F k).obj.obj, D), unitPower F σ D k = g ^ k • b := by
  induction k with
  | zero =>
    refine ⟨(1 : Γ(X, D)), ?_⟩
    have h0 : unitPower F σ D 0 = (1 : Γ(X, D)) := by
      rw [unitPower]
      have h : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0) = 𝟙 0 := rfl
      rw [h, CategoryTheory.Functor.map_id]
      rfl
    refine h0.trans ?_
    rw [pow_zero]
    exact (one_smul _ _).symm
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨b', hb'⟩ := exists_step_app_eq_smul F σ k D e g hσ b
    refine ⟨b', ?_⟩
    rw [unitPower_succ, hb]
    refine (Scheme.Modules.Hom.app_smul _ _ _).trans ?_
    rw [hb', smul_smul, pow_succ]

section Legs

variable (U : X.Opens)
  (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    (reflexivePowerStep F σ n).hom.hom))

/-- The zeroth leg of the cocone is restriction to `U`. -/
theorem reflexivePowerPushforwardLeg_zero_app (D : X.Opens) (a : Γ(X, D)) :
    Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep 0) D a = U.ι.app D a := by
  refine (reflexivePowerPushforwardLeg_app U F σ hstep 0 D a).trans ?_
  change ((U.ι.appIso (U.ι ⁻¹ᵁ D)).hom) (X.presheaf.map _ a) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- The image of the preimage of an open under the inclusion of `U` is the intersection. -/
private theorem image_preimage_ι_eq_inf {X : Scheme.{u}} (U Y : X.Opens) :
    U.ι ''ᵁ U.ι ⁻¹ᵁ Y = U ⊓ Y := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- The legs are compatible with the transition maps. -/
private theorem leg_app_map {n m : ℕ} (h : n ≤ m) (D : X.Opens)
    (t : Γ((reflexivePower F n).obj.obj, D)) :
    Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep m) D
        (Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE h)) D t) =
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) D t :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ D t)
    ((reflexivePowerCocone U F σ hstep).w (homOfLE h))

/-- The legs carry `unitPower` to the restriction of `1`. -/
theorem reflexivePowerPushforwardLeg_app_unitPower (D : X.Opens) (k : ℕ) :
    Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep k) D (unitPower F σ D k) =
      U.ι.app D 1 :=
  (leg_app_map F σ U hstep (Nat.zero_le k) D (1 : Γ(X, D))).trans
    (reflexivePowerPushforwardLeg_zero_app F σ U hstep D 1)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Restricting along an equality of opens and back is the identity. -/
theorem presheaf_map_eqToHom_map_eqToHom {A B : X.Opens} (h : A = B) (t : Γ(X, A)) :
    X.presheaf.map (eqToHom h).op (X.presheaf.map (eqToHom h.symm).op t) = t := by
  subst h
  simp

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The `𝒪_X(D)`-module structure on the sections of `j_*𝒪_U` over `D`. -/
theorem pushforward_unit_smul (D : X.Opens) (r : Γ(X, D))
    (ξ : Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), D)) :
    r • ξ = (U.ι.app D r * (show Γ(U, U.ι ⁻¹ᵁ D) from ξ) :
      Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), D)) := rfl

/-- **The local claim**: on an affine chart `D` on which `s = g e` and `U ∩ D = D(g)`, every
section of `j_*𝒪_U` over `D` is in the image of some leg. -/
theorem exists_leg_app_eq_of_chart (D : X.Opens) (hD : IsAffineOpen D) (e : Γ(F.obj.obj, D))
    (g : Γ(X, D))
    (hσ : ((σ.hom.hom).val.app (op D)).hom (1 : X.presheaf.obj (op D)) = g • e)
    (hUD : U ⊓ D = X.basicOpen g)
    (ξ : Γ(U, U.ι ⁻¹ᵁ D)) :
    ∃ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, D)),
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) D η = ξ := by
  have himg : U.ι ''ᵁ U.ι ⁻¹ᵁ D = X.basicOpen g := (image_preimage_ι_eq_inf U D).trans hUD
  set x : Γ(X, X.basicOpen g) :=
    X.presheaf.map (eqToHom himg.symm).op (ξ : Γ(X, U.ι ''ᵁ U.ι ⁻¹ᵁ D)) with hx
  obtain ⟨m, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X D hD g x
  have key : U.ι.app D y = (U.ι.app D g) ^ m * ξ := by
    have h := congrArg (X.presheaf.map (eqToHom himg).op) hy
    rw [map_mul, map_pow] at h
    have e1 : ∀ t : Γ(X, D), X.presheaf.map (eqToHom himg).op
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op t) = U.ι.app D t := fun t => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have e2 : X.presheaf.map (eqToHom himg).op x = ξ :=
      presheaf_map_eqToHom_map_eqToHom himg ξ
    rw [e2] at h
    have e1y : X.presheaf.map (eqToHom himg).op (y |_ X.basicOpen g) = U.ι.app D y := e1 y
    have e1g : X.presheaf.map (eqToHom himg).op (g |_ X.basicOpen g) = U.ι.app D g := e1 g
    rwa [e1y, e1g] at h
  obtain ⟨b, hb⟩ := exists_unitPower_eq_pow_smul F σ D e g hσ m
  refine ⟨m, y • b, ?_⟩
  have hℓ : ∀ (r : Γ(X, D)) (t : Γ((reflexivePower F m).obj.obj, D)),
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep m) D (r • t) =
        (U.ι.app D r * @id Γ(U, U.ι ⁻¹ᵁ D)
          (Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep m) D t)) :=
    fun r t => Scheme.Modules.Hom.app_smul _ r t
  have hone : (U.ι.app D g) ^ m * @id Γ(U, U.ι ⁻¹ᵁ D)
      (Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep m) D b) = 1 := by
    rw [← map_pow, ← hℓ, ← hb, reflexivePowerPushforwardLeg_app_unitPower, map_one]
  refine (hℓ y b).trans ?_
  rw [key, mul_assoc, mul_comm ξ, ← mul_assoc, hone, one_mul]

end Legs

/-! ### Assembly -/

section Assembly

omit [IsLocallyNoetherian X] in
/-- A section of a torsion free quasi-coherent module vanishing on a smaller open containing the
generic point (whenever the larger one does) is zero. -/
theorem eq_zero_of_presheaf_map_eq_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree M) {W W' : X.Opens}
    (h : W' ≤ W) (hW : genericPoint X ∈ W → genericPoint X ∈ W') (η : Γ(M, W))
    (hη : M.presheaf.map (homOfLE h).op η = 0) : η = 0 := by
  by_cases hg : genericPoint X ∈ W
  · apply injective_generic_germ_of_isTorsionFree M hM hg
    rw [map_zero, ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) _ (hW hg), hη,
      map_zero]
  · have := subsingleton_sections_of_notMem_genericPoint M W hg
    exact Subsingleton.elim _ _

omit [IsLocallyNoetherian X] in
/-- An open containing a point of an integral scheme contains its generic point. -/
theorem genericPoint_mem_of_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W :=
  ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open W.isOpen hx

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- A morphism of `𝒪_X`-modules commutes with restriction of sections. -/
theorem hom_app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W)
    (t : Γ(M, W)) :
    Scheme.Modules.Hom.app φ W' (M.presheaf.map (homOfLE h).op t) =
      N.presheaf.map (homOfLE h).op (Scheme.Modules.Hom.app φ W t) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op t

variable (U : X.Opens)
  (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    (reflexivePowerStep F σ n).hom.hom))

/-- **The legs are injective on sections** once `U` contains the generic point. -/
theorem reflexivePowerPushforwardLeg_app_eq_zero (hU : genericPoint X ∈ U) (n : ℕ)
    (W : X.Opens) (η : Γ((reflexivePower F n).obj.obj, W))
    (h : Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η = 0) :
    η = 0 := by
  have h' := (reflexivePowerPushforwardLeg_app U F σ hstep n W η).symm.trans h
  have hz := (app_hom_eq_iff_eq_app_inv (reflexivePowerRestrictLegIso U F σ hstep n)
    (U.ι ⁻¹ᵁ W) _ 0).1 h'
  rw [map_zero] at hz
  have : ((reflexivePower F n).obj.obj : X.Modules).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  exact eq_zero_of_presheaf_map_eq_zero (reflexivePower F n).obj.obj
    (Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_isReflexive_of_isLocallyNoetherian
      _ (isReflexive_reflexivePower F n)) (U.ι.image_preimage_le W)
    (fun hg => ⟨⟨genericPoint X, hU⟩, hg, rfl⟩) η hz

/-- **Gluing local preimages under a leg**: if the opens `D i` cover `O ≤ W` and each restriction
of `ξ` to `D i` is the image of a section `sf i` under the `N`-th leg, then so is the restriction
of `ξ` to `O`. -/
private theorem exists_leg_app_eq_of_cover (hU : genericPoint X ∈ U) (N : ℕ) {ι : Type u}
    (D : ι → X.Opens) {O W : X.Opens} (hDO : ∀ i, D i ≤ O) (hcover : O ≤ iSup D) (hOW : O ≤ W)
    (ξ : Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), W))
    (sf : ∀ i, Γ((reflexivePower F N).obj.obj, D i))
    (hsf : ∀ i, Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep N) (D i) (sf i) =
      ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
        (homOfLE ((hDO i).trans hOW)).op ξ) :
    ∃ η' : Γ((reflexivePower F N).obj.obj, O),
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep N) O η' =
        ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
          (homOfLE hOW).op ξ := by
  have hPres : ∀ {A B C : X.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
      (z : Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), C)),
      ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map (homOfLE h₁).op
          (((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
            (homOfLE h₂).op z) =
        ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
          (homOfLE (h₁.trans h₂)).op z :=
      fun h₁ h₂ z => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hlegres : ∀ (i : ι) {A : X.Opens} (hA : A ≤ D i),
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep N) A
        ((Scheme.Modules.presheaf (reflexivePower F N).obj.obj).map (homOfLE hA).op (sf i)) =
        ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
          (homOfLE (hA.trans ((hDO i).trans hOW))).op ξ := fun i A hA =>
    (hom_app_presheaf_map _ hA (sf i)).trans (by rw [hsf i, hPres])
  have hcompat : TopCat.Presheaf.IsCompatible
      (Scheme.Modules.presheaf (reflexivePower F N).obj.obj) D sf := by
    intro i j
    apply sub_eq_zero.mp
    apply reflexivePowerPushforwardLeg_app_eq_zero F σ U hstep hU N (D i ⊓ D j)
    refine (map_sub _ _ _).trans ?_
    rw [sub_eq_zero]
    exact (hlegres i inf_le_left).trans (hlegres j inf_le_right).symm
  obtain ⟨η', hη', -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨Scheme.Modules.presheaf (reflexivePower F N).obj.obj, Scheme.Modules.isSheaf _⟩ :
      TopCat.Sheaf Ab X) D O (fun i => homOfLE (hDO i)) hcover sf hcompat
  refine ⟨η', TopCat.Sheaf.eq_of_locally_eq'
    (⟨((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf,
      Scheme.Modules.isSheaf _⟩ : TopCat.Sheaf Ab X) D O (fun i => homOfLE (hDO i)) hcover _ _
    fun i => ?_⟩
  refine (hom_app_presheaf_map _ (hDO i) η').symm.trans ?_
  refine (congrArg _ (hη' i)).trans ?_
  exact (hsf i).trans (hPres (hDO i) hOW ξ).symm

end Assembly

section Main

variable [IsNormal X] [_root_.SheafOfModules.IsCoherent F.obj.obj]

omit [IsIntegral X] [IsNormal X] [_root_.SheafOfModules.IsCoherent F.obj.obj] in
/-- The section `σ` attached to `s` evaluates, on the unit section over `Y`, to `s` over `Y`. -/
theorem sectionObjHom_app_one (s : F.obj.obj.sections) (Y : X.Opens) :
    (((sectionObjHom F s).hom.hom).val.app (op Y)).hom (1 : X.presheaf.obj (op Y)) =
      s.eval (op Y) :=
  unitHomEquiv_symm_val_app_one F.obj.obj s Y

/-- **If the isomorphism locus misses the generic point, the section vanishes.** -/
theorem eval_eq_zero_of_genericPoint_notMem (s : F.obj.obj.sections) (V : X.Opens)
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hinv : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict F.obj.obj V.ι))
    (hU : genericPoint X ∉ sectionIsomorphismOpen X F.obj.obj s) (Y : X.Opens) :
    s.eval (op Y) = 0 := by
  have hgV : genericPoint X ∈ V := genericPoint_mem_of_two_le_codimension_compl V hV
  obtain ⟨D, -, hgD, -, e, g, hse, hloc⟩ :=
    exists_chart F.obj.obj s V hinv hgV (N := ⊤) trivial
  have hg0 : g = 0 := by
    rw [← basicOpen_eq_bot_iff]
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxU := (hloc x (X.basicOpen_le g hx)).2 hx
    exact (hU (genericPoint_mem_of_mem (W := sectionIsomorphismOpen X F.obj.obj s) hxU)).elim
  have hsD : s.eval (op D) = 0 := by
    rw [hse, hg0]
    exact zero_smul _ e
  have : (F.obj.obj : X.Modules).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  refine eq_zero_of_presheaf_map_eq_zero F.obj.obj
    (Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_isReflexive_of_isLocallyNoetherian
      _ F.property) (inf_le_left : Y ⊓ D ≤ Y) (fun hgY => ⟨hgY, hgD⟩) _ ?_
  have h1 : (Scheme.Modules.presheaf F.obj.obj).map (homOfLE (inf_le_left : Y ⊓ D ≤ Y)).op
      (s.eval (op Y)) = s.eval (op (Y ⊓ D)) := PresheafOfModules.sections_property s _
  have h2 : (Scheme.Modules.presheaf F.obj.obj).map (homOfLE (inf_le_right : Y ⊓ D ≤ D)).op
      (s.eval (op D)) = s.eval (op (Y ⊓ D)) := PresheafOfModules.sections_property s _
  exact h1.trans (h2.symm.trans (by rw [hsD]; exact map_zero _))

omit [IsNormal X] [_root_.SheafOfModules.IsCoherent F.obj.obj] in
/-- **The kernel condition**: a section killed by a leg is killed by a transition map. -/
theorem exists_map_app_eq_zero_of_leg_app_eq_zero (U : X.Opens)
    (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (reflexivePowerStep F σ n).hom.hom))
    (hzero : genericPoint X ∉ U → ∀ Y : X.Opens,
      ((σ.hom.hom).val.app (op Y)).hom (1 : X.presheaf.obj (op Y)) =
        (0 : Γ(X, Y)) • (0 : Γ(F.obj.obj, Y)))
    (W : X.Opens) (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W))
    (h : Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η = 0) :
    ∃ (m : ℕ) (hm : n ≤ m),
      Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE hm)) W η = 0 := by
  by_cases hgU : genericPoint X ∈ U
  · refine ⟨n, le_rfl, ?_⟩
    rw [reflexivePowerPushforwardLeg_app_eq_zero F σ U hstep hgU n W η h]
    exact map_zero _
  · obtain ⟨b', hb'⟩ := exists_step_app_eq_smul F σ n W 0 0 (hzero hgU W) η
    exact ⟨n + 1, n.le_add_right 1, (congrArg (fun φ => Scheme.Modules.Hom.app φ W η)
      (reflexivePowerModules_map_succ F σ n)).trans (hb'.trans (zero_smul _ _))⟩

omit [_root_.SheafOfModules.IsCoherent F.obj.obj] in
/-- **The surjectivity condition** over an affine open `W`: given affine charts on which
`σ(1) = g e` and `U ∩ D = D(g)` near every point of an open `V` whose complement has codimension at
least two, every section of `j_*𝒪_U` over `W` is in the image of some leg. -/
theorem exists_leg_app_eq_of_isAffineOpen (U : X.Opens)
    (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (reflexivePowerStep F σ n).hom.hom))
    (V : X.Opens)
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hchart : ∀ y ∈ V, ∀ N : X.Opens, y ∈ N → ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧ D ≤ N ∧
      ∃ (e : Γ(F.obj.obj, D)) (g : Γ(X, D)),
        ((σ.hom.hom).val.app (op D)).hom (1 : X.presheaf.obj (op D)) = g • e ∧
          U ⊓ D = X.basicOpen g)
    (W : X.Opens) (hW : IsAffineOpen W)
    (ξ : Γ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme), W)) :
    ∃ (n : ℕ) (η : Γ((reflexivePower F n).obj.obj, W)),
      Scheme.Modules.Hom.app (reflexivePowerPushforwardLeg U F σ hstep n) W η = ξ := by
  by_cases hg : genericPoint X ∈ U.ι ''ᵁ U.ι ⁻¹ᵁ W
  swap
  · have : Subsingleton Γ(unitModule X, U.ι ''ᵁ U.ι ⁻¹ᵁ W) :=
      subsingleton_sections_of_notMem_genericPoint _ _ hg
    exact ⟨0, 0, Subsingleton.elim (α := Γ(unitModule X, U.ι ''ᵁ U.ι ⁻¹ᵁ W)) _ _⟩
  rw [image_preimage_ι_eq_inf] at hg
  obtain ⟨hgU, hgW⟩ := hg
  have hgV : genericPoint X ∈ V := genericPoint_mem_of_two_le_codimension_compl V hV
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN := noetherianSpace_of_isAffineOpen W hW
  have hc : IsCompact ((V ⊓ W : X.Opens) : Set X) := by
    rw [Opens.coe_inf, Set.inter_comm, ← Subtype.image_preimage_coe]
    exact (@NoetherianSpace.isCompact _ _ hN _).image continuous_subtype_val
  choose D hDaff hyD hDle e g hσ hUD using
    fun y : {y : X // y ∈ V ⊓ W} => hchart y.1 y.2.1 (V ⊓ W) y.2
  have hDW : ∀ y, D y ≤ W := fun y => (hDle y).trans inf_le_right
  choose nn ηη hηη using fun y => exists_leg_app_eq_of_chart F σ U hstep (D y) (hDaff y) (e y)
    (g y) (hσ y) (hUD y)
    (((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme)).presheaf.map
      (homOfLE (hDW y)).op ξ)
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun y : {y : X // y ∈ V ⊓ W} => (D y : Set X))
    (fun y => (D y).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hyD _⟩)
  set N := t.sup nn
  have hle : ∀ i : t, nn i.1 ≤ N := fun i => Finset.le_sup i.2
  have hcover : V ⊓ W ≤ iSup fun i : t => D i.1 := fun x hx => by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨η', hleg'⟩ := exists_leg_app_eq_of_cover F σ U hstep hgU N (fun i : t => D i.1)
    (fun i => hDle i.1) hcover inf_le_right ξ
    (fun i => Scheme.Modules.Hom.app ((reflexivePowerModules F σ).map (homOfLE (hle i))) (D i.1)
      (ηη i.1))
    fun i => (leg_app_map F σ U hstep (hle i) _ _).trans (hηη i.1)
  obtain ⟨η, hη⟩ := (bijective_resF_inf_of_two_le_codimension V hV
    (reflexivePower F N).obj.obj (isReflexive_reflexivePower F N) W).2 η'
  refine ⟨N, η, ?_⟩
  have : Nonempty (U.ι ''ᵁ U.ι ⁻¹ᵁ (V ⊓ W)) := ⟨⟨genericPoint X, by
    rw [image_preimage_ι_eq_inf]
    exact ⟨hgU, hgV, hgW⟩⟩⟩
  apply map_injective_of_isIntegral (X := X)
    (homOfLE (Scheme.Hom.image_mono _ (Scheme.Hom.preimage_mono _ inf_le_right)) :
      U.ι ''ᵁ U.ι ⁻¹ᵁ (V ⊓ W) ⟶ U.ι ''ᵁ U.ι ⁻¹ᵁ W)
  refine Eq.trans ?_ (hleg'.trans ?_)
  · refine Eq.trans ?_ ((hom_app_presheaf_map (reflexivePowerPushforwardLeg U F σ hstep N)
      (inf_le_right : V ⊓ W ≤ W) η).symm.trans (congrArg _ hη))
    rfl
  · rfl

/-- **The colimit assertion of [Stacks, Tag 0EBN]**, given an open `V` whose complement has
codimension at least two and on which `ℱ` is invertible. -/
theorem nonempty_isColimit_sectionIsomorphismOpenCocone_of_codimTwo (s : F.obj.obj.sections)
    (V : X.Opens)
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hinv : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict F.obj.obj V.ι)) :
    Nonempty (IsColimit (sectionIsomorphismOpenCocone F s)) := by
  have hchart : ∀ y ∈ V, ∀ N : X.Opens, y ∈ N → ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧
      D ≤ N ∧ ∃ (e : Γ(F.obj.obj, D)) (g : Γ(X, D)),
        (((sectionObjHom F s).hom.hom).val.app (op D)).hom (1 : X.presheaf.obj (op D)) =
          g • e ∧ sectionIsomorphismOpen X F.obj.obj s ⊓ D = X.basicOpen g := by
    intro y hy N hyN
    obtain ⟨D, hDaff, hyD, hDN, e, g, hse, hloc⟩ := exists_chart F.obj.obj s V hinv hy hyN
    refine ⟨D, hDaff, hyD, hDN, e, g, (sectionObjHom_app_one F s D).trans hse, ?_⟩
    ext x
    exact ⟨fun ⟨hxU, hxD⟩ => (hloc x hxD).1 hxU,
      fun hx => ⟨(hloc x (X.basicOpen_le g hx)).2 hx, X.basicOpen_le g hx⟩⟩
  have hzero : genericPoint X ∉ sectionIsomorphismOpen X F.obj.obj s → ∀ Y : X.Opens,
      (((sectionObjHom F s).hom.hom).val.app (op Y)).hom (1 : X.presheaf.obj (op Y)) =
        (0 : Γ(X, Y)) • (0 : Γ(F.obj.obj, Y)) := fun hgU Y => by
    rw [sectionObjHom_app_one, eval_eq_zero_of_genericPoint_notMem F s V hV hinv hgU Y]
    exact (zero_smul Γ(X, Y) (0 : Γ(F.obj.obj, Y))).symm
  exact ⟨isColimitOfForallIsAffineOpen _
    (fun W hW ξ => exists_leg_app_eq_of_isAffineOpen F (sectionObjHom F s)
      (sectionIsomorphismOpen X F.obj.obj s)
      (isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen F s) V hV hchart W hW ξ)
    (fun W _ n η h => exists_map_app_eq_zero_of_leg_app_eq_zero F (sectionObjHom F s)
      (sectionIsomorphismOpen X F.obj.obj s)
      (isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen F s) hzero W n η h)⟩

end Main

section Tag

variable [IsNormal X]

/-- Let `X` be an integral locally Noetherian normal scheme, `ℱ` a rank one coherent reflexive
`𝒪_X`-module and `s ∈ Γ(X, ℱ)`.  The set `U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`
is open, so that `j : U → X` is an open subscheme, and

`j_*𝒪_U = colim (𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ℱ^{[3]} →ˢ ⋯)`,

where `ℱ^{[1]} = ℱ` and `ℱ^{[n + 1]} = (ℱ ⊗_{𝒪_X} ℱ^{[n]})^{**}`: the cocone
`AlgebraicGeometry.CoherentReflexive.sectionIsomorphismOpenCocone` on the directed system
`AlgebraicGeometry.CoherentReflexive.reflexivePowerModules` of reflexive powers under
multiplication by `s`, with vertex `j_*𝒪_U`, is a colimit cocone. -/
@[stacks 0EBN]
theorem isOpen_sectionIsomorphismLocus_and_nonempty_isColimit (F : RankOneReflexiveModules X)
    (s : F.module.sections) :
    IsOpen (sectionIsomorphismLocus F.module s) ∧
      Nonempty (IsColimit (sectionIsomorphismOpenCocone F.obj s)) := by
  refine ⟨isOpen_sectionIsomorphismLocus X F.module s, ?_⟩
  obtain ⟨V, hV, hinv⟩ := exists_codimTwo_isInvertible_restrict F
  exact nonempty_isColimit_sectionIsomorphismOpenCocone_of_codimTwo F.obj s V hV hinv

end Tag

end AlgebraicGeometry.CoherentReflexive
