module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsInjective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Reduction
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Injectivity of ideal-power homomorphisms on an open complement

Let `I` be a quasi-coherent ideal sheaf of finite type on a quasi-compact scheme `X`, and let
`F` be a quasi-coherent sheaf of modules. A homomorphism `I ^ n 𝒪_X ⟶ F` restricts to a section
of `F` over the complement of the support of `I`, because the unit section lies in `I ^ n 𝒪_X`
there. These restrictions are compatible with the inclusions `I ^ (n+1) 𝒪_X ⟶ I ^ n 𝒪_X`, so
they assemble into a map out of the colimit, and that map is injective.

## Main definitions

* `Stacks.Algebraization.idealPowerSystem` is the inverse system of the powers of an ideal
  sheaf.
* `Stacks.Algebraization.idealPowerHom` is the direct system of homomorphisms out of those
  powers.
* `Stacks.Algebraization.canonicalMapToSections` is the map to sections on the open complement,
  bundled with the local evaluation property that pins it down.

## Main results

* `Stacks.Algebraization.canonicalMapToSections_injective` — the canonical map is injective.

## Implementation notes

The canonical map is specified by, rather than identified with, its effect on local sections:
the bundled subtype carries the evaluation property, so every consumer is independent of how
the map is built.

Injectivity is local on a finite affine cover. If a representative `φ : I ^ n 𝒪_X ⟶ F` dies on
the complement, then on an affine chart each of its values is killed by some power of each
element of `I`; finite generation of `I` on that chart — which comes from the finite-type
hypothesis through `moduleFinite_sections_on_affine` — upgrades this to a single power `I ^ k`
annihilating all of them, and then `φ` precomposed with the inclusion of `I ^ (n+k) 𝒪_X`
vanishes on the chart. A finite cover makes one `k` work globally.

Statements spanning `Γ(X, U)` and `Γ(SheafOfModules.unit X.ringCatSheaf, U)`, or spanning
`X.Modules` and `SheafOfModules X.ringCatSheaf`, are definitionally equal and not syntactically
equal; `rw` and `simp` cannot cross them, so those steps are term mode, and
`moduleFinite_sections_affine_var` is stated over a variable module sheaf because the instance
`Module Γ(X, U) Γ(M, U)` does not synthesize when `M` is spelled `N.toSheafOfModules`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology (idealPowerHom)

noncomputable section

/-- The submodules of a sheaf of modules form a complete lattice. -/
local instance {X : Scheme.{u}} {M : X.Modules} : CompleteLattice M.Submodule :=
  SheafOfModules.Submodule.instCompleteLattice

/-- The module structure on the sections of a module sheaf, read off a VARIABLE module sheaf.

Instance search does not find `Module Γ(X, V) Γ(M, V)` when `M` is spelled
`N.toSheafOfModules`; instantiating this definition does not re-synthesize it, so binding it at
the spelling a goal actually uses supplies the action without any transparency option. -/
@[instance_reducible]
private def sectionsModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) Γ(M, V) := inferInstance

/-! ### Finite generation of the ideal on an affine chart -/

/-- Finiteness of the sections of a quasi-coherent module sheaf of finite type over an affine
open, stated over a VARIABLE module sheaf.

Kept separate deliberately: the instance `Module Γ(X, U) Γ(M, U)` does not synthesize when `M`
is spelled `N.toSheafOfModules`, while instantiating this lemma does not re-synthesize it. -/
private lemma moduleFinite_sections_affine_var {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) :=
  AlgebraicGeometry.moduleFinite_sections_on_affine M U.1 U.2

/-- A finite-type ideal sheaf has finitely generated sections on every affine chart. -/
private lemma affineIdeal_fg {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    [((idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).IsFiniteType] :
    (I.ideal U).FG := by
  have hQC : ((idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).IsQuasicoherent :=
    idealPowerMultiple_isQuasicoherent I 1 _
  have hfin := moduleFinite_sections_affine_var
    ((idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules) U
  have hsub : (((idealPowerMultiple I 1
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) :
        Submodule Γ(X, U.1) Γ(X, U.1))).FG :=
    Module.Finite.iff_fg.mp hfin
  rwa [idealPowerMultiple_unit_toSubmodule_obj_affine I 1 U, pow_one] at hsub

/-! ### The direct system of ideal-power homomorphisms -/

/-- The powers of an ideal sheaf decrease, as a comparison of underlying submodules. -/
lemma idealPowerMultiple_succ_toSubmodule_le {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) :
    (idealPowerMultiple I (n + 1) M).toSubmodule ≤ (idealPowerMultiple I n M).toSubmodule :=
  SheafOfModules.Submodule.le_iff.mp (idealPowerMultiple_antitone I M (Nat.le_succ n))

/-- The inverse system of powers of an ideal sheaf, with inclusion transition maps. -/
def idealPowerSystem {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) :
    ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n =>
    (idealPowerMultiple I n M).toSheafOfModules)
    (fun n => ⟨PresheafOfModules.Submodule.homOfLE
      (idealPowerMultiple_succ_toSubmodule_le I n M)⟩)

/-! ### Compatibility of the transitions with the inclusions -/

private lemma sheafSubmodule_homOfLE_comp_ι {X : Scheme.{u}} {M : X.Modules}
    {N P : M.Submodule} (h : N ≤ P) :
    (⟨PresheafOfModules.Submodule.homOfLE h⟩ :
      N.toSheafOfModules ⟶ P.toSheafOfModules) ≫ P.ι = N.ι :=
  SheafOfModules.Hom.ext (PresheafOfModules.Submodule.homOfLE_ι h)

private lemma idealPowerSystem_map_comp_ι {X : Scheme.{u}}
    (I : X.IdealSheafData) (n m : ℕ) (h : n ≤ m) :
    (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map (homOfLE h).op ≫
      (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι =
    (idealPowerMultiple I m (SheafOfModules.unit X.ringCatSheaf)).ι :=
  Stacks.LocalCohomology.ofOpSequence_map_comp
    (fun r => (idealPowerMultiple I r (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules)
    (fun r => (⟨PresheafOfModules.Submodule.homOfLE
      (idealPowerMultiple_succ_toSubmodule_le I r (SheafOfModules.unit X.ringCatSheaf))⟩ :
        (idealPowerMultiple I (r + 1) (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules ⟶
          (idealPowerMultiple I r (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules))
    (SheafOfModules.unit X.ringCatSheaf)
    (fun r => (idealPowerMultiple I r (SheafOfModules.unit X.ringCatSheaf)).ι)
    (fun r => sheafSubmodule_homOfLE_comp_ι (idealPowerMultiple_antitone I _ (Nat.le_succ r)))
    n m h

/-- The transition of the ideal-power system at a successor step is the inclusion of
subsheaves. -/
lemma idealPowerSystem_map_succ {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map (homOfLE (Nat.le_succ n)).op
      = (⟨PresheafOfModules.Submodule.homOfLE
          (idealPowerMultiple_succ_toSubmodule_le I n
            (SheafOfModules.unit X.ringCatSheaf))⟩ :
        (idealPowerMultiple I (n + 1) (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules ⟶
          (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The canonical colimit-to-sections map, specified by local evaluation whenever a section of
an ideal power represents the unit on the complement. -/
def canonicalMapToSections {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) :
    { f : colimit (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F) →
        Γ(F, Stacks.LocalCohomology.idealComplement I) //
      ∀ (n : ℕ) (φ :
        (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F)
        (V : X.Opens) (hV : V ≤ Stacks.LocalCohomology.idealComplement I)
        (s : ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj
          (op n)).val.obj (op V)),
        (((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app
          (op V)).hom s = (show _ from (1 : Γ(X, V)))) →
        ((F.presheaf.map (homOfLE hV).op).hom
          (f ((colimit.ι
            (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F) n) φ)) =
              (φ.val.app (op V)).hom s) } := by
  classical
  let D := idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F
  let eval (n : ℕ) (φ : D.obj n) : Γ(F, Stacks.LocalCohomology.idealComplement I) :=
    (φ.val.app (op (Stacks.LocalCohomology.idealComplement I))).hom
      (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)
  have heval (n : ℕ) (φ : D.obj n) :
      eval (n + 1) ((D.map (homOfLE (Nat.le_succ n))).hom φ) = eval n φ := by
    dsimp only [D, idealPowerHom]
    simp only [CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
    dsimp [eval]
    have hLift :
        ((((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
          (homOfLE (Nat.le_succ n)).op).val.app
          (op (Stacks.LocalCohomology.idealComplement I))).hom
            (complementUnitLift I (n + 1) (Stacks.LocalCohomology.idealComplement I) le_rfl)) =
          complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl := by
      rw [idealPowerSystem_map_succ]
      apply Subtype.ext
      rfl
    change (φ.val.app (op (Stacks.LocalCohomology.idealComplement I))).hom
        ((((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
          (homOfLE (Nat.le_succ n)).op).val.app
          (op (Stacks.LocalCohomology.idealComplement I))).hom
            (complementUnitLift I (n + 1) (Stacks.LocalCohomology.idealComplement I) le_rfl)) = _
    rw [hLift]
  let c : Cocone D := {
    pt := Γ(F, Stacks.LocalCohomology.idealComplement I)
    ι := NatTrans.ofSequence
      (fun n => TypeCat.ofHom (eval n))
      (fun n => by
        ext φ
        exact heval n φ) }
  refine ⟨(colimit.desc D c).hom.toFun, ?_⟩
  intro n φ V hV s hs
  change ((F.presheaf.map (homOfLE hV).op).hom
    ((colimit.ι D n ≫ colimit.desc D c).hom φ) = _)
  rw [colimit.ι_desc]
  dsimp [c, eval, D, idealPowerHom]
  let g : op (Stacks.LocalCohomology.idealComplement I) ⟶ op V := (homOfLE hV).op
  have hs' :
      ((((idealPowerMultiple I n
            (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).val.presheaf.map g).hom
        (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)) = s := by
    apply Subtype.ext
    change (X.ringCatSheaf.obj.map g).hom 1 = s.val
    rw [map_one]
    change s.val = (show Γ(SheafOfModules.unit X.ringCatSheaf, V) from
      (1 : Γ(X, V))) at hs
    exact hs.symm
  have hn' : (F.presheaf.map g).hom
      ((φ.val.app (op (Stacks.LocalCohomology.idealComplement I))).hom
        (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)) =
        (φ.val.app (op V)).hom
          ((((idealPowerMultiple I n
                (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).val.presheaf.map g).hom
            (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)) :=
    (PresheafOfModules.naturality_apply φ.val g
      (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)).symm
  change (F.presheaf.map g).hom ((φ.val.app (op (Stacks.LocalCohomology.idealComplement I))).hom
      (complementUnitLift I n (Stacks.LocalCohomology.idealComplement I) le_rfl)) =
    (φ.val.app (op V)).hom s
  rw [← hs']
  exact hn'

/-! ### Pointwise torsion of a representative that dies on the complement -/

/-- If a representative dies on the complement of the support, then on an affine chart each of
its values is annihilated by some power of each element of the ideal. -/
private lemma exists_pow_smul_eq_zero_of_canonicalMapToSections_zero
    {X : Scheme.{u}} [CompactSpace X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (φ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F)
    (heval : ∀ (V : X.Opens) (hV : V ≤ Stacks.LocalCohomology.idealComplement I),
      (φ.val.app (op V)).hom (complementUnitLift I n V hV) = 0)
    (U : X.affineOpens)
    (x : Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n), U.1))
    (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    letI : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
      inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
    ∃ m : ℕ, a ^ m • (φ.val.app (op U.1)).hom x = 0 := by
  let _ : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
  let V : X.Opens := X.basicOpen a
  have hV : V ≤ Stacks.LocalCohomology.idealComplement I := by
    intro y hy
    have hyU : y ∈ (U : X.Opens) := X.basicOpen_le a hy
    intro hyS
    have hyZ : y ∈ X.zeroLocus (U := U) (I.ideal U) :=
      (I.mem_support_iff_of_mem hyU).mp hyS
    exact (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, U.1)) y).mp hyZ a ha hy
  let i : V ⟶ (U : X.Opens) := homOfLE (X.basicOpen_le a)
  let _ : Module Γ(X, V) Γ(SheafOfModules.unit X.ringCatSheaf, V) :=
    inferInstanceAs (Module Γ(X, V) Γ(X, V))
  let _ := sectionsModule
    ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules) V
  let xV : Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n), V) :=
    ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj
      (op n)).presheaf.map i.op x
  let c : Γ(X, V) := xV.1
  have hxV : xV = c • complementUnitLift I n V hV := Subtype.ext (mul_one c).symm
  let _ : Module Γ(X, V) (F.val.obj (op V)) :=
    inferInstanceAs (Module Γ(X, V) Γ(F, V))
  let _ : Module Γ(X, V)
      (((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n)).val.obj (op V)) :=
    sectionsModule ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n)) V
  have hmap : (φ.val.app (op V)).hom (c • complementUnitLift I n V hV)
      = c • (φ.val.app (op V)).hom (complementUnitLift I n V hV) :=
    map_smul _ _ _
  have hphiV : (φ.val.app (op V)).hom xV = 0 := by
    rw [hxV, hmap, heval V hV, smul_zero]
  let _ : Module Γ(X, U.1) Γ(F, V) :=
    Module.compHom Γ(F, V) (X.presheaf.map i.op).hom
  let ρ := AlgebraicGeometry.Scheme.Modules.restrictionLinearMap F i
  have hρ : ρ ((φ.val.app (op U.1)).hom x) = 0 :=
    (PresheafOfModules.naturality_apply φ.val i.op x).symm.trans hphiV
  have : IsLocalizedModule (Submonoid.powers a) ρ :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      U.2.isCompact U.2.isQuasiSeparated a
  exact Stacks.LocalCohomology.exists_pow_smul_eq_zero_of_localized_zero a ρ
    ((φ.val.app (op U.1)).hom x) hρ

/-- On an affine chart, finite generation upgrades the pointwise power torsion of a
representative to a single ideal power annihilating all of its values. -/
private lemma exists_pow_ideal_annihilates_hom_on_affine
    {X : Scheme.{u}} [CompactSpace X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent]
    [((idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).IsFiniteType]
    (n : ℕ)
    (φ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F)
    (heval : ∀ (V : X.Opens) (hV : V ≤ Stacks.LocalCohomology.idealComplement I),
      (φ.val.app (op V)).hom (complementUnitLift I n V hV) = 0)
    (U : X.affineOpens) :
    letI : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
      inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
    ∃ k : ℕ, ∀ a ∈ I.ideal U ^ k,
      ∀ x : Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n), U.1),
        a • (φ.val.app (op U.1)).hom x = 0 := by
  let _ : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
  let A := Γ(X, U.1)
  let P := Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n), U.1)
  let N : Submodule A A :=
    (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1)
  have hI : (I.ideal U).FG := affineIdeal_fg I U
  have hN : N.FG := by
    dsimp only [N]
    rw [idealPowerMultiple_unit_toSubmodule_obj_affine I n U]
    exact hI.pow (n := n)
  have : Module.Finite A P := by
    change Module.Finite A ↥N
    exact Module.Finite.of_fg hN
  obtain ⟨k, hk⟩ := Stacks.LocalCohomology.exists_pow_le_annihilator_of_fg
    (I.ideal U) hI (⊤ : Submodule A P) (Module.Finite.fg_top) (φ.val.app (op U.1)).hom
    (fun a ha x _ => exists_pow_smul_eq_zero_of_canonicalMapToSections_zero I F n φ heval U x a ha)
  exact ⟨k, fun a ha x => hk a ha x Submodule.mem_top⟩

/-! ### Vanishing of a homomorphism from its restrictions -/

private lemma restrict_hom_eq_zero_fromSpec {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (g : M ⟶ N) (U : X.affineOpens)
    (h : g.val.app (op U.1) = 0) :
    letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    ((Scheme.Modules.restrictFunctor U.2.fromSpec).map g) = 0 := by
  let _ : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hImage : (U : X.Opens) = U.2.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  have h' : g.val.app (op (U.2.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U.1)).Opens))) = 0 := hImage ▸ h
  have htop : ((Scheme.Modules.restrictFunctor U.2.fromSpec).map g).val.app (op ⊤) = 0 := by
    ext x
    change (g.val.app (op (U.2.fromSpec ''ᵁ ⊤))).hom x = 0
    exact congrArg (fun q => q.hom x) h'
  exact Stacks.LocalCohomology.hom_eq_zero_of_app_top
    ((Scheme.Modules.restrictFunctor U.2.fromSpec).map g) htop

private lemma restrict_hom_eq_zero_openAffine {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) (U : X.affineOpens)
    (h : letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
      ((Scheme.Modules.restrictFunctor U.2.fromSpec).map g) = 0) :
    ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι (U : X.Opens))).map g) = 0 := by
  let _ : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let V : X.Opens := U
  let e := U.2.isoSpec
  let R := Scheme.Modules.restrictFunctor V.ι
  let S := Scheme.Modules.restrictFunctor e.inv
  have heq : e.inv ≫ V.ι = U.2.fromSpec := rfl
  have hfrom : (Scheme.Modules.restrictFunctor (e.inv ≫ V.ι)).map g = 0 := by
    have hn := (Scheme.Modules.restrictFunctorCongr heq).hom.naturality g
    apply (cancel_mono ((Scheme.Modules.restrictFunctorCongr heq).hom.app N)).1
    rw [hn, h, Limits.comp_zero, Limits.zero_comp]
  let η := Scheme.Modules.restrictFunctorComp e.inv V.ι
  have hcomp : (R ⋙ S).map g = 0 := by
    have hn := η.hom.naturality g
    have hh : η.hom.app M ≫ (R ⋙ S).map g = 0 := by
      rw [← hn, hfrom]
      simp
    exact (cancel_epi (η.hom.app M)).1 hh
  let ρ := Scheme.Modules.restrictFunctor e.hom
  let ηid : (S ⋙ ρ) ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  have hback : (S ⋙ ρ).map (R.map g) = 0 := by simpa using congrArg ρ.map hcomp
  exact Stacks.LocalCohomology.functor_map_zero_of_iso_id (S ⋙ ρ) ηid (R.map g) hback

private lemma transition_comp_hom_app_zero_on_affine {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n k : ℕ)
    (φ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F)
    (U : X.affineOpens)
    (hkill : letI : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
        inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
      ∀ a ∈ I.ideal U ^ k,
        ∀ x : Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n), U.1),
          a • (φ.val.app (op U.1)).hom x = 0) :
    LinearMap.comp (φ.val.app (op U.1)).hom
      (((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
        (homOfLE (show n ≤ n + k by omega)).op).val.app (op U.1)).hom = 0 := by
  let _ : Module Γ(X, U.1) (F.val.obj (op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(F, U.1))
  let _ : Module Γ(X, U.1) Γ(SheafOfModules.unit X.ringCatSheaf, U.1) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(X, U.1))
  let Pn : Submodule Γ(X, U.1) Γ(X, U.1) :=
    (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1)
  let Pm : Submodule Γ(X, U.1) Γ(X, U.1) :=
    (idealPowerMultiple I (n + k) (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1)
  have hn : Pn = I.ideal U ^ n := idealPowerMultiple_unit_toSubmodule_obj_affine I n U
  have hm : Pm = I.ideal U ^ (n + k) :=
    idealPowerMultiple_unit_toSubmodule_obj_affine I (n + k) U
  have hle : Pm ≤ Pn := by
    rw [hm, hn]
    exact Ideal.pow_le_pow_right (by omega)
  have htrans :
      (((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
        (homOfLE (show n ≤ n + k by omega)).op).val.app (op U.1)).hom
        = Submodule.inclusion hle := by
    have hmor :
        (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
          (homOfLE (show n ≤ n + k by omega)).op =
        (⟨PresheafOfModules.Submodule.homOfLE
            (SheafOfModules.Submodule.le_iff.mp
              (idealPowerMultiple_antitone I (SheafOfModules.unit X.ringCatSheaf)
                (show n ≤ n + k by omega)))⟩ :
          (idealPowerMultiple I (n + k)
              (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules ⟶
            (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules) := by
      apply (cancel_mono (idealPowerMultiple I n
        (SheafOfModules.unit X.ringCatSheaf)).ι).mp
      exact (idealPowerSystem_map_comp_ι I n (n + k) (by omega)).trans
        (sheafSubmodule_homOfLE_comp_ι _).symm
    rw [hmor]
    rfl
  rw [htrans]
  exact Stacks.LocalCohomology.linearMap_comp_inclusion_eq_zero_of_eq
    (I.ideal U) n k Pn Pm hn hm hle (φ.val.app (op U.1)).hom hkill

/-! ### Transitions in the direct system -/

private lemma idealPowerHom_map_apply {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) {n m : ℕ} (h : n ≤ m)
    (φ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F) :
    (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F).map
      (homOfLE h) φ =
      (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).map
          (homOfLE h).op ≫ φ :=
  Stacks.LocalCohomology.ofSequence_precomp_map_apply
    (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)) F h φ

/-! ### Injectivity -/

/-- Two representatives with the same image on the complement agree after a transition. -/
private lemma exists_eventual_eq_of_canonicalMap_eq {X : Scheme.{u}}
    [CompactSpace X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent]
    [((idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).IsFiniteType]
    (n m : ℕ)
    (φ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op n) ⟶ F)
    (ψ : (idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op m) ⟶ F)
    (hsec : (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F) n φ) =
      (canonicalMapToSections I F).1
        (colimit.ι (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F) m ψ)) :
    ∃ r : ℕ, ∃ f : n ⟶ r, ∃ g : m ⟶ r,
      (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F).map f φ =
        (idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F).map g ψ := by
  classical
  let D := idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F
  let S := idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)
  let q := max n m
  let α : n ⟶ q := homOfLE (Nat.le_max_left n m)
  let β : m ⟶ q := homOfLE (Nat.le_max_right n m)
  let φq : S.obj (op q) ⟶ F := D.map α φ
  let ψq : S.obj (op q) ⟶ F := D.map β ψ
  have hι {p : ℕ} (h : p ⟶ q) (x : D.obj p) : colimit.ι D q (D.map h x) = colimit.ι D p x := by
    change ((D.map h) ≫ colimit.ι D q) x = colimit.ι D p x
    rw [colimit.w]
  have hsecq : (canonicalMapToSections I F).1 (colimit.ι D q φq) =
      (canonicalMapToSections I F).1 (colimit.ι D q ψq) := by
    rwa [hι α φ, hι β ψ]
  let δ : S.obj (op q) ⟶ F := φq - ψq
  have hδeval (V : X.Opens) (hV : V ≤ Stacks.LocalCohomology.idealComplement I) :
      (δ.val.app (op V)).hom (complementUnitLift I q V hV) = 0 := by
    let s := complementUnitLift I q V hV
    have hφ := (canonicalMapToSections I F).property q φq V hV s
      (complementUnitLift_spec I q V hV)
    have hψ := (canonicalMapToSections I F).property q ψq V hV s
      (complementUnitLift_spec I q V hV)
    have hres := congrArg ((F.presheaf.map (homOfLE hV).op).hom) hsecq
    rw [hφ, hψ] at hres
    let _ : Module (X.ringCatSheaf.obj.obj (op V))
        Γ((idealPowerMultiple I q (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules, V) :=
      sectionsModule
        ((idealPowerMultiple I q (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules) V
    change ((φq.val.app (op V)).hom - (ψq.val.app (op V)).hom) s = 0
    exact (LinearMap.sub_apply _ _ s).trans (sub_eq_zero.mpr hres)
  obtain ⟨t, Ua, hcover⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affineOpens_sup_eq_top X (⊥ : X.Opens)
  have hsup : ⨆ l, (Ua l : X.Opens) = ⊤ := by
    simpa using hcover
  choose ki hki using fun i : Fin t =>
    exists_pow_ideal_annihilates_hom_on_affine I F q δ hδeval (Ua i)
  let K : ℕ := Finset.univ.sup ki
  have hkill (i : Fin t) (a : Γ(X, Ua i)) (ha : a ∈ I.ideal (Ua i) ^ K)
      (x : Γ((idealPowerSystem I (SheafOfModules.unit X.ringCatSheaf)).obj (op q), (Ua i).1)) :
      let : Module Γ(X, (Ua i).1) (F.val.obj (op (Ua i).1)) :=
        inferInstanceAs (Module Γ(X, (Ua i).1) Γ(F, (Ua i).1))
      a • (δ.val.app (op (Ua i))).hom x = 0 := by
    let _ : Module Γ(X, (Ua i).1) (F.val.obj (op (Ua i).1)) :=
      inferInstanceAs (Module Γ(X, (Ua i).1) Γ(F, (Ua i).1))
    exact hki i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha) x
  let r := q + K
  let γ : q ⟶ r := homOfLE (by omega)
  let τ : S.obj (op r) ⟶ F := S.map γ.op ≫ δ
  have _ : (S.obj (op r)).IsQuasicoherent := idealPowerMultiple_isQuasicoherent I r _
  have hτapp (i : Fin t) : (τ.val.app (op (Ua i))).hom = 0 := by
    let _ : Module Γ(X, (Ua i).1) ((S.obj (op r)).val.obj (op (Ua i).1)) :=
      sectionsModule (S.obj (op r)) (Ua i).1
    let _ : Module Γ(X, (Ua i).1) (F.val.obj (op (Ua i).1)) :=
      inferInstanceAs (Module Γ(X, (Ua i).1) Γ(F, (Ua i).1))
    ext x
    change LinearMap.comp (δ.val.app (op (Ua i))).hom
      ((S.map γ.op).val.app (op (Ua i))).hom x = 0
    exact congrArg (fun f : _ →ₗ[Γ(X, Ua i)] _ => f x)
      (transition_comp_hom_app_zero_on_affine I F q K δ (Ua i) (hkill i))
  have hτrest (i : Fin t) :
      ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι (Ua i : X.Opens))).map τ) = 0 :=
    restrict_hom_eq_zero_openAffine τ (Ua i)
      (restrict_hom_eq_zero_fromSpec τ (Ua i) (ModuleCat.hom_ext (hτapp i)))
  have hτ : τ = 0 := by
    refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
      (fun i : Fin t => (Ua i : X.Opens)) ?_ ?_
    · intro x
      have hx : x ∈ (⨆ l, (Ua l : X.Opens) : X.Opens) := by rw [hsup]; simp
      simpa using Opens.mem_iSup.mp hx
    · intro i
      rw [hτrest i]
      simp
  have hstage : D.map γ φq = D.map γ ψq := by
    rw [idealPowerHom_map_apply I F (by omega) φq,
      idealPowerHom_map_apply I F (by omega) ψq]
    change S.map γ.op ≫ φq = S.map γ.op ≫ ψq
    rw [← sub_eq_zero, ← Preadditive.comp_sub]
    exact hτ
  refine ⟨r, α ≫ γ, β ≫ γ, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact hstage

/-- The canonical map from the direct limit of ideal-power homomorphisms to sections over the
complement of the ideal's closed subscheme is injective. -/
theorem canonicalMapToSections_injective {X : Scheme.{u}} [CompactSpace X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules).IsFiniteType] :
    Function.Injective (canonicalMapToSections I F).1 := by
  intro x y hxy
  let D := idealPowerHom I (SheafOfModules.unit X.ringCatSheaf) F
  obtain ⟨n, φ, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit D) x
  obtain ⟨m, ψ, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit D) y
  obtain ⟨r, f, g, hfg⟩ := exists_eventual_eq_of_canonicalMap_eq I F n m φ ψ hxy
  exact (colimit_eq_iff (F := D)).2 ⟨r, f, g, hfg⟩

end

end Stacks.Algebraization

end
