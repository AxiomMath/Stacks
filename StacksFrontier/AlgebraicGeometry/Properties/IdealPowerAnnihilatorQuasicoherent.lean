module

public import StacksFrontier.AlgebraicGeometry.Properties.IdealPowerAnnihilator
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-coherence of the ideal-power annihilator subsheaf

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `I ⊆ 𝒪_X` a quasi-coherent sheaf of
ideals whose sections over every affine open form a finitely generated ideal.  This file proves
that the subsheaf `AlgebraicGeometry.idealPowerAnnihilator I F n` of sections locally
annihilated by `I ^ n` is quasi-coherent.  A locally Noetherian `X` is the special case in which
the finite generation is automatic.

## Main definitions

* `AlgebraicGeometry.sectionAnnihilator`: the ideal subsheaf of functions annihilating a fixed
  section of `F` after every restriction.
* `AlgebraicGeometry.submoduleModules`: a submodule subsheaf of an `𝒪_X`-module, bundled as an
  `𝒪_X`-module, with `submoduleVal` and `submoduleMk` naming the two directions of the
  identification of its sections with the sections of the ambient module that lie in it.
* `AlgebraicGeometry.idealSections`: the ideal of sections of an ideal subsheaf over an open.

## Main results

* `AlgebraicGeometry.mem_submodule_of_cover` and `AlgebraicGeometry.eq_zero_of_cover`: membership
  in a submodule subsheaf is local, and a section vanishing locally vanishes.
* `AlgebraicGeometry.exists_smul_eq_restrict_of_mem_sections_basicOpen`: a section of a
  quasi-coherent submodule subsheaf over a basic open of an affine open is a multiple of the
  restriction of a section over that affine open.
* `AlgebraicGeometry.pow_sections_le_idealPower` and
  `AlgebraicGeometry.smul_eq_zero_of_mem_idealPowerAnnihilator`: the sectionwise ideal power is
  contained in the sheaf-theoretic one, so a section of the annihilator subsheaf is killed by the
  sectionwise power.
* `AlgebraicGeometry.mem_idealPowerAnnihilator_of_smul_sections`: conversely, a section killed,
  after every restriction, by the `n`-th power of the *sections* of `I` lies in the annihilator
  subsheaf.
* `AlgebraicGeometry.mem_idealPowerAnnihilator_affine_iff`: over an affine open the annihilator
  subsheaf consists exactly of the sections killed by `I(U) ^ n`.
* `AlgebraicGeometry.isLocalizedModule_idealPowerAnnihilator`,
  `AlgebraicGeometry.idealPowerAnnihilator_isQuasicoherent_of_fg`,
  `AlgebraicGeometry.idealPowerAnnihilator_isQuasicoherent_of_fg_ideal` and
  `AlgebraicGeometry.idealPowerAnnihilator_isQuasicoherent`: the sections of the annihilator
  subsheaf localize on basic opens, hence the subsheaf is quasi-coherent — under finite
  generation of `I(U) ^ n`, of `I(U)`, and on a locally Noetherian scheme respectively.

## Implementation notes

`AlgebraicGeometry.idealPower I n` is a *least* ideal subsheaf, so it can only be bounded above
by exhibiting a member of the family it is the infimum of.  That member is
`AlgebraicGeometry.sectionAnnihilator`, the ideal subsheaf of functions annihilating a fixed
section after every restriction; it is what converts the defining condition of the annihilator
subsheaf, which quantifies over the sheaf-theoretic ideal powers, into the sectionwise condition
of `mem_idealPowerAnnihilator_affine_iff`.

Quasi-coherence of a subsheaf cannot be read off a presentation, so it is checked through the
localization criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
exactly as for the torsion subsheaf: it suffices that over each basic open `X.basicOpen a` of an
affine open `U` the annihilator sections are the localization away from `a` of the annihilator
sections over `U`.  Of the four conditions of `IsLocalizedModule.Away.mk_of_addCommGroup`, three
are inherited from `F` because the annihilator is a subobject and because `a` is invertible on
`X.basicOpen a`.  The fourth, surjectivity up to powers of `a`, is the only place a hypothesis is
needed beyond quasi-coherence: a preimage in `Γ(F, U)` of an annihilator section has each
generator of `I(U) ^ n` killing it only after multiplication by some power of `a`, and finitely
many generators are needed to make that power uniform.  Hence the hypothesis that `I(U) ^ n` is
finitely generated; it follows from finite generation of `I(U)` by `Ideal.FG.pow`, so an ideal
sheaf of finite type suffices.

The finite-type version of this result, for ideal-sheaf *data* rather than for a submodule of the
structure sheaf, is
`Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_annihilatorModule_of_fg`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 0AXT](https://stacks.math.columbia.edu/tag/0AXT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The annihilator ideal subsheaf of a section -/

/-- The presheaf-level ideal of functions annihilating a fixed section `s` of `F` over `V`:
over an open `W`, those functions whose restriction to any open contained in both `W` and `V`
annihilates the corresponding restriction of `s`. -/
noncomputable def sectionAnnihilatorSubmodule (F : X.Modules) {V : X.Opens} (s : Γ(F, V)) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).val.Submodule where
  obj := fun W ↦
    { carrier := {b | ∀ (W' : (Opens X)ᵒᵖ) (f : W ⟶ W') (g : op V ⟶ W'),
        (X.ringCatSheaf.obj.map f).hom b • F.val.presheaf.map g s = 0}
      zero_mem' := by
        intro W' f g
        exact (congrArg (fun z ↦ z • F.val.presheaf.map g s)
          (map_zero (X.ringCatSheaf.obj.map f).hom)).trans (zero_smul _ _)
      add_mem' := by
        intro x y hx hy W' f g
        exact ((congrArg (fun z ↦ z • F.val.presheaf.map g s)
            (map_add (X.ringCatSheaf.obj.map f).hom x y)).trans (add_smul _ _ _)).trans
          ((congrArg₂ (· + ·) (hx W' f g) (hy W' f g)).trans (add_zero 0))
      smul_mem' := by
        intro r x hx W' f g
        exact ((congrArg (fun z ↦ z • F.val.presheaf.map g s)
            (map_mul (X.ringCatSheaf.obj.map f).hom r x)).trans (mul_smul _ _ _)).trans
          ((congrArg (fun z ↦ (X.ringCatSheaf.obj.map f).hom r • z)
            (hx W' f g)).trans (smul_zero _)) }
  map := by
    intro W Y f b hb W' f' g
    have hcomp : (X.ringCatSheaf.obj.map f').hom ((X.ringCatSheaf.obj.map f).hom b) =
        (X.ringCatSheaf.obj.map (f ≫ f')).hom b :=
      (congrArg (fun φ : X.ringCatSheaf.obj.obj W ⟶ X.ringCatSheaf.obj.obj W' ↦ φ.hom b)
        (X.ringCatSheaf.obj.map_comp f f')).symm
    exact (congrArg (fun z ↦ z • F.val.presheaf.map g s) hcomp).trans (hb W' (f ≫ f') g)

/-- The ideal subsheaf of `𝒪_X` of functions annihilating a fixed section `s` of `F` after every
restriction. -/
noncomputable def sectionAnnihilator (F : X.Modules) {V : X.Opens} (s : Γ(F, V)) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule where
  toSubmodule := sectionAnnihilatorSubmodule F s
  isSheaf := by
    intro W b hb W' f g
    let N := sectionAnnihilatorSubmodule F s
    let S := N.toSubfunctor.sieveOfSection b
    have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
        (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf F))
    refine (hF (S.pullback f.unop)
      ((Opens.grothendieckTopology X).pullback_stable f.unop hb)).isSeparatedFor.ext ?_
    intro Y h hh
    change F.val.restrictₛₗ h.op
      ((X.ringCatSheaf.obj.map f).hom b • F.val.presheaf.map g s) =
      F.val.restrictₛₗ h.op 0
    rw [map_zero]
    refine ((F.val.restrictₛₗ h.op).map_smulₛₗ _ _).trans ?_
    change (X.ringCatSheaf.obj.map h.op).hom ((X.ringCatSheaf.obj.map f).hom b) •
      F.val.presheaf.map h.op (F.val.presheaf.map g s) = 0
    have hmem : (X.ringCatSheaf.obj.map ((h ≫ f.unop).op)).hom b ∈ N.obj (op Y) := hh
    have key := hmem (op Y) (𝟙 (op Y)) (g ≫ h.op)
    have hid : ∀ z : X.ringCatSheaf.obj.obj (op Y),
        (X.ringCatSheaf.obj.map (𝟙 (op Y))).hom z = z := fun z ↦ by simp
    rw [hid] at key
    have hring : (X.ringCatSheaf.obj.map ((h ≫ f.unop).op)).hom b =
        (X.ringCatSheaf.obj.map h.op).hom ((X.ringCatSheaf.obj.map f).hom b) := by
      rw [show ((h ≫ f.unop).op : W ⟶ op Y) = f ≫ h.op from by simp, Functor.map_comp]
      rfl
    have hFres : F.val.presheaf.map (g ≫ h.op) s =
        F.val.presheaf.map h.op (F.val.presheaf.map g s) := by
      rw [Functor.map_comp]
      rfl
    rwa [hring, hFres] at key

/-- Membership in the annihilator ideal subsheaf of a section, by definition. -/
lemma mem_sectionAnnihilator (F : X.Modules) {V : X.Opens} (s : Γ(F, V))
    {W : (Opens X)ᵒᵖ} (b : (SheafOfModules.unit.{u} X.ringCatSheaf).val.obj W) :
    b ∈ (sectionAnnihilator F s).toSubmodule.obj W ↔
      ∀ (W' : (Opens X)ᵒᵖ) (f : W ⟶ W') (g : op V ⟶ W'),
        (X.ringCatSheaf.obj.map f).hom b • F.val.presheaf.map g s = 0 :=
  Iff.rfl

/-- An element of the annihilator ideal of `s` over `W` kills every restriction of `s` to `W`. -/
private theorem smul_map_eq_zero_of_mem_sectionAnnihilator (F : X.Modules) {V : X.Opens}
    (s : Γ(F, V)) {W : (Opens X)ᵒᵖ} {b : X.ringCatSheaf.obj.obj W}
    (hb : b ∈ (sectionAnnihilator F s).toSubmodule.obj W) (g : op V ⟶ W) :
    b • F.val.presheaf.map g s = 0 := by
  have key := hb W (𝟙 W) g
  rwa [show (X.ringCatSheaf.obj.map (𝟙 W)).hom b = b by simp] at key

/-! ### Sections of a submodule subsheaf -/

/-- A submodule subsheaf of an `𝒪_X`-module, bundled as an `𝒪_X`-module.  The type `X.Modules`
does not unfold at instance-reducible transparency, so without this bundling the module
structure on the sections of the subsheaf is not found by instance search. -/
noncomputable def submoduleModules {M : X.Modules} (H : M.Submodule) : X.Modules :=
  H.toSheafOfModules

/-- The underlying section of `M` of a section of a submodule subsheaf. -/
noncomputable def submoduleVal {M : X.Modules} (H : M.Submodule) {W : X.Opens}
    (z : Γ(submoduleModules H, W)) : Γ(M, W) :=
  z.1

/-- A section of `M` lying in a submodule subsheaf, viewed as a section of that subsheaf. -/
noncomputable def submoduleMk {M : X.Modules} (H : M.Submodule) {W : X.Opens} (t : Γ(M, W))
    (ht : t ∈ H.toSubmodule.obj (op W)) : Γ(submoduleModules H, W) :=
  show ↥(H.toSubmodule.obj (op W)) from ⟨t, ht⟩

/-- The underlying section of a section of a submodule subsheaf lies in that subsheaf. -/
theorem submoduleVal_mem {M : X.Modules} (H : M.Submodule) {W : X.Opens}
    (z : Γ(submoduleModules H, W)) : submoduleVal H z ∈ H.toSubmodule.obj (op W) :=
  z.2

/-- Sections of a submodule subsheaf are determined by their underlying sections of `M`. -/
theorem submoduleVal_injective {M : X.Modules} (H : M.Submodule) {W : X.Opens}
    {z₁ z₂ : Γ(submoduleModules H, W)} (h : submoduleVal H z₁ = submoduleVal H z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Equal sections of a submodule subsheaf have equal underlying sections. -/
theorem submoduleVal_congr {M : X.Modules} (H : M.Submodule) {W : X.Opens}
    {z₁ z₂ : Γ(submoduleModules H, W)} (h : z₁ = z₂) :
    submoduleVal H z₁ = submoduleVal H z₂ := by
  rw [h]

/-- A section of `M` lying in a submodule subsheaf, viewed in the subsheaf, has itself as its
underlying section. -/
@[simp]
theorem submoduleVal_mk {M : X.Modules} (H : M.Submodule) {W : X.Opens} (t : Γ(M, W))
    (ht : t ∈ H.toSubmodule.obj (op W)) : submoduleVal H (submoduleMk H t ht) = t :=
  rfl

/-- Taking the underlying section of a section of a submodule subsheaf commutes with
restriction to a smaller open. -/
@[simp]
theorem submoduleVal_restrictₗ {M : X.Modules} (H : M.Submodule) {W W' : X.Opens} (h : W ≤ W')
    (z : Γ(submoduleModules H, W')) :
    submoduleVal H (restrictₗ (submoduleModules H) h z) = restrictₗ M h (submoduleVal H z) :=
  rfl

/-- **Sections of a quasi-coherent subsheaf over a basic open come from the affine open.**
Every section of a quasi-coherent submodule subsheaf over `X.basicOpen a` is a multiple of the
restriction of a section of that subsheaf over the affine open `U`. -/
theorem exists_smul_eq_restrict_of_mem_sections_basicOpen (M : X.Modules) [M.IsQuasicoherent]
    (H : M.Submodule) [H.toSheafOfModules.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U)) {c : Γ(M, X.basicOpen a)}
    (hc : c ∈ H.toSubmodule.obj (op (X.basicOpen a))) :
    ∃ (v : Γ(X, X.basicOpen a)) (y : Γ(M, U)), y ∈ H.toSubmodule.obj (op U) ∧
      c = v • M.presheaf.map (homOfLE (X.basicOpen_le a)).op y := by
  let Hm : X.Modules := submoduleModules H
  have hHq : Hm.IsQuasicoherent := inferInstanceAs H.toSheafOfModules.IsQuasicoherent
  let := moduleOfLE Hm (X.basicOpen_le a)
  let := moduleOfLE M (X.basicOpen_le a)
  have hloc : IsLocalizedModule.Away a (restrictₗ Hm (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ Hm hU a rfl (X.basicOpen_le a)
  obtain ⟨k, x₀, hx₀⟩ :=
    IsLocalizedModule.Away.surj (restrictₗ Hm (X.basicOpen_le a)) a (submoduleMk H c hc)
  have hval : restrictₗ M (X.basicOpen_le a) (submoduleVal H x₀) =
      X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ k) • c := by
    have h := submoduleVal_congr H hx₀
    rw [submoduleVal_restrictₗ] at h
    rw [← h]
    rfl
  obtain ⟨u, hu⟩ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ k)) := by
    have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
      X.toRingedSpace.isUnit_res_basicOpen a
    simpa only [map_pow] using h1.pow k
  refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen a)), submoduleVal H x₀, submoduleVal_mem H x₀, ?_⟩
  rw [show M.presheaf.map (homOfLE (X.basicOpen_le a)).op (submoduleVal H x₀) =
    restrictₗ M (X.basicOpen_le a) (submoduleVal H x₀) from rfl, hval, ← hu, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-! ### Locality of membership in a submodule subsheaf -/

/-- **Membership in a submodule subsheaf is local.** A section lying, after restriction, in the
subsheaf over an open neighbourhood of each point of its domain lies in it already. -/
theorem mem_submodule_of_cover {M : SheafOfModules.{u} X.ringCatSheaf} (N : M.Submodule)
    (U : X.Opens) (t : M.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      M.val.map (homOfLE hV).op t ∈ N.toSubmodule.obj (op V)) :
    t ∈ N.toSubmodule.obj (op U) := by
  apply N.isSheaf
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V, hV, hxV, hmem⟩ := h x hx
  exact ⟨V, homOfLE hV, hmem, hxV⟩

/-- A section of an `𝒪_X`-module vanishing on an open neighbourhood of each point of its domain
vanishes. -/
theorem eq_zero_of_cover (F : X.Modules) {U : X.Opens} (t : Γ(F, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      F.presheaf.map (homOfLE hV).op t = 0) :
    t = 0 := by
  have h1 : (1 : X.ringCatSheaf.obj.obj (op U)) ∈
      (sectionAnnihilator F t).toSubmodule.obj (op U) := by
    refine mem_submodule_of_cover _ U _ fun x hx ↦ ?_
    obtain ⟨V, hV, hxV, hzero⟩ := h x hx
    refine ⟨V, hV, hxV, fun W' f g ↦ ?_⟩
    have hgf : F.val.presheaf.map g t = 0 := by
      rw [Subsingleton.elim g ((homOfLE hV).op ≫ f), Functor.map_comp]
      show F.val.presheaf.map f (F.presheaf.map (homOfLE hV).op t) = 0
      rw [hzero]
      exact map_zero (ConcreteCategory.hom (F.val.presheaf.map f))
    rw [hgf, smul_zero]
  have key := smul_map_eq_zero_of_mem_sectionAnnihilator F t h1 (𝟙 (op U))
  have hidF : F.val.presheaf.map (𝟙 (op U)) t = t := by
    simp only [CategoryTheory.Functor.map_id]
    rfl
  rw [hidF] at key
  exact (one_smul Γ(X, U) t).symm.trans key

/-! ### The sheaf-theoretic and the sectionwise annihilation conditions -/

/-- The ideal of sections of an ideal subsheaf `I` over an open `V`, as an ideal of `Γ(X, V)`. -/
noncomputable abbrev idealSections (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    (V : X.Opens) : Ideal Γ(X, V) :=
  I.toSubmodule.obj (op V)

/-- Restriction carries the `n`-th power of the ideal of sections of an ideal subsheaf into the
`n`-th power of its ideal of sections over a smaller open. -/
theorem map_mem_pow_sections (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (n : ℕ)
    {V W : X.Opens} (h : W ≤ V) {b : Γ(X, V)} (hb : b ∈ idealSections I V ^ n) :
    X.presheaf.map (homOfLE h).op b ∈ idealSections I W ^ n := by
  have hle : Ideal.map (X.presheaf.map (homOfLE h).op).hom (idealSections I V) ≤
      idealSections I W :=
    Ideal.map_le_iff_le_comap.mpr fun x hx ↦ I.toSubmodule.map (homOfLE h).op hx
  have hmem := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE h).op).hom hb
  rw [Ideal.map_pow] at hmem
  exact pow_le_pow_left' hle n hmem

/-- The `n`-th power of the ideal of sections of `I` over an open `V` is contained in the sections
over `V` of the sheaf-theoretic ideal power `I ^ n`. -/
theorem pow_sections_le_idealPower
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (n : ℕ) (V : (Opens X)ᵒᵖ) :
    (show Ideal Γ(X, V.unop) from I.toSubmodule.obj V) ^ n ≤
      (idealPower I n).toSubmodule.obj V := by
  show _ ≤ (sInf ((fun P : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule ↦ P.toSubmodule)
    '' { J : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule | ∀ W : (Opens X)ᵒᵖ,
      (show Ideal _ from I.toSubmodule.obj W) ^ n ≤ J.toSubmodule.obj W })).obj V
  rw [PresheafOfModules.Submodule.sInf_obj]
  refine le_iInf₂ fun P hP ↦ ?_
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact hQ V

/-- A section of `F` over `V` annihilated by the sheaf-theoretic `n`-th ideal power is annihilated
already by the `n`-th power of the ideal of sections of `I` over `V`. -/
theorem smul_eq_zero_of_mem_idealPowerAnnihilator
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ)
    (V : X.Opens) (s : Γ(F, V))
    (hs : s ∈ (idealPowerAnnihilator I F n).toSubmodule.obj (op V)) (a : Γ(X, V))
    (ha : a ∈ idealSections I V ^ n) :
    a • s = 0 := by
  have h := hs (op V) (𝟙 (op V)) a (pow_sections_le_idealPower I n (op V) ha)
  have hid : (ConcreteCategory.hom (F.val.presheaf.map (𝟙 (op V)))) s = s := by
    simp only [CategoryTheory.Functor.map_id]
    rfl
  rwa [hid] at h

/-- **The sectionwise annihilation condition suffices.** A section annihilated, after every
restriction, by the `n`-th power of the ideal of *sections* of `I` lies in the ideal-power
annihilator subsheaf.

The annihilator `AlgebraicGeometry.sectionAnnihilator` of the section is an ideal subsheaf
containing every sectionwise power `I(W) ^ n`, hence contains the least such subsheaf
`AlgebraicGeometry.idealPower I n`. -/
theorem mem_idealPowerAnnihilator_of_smul_sections
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ)
    {V : X.Opens} (s : Γ(F, V))
    (hs : ∀ (W : X.Opens) (hW : W ≤ V) (b : Γ(X, W)), b ∈ idealSections I W ^ n →
      b • F.presheaf.map (homOfLE hW).op s = 0) :
    s ∈ (idealPowerAnnihilator I F n).toSubmodule.obj (op V) := by
  have hle : idealPower I n ≤ sectionAnnihilator F s := by
    refine sInf_le ?_
    intro W b hb W' f g
    have hf : (homOfLE (f.unop.le : W'.unop ≤ W.unop)).op = f := Subsingleton.elim _ _
    have hg : (homOfLE (g.unop.le : W'.unop ≤ V)).op = g := Subsingleton.elim _ _
    have key := hs W'.unop g.unop.le
      (X.presheaf.map (homOfLE (f.unop.le : W'.unop ≤ W.unop)).op b)
      (map_mem_pow_sections I n _ hb)
    rwa [hf, hg] at key
  intro W f a ha
  exact smul_map_eq_zero_of_mem_sectionAnnihilator F s
    (SheafOfModules.Submodule.le_iff.mp hle W ha) f

/-- **The ideal-power annihilator over an affine open.** Over an affine open `U` the annihilator
subsheaf consists exactly of the sections of `F` killed by the `n`-th power of the ideal
`I(U)`.

The nontrivial direction is that killing `I(U) ^ n` already forces the sheaf-theoretic condition
over every open contained in `U`.  That condition is local, and over a basic open `X.basicOpen a`
of `U` the ideal `I(X.basicOpen a)` consists of multiples of restrictions of elements of `I(U)`,
because `I` is quasi-coherent. -/
theorem mem_idealPowerAnnihilator_affine_iff
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) (n : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(F, U)) :
    s ∈ (idealPowerAnnihilator I F n).toSubmodule.obj (op U) ↔
      ∀ b ∈ idealSections I U ^ n, b • s = 0 := by
  refine ⟨fun hs b hb ↦ smul_eq_zero_of_mem_idealPowerAnnihilator I F n U s hs b hb, fun hs ↦ ?_⟩
  refine mem_idealPowerAnnihilator_of_smul_sections I F n s fun W hW b hb ↦ ?_
  refine eq_zero_of_cover F _ fun x hx ↦ ?_
  obtain ⟨a, haW, hxa⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hW hx)
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have hres : F.presheaf.map (homOfLE haW).op (F.presheaf.map (homOfLE hW).op s) =
      F.presheaf.map (homOfLE (X.basicOpen_le a)).op s := by
    rw [Subsingleton.elim (homOfLE (X.basicOpen_le a) : X.basicOpen a ⟶ U).op
      ((homOfLE hW).op ≫ (homOfLE haW).op), Functor.map_comp]
    rfl
  have hsmul : F.presheaf.map (homOfLE haW).op
        (b • F.presheaf.map (homOfLE hW).op s) =
      X.presheaf.map (homOfLE haW).op b •
        F.presheaf.map (homOfLE (X.basicOpen_le a)).op s := by
    rw [← hres]
    exact F.map_smul (homOfLE haW) b _
  rw [hsmul]
  have hmap : idealSections I (X.basicOpen a) ≤
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (idealSections I U) := by
    intro c hc
    obtain ⟨v, y, hy, hcv⟩ := exists_smul_eq_restrict_of_mem_sections_basicOpen
      (SheafOfModules.unit.{u} X.ringCatSheaf) I hU a hc
    rw [hcv]
    exact Submodule.smul_mem _ v
      (Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom hy)
  have hann : Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
        (idealSections I U ^ n) ≤
      (Submodule.span Γ(X, X.basicOpen a)
        {F.presheaf.map (homOfLE (X.basicOpen_le a)).op s}).annihilator := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_
    rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton]
    have hsm := F.map_smul (homOfLE (X.basicOpen_le a)) y s
    rw [hs y hy] at hsm
    exact hsm.symm.trans (map_zero _)
  have hpow := pow_le_pow_left' hmap n
  rw [← Ideal.map_pow] at hpow
  exact (Submodule.mem_annihilator_span_singleton _ _).mp
    (hann (hpow (map_mem_pow_sections I n haW hb)))

/-! ### Quasi-coherence of the annihilator subsheaf -/

/-- The sections of the ideal-power annihilator subsheaf over `X.basicOpen a` are the
localization away from `a` of its sections over an affine open `U`.

Three of the four conditions are inherited from `F`.  The fourth, surjectivity up to powers of
`a`, is where the Noetherian hypothesis enters: a preimage in `Γ(F, U)` of an annihilator section
is killed by each generator of `I(U) ^ n` only after multiplication by some power of `a`, and
finitely many generators make that power uniform. -/
theorem isLocalizedModule_idealPowerAnnihilator
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) (hFG : (idealSections I U ^ n).FG) (a : Γ(X, U)) :
    letI := moduleOfLE (submoduleModules (idealPowerAnnihilator I F n)) (X.basicOpen_le a)
    IsLocalizedModule.Away a
      (restrictₗ (submoduleModules (idealPowerAnnihilator I F n)) (X.basicOpen_le a)) := by
  classical
  have hDa : IsAffineOpen (X.basicOpen a) := hU.basicOpen a
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  set H := idealPowerAnnihilator I F n with hH
  let := moduleOfLE (submoduleModules H) (X.basicOpen_le a)
  let := moduleOfLE F (X.basicOpen_le a)
  have hloc : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨hFinj, hFsurj⟩ :=
    smul_bijective_of_isLocalizedModule (restrictₗ F (X.basicOpen_le a)) a
  have hkill0 : ∀ x : Γ(F, U), restrictₗ F (X.basicOpen_le a) x = 0 → ∃ m : ℕ, a ^ m • x = 0 :=
    fun x hx ↦ (IsLocalizedModule.Away.exists_of_eq a (hx.trans (map_zero _).symm)).imp
      fun m hm ↦ by rw [hm, smul_zero]
  have hann : ∀ (y : Γ(submoduleModules H, X.basicOpen a)) (b : Γ(X, X.basicOpen a)),
      b ∈ idealSections I (X.basicOpen a) ^ n → b • submoduleVal H y = 0 := fun y b hb ↦
    smul_eq_zero_of_mem_idealPowerAnnihilator I F n (X.basicOpen a) _ (submoduleVal_mem H y) b hb
  refine IsLocalizedModule.Away.mk_of_addCommGroup (isUnit_algebraMap_end ?_ ?_) ?_ ?_
  · exact fun y₁ y₂ hy ↦ submoduleVal_injective H (hFinj _ _ (submoduleVal_congr H hy))
  · intro y
    obtain ⟨w, hw⟩ := hFsurj (submoduleVal H y)
    have hwmem : w ∈ H.toSubmodule.obj (op (X.basicOpen a)) := by
      refine (mem_idealPowerAnnihilator_affine_iff I F n hDa w).mpr fun b hb ↦ ?_
      have hy := hann y b hb
      have hvy : submoduleVal H y =
          X.presheaf.map (homOfLE (X.basicOpen_le a)).op a • w := hw.symm
      rw [hvy, smul_smul, mul_comm, ← smul_smul] at hy
      exact eq_zero_of_isUnit_smul_eq_zero hunit hy
    exact ⟨submoduleMk H w hwmem, submoduleVal_injective H hw⟩
  · intro y
    obtain ⟨k, x₀, hx₀⟩ :=
      IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le a)) a (submoduleVal H y)
    obtain ⟨T, hT⟩ : (idealSections I U ^ n).FG := hFG
    have hTmem : ∀ t ∈ T, t ∈ idealSections I U ^ n := fun t ht ↦
      hT ▸ Submodule.subset_span ht
    have hkill : ∀ t ∈ T, ∃ m : ℕ, a ^ m • (t • x₀) = 0 := by
      intro t ht
      apply hkill0
      rw [map_smul, ← hx₀, smul_smul, mul_comm t (a ^ k), ← smul_smul]
      change a ^ k • (X.presheaf.map (homOfLE (X.basicOpen_le a)).op t • submoduleVal H y) = 0
      rw [hann y _ (map_mem_pow_sections I n (X.basicOpen_le a) (hTmem t ht)), smul_zero]
    choose mt hmt using hkill
    set m := T.attach.sup (fun t ↦ mt t.1 t.2) with hm
    have hmem : a ^ m • x₀ ∈ H.toSubmodule.obj (op U) := by
      refine (mem_idealPowerAnnihilator_affine_iff I F n hU _).mpr ?_
      have hgen : ∀ t ∈ T, t • (a ^ m • x₀) = 0 := by
        intro t ht
        have hle : mt t ht ≤ m :=
          Finset.le_sup (f := fun t : { x // x ∈ T } ↦ mt t.1 t.2)
            (Finset.mem_attach T ⟨t, ht⟩)
        have hsplit : t * a ^ m = a ^ (m - mt t ht) * (a ^ mt t ht * t) := by
          rw [show (a : Γ(X, U)) ^ m = a ^ (m - mt t ht) * a ^ mt t ht from by
            rw [← pow_add, Nat.sub_add_cancel hle]]
          ring
        rw [smul_smul, hsplit, ← smul_smul, ← smul_smul, hmt t ht, smul_zero]
      intro b hb
      rw [← hT] at hb
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · exact fun t ht ↦ hgen t (Finset.mem_coe.mp ht)
      · exact zero_smul _ _
      · intro c d _ _ hc hd
        rw [add_smul, hc, hd, add_zero]
      · intro c d _ hd
        rw [smul_eq_mul, mul_smul, hd, smul_zero]
    refine ⟨k + m, submoduleMk H (a ^ m • x₀) hmem, submoduleVal_injective H ?_⟩
    show a ^ (k + m) • submoduleVal H y = restrictₗ F (X.basicOpen_le a) (a ^ m • x₀)
    rw [map_smul, ← hx₀, smul_smul, ← pow_add, add_comm m k]
  · intro z hz
    obtain ⟨m, hmz⟩ := hkill0 (submoduleVal H z) (by
      change submoduleVal H (restrictₗ (submoduleModules H) (X.basicOpen_le a) z) = 0
      rw [hz]
      rfl)
    exact ⟨m, submoduleVal_injective H hmz⟩

/-- **The ideal-power annihilator subsheaf of Stacks tag 01PQ is quasi-coherent**, for a
quasi-coherent sheaf of ideals `I` whose `n`-th power is of finite type on every affine open. -/
theorem idealPowerAnnihilator_isQuasicoherent_of_fg
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hFG : ∀ U : X.Opens, IsAffineOpen U → (idealSections I U ^ n).FG) :
    (idealPowerAnnihilator I F n).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ
    (submoduleModules (idealPowerAnnihilator I F n))
    fun U hU a ↦ isLocalizedModule_idealPowerAnnihilator I F n hU (hFG U hU) a

/-- **The ideal-power annihilator subsheaf of Stacks tag 01PQ is quasi-coherent for an ideal
sheaf of finite type.** For a quasi-coherent `𝒪_X`-module `F` and a quasi-coherent sheaf of
ideals `I` whose sections over every affine open form a finitely generated ideal, the subsheaf
of sections annihilated by `I ^ n` is quasi-coherent. -/
theorem idealPowerAnnihilator_isQuasicoherent_of_fg_ideal
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hFG : ∀ U : X.Opens, IsAffineOpen U → (idealSections I U).FG) :
    (idealPowerAnnihilator I F n).toSheafOfModules.IsQuasicoherent :=
  idealPowerAnnihilator_isQuasicoherent_of_fg I F n fun U hU ↦ (hFG U hU).pow

/-- **The ideal-power annihilator subsheaf of Stacks tag 01PQ is quasi-coherent.** On a locally
Noetherian scheme, for a quasi-coherent `𝒪_X`-module `F` and a quasi-coherent sheaf of ideals
`I`, the subsheaf of sections annihilated by `I ^ n` is quasi-coherent.

This is the hypothesis that `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq` (tag 01YA) requires
of the subsheaf it is applied to in the Artin–Rees separation step of tag 01YB. -/
instance idealPowerAnnihilator_isQuasicoherent [IsLocallyNoetherian X]
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (idealPowerAnnihilator I F n).toSheafOfModules.IsQuasicoherent :=
  idealPowerAnnihilator_isQuasicoherent_of_fg I F n fun U hU ↦
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    IsNoetherian.noetherian _

end AlgebraicGeometry
