module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QcqsLocalization
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# The colimit of `Hom(Iⁿ, F)` injects into the sections away from `V(I)`

Let `X` be a quasi-compact scheme, let `I` be a quasi-coherent sheaf of ideals of finite type,
let `Z` be the closed subscheme it defines and let `U = X \ Z`. For a quasi-coherent
`𝒪_X`-module `F` this file builds the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F) ⟶ Γ(U, F)`

and proves it injective. This is the *first* assertion of Tag 01PQ.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow`: `Iⁿ` as a sheaf of modules on `X`,
  namely `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n 𝒪_X`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.oneSection`: the unit section of `Iⁿ` over the
  complement of the support of `I`, where `Iⁿ` restricts to the whole structure sheaf.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowHomSystem`: the direct system
  `n ↦ Hom(Iⁿ, F)`, with transition maps given by precomposition with the inclusions
  `I^(n+1) ⟶ Iⁿ`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSections`: the canonical map out of
  the colimit of that system, obtained from the cocone `φ ↦ φ(1)` on the complement of the
  support.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.killIdeal`: for an affine open `V`, the ideal of
  those sections of `Iⁿ` over `V` that `φ` sends to zero.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSections_injective`: the canonical
  map is injective.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero`: a `φ : Iⁿ ⟶ F` whose
  section over `U` vanishes already vanishes on `I^(n+N)` for some `N`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_pow_le_killIdeal`: the affine case, which
  is Tag 01PM transported to a scheme.

## Implementation notes

**Which `Iⁿ`.** The tree carries two unrelated encodings of the powers of an ideal sheaf:
`AlgebraicGeometry.idealPower`, an order homomorphism `ℕᵒᵈ →o (SheafOfModules.unit
X.ringCatSheaf).Submodule` defined as an infimum over *all* opens, and
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, a submodule of an arbitrary sheaf of
modules defined as an infimum over the *affine* opens of `X` for an
`AlgebraicGeometry.Scheme.IdealSheafData`. This file uses the latter, because it is the only one
whose sections can be computed: `idealPowerMultiple_obj_affineOpen` identifies the sections over
an affine open `V` with `I(V)ⁿ`, which is what makes the affine statement Tag 01PM applicable, and
`idealPowerMultiple_obj_eq_top_of_disjoint_support` identifies the restriction to the complement
of the support with the whole structure sheaf, which is what defines the canonical map at all.
`idealPower` has neither computation, and its domain carries no quasi-coherence and no support.

That `idealPow I n` really is the `n`-th power of `I` as a quasi-coherent ideal sheaf — and not
merely some subsheaf squeezed between `Iⁿ` and `𝒪_X` — is recorded by
`obj_idealPow_affineOpen_eq_ideal_pow`, which identifies its sections over an affine open with
`(I ^ n).ideal V` for Mathlib's own `Pow` on `X.IdealSheafData`.

**Finite type.** The hypothesis is spelled out as `∀ V : X.affineOpens, (I.ideal V).FG` rather
than through a predicate.

**No Hom comparison.** Rather than an equivalence `Hom_{𝒪_W}(Iⁿ|_W, F|_W) ≅ Hom_A(I(W)ⁿ, M)` on
an affine open `W`, `homOnIdealPow` reads off the `A`-linear map `I(W)ⁿ → M` directly from the
sections of `φ` over `W`, and the vanishing of a section of `F` over `W` on `D(f)` is turned into
its annihilation by a power of `f` through
`Stacks.AlgebraicGeometry.QcqsLocalization.exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact`.

**Kernel cost.** `val_subInclusion_app` is stated for an arbitrary pair of submodules rather
than for `idealPowMap` directly. Specialised to `idealPowerMultiple` the same `rfl` makes the
kernel unfold the defining `sInf`, which does not terminate within the heartbeat budget; with
the submodules kept as variables there is nothing to unfold.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM) (the affine case)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The structure sheaf and subsheaves as objects of `X.Modules` -/

/-- The structure sheaf of `X`, as a sheaf of modules over itself. -/
noncomputable abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The structure sheaf of `X` is quasi-coherent. -/
local instance instIsQuasicoherentStructureModule (X : Scheme.{u}) :
    (structureModule X).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X

/-- A subsheaf of a sheaf of modules, as an object of `X.Modules`. -/
noncomputable abbrev subMod {M : X.Modules} (N : M.Submodule) : X.Modules :=
  N.toSheafOfModules

/-- The inclusion of one subsheaf of a sheaf of modules into a larger one. -/
noncomputable abbrev subInclusion {M : X.Modules} {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    subMod N₁ ⟶ subMod N₂ :=
  SheafOfModules.Submodule.homOfLE hle

/-- An inclusion of subsheaves does not change the value of a section. -/
theorem val_subInclusion_app {M : X.Modules} {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂)
    (V : X.Opens) (z : Γ(subMod N₁, V)) :
    (((subInclusion hle).app V z).1 : Γ(M, V)) = (z.1 : Γ(M, V)) := rfl

/-- The inclusion of a subsheaf into itself is the identity. -/
theorem subInclusion_refl {M : X.Modules} (N : M.Submodule) :
    subInclusion (le_refl N) = 𝟙 (subMod N) := by
  ext V z
  exact Subtype.ext (val_subInclusion_app (le_refl N) V z)

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U x)
      = φ.app V (M.presheaf.map (homOfLE h).op x) :=
  (congr($(φ.mapPresheaf.naturality (homOfLE h).op) x)).symm

/-- A morphism of sheaves of modules sends the restriction of a section it kills to zero. -/
private theorem app_restrict_eq_zero {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    {x : Γ(M, U)} (hx : φ.app U x = 0) :
    φ.app V (M.presheaf.map (homOfLE h).op x) = 0 := by
  rw [← app_naturality, hx, map_zero]

/-! ### `Iⁿ` as a sheaf of modules -/

/-- `Iⁿ` as a sheaf of modules on `X`. -/
noncomputable abbrev idealPow (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  subMod (idealPowerMultiple I n (structureModule X))

/-- The inclusion `I^m ⟶ Iⁿ` for `n ≤ m`. -/
noncomputable abbrev idealPowMap (I : X.IdealSheafData) {n m : ℕ} (h : n ≤ m) :
    idealPow I m ⟶ idealPow I n :=
  idealPowerMultipleMap I (structureModule X) h

/-- The sections of `Iⁿ` over an affine open `V` are `I(V)ⁿ`. -/
theorem obj_idealPow_affineOpen (I : X.IdealSheafData) (n : ℕ) (V : X.affineOpens) :
    (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1)
      = (I.ideal V ^ n : Ideal Γ(X, V.1)) := by
  rw [idealPowerMultiple_obj_affineOpen I n (structureModule X) V]
  change (I.ideal V ^ n) • (⊤ : Ideal Γ(X, V.1)) = _
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- `idealPow I n` is the `n`-th power of `I` in the sense of Mathlib's `Pow` on
`AlgebraicGeometry.Scheme.IdealSheafData`. -/
theorem obj_idealPow_affineOpen_eq_ideal_pow (I : X.IdealSheafData) (n : ℕ)
    (V : X.affineOpens) :
    (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1)
      = ((I ^ n).ideal V : Ideal Γ(X, V.1)) :=
  (obj_idealPow_affineOpen I n V).trans (Scheme.IdealSheafData.ideal_pow I n ▸ rfl)

/-- The value of a restricted section of `Iⁿ` is the restriction of its value. -/
theorem val_map_idealPow (I : X.IdealSheafData) (m : ℕ) {V W : X.Opens} (h : W ≤ V)
    (t : Γ(idealPow I m, V)) :
    (((idealPow I m).presheaf.map (homOfLE h).op t).1 : Γ(X, W))
      = X.presheaf.map (homOfLE h).op (t.1 : Γ(X, V)) := rfl

/-- The inclusion `I^m ⟶ Iⁿ` does not change the value of a section. -/
theorem val_idealPowMap_app (I : X.IdealSheafData) {n m : ℕ} (h : n ≤ m) (V : X.Opens)
    (t : Γ(idealPow I m, V)) :
    (((idealPowMap I h).app V t).1 : Γ(X, V)) = (t.1 : Γ(X, V)) :=
  val_subInclusion_app (idealPowerMultiple_antitone I (structureModule X) h) V t

/-- The inclusion `Iⁿ ⟶ Iⁿ` is the identity. -/
theorem idealPowMap_refl (I : X.IdealSheafData) (n : ℕ) :
    idealPowMap I (le_refl n) = 𝟙 (idealPow I n) :=
  subInclusion_refl _

/-- The inclusions `I^k ⟶ I^m ⟶ Iⁿ` compose to the inclusion `I^k ⟶ Iⁿ`. -/
theorem idealPowMap_comp (I : X.IdealSheafData) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    idealPowMap I h' ≫ idealPowMap I h = idealPowMap I (h.trans h') :=
  idealPowerMultipleMap_comp I (structureModule X) h h'

/-- Over the complement of the support of `I` the subsheaf `Iⁿ` is the whole structure sheaf,
so it has a unit section there. -/
noncomputable def oneSection (I : X.IdealSheafData) (n : ℕ) :
    Γ(idealPow I n, (I.support.compl : X.Opens)) :=
  ⟨(1 : Γ(X, (I.support.compl : X.Opens))), by
    rw [idealPowerMultiple_obj_eq_top_of_disjoint_support I n (structureModule X)
      (W := (I.support.compl : X.Opens)) disjoint_compl_left le_rfl]
    exact Submodule.mem_top⟩

/-- The inclusion `I^m ⟶ Iⁿ` sends the unit section of `I^m` to the unit section of `Iⁿ`. -/
theorem idealPowMap_app_oneSection (I : X.IdealSheafData) {n m : ℕ} (h : n ≤ m) :
    (idealPowMap I h).app (I.support.compl : X.Opens) (oneSection I m) = oneSection I n :=
  Subtype.ext
    (val_subInclusion_app (idealPowerMultiple_antitone I (structureModule X) h) _
      (oneSection I m))

/-! ### A morphism out of `Iⁿ`, read off on sections -/

variable {I : X.IdealSheafData} {n : ℕ} {F : X.Modules}

/-- A morphism `Iⁿ ⟶ F`, as a linear map on the sections over an open. -/
noncomputable def homSections (φ : idealPow I n ⟶ F) (V : X.Opens) :
    Γ(idealPow I n, V) →ₗ[Γ(X, V)] Γ(F, V) where
  toFun s := φ.app V s
  map_add' s t := map_add (ConcreteCategory.hom (φ.app V)) s t
  map_smul' r s := Scheme.Modules.Hom.app_smul φ r s

/-- `homSections φ V` evaluates `φ` on sections over `V`. -/
@[simp] theorem homSections_apply (φ : idealPow I n ⟶ F) (V : X.Opens)
    (s : Γ(idealPow I n, V)) : homSections φ V s = φ.app V s := rfl

/-- Over an affine open `V` with `A = Γ(X, V)` and `M = Γ(F, V)`, a morphism `Iⁿ ⟶ F` is an
`A`-linear map `I(V)ⁿ → M`. -/
noncomputable def homOnIdealPow (φ : idealPow I n ⟶ F) (V : X.affineOpens) :
    ↥(I.ideal V ^ n : Ideal Γ(X, V.1)) →ₗ[Γ(X, V.1)] Γ(F, V.1) :=
  (homSections φ V.1).comp
    (Submodule.inclusion (le_of_eq (obj_idealPow_affineOpen I n V).symm))

/-- `homOnIdealPow φ V` evaluates `φ` on the section of `Iⁿ` over `V` with value `a`. -/
@[simp] theorem homOnIdealPow_apply (φ : idealPow I n ⟶ F) (V : X.affineOpens)
    (a : Γ(X, V.1)) (ha : a ∈ (I.ideal V ^ n : Ideal Γ(X, V.1)))
    (ha' : a ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1)) :
    homOnIdealPow φ V ⟨a, ha⟩ = φ.app V.1 ⟨a, ha'⟩ := rfl

/-- The ideal of sections of `Iⁿ` over an affine open that `φ` annihilates. -/
noncomputable def killIdeal (φ : idealPow I n ⟶ F) (V : X.affineOpens) : Ideal Γ(X, V.1) :=
  Submodule.map (Submodule.subtype (I.ideal V ^ n : Ideal Γ(X, V.1)))
    (LinearMap.ker (homOnIdealPow φ V))

/-- An element lies in `killIdeal φ V` if and only if it lies in `I(V)ⁿ` and is sent to zero by
`φ`. -/
theorem mem_killIdeal_iff {φ : idealPow I n ⟶ F} {V : X.affineOpens} {a : Γ(X, V.1)} :
    a ∈ killIdeal φ V ↔
      ∃ ha : a ∈ (I.ideal V ^ n : Ideal Γ(X, V.1)), homOnIdealPow φ V ⟨a, ha⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨a, ha⟩, h, rfl⟩

/-- `φ` sends a section of `Iⁿ` over an affine open whose value lies in `killIdeal φ V` to
zero. -/
theorem app_eq_zero_of_mem_killIdeal {φ : idealPow I n ⟶ F} {V : X.affineOpens}
    {a : Γ(X, V.1)} (ha : a ∈ killIdeal φ V)
    (ha' : a ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1)) :
    φ.app V.1 ⟨a, ha'⟩ = 0 := by
  obtain ⟨h1, h2⟩ := mem_killIdeal_iff.mp ha
  exact (homOnIdealPow_apply φ V a h1 ha').symm.trans h2

/-- `φ` sends a section `z` of `Iⁿ` over an affine open `V` to zero when the value of `z` lies in
`killIdeal φ V`. -/
theorem app_eq_zero_of_val_mem_killIdeal {φ : idealPow I n ⟶ F} (V : X.affineOpens)
    (z : Γ(idealPow I n, V.1)) (hz : (z.1 : Γ(X, V.1)) ∈ killIdeal φ V) :
    φ.app V.1 z = 0 :=
  app_eq_zero_of_mem_killIdeal hz z.2

/-! ### The affine case -/

/-- A basic open of an affine open cut out by a section of `I` misses the support of `I`. -/
theorem basicOpen_le_compl_support (I : X.IdealSheafData) (V : X.affineOpens)
    {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) :
    X.basicOpen f ≤ (I.support.compl : X.Opens) := by
  intro x hx
  have hxV : x ∈ V.1 := X.basicOpen_le f hx
  have hz : x ∉ X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) := by
    rw [Scheme.mem_zeroLocus_iff]
    exact fun h ↦ h f hf hx
  exact fun h ↦ hz ((Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV).mp h)

/-- If the section of `F` over `X \ V(I)` attached to `φ` vanishes, then the section
`φ(fⁿ)` over an affine open `V` restricts to zero on `D(f)`, for every `f ∈ I(V)`. -/
theorem res_basicOpen_eq_zero [F.IsQuasicoherent] (φ : idealPow I n ⟶ F)
    (hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0)
    (V : X.affineOpens) {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) :
    F.presheaf.map (homOfLE (X.basicOpen_le f)).op
      (homOnIdealPow φ V ⟨f ^ n, Ideal.pow_mem_pow hf n⟩) = 0 := by
  have hDU : X.basicOpen f ≤ (I.support.compl : X.Opens) := basicOpen_le_compl_support I V hf
  set x : Γ(idealPow I n, V.1) :=
    Submodule.inclusion (le_of_eq (obj_idealPow_affineOpen I n V).symm)
      ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ with hx
  set g : Γ(X, X.basicOpen f) := X.presheaf.map (homOfLE (X.basicOpen_le f)).op f with hg
  set w : Γ(idealPow I n, X.basicOpen f) :=
    (idealPow I n).presheaf.map (homOfLE hDU).op (oneSection I n) with hw'
  have h2 : (idealPow I n).presheaf.map (homOfLE (X.basicOpen_le f)).op x = g ^ n • w := by
    apply Subtype.ext
    change X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) = _
    rw [map_pow]
    change _ = g ^ n * (X.presheaf.map (homOfLE hDU).op (1 : Γ(X, (I.support.compl : X.Opens))))
    rw [map_one, mul_one]
  have hw : φ.app (X.basicOpen f) w = 0 := app_restrict_eq_zero φ hDU hφ
  change F.presheaf.map (homOfLE (X.basicOpen_le f)).op (φ.app V.1 x) = 0
  rw [app_naturality φ (X.basicOpen_le f) x, h2, Scheme.Modules.Hom.app_smul, hw, smul_zero]

/-- If `F` is quasi-coherent and the section of `F` over `X \ V(I)` attached to `φ` vanishes,
then for every `f ∈ I(V)` a power of `f` annihilates `φ(fⁿ)`. -/
theorem exists_pow_smul_eq_zero [F.IsQuasicoherent] (φ : idealPow I n ⟶ F)
    (hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0)
    (V : X.affineOpens) {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) :
    ∃ k : ℕ, f ^ k • homOnIdealPow φ V ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0 :=
  Stacks.AlgebraicGeometry.QcqsLocalization.exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact
    F V.2.isCompact f rfl (X.basicOpen_le f) _ (res_basicOpen_eq_zero φ hφ V hf)

/-- **The affine case.** On an affine open `V` with `I(V)` finitely generated, `φ` annihilates
`I(V)^(n+N)` for some `N`. -/
theorem exists_pow_le_killIdeal [F.IsQuasicoherent] (φ : idealPow I n ⟶ F)
    (hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0)
    (V : X.affineOpens) (hFG : (I.ideal V).FG) :
    ∃ N : ℕ, (I.ideal V ^ (n + N) : Ideal Γ(X, V.1)) ≤ killIdeal φ V := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.IdealPowerSections.exists_comp_inclusion_eq_zero
      Γ(X, V.1) (I.ideal V) Γ(F, V.1) hFG n (homOnIdealPow φ V)
      (fun f hf ↦ exists_pow_smul_eq_zero φ hφ V hf)
  refine ⟨N, fun a ha ↦ mem_killIdeal_iff.mpr
    ⟨Ideal.pow_le_pow_right (Nat.le_add_right n N) ha, ?_⟩⟩
  exact LinearMap.congr_fun hN ⟨a, ha⟩

/-- For affine opens `V ≤ W`, if `I(W)^m ≤ killIdeal φ W` then `I(V)^m ≤ killIdeal φ V`. -/
theorem pow_le_killIdeal_of_le {φ : idealPow I n ⟶ F} {V W : X.affineOpens} (hVW : V.1 ≤ W.1)
    {m : ℕ} (h : (I.ideal W ^ m : Ideal Γ(X, W.1)) ≤ killIdeal φ W) :
    (I.ideal V ^ m : Ideal Γ(X, V.1)) ≤ killIdeal φ V := by
  rw [← map_idealPow I m hVW, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap]
  obtain ⟨hb1, hb2⟩ := mem_killIdeal_iff.mp (h hb)
  refine mem_killIdeal_iff.mpr ⟨res_mem_idealPow I n hVW hb1, ?_⟩
  exact app_restrict_eq_zero φ hVW hb2

/-! ### Globalisation over a finite affine cover -/

/-- Given a cover by affine opens on each of which `φ` annihilates `I^(n+N)`, the composite
`I^(n+N) ⟶ Iⁿ ⟶ F` vanishes on every section. -/
theorem app_idealPowMap_eq_zero [F.IsQuasicoherent] (φ : idealPow I n ⟶ F) {N : ℕ}
    {s : Set X.affineOpens} (hcov : (Set.univ : Set X) = ⋃ i ∈ s, ((i : X.affineOpens) : Set X))
    (hmem : ∀ W ∈ s, (I.ideal W ^ (n + N) : Ideal Γ(X, W.1)) ≤ killIdeal φ W)
    (V₀ : X.Opens) (t : Γ(idealPow I (n + N), V₀)) :
    φ.app V₀ ((idealPowMap I (Nat.le_add_right n N)).app V₀ t) = 0 := by
  refine eq_zero_of_locally_zero _ fun x hx ↦ ?_
  obtain ⟨W, hWs, hxW⟩ : ∃ W ∈ s, x ∈ (W : X.affineOpens).1 := by
    have : x ∈ ⋃ i ∈ s, ((i : X.affineOpens) : Set X) := hcov ▸ Set.mem_univ x
    simpa using this
  obtain ⟨-, ⟨V', hV'aff, rfl⟩, hxV', hV'sub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₀ ⊓ (W : X.affineOpens).1 : X.Opens) : Set X) from ⟨hx, hxW⟩)
      (V₀ ⊓ (W : X.affineOpens).1).isOpen
  have hV'V₀ : V' ≤ V₀ := fun y hy ↦ (hV'sub hy).1
  have hV'W : V' ≤ (W : X.affineOpens).1 := fun y hy ↦ (hV'sub hy).2
  refine ⟨V', hV'V₀, hxV', ?_⟩
  have hkill : (I.ideal ⟨V', hV'aff⟩ ^ (n + N) : Ideal Γ(X, V')) ≤ killIdeal φ ⟨V', hV'aff⟩ :=
    pow_le_killIdeal_of_le (V := ⟨V', hV'aff⟩) (W := W) hV'W (hmem W hWs)
  have hval : ((((idealPow I (n + N)).presheaf.map (homOfLE hV'V₀).op t) : _).1 : Γ(X, V'))
      ∈ (I.ideal ⟨V', hV'aff⟩ ^ (n + N) : Ideal Γ(X, V')) :=
    le_of_eq (obj_idealPow_affineOpen I (n + N) ⟨V', hV'aff⟩)
      ((idealPow I (n + N)).presheaf.map (homOfLE hV'V₀).op t).2
  rw [app_naturality φ hV'V₀ _]
  refine app_eq_zero_of_val_mem_killIdeal ⟨V', hV'aff⟩ _ ?_
  rw [val_map_idealPow, val_idealPowMap_app, ← val_map_idealPow]
  exact hkill hval

/-- For `X` quasi-compact, `I` of finite type and `F` quasi-coherent, if the section of `F` over
`X \ V(I)` attached to `φ` vanishes, then there are an `N` and an affine cover of `X` on each
member `W` of which `I(W)^(n+N) ≤ killIdeal φ W`. -/
theorem exists_forall_mem_pow_le_killIdeal [CompactSpace X] [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (φ : idealPow I n ⟶ F)
    (hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0) :
    ∃ (N : ℕ) (s : Set X.affineOpens),
      (Set.univ : Set X) = ⋃ i ∈ s, ((i : X.affineOpens) : Set X) ∧
        ∀ W ∈ s, (I.ideal W ^ (n + N) : Ideal Γ(X, W.1)) ≤ killIdeal φ W := by
  classical
  obtain ⟨s, hsfin, hcov⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      (⟨isCompact_univ, isOpen_univ⟩ :
        IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X))
  have key : ∀ V : X.affineOpens,
      ∃ N : ℕ, (I.ideal V ^ (n + N) : Ideal Γ(X, V.1)) ≤ killIdeal φ V :=
    fun V ↦ exists_pow_le_killIdeal φ hφ V (hFT V)
  choose Nf hNf using key
  refine ⟨hsfin.toFinset.sup Nf, s, hcov, fun W hW ↦ ?_⟩
  refine le_trans (Ideal.pow_le_pow_right ?_) (hNf W)
  have : Nf W ≤ hsfin.toFinset.sup Nf := Finset.le_sup (hsfin.mem_toFinset.mpr hW)
  omega

/-- For `X` quasi-compact, `I` of finite type and `F`
quasi-coherent, a morphism `φ : Iⁿ ⟶ F` whose section over `X \ V(I)` vanishes already dies on
`I^(n+N)` for some `N`. -/
theorem exists_comp_eq_zero [CompactSpace X] [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (φ : idealPow I n ⟶ F)
    (hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0) :
    ∃ N : ℕ, (idealPowMap I (Nat.le_add_right n N) ≫ φ : idealPow I (n + N) ⟶ F) = 0 := by
  obtain ⟨N, s, hcov, hmem⟩ := exists_forall_mem_pow_le_killIdeal hFT φ hφ
  refine ⟨N, ?_⟩
  ext V₀ t
  exact app_idealPowMap_eq_zero φ hcov hmem V₀ t

/-! ### The colimit and the canonical map -/

/-- The direct system `n ↦ Hom_{𝒪_X}(Iⁿ, F)`, the transition maps being precomposition with the
inclusions between the powers of `I`. -/
noncomputable def idealPowHomSystem (I : X.IdealSheafData) (F : X.Modules) :
    ℕ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (idealPow I n ⟶ F)
  map {m n} h := AddCommGrpCat.ofHom (Preadditive.leftComp F (idealPowMap I (leOfHom h)))
  map_id n := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowMap I (le_refl n) ≫ φ = φ
    rw [idealPowMap_refl, Category.id_comp])
  map_comp {k m n} h h' := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowMap I (leOfHom (h ≫ h')) ≫ φ
      = idealPowMap I (leOfHom h') ≫ (idealPowMap I (leOfHom h) ≫ φ)
    rw [← Category.assoc, idealPowMap_comp])

/-- The transition maps of `idealPowHomSystem` are precomposition with the inclusions. -/
@[simp] theorem idealPowHomSystem_map (I : X.IdealSheafData) (F : X.Modules) {m n : ℕ}
    (h : m ⟶ n) (φ : idealPow I m ⟶ F) :
    (idealPowHomSystem I F).map h φ = idealPowMap I (leOfHom h) ≫ φ := rfl

/-- Precomposing `φ : I^m ⟶ F` with the inclusion `Iⁿ ⟶ I^m` does not change its value on the
unit section. -/
theorem comp_app_oneSection (I : X.IdealSheafData) (F : X.Modules) {m n : ℕ} (h : m ≤ n)
    (φ : idealPow I m ⟶ F) :
    (idealPowMap I h ≫ φ : idealPow I n ⟶ F).app (I.support.compl : X.Opens) (oneSection I n)
      = φ.app (I.support.compl : X.Opens) (oneSection I m) := by
  rw [Scheme.Modules.Hom.comp_app]
  change φ.app (I.support.compl : X.Opens)
    ((idealPowMap I h).app (I.support.compl : X.Opens) (oneSection I n)) = _
  rw [idealPowMap_app_oneSection]

/-- The cocone on `idealPowHomSystem` sending `φ : Iⁿ ⟶ F` to the section `φ(1)` of `F` over the
complement of the support of `I`, where `Iⁿ` is the whole structure sheaf. -/
noncomputable def sectionsCocone (I : X.IdealSheafData) (F : X.Modules) :
    Limits.Cocone (idealPowHomSystem I F) where
  pt := Γ(F, (I.support.compl : X.Opens))
  ι :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun φ : idealPow I n ⟶ F ↦
            φ.app (I.support.compl : X.Opens) (oneSection I n))
          (fun φ ψ ↦ by rw [Scheme.Modules.Hom.add_app]; rfl))
      naturality := fun {m n} h ↦ by
        simp only [Functor.const_obj_map]
        exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦
          comp_app_oneSection I F (leOfHom h) φ) }

/-- The canonical map `colim_n Hom_{𝒪_X}(Iⁿ, F) ⟶ Γ(X \ V(I), F)`. -/
@[stacks 01PQ "canonical_map"]
noncomputable def canonicalMapToSections (I : X.IdealSheafData) (F : X.Modules) :
    Limits.colimit (idealPowHomSystem I F) ⟶ Γ(F, (I.support.compl : X.Opens)) :=
  Limits.colimit.desc _ (sectionsCocone I F)

/-- The canonical map sends the class of `φ : Iⁿ ⟶ F` to the value of `φ` on the unit
section. -/
theorem canonicalMapToSections_ι (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (φ : idealPow I n ⟶ F) :
    canonicalMapToSections I F (Limits.colimit.ι (idealPowHomSystem I F) n φ)
      = φ.app (I.support.compl : X.Opens) (oneSection I n) :=
  congr($(Limits.colimit.ι_desc (sectionsCocone I F) n) φ)

/-- For a quasi-compact scheme `X`, a quasi-coherent sheaf of ideals `I` of finite type and a
quasi-coherent `𝒪_X`-module `F`, the canonical map `colim_n Hom_{𝒪_X}(Iⁿ, F) → Γ(X \ V(I), F)`
is injective. -/
@[stacks 01PQ "injective: the FIRST display colim Hom(Iⁿ, F) → Γ(U, F) is injective; X \
quasi-compact, I quasi-coherent of finite type, F quasi-coherent.  The second display is \
canonicalMapToSectionsQuotient_bijective"]
theorem canonicalMapToSections_injective [CompactSpace X] (I : X.IdealSheafData)
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (F : X.Modules) [F.IsQuasicoherent] :
    Function.Injective (canonicalMapToSections I F) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  refine (injective_iff_map_eq_zero
    (AddCommGrpCat.Hom.hom (canonicalMapToSections I F))).mpr fun z hz ↦ ?_
  obtain ⟨n, φ, rfl⟩ := Limits.Concrete.colimit_exists_rep (idealPowHomSystem I F) z
  obtain ⟨N, hN⟩ := exists_comp_eq_zero hFT φ
    ((canonicalMapToSections_ι I F n φ).symm.trans hz)
  calc Limits.colimit.ι (idealPowHomSystem I F) n φ
      = Limits.colimit.ι (idealPowHomSystem I F) (n + N)
          ((idealPowHomSystem I F).map (homOfLE (Nat.le_add_right n N)) φ) := by
        rw [← ConcreteCategory.comp_apply, Limits.colimit.w]
    _ = Limits.colimit.ι (idealPowHomSystem I F) (n + N) 0 :=
        congrArg (ConcreteCategory.hom (Limits.colimit.ι (idealPowHomSystem I F) (n + N)))
          (show (idealPowHomSystem I F).map (homOfLE (Nat.le_add_right n N)) φ = 0 from hN)
    _ = 0 := map_zero _

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
