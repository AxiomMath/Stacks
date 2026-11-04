module

public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import StacksFrontier.AlgebraicGeometry.TorsionSubsheaf.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the torsion subsheaf

Let `X` be an integral scheme and `F` a quasi-coherent `𝒪_X`-module. This file proves that the
torsion subsheaf `torsionSubsheaf F` of `F` -- equivalently, by
`torsionSubmodule_eq_torsionSubsheaf`, the supremum `torsionSubmodule F` of all submodule
sheaves of `F` with torsion sections -- is quasi-coherent.

## Main results

* `isTorsionSection_iff_exists_ne_zero` is the part of [Stacks, Tag 0AXR] that is needed: on a
  nonempty affine open of an integral scheme, a section of a quasi-coherent module is torsion
  (all its germs are annihilated by nonzero elements of the local rings) if and only if it is
  annihilated by a single nonzero function on that open.
* `torsionSubmodule_isQuasicoherent` is the first assertion of [Stacks, Tag 0AXT]: the torsion
  subsheaf is quasi-coherent.

## Implementation notes

Quasi-coherence of a subsheaf cannot be read off a presentation, so it is checked through the
localization criterion `isQuasicoherent_of_isLocalizedModule_restrictₗ`: it suffices that for
each affine open `U` and each `a : Γ(X, U)`, the torsion sections over `X.basicOpen a` are the
localization away from `a` of the torsion sections over `U`. The three conditions of
`IsLocalizedModule.Away.mk_of_addCommGroup` are discharged as follows, the corresponding
statements for `F` itself coming from `QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

* That `a` acts invertibly on the torsion sections over `X.basicOpen a` is purely a germ
  computation: the germ of `a` is a unit at each point of `X.basicOpen a`, and dividing a
  torsion germ by a unit leaves it torsion (`isTorsionElement_of_isUnit_smul`).
* Injectivity up to powers of `a` is inherited from `F` verbatim, the torsion sections being a
  subobject.
* Surjectivity up to powers of `a` is the one place where [Stacks, Tag 0AXR] is needed: a
  section of `F` over `U` whose restriction to `X.basicOpen a` is torsion must itself be
  torsion. The argument runs through the generic point `η` of `X`, which lies in every nonempty
  open: the local ring at `η` is a field, so a torsion germ there vanishes, a vanishing germ
  means the section dies on some basic open `X.basicOpen c` with `c ≠ 0`, and the localization
  property of `F` away from `c` then produces the single annihilator `c ^ n` on all of `U`.

The torsion subsheaf is bundled as `torsionModule F : X.Modules`, with `mk` and `val` naming
the two directions of the (definitional) identification of its sections with the torsion
sections of `F`. The type `X.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` that does
not unfold at instance-reducible transparency, so without this bundling the
`Module Γ(X, U) Γ(_, U)` instance of `AlgebraicGeometry.Scheme.Modules` is not found for
`(torsionSubsheaf F).toSheafOfModules`.

The field structure on the local ring at the generic point is used only through
`isUnit_of_ne_zero_stalk_genericPoint`: a `Field` instance in the local context is picked up in
preference to the `CommRingCat` structure when elaborating scalar multiplication, and then the
module structure on the stalk of `F` is no longer found.

## References

* [Stacks Project, Tag 0AXT](https://stacks.math.columbia.edu/tag/0AXT)
* [Stacks Project, Tag 0AXR](https://stacks.math.columbia.edu/tag/0AXR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionSubsheaf

universe u

namespace Stacks.AlgebraicGeometry.TorsionQuasicoherent

variable {X : Scheme.{u}}

/-! ### Torsion elements -/

/-- Dividing a torsion element by a unit leaves it torsion. -/
theorem isTorsionElement_of_isUnit_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {u : R} (hu : IsUnit u) {m : M} (h : IsTorsionElement (R := R) (u • m)) :
    IsTorsionElement (R := R) m := by
  obtain ⟨t, ht, htm⟩ := h
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨t, ht, ?_⟩
  have key : c • (t • (u • m)) = t • m := by
    rw [smul_smul, smul_smul, show c * t * u = c * u * t by ring, hc, one_mul]
  rw [← key, htm, smul_zero]

/-- An element annihilated by a unit is zero. -/
theorem eq_zero_of_isUnit_smul_eq_zero {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {u : R} (hu : IsUnit u) {m : M} (h : u • m = 0) : m = 0 := by
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  have key : (c * u) • m = 0 := by rw [mul_smul, h, smul_zero]
  rwa [hc, one_smul] at key

/-! ### The generic point -/

/-- The generic point of an irreducible scheme belongs to every nonempty open. -/
@[ega "0 2.1.2" "irreducible schemes"]
theorem genericPoint_mem [IrreducibleSpace X] (U : X.Opens) [h : Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)

/-- The local ring of an integral scheme at its generic point is the function field, so every
nonzero element of it is a unit. -/
@[ega "I 8.2.1" "partial"]
theorem isUnit_of_ne_zero_stalk_genericPoint [IsIntegral X]
    {t : ↑(X.presheaf.stalk (genericPoint X))} (ht : t ≠ 0) : IsUnit t :=
  isUnit_iff_ne_zero.mpr ht

/-- A section of a module on an integral scheme whose germ at the generic point is torsion has
vanishing germ at the generic point: the local ring there is a field. This is the implication
(1) → (3) of [Stacks, Tag 0AXR] at the generic point. -/
theorem germ_genericPoint_eq_zero [IsIntegral X] (F : X.Modules) {U : X.Opens} [Nonempty U]
    {s : Γ(F, U)}
    (hs : IsTorsionElement (R := X.presheaf.stalk (genericPoint X))
      (M := F.presheaf.stalk (genericPoint X))
      (F.presheaf.germ U (genericPoint X) (genericPoint_mem U) s)) :
    F.presheaf.germ U (genericPoint X) (genericPoint_mem U) s = 0 := by
  obtain ⟨t, ht, hts⟩ := hs
  exact eq_zero_of_isUnit_smul_eq_zero (isUnit_of_ne_zero_stalk_genericPoint ht) hts

/-! ### Torsion sections on an affine open -/

/-- A section of a module on an integral scheme that is annihilated by a nonzero function is
torsion, because the germ maps of the structure sheaf are injective. This is the implication
(3) → (2) of [Stacks, Tag 0AXR], in the form in which it is used. -/
theorem isTorsionSection_of_smul_eq_zero [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} {b : Γ(X, U)} (hb : b ≠ 0) {s : Γ(F, U)} (hbs : b • s = 0) :
    IsTorsionSection F s := fun x hx ↦
  ⟨X.presheaf.germ U x hx b,
    fun hz ↦ hb (germ_injective_of_isIntegral X x hx (by rw [hz, map_zero])),
    by rw [← germ_smul F x hx b s, hbs, map_zero]⟩

/-- A section of a quasi-coherent module over an affine open `U` that dies on `X.basicOpen a` is
killed by a power of `a`. -/
private theorem exists_pow_smul_eq_zero_of_map_eq_zero (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) {s : Γ(F, U)}
    (hs : F.presheaf.map (homOfLE (X.basicOpen_le a)).op s = 0) : ∃ n : ℕ, a ^ n • s = 0 := by
  let := moduleOfLE F (X.basicOpen_le a)
  have hloc : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq a
    (show restrictₗ F (X.basicOpen_le a) s = restrictₗ F (X.basicOpen_le a) 0 by
      rw [map_zero]; exact hs)
  exact ⟨n, by rw [hn, smul_zero]⟩

/-- On an affine open of an integral scheme, a section of a quasi-coherent module whose germ at
the generic point vanishes is annihilated by a nonzero function: the section already dies on a
basic open `X.basicOpen c` containing the generic point, so `c ≠ 0`, and the sections of `F`
over `X.basicOpen c` are the localization of `Γ(F, U)` away from `c`. -/
theorem exists_ne_zero_smul_eq_zero [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {s : Γ(F, U)}
    (hs : F.presheaf.germ U (genericPoint X) (genericPoint_mem U) s = 0) :
    ∃ b : Γ(X, U), b ≠ 0 ∧ b • s = 0 := by
  have hη : genericPoint X ∈ U := genericPoint_mem U
  obtain ⟨W, hηW, i, j, hW⟩ :=
    F.presheaf.germ_eq (genericPoint X) hη hη s 0 (by rw [hs, map_zero])
  rw [map_zero] at hW
  obtain ⟨c, hcW, hηc⟩ := hU.exists_basicOpen_le ⟨genericPoint X, hηW⟩ hη
  have hc : c ≠ 0 := fun h ↦ by simp [h, Scheme.basicOpen_zero] at hηc
  have hcomp : (homOfLE (X.basicOpen_le c) : X.basicOpen c ⟶ U) = homOfLE hcW ≫ i :=
    Subsingleton.elim _ _
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_map_eq_zero F hU c
    (by rw [hcomp, op_comp, Functor.map_comp_apply, hW, map_zero])
  exact ⟨c ^ n, pow_ne_zero n hc, hn⟩

/-- **[Stacks, Tag 0AXR].** On a nonempty affine open of an integral scheme, a section of a
quasi-coherent module is torsion if and only if it is annihilated by a nonzero function. -/
theorem isTorsionSection_iff_exists_ne_zero [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (s : Γ(F, U)) :
    IsTorsionSection F s ↔ ∃ b : Γ(X, U), b ≠ 0 ∧ b • s = 0 :=
  ⟨fun hs ↦ exists_ne_zero_smul_eq_zero F hU
      (germ_genericPoint_eq_zero F (hs _ (genericPoint_mem U))),
    fun ⟨_, hb, hbs⟩ ↦ isTorsionSection_of_smul_eq_zero F hb hbs⟩

/-! ### Invertible scalars on a module -/

/-- Multiplication by `r` is a unit of `Module.End R M` as soon as it is bijective. -/
theorem isUnit_algebraMap_end {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {r : R} (hinj : ∀ m₁ m₂ : M, r • m₁ = r • m₂ → m₁ = m₂)
    (hsurj : ∀ m : M, ∃ m' : M, r • m' = m) :
    IsUnit (algebraMap R (Module.End R M) r) :=
  (Module.End.isUnit_iff _).mpr
    ⟨fun _ _ h ↦ hinj _ _ (by simpa only [Module.algebraMap_end_apply] using h), fun m ↦ by
      obtain ⟨m', hm'⟩ := hsurj m
      exact ⟨m', by simpa only [Module.algebraMap_end_apply] using hm'⟩⟩

/-- In a localization away from `r`, multiplication by `r` is bijective. -/
theorem smul_bijective_of_isLocalizedModule {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (r : R)
    [IsLocalizedModule.Away r f] :
    (∀ n₁ n₂ : N, r • n₁ = r • n₂ → n₁ = n₂) ∧ ∀ n : N, ∃ n' : N, r • n' = n := by
  have h := (Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap f r)
  refine ⟨fun n₁ n₂ hn ↦ h.1 (by simpa only [Module.algebraMap_end_apply] using hn), fun n ↦ ?_⟩
  obtain ⟨n', hn'⟩ := h.2 n
  exact ⟨n', by simpa only [Module.algebraMap_end_apply] using hn'⟩

/-! ### The torsion subsheaf is quasi-coherent -/

/-- The torsion subsheaf of `F`, bundled as an `𝒪_X`-module. -/
@[ega "I 7.4.1" "special case"]
noncomputable def torsionModule [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] :
    X.Modules :=
  (torsionSubsheaf F).toSheafOfModules

variable [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]

/-- A torsion section of `F`, viewed as a section of the torsion subsheaf. -/
noncomputable def mk {W : X.Opens} (s : Γ(F, W)) (hs : IsTorsionSection F s) :
    Γ(torsionModule F, W) :=
  show ↥(torsionSections F W) from ⟨s, hs⟩

/-- The underlying section of `F` of a section of the torsion subsheaf. -/
noncomputable def val {W : X.Opens} (z : Γ(torsionModule F, W)) : Γ(F, W) :=
  z.1

/-- A section of `torsionModule F` is a torsion section of `F`. -/
theorem isTorsionSection_val {W : X.Opens} (z : Γ(torsionModule F, W)) :
    IsTorsionSection F (val F z) :=
  z.2

/-- Sections of `torsionModule F` are determined by the underlying sections of `F`. -/
theorem val_inj {W : X.Opens} {z₁ z₂ : Γ(torsionModule F, W)} (h : val F z₁ = val F z₂) :
    z₁ = z₂ :=
  Subtype.ext h

/-- Equal sections of `torsionModule F` have equal underlying sections of `F`. -/
theorem val_eq_val {W : X.Opens} {z₁ z₂ : Γ(torsionModule F, W)} (h : z₁ = z₂) :
    val F z₁ = val F z₂ := by
  rw [h]

/-- The underlying section of `r • z` in `F` is `r • val F z`. -/
@[simp]
theorem val_smul {W : X.Opens} (r : Γ(X, W)) (z : Γ(torsionModule F, W)) :
    val F (r • z) = r • val F z :=
  rfl

/-- The underlying section in `F` of the zero section of `torsionModule F` is zero. -/
@[simp]
theorem val_zero {W : X.Opens} : val F (0 : Γ(torsionModule F, W)) = (0 : Γ(F, W)) :=
  rfl

/-- The sections of `torsionModule F` over `X.basicOpen a` are the localization away from `a`
of its sections over an affine open `U`. -/
theorem isLocalizedModule_torsionModule {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE (torsionModule F) (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (torsionModule F) (X.basicOpen_le a)) := by
  let := moduleOfLE (torsionModule F) (X.basicOpen_le a)
  let := moduleOfLE F (X.basicOpen_le a)
  have hloc : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨hFinj, hFsurj⟩ :=
    smul_bijective_of_isLocalizedModule (restrictₗ F (X.basicOpen_le a)) a
  refine IsLocalizedModule.Away.mk_of_addCommGroup (isUnit_algebraMap_end ?_ ?_) ?_ ?_
  · exact fun y₁ y₂ hy ↦ val_inj F (hFinj (val F y₁) (val F y₂) (val_eq_val F hy))
  · intro y
    obtain ⟨w, hw⟩ := hFsurj (val F y)
    have hwt : IsTorsionSection F w := by
      intro x hx
      have hunit : IsUnit (X.presheaf.germ U x (X.basicOpen_le a hx) a) :=
        (X.mem_basicOpen a x (X.basicOpen_le a hx)).mp hx
      have hw' : X.presheaf.map (homOfLE (X.basicOpen_le a)).op a • w = val F y := hw
      have hgs : F.presheaf.germ (X.basicOpen a) x hx (val F y) =
          X.presheaf.germ U x (X.basicOpen_le a hx) a •
            F.presheaf.germ (X.basicOpen a) x hx w := by
        rw [← hw', germ_smul F x hx _ w]
        simp
      have htors := isTorsionSection_val F y x hx
      rw [hgs] at htors
      exact isTorsionElement_of_isUnit_smul hunit htors
    exact ⟨mk F w hwt, val_inj F hw⟩
  · intro y
    by_cases ha : a = 0
    · subst ha
      exact ⟨1, 0, by rw [pow_one, zero_smul, map_zero]⟩
    have hne : Set.Nonempty ((X.basicOpen a : X.Opens) : Set X) :=
      (Opens.ne_bot_iff_nonempty _).mp fun h ↦ ha ((basicOpen_eq_bot_iff a).mp h)
    have hVne : Nonempty (X.basicOpen a) := hne.to_subtype
    have hηV : genericPoint X ∈ X.basicOpen a := genericPoint_mem (X.basicOpen a)
    have hUne : Nonempty U := ⟨⟨genericPoint X, X.basicOpen_le a hηV⟩⟩
    obtain ⟨n, x₀, hx₀⟩ :=
      IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le a)) a (val F y)
    have hmem : IsTorsionSection F (restrictₗ F (X.basicOpen_le a) x₀) := by
      rw [← hx₀]
      exact (torsionSections F (X.basicOpen a)).smul_mem
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ n)) (isTorsionSection_val F y)
    have hgerm : IsTorsionElement (R := X.presheaf.stalk (genericPoint X))
        (M := F.presheaf.stalk (genericPoint X))
        (F.presheaf.germ U (genericPoint X) (genericPoint_mem U) x₀) := by
      have he : F.presheaf.germ (X.basicOpen a) (genericPoint X) hηV
            (F.presheaf.map (homOfLE (X.basicOpen_le a)).op x₀) =
          F.presheaf.germ U (genericPoint X) (genericPoint_mem U) x₀ :=
        TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (X.basicOpen_le a)) _ hηV x₀
      rw [← he]
      exact hmem (genericPoint X) hηV
    obtain ⟨b, hb, hbx⟩ := exists_ne_zero_smul_eq_zero F hU (germ_genericPoint_eq_zero F hgerm)
    exact ⟨n, mk F x₀ (isTorsionSection_of_smul_eq_zero F hb hbx), val_inj F hx₀⟩
  · intro z hz
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_map_eq_zero F hU a (val_eq_val F hz)
    refine ⟨n, val_inj F ?_⟩
    rw [val_smul, val_zero]
    exact hn

/-- **The torsion subsheaf of a quasi-coherent module on an integral scheme is
quasi-coherent.** -/
@[ega "I 7.4.1"]
theorem torsionSubsheaf_isQuasicoherent :
    (torsionSubsheaf F).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (torsionModule F)
    fun _ hU a ↦ isLocalizedModule_torsionModule F hU a

/-- **The first assertion of [Stacks, Tag 0AXT].** The torsion submodule sheaf of a
quasi-coherent module on an integral scheme is quasi-coherent. -/
@[stacks 0AXT "torsion_subsheaf_quasi_coherent", ega "I 7.4.1" "quasi-coherence of T"]
instance torsionSubmodule_isQuasicoherent :
    (torsionSubmodule F).toSheafOfModules.IsQuasicoherent := by
  rw [torsionSubmodule_eq_torsionSubsheaf]
  exact torsionSubsheaf_isQuasicoherent F

end Stacks.AlgebraicGeometry.TorsionQuasicoherent

end
