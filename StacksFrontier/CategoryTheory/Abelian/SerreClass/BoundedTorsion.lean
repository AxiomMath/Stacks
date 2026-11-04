module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Objects annihilated by a power of an integer form a Serre class

Fix a natural number `ℓ`. An object `F` of a preadditive category is *`ℓ`-power torsion* when
`ℓ ^ k • 𝟙 F = 0` for some `k`, i.e. when a single power of `ℓ` annihilates it. In an abelian
category these objects form a Serre class, so one may localize at them, and the resulting quotient
is again abelian.

The hom-groups of the quotient are computed here: the localization functor exhibits
`Hom (L.obj X) (L.obj Y)` as the localization of the abelian group `Hom X Y` at the powers of `ℓ`.
Two statements carry that content. A morphism dies in the quotient exactly when a power of `ℓ`
annihilates it (`map_eq_zero_iff`), and every morphism of the quotient becomes the image of an
honest morphism after multiplication by a power of `ℓ` (`exists_nsmul_eq_map`). Both come from one
elementary observation (`exists_comp_eq_nsmul_id`): a morphism whose kernel and cokernel are
`ℓ`-power torsion has a two-sided pseudo-inverse for a power of `ℓ`, obtained by factoring
`ℓ ^ k • 𝟙` through the epi-mono factorisation — no `Ext` group is needed.

## Main definitions

* `Stacks.CategoryTheory.isTorsionObject`: the object property "annihilated by a power of `ℓ`".

## Main results

* `Stacks.CategoryTheory.isTorsionObject_isSerreClass`: the `ℓ`-power torsion objects of an
  abelian category are a Serre class.
* `Stacks.CategoryTheory.exists_comp_eq_nsmul_id`: a morphism which is an isomorphism modulo
  `ℓ`-power torsion has a pseudo-inverse for a power of `ℓ`.
* `Stacks.CategoryTheory.isLocalizedModule_mapIntLinearMap`: the hom-groups of the Serre quotient
  are the hom-groups of the original category localized at the powers of `ℓ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace Stacks.CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- Multiplying the identity by `k` and then composing is multiplication by `k`. -/
public theorem nsmul_id_comp (k : ℕ) {X Y : C} (f : X ⟶ Y) : (k • 𝟙 X) ≫ f = k • f := by
  rw [Preadditive.nsmul_comp, Category.id_comp]

/-- Composing with `k` times the identity is multiplication by `k`. -/
public theorem comp_nsmul_id (k : ℕ) {X Y : C} (f : X ⟶ Y) : f ≫ (k • 𝟙 Y) = k • f := by
  rw [Preadditive.comp_nsmul, Category.comp_id]

/-- An object is `ℓ`-power torsion when some power of `ℓ` annihilates its identity, equivalently
when it annihilates every morphism into or out of the object. -/
public def isTorsionObject (ℓ : ℕ) : ObjectProperty C := fun F => ∃ k : ℕ, (ℓ ^ k) • 𝟙 F = 0

/-- Unfolding `isTorsionObject`. -/
public theorem isTorsionObject_iff (ℓ : ℕ) (F : C) :
    isTorsionObject ℓ F ↔ ∃ k : ℕ, (ℓ ^ k) • 𝟙 F = 0 := Iff.rfl

/-- A monomorphism annihilated by `ℓ ^ k` has `ℓ`-power torsion source. -/
public theorem isTorsionObject_of_mono {ℓ : ℕ} {K X : C} (i : K ⟶ X) [Mono i] {k : ℕ}
    (h : (ℓ ^ k) • i = 0) : isTorsionObject ℓ K :=
  ⟨k, by rwa [← cancel_mono i, zero_comp, nsmul_id_comp]⟩

/-- An epimorphism annihilated by `ℓ ^ k` has `ℓ`-power torsion target. -/
public theorem isTorsionObject_of_epi {ℓ : ℕ} {X Q : C} (p : X ⟶ Q) [Epi p] {k : ℕ}
    (h : (ℓ ^ k) • p = 0) : isTorsionObject ℓ Q :=
  ⟨k, by rwa [← cancel_epi p, comp_zero, comp_nsmul_id]⟩

/-- A subobject of an `ℓ`-power torsion object is `ℓ`-power torsion. -/
public instance isTorsionObject_isClosedUnderSubobjects (ℓ : ℕ) :
    (isTorsionObject (C := C) ℓ).IsClosedUnderSubobjects where
  prop_of_mono {_ X} i _ hX := by
    obtain ⟨k, hk⟩ := hX
    exact isTorsionObject_of_mono i (by rw [← comp_nsmul_id (ℓ ^ k) i, hk, comp_zero])

/-- A quotient of an `ℓ`-power torsion object is `ℓ`-power torsion. -/
public instance isTorsionObject_isClosedUnderQuotients (ℓ : ℕ) :
    (isTorsionObject (C := C) ℓ).IsClosedUnderQuotients where
  prop_of_epi {X _} p _ hX := by
    obtain ⟨k, hk⟩ := hX
    exact isTorsionObject_of_epi p (by rw [← nsmul_id_comp (ℓ ^ k) p, hk, zero_comp])

/-- A zero object is `ℓ`-power torsion. -/
public instance isTorsionObject_containsZero (ℓ : ℕ) [HasZeroObject C] :
    (isTorsionObject (C := C) ℓ).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
    exact ⟨Z, hZ, 0, by simpa using hZ.eq_of_src (𝟙 Z) 0⟩

/-- The kernel of multiplication by `ℓ ^ k` is `ℓ`-power torsion. -/
public theorem isTorsionObject_kernel_nsmul_id (ℓ k : ℕ) (X : C)
    [HasKernel ((ℓ ^ k) • 𝟙 X)] : isTorsionObject ℓ (kernel ((ℓ ^ k) • 𝟙 X)) :=
  isTorsionObject_of_mono (kernel.ι ((ℓ ^ k) • 𝟙 X)) (k := k) (by
    rw [← comp_nsmul_id (ℓ ^ k) (kernel.ι ((ℓ ^ k) • 𝟙 X))]
    exact kernel.condition _)

/-- The cokernel of multiplication by `ℓ ^ k` is `ℓ`-power torsion. -/
public theorem isTorsionObject_cokernel_nsmul_id (ℓ k : ℕ) (X : C)
    [HasCokernel ((ℓ ^ k) • 𝟙 X)] : isTorsionObject ℓ (cokernel ((ℓ ^ k) • 𝟙 X)) :=
  isTorsionObject_of_epi (cokernel.π ((ℓ ^ k) • 𝟙 X)) (k := k) (by
    rw [← nsmul_id_comp (ℓ ^ k) (cokernel.π ((ℓ ^ k) • 𝟙 X))]
    exact cokernel.condition _)

end Preadditive

section Abelian

variable [Abelian C]

/-- An extension of `ℓ`-power torsion objects is `ℓ`-power torsion: the exponents add. -/
public instance isTorsionObject_isClosedUnderExtensions (ℓ : ℕ) :
    (isTorsionObject (C := C) ℓ).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨k₁, hk₁⟩ := h₁
    obtain ⟨k₃, hk₃⟩ := h₃
    have hz : ((ℓ ^ k₃) • 𝟙 S.X₂) ≫ S.g = 0 := by
      rw [nsmul_id_comp, ← comp_nsmul_id (ℓ ^ k₃) S.g, hk₃, comp_zero]
    obtain ⟨u, hu⟩ := KernelFork.IsLimit.lift' hS.fIsKernel _ hz
    have hu' : u ≫ S.f = (ℓ ^ k₃) • 𝟙 S.X₂ := hu
    refine ⟨k₁ + k₃, ?_⟩
    calc (ℓ ^ (k₁ + k₃)) • 𝟙 S.X₂
        = (ℓ ^ k₁) • ((ℓ ^ k₃) • 𝟙 S.X₂) := by rw [pow_add, mul_smul]
      _ = (ℓ ^ k₁) • (u ≫ S.f) := by rw [hu']
      _ = u ≫ ((ℓ ^ k₁) • S.f) := by rw [Preadditive.comp_nsmul]
      _ = 0 := by rw [← nsmul_id_comp (ℓ ^ k₁) S.f, hk₁, zero_comp, comp_zero]

/-- The `ℓ`-power torsion objects of an abelian category form a Serre class: they contain the
zero object and are closed under subobjects, quotients and extensions. For `ℤ_ℓ`-sheaves this is
the Serre subcategory of torsion sheaves of Stacks 03UR. -/
@[stacks 03UR "torsion sheaves are a Serre subcategory", sga "4½ Rapport 2.9" "more general"]
public instance isTorsionObject_isSerreClass (ℓ : ℕ) :
    (isTorsionObject (C := C) ℓ).IsSerreClass where

/-- Given an epi-mono factorisation `e ≫ m` whose outer kernel and cokernel are `ℓ`-power
torsion, the composite has a two-sided pseudo-inverse for a power of `ℓ`.

Both halves of the pseudo-inverse come from factoring a multiple of an identity: `ℓ ^ a • 𝟙`
kills the kernel of the epimorphism `e`, hence factors through `e`; dually `ℓ ^ b • 𝟙` dies in the
cokernel of the monomorphism `m`, hence factors through `m`. -/
public theorem exists_comp_eq_nsmul_id_of_fac (ℓ : ℕ) {X I Y : C} (e : X ⟶ I) (m : I ⟶ Y)
    [Epi e] [Mono m] (he : isTorsionObject ℓ (kernel e))
    (hm : isTorsionObject ℓ (cokernel m)) :
    ∃ (k : ℕ) (t : Y ⟶ X), (e ≫ m) ≫ t = (ℓ ^ k) • 𝟙 X ∧ t ≫ (e ≫ m) = (ℓ ^ k) • 𝟙 Y := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hm
  have hz1 : kernel.ι e ≫ ((ℓ ^ a) • 𝟙 X) = 0 := by
    rw [comp_nsmul_id, ← nsmul_id_comp (ℓ ^ a) (kernel.ι e), ha, zero_comp]
  have hz2 : ((ℓ ^ b) • 𝟙 Y) ≫ cokernel.π m = 0 := by
    rw [nsmul_id_comp, ← comp_nsmul_id (ℓ ^ b) (cokernel.π m), hb, comp_zero]
  set v := Abelian.epiDesc e ((ℓ ^ a) • 𝟙 X) hz1
  set r := Abelian.monoLift m ((ℓ ^ b) • 𝟙 Y) hz2
  have hv : e ≫ v = (ℓ ^ a) • 𝟙 X := Abelian.comp_epiDesc e _ hz1
  have hr : r ≫ m = (ℓ ^ b) • 𝟙 Y := Abelian.monoLift_comp m _ hz2
  have hv' : v ≫ e = (ℓ ^ a) • 𝟙 I := by
    rw [← cancel_epi e, ← Category.assoc, hv, nsmul_id_comp, comp_nsmul_id]
  have hr' : m ≫ r = (ℓ ^ b) • 𝟙 I := by
    rw [← cancel_mono m, Category.assoc, hr, comp_nsmul_id, nsmul_id_comp]
  refine ⟨b + a, r ≫ v, ?_, ?_⟩
  · calc (e ≫ m) ≫ (r ≫ v)
        = e ≫ (m ≫ r) ≫ v := by simp only [Category.assoc]
      _ = e ≫ ((ℓ ^ b) • 𝟙 I) ≫ v := by rw [hr']
      _ = (ℓ ^ b) • ((ℓ ^ a) • 𝟙 X) := by rw [nsmul_id_comp, Preadditive.comp_nsmul, hv]
      _ = (ℓ ^ (b + a)) • 𝟙 X := by rw [← mul_smul, ← pow_add]
  · calc (r ≫ v) ≫ (e ≫ m)
        = r ≫ (v ≫ e) ≫ m := by simp only [Category.assoc]
      _ = r ≫ ((ℓ ^ a) • 𝟙 I) ≫ m := by rw [hv']
      _ = (ℓ ^ a) • ((ℓ ^ b) • 𝟙 Y) := by rw [nsmul_id_comp, Preadditive.comp_nsmul, hr]
      _ = (ℓ ^ (b + a)) • 𝟙 Y := by rw [← mul_smul, ← pow_add, add_comm]

/-- A morphism whose kernel and cokernel are `ℓ`-power torsion — an isomorphism modulo the Serre
class — has a two-sided pseudo-inverse for a power of `ℓ`. -/
public theorem exists_comp_eq_nsmul_id (ℓ : ℕ) {X Y : C} (s : X ⟶ Y)
    (hk : isTorsionObject ℓ (kernel s)) (hc : isTorsionObject ℓ (cokernel s)) :
    ∃ (k : ℕ) (t : Y ⟶ X), s ≫ t = (ℓ ^ k) • 𝟙 X ∧ t ≫ s = (ℓ ^ k) • 𝟙 Y := by
  have hfac : Abelian.factorThruImage s ≫ Abelian.image.ι s = s := Abelian.image.fac s
  have hke : isTorsionObject ℓ (kernel (Abelian.factorThruImage s)) := by
    have hz : kernel.ι (Abelian.factorThruImage s) ≫ s = 0 :=
      calc kernel.ι (Abelian.factorThruImage s) ≫ s
          = kernel.ι (Abelian.factorThruImage s) ≫
              (Abelian.factorThruImage s ≫ Abelian.image.ι s) := by rw [hfac]
        _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
    have : Mono (kernel.lift s _ hz) := mono_of_mono_fac (kernel.lift_ι s _ hz)
    exact (isTorsionObject ℓ).prop_of_mono (kernel.lift s _ hz) hk
  have hcm : isTorsionObject ℓ (cokernel (Abelian.image.ι s)) := by
    have hz : s ≫ cokernel.π (Abelian.image.ι s) = 0 :=
      calc s ≫ cokernel.π (Abelian.image.ι s)
          = (Abelian.factorThruImage s ≫ Abelian.image.ι s) ≫
              cokernel.π (Abelian.image.ι s) := by rw [hfac]
        _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
    have : Epi (cokernel.desc s _ hz) := epi_of_epi_fac (cokernel.π_desc s _ hz)
    exact (isTorsionObject ℓ).prop_of_epi (cokernel.desc s _ hz) hc
  obtain ⟨k, t, h₁, h₂⟩ :=
    exists_comp_eq_nsmul_id_of_fac ℓ (Abelian.factorThruImage s) (Abelian.image.ι s) hke hcm
  rw [hfac] at h₁ h₂
  exact ⟨k, t, h₁, h₂⟩

end Abelian

section Localization

variable [Abelian C] {D : Type u'} [Category.{v'} D] [Preadditive D] (ℓ : ℕ) (L : C ⥤ D)
  [L.Additive] [L.IsLocalization (isTorsionObject (C := C) ℓ).isoModSerre]

/-- A morphism becomes zero in the Serre quotient at the `ℓ`-power torsion objects exactly when a
power of `ℓ` annihilates it. -/
@[sga "4½ Rapport 2.9" "Kernel part of Hom(F⊗Q_ℓ"]
public theorem map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    L.map f = 0 ↔ ∃ k : ℕ, (ℓ ^ k) • f = 0 := by
  rw [ObjectProperty.SerreClassLocalization.map_eq_zero_iff L (isTorsionObject ℓ),
    isTorsionObject_iff]
  constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩
  · calc (ℓ ^ k) • f
        = (ℓ ^ k) • (Abelian.factorThruImage f ≫ Abelian.image.ι f) := by rw [Abelian.image.fac]
      _ = Abelian.factorThruImage f ≫ (((ℓ ^ k) • 𝟙 (Abelian.image f)) ≫ Abelian.image.ι f) := by
            rw [nsmul_id_comp, Preadditive.comp_nsmul]
      _ = 0 := by rw [hk, zero_comp, comp_zero]
  · rw [← cancel_epi (Abelian.factorThruImage f), ← cancel_mono (Abelian.image.ι f), comp_zero,
      zero_comp, Category.assoc, nsmul_id_comp, Preadditive.comp_nsmul, Abelian.image.fac, hk]

/-- Every morphism of the Serre quotient at the `ℓ`-power torsion objects becomes the image of a
morphism of `C` after multiplication by a power of `ℓ`. -/
@[sga "4½ Rapport 2.9" "partial"]
public theorem exists_nsmul_eq_map {X Y : C} (φ : L.obj X ⟶ L.obj Y) :
    ∃ (k : ℕ) (g : X ⟶ Y), (ℓ ^ k) • φ = L.map g := by
  obtain ⟨ψ, hψ⟩ :=
    Localization.exists_rightFraction L (isTorsionObject (C := C) ℓ).isoModSerre φ
  have key : L.map ψ.s ≫ φ = L.map ψ.f := by
    rw [hψ]
    exact ψ.map_s_comp_map L (Localization.inverts L _)
  obtain ⟨k, t, -, hts⟩ := exists_comp_eq_nsmul_id ℓ ψ.s ψ.hs.1 ψ.hs.2
  refine ⟨k, t ≫ ψ.f, ?_⟩
  calc (ℓ ^ k) • φ
      = ((ℓ ^ k) • 𝟙 (L.obj X)) ≫ φ := by rw [nsmul_id_comp]
    _ = L.map ((ℓ ^ k) • 𝟙 X) ≫ φ := by rw [Functor.map_nsmul, L.map_id]
    _ = L.map (t ≫ ψ.s) ≫ φ := by rw [hts]
    _ = L.map t ≫ (L.map ψ.s ≫ φ) := by rw [L.map_comp, Category.assoc]
    _ = L.map (t ≫ ψ.f) := by rw [key, L.map_comp]

/-- Multiplication by `ℓ ^ k` on an object becomes invertible in the Serre quotient at the
`ℓ`-power torsion objects. -/
public theorem isIso_map_nsmul_id (X : C) (k : ℕ) : IsIso (L.map ((ℓ ^ k) • 𝟙 X)) :=
  Localization.inverts L (isTorsionObject (C := C) ℓ).isoModSerre _
    ⟨isTorsionObject_kernel_nsmul_id ℓ k X, isTorsionObject_cokernel_nsmul_id ℓ k X⟩

/-- The map on hom-groups induced by an additive functor, as a `ℤ`-linear map. -/
public def mapIntLinearMap (X Y : C) : (X ⟶ Y) →ₗ[ℤ] (L.obj X ⟶ L.obj Y) :=
  (L.mapAddHom : (X ⟶ Y) →+ (L.obj X ⟶ L.obj Y)).toIntLinearMap

/-- The map `mapIntLinearMap L X Y` sends a morphism `f` to `L.map f`. -/
@[simp]
public theorem mapIntLinearMap_apply {X Y : C} (f : X ⟶ Y) :
    mapIntLinearMap L X Y f = L.map f := rfl

/-- An integer power of `ℓ` acts as the corresponding natural power. -/
public theorem zpow_nsmul_eq {M : Type*} [AddCommGroup M] (ℓ k : ℕ) (a : M) :
    (((ℓ : ℤ)) ^ k) • a = (ℓ ^ k) • a := by
  rw [← Nat.cast_pow, natCast_zsmul]

/-- **The hom-groups of a Serre quotient at the `ℓ`-power torsion objects.** The localization
functor exhibits `Hom (L.obj X) (L.obj Y)` as the localization of the abelian group `Hom X Y` at
the powers of `ℓ`: multiplication by `ℓ` is invertible on the target, every element of the target
is a power of `ℓ` away from the image, and two morphisms have the same image exactly when a power
of `ℓ` equalizes them. For `ℤ_ℓ`-sheaves this is the formula
`Hom_{ℚ_ℓ}(F, G) = Hom_{ℤ_ℓ}(F, G) ⊗_{ℤ_ℓ} ℚ_ℓ` of Stacks 03UR, since every integer prime to `ℓ`
is already a unit of `ℤ_ℓ`. -/
@[stacks 03UR "Hom_{Q_l}(F,G) = Hom_{Z_l}(F,G) localized at the powers of l",
  sga "4½ Rapport 2.9" "more general"]
public instance isLocalizedModule_mapIntLinearMap (X Y : C) :
    IsLocalizedModule (Submonoid.powers (ℓ : ℤ)) (mapIntLinearMap L X Y) where
  map_units x := by
    obtain ⟨k, hk⟩ := x.2
    haveI := isIso_map_nsmul_id ℓ L X k
    have hsmul : ∀ φ : L.obj X ⟶ L.obj Y, (x : ℤ) • φ = L.map ((ℓ ^ k) • 𝟙 X) ≫ φ := by
      intro φ
      rw [← hk, zpow_nsmul_eq, Functor.map_nsmul, L.map_id, nsmul_id_comp]
    refine (Module.End.isUnit_iff _).2 ⟨fun a b h => ?_, fun c => ?_⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hsmul, hsmul] at h
      exact (cancel_epi (L.map ((ℓ ^ k) • 𝟙 X))).1 h
    · refine ⟨inv (L.map ((ℓ ^ k) • 𝟙 X)) ≫ c, ?_⟩
      rw [Module.algebraMap_end_apply, hsmul, IsIso.hom_inv_id_assoc]
  surj y := by
    obtain ⟨k, g, hg⟩ := exists_nsmul_eq_map ℓ L y
    refine ⟨⟨g, ⟨(ℓ : ℤ) ^ k, k, rfl⟩⟩, ?_⟩
    rwa [Submonoid.smul_def, mapIntLinearMap_apply, zpow_nsmul_eq]
  exists_of_eq {a b} h := by
    rw [mapIntLinearMap_apply, mapIntLinearMap_apply] at h
    have h0 : L.map (a - b) = 0 := by rw [Functor.map_sub, h, sub_self]
    obtain ⟨k, hk⟩ := (map_eq_zero_iff ℓ L (a - b)).1 h0
    refine ⟨⟨(ℓ : ℤ) ^ k, k, rfl⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hk
    rwa [Submonoid.smul_def, Submonoid.smul_def, zpow_nsmul_eq, zpow_nsmul_eq]

end Localization

end Stacks.CategoryTheory

end
