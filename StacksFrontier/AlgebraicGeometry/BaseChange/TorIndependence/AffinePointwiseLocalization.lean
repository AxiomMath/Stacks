module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizations of modules along localizations of rings

A composite of localizations of modules at nested submonoids is a localization at the larger one.
For a localization of rings `B ⟶ B'` and a ring map `ρ : B' ⟶ C`, a map of `B'`-modules is a
localization at the elements becoming units in `C` exactly when it is one over `B`. For
localizations `R ⟶ R₁`, `A ⟶ A₁`, `C ⟶ C₁` of `R`-algebras over `R₁`, the ring map
`A ⊗_R C ⟶ A₁ ⊗_{R₁} C₁` is a localization.

## Main definitions

* `IsLocalizedModule.unitsComap`: the elements whose image under a ring map is a unit.
* `IsLocalization.tensorLocalizationMap`: the ring map `A ⊗_R C ⟶ A₁ ⊗_{R₁} C₁`.
* `IsLocalization.tensorSubmonoid`: the submonoid of pure tensors `w ⊗ z`.

## Main results

* `IsLocalizedModule.comp_of_le`: a composite of localizations at nested submonoids `T ≤ V` is a
  localization at `V`.
* `IsLocalizedModule.iff_restrictScalars_unitsComap`: localization at the elements becoming units
  in `C`, over `B'` and over `B`.
* `IsLocalizedModule.iff_of_exists_mul_mem`: localization at a submonoid is localization at any
  larger one each of whose elements divides an element of the smaller one.
* `IsLocalization.isLocalization_tensorLocalizationMap`: `A₁ ⊗_{R₁} C₁` is the localization of
  `A ⊗_R C` at the pure tensors `w ⊗ z`.
-/

@[expose] public noncomputable section

universe u

namespace IsLocalizedModule

/-- For submonoids `T ≤ V`, the composite of a localization at `T` and a localization at `V` is a
localization at `V`. -/
theorem comp_of_le {R M M₁ M₂ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (T V : Submonoid R)
    (hTV : T ≤ V) (g : M →ₗ[R] M₁) [IsLocalizedModule T g] (h : M₁ →ₗ[R] M₂)
    [IsLocalizedModule V h] : IsLocalizedModule V (h ∘ₗ g) := by
  constructor
  · exact IsLocalizedModule.map_units h
  · intro y
    obtain ⟨⟨x₁, v⟩, hx₁⟩ := IsLocalizedModule.surj V h y
    obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.surj T g x₁
    simp only [Submonoid.smul_def] at hx₁ hx
    refine ⟨⟨x, ⟨(t : R) * v, V.mul_mem (hTV t.2) v.2⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.comp_apply]
    rw [← hx, map_smul, ← hx₁, smul_smul, mul_comm]
  · intro x₁ x₂ e
    obtain ⟨⟨v, hv⟩, hvx⟩ := IsLocalizedModule.exists_of_eq (S := V) (f := h) e
    simp only [Submonoid.smul_def] at hvx
    rw [← map_smul, ← map_smul] at hvx
    obtain ⟨⟨t, ht⟩, htx⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) hvx
    simp only [Submonoid.smul_def] at htx
    refine ⟨⟨t * v, V.mul_mem (hTV ht) hv⟩, ?_⟩
    simp only [Submonoid.smul_def]
    rw [mul_smul, mul_smul, htx]

variable {B B' C : Type u} [CommRing B] [CommRing B'] [CommRing C] [Algebra B B'] (ρ : B' →+* C)
  (T : Submonoid B) [IsLocalization T B']

/-- The submonoid of a ring of the elements whose image under a ring map is a unit. -/
abbrev unitsComap {D : Type u} [CommRing D] (σ : D →+* C) : Submonoid D :=
  (IsUnit.submonoid C).comap σ

include T in
/-- **Localization at the units of `C`, read over a localization of rings.**  For a localization
`B ⟶ B'`, a map of `B'`-modules is a localization at the elements of `B'` that become units in
`C` exactly when, read over `B`, it is a localization at the elements of `B` that do. -/
theorem iff_restrictScalars_unitsComap {M N : Type u} [AddCommGroup M] [Module B M]
    [Module B' M] [IsScalarTower B B' M] [AddCommGroup N] [Module B N] [Module B' N]
    [IsScalarTower B B' N] (f : M →ₗ[B'] N) :
    IsLocalizedModule (unitsComap ρ) f ↔
      IsLocalizedModule (unitsComap (ρ.comp (algebraMap B B'))) (f.restrictScalars B) := by
  have hBN : ∀ (b : B) (y : N), b • y = (algebraMap B B' b) • y := fun b y =>
    (algebraMap_smul B' b y).symm
  have hBM : ∀ (b : B) (y : M), b • y = (algebraMap B B' b) • y := fun b y =>
    (algebraMap_smul B' b y).symm
  constructor
  · intro hf
    constructor
    · rintro ⟨b, hb⟩
      have := IsLocalizedModule.map_units (S := unitsComap ρ) f ⟨algebraMap B B' b, hb⟩
      rw [Module.End.isUnit_iff] at this ⊢
      convert this using 1
      funext y
      exact hBN b y
    · intro y
      obtain ⟨⟨x, ⟨u, hu⟩⟩, hx⟩ := IsLocalizedModule.surj (unitsComap ρ) f y
      obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj T u
      simp only [Submonoid.smul_def] at hx
      refine ⟨⟨(algebraMap B B' t) • x, ⟨b, ?_⟩⟩, ?_⟩
      · change IsUnit (ρ (algebraMap B B' b))
        rw [← hb, map_mul]
        exact hu.mul ((IsLocalization.map_units B' t).map ρ)
      · simp only [Submonoid.smul_def, LinearMap.restrictScalars_apply]
        rw [hBN, ← hb, map_smul, ← hx, smul_smul, mul_comm]
    · intro x₁ x₂ e
      obtain ⟨⟨u, hu⟩, hux⟩ := IsLocalizedModule.exists_of_eq (S := unitsComap ρ) (f := f) e
      obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj T u
      simp only [Submonoid.smul_def] at hux
      refine ⟨⟨b, ?_⟩, ?_⟩
      · change IsUnit (ρ (algebraMap B B' b))
        rw [← hb, map_mul]
        exact hu.mul ((IsLocalization.map_units B' t).map ρ)
      · simp only [Submonoid.smul_def]
        rw [hBM, hBM, ← hb, mul_comm, mul_smul, mul_smul, hux]
  · intro hf
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj T u
      have hb' : IsUnit (ρ (algebraMap B B' b)) := by
        rw [← hb, map_mul]
        exact hu.mul ((IsLocalization.map_units B' t).map ρ)
      have h1 := IsLocalizedModule.map_units (S := unitsComap (ρ.comp (algebraMap B B')))
        (f.restrictScalars B) ⟨b, hb'⟩
      rw [Module.End.isUnit_iff] at h1 ⊢
      have h2 : Function.Bijective (fun y : N => (algebraMap B B' (t : B)) • y) := by
        have := (IsLocalization.map_units B' t).map (algebraMap B' (Module.End B' N))
        rwa [Module.End.isUnit_iff] at this
      have h3 : (fun y : N => (algebraMap B B' b) • y) =
          (fun y : N => u • y) ∘ (fun y : N => (algebraMap B B' (t : B)) • y) := by
        funext y
        simp only [Function.comp_apply, smul_smul, ← hb]
      have h4 : Function.Bijective (fun y : N => (algebraMap B B' b) • y) := by
        convert h1 using 1
        funext y
        exact (hBN b y).symm
      rw [h3] at h4
      exact (Function.Bijective.of_comp_iff _ h2).1 h4
    · intro y
      obtain ⟨⟨x, ⟨b, hb⟩⟩, hx⟩ := IsLocalizedModule.surj
        (unitsComap (ρ.comp (algebraMap B B'))) (f.restrictScalars B) y
      simp only [Submonoid.smul_def] at hx
      exact ⟨⟨x, ⟨algebraMap B B' b, hb⟩⟩, by rwa [Submonoid.smul_def, ← hBN]⟩
    · intro x₁ x₂ e
      obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalizedModule.exists_of_eq
        (S := unitsComap (ρ.comp (algebraMap B B'))) (f := f.restrictScalars B) e
      simp only [Submonoid.smul_def] at hbx
      refine ⟨⟨algebraMap B B' b, hb⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rwa [← hBM, ← hBM]

/-- Localization at a submonoid is localization at any larger submonoid each of whose elements
divides an element of the smaller one. -/
theorem iff_of_exists_mul_mem {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (S T : Submonoid R) (hle : S ≤ T)
    (h' : ∀ x : T, ∃ m : R, m * x ∈ S) (f : M →ₗ[R] N) :
    IsLocalizedModule S f ↔ IsLocalizedModule T f := by
  refine ⟨fun hf => IsLocalizedModule.of_exists_mul_mem S T hle h' f, fun hf => ?_⟩
  constructor
  · exact fun s => IsLocalizedModule.map_units (S := T) f ⟨s, hle s.2⟩
  · intro y
    obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.surj T f y
    obtain ⟨m, hm⟩ := h' t
    refine ⟨⟨m • x, ⟨m * t, hm⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hx ⊢
    rw [mul_smul, hx, map_smul]
  · intro x₁ x₂ e
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) e
    obtain ⟨m, hm⟩ := h' c
    refine ⟨⟨m * c, hm⟩, ?_⟩
    simp only [Submonoid.smul_def] at hc ⊢
    rw [mul_smul, mul_smul, hc]

end IsLocalizedModule

namespace IsLocalization

open scoped TensorProduct

variable {R R₁ A A₁ C C₁ : Type u} [CommRing R] [CommRing R₁] [CommRing A] [CommRing A₁]
  [CommRing C] [CommRing C₁] [Algebra R R₁] [Algebra R A] [Algebra R C] [Algebra R₁ A₁]
  [Algebra R₁ C₁] [Algebra A A₁] [Algebra C C₁] [Algebra R A₁] [Algebra R C₁]
  [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [IsScalarTower R C C₁] [IsScalarTower R R₁ C₁]

variable (R R₁ A A₁ C C₁) in
/-- The ring map `A ⊗_R C ⟶ A₁ ⊗_{R₁} C₁` induced by ring maps `A ⟶ A₁`, `C ⟶ C₁` over
`R ⟶ R₁`. -/
def tensorLocalizationMap : A ⊗[R] C →+* A₁ ⊗[R₁] C₁ :=
  (Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (R := R₁) (S := R) (A := A₁) (B := C₁)).comp
      (IsScalarTower.toAlgHom R A A₁))
    (((Algebra.TensorProduct.includeRight (R := R₁) (A := A₁) (B := C₁)).restrictScalars R).comp
      (IsScalarTower.toAlgHom R C C₁))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- The map `tensorLocalizationMap` sends `a ⊗ c` to `a ⊗ c` with each factor mapped by its
algebra map. -/
theorem tensorLocalizationMap_tmul (a : A) (c : C) :
    tensorLocalizationMap R R₁ A A₁ C C₁ (a ⊗ₜ c) = algebraMap A A₁ a ⊗ₜ algebraMap C C₁ c := by
  change (algebraMap A A₁ a ⊗ₜ[R₁] (1 : C₁)) * ((1 : A₁) ⊗ₜ[R₁] algebraMap C C₁ c) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable (A C) in
/-- The submonoid of pure tensors `w ⊗ z`. -/
def tensorSubmonoid (W : Submonoid A) (Z : Submonoid C) : Submonoid (A ⊗[R] C) where
  carrier := {x | ∃ w ∈ W, ∃ z ∈ Z, x = w ⊗ₜ z}
  one_mem' := ⟨1, W.one_mem, 1, Z.one_mem, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w, hw, z, hz, rfl⟩ ⟨w', hw', z', hz', rfl⟩
    exact ⟨w * w', W.mul_mem hw hw', z * z', Z.mul_mem hz hz',
      Algebra.TensorProduct.tmul_mul_tmul _ _ _ _⟩

/-- **A tensor product of localizations over a localization is a localization.** For
localizations `R ⟶ R₁` at `U`, `A ⟶ A₁` at `W` and `C ⟶ C₁` at `Z`, the ring map
`A ⊗_R C ⟶ A₁ ⊗_{R₁} C₁` is a localization at the pure tensors `w ⊗ z` with `w ∈ W`, `z ∈ Z`. -/
theorem isLocalization_tensorLocalizationMap (U : Submonoid R) [IsLocalization U R₁]
    (W : Submonoid A) [IsLocalization W A₁] (Z : Submonoid C) [IsLocalization Z C₁] :
    letI := (tensorLocalizationMap R R₁ A A₁ C C₁).toAlgebra
    IsLocalization (tensorSubmonoid (R := R) A C W Z) (A₁ ⊗[R₁] C₁) := by
  let := (tensorLocalizationMap R R₁ A A₁ C C₁).toAlgebra
  let T := tensorSubmonoid (R := R) A C W Z
  let L := Localization T
  have hβ : ∀ x, algebraMap (A ⊗[R] C) (A₁ ⊗[R₁] C₁) x = tensorLocalizationMap R R₁ A A₁ C C₁ x :=
    fun _ => rfl
  have hU : ∀ u : U, IsUnit (algebraMap (A ⊗[R] C) L (algebraMap R (A ⊗[R] C) u)) := by
    intro u
    have hu : IsUnit (algebraMap A A₁ (algebraMap R A u)) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R₁ A₁]
      exact (IsLocalization.map_units R₁ u).map _
    obtain ⟨v, hv⟩ := hu
    obtain ⟨⟨a, w⟩, ha⟩ := IsLocalization.surj W (↑v⁻¹ : A₁)
    have h1 : algebraMap A A₁ (algebraMap R A u * a) = algebraMap A A₁ (w : A) := by
      rw [map_mul, ← ha, ← hv, ← mul_assoc, Units.mul_inv, one_mul]
    obtain ⟨w', hw'⟩ := IsLocalization.exists_of_eq (M := W) h1
    have hT : (w' * a : A) ⊗ₜ[R] (1 : C) * algebraMap R (A ⊗[R] C) u ∈ T := by
      refine ⟨w' * w, W.mul_mem w'.2 w.2, 1, Z.one_mem, ?_⟩
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      congr 1
      rw [mul_assoc, mul_comm a, ← hw', mul_comm]
    have := IsLocalization.map_units L (⟨_, hT⟩ : T)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_right this
  let : Algebra R₁ L := (IsLocalization.lift (M := U) (g := (algebraMap (A ⊗[R] C) L).comp
    (algebraMap R (A ⊗[R] C))) hU).toAlgebra
  have hR₁ : ∀ r : R, algebraMap R₁ L (algebraMap R R₁ r) =
      algebraMap (A ⊗[R] C) L (algebraMap R (A ⊗[R] C) r) := fun r =>
    IsLocalization.lift_eq (M := U) (g := (algebraMap (A ⊗[R] C) L).comp
      (algebraMap R (A ⊗[R] C))) hU r
  have hW : ∀ w : W, IsUnit (((algebraMap (A ⊗[R] C) L).comp
      Algebra.TensorProduct.includeLeftRingHom) (w : A)) := fun w =>
    IsLocalization.map_units L (⟨_, w, w.2, 1, Z.one_mem, rfl⟩ : T)
  have hZ : ∀ z : Z, IsUnit (((algebraMap (A ⊗[R] C) L).comp
      Algebra.TensorProduct.includeRight.toRingHom) (z : C)) := fun z =>
    IsLocalization.map_units L (⟨_, 1, W.one_mem, z, z.2, rfl⟩ : T)
  let f₁ : A₁ →+* L := IsLocalization.lift (M := W) hW
  let g₁ : C₁ →+* L := IsLocalization.lift (M := Z) hZ
  have hf₁ : ∀ r : R₁, f₁ (algebraMap R₁ A₁ r) = algebraMap R₁ L r := by
    have : f₁.comp (algebraMap R₁ A₁) = algebraMap R₁ L := by
      refine IsLocalization.ringHom_ext U (RingHom.ext fun r => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hR₁,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A A₁,
        IsLocalization.lift_eq]
      rfl
    exact RingHom.congr_fun this
  have hg₁ : ∀ r : R₁, g₁ (algebraMap R₁ C₁ r) = algebraMap R₁ L r := by
    have : g₁.comp (algebraMap R₁ C₁) = algebraMap R₁ L := by
      refine IsLocalization.ringHom_ext U (RingHom.ext fun r => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hR₁,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R C C₁,
        IsLocalization.lift_eq]
      change algebraMap (A ⊗[R] C) L ((1 : A) ⊗ₜ[R] algebraMap R C r) =
        algebraMap (A ⊗[R] C) L ((algebraMap R A r) ⊗ₜ[R] (1 : C))
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact RingHom.congr_fun this
  let φ : A₁ ⊗[R₁] C₁ →+* L := (Algebra.TensorProduct.lift (⟨f₁, hf₁⟩ : A₁ →ₐ[R₁] L)
    (⟨g₁, hg₁⟩ : C₁ →ₐ[R₁] L) (fun _ _ => Commute.all _ _)).toRingHom
  have hφ : ∀ x, φ (tensorLocalizationMap R R₁ A A₁ C C₁ x) = algebraMap (A ⊗[R] C) L x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul a c =>
      rw [tensorLocalizationMap_tmul]
      change f₁ (algebraMap A A₁ a) * g₁ (algebraMap C C₁ c) = _
      rw [IsLocalization.lift_eq, IsLocalization.lift_eq]
      change algebraMap (A ⊗[R] C) L (a ⊗ₜ[R] 1) * algebraMap (A ⊗[R] C) L (1 ⊗ₜ[R] c) = _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, w, hw, z, hz, rfl⟩
    rw [hβ, tensorLocalizationMap_tmul, ← mul_one (algebraMap A A₁ w),
      ← one_mul (algebraMap C C₁ z), ← Algebra.TensorProduct.tmul_mul_tmul]
    exact ((IsLocalization.map_units A₁ ⟨w, hw⟩).map
      (Algebra.TensorProduct.includeLeftRingHom (R := R₁) (B := C₁))).mul
      ((IsLocalization.map_units C₁ ⟨z, hz⟩).map
        (Algebra.TensorProduct.includeRight (R := R₁) (A := A₁) (B := C₁)))
  · intro y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨⟨x₁, t₁⟩, h₁⟩ := hx
      obtain ⟨⟨x₂, t₂⟩, h₂⟩ := hy
      refine ⟨⟨x₁ * t₂ + x₂ * t₁, t₁ * t₂⟩, ?_⟩
      simp only [map_mul, map_add] at h₁ h₂ ⊢
      rw [← h₁, ← h₂, Submonoid.coe_mul, map_mul]
      ring
    | tmul a₁ c₁ =>
      obtain ⟨⟨a, w⟩, ha⟩ := IsLocalization.surj W a₁
      obtain ⟨⟨c, z⟩, hc⟩ := IsLocalization.surj Z c₁
      refine ⟨⟨a ⊗ₜ c, ⟨w ⊗ₜ z, w, w.2, z, z.2, rfl⟩⟩, ?_⟩
      change a₁ ⊗ₜ[R₁] c₁ * tensorLocalizationMap R R₁ A A₁ C C₁ ((w : A) ⊗ₜ (z : C)) =
        tensorLocalizationMap R R₁ A A₁ C C₁ (a ⊗ₜ c)
      rw [tensorLocalizationMap_tmul, tensorLocalizationMap_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, ha, hc]
  · intro x y hxy
    have h := congrArg φ hxy
    rw [hβ, hβ, hφ, hφ] at h
    exact IsLocalization.exists_of_eq (M := T) h

end IsLocalization

