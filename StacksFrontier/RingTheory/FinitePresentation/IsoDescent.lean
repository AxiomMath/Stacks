module

public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

/-!
# Local isomorphisms of finitely presented algebras descend to a finite type stage

Let `R₀ ⊆ R` be a subring of finite type over `ℤ`, let `T₀` and `S₀` be finitely presented
`R₀`-algebras, and let `C = R ⊗_{R₀} T₀` and `B = R ⊗_{R₀} S₀` be the colimits of the directed
systems `R_μ ⊗_{R₀} T₀` and `R_μ ⊗_{R₀} S₀` of `Algebra.FiniteTypeSystem`. A map `C → B` that is
already defined at a stage `R_λ`, through `ψ : T₀ → R_λ ⊗_{R₀} S₀`, and that becomes bijective
after inverting an element `c` of `R_λ ⊗_{R₀} T₀`, is bijective after inverting `c` at every
sufficiently late stage.

## Main definitions

* `Algebra.FiniteTypeSystem.stageMap`: for `ψ : T₀ → R_λ ⊗_{R₀} S₀` and `R_λ ⊆ R_μ`, the
  `R_μ`-algebra map `R_μ ⊗_{R₀} T₀ → R_μ ⊗_{R₀} S₀` extending `ψ`.
* `Algebra.FiniteTypeSystem.awayStage`, `Algebra.FiniteTypeSystem.awayTransition`,
  `Algebra.FiniteTypeSystem.awayLeg`: the directed system of localizations
  `(R_μ ⊗_{R₀} T₀)_e` at the images of `e ∈ R_λ ⊗_{R₀} T₀`, with its maps to `C_e`.

## Main results

* `Algebra.FiniteTypeSystem.ringToRing_stageMap`: the stage maps are compatible with `C → B`.
* `Algebra.FiniteTypeSystem.awayLeg_jointly_surjective` and
  `Algebra.FiniteTypeSystem.exists_awayTransition_eq_zero`: `C_e` is the directed colimit of the
  `(R_μ ⊗_{R₀} T₀)_e`.
* `Algebra.FiniteTypeSystem.exists_forall_bijective_awayMap`: bijectivity of `C_c → B_c`
  descends to every late enough stage.

## Implementation notes

Bijectivity of a map of principal localizations is tested elementwise
(`Localization.awayMap_injective_iff`, `Localization.awayMap_surjective_iff`), so no comparison
of localizations is needed.

For surjectivity, the elements of `R_μ ⊗_{R₀} S₀` satisfying the criterion form an
`R_μ`-subalgebra, so it suffices to check the finitely many generators `1 ⊗ s` of `S₀`; each of
them satisfies the criterion in `B`, hence at a late stage.

For injectivity, the inverse `B_c → C_c` restricted to `S₀` is a map out of a finitely presented
`R₀`-algebra into the directed colimit `C_c` of the `(R_μ ⊗_{R₀} T₀)_c`, so it factors through a
stage (`AlgHom.exists_comp_eq_of_finitePresentation`). Its `R_μ`-linear extensions `σ_μ` satisfy
`σ_μ ∘ φ_μ = (localization map)` on the finitely many generators `1 ⊗ t` of `T₀` at a late stage,
because the two sides agree in `C_c`; then an element killed by `φ_μ` dies in
`(R_μ ⊗_{R₀} T₀)_c`.

The `R₀`-algebra structures on the localizations are the ones they inherit from the
`R₀`-algebras they localize, so the inverse is built as a map of `R₀`-algebras throughout.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.FiniteTypeSystem

variable {R : Type*} [CommRing R] (R₀ : Subring R)

/-- The transition maps `R_λ ⊗_{R₀} S₀ → R_μ ⊗_{R₀} S₀` compose. -/
theorem ringMap_ringMap {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀] {i j k : Index R₀}
    (hij : i ≤ j) (hjk : j ≤ k) (x : Ring R₀ S₀ i) :
    ringMap R₀ S₀ hjk (ringMap R₀ S₀ hij x) = ringMap R₀ S₀ (hij.trans hjk) x :=
  DirectedSystem.map_map (f := fun _ _ h ↦ ringMap R₀ S₀ h) hij hjk x

/-! ### Maps out of a stage -/

section StageMap

variable {T₀ S₀ : Type*} [CommRing T₀] [CommRing S₀] [Algebra R₀ T₀] [Algebra R₀ S₀]

/-- For `ψ : T₀ → R_λ ⊗_{R₀} S₀` and `R_λ ⊆ R_μ`, the `R_μ`-algebra map
`R_μ ⊗_{R₀} T₀ → R_μ ⊗_{R₀} S₀` extending `T₀ → R_λ ⊗_{R₀} S₀ → R_μ ⊗_{R₀} S₀`. -/
noncomputable def stageMap {i k : Index R₀} (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i) (h : i ≤ k) :
    Ring R₀ T₀ k →ₐ[Base R₀ k] Ring R₀ S₀ k :=
  Algebra.TensorProduct.lift (Algebra.ofId (Base R₀ k) (Ring R₀ S₀ k)) ((ringMap R₀ S₀ h).comp ψ)
    fun _ _ ↦ Commute.all _ _

/-- The stage map on pure tensors. -/
@[simp]
theorem stageMap_tmul {i k : Index R₀} (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i) (h : i ≤ k)
    (r : Base R₀ k) (t : T₀) :
    stageMap R₀ ψ h (r ⊗ₜ t) = algebraMap (Base R₀ k) (Ring R₀ S₀ k) r * ringMap R₀ S₀ h (ψ t) :=
  Algebra.TensorProduct.lift_tmul _ _ _ r t

/-- The stage map on `1 ⊗ t` is the transition of `ψ(t)`. -/
@[simp]
theorem stageMap_one_tmul {i k : Index R₀} (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i) (h : i ≤ k) (t : T₀) :
    stageMap R₀ ψ h ((1 : Base R₀ k) ⊗ₜ t) = ringMap R₀ S₀ h (ψ t) := by
  rw [stageMap_tmul, map_one, one_mul]

/-- The stage maps are compatible with the transition maps. -/
theorem stageMap_ringMap {i k l : Index R₀} (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i) (hik : i ≤ k)
    (hkl : k ≤ l) (y : Ring R₀ T₀ k) :
    stageMap R₀ ψ (hik.trans hkl) (ringMap R₀ T₀ hkl y) =
      ringMap R₀ S₀ hkl (stageMap R₀ ψ hik y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul r t =>
    rw [ringMap_tmul, stageMap_tmul, stageMap_tmul, map_mul, ringMap_ringMap, ringMap_algebraMap]

/-- `Base R₀ k → B` factors through `C` for a tower `R → C → B`. -/
private theorem algebraMap_base_comp (C B : Type*) [CommRing C] [CommRing B] [Algebra R C]
    [Algebra R B] [Algebra C B] [IsScalarTower R C B] {k : Index R₀} (b : Base R₀ k) :
    algebraMap (Base R₀ k) B b = algebraMap C B (algebraMap (Base R₀ k) C b) := by
  rw [IsScalarTower.algebraMap_apply (Base R₀ k) R B,
    IsScalarTower.algebraMap_apply (Base R₀ k) R C, ← IsScalarTower.algebraMap_apply R C B]

/-- The stage maps are compatible with a map `C → B` of the colimits that `ψ` is compatible
with. -/
theorem ringToRing_stageMap {C B : Type*} [CommRing C] [CommRing B] [Algebra R C] [Algebra R B]
    [Algebra C B] [IsScalarTower R C B] [Algebra T₀ C] [IsScalarTower R₀ T₀ C] [Algebra S₀ B]
    [IsScalarTower R₀ S₀ B] {i k : Index R₀} (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i)
    (hψ : ∀ t, algebraMap (Ring R₀ S₀ i) B (ψ t) = algebraMap C B (algebraMap T₀ C t))
    (h : i ≤ k) (y : Ring R₀ T₀ k) :
    ringToRing R₀ S₀ (S := B) k (stageMap R₀ ψ h y) =
      algebraMap C B (ringToRing R₀ T₀ (S := C) k y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul r t =>
    rw [stageMap_tmul, map_mul, ring_cocone]
    change _ * algebraMap (Ring R₀ S₀ i) B (ψ t) = _
    rw [hψ, ringToRing_tmul, map_mul]
    congr 1
    change ringToRing R₀ S₀ (S := B) k (r ⊗ₜ 1) = _
    rw [ringToRing_tmul, map_one, mul_one, algebraMap_base_comp R₀ C B]

end StageMap

/-! ### Localizations of the stages at an element of one stage -/

/-- An element of `A` dies in `A_a` if and only if some power of `a` kills it. -/
private theorem away_algebraMap_eq_zero_iff {A Aₚ : Type*} [CommRing A] [CommRing Aₚ]
    [Algebra A Aₚ] (a : A) [IsLocalization.Away a Aₚ] (x : A) :
    algebraMap A Aₚ x = 0 ↔ ∃ n : ℕ, a ^ n * x = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers a)]
  exact ⟨fun ⟨⟨_, n, rfl⟩, h⟩ ↦ ⟨n, h⟩, fun ⟨n, h⟩ ↦ ⟨⟨_, n, rfl⟩, h⟩⟩

/-- The map of principal localizations induced by an algebra map restricts to that algebra map. -/
private theorem away_mapₐ_algebraMap {K A B Aₚ Bₚ : Type*} [CommRing K] [CommRing A]
    [CommRing B] [CommRing Aₚ] [CommRing Bₚ] [Algebra K A] [Algebra K B] [Algebra A Aₚ]
    [Algebra K Aₚ] [IsScalarTower K A Aₚ] [Algebra B Bₚ] [Algebra K Bₚ] [IsScalarTower K B Bₚ]
    (f : A →ₐ[K] B) (a : A) [IsLocalization.Away a Aₚ] [IsLocalization.Away (f a) Bₚ] (x : A) :
    IsLocalization.Away.mapₐ Aₚ Bₚ f a (algebraMap A Aₚ x) = algebraMap B Bₚ (f x) := by
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

section Away

variable {T₀ : Type*} [CommRing T₀] [Algebra R₀ T₀] {i : Index R₀} (e : Ring R₀ T₀ i)

/-- The stages at or after `R_λ`. -/
abbrev Above (i : Index R₀) : Type _ := {k : Index R₀ // i ≤ k}

/-- The localization `(R_μ ⊗_{R₀} T₀)_e` of a stage at or after `R_λ` at the image of
`e ∈ R_λ ⊗_{R₀} T₀`. -/
abbrev awayStage (k : Above R₀ i) : Type _ := Localization.Away (ringMap R₀ T₀ k.2 e)

/-- For `R_μ ⊆ R_ν`, `(R_ν ⊗_{R₀} T₀)_e` is the localization of `R_ν ⊗_{R₀} T₀` at the image of
`e` under the composite `R_λ ⊗_{R₀} T₀ → R_μ ⊗_{R₀} T₀ → R_ν ⊗_{R₀} T₀`. -/
theorem isLocalization_awayStage {k l : Above R₀ i} (h : k.1 ≤ l.1) :
    IsLocalization.Away (ringMap R₀ T₀ h (ringMap R₀ T₀ k.2 e)) (awayStage R₀ e l) := by
  rw [ringMap_ringMap]
  infer_instance

/-- The transition map `(R_μ ⊗_{R₀} T₀)_e → (R_ν ⊗_{R₀} T₀)_e`. -/
noncomputable def awayTransition {k l : Above R₀ i} (h : k.1 ≤ l.1) :
    awayStage R₀ e k →ₐ[R₀] awayStage R₀ e l :=
  haveI := isLocalization_awayStage R₀ e h
  IsLocalization.Away.mapₐ (awayStage R₀ e k) (awayStage R₀ e l) (ringMap R₀ T₀ h)
    (ringMap R₀ T₀ k.2 e)

/-- The transition map `(R_μ ⊗_{R₀} T₀)_e → (R_ν ⊗_{R₀} T₀)_e` restricts to the transition map
`R_μ ⊗_{R₀} T₀ → R_ν ⊗_{R₀} T₀`. -/
theorem awayTransition_algebraMap {k l : Above R₀ i} (h : k.1 ≤ l.1) (y : Ring R₀ T₀ k.1) :
    awayTransition R₀ e h (algebraMap (Ring R₀ T₀ k.1) (awayStage R₀ e k) y) =
      algebraMap (Ring R₀ T₀ l.1) (awayStage R₀ e l) (ringMap R₀ T₀ h y) := by
  have := isLocalization_awayStage R₀ e h
  exact away_mapₐ_algebraMap (ringMap R₀ T₀ h) (ringMap R₀ T₀ k.2 e) y

/-- Algebra maps out of `(R_μ ⊗_{R₀} T₀)_e` are determined on `R_μ ⊗_{R₀} T₀`. -/
theorem awayStage_algHom_ext {k : Above R₀ i} {X : Type*} [CommRing X] [Algebra R₀ X]
    {f g : awayStage R₀ e k →ₐ[R₀] X}
    (H : ∀ y, f (algebraMap (Ring R₀ T₀ k.1) (awayStage R₀ e k) y) =
      g (algebraMap (Ring R₀ T₀ k.1) (awayStage R₀ e k) y)) :
    f = g :=
  IsLocalization.algHom_ext (Submonoid.powers (ringMap R₀ T₀ k.2 e)) (AlgHom.ext H)

/-- The localizations `(R_μ ⊗_{R₀} T₀)_e` and their transition maps form a directed system. -/
instance : DirectedSystem (awayStage R₀ e) fun _ _ h ↦ awayTransition R₀ e h where
  map_self k x := by
    have : awayTransition R₀ e (le_refl k.1) = AlgHom.id R₀ _ :=
      awayStage_algHom_ext R₀ e fun y ↦ by
        rw [awayTransition_algebraMap, AlgHom.id_apply,
          DirectedSystem.map_self (f := fun _ _ h ↦ ringMap R₀ T₀ h)]
    exact DFunLike.congr_fun this x
  map_map k l m hkl hlm x := by
    have : (awayTransition R₀ e hlm).comp (awayTransition R₀ e hkl) =
        awayTransition R₀ e (hkl.trans hlm) :=
      awayStage_algHom_ext R₀ e fun y ↦ by
        rw [AlgHom.comp_apply, awayTransition_algebraMap, awayTransition_algebraMap,
          awayTransition_algebraMap, ringMap_ringMap]
    exact DFunLike.congr_fun this x

variable {C : Type*} [CommRing C] [Algebra R C] [Algebra T₀ C] [IsScalarTower R₀ T₀ C]

/-- `C_e` is the localization of `C` at the image in `C` of the image of `e` in `R_μ ⊗_{R₀} T₀`. -/
theorem isLocalization_awayStage_leg (k : Above R₀ i) :
    IsLocalization.Away (ringToRing R₀ T₀ (S := C) k.1 (ringMap R₀ T₀ k.2 e))
      (Localization.Away (ringToRing R₀ T₀ (S := C) i e)) := by
  rw [ring_cocone]
  infer_instance

/-- The map `(R_μ ⊗_{R₀} T₀)_e → C_e` to the colimit. -/
noncomputable def awayLeg (k : Above R₀ i) :
    awayStage R₀ e k →ₐ[R₀] Localization.Away (ringToRing R₀ T₀ (S := C) i e) :=
  haveI := isLocalization_awayStage_leg R₀ e (C := C) k
  IsLocalization.Away.mapₐ (awayStage R₀ e k) (Localization.Away (ringToRing R₀ T₀ (S := C) i e))
    (ringToRing R₀ T₀ (S := C) k.1) (ringMap R₀ T₀ k.2 e)

/-- The map `(R_μ ⊗_{R₀} T₀)_e → C_e` restricts to the map `R_μ ⊗_{R₀} T₀ → C`. -/
theorem awayLeg_algebraMap (k : Above R₀ i) (y : Ring R₀ T₀ k.1) :
    awayLeg R₀ e (C := C) k (algebraMap (Ring R₀ T₀ k.1) (awayStage R₀ e k) y) =
      algebraMap C (Localization.Away (ringToRing R₀ T₀ (S := C) i e))
        (ringToRing R₀ T₀ (S := C) k.1 y) := by
  have := isLocalization_awayStage_leg R₀ e (C := C) k
  exact away_mapₐ_algebraMap (ringToRing R₀ T₀ (S := C) k.1) (ringMap R₀ T₀ k.2 e) y

/-- The maps `(R_μ ⊗_{R₀} T₀)_e → C_e` commute with the transition maps. -/
theorem awayLeg_awayTransition {k l : Above R₀ i} (h : k.1 ≤ l.1) (x : awayStage R₀ e k) :
    awayLeg R₀ e (C := C) l (awayTransition R₀ e h x) = awayLeg R₀ e (C := C) k x := by
  have : (awayLeg R₀ e (C := C) l).comp (awayTransition R₀ e h) = awayLeg R₀ e (C := C) k :=
    awayStage_algHom_ext R₀ e fun y ↦ by
      rw [AlgHom.comp_apply, awayTransition_algebraMap, awayLeg_algebraMap, awayLeg_algebraMap,
        ring_cocone]
  exact DFunLike.congr_fun this x

variable [Algebra.FiniteType ℤ R₀] [Algebra.IsPushout R₀ R T₀ C]

/-- `C_e` is the directed colimit of the `(R_μ ⊗_{R₀} T₀)_e`: every element comes from a stage. -/
theorem awayLeg_jointly_surjective (z : Localization.Away (ringToRing R₀ T₀ (S := C) i e)) :
    ∃ k x, awayLeg R₀ e (C := C) k x = z := by
  obtain ⟨⟨x, _, n, rfl⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (ringToRing R₀ T₀ (S := C) i e)) z
  dsimp only
  obtain ⟨k₀, y, hy⟩ := (ring_colimit R₀ T₀ (S := C)).1 x
  obtain ⟨k₁, hi, h0⟩ := exists_ge_ge i k₀
  let k : Above R₀ i := ⟨k₁, hi⟩
  refine ⟨k, IsLocalization.mk' (awayStage R₀ e k) (ringMap R₀ T₀ h0 y)
    (⟨ringMap R₀ T₀ hi e ^ n, n, rfl⟩ : Submonoid.powers (ringMap R₀ T₀ hi e)), ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  calc _ = awayLeg R₀ e (C := C) k (IsLocalization.mk' (awayStage R₀ e k) (ringMap R₀ T₀ h0 y)
          (⟨ringMap R₀ T₀ hi e ^ n, n, rfl⟩ : Submonoid.powers (ringMap R₀ T₀ hi e)) *
        algebraMap (Ring R₀ T₀ k.1) (awayStage R₀ e k) (ringMap R₀ T₀ hi e ^ n)) := by
        rw [map_mul, awayLeg_algebraMap, map_pow, map_pow, ring_cocone, map_pow]
    _ = _ := by rw [IsLocalization.mk'_spec, awayLeg_algebraMap, ring_cocone, hy]

/-- `C_e` is the directed colimit of the `(R_μ ⊗_{R₀} T₀)_e`: an element of a stage that dies in
`C_e` dies in a later stage. -/
theorem exists_awayTransition_eq_zero {k : Above R₀ i} (x : awayStage R₀ e k)
    (hx : awayLeg R₀ e (C := C) k x = 0) :
    ∃ l : Above R₀ i, ∃ h : k.1 ≤ l.1, awayTransition R₀ e h x = 0 := by
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (ringMap R₀ T₀ k.2 e)) x
  dsimp only at hx ⊢
  have hy : algebraMap C (Localization.Away (ringToRing R₀ T₀ (S := C) i e))
      (ringToRing R₀ T₀ (S := C) k.1 y) = 0 := by
    rw [← awayLeg_algebraMap, ← IsLocalization.mk'_spec (awayStage R₀ e k) y s, map_mul, hx,
      zero_mul]
  obtain ⟨p, hp⟩ := (away_algebraMap_eq_zero_iff (ringToRing R₀ T₀ (S := C) i e) _).mp hy
  have hp' : ringToRing R₀ T₀ (S := C) k.1 (ringMap R₀ T₀ k.2 e ^ p * y) =
      ringToRing R₀ T₀ (S := C) k.1 0 := by
    rwa [map_mul, map_pow, ring_cocone, map_zero]
  obtain ⟨l₁, h, hl⟩ := (ring_colimit R₀ T₀ (S := C)).2 k.1 _ _ hp'
  let l : Above R₀ i := ⟨l₁, k.2.trans h⟩
  refine ⟨l, h, ?_⟩
  have hz : algebraMap (Ring R₀ T₀ l.1) (awayStage R₀ e l) (ringMap R₀ T₀ h y) = 0 := by
    refine (away_algebraMap_eq_zero_iff (ringMap R₀ T₀ l.2 e) _).mpr ⟨p, ?_⟩
    rwa [map_zero, map_mul, map_pow, ringMap_ringMap] at hl
  have hu : IsUnit (algebraMap (Ring R₀ T₀ l.1) (awayStage R₀ e l) (ringMap R₀ T₀ h s)) := by
    obtain ⟨_, q, rfl⟩ := s
    rw [map_pow, map_pow, ringMap_ringMap]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow q
  refine (hu.mul_left_eq_zero).mp ?_
  rw [← awayTransition_algebraMap, ← map_mul, IsLocalization.mk'_spec, awayTransition_algebraMap,
    hz]

end Away

/-! ### Descent of bijectivity -/

/-- Two `R₀`-algebra maps out of `R_μ ⊗_{R₀} X` agreeing on `R_μ` and on `1 ⊗ x` for `x` in a
generating set of `X` are equal. -/
theorem ring_algHom_ext {X : Type*} [CommRing X] [Algebra R₀ X] {k : Index R₀} {Y : Type*}
    [Semiring Y] [Algebra R₀ Y] {f g : Ring R₀ X k →ₐ[R₀] Y} {s : Set X}
    (hs : Algebra.adjoin R₀ s = ⊤) (h₁ : ∀ b : Base R₀ k, f (b ⊗ₜ 1) = g (b ⊗ₜ 1))
    (h₂ : ∀ x ∈ s, f ((1 : Base R₀ k) ⊗ₜ x) = g ((1 : Base R₀ k) ⊗ₜ x)) : f = g :=
  Algebra.TensorProduct.ext (AlgHom.ext h₁) (AlgHom.ext_of_adjoin_eq_top hs h₂)

/-- **Local isomorphisms descend to a finite type stage.** Let `R₀ ⊆ R` be a subring of finite
type over `ℤ`, let `T₀` and `S₀` be finitely presented `R₀`-algebras with `C = R ⊗_{R₀} T₀` and
`B = R ⊗_{R₀} S₀`, and let `C → B` be an `R`-algebra map that comes from a stage `R_λ`: it agrees
on `T₀` with `ψ : T₀ → R_λ ⊗_{R₀} S₀`. If `C_c → B_c` is bijective for some
`c ∈ R_λ ⊗_{R₀} T₀`, then there is a stage `R_{λ'} ⊇ R_λ` such that for every `R_μ ⊇ R_{λ'}` the
map `(R_μ ⊗_{R₀} T₀)_c → (R_μ ⊗_{R₀} S₀)_{φ_μ(c)}` induced by the stage map `φ_μ` is bijective. -/
theorem exists_forall_bijective_awayMap [Algebra.FiniteType ℤ R₀]
    (T₀ S₀ : Type*) [CommRing T₀] [CommRing S₀] [Algebra R₀ T₀] [Algebra R₀ S₀]
    [Algebra.FinitePresentation R₀ T₀] [Algebra.FinitePresentation R₀ S₀]
    {C B : Type*} [CommRing C] [CommRing B] [Algebra R C] [Algebra R B] [Algebra C B]
    [IsScalarTower R C B] [Algebra T₀ C] [IsScalarTower R₀ T₀ C] [Algebra.IsPushout R₀ R T₀ C]
    [Algebra S₀ B] [IsScalarTower R₀ S₀ B] [Algebra.IsPushout R₀ R S₀ B]
    (i : Index R₀) (ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i)
    (hψ : ∀ t, algebraMap (Ring R₀ S₀ i) B (ψ t) = algebraMap C B (algebraMap T₀ C t))
    (c : Ring R₀ T₀ i)
    (hc : Function.Bijective
      (Localization.awayMap (algebraMap C B) (algebraMap (Ring R₀ T₀ i) C c))) :
    ∃ i' : Index R₀, ∃ hi : i ≤ i', ∀ k (hk : i' ≤ k),
      Function.Bijective (Localization.awayMap (stageMap R₀ ψ (hi.trans hk)).toRingHom
        (ringMap R₀ T₀ (hi.trans hk) c)) := by
  classical
  -- the colimit level
  let eS : Ring R₀ S₀ i := stageMap R₀ ψ (le_refl i) c
  let c' : C := ringToRing R₀ T₀ (S := C) i c
  have hc' : ringToRing R₀ S₀ (S := B) i eS = algebraMap C B c' :=
    ringToRing_stageMap R₀ ψ hψ (le_refl i) c
  let Cc := Localization.Away c'
  let Bc := Localization.Away (ringToRing R₀ S₀ (S := B) i eS)
  have hBc : IsLocalization.Away (algebraMap C B c') Bc := by
    rw [← hc']
    infer_instance
  have : IsLocalization.Away ((IsScalarTower.toAlgHom R₀ C B) c') Bc := hBc
  let g : Cc →ₐ[R₀] Bc := IsLocalization.Away.mapₐ Cc Bc (IsScalarTower.toAlgHom R₀ C B) c'
  have hg : Function.Bijective g := by
    obtain ⟨h1, h2⟩ := hc
    rw [Localization.awayMap_injective_iff] at h1
    rw [Localization.awayMap_surjective_iff] at h2
    change Function.Bijective (IsLocalization.Away.map Cc Bc (algebraMap C B) c')
    exact ⟨(IsLocalization.Away.map_injective_iff (S := Cc) (Q := Bc) _ _).mpr h1,
      (IsLocalization.Away.map_surjective_iff (S := Cc) (Q := Bc) _ _).mpr h2⟩
  have hgC (x : C) : g (algebraMap C Cc x) = algebraMap B Bc (algebraMap C B x) := by
    exact away_mapₐ_algebraMap (IsScalarTower.toAlgHom R₀ C B) c' x
  let e : Cc ≃ₐ[R₀] Bc := AlgEquiv.ofBijective g hg
  have he (x : C) : e.symm (algebraMap B Bc (algebraMap C B x)) = algebraMap C Cc x := by
    rw [AlgEquiv.symm_apply_eq]
    exact (hgC x).symm
  let w : S₀ →ₐ[R₀] Cc := (e.symm : Bc →ₐ[R₀] Cc).comp
    ((IsScalarTower.toAlgHom R₀ B Bc).comp (IsScalarTower.toAlgHom R₀ S₀ B))
  -- the localized system of the source and a stage through which `w` factors
  have : IsDirected (Above R₀ i) (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨m, hm⟩ := ({a.1, b.1} : Finset (Index R₀)).exists_le
    exact ⟨⟨m, a.2.trans (hm a.1 (by simp))⟩, hm a.1 (by simp), hm b.1 (by simp)⟩⟩
  have : Nonempty (Above R₀ i) := ⟨⟨i, le_rfl⟩⟩
  obtain ⟨⟨k₁, hik₁⟩, σ₀, hσ₀⟩ := AlgHom.exists_comp_eq_of_finitePresentation (A := R₀) (C := S₀)
    (G := awayStage R₀ c) (fun _ _ h ↦ awayTransition R₀ c h)
    (fun k ↦ awayLeg R₀ c (C := C) k) (fun _ _ h x ↦ awayLeg_awayTransition R₀ c h x)
    (awayLeg_jointly_surjective R₀ c) (fun k x hx ↦ by
      obtain ⟨l, h, hl⟩ := exists_awayTransition_eq_zero R₀ c x hx
      exact ⟨l, h, hl⟩) w
  have hw (s : S₀) : awayLeg R₀ c (C := C) ⟨k₁, hik₁⟩ (σ₀ s) = w s := DFunLike.congr_fun hσ₀ s
  -- the extensions of `σ₀` to the later stages
  let σ (k : Index R₀) (hk : k₁ ≤ k) :
      Ring R₀ S₀ k →ₐ[R₀] awayStage R₀ c ⟨k, hik₁.trans hk⟩ :=
    Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom R₀ (Ring R₀ T₀ k) (awayStage R₀ c ⟨k, hik₁.trans hk⟩)).comp
        Algebra.TensorProduct.includeLeft)
      ((awayTransition R₀ c (k := ⟨k₁, hik₁⟩) (l := ⟨k, hik₁.trans hk⟩) hk).comp σ₀)
      fun _ _ ↦ Commute.all _ _
  have hσ_tmul (k : Index R₀) (hk : k₁ ≤ k) (b : Base R₀ k) (s : S₀) :
      σ k hk (b ⊗ₜ s) = algebraMap (Ring R₀ T₀ k) (awayStage R₀ c ⟨k, hik₁.trans hk⟩)
        (b ⊗ₜ[R₀] (1 : T₀)) *
          awayTransition R₀ c (k := ⟨k₁, hik₁⟩) (l := ⟨k, hik₁.trans hk⟩) hk (σ₀ s) :=
    Algebra.TensorProduct.lift_tmul _ _ _ b s
  have hσnat (k l : Index R₀) (hk : k₁ ≤ k) (hkl : k ≤ l) (y : Ring R₀ S₀ k) :
      σ l (hk.trans hkl) (ringMap R₀ S₀ hkl y) =
        awayTransition R₀ c (k := ⟨k, hik₁.trans hk⟩) (l := ⟨l, hik₁.trans (hk.trans hkl)⟩) hkl
          (σ k hk y) := by
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul b s =>
      rw [ringMap_tmul, hσ_tmul, hσ_tmul, map_mul, awayTransition_algebraMap, ringMap_tmul]
      congr 1
      exact (DirectedSystem.map_map (F := awayStage R₀ c) (f := fun _ _ h ↦ awayTransition R₀ c h)
        (show (⟨k₁, hik₁⟩ : Above R₀ i) ≤ ⟨k, hik₁.trans hk⟩ from hk)
        (show (⟨k, hik₁.trans hk⟩ : Above R₀ i) ≤ ⟨l, hik₁.trans (hk.trans hkl)⟩ from hkl)
        (σ₀ s)).symm
  have hlegσ (y : Ring R₀ S₀ k₁) : awayLeg R₀ c (C := C) ⟨k₁, hik₁⟩ (σ k₁ le_rfl y) =
      e.symm (algebraMap B Bc (ringToRing R₀ S₀ (S := B) k₁ y)) := by
    have : (awayLeg R₀ c (C := C) ⟨k₁, hik₁⟩).comp (σ k₁ le_rfl) = (e.symm : Bc →ₐ[R₀] Cc).comp
        ((IsScalarTower.toAlgHom R₀ B Bc).comp (ringToRing R₀ S₀ (S := B) k₁)) := by
      refine ring_algHom_ext R₀ (s := Set.univ) (Algebra.adjoin_univ (R := R₀) (A := S₀))
        (fun b ↦ ?_) (fun s _ ↦ ?_)
      · simp only [AlgHom.comp_apply, hσ_tmul, map_one, mul_one, IsScalarTower.coe_toAlgHom',
          ringToRing_tmul, algebraMap_base_comp R₀ C B]
        exact (awayLeg_algebraMap R₀ c (C := C) ⟨k₁, hik₁⟩ _).trans
          (by rw [ringToRing_tmul, map_one, mul_one]; exact (he _).symm)
      · simp only [AlgHom.comp_apply, hσ_tmul, ← Algebra.TensorProduct.one_def, map_one, one_mul,
          awayLeg_awayTransition, hw, IsScalarTower.coe_toAlgHom', ringToRing_tmul]
        rfl
    exact DFunLike.congr_fun this y
  -- `σ ∘ φ` is the localization map at every late enough stage
  obtain ⟨gT, hgT⟩ := Algebra.FiniteType.out (R := R₀) (A := T₀)
  let δ (t : T₀) : awayStage R₀ c ⟨k₁, hik₁⟩ :=
    σ k₁ le_rfl (stageMap R₀ ψ hik₁ ((1 : Base R₀ k₁) ⊗ₜ t)) -
      algebraMap (Ring R₀ T₀ k₁) (awayStage R₀ c ⟨k₁, hik₁⟩) ((1 : Base R₀ k₁) ⊗ₜ t)
  have hδ (t : T₀) : awayLeg R₀ c (C := C) ⟨k₁, hik₁⟩ (δ t) = 0 := by
    rw [map_sub, hlegσ, ringToRing_stageMap R₀ ψ hψ hik₁ ((1 : Base R₀ k₁) ⊗ₜ t), he,
      awayLeg_algebraMap, sub_self]
  choose l hl hl0 using fun t ↦ exists_awayTransition_eq_zero R₀ c (δ t) (hδ t)
  obtain ⟨k₂, hk₂⟩ := (insert k₁ (gT.image fun t ↦ (l t).1)).exists_le
  have h₁₂ : k₁ ≤ k₂ := hk₂ _ (Finset.mem_insert_self _ _)
  have keyT (k : Index R₀) (hk : k₂ ≤ k) (a : Ring R₀ T₀ k) :
      σ k (h₁₂.trans hk) (stageMap R₀ ψ (hik₁.trans (h₁₂.trans hk)) a) =
        algebraMap (Ring R₀ T₀ k) (awayStage R₀ c ⟨k, hik₁.trans (h₁₂.trans hk)⟩) a := by
    have : (σ k (h₁₂.trans hk)).comp
        ((stageMap R₀ ψ (hik₁.trans (h₁₂.trans hk))).restrictScalars R₀) =
        IsScalarTower.toAlgHom R₀ (Ring R₀ T₀ k)
          (awayStage R₀ c ⟨k, hik₁.trans (h₁₂.trans hk)⟩) := by
      refine ring_algHom_ext R₀ hgT (fun b ↦ ?_) (fun t ht ↦ ?_)
      · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, stageMap_tmul, map_one,
          mul_one, IsScalarTower.coe_toAlgHom']
        change σ k _ (b ⊗ₜ 1) = _
        rw [hσ_tmul, map_one, map_one, mul_one]
      · have hlt : (l t).1 ≤ k :=
          (hk₂ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))).trans hk
        have e2 : (1 : Base R₀ k) ⊗ₜ[R₀] t =
            ringMap R₀ T₀ (h₁₂.trans hk) ((1 : Base R₀ k₁) ⊗ₜ t) := by
          rw [ringMap_tmul, map_one]
        have h0 : awayTransition R₀ c (k := ⟨k₁, hik₁⟩) (l := ⟨k, hik₁.trans (h₁₂.trans hk)⟩)
            (h₁₂.trans hk) (δ t) = 0 := by
          rw [← DirectedSystem.map_map (F := awayStage R₀ c)
            (f := fun _ _ h ↦ awayTransition R₀ c h) (hl t)
            (show l t ≤ ⟨k, hik₁.trans (h₁₂.trans hk)⟩ from hlt) (δ t), hl0 t, map_zero]
        simp only [δ, map_sub, sub_eq_zero] at h0
        change σ k (h₁₂.trans hk) (stageMap R₀ ψ (hik₁.trans (h₁₂.trans hk))
            ((1 : Base R₀ k) ⊗ₜ t)) = algebraMap (Ring R₀ T₀ k)
            (awayStage R₀ c ⟨k, hik₁.trans (h₁₂.trans hk)⟩) ((1 : Base R₀ k) ⊗ₜ t)
        rw [e2, stageMap_ringMap R₀ ψ hik₁ (h₁₂.trans hk), hσnat k₁ k le_rfl, h0,
          awayTransition_algebraMap]
    exact DFunLike.congr_fun this a
  -- surjectivity on the generators of `S₀` at late stages
  obtain ⟨gS, hgS⟩ := Algebra.FiniteType.out (R := R₀) (A := S₀)
  have hgen (s : S₀) : ∃ l : Index R₀, i ≤ l ∧ ∀ k (hk : l ≤ k) (hik : i ≤ k),
      ∃ (a : Ring R₀ T₀ k) (m : ℕ), stageMap R₀ ψ hik a =
        stageMap R₀ ψ hik (ringMap R₀ T₀ hik c) ^ m * ((1 : Base R₀ k) ⊗ₜ s) := by
    obtain ⟨x, m, hx⟩ := Localization.awayMap_surjective_iff.mp hc.2 (algebraMap S₀ B s)
    obtain ⟨j₀, x₀, hx₀⟩ := (ring_colimit R₀ T₀ (S := C)).1 x
    obtain ⟨j, hj⟩ := ({i, j₀} : Finset (Index R₀)).exists_le
    have hij : i ≤ j := hj i (by simp)
    have h0 : j₀ ≤ j := hj j₀ (by simp)
    have heq : ringToRing R₀ S₀ (S := B) j (stageMap R₀ ψ hij (ringMap R₀ T₀ h0 x₀)) =
        ringToRing R₀ S₀ (S := B) j (stageMap R₀ ψ hij (ringMap R₀ T₀ hij c) ^ m *
          ((1 : Base R₀ j) ⊗ₜ s)) := by
      rw [ringToRing_stageMap R₀ ψ hψ, ring_cocone, hx₀, hx, map_mul, map_pow,
        ringToRing_stageMap R₀ ψ hψ, ring_cocone, ringToRing_tmul, map_one, one_mul]
      rfl
    obtain ⟨l, hjl, hl⟩ := (ring_colimit R₀ S₀ (S := B)).2 j _ _ heq
    refine ⟨l, hij.trans hjl, fun k hlk hik ↦ ⟨ringMap R₀ T₀ (hjl.trans hlk)
      (ringMap R₀ T₀ h0 x₀), m, ?_⟩⟩
    have hl' := congrArg (ringMap R₀ S₀ hlk) hl
    rw [ringMap_ringMap, ringMap_ringMap, ← stageMap_ringMap R₀ ψ hij (hjl.trans hlk), map_mul,
      map_pow, ← stageMap_ringMap R₀ ψ hij (hjl.trans hlk), ringMap_ringMap, ringMap_tmul,
      map_one, ringMap_ringMap] at hl'
    rw [ringMap_ringMap]
    exact hl'
  choose l hil hl using hgen
  obtain ⟨k₃, hk₃⟩ := (insert k₂ (gS.image l)).exists_le
  have h₂₃ : k₂ ≤ k₃ := hk₃ _ (Finset.mem_insert_self _ _)
  have hik₃ : i ≤ k₃ := hik₁.trans (h₁₂.trans h₂₃)
  refine ⟨k₃, hik₃, fun k hk ↦ ⟨?_, ?_⟩⟩
  · refine Localization.awayMap_injective_iff.mpr fun a ha ↦ ?_
    have h := keyT k (h₂₃.trans hk) a
    change stageMap R₀ ψ (hik₃.trans hk) a = 0 at ha
    rw [ha, map_zero] at h
    exact (away_algebraMap_eq_zero_iff _ _).mp h.symm
  · refine Localization.awayMap_surjective_iff.mpr fun b ↦ ?_
    let d := stageMap R₀ ψ (hik₃.trans hk) (ringMap R₀ T₀ (hik₃.trans hk) c)
    let Sub : Subalgebra (Base R₀ k) (Ring R₀ S₀ k) :=
      { carrier := {b | ∃ (a : Ring R₀ T₀ k) (m : ℕ), stageMap R₀ ψ (hik₃.trans hk) a = d ^ m * b}
        mul_mem' := by
          rintro b₁ b₂ ⟨a₁, m₁, h₁⟩ ⟨a₂, m₂, h₂⟩
          exact ⟨a₁ * a₂, m₁ + m₂, by rw [map_mul, h₁, h₂, pow_add]; ring⟩
        add_mem' := by
          rintro b₁ b₂ ⟨a₁, m₁, h₁⟩ ⟨a₂, m₂, h₂⟩
          refine ⟨ringMap R₀ T₀ (hik₃.trans hk) c ^ m₂ * a₁ +
            ringMap R₀ T₀ (hik₃.trans hk) c ^ m₁ * a₂, m₁ + m₂, ?_⟩
          rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁, h₂, pow_add]
          ring
        algebraMap_mem' := fun r ↦ ⟨algebraMap _ _ r, 0, by rw [AlgHom.commutes, pow_zero,
          one_mul]⟩ }
    have hSub : (⊤ : Subalgebra (Base R₀ k) (Ring R₀ S₀ k)) ≤ Sub := by
      rw [← Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Base R₀ k) (gS : Set S₀)
        hgS, Algebra.adjoin_le_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact hl s k ((hk₃ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs))).trans hk)
        (hik₃.trans hk)
    obtain ⟨a, m, ham⟩ := hSub (Algebra.mem_top (x := b))
    exact ⟨a, m, ham⟩

end Algebra.FiniteTypeSystem

end
