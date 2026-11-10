module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsBaseChange

/-!
# Transport of places, completions and adeles along an isomorphism of fields

Let `σ : K ≃+* K'` be an isomorphism of fields. A place `w` of `K'` pulls back to the place
`σ⁻¹(w)` of `K`, the completion of `K` at `σ⁻¹(w)` is isomorphic to the completion of `K'` at `w`
by the extension of `σ`, compatibly with the rings of integers and with the embeddings of `K` and
`K'`, and these isomorphisms assemble to an isomorphism of adele rings `A_K ≃+* A_{K'}` mapping
the integral adeles onto the integral adeles and the principal adeles onto the principal adeles.

## Main definitions

* `Stacks.Drinfeld.placeComap` — the place `σ⁻¹(w)` of `K` under a place `w` of `K'`.
* `Stacks.Drinfeld.completionEquiv` — `K_{σ⁻¹ w} ≃+* K'_w`.
* `Stacks.Drinfeld.adeleMap` — the induced map `A_K →+* A_{K'}`.
* `Stacks.Drinfeld.adeleEquiv` — the induced isomorphism `A_K ≃+* A_{K'}`.
* `Stacks.Drinfeld.glMap` — the induced map `GL₂(A_K) →* GL₂(A_{K'})`.
* `Stacks.Drinfeld.placeEquiv` — the bijection of places induced by `σ`.

## Main results

* `Stacks.Drinfeld.completionEquiv_mem_integers_iff` — `O_{σ⁻¹ w}` maps onto `O_w`.
* `Stacks.Drinfeld.completionEquiv_coeRingHom` — compatibility with `K → K_v`.
* `Stacks.Drinfeld.adeleMap_mem_integralAdeles_iff`,
  `Stacks.Drinfeld.adeleMap_mem_principalAdeles_iff` — compatibility with the integral and the
  principal adeles.
* `Stacks.Drinfeld.isCuspFormCentralChar_comp_glMap`,
  `Stacks.Drinfeld.cuspFormsCentralChar_ne_bot_of_ringEquiv` — transport of `C(Λ)` along `σ`.
-/

@[expose] public noncomputable section

open Matrix UniformSpace
open scoped RestrictedProduct

universe u w

section UniformCongr

variable {R S : Type*} [Field R] [Field S] {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀']

/-- An isomorphism of fields carrying a valuation `v` to a valuation equivalent to `w` is
uniformly continuous for the valuation uniformities. -/
public theorem Valuation.uniformContinuous_congr_of_isEquiv_comap {v : Valuation R Γ₀}
    {w : Valuation S Γ₀'} (f : R ≃+* S) (h : v.IsEquiv (w.comap f.toRingHom)) :
    UniformContinuous (WithVal.congr v w f) := by
  refine uniformContinuous_of_continuousAt_zero (WithVal.congr v w f) ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ :=
    Valuation.restrict_exists_div_eq (Valued.v : Valuation (WithVal w) Γ₀') γ
  set r' : WithVal v := (WithVal.congr v w f).symm r
  set s' : WithVal v := (WithVal.congr v w f).symm s
  have hcomp : ∀ a : WithVal v, (Valued.v : Valuation (WithVal w) Γ₀') (WithVal.congr v w f a) =
      w.comap f.toRingHom a.ofVal := fun a => rfl
  have hr' : WithVal.congr v w f r' = r := by simp [r']
  have hs' : WithVal.congr v w f s' = s := by simp [s']
  have hpos : ∀ a : WithVal v, 0 < (Valued.v : Valuation (WithVal w) Γ₀') (WithVal.congr v w f a) →
      0 < (Valued.v : Valuation (WithVal v) Γ₀) a := by
    intro a ha
    rw [hcomp] at ha
    exact h.pos_iff.2 ha
  have hr'₀ : 0 < (Valued.v : Valuation (WithVal v) Γ₀) r' := hpos r' (by rwa [hr'])
  have hs'₀ : 0 < (Valued.v : Valuation (WithVal v) Γ₀) s' := hpos s' (by rwa [hs'])
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal v) Γ₀).restrict r' /
    (Valued.v : Valuation (WithVal v) Γ₀).restrict s') ?_, fun x hx => ?_⟩
  · exact div_ne_zero ((Valuation.restrict_pos_iff _ _).2 hr'₀).ne'
      ((Valuation.restrict_pos_iff _ _).2 hs'₀).ne'
  simp only [Units.val_mk0, Set.mem_ofPred_eq] at hx ⊢
  rw [← hr, lt_div_iff₀ ((Valuation.restrict_pos_iff _ _).2 hs₀), ← map_mul,
    Valuation.restrict_lt_iff]
  rw [lt_div_iff₀ ((Valuation.restrict_pos_iff _ _).2 hs'₀), ← map_mul,
    Valuation.restrict_lt_iff] at hx
  rw [← hr', ← hs', ← map_mul, hcomp, hcomp]
  exact h.lt_iff_lt.1 hx

end UniformCongr

namespace Stacks.Drinfeld

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

section Places

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- The place `σ⁻¹(w)` of `K` under a place `w` of `K'`. -/
public def placeComap (w : Place K') : Place K :=
  ⟨w.1.comap σ.toRingHom, fun h => w.2 (by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have : σ.symm y ∈ w.1.comap σ.toRingHom := h ▸ trivial
    simpa [ValuationSubring.mem_comap] using this)⟩

/-- `y` lies in the valuation ring of `σ⁻¹(w)` exactly when `σ y` lies in that of `w`. -/
@[simp]
public theorem mem_placeComap {w : Place K'} {y : K} : y ∈ (placeComap σ w).1 ↔ σ y ∈ w.1 :=
  ValuationSubring.mem_comap

/-- Pulling a place of `K` back along `σ⁻¹` and then along `σ` returns it. -/
public theorem placeComap_symm_placeComap (v : Place K) :
    placeComap σ (placeComap σ.symm v) = v :=
  Subtype.ext (by ext y; simp)

/-- Pulling a place of `K'` back along `σ` and then along `σ⁻¹` returns it. -/
public theorem placeComap_placeComap_symm (w : Place K') :
    placeComap σ.symm (placeComap σ w) = w :=
  Subtype.ext (by ext y; simp)

/-- `w ↦ σ⁻¹(w)` is injective. -/
public theorem placeComap_injective : Function.Injective (placeComap σ) := fun w w' h => by
  rw [← placeComap_placeComap_symm σ w, h, placeComap_placeComap_symm]

/-- `w ↦ σ⁻¹(w)` is surjective. -/
public theorem placeComap_surjective : Function.Surjective (placeComap σ) := fun v =>
  ⟨placeComap σ.symm v, placeComap_symm_placeComap σ v⟩

end Places

section Completion

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- The valuation of `σ⁻¹(w)` is equivalent to that of `w` pulled back along `σ`. -/
public theorem isEquiv_valuation_comap {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) :
    v.1.valuation.IsEquiv (w.1.valuation.comap σ.toRingHom) := by
  refine Valuation.isEquiv_iff_val_le_one.2 fun {y} => ?_
  rw [ValuationSubring.valuation_le_one_iff, Valuation.comap_apply,
    ValuationSubring.valuation_le_one_iff, h, ValuationSubring.mem_comap]

/-- `σ` as a uniform isomorphism `K_{σ⁻¹ w} ⊇ K ≃ K' ⊆ K'_w` for the valuation uniformities. -/
public def withValUniformEquiv {v : Place K} {w : Place K'} (h : v.1 = w.1.comap σ.toRingHom) :
    WithVal v.1.valuation ≃ᵤ WithVal w.1.valuation where
  toEquiv := (WithVal.congr v.1.valuation w.1.valuation σ).toEquiv
  uniformContinuous_toFun :=
    Valuation.uniformContinuous_congr_of_isEquiv_comap σ (isEquiv_valuation_comap σ h)
  uniformContinuous_invFun := by
    refine Valuation.uniformContinuous_congr_of_isEquiv_comap σ.symm ?_
    refine Valuation.isEquiv_iff_val_le_one.2 fun {y} => ?_
    rw [ValuationSubring.valuation_le_one_iff, Valuation.comap_apply,
      ValuationSubring.valuation_le_one_iff, h, ValuationSubring.mem_comap]
    simp

/-- The map of completions `K_v →+* K'_w` induced by `σ`, where `v = σ⁻¹(w)`. -/
public def completionMap {v : Place K} {w : Place K'} (h : v.1 = w.1.comap σ.toRingHom) :
    v.completion →+* w.completion :=
  Completion.mapRingHom (WithVal.congr v.1.valuation w.1.valuation σ).toRingHom
    (withValUniformEquiv σ h).uniformContinuous.continuous

/-- On an element of `K`, the map of completions is `σ`. -/
public theorem completionMap_coe {v : Place K} {w : Place K'} (h : v.1 = w.1.comap σ.toRingHom)
    (a : WithVal v.1.valuation) :
    completionMap σ h (a : Completion (WithVal v.1.valuation)) =
      ((WithVal.congr v.1.valuation w.1.valuation σ a : WithVal w.1.valuation) :
        Completion (WithVal w.1.valuation)) :=
  Completion.mapRingHom_coe _ a

/-- The map of completions induced by `σ` is continuous. -/
public theorem continuous_completionMap {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) : Continuous (completionMap σ h) :=
  Completion.continuous_map

/-- If `v = σ⁻¹(w)` then `w = σ(v)`, the pullback of `v` along `σ⁻¹`. -/
public theorem comap_symm_of_eq_comap {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) : w.1 = v.1.comap σ.symm.toRingHom := by
  ext y
  rw [ValuationSubring.mem_comap, h, ValuationSubring.mem_comap]
  simp

/-- The isomorphism of completions `K_v ≃+* K'_w` induced by `σ`, where `v = σ⁻¹(w)`. -/
public def completionEquiv {v : Place K} {w : Place K'} (h : v.1 = w.1.comap σ.toRingHom) :
    v.completion ≃+* w.completion where
  toFun := completionMap σ h
  invFun := completionMap σ.symm (comap_symm_of_eq_comap σ h)
  left_inv z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq ((continuous_completionMap _ _).comp
        (continuous_completionMap _ _)) continuous_id
    | ih a =>
      rw [completionMap_coe, completionMap_coe]
      congr 1
      simp
  right_inv z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq ((continuous_completionMap _ _).comp
        (continuous_completionMap _ _)) continuous_id
    | ih a =>
      rw [completionMap_coe, completionMap_coe]
      congr 1
      simp
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism of completions agrees with the map of completions. -/
public theorem completionEquiv_apply {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) (z : v.completion) :
    completionEquiv σ h z = completionMap σ h z := rfl

/-- The inverse of the isomorphism of completions is the map of completions induced by `σ⁻¹`. -/
public theorem completionEquiv_symm_apply {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) (z : w.completion) :
    (completionEquiv σ h).symm z = completionMap σ.symm (comap_symm_of_eq_comap σ h) z := rfl

/-- The isomorphism of completions induced by `σ` is continuous. -/
public theorem continuous_completionEquiv {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) : Continuous (completionEquiv σ h) :=
  continuous_completionMap σ h

/-- The isomorphism of completions is compatible with the embeddings `K → K_v` and `K' → K'_w`. -/
public theorem completionEquiv_coeRingHom {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) (y : K) :
    completionEquiv σ h (v.coeRingHom y) = w.coeRingHom (σ y) :=
  completionMap_coe σ h (WithVal.toVal v.1.valuation y)

/-- The image in `K'_w` of an element `y` of `K` lies in `O_w` exactly when the image of `y` in
`K_v` lies in `O_v`. -/
theorem completionEquiv_coeRingHom_mem_integers_iff {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) (y : K) :
    completionEquiv σ h (v.coeRingHom y) ∈ w.integers ↔ v.coeRingHom y ∈ v.integers := by
  rw [completionEquiv_coeRingHom, Place.integers, Place.integers,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    Place.valued_coeRingHom, Place.valued_coeRingHom, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.valuation_le_one_iff, h, ValuationSubring.mem_comap]
  rfl

/-- `σ` maps `O_v` onto `O_w`. -/
public theorem completionEquiv_mem_integers_iff {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) (z : v.completion) :
    completionEquiv σ h z ∈ w.integers ↔ z ∈ v.integers := by
  induction z using Completion.induction_on with
  | hp =>
    have h1 : IsClopen {z : v.completion | z ∈ v.integers} :=
      Valued.isClopen_valuationSubring v.completion
    have h2 : IsClopen ((completionEquiv σ h) ⁻¹' {z : w.completion | z ∈ w.integers}) :=
      (Valued.isClopen_valuationSubring w.completion).preimage (continuous_completionEquiv σ h)
    have : {z : v.completion | completionEquiv σ h z ∈ w.integers ↔ z ∈ v.integers} =
        ((completionEquiv σ h) ⁻¹' {z | z ∈ w.integers} ∩ {z | z ∈ v.integers}) ∪
        (((completionEquiv σ h) ⁻¹' {z | z ∈ w.integers})ᶜ ∩ {z | z ∈ v.integers}ᶜ) := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_compl_iff]; tauto
    rw [this]
    exact ((h2.isClosed.inter h1.isClosed).union (h2.compl.isClosed.inter h1.compl.isClosed))
  | ih a => exact completionEquiv_coeRingHom_mem_integers_iff σ h a.ofVal

end Completion

section Adeles

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- The ring homomorphism `A_K →+* A_{K'}` induced by `σ`: its component at a place `w` of `K'`
is the image under `K_{σ⁻¹ w} ≃+* K'_w` of the component at `σ⁻¹(w)`. -/
public def adeleMap : AdeleRing K →+* AdeleRing K' :=
  RestrictedProduct.mapAlongRingHom (fun v : Place K => v.completion)
    (fun w : Place K' => w.completion) (placeComap σ)
    (placeComap_injective σ).tendsto_cofinite
    (fun w => (completionEquiv σ (v := placeComap σ w) (w := w) rfl).toRingHom)
    (Filter.Eventually.of_forall fun w z hz =>
      (completionEquiv_mem_integers_iff σ (v := placeComap σ w) (w := w) rfl z).2 hz)

/-- The component of `adeleMap σ x` at `w` is the image of the component of `x` at `σ⁻¹(w)`. -/
public theorem adeleMap_apply (x : AdeleRing K) (w : Place K') :
    adeleMap σ x w = completionEquiv σ (v := placeComap σ w) (w := w) rfl (x (placeComap σ w)) :=
  rfl

/-- The component of `x` at equal places, read through `σ`. -/
public theorem completionEquiv_congr_place (x : AdeleRing K) {v₁ v₂ : Place K} (e : v₁ = v₂)
    {w : Place K'} (h₁ : v₁.1 = w.1.comap σ.toRingHom) (h₂ : v₂.1 = w.1.comap σ.toRingHom) :
    completionEquiv σ h₁ (x v₁) = completionEquiv σ h₂ (x v₂) := by
  subst e; rfl

/-- The adele map of `σ⁻¹` is a left inverse of the adele map of `σ`. -/
public theorem adeleMap_symm_adeleMap (x : AdeleRing K) : adeleMap σ.symm (adeleMap σ x) = x := by
  ext v
  rw [adeleMap_apply, adeleMap_apply]
  have hv : v.1 = (placeComap σ.symm v).1.comap σ.toRingHom :=
    congrArg Subtype.val (placeComap_symm_placeComap σ v).symm
  rw [completionEquiv_congr_place σ x (placeComap_symm_placeComap σ v) rfl hv]
  exact (completionEquiv σ hv).symm_apply_apply (x v)

/-- The adele map of `σ⁻¹` is a right inverse of the adele map of `σ`. -/
public theorem adeleMap_adeleMap_symm (x : AdeleRing K') : adeleMap σ (adeleMap σ.symm x) = x := by
  have := adeleMap_symm_adeleMap σ.symm x
  rwa [RingEquiv.symm_symm] at this

/-- The isomorphism of adele rings `A_K ≃+* A_{K'}` induced by `σ`. -/
public def adeleEquiv : AdeleRing K ≃+* AdeleRing K' where
  toFun := adeleMap σ
  invFun := adeleMap σ.symm
  left_inv := adeleMap_symm_adeleMap σ
  right_inv := adeleMap_adeleMap_symm σ
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism of adele rings acts as the adele map of `σ`. -/
@[simp]
public theorem adeleEquiv_apply (x : AdeleRing K) : adeleEquiv σ x = adeleMap σ x := rfl

/-- The inverse of the isomorphism of adele rings acts as the adele map of `σ⁻¹`. -/
@[simp]
public theorem adeleEquiv_symm_apply (x : AdeleRing K') :
    (adeleEquiv σ).symm x = adeleMap σ.symm x := rfl

/-- The adele map of `σ` is injective. -/
public theorem adeleMap_injective : Function.Injective (adeleMap σ) :=
  (adeleEquiv σ).injective

/-- The adele map of `σ` is surjective. -/
public theorem adeleMap_surjective : Function.Surjective (adeleMap σ) :=
  (adeleEquiv σ).surjective

/-- The adele map of `σ` maps integral adeles to integral adeles. -/
public theorem adeleMap_mem_integralAdeles {x : AdeleRing K} (hx : x ∈ integralAdeles K) :
    adeleMap σ x ∈ integralAdeles K' := fun w =>
  (completionEquiv_mem_integers_iff σ (v := placeComap σ w) (w := w) rfl _).2 (hx _)

/-- An adele is integral exactly when its image under the adele map of `σ` is integral. -/
public theorem adeleMap_mem_integralAdeles_iff {x : AdeleRing K} :
    adeleMap σ x ∈ integralAdeles K' ↔ x ∈ integralAdeles K := by
  refine ⟨fun h => ?_, adeleMap_mem_integralAdeles σ⟩
  rw [← adeleMap_symm_adeleMap σ x]
  exact adeleMap_mem_integralAdeles σ.symm h

/-- The adele map of `σ` maps principal adeles to principal adeles. -/
public theorem adeleMap_mem_principalAdeles {x : AdeleRing K} (hx : x ∈ principalAdeles K) :
    adeleMap σ x ∈ principalAdeles K' := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨σ c, fun w => ?_⟩
  rw [adeleMap_apply, hc]
  exact completionEquiv_coeRingHom σ (v := placeComap σ w) (w := w) rfl c

/-- An adele is principal exactly when its image under the adele map of `σ` is principal. -/
public theorem adeleMap_mem_principalAdeles_iff {x : AdeleRing K} :
    adeleMap σ x ∈ principalAdeles K' ↔ x ∈ principalAdeles K := by
  refine ⟨fun h => ?_, adeleMap_mem_principalAdeles σ⟩
  rw [← adeleMap_symm_adeleMap σ x]
  exact adeleMap_mem_principalAdeles σ.symm h

/-- The induced map `GL₂(A_K) →* GL₂(A_{K'})`. -/
public def glMap : GL (Fin 2) (AdeleRing K) →* GL (Fin 2) (AdeleRing K') :=
  Matrix.GeneralLinearGroup.map (adeleMap σ)

/-- The entries of `glMap σ x` are the images of the entries of `x` under the adele map. -/
public theorem glMap_apply (x : GL (Fin 2) (AdeleRing K)) (i j : Fin 2) :
    (glMap σ x : Matrix (Fin 2) (Fin 2) (AdeleRing K')) i j =
      adeleMap σ ((x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) := rfl

/-- The map `GL₂(A_{K'}) →* GL₂(A_K)` of `σ⁻¹` is a left inverse of that of `σ`. -/
public theorem glMap_symm_glMap (x : GL (Fin 2) (AdeleRing K)) : glMap σ.symm (glMap σ x) = x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact adeleMap_symm_adeleMap σ _

/-- The map `GL₂(A_{K'}) →* GL₂(A_K)` of `σ⁻¹` is a right inverse of that of `σ`. -/
public theorem glMap_glMap_symm (x : GL (Fin 2) (AdeleRing K')) :
    glMap σ (glMap σ.symm x) = x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact adeleMap_adeleMap_symm σ _

/-- `σ` maps the unipotent matrix `(1, z; 0, 1)` to `(1, σ z; 0, 1)`. -/
public theorem glMap_upperRightHom (z : AdeleRing K) :
    glMap σ (GeneralLinearGroup.upperRightHom z) =
      GeneralLinearGroup.upperRightHom (adeleMap σ z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMap_apply, GeneralLinearGroup.upperRightHom]

/-- `σ` maps the scalar matrix of an idele `c` to the scalar matrix of the image of `c`. -/
public theorem glMap_scalarGL (c : (AdeleRing K)ˣ) :
    glMap σ (scalarGL c) = scalarGL (Units.map (adeleMap σ).toMonoidHom c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMap_apply, coe_scalarGL]

/-- `σ` maps `GL₂(S)` into `GL₂(S')` when `adeleMap σ` maps the subring `S` into `S'`. -/
private theorem glMap_map_subtype {S : Subring (AdeleRing K)} {S' : Subring (AdeleRing K')}
    (hS : ∀ {x}, x ∈ S → adeleMap σ x ∈ S') (κ : GL (Fin 2) S) :
    ∃ κ' : GL (Fin 2) S', glMap σ (GeneralLinearGroup.map S.subtype κ) =
      GeneralLinearGroup.map S'.subtype κ' :=
  ⟨GeneralLinearGroup.map ((adeleMap σ).restrict _ _ fun _ => hS) κ,
    Units.ext (Matrix.ext fun _ _ => rfl)⟩

/-- `σ` maps `GL₂(O_K)` into `GL₂(O_{K'})`. -/
public theorem glMap_mapO (κ : GL (Fin 2) (integralAdeles K)) :
    ∃ κ' : GL (Fin 2) (integralAdeles K'), glMap σ (mapO κ) = mapO κ' :=
  glMap_map_subtype σ (adeleMap_mem_integralAdeles σ) κ

/-- `σ` maps `GL₂(K)` into `GL₂(K')`. -/
public theorem glMap_mapK (γ : GL (Fin 2) (principalAdeles K)) :
    ∃ γ' : GL (Fin 2) (principalAdeles K'), glMap σ (mapK γ) = mapK γ' :=
  glMap_map_subtype σ (adeleMap_mem_principalAdeles σ) γ

/-- The entries of `σ(x) E₁₂ σ(x)⁻¹` are the images of the entries of `x E₁₂ x⁻¹`. -/
public theorem conjE_glMap (x : GL (Fin 2) (AdeleRing K)) (i j : Fin 2) :
    conjE K' (glMap σ x) i j = adeleMap σ (conjE K x i j) := by
  have hinv : glMap σ x⁻¹ = (glMap σ x)⁻¹ := map_inv _ _
  simp only [conjE, ← hinv]
  rw [show ((glMap σ x : GL (Fin 2) (AdeleRing K')) : Matrix (Fin 2) (Fin 2) (AdeleRing K')) =
      (adeleMap σ).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) from rfl,
    show ((glMap σ x⁻¹ : GL (Fin 2) (AdeleRing K')) : Matrix (Fin 2) (Fin 2) (AdeleRing K')) =
      (adeleMap σ).mapMatrix ((x⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) _) from rfl,
    show eOneTwo (AdeleRing K') = (adeleMap σ).mapMatrix (eOneTwo (AdeleRing K)) by
      ext a b; fin_cases a <;> fin_cases b <;> simp [eOneTwo],
    ← map_mul, ← map_mul]
  rfl

/-- `σ y` lies in `U_{σ x}` exactly when `y` lies in `U_x`. -/
public theorem mem_stabSubgroup_glMap_iff (x : GL (Fin 2) (AdeleRing K)) (y : AdeleRing K) :
    adeleMap σ y ∈ stabSubgroup K' (glMap σ x) ↔ y ∈ stabSubgroup K x := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conjE_glMap, ← map_mul, adeleMap_mem_integralAdeles_iff]

end Adeles

section Local

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- `σ` restricted to the valuation rings `σ⁻¹(w) ≃+* w` of `K` and `K'`. -/
public def placeComapRingEquiv (w : Place K') : (placeComap σ w).1 ≃+* w.1 where
  toFun y := ⟨σ y, (mem_placeComap σ).1 y.2⟩
  invFun y := ⟨σ.symm y, (mem_placeComap σ).2 (by simp)⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp
  map_add' y z := by ext; simp

/-- The residue fields of `σ⁻¹(w)` and of `w` have the same cardinality. -/
public theorem resCard_placeComap (w : Place K') : (placeComap σ w).resCard = w.resCard :=
  Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (placeComapRingEquiv σ w)).toEquiv

/-- The residue fields of the completions at `σ⁻¹(w)` and at `w` have the same cardinality. -/
public theorem residueCard_placeComap (w : Place K') :
    (placeComap σ w).residueCard = w.residueCard := by
  rw [Place.residueCard_eq_resCard, Place.residueCard_eq_resCard, resCard_placeComap]

/-- `σ` restricted to the rings of integers `O_{σ⁻¹ w} ≃+* O_w` of the completions. -/
public def integersEquiv {v : Place K} {w : Place K'} (h : v.1 = w.1.comap σ.toRingHom) :
    v.integers ≃+* w.integers where
  toFun y := ⟨completionEquiv σ h y, (completionEquiv_mem_integers_iff σ h y).2 y.2⟩
  invFun y := ⟨(completionEquiv σ h).symm y, (completionEquiv_mem_integers_iff σ h _).1
    (by simp)⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp
  map_add' y z := by ext; simp

/-- `σ` maps a uniformizer of `O_v` to a uniformizer of `O_w`, where `v = σ⁻¹(w)`. -/
public theorem isUniformizer_integersEquiv {v : Place K} {w : Place K'}
    (h : v.1 = w.1.comap σ.toRingHom) {π : v.integers} (hπ : Place.IsUniformizer v π) :
    Place.IsUniformizer w (integersEquiv σ h π) := by
  unfold Place.IsUniformizer at hπ ⊢
  have hmap := Ideal.map_span (integersEquiv σ h) {π}
  rw [Set.image_singleton] at hmap
  rw [← hmap, hπ]
  ext y
  rw [Ideal.mem_map_of_equiv (integersEquiv σ h)]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    exact fun hu => hz ((isUnit_map_iff (integersEquiv σ h) z).1 hu)
  · intro hy
    refine ⟨(integersEquiv σ h).symm y, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    exact fun hu => hy (by simpa using (isUnit_map_iff (integersEquiv σ h) _).2 hu)

/-- If `x` has component `m` at `σ⁻¹(w)` and the identity at every other place, then `σ(x)` has
component `σ(m)` at `w` and the identity at every other place. -/
public theorem isLocalMatrixAt_glMap {w : Place K'}
    {m : Matrix (Fin 2) (Fin 2) (placeComap σ w).completion} {x : GL (Fin 2) (AdeleRing K)}
    (hx : IsLocalMatrixAt (placeComap σ w) m x) :
    IsLocalMatrixAt w ((completionEquiv σ (v := placeComap σ w) (w := w) rfl).toRingHom.mapMatrix m)
      (glMap σ x) := by
  refine ⟨fun i j => ?_, fun w' hw' i j => ?_⟩
  · rw [glMap_apply, adeleMap_apply, hx.1 i j]
    rfl
  · rw [glMap_apply, adeleMap_apply,
      hx.2 _ (fun h => hw' (placeComap_injective σ h)) i j]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Matrix.one_apply_ne hij]

/-- `σ` maps an adelic matrix that is `diag (π⁻¹, π⁻¹)` at `σ⁻¹(w)`, for a uniformizer `π`, and
the identity elsewhere, to such a matrix at `w`. -/
public theorem isCentralDataAt_glMap {w : Place K'} {a : GL (Fin 2) (AdeleRing K)}
    (ha : IsCentralDataAt (placeComap σ w) a) : IsCentralDataAt w (glMap σ a) := by
  obtain ⟨π, hπ, hloc⟩ := ha
  refine ⟨integersEquiv σ (v := placeComap σ w) (w := w) rfl π,
    isUniformizer_integersEquiv σ rfl hπ, ?_⟩
  convert isLocalMatrixAt_glMap σ hloc using 1
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [integersEquiv]
  · simp [Matrix.diagonal_apply_ne _ hij]

end Local

section Orders

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- The pullback `σ⁻¹(w)` of a discrete place is discrete. -/
public theorem isDiscrete_placeComap {w : Place K'} (hw : w.IsDiscrete) :
    (placeComap σ w).IsDiscrete := by
  obtain ⟨u, hu, hs⟩ := hw
  refine ⟨u.comap σ.toRingHom, ?_, fun g => ?_⟩
  · ext y
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ← Valuation.mem_valuationSubring_iff, hu, mem_placeComap]
    rfl
  · obtain ⟨y, rfl⟩ := hs g
    exact ⟨σ.symm y, by simp⟩

/-- The normalized valuation of `σ⁻¹(w)` is the pullback along `σ` of that of `w`. -/
public theorem normVal_placeComap {w : Place K'} (hw : w.IsDiscrete) :
    (placeComap σ w).normVal = w.normVal.comap σ.toRingHom := by
  refine Place.normVal_eq ?_ fun g => ?_
  · ext y
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, Place.normVal_le_one_iff hw,
      mem_placeComap]
    rfl
  · obtain ⟨y, hy⟩ := (Place.normVal_spec hw).2 g
    exact ⟨σ.symm y, by simpa using hy⟩

/-- `ord_{σ⁻¹ w}(y) = ord_w(σ y)`. -/
public theorem ord_placeComap {w : Place K'} (hw : w.IsDiscrete) (y : K) :
    (placeComap σ w).ord y = w.ord (σ y) := by
  rw [Place.ord, Place.ord, normVal_placeComap σ hw]
  rfl

/-- The order of `0` in `K_v` is the order of `0` in `K`. -/
public theorem ordC_zero (v : Place K) : v.ordC 0 = v.ord 0 := by
  rw [Place.ordC]
  have h := (Place.exists_valued_eq v (0 : v.completion)).choose_spec
  generalize (Place.exists_valued_eq v (0 : v.completion)).choose = y at h ⊢
  rw [map_zero, eq_comm, Valuation.zero_iff, map_eq_zero] at h
  rw [h]

/-- `σ` maps `ϖ^m O_{σ⁻¹ w}` onto `ϖ^m O_w`. -/
public theorem completionEquiv_mem_ball_iff {w : Place K'} (hw : w.IsDiscrete) (m : ℤ)
    (z : (placeComap σ w).completion) :
    completionEquiv σ (v := placeComap σ w) (w := w) rfl z ∈ w.ball m ↔
      z ∈ (placeComap σ w).ball m := by
  have hv : (placeComap σ w).IsDiscrete := isDiscrete_placeComap σ hw
  have hϖ : (placeComap σ w).unif ^ (-m) ≠ 0 := zpow_ne_zero _ (Place.unif_ne_zero hv)
  have hord : (placeComap σ w).ord ((placeComap σ w).unif ^ (-m)) = -m := by
    simp [Place.ord, Place.normVal_unif_zpow hv]
  have hc : (placeComap σ w).coeRingHom ((placeComap σ w).unif ^ (-m)) ≠ 0 :=
    (map_ne_zero _).2 hϖ
  have hσ : σ ((placeComap σ w).unif ^ (-m)) ≠ 0 := (map_ne_zero σ).2 hϖ
  have hc' : w.coeRingHom (σ ((placeComap σ w).unif ^ (-m))) ≠ 0 := (map_ne_zero _).2 hσ
  have h1 := Place.mul_mem_ball_iff hv hc (m := m) (y := z)
  have h2 := Place.mul_mem_ball_iff hw hc' (m := m)
    (y := completionEquiv σ (v := placeComap σ w) (w := w) rfl z)
  rw [Place.ordC_coeRingHom hv hϖ, hord, add_neg_cancel, Place.mem_ball_zero_iff] at h1
  rw [Place.ordC_coeRingHom hw hσ, ← ord_placeComap σ hw, hord, add_neg_cancel,
    Place.mem_ball_zero_iff] at h2
  have key : w.coeRingHom (σ ((placeComap σ w).unif ^ (-m))) *
      completionEquiv σ (v := placeComap σ w) (w := w) rfl z =
      completionEquiv σ (v := placeComap σ w) (w := w) rfl
        ((placeComap σ w).coeRingHom ((placeComap σ w).unif ^ (-m)) * z) := by
    rw [map_mul]
    congr 1
    exact (completionEquiv_coeRingHom σ (v := placeComap σ w) (w := w) rfl _).symm
  rw [← h2, key]
  exact (completionEquiv_mem_integers_iff σ (v := placeComap σ w) (w := w) rfl _).trans h1

/-- `σ` preserves the order of elements of the completions. -/
public theorem ordC_completionEquiv {w : Place K'} (hw : w.IsDiscrete)
    (z : (placeComap σ w).completion) :
    w.ordC (completionEquiv σ (v := placeComap σ w) (w := w) rfl z) = (placeComap σ w).ordC z := by
  have hv : (placeComap σ w).IsDiscrete := isDiscrete_placeComap σ hw
  rcases eq_or_ne z 0 with rfl | hz
  · rw [show completionEquiv σ (v := placeComap σ w) (w := w) rfl 0 = 0 from map_zero _,
      ordC_zero, ordC_zero, ord_placeComap σ hw, map_zero]
  have hz' : completionEquiv σ (v := placeComap σ w) (w := w) rfl z ≠ 0 := by simpa using hz
  have key : ∀ m, m ≤ w.ordC (completionEquiv σ (v := placeComap σ w) (w := w) rfl z) ↔
      m ≤ (placeComap σ w).ordC z := by
    intro m
    have h1 := Place.mem_ball_iff_ordC hv (m := m) (y := z)
    have h2 := Place.mem_ball_iff_ordC hw (m := m)
      (y := completionEquiv σ (v := placeComap σ w) (w := w) rfl z)
    rw [completionEquiv_mem_ball_iff σ hw] at h2
    simp only [hz, hz', false_or] at h1 h2
    rw [← h1, ← h2]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/-- The bijection of places induced by `σ`. -/
public def placeEquiv : Place K ≃ Place K' where
  toFun := placeComap σ.symm
  invFun := placeComap σ
  left_inv := placeComap_symm_placeComap σ
  right_inv := placeComap_placeComap_symm σ

end Orders

section CuspForms

variable {K K' : Type u} [Field K] [Field K'] (σ : K ≃+* K')

/-- `σ y` lies in `K' + U_{σ x}` exactly when `y` lies in `K + U_x`. -/
public theorem adeleMap_mem_sup_iff (x : GL (Fin 2) (AdeleRing K)) (y : AdeleRing K) :
    adeleMap σ y ∈ (principalAdeles K').toAddSubgroup ⊔ stabSubgroup K' (glMap σ x) ↔
      y ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x := by
  simp only [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨p, hp, u, hu, he⟩
    refine ⟨adeleMap σ.symm p, adeleMap_mem_principalAdeles σ.symm hp, adeleMap σ.symm u, ?_, ?_⟩
    · rwa [← mem_stabSubgroup_glMap_iff σ, adeleMap_adeleMap_symm]
    · rw [← map_add, he, adeleMap_symm_adeleMap]
  · rintro ⟨p, hp, u, hu, rfl⟩
    exact ⟨adeleMap σ p, adeleMap_mem_principalAdeles σ hp, adeleMap σ u,
      (mem_stabSubgroup_glMap_iff σ x u).2 hu, (map_add _ _ _).symm⟩

open scoped Classical in
/-- `σ` maps a transversal of `A_K / (K + U_x)` to a transversal of `A_{K'} / (K' + U_{σ x})`. -/
public theorem isTransversal_image_adeleMap (x : GL (Fin 2) (AdeleRing K))
    {s : Finset (AdeleRing K)}
    (hs : ∀ a, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x) :
    ∀ a, ∃! z ∈ s.image (adeleMap σ),
      a - z ∈ (principalAdeles K').toAddSubgroup ⊔ stabSubgroup K' (glMap σ x) := by
  classical
  intro a
  obtain ⟨z, ⟨hz, hza⟩, huniq⟩ := hs (adeleMap σ.symm a)
  refine ⟨adeleMap σ z, ⟨Finset.mem_image_of_mem _ hz, ?_⟩, ?_⟩
  · rwa [← adeleMap_adeleMap_symm σ a, ← map_sub, adeleMap_mem_sup_iff]
  · rintro z' ⟨hz', hz'a⟩
    obtain ⟨z'', hz'', rfl⟩ := Finset.mem_image.1 hz'
    rw [← adeleMap_adeleMap_symm σ a, ← map_sub, adeleMap_mem_sup_iff] at hz'a
    rw [huniq z'' ⟨hz'', hz'a⟩]

open scoped Classical in
/-- Summing over the image of `s` under the adele map of `σ` is summing over `s`. -/
public theorem sum_image_adeleMap {M : Type*} [AddCommMonoid M] (φ : AdeleRing K' → M)
    (s : Finset (AdeleRing K)) :
    ∑ z ∈ s.image (adeleMap σ), φ z = ∑ z ∈ s, φ (adeleMap σ z) := by
  classical
  exact Finset.sum_image fun _ _ _ _ h => adeleMap_injective σ h

/-- Transport of the star cusp condition along `σ⁻¹`. -/
public theorem starCusp_comp_glMap {Λ : Type w} [CommRing Λ] {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : StarCusp K Λ f) : StarCusp K' Λ (fun x => f (glMap σ.symm x)) := by
  classical
  intro x s hs
  have hs' := isTransversal_image_adeleMap σ.symm x hs
  have := hf (glMap σ.symm x) (s.image (adeleMap σ.symm))
    (by simpa only [RingEquiv.symm_symm] using hs')
  rw [sum_image_adeleMap] at this
  rw [← this]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [map_mul, glMap_upperRightHom]

/-- **Transport of `C(Λ)` along an isomorphism of function fields.** -/
public theorem isCuspFormCentralChar_comp_glMap (k : Type u) [Field k] [Finite k] [Algebra k K']
    [Algebra (RatFunc k) K'] [IsScalarTower k (RatFunc k) K'] [FunctionField k K']
    {Λ : Type w} [CommRing Λ] (hp : IsUnit (ringChar k : Λ)) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsCuspFormCentralChar Λ f) :
    IsCuspFormCentralChar Λ (fun x => f (glMap σ.symm x)) := by
  refine ⟨isUnramifiedCuspForm_of_starCusp k hp (fun κ x => ?_) (fun γ x => ?_)
    (starCusp_comp_glMap σ (IsUnramifiedCuspForm.starCusp hf.1)), fun w a ha x => ?_⟩
  · obtain ⟨κ', hκ'⟩ := glMap_mapO σ.symm κ
    simp only [map_mul, hκ']
    exact hf.1.left_invariant _ κ'
  · obtain ⟨γ', hγ'⟩ := glMap_mapK σ.symm γ
    simp only [map_mul, hγ']
    exact hf.1.right_invariant _ γ'
  · obtain ⟨u, rfl⟩ := placeComap_surjective σ.symm w
    have := hf.2 u _ (isCentralDataAt_glMap σ.symm ha) (glMap σ.symm x)
    simp only [centralOperator, map_mul] at this ⊢
    rw [residueCard_placeComap]
    exact this

include σ in
/-- If `C(Λ)` is nonzero for `K` then it is nonzero for any field `K'` isomorphic to `K`. -/
public theorem cuspFormsCentralChar_ne_bot_of_ringEquiv (k : Type u) [Field k] [Finite k]
    [Algebra k K'] [Algebra (RatFunc k) K'] [IsScalarTower k (RatFunc k) K'] [FunctionField k K']
    {Λ : Type w} [CommRing Λ] (hp : IsUnit (ringChar k : Λ))
    (h : cuspFormsCentralChar K Λ ≠ ⊥) : cuspFormsCentralChar K' Λ ≠ ⊥ := by
  intro hbot
  apply h
  rw [cuspFormsCentralChar, Submodule.span_eq_bot] at hbot ⊢
  intro f hf
  have h0 := hbot _ (isCuspFormCentralChar_comp_glMap σ k hp hf)
  funext x
  have := congrFun h0 (glMap σ x)
  simpa [glMap_symm_glMap] using this

end CuspForms

end Stacks.Drinfeld

end
