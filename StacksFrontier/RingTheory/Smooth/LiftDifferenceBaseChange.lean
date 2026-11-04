module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.LocalThickening.FiniteFreeRetraction
public import StacksFrontier.RingTheory.Smooth.SquareZeroLifts

/-!
# Flat base change of the differences of lifts

Let `R → A` be a surjection of commutative rings with square-zero kernel `I`, let `C` be a smooth
`R`-algebra, `E` an `R`-algebra and `ζ : C → E ⧸ I E` a map of `R`-algebras. The differences of
two lifts of `ζ` to `E` form the module `Stacks.SquareZeroLift.diff`. This module commutes with
flat base change: for a flat `R`-algebra `B'` the map

  `diff (E → E ⧸ I E) ζ ⊗_R B' → diff (E ⊗_R B' → (E ⊗_R B') ⧸ I (E ⊗_R B')) ζ_{B'}`,
  `D ⊗ b ↦ (c ↦ D c ⊗ b)`

is bijective (`Stacks.SquareZeroLift.diffBaseChange_bijective`).

## Main definitions

* `Stacks.SquareZeroLift.homTensor`: the comparison `Hom_C(P, N) ⊗_R B' → Hom_C(P, N ⊗_R B')`.
* `Stacks.SquareZeroLift.redπ`: the projection `E → E ⧸ I E`, for `I E` the ideal
  `Stacks.LocalThickening.extendedIdeal`.
* `Stacks.SquareZeroLift.diffBaseChange`: the base change map above.

## Main results

* `Stacks.SquareZeroLift.homTensor_bijective`: the comparison is bijective when `P` is a finitely
  generated projective `C`-module.
* `Stacks.SquareZeroLift.diffBaseChange_bijective`: the base change map of the differences of
  lifts is bijective for a smooth `R`-algebra `C` and a flat `R`-algebra `B'`.

## Implementation notes

The differences of lifts of `ζ` are the derivations `C → I E` for the `C`-module structure on
`I E` through any one lift, hence `Hom_C(Ω_{C/R}, I E)`. The module `Ω_{C/R}` is finitely
generated and projective because `C` is smooth, so `Hom_C(Ω_{C/R}, -)` commutes with `- ⊗_R B'`
by the retract argument of `Stacks.SquareZeroLift.homTensor_bijective`, and `I E ⊗_R B'` is
`I (E ⊗_R B')` because `B'` is flat.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open TensorProduct Stacks.LocalThickening

universe u

namespace Stacks.SquareZeroLift

/-! ### Homomorphisms out of a finitely generated projective module, and base change -/

section HomTensor

variable (R : Type u) [CommRing R] (C : Type u) [CommRing C] [Algebra R C]
  (B' : Type u) [AddCommGroup B'] [Module R B']
  (N : Type u) [AddCommGroup N] [Module C N] [Module R N] [IsScalarTower R C N]

/-- The `C`-linear map `n ↦ n ⊗ b`. -/
def tmulRight (b : B') : N →ₗ[C] N ⊗[R] B' where
  toFun n := n ⊗ₜ b
  map_add' n n' := add_tmul n n' b
  map_smul' c n := (smul_tmul' c n b).symm

/-- `tmulRight R C B' N b` sends `n` to `n ⊗ b`. -/
@[simp]
theorem tmulRight_apply (b : B') (n : N) : tmulRight R C B' N b n = n ⊗ₜ b :=
  rfl

/-- **The comparison `Hom_C(P, N) ⊗_R B' → Hom_C(P, N ⊗_R B')`**, `f ⊗ b ↦ (p ↦ f p ⊗ b)`. -/
def homTensor (P : Type u) [AddCommGroup P] [Module C P] :
    (P →ₗ[C] N) ⊗[R] B' →ₗ[R] (P →ₗ[C] N ⊗[R] B') :=
  TensorProduct.lift
    { toFun f :=
        { toFun b := (tmulRight R C B' N b).comp f
          map_add' b b' := by ext p; simp [tmul_add]
          map_smul' r b := by ext p; simp }
      map_add' f f' := by ext b p; simp [add_tmul]
      map_smul' r f := by ext b p; simp [smul_tmul'] }

/-- The comparison `homTensor` sends `f ⊗ b` to `p ↦ f p ⊗ b`. -/
@[simp]
theorem homTensor_tmul_apply {P : Type u} [AddCommGroup P] [Module C P] (f : P →ₗ[C] N)
    (b : B') (p : P) : homTensor R C B' N P (f ⊗ₜ b) p = f p ⊗ₜ b :=
  rfl

variable {N}

/-- Precomposition with a `C`-linear map, as an `R`-linear map of `Hom` modules. -/
def precomp {P P' : Type u} [AddCommGroup P] [Module C P] [AddCommGroup P'] [Module C P']
    (M : Type u) [AddCommGroup M] [Module C M] [Module R M] [IsScalarTower R C M]
    (g : P →ₗ[C] P') : (P' →ₗ[C] M) →ₗ[R] (P →ₗ[C] M) where
  toFun h := h.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison `homTensor` is natural in `P`: it commutes with precomposition by a
`C`-linear map `g : P → P'`. -/
theorem homTensor_comp_rTensor_precomp {P P' : Type u} [AddCommGroup P] [Module C P]
    [AddCommGroup P'] [Module C P'] (g : P →ₗ[C] P') :
    (homTensor R C B' N P).comp ((precomp R C N g).rTensor B') =
      (precomp R C (N ⊗[R] B') g).comp (homTensor R C B' N P') := by
  ext f b p
  rfl

/-- Precomposition by a section `s` of `p` is a retraction of precomposition by `p`. -/
private theorem precomp_comp_precomp {P P' : Type u} [AddCommGroup P] [Module C P]
    [AddCommGroup P'] [Module C P'] (M : Type u) [AddCommGroup M] [Module C M] [Module R M]
    [IsScalarTower R C M] {p : P →ₗ[C] P'} {s : P' →ₗ[C] P} (hs : p.comp s = LinearMap.id) :
    (precomp R C M s).comp (precomp R C M p) = LinearMap.id := by
  ext h x
  show h (p (s x)) = h x
  rw [← LinearMap.comp_apply p s, hs, LinearMap.id_apply]

variable (N) in
/-- The comparison is bijective for a finite free module `Fin n → C`. -/
theorem homTensor_bijective_pi (n : ℕ) :
    Function.Bijective (homTensor R C B' N (Fin n → C)) := by
  classical
  let e₁ := LinearEquiv.piRing C N (Fin n) R
  let e₂ := LinearEquiv.piRing C (N ⊗[R] B') (Fin n) R
  let e₃ : (Fin n → N) ⊗[R] B' ≃ₗ[R] Fin n → N ⊗[R] B' := TensorProduct.piLeft R B' fun _ => N
  have key : homTensor R C B' N (Fin n → C) =
      (e₂.symm.toLinearMap.comp e₃.toLinearMap).comp (e₁.toLinearMap.rTensor B') := by
    refine TensorProduct.ext' fun f b => ?_
    apply e₂.injective
    funext i
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.piRing_apply, homTensor_tmul_apply]
    show _ = e₃ (e₁ f ⊗ₜ b) i
    simp only [e₃, TensorProduct.piLeft, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
      TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply]
    rw [LinearEquiv.piRing_apply]
  rw [key]
  exact (e₂.symm.bijective.comp e₃.bijective).comp
    (LinearEquiv.rTensor B' e₁).bijective

/-- **`Hom_C(P, N) ⊗_R B' ≅ Hom_C(P, N ⊗_R B')` for `P` finitely generated and projective.** -/
theorem homTensor_bijective (P : Type u) [AddCommGroup P] [Module C P] [Module.Finite C P]
    [Module.Projective C P] : Function.Bijective (homTensor R C B' N P) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' C P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hpi := homTensor_bijective_pi R C B' N n
  have hret : ((precomp R C N s).rTensor B').comp ((precomp R C N p).rTensor B') =
      LinearMap.id := by
    rw [← LinearMap.rTensor_comp, precomp_comp_precomp R C N hs, LinearMap.rTensor_id]
  refine ⟨fun x y hxy => ?_, fun F => ?_⟩
  · have h1 : homTensor R C B' N (Fin n → C) ((precomp R C N p).rTensor B' x) =
        homTensor R C B' N (Fin n → C) ((precomp R C N p).rTensor B' y) := by
      rw [← LinearMap.comp_apply, homTensor_comp_rTensor_precomp, LinearMap.comp_apply, hxy,
        ← LinearMap.comp_apply, ← homTensor_comp_rTensor_precomp, LinearMap.comp_apply]
    have h2 := congrArg ((precomp R C N s).rTensor B') (hpi.1 h1)
    rwa [← LinearMap.comp_apply, hret, ← LinearMap.comp_apply, hret, LinearMap.id_apply,
      LinearMap.id_apply] at h2
  · obtain ⟨y, hy⟩ := hpi.2 (precomp R C (N ⊗[R] B') p F)
    refine ⟨(precomp R C N s).rTensor B' y, ?_⟩
    rw [← LinearMap.comp_apply, homTensor_comp_rTensor_precomp, LinearMap.comp_apply, hy,
      ← LinearMap.comp_apply, precomp_comp_precomp R C _ hs, LinearMap.id_apply]

end HomTensor

/-! ### The thickening `E → A ⊗_R E` -/

section Reduction

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

variable (R A) in
/-- The reduction `E → A ⊗_R E` of an `R`-algebra `E` along `R → A`. -/
abbrev redπ (E : Type u) [CommRing E] [Algebra R E] : E →ₐ[R] A ⊗[R] E :=
  Algebra.TensorProduct.includeRight

/-- The reduction `E → A ⊗_R E` is surjective when `R → A` is surjective. -/
theorem redπ_surjective (hA : Function.Surjective (algebraMap R A)) (E : Type u) [CommRing E]
    [Algebra R E] : Function.Surjective (redπ R A E) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a e =>
    obtain ⟨r, rfl⟩ := hA a
    refine ⟨r • e, ?_⟩
    show (1 : A) ⊗ₜ[R] (r • e) = _
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', map_add _ _ _⟩

/-- **The kernel of `E → A ⊗_R E` is `I E`**, for `R → A` surjective with kernel `I`. -/
theorem redπ_eq_zero_iff (hA : Function.Surjective (algebraMap R A)) {E : Type u} [CommRing E]
    [Algebra R E] (e : E) : redπ R A E e = 0 ↔ e ∈ extendedIdeal R A E := by
  constructor
  · intro h
    let φ : A ⊗[R] E →ₐ[R] E ⧸ extendedIdeal R A E :=
      Algebra.TensorProduct.lift (quotientStructureAlgHom hA) (Ideal.Quotient.mkₐ R _)
        (fun _ _ => mul_comm _ _)
    have h' := congrArg φ h
    rw [map_zero] at h'
    change quotientStructureAlgHom hA 1 * Ideal.Quotient.mk _ e = 0 at h'
    rwa [map_one, one_mul, Ideal.Quotient.eq_zero_iff_mem] at h'
  · intro he
    refine Submodule.span_induction ?_ ?_ ?_ ?_ he
    · rintro _ ⟨r, hr, rfl⟩
      show (1 : A) ⊗ₜ[R] (algebraMap R E r) = 0
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        RingHom.mem_ker.1 hr, TensorProduct.zero_tmul]
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The reduction `E → A ⊗_R E` has square-zero kernel when `R → A` is surjective with
square-zero kernel. -/
theorem isSqZero_redπ (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) (E : Type u) [CommRing E] [Algebra R E] :
    IsSqZero (redπ R A E) := fun a b ha hb =>
  mul_eq_zero_of_mem_extendedIdeal hI ((redπ_eq_zero_iff hA a).1 ha)
    ((redπ_eq_zero_iff hA b).1 hb)

variable (A) in
/-- The map `A ⊗_R E₁ → A ⊗_R E₂` induced by a map of `R`-algebras. -/
abbrev redMap {E₁ E₂ : Type u} [CommRing E₁] [CommRing E₂] [Algebra R E₁] [Algebra R E₂]
    (τ : E₁ →ₐ[R] E₂) : A ⊗[R] E₁ →ₐ[R] A ⊗[R] E₂ :=
  Algebra.TensorProduct.map (AlgHom.id R A) τ

/-- The reductions commute with a map of `R`-algebras `τ : E₁ → E₂`. -/
theorem redMap_comp_redπ {E₁ E₂ : Type u} [CommRing E₁] [CommRing E₂] [Algebra R E₁]
    [Algebra R E₂] (τ : E₁ →ₐ[R] E₂) :
    (redMap A τ).comp (redπ R A E₁) = (redπ R A E₂).comp τ :=
  AlgHom.ext fun _ => rfl

/-- The induced map `redMap A` is compatible with composition. -/
theorem redMap_comp {E₁ E₂ E₃ : Type u} [CommRing E₁] [CommRing E₂] [CommRing E₃]
    [Algebra R E₁] [Algebra R E₂] [Algebra R E₃] (τ : E₁ →ₐ[R] E₂) (τ' : E₂ →ₐ[R] E₃) :
    (redMap A τ').comp (redMap A τ) = redMap A (τ'.comp τ) := by
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]

end Reduction

/-! ### Base change of the differences -/

section BaseChange

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {C : Type u} [CommRing C] [Algebra R C]
  {E : Type u} [CommRing E] [Algebra R E]
  (B' : Type u) [CommRing B'] [Algebra R B']

variable (R E) in
/-- The inclusion `E → E ⊗_R B'`. -/
abbrev incl : E →ₐ[R] E ⊗[R] B' := Algebra.TensorProduct.includeLeft

variable {B'} (ζ : C →ₐ[R] A ⊗[R] E)

/-- The linear map `c ↦ D c ⊗ b`. -/
def tmulDiff (D : C →ₗ[R] E) (b : B') : C →ₗ[R] E ⊗[R] B' :=
  (TensorProduct.mk R E B').flip b ∘ₗ D

/-- `tmulDiff D b` sends `c` to `D c ⊗ b`. -/
@[simp]
theorem tmulDiff_apply (D : C →ₗ[R] E) (b : B') (c : C) : tmulDiff D b c = D c ⊗ₜ b :=
  rfl

/-- A smooth `R`-algebra `C` lifts `ζ` along `E → A ⊗_R E` to an `R`-algebra map. -/
private theorem exists_lift [Algebra.FormallySmooth R C] (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) :
    ∃ q : C →ₐ[R] E, (redπ R A E).comp q = ζ :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective ζ (redπ R A E) (redπ_surjective hA E)
    (isNilpotent_ker_of_isSqZero (isSqZero_redπ hA hI E))⟩

/-- A lift `q` of `ζ` to `E` gives the lift `incl ∘ q` of the base change of `ζ`. -/
private theorem redπ_comp_incl_comp {q : C →ₐ[R] E} (hq : (redπ R A E).comp q = ζ) :
    (redπ R A (E ⊗[R] B')).comp ((incl R E B').comp q) = (redMap A (incl R E B')).comp ζ := by
  rw [← AlgHom.comp_assoc, ← redMap_comp_redπ, AlgHom.comp_assoc, hq]

/-- If `e` lies in `I E`, then `e ⊗ b` lies in `I (E ⊗_R B')`. -/
theorem tmul_mem_extendedIdeal {e : E} (he : e ∈ extendedIdeal R A E) (b : B') :
    e ⊗ₜ[R] b ∈ extendedIdeal R A (E ⊗[R] B') := by
  have h : e ⊗ₜ[R] b = incl R E B' e * (1 ⊗ₜ b) := by simp
  rw [h]
  refine Ideal.mul_mem_right _ _ ?_
  have hle : extendedIdeal R A E ≤ (extendedIdeal R A (E ⊗[R] B')).comap (incl R E B') := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show incl R E B' (algebraMap R E a) ∈ extendedIdeal R A (E ⊗[R] B')
    rw [AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  exact hle he

/-- For a difference `D` of lifts of `ζ` to `E` and `b : B'`, the map `c ↦ D c ⊗ b` is a
difference of lifts of the base change of `ζ` to `E ⊗_R B'`. -/
theorem tmulDiff_mem (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) [Algebra.FormallySmooth R C] {D : C →ₗ[R] E}
    (hD : D ∈ diff (redπ R A E) ζ) (b : B') :
    tmulDiff D b ∈ diff (redπ R A (E ⊗[R] B')) ((redMap A (incl R E B')).comp ζ) := by
  obtain ⟨q, hq⟩ := exists_lift ζ hA hI
  have h0 : ∀ c, redπ R A (E ⊗[R] B') (tmulDiff D b c) = 0 := fun c =>
    (redπ_eq_zero_iff hA _).2 (tmul_mem_extendedIdeal ((redπ_eq_zero_iff hA _).1 (hD.1 c)) b)
  refine mem_diff_of_leibniz (isSqZero_redπ hA hI _) h0 (q := (incl R E B').comp q) ?_ ?_
  · exact redπ_comp_incl_comp ζ hq
  · intro x y
    simp only [tmulDiff_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      leibniz_of_mem_diff hD hq x y, add_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **The base change map of the differences**, `D ⊗ b ↦ (c ↦ D c ⊗ b)`. -/
def diffBaseChange (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) [Algebra.FormallySmooth R C] :
    diff (redπ R A E) ζ ⊗[R] B' →ₗ[R]
      diff (redπ R A (E ⊗[R] B')) ((redMap A (incl R E B')).comp ζ) :=
  TensorProduct.lift
    { toFun D :=
        { toFun b := ⟨tmulDiff D.1 b, tmulDiff_mem ζ hA hI D.2 b⟩
          map_add' b b' := by ext c; simp [tmul_add]
          map_smul' r b := by ext c; simp }
      map_add' D D' := by ext b c; simp [add_tmul]
      map_smul' r D := by ext b c; simp [smul_tmul'] }

/-- The base change map `diffBaseChange` sends `D ⊗ b` to `c ↦ D c ⊗ b`. -/
@[simp]
theorem diffBaseChange_tmul_apply (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) [Algebra.FormallySmooth R C]
    (D : diff (redπ R A E) ζ) (b : B') (c : C) :
    (diffBaseChange ζ hA hI (D ⊗ₜ b)).1 c = D.1 c ⊗ₜ b :=
  rfl

section Bijective

variable [Algebra.Smooth R C] [Module.Flat R B']

variable (A) in
/-- The ideal `I E` with the structure of a `C`-module through a lift `q` of `ζ`. -/
@[instance_reducible]
def liftModule (q : C →ₐ[R] E) : Module C (extendedIdeal R A E) :=
  Module.compHom (extendedIdeal R A E) (q : C →+* E)

omit [Algebra.Smooth R C] in
/-- In the module structure `liftModule A q`, `c • n = q c * n` in `E`. -/
theorem liftModule_smul_coe (q : C →ₐ[R] E) (c : C) (n : extendedIdeal R A E) :
    letI := liftModule A q
    ((c • n : extendedIdeal R A E) : E) = q c * n :=
  rfl

variable (A) in
omit [Algebra.Smooth R C] in
/-- The `C`-module structure `liftModule A q` on `I E` is compatible with its `R`-module
structure. -/
theorem liftModule_isScalarTower (q : C →ₐ[R] E) :
    letI := liftModule A q
    IsScalarTower R C (extendedIdeal R A E) := by
  let := liftModule A q
  refine ⟨fun r c n => Subtype.ext ?_⟩
  show q (r • c) * n = r • (q c * (n : E))
  rw [map_smul, smul_mul_assoc]

/-- **The differences of lifts are the derivations into `I E`.** -/
def diffToDerivation (hA : Function.Surjective (algebraMap R A)) {q : C →ₐ[R] E}
    (hq : (redπ R A E).comp q = ζ) :
    letI := liftModule A q
    haveI := liftModule_isScalarTower A q
    diff (redπ R A E) ζ →ₗ[R] Derivation R C (extendedIdeal R A E) :=
  letI := liftModule A q
  haveI := liftModule_isScalarTower A q
  { toFun D :=
      { toLinearMap := LinearMap.codRestrict ((extendedIdeal R A E).restrictScalars R) D.1
          (fun c => (redπ_eq_zero_iff hA _).1 (D.2.1 c))
        map_one_eq_zero' := Subtype.ext (map_one_of_mem_diff D.2 hq)
        leibniz' := fun a b => Subtype.ext (by
          change D.1 (a * b) = q a * D.1 b + q b * D.1 a
          exact leibniz_of_mem_diff D.2 hq a b) }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

omit [Algebra.Smooth R C] in
/-- The derivation `diffToDerivation ζ hA hq D` takes the values of `D`. -/
theorem diffToDerivation_apply (hA : Function.Surjective (algebraMap R A)) {q : C →ₐ[R] E}
    (hq : (redπ R A E).comp q = ζ) (D : diff (redπ R A E) ζ) (c : C) :
    ((diffToDerivation ζ hA hq D c : extendedIdeal R A E) : E) = D.1 c :=
  rfl

omit [Algebra.Smooth R C] in
/-- The map from the differences of lifts of `ζ` to the derivations `C → I E` is bijective. -/
theorem diffToDerivation_bijective (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) {q : C →ₐ[R] E} (hq : (redπ R A E).comp q = ζ) :
    Function.Bijective (diffToDerivation ζ hA hq) := by
  let := liftModule A q
  have := liftModule_isScalarTower A q
  refine ⟨fun D D' h => Subtype.ext (LinearMap.ext fun c => ?_), fun d => ?_⟩
  · have := congrArg
      (fun d : Derivation R C (extendedIdeal R A E) => ((d c : extendedIdeal R A E) : E)) h
    exact this
  · let D : C →ₗ[R] E := ((extendedIdeal R A E).restrictScalars R).subtype ∘ₗ d.toLinearMap
    have hD : D ∈ diff (redπ R A E) ζ := by
      refine mem_diff_of_leibniz (isSqZero_redπ hA hI E)
        (fun c => (redπ_eq_zero_iff hA _).2 (d c).2) hq fun a b => ?_
      have h := congrArg Subtype.val (d.leibniz a b)
      exact h
    exact ⟨⟨D, hD⟩, Derivation.ext fun c => rfl⟩

variable (R A E B') in
/-- The inclusion `I E ⊗_R B' → E ⊗_R B'`. -/
abbrev idealTensor : extendedIdeal R A E ⊗[R] B' →ₗ[R] E ⊗[R] B' :=
  LinearMap.rTensor B' ((extendedIdeal R A E).restrictScalars R).subtype

variable (R A E B') in
/-- The map `I E ⊗_R B' → E ⊗_R B'` is injective for `B'` flat over `R`. -/
theorem idealTensor_injective : Function.Injective (idealTensor R A E B') :=
  Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

variable (R A E B') in
omit [Module.Flat R B'] in
/-- The image of `I E ⊗_R B' → E ⊗_R B'` is the ideal `I (E ⊗_R B')`. -/
theorem range_idealTensor :
    LinearMap.range (idealTensor R A E B') =
      (extendedIdeal R A (E ⊗[R] B')).restrictScalars R := by
  show LinearMap.range
    (LinearMap.rTensor B' ((extendedIdeal R A E).restrictScalars R).subtype) = _
  rw [← Ideal.map_includeLeft_eq]
  congr 1
  show Ideal.map ((Algebra.TensorProduct.includeLeft : E →ₐ[R] E ⊗[R] B') : E →+* E ⊗[R] B')
    (Ideal.map (algebraMap R E) _) = _
  rw [Ideal.map_map]
  rfl

omit [Algebra.Smooth R C] [Module.Flat R B'] in
/-- The map `I E ⊗_R B' → E ⊗_R B'` sends `c • x` to `(q c ⊗ 1) * x`, for the `C`-module
structure on `I E` through `q`. -/
theorem idealTensor_smul (q : C →ₐ[R] E) (c : C) (x : extendedIdeal R A E ⊗[R] B') :
    letI := liftModule A q
    haveI := liftModule_isScalarTower A q
    idealTensor R A E B' (c • x) = (incl R E B' (q c)) * idealTensor R A E B' x := by
  let := liftModule A q
  have := liftModule_isScalarTower A q
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n b =>
    rw [smul_tmul']
    show ((c • n : extendedIdeal R A E) : E) ⊗ₜ[R] b = (q c ⊗ₜ[R] (1 : B')) * ((n : E) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

/-- **Flat base change of the differences of lifts.** For a smooth `R`-algebra `C`, an
`R`-algebra `E`, a map `ζ : C → E ⧸ I E` and a flat `R`-algebra `B'`, the map
`D ⊗ b ↦ (c ↦ D c ⊗ b)` from the differences of lifts of `ζ` to `E`, tensored with `B'`, to the
differences of lifts of `ζ` to `E ⊗_R B'` is bijective. -/
theorem diffBaseChange_bijective (hA : Function.Surjective (algebraMap R A))
    (hI : RingHom.ker (algebraMap R A) ^ 2 = ⊥) :
    Function.Bijective (diffBaseChange ζ hA hI (B' := B')) := by
  obtain ⟨q, hq⟩ := exists_lift ζ hA hI
  let := liftModule A q
  have := liftModule_isScalarTower A q
  let N := extendedIdeal R A E
  let χ : diff (redπ R A E) ζ →ₗ[R] (Ω[C⁄R] →ₗ[C] N) :=
    ((KaehlerDifferential.linearMapEquivDerivation R C).symm.restrictScalars R).toLinearMap ∘ₗ
      diffToDerivation ζ hA hq
  have hχ : Function.Bijective χ :=
    ((KaehlerDifferential.linearMapEquivDerivation R C).symm.restrictScalars R).bijective.comp
      (diffToDerivation_bijective ζ hA hI hq)
  let Φ := homTensor R C B' N (Ω[C⁄R])
  have hΦ : Function.Bijective Φ := homTensor_bijective R C B' (N := N) (Ω[C⁄R])
  let dR : C →ₗ[R] Ω[C⁄R] := (KaehlerDifferential.D R C).toLinearMap
  let Ψ : (Ω[C⁄R] →ₗ[C] N ⊗[R] B') →ₗ[R] (C →ₗ[R] E ⊗[R] B') :=
    { toFun F := idealTensor R A E B' ∘ₗ (F.restrictScalars R) ∘ₗ dR
      map_add' F F' := by ext c; simp
      map_smul' r F := by ext c; simp }
  have hΨ : Function.Injective Ψ := by
    intro F F' h
    refine Derivation.liftKaehlerDifferential_unique F F' (Derivation.ext fun c => ?_)
    exact idealTensor_injective R A E B' (LinearMap.congr_fun h c)
  have hcomp :
      (diff (redπ R A (E ⊗[R] B')) ((redMap A (incl R E B')).comp ζ)).subtype.restrictScalars R ∘ₗ
        diffBaseChange ζ hA hI = Ψ ∘ₗ Φ ∘ₗ χ.rTensor B' := by
    refine TensorProduct.ext' fun D b => LinearMap.ext fun c => ?_
    show D.1 c ⊗ₜ b = idealTensor R A E B' (Φ (χ D ⊗ₜ b) (KaehlerDifferential.D R C c))
    rw [homTensor_tmul_apply]
    show D.1 c ⊗ₜ b = idealTensor R A E B'
      (((diffToDerivation ζ hA hq D).liftKaehlerDifferential (KaehlerDifferential.D R C c)) ⊗ₜ b)
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
  have hinj : Function.Injective (Ψ ∘ₗ Φ ∘ₗ χ.rTensor B') :=
    hΨ.comp (hΦ.1.comp (LinearEquiv.rTensor B' (LinearEquiv.ofBijective χ hχ)).injective)
  refine ⟨fun x y h => hinj ?_, fun D => ?_⟩
  · rw [← hcomp, LinearMap.comp_apply, LinearMap.comp_apply, h]
  · have hmem : ∀ c, D.1 c ∈ LinearMap.range (idealTensor R A E B') := fun c => by
      rw [range_idealTensor R A E B']
      exact (redπ_eq_zero_iff hA _).1 (D.2.1 c)
    choose D' hD' using hmem
    let D'' : C →ₗ[R] N ⊗[R] B' :=
      { toFun := D'
        map_add' a b := idealTensor_injective R A E B' (by rw [map_add, hD', hD', hD', map_add])
        map_smul' r a :=
          idealTensor_injective R A E B' (by rw [map_smul, hD', hD', map_smul]; rfl) }
    have hqB := redπ_comp_incl_comp (B' := B') ζ hq
    let d : Derivation R C (N ⊗[R] B') :=
      { toLinearMap := D''
        map_one_eq_zero' := idealTensor_injective R A E B' (by
          show idealTensor R A E B' (D' 1) = idealTensor R A E B' 0
          rw [hD', map_zero]
          exact map_one_of_mem_diff D.2 hqB)
        leibniz' := fun a b => idealTensor_injective R A E B' (by
          show idealTensor R A E B' (D' (a * b)) = idealTensor R A E B' (a • D' b + b • D' a)
          rw [hD', map_add, idealTensor_smul (A := A) (B' := B') q,
            idealTensor_smul (A := A) (B' := B') q, hD', hD']
          exact leibniz_of_mem_diff D.2 hqB a b) }
    obtain ⟨y, hy⟩ := (hΦ.comp (LinearEquiv.rTensor B'
      (LinearEquiv.ofBijective χ hχ)).bijective).2 d.liftKaehlerDifferential
    refine ⟨y, Subtype.ext ?_⟩
    have h := congrArg (fun F => Ψ F) hy
    change (Ψ ∘ₗ Φ ∘ₗ χ.rTensor B') y = Ψ d.liftKaehlerDifferential at h
    rw [← hcomp] at h
    refine h.trans (LinearMap.ext fun c => ?_)
    show idealTensor R A E B' (d.liftKaehlerDifferential (KaehlerDifferential.D R C c)) = D.1 c
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact hD' c

end Bijective

end BaseChange


end Stacks.SquareZeroLift

end
