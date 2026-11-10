module

public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentIdealUniversalInjectivity

/-!
# Universal injectivity modulo a nilpotent ideal, over the quotient ring

Let `R` be a commutative ring, `I ⊆ R` an ideal and `f : M →ₗ[R] M'` a map of `R`-modules with
`M'` flat. The last paragraph of the proof of Stacks 05U9 reduces universal injectivity of `f`
to universal injectivity of the reduction `f ⧸ I : M/IM → M'/IM'` when `I` is nilpotent.

`Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent` already carries that
reduction, but it states the hypothesis *pointwise over `R`* — `f ⊗ id_P` is injective for every
`R`-module `P` killed by `I` — and its implementation notes say why: the pointwise form "avoids
transporting the tensor products across" the identification `M ⊗[R] P = (M/IM) ⊗[R ⧸ I] P`.
This file performs that transport, so that the hypothesis can be stated the way it is actually
produced: as universal injectivity of a map of `R ⧸ I`-modules, over the ring `R ⧸ I`.

That is the shape Stacks 0AT9 outputs:
`AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective` concludes
`UniversallyInjective u` for a map of modules over the base ring of a finitely presented
localized-module situation, and in the proof of Stacks 05U9 that ring is the quotient `A ⧸ I₀` by a
finitely generated nilpotent ideal. The results below are the interface between the two.

## Main definitions

* `Stacks.NilpotentReduction.mapQSMulTop` is the reduction `M/IM → M'/IM'` of an `R`-linear map,
  as a map of `R ⧸ I`-modules. Its underlying function is `Submodule.mapQ` of `f`.
* `Stacks.NilpotentReduction.quotientTensorEquiv` identifies `X ⊗[R ⧸ I] P` with `X ⊗[R] P` for
  `R ⧸ I`-modules `X` and `P`.

## Main results

* `Stacks.NilpotentReduction.rTensor_mkQ_smul_top_bijective`: if the ideal `I` kills `P`, then
  `M ⊗[R] P → (M/IM) ⊗[R] P` is bijective. This is the transport itself.
* `Stacks.NilpotentReduction.injective_rTensor_iff_injective_rTensor_mapQSMulTop`: for an
  `R ⧸ I`-module `P`, the map `f ⊗ id_P` over `R` is injective if and only if the reduction
  tensored with `P` over `R ⧸ I` is injective. No hypothesis on `I`, `M` or `M'`.
* `Stacks.NilpotentReduction.universallyInjectivePoly_iff_mapQSMulTop_of_isNilpotent`: for
  nilpotent `I` and flat `M'`, `f` is universally injective if and only if its reduction is
  universally injective over `R ⧸ I`.
* `AlgebraicGeometry.universallyInjectivePoly_iff_reduction_of_isNilpotent`: the same equivalence
  in Situation 0AT0, which is the universal-injectivity clause of Stacks 05U9 reduced to the
  quotient by a nilpotent ideal.

## Implementation notes

The last two results are stated as equivalences: the `→` direction needs neither nilpotence nor
flatness. They convert the pointwise hypothesis over `R` of
`Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent` into universal injectivity
over the quotient ring, the form in which Stacks 0AT9 states its conclusion.

The two tensor identifications are `Submodule.mkQ`'s `rTensor` (bijective exactly because `I`
kills the test module: the kernel is the image of `(I • ⊤) ⊗ P`, and `(a • m) ⊗ p = m ⊗ (a • p)`
vanishes there) and `TensorProduct.equivOfCompatibleSMul`, whose two `CompatibleSMul` hypotheses
are one instance-found (`TensorProduct.CompatibleSMul.isScalarTower`) and one proved here from the
surjectivity of `R → R ⧸ I`.

`Submodule.mapQ` of `f` is made `R ⧸ I`-linear, from `R`-linear, by
`LinearMap.extendScalarsOfSurjective`; the `R ⧸ I`-module structure on `M ⧸ I • ⊤` and its scalar
tower over `R` are Mathlib's, from `Module.IsTorsionBySet`.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

open TensorProduct

namespace Stacks.NilpotentReduction

variable {R : Type u₁} [CommRing R] (I : Ideal R)

/-! ### The ideal kills a module whose scalars factor through the quotient -/

/-- The class of `a` in `R ⧸ I` acts on an `IsScalarTower` module as `a` does. -/
private theorem mk_smul_eq_smul {P : Type*} [AddCommGroup P] [Module R P] [Module (R ⧸ I) P]
    [IsScalarTower R (R ⧸ I) P] (a : R) (x : P) : (Ideal.Quotient.mk I a) • x = a • x := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]

/-- An element of `I` acts by zero on a module whose `R`-action factors through `R ⧸ I`. -/
theorem smul_eq_zero_of_mem (P : Type*) [AddCommGroup P] [Module R P] [Module (R ⧸ I) P]
    [IsScalarTower R (R ⧸ I) P] {a : R} (ha : a ∈ I) (x : P) : a • x = 0 := by
  rw [← mk_smul_eq_smul I, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]

/-! ### Tensoring with a module killed by `I` kills `I • ⊤` -/

section Bijective

variable (M : Type*) [AddCommGroup M] [Module R M] (P : Type*) [AddCommGroup P] [Module R P]
  (hP : ∀ a ∈ I, ∀ x : P, a • x = 0)

include hP in
/-- If `I` kills `P`, then `(I • ⊤) ⊗[R] P → M ⊗[R] P` is zero, because
`(a • m) ⊗ p = m ⊗ (a • p) = 0` for `a ∈ I`. -/
theorem rTensor_subtype_smul_top_eq_zero :
    (I • ⊤ : Submodule R M).subtype.rTensor P = 0 := by
  refine TensorProduct.ext' fun z p => ?_
  simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearMap.zero_apply]
  refine Submodule.smul_induction_on (p := fun w : M => w ⊗ₜ[R] p = 0) z.2 ?_ ?_
  · intro a ha m _
    rw [TensorProduct.smul_tmul, hP a ha p, TensorProduct.tmul_zero]
  · intro u v hu hv
    rw [TensorProduct.add_tmul, hu, hv, add_zero]

include hP in
/-- **The transport.** If the ideal `I` kills the module `P`, then the canonical map
`M ⊗[R] P → (M ⧸ I • ⊤) ⊗[R] P` is bijective. -/
theorem rTensor_mkQ_smul_top_bijective :
    Function.Bijective ((I • ⊤ : Submodule R M).mkQ.rTensor P) := by
  refine ⟨LinearMap.ker_eq_bot.mp ?_,
    LinearMap.rTensor_surjective P (Submodule.mkQ_surjective _)⟩
  rw [_root_.rTensor_mkQ P (I • ⊤ : Submodule R M), LinearMap.range_eq_bot]
  exact rTensor_subtype_smul_top_eq_zero I M P hP

end Bijective

/-! ### Changing the base ring from `R` to `R ⧸ I` -/

section Compat

variable (X : Type*) [AddCommGroup X] [Module R X] [Module (R ⧸ I) X]
  [IsScalarTower R (R ⧸ I) X] (P : Type*) [AddCommGroup P] [Module R P] [Module (R ⧸ I) P]
  [IsScalarTower R (R ⧸ I) P]

/-- An element of `R ⧸ I` can be moved across a tensor product over `R` of two
`R ⧸ I`-modules, because it lifts to `R`. -/
theorem compatibleSMul_of_isScalarTower : TensorProduct.CompatibleSMul R (R ⧸ I) X P :=
  ⟨fun c m n => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) c
    rw [mk_smul_eq_smul I, mk_smul_eq_smul I, TensorProduct.smul_tmul]⟩

/-- For `R ⧸ I`-modules the tensor product over `R ⧸ I` agrees with the tensor product
over `R`. -/
noncomputable def quotientTensorEquiv : X ⊗[R ⧸ I] P ≃ₗ[R] X ⊗[R] P :=
  letI := compatibleSMul_of_isScalarTower I X P
  TensorProduct.equivOfCompatibleSMul R (R ⧸ I) R X P

/-- `quotientTensorEquiv` sends `x ⊗ₜ[R ⧸ I] p` to `x ⊗ₜ[R] p`. -/
@[simp] theorem quotientTensorEquiv_tmul (x : X) (p : P) :
    quotientTensorEquiv I X P (x ⊗ₜ[R ⧸ I] p) = x ⊗ₜ[R] p := rfl

end Compat

/-! ### The reduction of a linear map, over the quotient ring -/

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The reduction `M/IM → M'/IM'` of an `R`-linear map `f : M →ₗ[R] M'`, as a map of
`R ⧸ I`-modules. Its underlying function is `Submodule.mapQ` of `f`. -/
noncomputable def mapQSMulTop (f : M →ₗ[R] M') :
    (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R ⧸ I] (M' ⧸ (I • ⊤ : Submodule R M')) :=
  (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- The reduction `mapQSMulTop I f` sends the class of `m` to the class of `f m`. -/
@[simp] theorem mapQSMulTop_mk (f : M →ₗ[R] M') (m : M) :
    mapQSMulTop I f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl

/-- Injectivity transfers across a commuting square whose horizontal maps are bijective. -/
private theorem injective_iff_of_comm {A A' B B' : Type*} {e : A → A'} {e' : B → B'}
    {g : A → B} {h : A' → B'} (he : Function.Bijective e) (he' : Function.Injective e')
    (hcomm : ∀ x, e' (g x) = h (e x)) : Function.Injective g ↔ Function.Injective h := by
  constructor
  · intro hg x y hxy
    obtain ⟨a, rfl⟩ := he.2 x
    obtain ⟨b, rfl⟩ := he.2 y
    rw [← hcomm, ← hcomm] at hxy
    exact congrArg e (hg (he' hxy))
  · intro hh x y hxy
    refine he.1 (hh ?_)
    rw [← hcomm, ← hcomm, hxy]

/-- The square relating `f ⊗ id_P` to the reduction of `f` tensored with `P`, both over `R`. -/
theorem rTensor_mkQ_comm (P : Type*) [AddCommGroup P] [Module R P] (f : M →ₗ[R] M')
    (x : M ⊗[R] P) :
    (I • ⊤ : Submodule R M').mkQ.rTensor P (f.rTensor P x) =
      (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)).rTensor P
        ((I • ⊤ : Submodule R M).mkQ.rTensor P x) := by
  induction x with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m p => simp [Submodule.mapQ_apply]

section Transfer

variable (P : Type u₅) [AddCommGroup P] [Module R P] [Module (R ⧸ I) P]
  [IsScalarTower R (R ⧸ I) P]

/-- The square relating the reduction of `f` tensored with `P` over `R ⧸ I` to the same
tensored over `R`. -/
theorem rTensor_mapQSMulTop_comm (f : M →ₗ[R] M')
    (x : (M ⧸ (I • ⊤ : Submodule R M)) ⊗[R ⧸ I] P) :
    quotientTensorEquiv I _ P ((mapQSMulTop I f).rTensor P x) =
      (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)).rTensor P
        (quotientTensorEquiv I _ P x) := by
  induction x with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m p =>
      rw [LinearMap.rTensor_tmul, quotientTensorEquiv_tmul, quotientTensorEquiv_tmul,
        LinearMap.rTensor_tmul]
      rfl

/-- **The shape conversion, one test module at a time.** For a test module `P` whose `R`-action
factors through `R ⧸ I`, the map `f ⊗ id_P` over `R` is injective if and only if the reduction
`M/IM → M'/IM'` tensored with `P` over `R ⧸ I` is injective.

No hypothesis on `I`, `M` or `M'`: this is the bare identification
`M ⊗[R] P = (M/IM) ⊗[R ⧸ I] P`. -/
theorem injective_rTensor_iff_injective_rTensor_mapQSMulTop (f : M →ₗ[R] M') :
    Function.Injective (f.rTensor P) ↔ Function.Injective ((mapQSMulTop I f).rTensor P) := by
  have hP := fun a (ha : a ∈ I) (x : P) => smul_eq_zero_of_mem I P ha x
  have h₁ : Function.Injective (f.rTensor P) ↔
      Function.Injective ((Submodule.mapQ _ _ f
        (Submodule.smul_top_le_comap_smul_top I f)).rTensor P) :=
    injective_iff_of_comm (rTensor_mkQ_smul_top_bijective I M P hP)
      (rTensor_mkQ_smul_top_bijective I M' P hP).1 (rTensor_mkQ_comm I P f)
  have h₂ : Function.Injective ((mapQSMulTop I f).rTensor P) ↔
      Function.Injective ((Submodule.mapQ _ _ f
        (Submodule.smul_top_le_comap_smul_top I f)).rTensor P) :=
    injective_iff_of_comm (quotientTensorEquiv I _ P).bijective
      (quotientTensorEquiv I _ P).injective (rTensor_mapQSMulTop_comm I P f)
  rw [h₁, ← h₂]

end Transfer

/-- **Universal injectivity modulo a nilpotent ideal, over the quotient ring.** Let
`f : M →ₗ[R] M'` with `M'` flat and let `I ⊆ R` be a nilpotent ideal. Then `f` is universally
injective if and only if its reduction `M/IM → M'/IM'` is universally injective over `R ⧸ I`.
-/
theorem universallyInjectivePoly_iff_mapQSMulTop_of_isNilpotent [Module.Flat R M']
    (f : M →ₗ[R] M') (hI : IsNilpotent I) :
    UniversallyInjectivePoly.{_, u₅} f ↔
      UniversallyInjectivePoly.{_, u₅} (mapQSMulTop I f) := by
  constructor
  · intro hf Q _ _
    let _ : Module R Q := Module.compHom Q (algebraMap R (R ⧸ I))
    have _ : IsScalarTower R (R ⧸ I) Q :=
      ⟨fun x y z => by
        change (algebraMap R (R ⧸ I) x * y) • z = algebraMap R (R ⧸ I) x • (y • z)
        rw [mul_smul]⟩
    exact (injective_rTensor_iff_injective_rTensor_mapQSMulTop I Q f).mp (hf Q)
  · intro hbar
    refine Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent f hI
      fun P _ _ hkill => ?_
    have hT : Module.IsTorsionBySet R P (I : Set R) := fun {x} {a} => hkill a a.2 x
    let _ : Module (R ⧸ I) P := hT.module
    have _ : IsScalarTower R (R ⧸ I) P := hT.isScalarTower
    exact (injective_rTensor_iff_injective_rTensor_mapQSMulTop I P f).mpr (hbar P)

end Stacks.NilpotentReduction

namespace AlgebraicGeometry

open Stacks.NilpotentReduction

/-- **Stacks Project, Tag 05U9 (universal injectivity), modulo a nilpotent ideal of the base.**
In Situation 0AT0 — a local homomorphism `A → B` of local rings essentially of finite type, a
flat `A`-module `M`, a finite `B`-module `N` and an `A`-linear `u : N → M` injective modulo the
maximal ideal of `A` — and for a nilpotent ideal `I ⊆ A`, the map `u` is `A`-universally
injective if and only if its reduction `N/IN → M/IM` is `A ⧸ I`-universally injective.

This is the last paragraph of the proof of Stacks 05U9 in the form its producer speaks: the
right-hand side is what Stacks 0AT9
(`AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective`) concludes, over the
base ring `A ⧸ I₀` for the finitely generated nilpotent ideal `I₀` that Claim 1 of the source
proof produces. -/
theorem universallyInjectivePoly_iff_reduction_of_isNilpotent
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    {I : Ideal S.A} (hI : IsNilpotent I) :
    UniversallyInjectivePoly.{_, u₅} S.u ↔
      UniversallyInjectivePoly.{_, u₅} (mapQSMulTop I S.u) :=
  universallyInjectivePoly_iff_mapQSMulTop_of_isNilpotent I S.u hI

/-- The equivalence is not vacuous at either end: over a Noetherian base both sides hold, with
`I = ⊥`, by the universal-injectivity clause of Stacks 0AT1. -/
theorem universallyInjectivePoly_reduction_of_isNoetherianRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [IsNoetherianRing S.A] :
    UniversallyInjectivePoly.{_, u₅} (mapQSMulTop (⊥ : Ideal S.A) S.u) :=
  (universallyInjectivePoly_iff_reduction_of_isNilpotent S (I := ⊥) ⟨1, by simp⟩).mp
    (universallyInjective_of_isNoetherianRing' S)

end AlgebraicGeometry

end
