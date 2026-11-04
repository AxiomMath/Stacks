module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMap
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksCore.Tactic.StacksAttribute

/-!
# The determinant map of a right-exact presentation by finite free modules

Let `R` be a commutative ring and let

`ℰ₁ --α--> ℰ₀ --π--> ℱ ⟶ 0`

be a right-exact sequence of `R`-modules with `ℰ₁` free of rank `r₁`. Writing `r₀ = r₁ + r`,
this file constructs the canonical map

`⋀^r ℱ ⟶ ⋀^{r₁}(ℰ₁^∨) ⊗ ⋀^{r₀} ℰ₀`

of [Stacks, Tag 0E9Y] in the module-theoretic (equivalently: stalkwise) case, pins it down by
the local formula the source gives,

`s₁ ∧ ⋯ ∧ s_r ↦ t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨ ⊗ α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r`

for `t` a basis of `ℰ₁` and `s̃ᵢ` lifts of `sᵢ`, and proves it is an isomorphism when the
presentation is split with `ℱ` free of rank `r`.

## The construction

The source omits the proof that the displayed formula is well defined; that proof is the whole
content here, and it is a descent along the epimorphism `⋀^r ℰ₀ ⟶ ⋀^r ℱ`.

Wedging with the top wedge `α(t₁) ∧ ⋯ ∧ α(t_{r₁})` of the image of a basis of `ℰ₁` is a linear
map `⋀^r ℰ₀ ⟶ ⋀^{r₁ + r} ℰ₀`; tensoring its value with the top wedge of the dual basis gives
`determinantLift`. Its kernel contains the kernel of `⋀^r π`: by the exterior half of
[Stacks, Tag 00DO] that kernel is the image of `ker π ⊗ ⋀^{r-1} ℰ₀ ⟶ ⋀^r ℰ₀`,
`x ⊗ y ↦ x ∧ y`, so it is enough that `α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ α(m)` vanishes for every
`m : ℰ₁` — and that wedge is the image under `⋀ α` of `t₁ ∧ ⋯ ∧ t_{r₁} ∧ m`, a section of
`⋀^{r₁ + 1} ℰ₁ = 0`. Since `⋀^r π` is surjective, the descent is unique.

The resulting map does not depend on the basis of `ℰ₁`: changing the basis multiplies the top
wedge of the dual basis by one unit and the top wedge of the image basis by its inverse. This is
the same cancellation as in `Stacks.DeRham.ιMulti_tmul_basisTopDual_eq`, read through the
identification of `⋀^{r₁}(ℰ₁^∨)` with `(⋀^{r₁} ℰ₁)^∨`.

## Main definitions

* `exteriorPower.pairingDualEquiv`: **the exterior power of the dual is the dual of the exterior
  power** for a finite free module — Mathlib's `exteriorPower.pairingDual` packaged as a linear
  equivalence using `exteriorPower.bijective_pairingDual`.
* `Stacks.Duality.descOfSurjective`: the descent of a linear map along a surjection whose kernel
  it kills, with a real body rather than a choice.
* `Stacks.Duality.determinantLift`: the map `⋀^r ℰ₀ ⟶ ⋀^{r₁}(ℰ₁^∨) ⊗ ⋀^{r₁ + r} ℰ₀` that the
  determinant map descends from.
* `Stacks.Duality.determinantMap`: **the canonical map of Tag 0E9Y**.
* `Stacks.Duality.basisOfAdapted`: the basis of `ℱ` carried by a presentation split by an adapted
  basis of `ℰ₀`.

## Main results

* `exteriorPower.pairingDual_ιMulti_dualBasis`: the top wedge of a dual basis pairs to
  `Stacks.DeRham.basisTopDual`.
* `Stacks.Duality.determinantMap_map` and `Stacks.Duality.determinantMap_ιMulti`: **the local
  formula of Tag 0E9Y**, in the form "the composite with `⋀^r π` is `determinantLift`" and
  evaluated on a wedge of sections with chosen lifts.
* `Stacks.Duality.determinantMap_unique`: the formula determines the map.
* `Stacks.Duality.determinantMap_congr_basis`: the map does not depend on the chosen basis
  of `ℰ₁`, so it is canonical.
* `Stacks.Duality.bijective_determinantMap` and
  `Stacks.Duality.bijective_determinantMap_of_adapted`: **the determinant map is an isomorphism
  when the presentation is split with `ℱ` free of rank `r`**, which is the "straightforward"
  direction of the equivalence Tag 0E9Y asserts.
* `Stacks.Duality.linearIndependent_of_adapted` and `Stacks.Duality.span_of_adapted`: the two
  halves of `Stacks.Duality.basisOfAdapted`.

## Implementation notes

**Ranks are written additively.** The source writes the degree of the source of the map as
`r₀ - r₁` and the degree of the last factor as `r₀`; here the two are `r` and `r₁ + r`, which
says the same thing without truncated subtraction and makes `r₁ ≤ r₀` a hypothesis-free
consequence of the shape. The case `r₁ > r₀` of the source, where the exterior power is zero by
convention and no isomorphism can exist, is therefore not expressible and not needed.

**Free of rank `r₁` is recorded by a basis indexed by `Fin r₁`.** This is the convention of
`StacksFrontier.AlgebraicGeometry.Duality.FunnyMap`, and it handles the zero ring with no
nontriviality side condition.

**Right exactness is two separate hypotheses.** Surjectivity of `π` and the equality
`range α = ker π` are supplied as plain hypotheses rather than bundled into a short complex,
because they are exactly what the exterior half of Tag 00DO consumes. No quotient is formed:
`ℱ` is an arbitrary module receiving a surjection from `ℰ₀`.

**The degree-zero case of Tag 00DO.** The exterior half of Tag 00DO is stated for degrees `≥ 1`,
so `Stacks.Duality.ker_map_le_ker_determinantLift` splits off `r = 0`, where
`⋀^0 π` is an isomorphism (both sides are `R`) and the kernel is zero.

## References

* [Stacks Project, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 0FL8](https://stacks.math.columbia.edu/tag/0FL8)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The exterior power of the dual is the dual of the exterior power.** For a finite free
module `M` the canonical pairing `exteriorPower.pairingDual` is bijective, so it identifies
`⋀ⁿ(M^∨)` with `(⋀ⁿ M)^∨`. -/
noncomputable def pairingDualEquiv (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (n : ℕ) :
    ⋀[R]^n (Module.Dual R M) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  LinearEquiv.ofBijective (pairingDual R M n) (bijective_pairingDual R M n)

@[simp]
theorem pairingDualEquiv_apply [Module.Free R M] [Module.Finite R M] (n : ℕ)
    (x : ⋀[R]^n (Module.Dual R M)) : pairingDualEquiv R M n x = pairingDual R M n x := rfl

/-- The top wedge of a dual basis, paired against the top wedge of a family of vectors, is the
determinant of the coordinate matrix of that family. -/
theorem pairingDual_ιMulti_dualBasis_apply_ιMulti {n : ℕ} (b : Module.Basis (Fin n) R M)
    (v : Fin n → M) :
    pairingDual R M n (ιMulti R n b.dualBasis) (ιMulti R n v) = b.det v := by
  classical
  rw [pairingDual_ιMulti_ιMulti, Module.Basis.det_apply,
    ← Matrix.det_transpose (b.toMatrix v)]
  congr 1 with i j
  rw [Matrix.of_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
    Module.Basis.coe_dualBasis, Module.Basis.coord_apply]

/-- **The top wedge of a dual basis is the dual of the top wedge of the basis.** Under
`exteriorPower.pairingDual` the section `t₁^∨ ∧ ⋯ ∧ tₙ^∨` of `⋀ⁿ(M^∨)` goes to the linear form
`Stacks.DeRham.basisTopDual` that takes the value `1` on `t₁ ∧ ⋯ ∧ tₙ`. -/
theorem pairingDual_ιMulti_dualBasis {n : ℕ} (b : Module.Basis (Fin n) R M) :
    pairingDual R M n (ιMulti R n b.dualBasis) = Stacks.DeRham.basisTopDual b := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro x ⟨v, rfl⟩
  rw [pairingDual_ιMulti_dualBasis_apply_ιMulti, Stacks.DeRham.basisTopDual,
    alternatingMapLinearEquiv_apply_ιMulti]

/-- **Change of basis for the top wedge of a dual basis.** Replacing the basis `b` by `b'`
multiplies `t₁^∨ ∧ ⋯ ∧ tₙ^∨` by the determinant of `b` in the basis `b'`. -/
theorem ιMulti_dualBasis_eq_smul [Module.Free R M] [Module.Finite R M] {n : ℕ}
    (b b' : Module.Basis (Fin n) R M) :
    ιMulti R n b'.dualBasis = b'.det b • ιMulti R n b.dualBasis := by
  refine (pairingDualEquiv R M n).injective ?_
  rw [pairingDualEquiv_apply, pairingDualEquiv_apply, map_smul,
    pairingDual_ιMulti_dualBasis, pairingDual_ιMulti_dualBasis,
    Stacks.DeRham.basisTopDual, Stacks.DeRham.basisTopDual, ← map_smul]
  exact congrArg _ ((Module.Basis.det b').eq_smul_basis_det b)

end exteriorPower

namespace Stacks.Duality

open Stacks.DeRham

section Desc

variable {R : Type u} [CommRing R] {A : Type v} {B : Type w} {Z : Type x}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup Z] [Module R Z]

/-- **Descent along a surjection.** A linear map `Φ : A ⟶ Z` whose kernel contains the kernel of
a surjection `s : A ⟶ B` factors through `s`. The factorization is built from the first
isomorphism theorem rather than chosen from an existence statement, so it has a body. -/
noncomputable def descOfSurjective (s : A →ₗ[R] B) (hs : Function.Surjective s) (Φ : A →ₗ[R] Z)
    (h : LinearMap.ker s ≤ LinearMap.ker Φ) : B →ₗ[R] Z :=
  ((LinearMap.ker s).liftQ Φ h).comp (LinearMap.quotKerEquivOfSurjective s hs).symm.toLinearMap

@[simp]
theorem descOfSurjective_apply (s : A →ₗ[R] B) (hs : Function.Surjective s) (Φ : A →ₗ[R] Z)
    (h : LinearMap.ker s ≤ LinearMap.ker Φ) (a : A) :
    descOfSurjective s hs Φ h (s a) = Φ a := by
  rw [descOfSurjective, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The descent along a surjection is the only linear map with its defining property. -/
theorem eq_descOfSurjective (s : A →ₗ[R] B) (hs : Function.Surjective s) (Φ : A →ₗ[R] Z)
    (h : LinearMap.ker s ≤ LinearMap.ker Φ) (D : B →ₗ[R] Z) (hD : ∀ a, D (s a) = Φ a) :
    D = descOfSurjective s hs Φ h := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨a, rfl⟩ := hs y
  rw [hD, descOfSurjective_apply]

end Desc

section Vanishing

variable {R : Type u} [CommRing R] {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]

/-- A module free of rank `r₁` has no nonzero sections of `⋀^{r₁+1}`. -/
theorem subsingleton_exteriorPower_succ {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁) :
    Subsingleton (⋀[R]^(r₁ + 1) M₁) :=
  exteriorPower.subsingleton_of_span_eq_top_of_card_lt (R := R) (b : Fin r₁ → M₁) b.span_eq
    (r₁ + 1) (by simp)

/-- A one-element wedge is a degree-one generator. -/
theorem ιMulti_one_eq (m : M₁) :
    ExteriorAlgebra.ιMulti R 1 (fun _ => m) = ExteriorAlgebra.ι R m := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp

/-- **The top wedge of a basis wedged with one more vector vanishes.** For `b` a basis of `M₁`
indexed by `Fin r₁` the product `b₁ ∧ ⋯ ∧ b_{r₁} ∧ m` lies in `⋀^{r₁+1} M₁ = 0`. -/
theorem ιMulti_basis_mul_ι_eq_zero {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁) (m : M₁) :
    ExteriorAlgebra.ιMulti R r₁ (b : Fin r₁ → M₁) * ExteriorAlgebra.ι R m = 0 := by
  have := subsingleton_exteriorPower_succ b
  have h0 : exteriorPower.wedgeMul (R := R) r₁ 1 (exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁))
      (exteriorPower.ιMulti R 1 (fun _ => m)) = 0 := Subsingleton.elim _ _
  have h1 := Subtype.ext_iff.mp h0
  rw [exteriorPower.wedgeMul_apply_coe, exteriorPower.ιMulti_apply_coe,
    exteriorPower.ιMulti_apply_coe, ιMulti_one_eq] at h1
  simpa using h1

end Vanishing

section DeterminantMap

variable {R : Type u} [CommRing R] {M₁ : Type v} {M₀ : Type w} {F : Type x}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup F] [Module R F]

/-- **The lift of the determinant map to `⋀^r ℰ₀`.** It wedges a section of `⋀^r ℰ₀` on the left
with `α(t₁) ∧ ⋯ ∧ α(t_{r₁})` and tensors the result with the top wedge `t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨` of
the dual basis. The determinant map of Tag 0E9Y is its descent along `⋀^r π`. -/
noncomputable def determinantLift (α : M₁ →ₗ[R] M₀) {r₁ : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (r : ℕ) :
    (⋀[R]^r M₀) →ₗ[R] (⋀[R]^r₁ (Module.Dual R M₁)) ⊗[R] (⋀[R]^(r₁ + r) M₀) :=
  (TensorProduct.mk R (⋀[R]^r₁ (Module.Dual R M₁)) (⋀[R]^(r₁ + r) M₀)
      (exteriorPower.ιMulti R r₁ b.dualBasis)).comp
    (exteriorPower.wedgeMul (R := R) r₁ r (exteriorPower.ιMulti R r₁ fun i => α (b i)))

theorem determinantLift_apply (α : M₁ →ₗ[R] M₀) {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁)
    (r : ℕ) (η : ⋀[R]^r M₀) :
    determinantLift α b r η =
      exteriorPower.ιMulti R r₁ b.dualBasis ⊗ₜ[R]
        exteriorPower.wedgeMul (R := R) r₁ r (exteriorPower.ιMulti R r₁ fun i => α (b i)) η := rfl

/-- `determinantLift` on a wedge of sections of `ℰ₀` concatenates the two families. -/
theorem determinantLift_ιMulti (α : M₁ →ₗ[R] M₀) {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁)
    (r : ℕ) (v : Fin r → M₀) :
    determinantLift α b r (exteriorPower.ιMulti R r v) =
      exteriorPower.ιMulti R r₁ b.dualBasis ⊗ₜ[R]
        exteriorPower.ιMulti R (r₁ + r) (Fin.append (fun i => α (b i)) v) := by
  rw [determinantLift_apply, exteriorPower.wedgeMul_ιMulti]

/-- **The key vanishing.** `determinantLift` kills a section of `⋀^r ℰ₀` of the form
`α(m) ∧ y`, because `α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ α(m)` is the image under `⋀ α` of a section of
`⋀^{r₁ + 1} ℰ₁ = 0`. -/
theorem determinantLift_comp_beta (α : M₁ →ₗ[R] M₀) {r₁ : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (k : ℕ) :
    (determinantLift α b (k + 1)).comp (ExtPow.beta k α) = 0 := by
  refine TensorProduct.ext' fun m y => ?_
  rw [LinearMap.comp_apply, determinantLift_apply, LinearMap.zero_apply]
  refine Eq.trans (congrArg _ ?_) (TensorProduct.tmul_zero _ _)
  refine Subtype.ext ?_
  rw [exteriorPower.wedgeMul_apply_coe, ZeroMemClass.coe_zero, ExtPow.beta_tmul,
    exteriorPower.ιMulti_apply_coe, ← mul_assoc]
  have hmap : ExteriorAlgebra.ιMulti R r₁ (fun i => α (b i)) * ExteriorAlgebra.ι R (α m) =
      ExteriorAlgebra.map α
        (ExteriorAlgebra.ιMulti R r₁ (b : Fin r₁ → M₁) * ExteriorAlgebra.ι R m) := by
    rw [map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · have h := Subtype.ext_iff.mp
        (exteriorPower.map_apply_ιMulti (R := R) (n := r₁) α (b : Fin r₁ → M₁))
      rw [exteriorPower.coe_map, exteriorPower.ιMulti_apply_coe,
        exteriorPower.ιMulti_apply_coe] at h
      exact h.symm
    · exact (LinearMap.congr_fun (ExteriorAlgebra.map_comp_ι α) m).symm
  rw [hmap, ιMulti_basis_mul_ι_eq_zero b m, map_zero, zero_mul]

/-- The kernel of `⋀^0 π` is zero: in degree zero both exterior powers are `R` and the map is
the identity. -/
theorem ker_map_zero (π : M₀ →ₗ[R] F) :
    LinearMap.ker (exteriorPower.map 0 π) = ⊥ := by
  have key : (exteriorPower.zeroEquiv R F).toLinearMap.comp
      (exteriorPower.map 0 π) = (exteriorPower.zeroEquiv R M₀).toLinearMap := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span R 0 M₀) ?_
    rintro x ⟨v, rfl⟩
    simp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  refine (exteriorPower.zeroEquiv R M₀).injective ?_
  have h := LinearMap.congr_fun key x
  rw [LinearMap.comp_apply, hx] at h
  simpa using h.symm

/-- **The kernel of `⋀^r π` is killed by `determinantLift`.** This is the well-definedness of
the formula of Tag 0E9Y, which the source omits: that kernel is described by the exterior half
of Tag 00DO as the set of sums of sections `α(m) ∧ y`, and those are killed by
`Stacks.Duality.determinantLift`. -/
theorem ker_map_le_ker_determinantLift (α : M₁ →ₗ[R] M₀) {r₁ : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (r : ℕ) (π : M₀ →ₗ[R] F)
    (hπ : Function.Surjective π) (hex : LinearMap.range α = LinearMap.ker π) :
    LinearMap.ker (exteriorPower.map r π) ≤ LinearMap.ker (determinantLift α b r) := by
  match r with
  | 0 => rw [ker_map_zero]; exact bot_le
  | (k + 1) =>
    have hker := (exterior_power_presentation α π hπ hex k).2
    intro z hz
    rw [← hker] at hz
    obtain ⟨t, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun (determinantLift_comp_beta α b k) t

/-- **The canonical map of Tag 0E9Y**, attached to a right-exact sequence

`ℰ₁ --α--> ℰ₀ --π--> ℱ ⟶ 0`

of `R`-modules and a basis of `ℰ₁` indexed by `Fin r₁`:

`⋀^r ℱ ⟶ ⋀^{r₁}(ℰ₁^∨) ⊗ ⋀^{r₁ + r} ℰ₀`.

It is the descent of `Stacks.Duality.determinantLift` along the epimorphism `⋀^r π`, and by
`Stacks.Duality.determinantMap_congr_basis` it does not depend on the chosen basis, so it is
canonical. -/
noncomputable def determinantMap (α : M₁ →ₗ[R] M₀) {r₁ : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (r : ℕ) (π : M₀ →ₗ[R] F)
    (hπ : Function.Surjective π) (hex : LinearMap.range α = LinearMap.ker π) :
    (⋀[R]^r F) →ₗ[R] (⋀[R]^r₁ (Module.Dual R M₁)) ⊗[R] (⋀[R]^(r₁ + r) M₀) :=
  descOfSurjective (exteriorPower.map r π) (exteriorPower.map_surjective hπ)
    (determinantLift α b r) (ker_map_le_ker_determinantLift α b r π hπ hex)

/-- **The defining property of the determinant map**: its composite with `⋀^r π` is
`Stacks.Duality.determinantLift`. -/
@[simp]
theorem determinantMap_map (α : M₁ →ₗ[R] M₀) {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁)
    (r : ℕ) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π) (η : ⋀[R]^r M₀) :
    determinantMap α b r π hπ hex (exteriorPower.map r π η) = determinantLift α b r η :=
  descOfSurjective_apply _ _ _ _ η

/-- **The local formula of Tag 0E9Y.** For `t` a basis of `ℰ₁`, sections `s₁, …, s_r` of `ℱ` and
lifts `s̃₁, …, s̃_r` of them to `ℰ₀`, the determinant map sends `s₁ ∧ ⋯ ∧ s_r` to

`t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨ ⊗ α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r`. -/
theorem determinantMap_ιMulti (α : M₁ →ₗ[R] M₀) {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁)
    (r : ℕ) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π) (s : Fin r → F)
    (v : Fin r → M₀) (hv : ∀ i, π (v i) = s i) :
    determinantMap α b r π hπ hex (exteriorPower.ιMulti R r s) =
      exteriorPower.ιMulti R r₁ b.dualBasis ⊗ₜ[R]
        exteriorPower.ιMulti R (r₁ + r) (Fin.append (fun i => α (b i)) v) := by
  have hs : exteriorPower.map r π (exteriorPower.ιMulti R r v) =
      exteriorPower.ιMulti R r s := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ (funext hv)
  rw [← hs, determinantMap_map, determinantLift_ιMulti]

/-- **The local formula determines the determinant map.** Any linear map out of `⋀^r ℱ` whose
composite with `⋀^r π` is `Stacks.Duality.determinantLift` equals it. -/
theorem determinantMap_unique (α : M₁ →ₗ[R] M₀) {r₁ : ℕ} (b : Module.Basis (Fin r₁) R M₁)
    (r : ℕ) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (D : (⋀[R]^r F) →ₗ[R] (⋀[R]^r₁ (Module.Dual R M₁)) ⊗[R] (⋀[R]^(r₁ + r) M₀))
    (hD : ∀ η : ⋀[R]^r M₀, D (exteriorPower.map r π η) = determinantLift α b r η) :
    D = determinantMap α b r π hπ hex :=
  eq_descOfSurjective _ _ _ _ D hD

/-- Every section of the top exterior power of a free module is a multiple, by its
`basisTopDual` coordinate, of the wedge of the basis. -/
private theorem eq_basisTopDual_smul_ιMulti {N : Type v} [AddCommGroup N] [Module R N] {n : ℕ}
    (b : Module.Basis (Fin n) R N) (x : ⋀[R]^n N) :
    x = basisTopDual b x • exteriorPower.ιMulti R n (b : Fin n → N) := by
  simpa using eq_basisTopDual_smul b LinearMap.id x

/-- **The determinant map is canonical: it does not depend on the basis of `ℰ₁`.** Changing the
basis scales the top wedge of the dual basis and the top wedge of the image basis by inverse
units. -/
theorem determinantMap_congr_basis (α : M₁ →ₗ[R] M₀) {r₁ : ℕ}
    (b b' : Module.Basis (Fin r₁) R M₁) (r : ℕ) (π : M₀ →ₗ[R] F)
    (hπ : Function.Surjective π) (hex : LinearMap.range α = LinearMap.ker π) :
    determinantMap α b r π hπ hex = determinantMap α b' r π hπ hex := by
  have : Module.Free R M₁ := Module.Free.of_basis b
  have : Module.Finite R M₁ := Module.Finite.of_basis b
  refine determinantMap_unique α b' r π hπ hex _ fun η => ?_
  rw [determinantMap_map, determinantLift_apply, determinantLift_apply]
  have h1 : exteriorPower.ιMulti R r₁ b'.dualBasis =
      b'.det b • exteriorPower.ιMulti R r₁ b.dualBasis :=
    exteriorPower.ιMulti_dualBasis_eq_smul b b'
  have h2 : (exteriorPower.ιMulti R r₁ fun i => α (b' i)) =
      b.det b' • exteriorPower.ιMulti R r₁ fun i => α (b i) := by
    have hb : exteriorPower.ιMulti R r₁ (b' : Fin r₁ → M₁) =
        b.det b' • exteriorPower.ιMulti R r₁ (b : Fin r₁ → M₁) := by
      simpa [basisTopDual] using eq_basisTopDual_smul_ιMulti b
        (exteriorPower.ιMulti R r₁ (b' : Fin r₁ → M₁))
    have h := congrArg (exteriorPower.map r₁ α) hb
    simpa [exteriorPower.map_apply_ιMulti, Function.comp_def] using h
  have h3 : b.det b' * b'.det b = 1 := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [h1, h2, map_smul, LinearMap.smul_apply, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, h3, one_smul]

end DeterminantMap

section Bijective

variable {R : Type u} [CommRing R] {M₁ : Type v} {M₀ : Type w} {F : Type x}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup F] [Module R F]

/-- A linear map is determined on a vector by its values on a finite basis. -/
private theorem map_eq_sum_repr_smul {ι : Type*} [Fintype ι] {N : Type*} [AddCommGroup N]
    [Module R N] (f : M₀ →ₗ[R] N) (c : Module.Basis ι R M₀) (y : M₀) :
    f y = ∑ i, c.repr y i • f (c i) := by
  conv_lhs => rw [← c.sum_repr y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul f _ _

/-- If `A` is generated by `x` and `B` by `y`, then `A ⊗ B` is generated by `x ⊗ y`. -/
theorem span_singleton_tmul_eq_top {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (x : A) (y : B)
    (hx : Submodule.span R {x} = ⊤) (hy : Submodule.span R {y} = ⊤) :
    Submodule.span R {x ⊗ₜ[R] y} = (⊤ : Submodule R (A ⊗[R] B)) := by
  refine top_unique ?_
  rw [← TensorProduct.span_tmul_eq_top R A B, Submodule.span_le]
  rintro - ⟨a, c, rfl⟩
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1
    (hx.ge (Submodule.mem_top : a ∈ (⊤ : Submodule R A)))
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1
    (hy.ge (Submodule.mem_top : c ∈ (⊤ : Submodule R B)))
  have h : (s • x) ⊗ₜ[R] (t • y) = (s * t) • (x ⊗ₜ[R] y) := by
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]
  rw [SetLike.mem_coe, h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A presentation adapted to a basis of `ℰ₀`: the first block of the basis is the image of a
basis of `ℰ₁`. -/
theorem apply_castAdd_of_adapted {α : M₁ →ₗ[R] M₀} {r₁ r : ℕ}
    {b : Module.Basis (Fin r₁) R M₁} {w : Fin r → M₀}
    {c : Module.Basis (Fin (r₁ + r)) R M₀}
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) (j : Fin r₁) :
    c (Fin.castAdd r j) = α (b j) := by
  rw [hc]; exact Fin.append_left _ _ j

/-- The second block of an adapted basis of `ℰ₀` is the chosen family of lifts. -/
theorem apply_natAdd_of_adapted {α : M₁ →ₗ[R] M₀} {r₁ r : ℕ}
    {b : Module.Basis (Fin r₁) R M₁} {w : Fin r → M₀}
    {c : Module.Basis (Fin (r₁ + r)) R M₀}
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) (k : Fin r) :
    c (Fin.natAdd r₁ k) = w k := by
  rw [hc]; exact Fin.append_right _ _ k

/-- **The images of the lifts in a split presentation are independent.** A relation among the
`π(wᵢ)` lifts to a relation among the whole adapted basis of `ℰ₀`, hence is trivial. -/
theorem linearIndependent_of_adapted (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F)
    (hex : LinearMap.range α = LinearMap.ker π) (w : Fin r → M₀)
    (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) :
    LinearIndependent R fun i => π (w i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : π (∑ k, g k • w k) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hg
  obtain ⟨m, hm⟩ : (∑ k, g k • w k) ∈ LinearMap.range α := by
    rw [hex]; exact LinearMap.mem_ker.2 h1
  have hαm := map_eq_sum_repr_smul α b m
  have hzero : ∑ i, Fin.append (fun j => b.repr m j) (fun k => -g k) i • c i = 0 := by
    rw [Fin.sum_univ_add]
    have e₁ : ∀ j : Fin r₁,
        Fin.append (fun j => b.repr m j) (fun k => -g k) (Fin.castAdd r j) •
          c (Fin.castAdd r j) = b.repr m j • α (b j) := fun j => by
      rw [Fin.append_left, apply_castAdd_of_adapted hc]
    have e₂ : ∀ k : Fin r,
        Fin.append (fun j => b.repr m j) (fun k => -g k) (Fin.natAdd r₁ k) •
          c (Fin.natAdd r₁ k) = -(g k • w k) := fun k => by
      rw [Fin.append_right, apply_natAdd_of_adapted hc, neg_smul]
    rw [Finset.sum_congr rfl fun j _ => e₁ j, Finset.sum_congr rfl fun k _ => e₂ k,
      Finset.sum_neg_distrib, ← hαm, hm, add_neg_cancel]
  have h := (Fintype.linearIndependent_iff.1 c.linearIndependent) _ hzero (Fin.natAdd r₁ i)
  rw [Fin.append_right] at h
  exact neg_eq_zero.1 h

/-- **The images of the lifts in a split presentation span `ℱ`.** `π` is surjective and kills
the first block of the adapted basis of `ℰ₀`. -/
theorem span_of_adapted (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π) (w : Fin r → M₀)
    (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) :
    (⊤ : Submodule R F) ≤ Submodule.span R (Set.range fun i => π (w i)) := by
  have hkill : ∀ j : Fin r₁, π (α (b j)) = 0 := fun j =>
    LinearMap.mem_ker.1 (hex.le (LinearMap.mem_range_self α (b j)))
  intro x _
  obtain ⟨y, rfl⟩ := hπ x
  rw [map_eq_sum_repr_smul π c y]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · rw [apply_castAdd_of_adapted hc, hkill, smul_zero]
    exact Submodule.zero_mem _
  · rw [apply_natAdd_of_adapted hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **The basis of `ℱ` carried by a split presentation.** If `ℰ₁ --α--> ℰ₀ --π--> ℱ ⟶ 0` is
right exact, `b` is a basis of `ℰ₁` and the concatenated family `α(b₁), …, α(b_{r₁}), w₁, …, w_r`
is a basis of `ℰ₀`, then `π(w₁), …, π(w_r)` is a basis of `ℱ`, so `ℱ` is free of rank `r`. -/
noncomputable def basisOfAdapted (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π) (w : Fin r → M₀)
    (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) :
    Module.Basis (Fin r) R F :=
  Module.Basis.mk (linearIndependent_of_adapted α b π hex w c hc)
    (span_of_adapted α b π hπ hex w c hc)

@[simp]
theorem basisOfAdapted_apply (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π) (w : Fin r → M₀)
    (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) (i : Fin r) :
    basisOfAdapted α b π hπ hex w c hc i = π (w i) :=
  Module.Basis.mk_apply _ _ i

/-- **The determinant map of Tag 0E9Y is an isomorphism when the presentation is split with
`ℱ` free of rank `r`.** The hypotheses say exactly that: `b` is a basis of `ℰ₁`, the family
`α(b₁), …, α(b_{r₁}), w₁, …, w_r` is a basis `c` of `ℰ₀`, and the images `π(wᵢ)` form a basis `d`
of `ℱ`. Source and target are then free of rank one, the determinant map matches their
generators, so it is bijective.

This is the "straightforward" direction of the equivalence Tag 0E9Y asserts. The hypothesis is
stronger than local freeness of `ℱ` alone: in the sheaf setting the adapted bases `c` and `d` are
produced from local freeness of `ℱ` by splitting `π` and using that over a local ring a finite
projective module is free of the expected rank, which is not formalized here. -/
theorem bijective_determinantMap (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (w : Fin r → M₀) (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i)
    (d : Module.Basis (Fin r) R F) (hd : ∀ i, d i = π (w i)) :
    Function.Bijective (determinantMap α b r π hπ hex) := by
  have : Module.Free R M₁ := Module.Free.of_basis b
  have : Module.Finite R M₁ := Module.Finite.of_basis b
  set g₁ : ⋀[R]^r₁ (Module.Dual R M₁) := exteriorPower.ιMulti R r₁ b.dualBasis with hg₁
  set g₂ : ⋀[R]^(r₁ + r) M₀ := exteriorPower.ιMulti R (r₁ + r) (c : Fin (r₁ + r) → M₀) with hg₂
  -- the determinant map sends the generator of the source to `g₁ ⊗ g₂`
  have hgen : determinantMap α b r π hπ hex (exteriorPower.ιMulti R r (d : Fin r → F)) =
      g₁ ⊗ₜ[R] g₂ := by
    rw [determinantMap_ιMulti α b r π hπ hex (d : Fin r → F) w (fun i => (hd i).symm), hg₁, hg₂]
    exact congrArg _ (congrArg _ (funext fun i => (hc i).symm))
  -- the composite with the product of the two top-wedge coordinates is the coordinate of `d`
  set φ : (⋀[R]^r₁ (Module.Dual R M₁)) ⊗[R] (⋀[R]^(r₁ + r) M₀) →ₗ[R] R :=
    (TensorProduct.lid R R).toLinearMap.comp
      (TensorProduct.map (basisTopDual b.dualBasis) (basisTopDual c)) with hφ
  have hφgen : φ (g₁ ⊗ₜ[R] g₂) = 1 := by
    rw [hφ, LinearMap.comp_apply, TensorProduct.map_tmul, hg₁, hg₂, basisTopDual_apply,
      basisTopDual_apply]
    simp
  have hcomp : φ.comp (determinantMap α b r π hπ hex) = basisTopDual d := by
    refine linearMap_top_ext d ?_
    rw [LinearMap.comp_apply, hgen, hφgen, basisTopDual_apply]
  refine ⟨?_, ?_⟩
  · intro y z hyz
    have h : basisTopDual d y = basisTopDual d z := by
      have h1 := LinearMap.congr_fun hcomp y
      have h2 := LinearMap.congr_fun hcomp z
      rw [LinearMap.comp_apply, hyz] at h1
      rw [LinearMap.comp_apply] at h2
      exact h1.symm.trans h2
    rw [eq_basisTopDual_smul_ιMulti d y, eq_basisTopDual_smul_ιMulti d z, h]
  · intro z
    have hz : z ∈ Submodule.span R {g₁ ⊗ₜ[R] g₂} := by
      rw [span_singleton_tmul_eq_top g₁ g₂ (hg₁ ▸ span_singleton_ιMulti_basis b.dualBasis)
        (hg₂ ▸ span_singleton_ιMulti_basis c)]
      exact Submodule.mem_top
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨t • exteriorPower.ιMulti R r (d : Fin r → F), by rw [map_smul, hgen]⟩

/-- **The determinant map of Tag 0E9Y is an isomorphism for a split presentation.** This is
`Stacks.Duality.bijective_determinantMap` with the basis of `ℱ` produced by
`Stacks.Duality.basisOfAdapted` instead of assumed. -/
theorem bijective_determinantMap_of_adapted (α : M₁ →ₗ[R] M₀) {r₁ r : ℕ}
    (b : Module.Basis (Fin r₁) R M₁) (π : M₀ →ₗ[R] F) (hπ : Function.Surjective π)
    (hex : LinearMap.range α = LinearMap.ker π)
    (w : Fin r → M₀) (c : Module.Basis (Fin (r₁ + r)) R M₀)
    (hc : ∀ i, c i = Fin.append (fun j => α (b j)) w i) :
    Function.Bijective (determinantMap α b r π hπ hex) :=
  bijective_determinantMap α b π hπ hex w c hc (basisOfAdapted α b π hπ hex w c hc)
    (basisOfAdapted_apply α b π hπ hex w c hc)

end Bijective

end Stacks.Duality

end
