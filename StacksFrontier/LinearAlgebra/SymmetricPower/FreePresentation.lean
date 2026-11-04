module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.MvPolynomial.HomogeneousBasis
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Free presentations of symmetric and exterior powers

Let `M₂ --g--> M₁ --f--> M → 0` be an exact presentation of modules over a commutative
ring `R`, and let `n = k + 1 ≥ 1`. The presentation sequences

* `M₂ ⊗ Symᵏ(M₁) --α--> Symᵏ⁺¹(M₁) --Symᵏ⁺¹(f)--> Symᵏ⁺¹(M) → 0`,
* `M₂ ⊗ ⋀ᵏ(M₁) --β--> ⋀ᵏ⁺¹(M₁) --⋀ᵏ⁺¹(f)--> ⋀ᵏ⁺¹(M) → 0`

are exact; when `M₁` and `M₂` are free (respectively finite free) the
first two terms of each sequence are again free (respectively finite free). So a free
presentation of `M` induces a free presentation of every positive symmetric and exterior
power, with the degree of the power free to vary.

## Main definitions

* `SymPow.symmetricPowerEquivHomogeneousSubmodule` identifies `Symⁿ(M)` with the
  degree-`n` homogeneous part of a polynomial ring on a basis of `M`.
* `SymPow.gradedMvPolynomialHom` and `SymPow.gradedMvPolynomialInv` assemble those
  degreewise identifications into mutually inverse homomorphisms of **graded rings**
  between `Sym_R(M)` and the polynomial ring on a basis of `M`: the symmetric algebra of a
  module with a basis indexed by `n + 1` elements is a graded polynomial ring in `n + 1`
  variables.

## Main results

* `SymPow.free_symmetricPower` and `SymPow.finite_symmetricPower`: the symmetric powers of
  a free (respectively finite) module are free (respectively finite). The exterior
  counterparts are `exteriorPower.instFree` and `exteriorPower.instFinite` in Mathlib.
* `SymPow.symmetricPower_freePresentation` and `exteriorPower_freePresentation` present
  every positive power of a freely presented module by free modules.
* `SymPow.symmetricPower_finiteFreePresentation` and
  `exteriorPower_finiteFreePresentation` are the finite free versions.

## Implementation notes

The symmetric power used here is `SymPow.symmetricPower n R M`, the `n`-th power of
`LinearMap.range (SymmetricAlgebra.ι R M)` inside `SymmetricAlgebra R M`, which is the
model Mathlib's `exteriorPower` uses on the exterior side and the one the presentation
sequences of Tag 00DO are stated for (rather than Mathlib's `SymmetricPower`, a quotient of a
`PiTensorProduct`). Freeness of `symmetricPower` is proved by transporting along
`SymmetricAlgebra.equivMvPolynomial` and using `MvPolynomial.homogeneousSubmodule_one_pow` to
recognise the `n`-th power of the degree-one part as the degree-`n` part, whose monomial basis
is `MvPolynomial.basisHomogeneousSubmodule`.

Finiteness is proved separately and does not go through a basis: the degree-one part is a
finitely generated submodule and finite generation is preserved by submodule powers, so no
freeness hypothesis is needed for `SymPow.finite_symmetricPower`.

The index type of the monomial basis is the subtype of `κ →₀ ℕ` cut out by `degree = n`,
with `κ` indexing a basis of the module; its cardinality is the number of degree-`n`
monomials. The finite statements are phrased with `Module.Finite` rather than with an
explicitly finite index type, which is the same information and avoids choosing a
numbering of the monomials.

## References

* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open scoped TensorProduct

namespace SymPow

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A basis of `M` identifies the degree-one part of `SymmetricAlgebra R M` with the span
of the variables in the corresponding polynomial ring. -/
theorem map_range_ι {κ : Type*} (b : Module.Basis κ R M) :
    Submodule.map (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toLinearMap
        (LinearMap.range (SymmetricAlgebra.ι R M)) =
      MvPolynomial.homogeneousSubmodule κ R 1 := by
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, ← LinearMap.range_comp,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext fun i => SymmetricAlgebra.equivMvPolynomial_ι_apply b i)

/-- A basis of `M` identifies `Symⁿ(M)` with the degree-`n` homogeneous part of the
polynomial ring on that basis. -/
theorem map_symmetricPower {κ : Type*} (b : Module.Basis κ R M) (n : ℕ) :
    Submodule.map (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toLinearMap
        (symmetricPower n R M) =
      MvPolynomial.homogeneousSubmodule κ R n := by
  rw [show symmetricPower n R M = LinearMap.range (SymmetricAlgebra.ι R M) ^ n from rfl,
    Submodule.map_pow, map_range_ι b, MvPolynomial.homogeneousSubmodule_one_pow]

/-- The symmetric power `Symⁿ(M)` of a module with a basis, identified with the degree-`n`
homogeneous part of the polynomial ring on that basis. -/
noncomputable def symmetricPowerEquivHomogeneousSubmodule {κ : Type*}
    (b : Module.Basis κ R M) (n : ℕ) :
    symmetricPower n R M ≃ₗ[R] MvPolynomial.homogeneousSubmodule κ R n :=
  (Submodule.equivMapOfInjective _
      (SymmetricAlgebra.equivMvPolynomial b).injective (symmetricPower n R M)).trans
    (LinearEquiv.ofEq _ _ (map_symmetricPower b n))

/-! ### The polynomial ring on a basis, as a graded ring -/

section Graded

variable {κ : Type*} (b : Module.Basis κ R M)

/-- **A basis of `M` identifies `Sym_R(M)` with a polynomial ring as a graded ring.** The
underlying algebra isomorphism is Mathlib's `SymmetricAlgebra.equivMvPolynomial`, and it carries
the `n`-th symmetric power into the degree-`n` homogeneous part by
`SymPow.map_symmetricPower`. -/
noncomputable def gradedMvPolynomialHom :
    (fun n : ℕ => symmetricPower n R M) →+*ᵍ MvPolynomial.homogeneousSubmodule κ R where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv.toRingHom
  map_mem {i _} hx := by
    rw [← map_symmetricPower b i]
    exact Submodule.mem_map_of_mem hx

/-- `SymPow.gradedMvPolynomialHom` is `SymmetricAlgebra.equivMvPolynomial` on elements. -/
@[simp]
theorem gradedMvPolynomialHom_apply (x : SymmetricAlgebra R M) :
    gradedMvPolynomialHom b x = SymmetricAlgebra.equivMvPolynomial b x :=
  rfl

/-- The inverse of `SymPow.gradedMvPolynomialHom`: a basis of `M` identifies a polynomial ring
with `Sym_R(M)` as a graded ring. -/
noncomputable def gradedMvPolynomialInv :
    MvPolynomial.homogeneousSubmodule κ R →+*ᵍ (fun n : ℕ => symmetricPower n R M) where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toRingHom
  map_mem {i _} hx := by
    rw [← map_symmetricPower b i] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy

/-- `SymPow.gradedMvPolynomialInv` is the inverse of `SymmetricAlgebra.equivMvPolynomial` on
elements. -/
@[simp]
theorem gradedMvPolynomialInv_apply (x : MvPolynomial κ R) :
    gradedMvPolynomialInv b x = (SymmetricAlgebra.equivMvPolynomial b).symm x :=
  rfl

/-- `SymPow.gradedMvPolynomialInv` is a right inverse of `SymPow.gradedMvPolynomialHom`. -/
theorem gradedMvPolynomialHom_comp_inv :
    (gradedMvPolynomialHom b).comp (gradedMvPolynomialInv b) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule κ R) :=
  GradedRingHom.ext fun x => (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x

/-- `SymPow.gradedMvPolynomialInv` is a left inverse of `SymPow.gradedMvPolynomialHom`. -/
theorem gradedMvPolynomialInv_comp_hom :
    (gradedMvPolynomialInv b).comp (gradedMvPolynomialHom b) =
      GradedRingHom.id (fun n : ℕ => symmetricPower n R M) :=
  GradedRingHom.ext fun x => (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x

end Graded

/-- The monomial basis of the symmetric power of a module with a basis. -/
noncomputable def basisSymmetricPower {κ : Type*} (b : Module.Basis κ R M) (n : ℕ) :
    Module.Basis {d : κ →₀ ℕ | d.degree = n} R (symmetricPower n R M) :=
  (MvPolynomial.basisHomogeneousSubmodule κ R n).map
    (symmetricPowerEquivHomogeneousSubmodule b n).symm

/-- The symmetric powers of a free module are free. This is the symmetric half of Tag
00DN, for the symmetric power modelled as a graded piece of the symmetric algebra. -/
instance free_symmetricPower [Module.Free R M] (n : ℕ) :
    Module.Free R (symmetricPower n R M) :=
  Module.Free.of_basis (basisSymmetricPower (Module.Free.chooseBasis R M) n)

/-- The symmetric powers of a finite module are finite. No freeness is needed. -/
@[ega "0 19.5.8" "partial", ega "II 1.7.7" "special case"]
instance finite_symmetricPower [Module.Finite R M] (n : ℕ) :
    Module.Finite R (symmetricPower n R M) := by
  refine Module.Finite.of_fg (Submodule.FG.pow ?_ n)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.mp ‹_›).map _

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- **Free presentations of symmetric powers.** If `M₂ --g--> M₁ --f--> M → 0` is exact and
`M₁`, `M₂` are free, then for every `n = k + 1 ≥ 1` the presentation sequence
`M₂ ⊗ Symᵏ(M₁) --α--> Symⁿ(M₁) --Symⁿ(f)--> Symⁿ(M) → 0` of Tag 00DO is exact and its
first two terms are free. -/
theorem symmetricPower_freePresentation [Module.Free R M₁] [Module.Free R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M) (hf : Function.Surjective f)
    (hexact : LinearMap.range g = LinearMap.ker f) (k : ℕ) :
    Module.Free R (M₂ ⊗[R] symmetricPower k R M₁) ∧
      Module.Free R (symmetricPower (k + 1) R M₁) ∧
      Function.Surjective (symMap (k + 1) f) ∧
      LinearMap.range (symMulMap k g) = LinearMap.ker (symMap (k + 1) f) :=
  ⟨inferInstance, inferInstance, symmetric_power_presentation g f hf hexact k⟩

/-- **Finite free presentations of symmetric powers.** The finite version of
`SymPow.symmetricPower_freePresentation`. -/
theorem symmetricPower_finiteFreePresentation [Module.Free R M₁] [Module.Free R M₂]
    [Module.Finite R M₁] [Module.Finite R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M) (hf : Function.Surjective f)
    (hexact : LinearMap.range g = LinearMap.ker f) (k : ℕ) :
    Module.Free R (M₂ ⊗[R] symmetricPower k R M₁) ∧
      Module.Finite R (M₂ ⊗[R] symmetricPower k R M₁) ∧
      Module.Free R (symmetricPower (k + 1) R M₁) ∧
      Module.Finite R (symmetricPower (k + 1) R M₁) ∧
      Function.Surjective (symMap (k + 1) f) ∧
      LinearMap.range (symMulMap k g) = LinearMap.ker (symMap (k + 1) f) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    symmetric_power_presentation g f hf hexact k⟩

end SymPow

/-- **Free presentations of exterior powers.** If `M₂ --g--> M₁ --f--> M → 0` is exact and
`M₁`, `M₂` are free, then for every `n = k + 1 ≥ 1` the presentation sequence
`M₂ ⊗ ⋀ᵏ(M₁) --β--> ⋀ⁿ(M₁) --⋀ⁿ(f)--> ⋀ⁿ(M) → 0` of Tag 00DO is exact and its first two
terms are free. -/
theorem exteriorPower_freePresentation {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Free R M₁] [Module.Free R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M) (hf : Function.Surjective f)
    (hexact : LinearMap.range g = LinearMap.ker f) (k : ℕ) :
    Module.Free R (M₂ ⊗[R] ⋀[R]^k M₁) ∧
      Module.Free R (⋀[R]^(k + 1) M₁) ∧
      Function.Surjective (exteriorPower.map (k + 1) f) ∧
      LinearMap.range (ExtPow.beta k g) = LinearMap.ker (exteriorPower.map (k + 1) f) :=
  ⟨inferInstance, inferInstance, exterior_power_presentation g f hf hexact k⟩

/-- **Finite free presentations of exterior powers.** The finite version of
`exteriorPower_freePresentation`. -/
theorem exteriorPower_finiteFreePresentation {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Free R M₁] [Module.Free R M₂]
    [Module.Finite R M₁] [Module.Finite R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M) (hf : Function.Surjective f)
    (hexact : LinearMap.range g = LinearMap.ker f) (k : ℕ) :
    Module.Free R (M₂ ⊗[R] ⋀[R]^k M₁) ∧
      Module.Finite R (M₂ ⊗[R] ⋀[R]^k M₁) ∧
      Module.Free R (⋀[R]^(k + 1) M₁) ∧
      Module.Finite R (⋀[R]^(k + 1) M₁) ∧
      Function.Surjective (exteriorPower.map (k + 1) f) ∧
      LinearMap.range (ExtPow.beta k g) = LinearMap.ker (exteriorPower.map (k + 1) f) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    exterior_power_presentation g f hf hexact k⟩

end
