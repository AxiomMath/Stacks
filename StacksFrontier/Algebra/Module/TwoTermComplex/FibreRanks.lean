module

public import StacksFrontier.Algebra.Module.TwoTermComplex.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre dimensions of a two-term complex of finite projective modules

Let `δ : K₀ ⟶ K₁` be a map of finite projective `R`-modules. At a point `p` of `Spec R` write
`δ(p) : κ(p) ⊗ K₀ ⟶ κ(p) ⊗ K₁` for the fibre of `δ`. Then

* the alternating sum `dim ker δ(p) - dim coker δ(p)` is the difference of the ranks of `K₀` and
  `K₁` at `p`, hence a locally constant function of `p`;
* the locus where `coker δ(p) = 0` is open: it is the complement of the support of `coker δ`;
* consequently, for every `r`, the locus where `coker δ(p) = 0` and `dim ker δ(p) = r` is open.

These are the statements about a perfect complex of amplitude `[0, 1]` that the cohomology and
base change argument for families of curves needs.

## Main results

* `Stacks.TwoTermComplex.finrank_residueField_tensor`: the fibre dimension of a finite
  projective module is its rank at the stalk.
* `Stacks.TwoTermComplex.finrank_ker_sub_finrank_coker`: the fibre Euler characteristic.
* `Stacks.TwoTermComplex.isLocallyConstant_fibreEuler`.
* `Stacks.TwoTermComplex.isOpen_setOf_coker_fibre_trivial_and_finrank_ker_eq`.
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace Stacks.TwoTermComplex

variable {R : Type u} [CommRing R]

/-- The fibre `κ(p) ⊗ M` of a module at a point of the spectrum. -/
abbrev fibre (p : PrimeSpectrum R) (M : Type u) [AddCommGroup M] [Module R M] : Type u :=
  p.asIdeal.ResidueField ⊗[R] M

/-- **The fibre dimension of a finite projective module is its rank at the stalk.** -/
theorem finrank_residueField_tensor (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField (fibre p M) = Module.rankAtStalk M p := by
  let Rp := Localization.AtPrime p.asIdeal
  let κ := p.asIdeal.ResidueField
  have : Module.Free Rp (Rp ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  rw [(AlgebraTensorModule.cancelBaseChange R Rp κ κ M).symm.finrank_eq,
    Module.finrank_baseChange, Module.rankAtStalk_eq_finrank_tensorProduct]

/-- The fibre rank of a finite projective module is locally constant. -/
theorem isLocallyConstant_finrank_fibre (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField (fibre p M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  simp_rw [finrank_residueField_tensor]
  exact Module.isLocallyConstant_rankAtStalk

variable {K₀ K₁ : Type u} [AddCommGroup K₀] [AddCommGroup K₁] [Module R K₀] [Module R K₁]
  (δ : K₀ →ₗ[R] K₁)

/-- The difference of the ranks of two finite projective modules is locally constant. -/
theorem isLocallyConstant_rankAtStalk_sub [Module.Finite R K₀] [Module.Projective R K₀]
    [Module.Finite R K₁] [Module.Projective R K₁] :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      (Module.rankAtStalk K₀ p : ℤ) - Module.rankAtStalk K₁ p := by
  simp_rw [← finrank_residueField_tensor]
  exact ((isLocallyConstant_finrank_fibre K₀).comp _).sub
    ((isLocallyConstant_finrank_fibre K₁).comp _)

/-- The fibre of `δ` at `p`. -/
abbrev fibreMap (p : PrimeSpectrum R) : fibre p K₀ →ₗ[p.asIdeal.ResidueField] fibre p K₁ :=
  δ.baseChange p.asIdeal.ResidueField

/-- **The fibre Euler characteristic of a two-term complex of finite projective modules** is the
difference of the ranks of its terms. -/
theorem finrank_ker_sub_finrank_coker [Module.Finite R K₀] [Module.Projective R K₀]
    [Module.Finite R K₁] [Module.Projective R K₁] (p : PrimeSpectrum R) :
    (Module.finrank p.asIdeal.ResidueField (LinearMap.ker (fibreMap δ p)) : ℤ) -
        Module.finrank p.asIdeal.ResidueField
          (fibre p K₁ ⧸ LinearMap.range (fibreMap δ p)) =
      Module.rankAtStalk K₀ p - Module.rankAtStalk K₁ p := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (fibreMap δ p)
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (fibreMap δ p))
  rw [← finrank_residueField_tensor K₀ p, ← finrank_residueField_tensor K₁ p]
  omega

/-- The fibre Euler characteristic is locally constant. -/
@[ega "III 7.9.3" "special case", ega "III 7.9.5" "special case"]
theorem isLocallyConstant_fibreEuler [Module.Finite R K₀] [Module.Projective R K₀]
    [Module.Finite R K₁] [Module.Projective R K₁] :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      (Module.finrank p.asIdeal.ResidueField (LinearMap.ker (fibreMap δ p)) : ℤ) -
        Module.finrank p.asIdeal.ResidueField
          (fibre p K₁ ⧸ LinearMap.range (fibreMap δ p)) := by
  simp_rw [finrank_ker_sub_finrank_coker]
  exact isLocallyConstant_rankAtStalk_sub

/-- **The fibre of `δ` is onto exactly away from the support of the cokernel of `δ`**: by right
exactness of the tensor product, the cokernel of `δ(p)` is the fibre of the cokernel of `δ`, and a
finite module has nonzero fibre exactly on its support. -/
theorem surjective_fibreMap_iff [Module.Finite R K₁] (p : PrimeSpectrum R) :
    Function.Surjective (fibreMap δ p) ↔ p ∉ Module.support R (K₁ ⧸ LinearMap.range δ) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
  let κ := p.asIdeal.ResidueField
  let q := (LinearMap.range δ).mkQ
  have hex : Function.Exact (δ.lTensor κ) (q.lTensor κ) :=
    lTensor_exact κ (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)
  have hq : Function.Surjective (q.lTensor κ) :=
    LinearMap.lTensor_surjective κ (Submodule.mkQ_surjective _)
  rw [show ⇑(fibreMap δ p) = ⇑(δ.lTensor κ) from LinearMap.baseChange_eq_ltensor δ]
  refine ⟨fun hs => ⟨fun a b => ?_⟩, fun _ y => (hex y).mp (Subsingleton.elim _ _)⟩
  obtain ⟨a, rfl⟩ := hq a
  obtain ⟨b, rfl⟩ := hq b
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  rw [hex.apply_apply_eq_zero, hex.apply_apply_eq_zero]

/-- **The locus where the fibre of `δ` is onto is open.** -/
theorem isOpen_setOf_surjective_fibreMap [Module.Finite R K₁] :
    IsOpen {p : PrimeSpectrum R | Function.Surjective (fibreMap δ p)} := by
  simp_rw [surjective_fibreMap_iff]
  exact Module.isClosed_support.isOpen_compl

/-- **If every fibre of `δ` is onto, `δ` is onto.** -/
theorem surjective_of_forall_surjective_fibreMap [Module.Finite R K₁]
    (h : ∀ p : PrimeSpectrum R, Function.Surjective (fibreMap δ p)) : Function.Surjective δ := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact Module.support_eq_empty_iff.mp
    (Set.eq_empty_of_forall_notMem fun p => (surjective_fibreMap_iff δ p).mp (h p))

/-- On the locus where the fibre of `δ` is onto, the dimension of its kernel is the difference of
the ranks. -/
theorem finrank_ker_fibreMap_of_surjective [Module.Finite R K₀] [Module.Projective R K₀]
    [Module.Finite R K₁] [Module.Projective R K₁] (p : PrimeSpectrum R)
    (hp : Function.Surjective (fibreMap δ p)) :
    (Module.finrank p.asIdeal.ResidueField (LinearMap.ker (fibreMap δ p)) : ℤ) =
      Module.rankAtStalk K₀ p - Module.rankAtStalk K₁ p := by
  have h := finrank_ker_sub_finrank_coker δ p
  have : Subsingleton (fibre p K₁ ⧸ LinearMap.range (fibreMap δ p)) := by
    rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  rw [Module.finrank_zero_of_subsingleton (M := fibre p K₁ ⧸ _)] at h
  simpa using h

/-- **The locus where the fibre of `δ` is onto with kernel of dimension `r` is open.** -/
theorem isOpen_setOf_surjective_fibreMap_and_finrank_ker_eq [Module.Finite R K₀]
    [Module.Projective R K₀] [Module.Finite R K₁] [Module.Projective R K₁] (r : ℕ) :
    IsOpen {p : PrimeSpectrum R | Function.Surjective (fibreMap δ p) ∧
      Module.finrank p.asIdeal.ResidueField (LinearMap.ker (fibreMap δ p)) = r} := by
  have : {p : PrimeSpectrum R | Function.Surjective (fibreMap δ p) ∧
      Module.finrank p.asIdeal.ResidueField (LinearMap.ker (fibreMap δ p)) = r} =
      {p | Function.Surjective (fibreMap δ p)} ∩
        {p | (Module.rankAtStalk K₀ p : ℤ) - Module.rankAtStalk K₁ p = r} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    refine and_congr_right fun hs => ?_
    rw [← finrank_ker_fibreMap_of_surjective δ p hs, Nat.cast_inj]
  rw [this]
  exact (isOpen_setOf_surjective_fibreMap δ).inter
    (isLocallyConstant_rankAtStalk_sub.isOpen_fiber _)

end Stacks.TwoTermComplex
