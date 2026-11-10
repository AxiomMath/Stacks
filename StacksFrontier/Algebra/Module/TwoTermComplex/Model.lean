module

public import StacksFrontier.Algebra.Module.TwoTermComplex.Noetherian
public import StacksFrontier.Algebra.Module.TwoTermComplex.FibreRanks
public import Mathlib.RingTheory.TensorProduct.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two-term complexes with a finite projective model

A map `d : C₀ ⟶ C₁` of `R`-modules *has a finite projective model* when there is a comparison
square (`Stacks.TwoTermComplex.IsComparisonSquare`) into it from a map `δ : K₀ ⟶ K₁` of finite
projective modules. Then `d` and `δ` have the same kernel and cokernel, and when `C₁` is flat the
same holds after every base change; so every statement about the fibres of `δ` is a statement
about the fibres of `d`.

Over a Noetherian ring a map of flat modules with finite kernel and cokernel has a finite
projective model (`Stacks.TwoTermComplex.exists_finsuppModel`), and the property is stable under
base change.

## Main definitions

* `Stacks.TwoTermComplex.HasFiniteProjectiveModel`.

## Main results

* `Stacks.TwoTermComplex.HasFiniteProjectiveModel.of_isNoetherianRing`.
* `Stacks.TwoTermComplex.HasFiniteProjectiveModel.baseChange` and `.of_linearEquiv`.
* `Stacks.TwoTermComplex.HasFiniteProjectiveModel.isOpen_setOf_surjective_fibre`,
  `.isOpen_setOf_surjective_fibre_and_finrank_ker_eq`, `.isLocallyConstant_fibreEuler`,
  `.surjective_of_forall`.
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace Stacks.TwoTermComplex

variable {R : Type u} [CommRing R] {C₀ C₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁]
  [Module R C₀] [Module R C₁]

/-- `d` has a finite projective model: a comparison square into it from a map of finite projective
modules. -/
def HasFiniteProjectiveModel (d : C₀ →ₗ[R] C₁) : Prop :=
  ∃ (K₀ K₁ : Type u) (_ : AddCommGroup K₀) (_ : AddCommGroup K₁) (_ : Module R K₀)
    (_ : Module R K₁) (_ : Module.Finite R K₀) (_ : Module.Projective R K₀)
    (_ : Module.Finite R K₁) (_ : Module.Projective R K₁) (δ : K₀ →ₗ[R] K₁)
    (φ₀ : K₀ →ₗ[R] C₀) (φ₁ : K₁ →ₗ[R] C₁), IsComparisonSquare δ d φ₀ φ₁

namespace IsComparisonSquare

variable {K₀ K₁ : Type u} [AddCommGroup K₀] [AddCommGroup K₁] [Module R K₀] [Module R K₁]
  {δ : K₀ →ₗ[R] K₁} {d : C₀ →ₗ[R] C₁} {φ₀ : K₀ →ₗ[R] C₀} {φ₁ : K₁ →ₗ[R] C₁}

/-- A comparison square can be transported along isomorphisms of its target complex. -/
theorem of_linearEquiv (h : IsComparisonSquare δ d φ₀ φ₁) {D₀ D₁ : Type u} [AddCommGroup D₀]
    [AddCommGroup D₁] [Module R D₀] [Module R D₁] (e₀ : C₀ ≃ₗ[R] D₀) (e₁ : C₁ ≃ₗ[R] D₁)
    (d' : D₀ →ₗ[R] D₁) (hd : e₁.toLinearMap ∘ₗ d = d' ∘ₗ e₀.toLinearMap) :
    IsComparisonSquare δ d' (e₀.toLinearMap ∘ₗ φ₀) (e₁.toLinearMap ∘ₗ φ₁) := by
  have hd' (x : C₀) : e₁ (d x) = d' (e₀ x) := LinearMap.congr_fun hd x
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp [← hd', h.comm_apply]
  · intro x y hxy
    apply h.injective
    have h1 : δ x = δ y := congrArg Prod.fst hxy
    have h2 : e₀ (φ₀ x) = e₀ (φ₀ y) := congrArg Prod.snd hxy
    rw [EmbeddingLike.apply_eq_iff_eq] at h2
    simp [h1, h2]
  · intro ⟨k, c⟩
    obtain ⟨c, rfl⟩ := e₀.surjective c
    have := h.exact (k, c)
    simp only [LinearMap.coprod_apply, LinearMap.neg_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, Set.mem_range, LinearMap.prod_apply] at this ⊢
    rw [← hd', ← map_neg, ← map_add, LinearEquiv.map_eq_zero_iff, this]
    simp
  · intro y
    obtain ⟨y, rfl⟩ := e₁.surjective y
    obtain ⟨⟨k, c⟩, hkc⟩ := h.surjective y
    refine ⟨(k, e₀ c), ?_⟩
    simp only [LinearMap.coprod_apply, LinearMap.neg_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply] at hkc ⊢
    rw [← hd', ← map_neg, ← map_add, hkc]

end IsComparisonSquare

namespace HasFiniteProjectiveModel

variable {d : C₀ →ₗ[R] C₁}

/-- **Over a Noetherian ring a map of flat modules with finite kernel and cokernel has a finite
projective model.** -/
theorem of_isNoetherianRing [IsNoetherianRing R] [Module.Flat R C₀] [Module.Flat R C₁]
    (hker : Module.Finite R (LinearMap.ker d))
    (hcoker : Module.Finite R (C₁ ⧸ LinearMap.range d)) : HasFiniteProjectiveModel d := by
  obtain ⟨n, c, hc⟩ := exists_finsuppModel d hcoker
  have := FinsuppModel.finite_K₀ d c hker
  have := FinsuppModel.projective_K₀ d c hc hker
  exact ⟨_, _, _, _, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, _,
    FinsuppModel.isComparisonSquare d c hc⟩

/-- A finite projective model transports along isomorphisms of the complex. -/
theorem of_linearEquiv (h : HasFiniteProjectiveModel d) {D₀ D₁ : Type u} [AddCommGroup D₀]
    [AddCommGroup D₁] [Module R D₀] [Module R D₁] (e₀ : C₀ ≃ₗ[R] D₀) (e₁ : C₁ ≃ₗ[R] D₁)
    (d' : D₀ →ₗ[R] D₁) (hd : e₁.toLinearMap ∘ₗ d = d' ∘ₗ e₀.toLinearMap) :
    HasFiniteProjectiveModel d' := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  exact ⟨K₀, K₁, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, δ, _, _, hsq.of_linearEquiv e₀ e₁ d' hd⟩

/-- **A finite projective model of a complex with flat second term base changes.** -/
theorem baseChange (h : HasFiniteProjectiveModel d) [Module.Flat R C₁] (B : Type u) [CommRing B]
    [Algebra R B] : HasFiniteProjectiveModel (d.baseChange B) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  exact ⟨B ⊗[R] K₀, B ⊗[R] K₁, _, _, _, _, inferInstance, inferInstance, inferInstance,
    inferInstance, δ.baseChange B, _, _, hsq.baseChange B⟩

end HasFiniteProjectiveModel

/-! ### Fibres -/

namespace IsComparisonSquare

variable {K₀ K₁ : Type u} [AddCommGroup K₀] [AddCommGroup K₁] [Module R K₀] [Module R K₁]
  {δ : K₀ →ₗ[R] K₁} {d : C₀ →ₗ[R] C₁} {φ₀ : K₀ →ₗ[R] C₀} {φ₁ : K₁ →ₗ[R] C₁}

/-- In a comparison square, `δ` is surjective if and only if `d` is surjective. -/
theorem surjective_iff (h : IsComparisonSquare δ d φ₀ φ₁) :
    Function.Surjective δ ↔ Function.Surjective d := by
  rw [← LinearMap.range_eq_top, ← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
    ← Submodule.Quotient.subsingleton_iff]
  exact h.cokerEquiv.toEquiv.subsingleton_congr

end IsComparisonSquare

namespace HasFiniteProjectiveModel

variable {d : C₀ →ₗ[R] C₁} [Module.Flat R C₁]

/-- **The locus where the fibre of `d` is onto is open.** -/
theorem isOpen_setOf_surjective_fibre (h : HasFiniteProjectiveModel d) :
    IsOpen {p : PrimeSpectrum R | Function.Surjective (d.baseChange p.asIdeal.ResidueField)} := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  convert isOpen_setOf_surjective_fibreMap δ using 3 with p
  exact (hsq.baseChange p.asIdeal.ResidueField).surjective_iff.symm

/-- **The locus where the fibre of `d` is onto with kernel of dimension `r` is open.** -/
theorem isOpen_setOf_surjective_fibre_and_finrank_ker_eq (h : HasFiniteProjectiveModel d)
    (r : ℕ) :
    IsOpen {p : PrimeSpectrum R | Function.Surjective (d.baseChange p.asIdeal.ResidueField) ∧
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker (d.baseChange p.asIdeal.ResidueField)) = r} := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  convert isOpen_setOf_surjective_fibreMap_and_finrank_ker_eq δ r using 3 with p
  have hp := hsq.baseChange p.asIdeal.ResidueField
  rw [← hp.surjective_iff, ← hp.kerEquiv.finrank_eq]

/-- The kernel of a fibre of `d` is finite dimensional. -/
theorem finiteDimensional_ker_fibre (h : HasFiniteProjectiveModel d) (p : PrimeSpectrum R) :
    FiniteDimensional p.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange p.asIdeal.ResidueField)) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  exact Module.Finite.equiv (hsq.baseChange p.asIdeal.ResidueField).kerEquiv

/-- The cokernel of a fibre of `d` is finite dimensional. -/
theorem finiteDimensional_coker_fibre (h : HasFiniteProjectiveModel d) (p : PrimeSpectrum R) :
    FiniteDimensional p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] C₁ ⧸ LinearMap.range (d.baseChange p.asIdeal.ResidueField)) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  exact Module.Finite.equiv (hsq.baseChange p.asIdeal.ResidueField).cokerEquiv

/-- **The fibre Euler characteristic of `d` is locally constant.** -/
@[ega "III 7.9.3" "special case"]
theorem isLocallyConstant_fibreEuler (h : HasFiniteProjectiveModel d) :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      (Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange p.asIdeal.ResidueField)) : ℤ) -
        Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] C₁ ⧸
            LinearMap.range (d.baseChange p.asIdeal.ResidueField)) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  convert Stacks.TwoTermComplex.isLocallyConstant_fibreEuler δ using 2 with p
  have hp := hsq.baseChange p.asIdeal.ResidueField
  rw [← hp.kerEquiv.finrank_eq, ← hp.cokerEquiv.finrank_eq]

/-- **If every fibre of `d` is onto, `d` is onto.** -/
theorem surjective_of_forall (h : HasFiniteProjectiveModel d)
    (hp : ∀ p : PrimeSpectrum R, Function.Surjective (d.baseChange p.asIdeal.ResidueField)) :
    Function.Surjective d := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  exact hsq.surjective_iff.mp (surjective_of_forall_surjective_fibreMap δ fun p =>
    (hsq.baseChange p.asIdeal.ResidueField).surjective_iff.mpr (hp p))

omit [Module.Flat R C₁] in
/-- **If `d` is onto, its kernel is finite projective.** -/
theorem projective_ker (h : HasFiniteProjectiveModel d) (hd : Function.Surjective d) :
    Module.Finite R (LinearMap.ker d) ∧ Module.Projective R (LinearMap.ker d) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ := h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property δ LinearMap.id (hsq.surjective_iff.mpr hd)
  have hs' (y : K₁) : δ (s y) = y := LinearMap.congr_fun hs y
  let r : K₀ →ₗ[R] LinearMap.ker δ := (LinearMap.id - s ∘ₗ δ).codRestrict _ fun x => by
    simp [hs']
  have hK : Module.Projective R (LinearMap.ker δ) := by
    refine Module.Projective.of_split (LinearMap.ker δ).subtype r ?_
    ext ⟨x, hx⟩
    simp [r, LinearMap.mem_ker.mp hx]
  have hKf : Module.Finite R (LinearMap.ker δ) :=
    Module.Finite.of_surjective r fun ⟨x, hx⟩ => ⟨x, by ext; simp [r, LinearMap.mem_ker.mp hx]⟩
  exact ⟨Module.Finite.equiv hsq.kerEquiv, Module.Projective.of_equiv hsq.kerEquiv⟩

end HasFiniteProjectiveModel

end Stacks.TwoTermComplex

namespace Stacks.TwoTermComplex

variable {R : Type u} [CommRing R] {C₀ C₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁]
  [Module R C₀] [Module R C₁]

/-- **The kernel of a surjection onto a flat module commutes with base change**, as an
equivalence of `B`-modules `B ⊗ ker d ≃ ker (B ⊗ d)`. -/
noncomputable def baseChangeKerEquiv [Module.Flat R C₁] (d : C₀ →ₗ[R] C₁)
    (hd : Function.Surjective d) (B : Type u) [CommRing B] [Algebra R B] :
    B ⊗[R] LinearMap.ker d ≃ₗ[B] LinearMap.ker (d.baseChange B) := by
  have hinj : Function.Injective ((LinearMap.ker d).subtype.baseChange B) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_injective_of_exact_of_flat d hd _ (LinearMap.ker d).subtype_injective
      (LinearMap.exact_subtype_ker_map _) B
  have hrange : LinearMap.range ((LinearMap.ker d).subtype.baseChange B) =
      LinearMap.ker (d.baseChange B) := by
    ext x
    have h := (lTensor_exact B (LinearMap.exact_subtype_ker_map d) hd x).symm
    rwa [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor] at h
  exact (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)

/-- `baseChangeKerEquiv` sends `b ⊗ₜ x` to the element `b ⊗ₜ x` of `B ⊗[R] C₀`. -/
theorem baseChangeKerEquiv_tmul [Module.Flat R C₁] (d : C₀ →ₗ[R] C₁)
    (hd : Function.Surjective d) (B : Type u) [CommRing B] [Algebra R B] (b : B)
    (x : LinearMap.ker d) :
    (baseChangeKerEquiv d hd B (b ⊗ₜ x) : B ⊗[R] C₀) = b ⊗ₜ (x : C₀) :=
  rfl

end Stacks.TwoTermComplex
