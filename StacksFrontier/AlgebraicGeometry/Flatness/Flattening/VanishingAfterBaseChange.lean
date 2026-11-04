module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Flattening a module map

Let `A` be a commutative ring and let `u : M →ₗ[A] N` be a map of `A`-modules. The base
changes of `A` along which `u` becomes zero, respectively along which a surjective `u`
becomes an isomorphism, are cut out by a single ideal of `A`: the base change `A → B` has
the stated property exactly when the ideal maps to `⊥` in `B`.

## Main results

* `Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot`: when the target of `u` is projective,
  an ideal of `A` detects the base changes on which `u` vanishes.
* `Module.exists_ideal_bijective_rTensor_iff_map_eq_bot`: when `u` is surjective and its
  source is projective, an ideal of `A` detects the base changes on which `u` becomes an
  isomorphism.

## Implementation notes

The base change of `u` along `A → B` is `LinearMap.rTensor B u`. A ring map out of the base
ring is presented as an algebra structure, and the assertion that an ideal has zero image
under it is expressed by its mapped ideal being `⊥`. An isomorphism of modules is recorded
by bijectivity of the underlying linear map.

## References

* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
-/

@[expose] public section

namespace Module

universe u v w x

/-- **Stacks Project, Tag 083L.** If the target of a linear map is projective, the base
changes on which the map vanishes are cut out by an ideal of the base ring. -/
@[stacks 083L]
theorem exists_ideal_rTensor_eq_zero_iff_map_eq_bot
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (hN : Module.Projective A N) :
    ∃ I : Ideal A, ∀ (B : Type x) [CommRing B] (φ : A →+* B),
      letI := φ.toAlgebra
      f.rTensor B = 0 ↔ Ideal.map φ I = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def (R := A) (P := N)).mp hN
  refine ⟨Ideal.span (Set.range (fun p : M × N => s (f p.1) p.2)), ?_⟩
  intro B _ φ
  let := φ.toAlgebra
  have hφ : algebraMap A B = φ := rfl
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.span_le, Set.range_subset_iff]
  show f.rTensor B = 0 ↔ ∀ p : M × N, φ ((s (f p.1)) p.2) = 0
  constructor
  · intro hf p
    have ht : (s (f p.1)) ⊗ₜ[A] (1 : B) = 0 := by
      simpa using congrArg (fun t => s.rTensor B t)
        (LinearMap.congr_fun hf (p.1 ⊗ₜ[A] (1 : B)))
    have h := congrArg (fun t : (TensorProduct A (N →₀ A) B) =>
      (TensorProduct.finsuppScalarLeft A B N t) p.2) ht
    simpa [TensorProduct.finsuppScalarLeft_apply_tmul_apply, Algebra.smul_def, hφ] using h
  · intro hc
    have ht (m : M) (b : B) : (s (f m)) ⊗ₜ[A] b = 0 := by
      apply (TensorProduct.finsuppScalarLeft A B N).injective
      ext i
      simp [TensorProduct.finsuppScalarLeft_apply_tmul_apply,
        Algebra.smul_def, hφ, hc (m, i)]
    ext m b
    simpa [LinearMap.rTensor_tmul, hs (f m)] using congrArg
      (fun t : (TensorProduct A (N →₀ A) B) =>
        (Finsupp.linearCombination A (id : N → N)).rTensor B t) (ht m b)

variable (A : Type u) [CommRing A]
variable (M : Type v) [AddCommGroup M] [Module A M]
variable (N : Type w) [AddCommGroup N] [Module A N]

/-- **Stacks Project, Tag 05PE.** A surjection from a projective module has a
flattening ideal: after every base change, the map is an isomorphism exactly
when the image of this ideal vanishes. -/
@[stacks 05PE]
theorem exists_ideal_bijective_rTensor_iff_map_eq_bot
    (u : M →ₗ[A] N) (hu : Function.Surjective u) [Module.Projective A M] :
    ∃ I : Ideal A, ∀ (B : Type*) [CommRing B] [Algebra A B],
      Function.Bijective (u.rTensor B) ↔ Ideal.map (algebraMap A B) I = ⊥ := by
  let _ : AddCommMonoid (LinearMap.ker u) :=
    (LinearMap.ker u).addCommGroup.toAddCommMonoid
  obtain ⟨I, hI⟩ := exists_ideal_rTensor_eq_zero_iff_map_eq_bot (LinearMap.ker u).subtype
    inferInstance
  refine ⟨I, fun B _ _ => ?_⟩
  rw [show Function.Bijective (u.rTensor B) ↔ Function.Injective (u.rTensor B) from
    and_iff_left (LinearMap.rTensor_surjective B hu), ← LinearMap.ker_eq_bot,
    (rTensor_exact B (LinearMap.exact_subtype_ker_map u) hu).linearMap_ker_eq,
    LinearMap.range_eq_bot]
  have hi := hI B (algebraMap A B)
  rwa [show (algebraMap A B).toAlgebra = _ from toAlgebra_algebraMap] at hi

end Module
