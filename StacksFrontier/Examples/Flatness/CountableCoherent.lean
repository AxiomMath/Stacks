module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksFrontier.RingTheory.Coherent.Flat

/-!
# Countable modules, finiteness and coherence

Over a countable ring, finiteness properties of countable modules and coherence of the ring
itself are all detected by one countable product.

For a countable module `M` over a commutative ring `R`, finite generation of `M` is equivalent
to surjectivity of the canonical comparison map `M ⊗[R] R^ℕ → M^ℕ`, and — when `R` is countable
as well — finite presentation of `M` is equivalent to bijectivity of that map. Combining the two
with the ideal-theoretic characterization of coherence shows that a countable commutative ring
is coherent exactly when `R^ℕ` is a flat `R`-module.

The proofs are the ones in the source. Surjectivity of the comparison map produces, from a
surjection `ℕ → M`, a finite generating family by expanding one element of `M ⊗[R] R^ℕ` as a
finite sum of pure tensors. Finite presentation is obtained from the general tensor-product
criterion for finite presentation after transporting along the equivalence `ULift ℕ ≃ ℕ`, and in
the converse direction by exhibiting the kernel of a finite free presentation as a finitely
generated module, again using the comparison map. Coherence then follows from the
characterization of coherence by finite presentation of finitely generated ideals.

## Main results

* `Stacks.Examples.finite_iff_piScalarRightHom_nat_surjective`: finite generation of a countable
  module is surjectivity of `M ⊗[R] R^ℕ → M^ℕ`.
* `Stacks.Examples.finitePresentation_iff_piScalarRightHom_nat_bijective`: finite presentation
  of a countable module over a countable ring is bijectivity of `M ⊗[R] R^ℕ → M^ℕ`.
* `Stacks.Examples.isCoherentRing_iff_flat_pi_nat`: a countable commutative ring is coherent if
  and only if `ℕ → R` is flat over `R`.

## Implementation notes

The source's canonical map `M ⊗[R] R^ℕ → M^ℕ` is `TensorProduct.piScalarRightHom R R M ℕ`; on a
pure tensor it sends `m ⊗ a` to the family `n ↦ a n • m`. "Is an isomorphism" is expressed as
bijectivity of the underlying function, which is the form the general tensor-product criterion
for finite presentation takes. The product `R^ℕ` is the function type `ℕ → R` with its pointwise
module structure, and countability of the underlying set is the typeclass `Countable`.

## References

* [Stacks Project, Tag 0AL9](https://stacks.math.columbia.edu/tag/0AL9)
* [Stacks Project, Tag 0ALA](https://stacks.math.columbia.edu/tag/0ALA)
* [Stacks Project, Tag 0ALB](https://stacks.math.columbia.edu/tag/0ALB)
-/

@[expose] public section

universe u v

namespace Stacks.Examples

section Finite

variable (R : Type u) [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M] [Countable M]

/-- A countable module is finitely generated if and only if the canonical map
`M ⊗[R] (ℕ → R) → (ℕ → M)` is surjective. -/
@[stacks 0AL9]
theorem finite_iff_piScalarRightHom_nat_surjective :
    Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) := by
  classical
  constructor
  · intro h
    obtain ⟨n, x, hx⟩ := @Module.Finite.exists_fin R M _ _ _ h
    intro f
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun R).mp
      (hx.ge (Submodule.mem_top : f i ∈ ⊤))
    refine ⟨∑ j, x j ⊗ₜ[R] (fun i => c i j), ?_⟩
    ext i
    simpa [TensorProduct.piScalarRightHom_tmul] using hc i
  · intro h
    obtain ⟨enum, henum⟩ := exists_surjective_nat M
    obtain ⟨t, ht⟩ := h enum
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
    refine Module.Finite.of_fg_top ⟨s.image Prod.fst, Submodule.eq_top_iff'.2 fun m => ?_⟩
    obtain ⟨n, rfl⟩ := henum m
    have hmap := congrFun ht n
    rw [hs] at hmap
    simp only [map_sum, TensorProduct.piScalarRightHom_tmul, Finset.sum_apply] at hmap
    rw [← hmap]
    exact Submodule.sum_mem _ (fun p hp => Submodule.smul_mem _ _ <|
      Submodule.subset_span (Finset.mem_image_of_mem Prod.fst hp))

end Finite

section FinitePresentation

variable (R : Type u) [CommRing R] [Countable R] (M : Type v)
  [AddCommGroup M] [Module R M] [Countable M]

/-- A countable module over a countable ring is finitely presented if and only if the canonical
map `M ⊗[R] (ℕ → R) → (ℕ → M)` is bijective. -/
@[stacks 0ALA]
theorem finitePresentation_iff_piScalarRightHom_nat_bijective :
    Module.FinitePresentation R M ↔
      Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ) := by
  classical
  constructor
  · intro hfp
    let A := ULift.{v} ℕ
    have hbijEvery :=
      ((Module.FinitePresentation.tfae_piRightHom_bijective R M).out 1 4).mp hfp
    have hbijA : Function.Bijective (TensorProduct.piScalarRightHom R R M A) := hbijEvery A
    let e : A ≃ ℕ := Equiv.ulift
    let eM : (A → M) ≃ₗ[R] (ℕ → M) :=
      LinearEquiv.piCongrLeft R (fun _ : ℕ => M) e
    let sourceEquiv : TensorProduct R M (A → R) ≃ₗ[R] TensorProduct R M (ℕ → R) :=
      TensorProduct.congr (LinearEquiv.refl R M)
        (LinearEquiv.piCongrLeft R (fun _ : ℕ => R) e)
    have hnatural :
        (TensorProduct.piScalarRightHom R R M ℕ).comp
            sourceEquiv.toLinearMap =
          eM.toLinearMap.comp
            (TensorProduct.piScalarRightHom R R M A) := by
      refine TensorProduct.ext' fun x a => ?_
      ext n
      simp [sourceEquiv, eM, e, LinearEquiv.piCongrLeft, Function.comp_apply]
    apply (sourceEquiv.toEquiv.bijective_comp _).mp
    change Function.Bijective (((TensorProduct.piScalarRightHom R R M ℕ).comp
      sourceEquiv.toLinearMap) : _ → _)
    rw [hnatural]
    exact eM.bijective.comp hbijA
  · intro hbij
    have : Module.Finite R M :=
      (finite_iff_piScalarRightHom_nat_surjective R M).2 hbij.2
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    let P := (Fin n → R)
    let K := LinearMap.ker f
    have : Countable P := inferInstance
    have : Countable K := inferInstance
    have hPsurj : Function.Surjective (TensorProduct.piScalarRightHom R R P ℕ) :=
      (finite_iff_piScalarRightHom_nat_surjective R P).1 inferInstance
    have hKsurj : Function.Surjective (TensorProduct.piScalarRightHom R R K ℕ) := by
      intro y
      let yP : ℕ → P := fun i => f.ker.subtype (y i)
      obtain ⟨t, ht⟩ := hPsurj yP
      have hz : LinearMap.rTensor (ℕ → R) f t = 0 := by
        apply hbij.1
        ext i
        rw [map_zero, TensorProduct.piScalarRightHom_rTensor_apply, ht]
        exact (y i).property
      obtain ⟨s, hs⟩ := (rTensor_exact (ℕ → R)
        (LinearMap.exact_subtype_ker_map f) hf t).mp hz
      refine ⟨s, funext fun i => ?_⟩
      apply Subtype.ext
      have hi := congrFun ht i
      rw [← hs, TensorProduct.piScalarRightHom_rTensor_apply] at hi
      simpa [yP] using hi
    exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp
      ((finite_iff_piScalarRightHom_nat_surjective R K).2 hKsurj))

end FinitePresentation

/-- A countable commutative ring is coherent if and only if its countable product, as a module
over itself, is flat. -/
@[stacks 0ALB]
theorem isCoherentRing_iff_flat_pi_nat (R : Type u) [CommRing R] [Countable R] :
    IsCoherentRing R ↔ Module.Flat R (ℕ → R) := by
  constructor
  · intro h
    have hiff : IsCoherentRing R ↔ ∀ A : Type u, Module.Flat R (A → R) :=
      (IsCoherentRing.tfae_flat_pi R).out 1 3
    have : Module.Flat R (ULift.{u} ℕ → R) := hiff.mp h _
    exact Module.Flat.of_linearEquiv (LinearEquiv.piCongrLeft R (fun _ : ℕ => R) Equiv.ulift).symm
  · intro h
    refine (isCoherentRing_iff_forall_fg_ideal_finitePresentation R).2 fun I hI => ?_
    apply (finitePresentation_iff_piScalarRightHom_nat_bijective R I).2
    refine ⟨?_, (finite_iff_piScalarRightHom_nat_surjective R I).mp
      (Module.Finite.iff_fg.mpr hI)⟩
    intro x y hxy
    apply (Module.Flat.iff_rTensor_injective.mp h hI)
    apply ((finitePresentation_iff_piScalarRightHom_nat_bijective R R).mp inferInstance).1
    funext n
    rw [TensorProduct.piScalarRightHom_rTensor_apply, TensorProduct.piScalarRightHom_rTensor_apply]
    exact congrArg (fun z : I => (z : R)) (congrFun hxy n)

end Stacks.Examples

end
