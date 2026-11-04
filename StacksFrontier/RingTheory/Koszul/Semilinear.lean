module

public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contraction of the exterior algebra under a semilinear base change

Let `σ : R →+* S` be a ring homomorphism, `M` an `R`-module, `N` an `S`-module and
`g : M →ₛₗ[σ] N` a `σ`-semilinear map. Then `ExteriorAlgebra.mapₛₗ σ g` is a ring homomorphism
`⋀(M) ⟶ ⋀(N)`, and this file proves that it intertwines the two contraction operators of
`StacksFrontier.RingTheory.Koszul.Defs` as soon as the two functionals are compatible:
`σ (φ m) = ψ (g m)`.

This is the identity a *sheaf* of Koszul complexes needs. The restriction maps of the presheaf of
sectionwise exterior powers `PresheafOfModules.extPow` are exactly the maps
`ExteriorAlgebra.mapₛₗ` of the restriction maps of the underlying presheaf of modules
(`PresheafOfModules.extPowSections_map`), so the naturality of a sectionwise Koszul differential
in the object of the site *is* this lemma.

## Main results

* `Koszul.mapₛₗ_contraction`: **contraction commutes with a semilinear base change** of the
  exterior algebra, for compatible functionals.
* `Koszul.contraction_mul_of_mem`: the graded Leibniz rule
  `d (x * y) = d x * y + (-1)ⁿ • (x * d y)` for a left factor `x` of exterior degree `n`, written
  for `Koszul.contraction` itself. This is
  `Koszul.HomologicalDifferentialGradedExteriorAlgebra.differential_mul_of_mem` at
  `Koszul.differentialGradedAlgebra`.
* `Koszul.contraction_eq_zero_of_mem_zero`: contraction annihilates exterior degree zero.

## Implementation notes

The induction is `CliffordAlgebra.left_induction`, the same one
`Koszul.HomologicalDifferentialGradedExteriorAlgebra.differential_unique` uses: the three cases
`algebraMap`, `add` and `ι_mul` are precisely the three clauses that pin a left contraction down,
so no spanning argument over `ExteriorAlgebra.ιMulti` and no grading is needed. The base change
enters only through its two defining equations, `ExteriorAlgebra.mapₛₗ_algebraMap` and
`mapₛₗ_ι`, and through the fact that it is a ring homomorphism; its semilinearity is not used.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]

/-- **Contraction commutes with a semilinear base change of the exterior algebra.** If the
functional `ψ` on `N` pulls back along `g` to the functional `φ` on `M`, in the sense that
`σ (φ m) = ψ (g m)`, then `ExteriorAlgebra.mapₛₗ σ g` intertwines contraction by `φ` with
contraction by `ψ`. -/
theorem mapₛₗ_contraction (σ : R →+* S) (g : M →ₛₗ[σ] N)
    (φ : Module.Dual R M) (ψ : Module.Dual S N) (hg : ∀ m : M, σ (φ m) = ψ (g m))
    (a : ExteriorAlgebra R M) :
    ExteriorAlgebra.mapₛₗ σ g (contraction φ a) =
      contraction ψ (ExteriorAlgebra.mapₛₗ σ g a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contraction, CliffordAlgebra.contractLeft_algebraMap, map_zero,
      ExteriorAlgebra.mapₛₗ_algebraMap, contraction,
      CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (map_add _ _ _).symm
  | ι_mul x m hx =>
    rw [contraction, CliffordAlgebra.contractLeft_ι_mul, map_sub, ExteriorAlgebra.mapₛₗ_smul,
      map_mul, ExteriorAlgebra.mapₛₗ_ι, hg, hx, map_mul, ExteriorAlgebra.mapₛₗ_ι,
      contraction, CliffordAlgebra.contractLeft_ι_mul]

/-- **The graded Leibniz rule for contraction**, for a left factor of exterior degree `n`. This
is `Koszul.HomologicalDifferentialGradedExteriorAlgebra.differential_mul_of_mem` read at
`Koszul.differentialGradedAlgebra`, where the differential is `Koszul.contraction`. -/
@[ega "III 1.1.1" "i_f is an antiderivation"]
theorem contraction_mul_of_mem (φ : Module.Dual R M) (n : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) (y : ExteriorAlgebra R M) :
    contraction φ (x * y) =
      contraction φ x * y + ((-1 : R) ^ n) • (x * contraction φ y) :=
  (differentialGradedAlgebra φ).differential_mul_of_mem n hx y

/-- **Contraction annihilates exterior degree zero**: the degree-zero part of the exterior
algebra is the image of the structure map, which contraction kills. -/
theorem contraction_eq_zero_of_mem_zero (φ : Module.Dual R M) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^0 M) : contraction φ x = 0 := by
  rw [show (⋀[R]^0 M) = 1 from pow_zero _, Submodule.mem_one] at hx
  obtain ⟨r, rfl⟩ := hx
  exact CliffordAlgebra.contractLeft_algebraMap _ φ r

end Koszul

end
