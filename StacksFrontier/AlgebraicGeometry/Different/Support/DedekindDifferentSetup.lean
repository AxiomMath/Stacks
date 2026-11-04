module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Contraction

/-!
# The complementary module and the Dedekind different

Let `A → B` be a finite map from a Noetherian ring which carries every nonzerodivisor of `A` to
a nonzerodivisor of `B`. Writing `Q(A)` for the total quotient ring of `A` and assuming the
generic fibre `B ⊗[A] Q(A)` étale over `Q(A)`, the trace pairing of the generic fibre defines
the *complementary module* of `B/A`, consisting of the elements whose trace pairing against `B`
takes values in `A`. The *Dedekind different* is the module of multipliers carrying the
complementary module back into `B`.

## Main definitions

* `Stacks.Discriminant.DedekindDifferentSetup` packages the hypotheses on `A → B` and its
  generic fibre.
* `Stacks.Discriminant.DedekindDifferentSetup.trace` is the finite-projective trace of the
  generic fibre.
* `Stacks.Discriminant.DedekindDifferentSetup.complementaryModule` is the submodule of elements
  whose trace pairing with `B` takes values in `A`.
* `Stacks.Discriminant.DedekindDifferentSetup.dedekindDifferent` is the submodule of multipliers
  carrying the complementary module into `B`.

## Main results

* `Stacks.Discriminant.DedekindDifferentSetup.mem_complementaryModule` characterizes membership
  in the complementary module by the trace condition.
* `Stacks.Discriminant.DedekindDifferentSetup.mem_dedekindDifferent` characterizes membership in
  the Dedekind different by the multiplier condition.

## Implementation notes

The total quotient ring is Mathlib's `FractionRing A`. Both occurrences of `A` and `B` in the
defining conditions mean their canonical images in the appropriate localization or tensor
product, and are therefore expressed as ranges of algebra maps. The right-algebra structure on
`B ⊗[A] FractionRing A` is the canonical map from the second tensor factor. Since a finite étale
algebra is finite projective but need not be free of constant rank, its trace is defined by the
canonical duality equivalence rather than by the finite-free-only `Algebra.trace`.

## References

* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
* [Stacks Project, Tag 02C5](https://stacks.math.columbia.edu/tag/02C5)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

/-- The standing hypotheses for the Dedekind different of a finite ring map `A → B`.
The generic fibre is the canonical tensor product `B ⊗[A] FractionRing A`. -/
class DedekindDifferentSetup (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] where
  /-- The base ring is Noetherian. -/
  [isNoetherianRing : IsNoetherianRing A]
  /-- The algebra is finite as a module over the base. -/
  [finite : Module.Finite A B]
  /-- Nonzerodivisors of `A` remain nonzerodivisors in `B`. -/
  maps_nonZeroDivisors : ∀ a : A, a ∈ nonZeroDivisors A →
    algebraMap A B a ∈ nonZeroDivisors B
  /-- The generic fibre is étale over the total quotient ring. -/
  [etaleGenericFiber :
    (letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
        Algebra.TensorProduct.rightAlgebra;
      Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A))]

namespace DedekindDifferentSetup

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The trace of the finite projective generic fibre `B ⊗[A] Q(A)` over `Q(A)`.
It is the categorical trace obtained by contracting the tensor representing left
multiplication. -/
noncomputable def trace (setup : DedekindDifferentSetup A B) :
    (letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
        Algebra.TensorProduct.rightAlgebra;
      (B ⊗[A] FractionRing A) →ₗ[FractionRing A] FractionRing A) := by
  letI := setup.finite
  letI := Algebra.TensorProduct.rightAlgebra
    (R := A) (A := B) (B := FractionRing A)
  letI := setup.etaleGenericFiber
  let K := FractionRing A
  let L := B ⊗[A] FractionRing A
  letI : Module.Finite K (K ⊗[A] B) := Module.Finite.base_change A K B
  let e : (K ⊗[A] B) ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  letI : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  letI : Module.Flat K L := Algebra.Smooth.flat K L
  letI : Module.FinitePresentation K L :=
    Module.FinitePresentation.of_finite_of_finitePresentation K L
  letI : Module.Projective K L := Module.Flat.projective_of_finitePresentation
  exact (contractLeft K L ∘ₗ
    (dualTensorHomEquiv K L L).symm.toLinearMap).comp (Algebra.lmul K L).toLinearMap

/-- The complementary module `{x ∈ B ⊗[A] Q(A) | Tr(bx) ∈ A for every b ∈ B}`. -/
noncomputable def complementaryModule (setup : DedekindDifferentSetup A B) :
    Submodule B (B ⊗[A] FractionRing A) := by
  letI := Algebra.TensorProduct.rightAlgebra
    (R := A) (A := B) (B := FractionRing A)
  let L := B ⊗[A] FractionRing A
  let K := FractionRing A
  let tr : L →ₗ[K] K := setup.trace
  let iA : A →+* K := algebraMap A K
  let iB : B →+* L := algebraMap B L
  refine
    { carrier := {x | ∀ b : B, tr (iB b * x) ∈ Set.range iA}
      zero_mem' := fun b => ⟨0, by simp [tr, iA]⟩
      add_mem' := fun hx hy b => by
        obtain ⟨a, ha⟩ := hx b
        obtain ⟨a', ha'⟩ := hy b
        refine ⟨a + a', ?_⟩
        rw [mul_add, tr.map_add, ← ha, ← ha']
        exact map_add iA a a'
      smul_mem' := fun c x hx b => by
        obtain ⟨a, ha⟩ := hx (b * c)
        refine ⟨a, ?_⟩
        rw [show c • x = iB c * x by
          exact Algebra.smul_def c x]
        change iA a = tr (iB b * (iB c * x))
        rw [← mul_assoc, ← map_mul]
        exact ha }

/-- An element lies in the complementary module exactly when its trace pairing with every
element of `B` belongs to the canonical image of `A` in its total quotient ring. -/
@[simp]
theorem mem_complementaryModule (setup : DedekindDifferentSetup A B)
    (x : B ⊗[A] FractionRing A) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    x ∈ setup.complementaryModule ↔
      ∀ b : B, setup.trace (algebraMap B (B ⊗[A] FractionRing A) b * x) ∈
        Set.range (algebraMap A (FractionRing A)) := by
  rfl

/-- The Dedekind different, consisting of the elements of the generic fibre which
carry the complementary module into the canonical image of `B`. -/
noncomputable def dedekindDifferent (setup : DedekindDifferentSetup A B) :
    Submodule B (B ⊗[A] FractionRing A) := by
  letI := Algebra.TensorProduct.rightAlgebra
    (R := A) (A := B) (B := FractionRing A)
  let L := B ⊗[A] FractionRing A
  let iB : B →+* L := algebraMap B L
  refine
    { carrier := {x | ∀ y ∈ setup.complementaryModule, x * y ∈ Set.range iB}
      zero_mem' := fun y _ => ⟨0, by simp [iB]⟩
      add_mem' := fun hx hz y hy => by
        obtain ⟨b, hb⟩ := hx y hy
        obtain ⟨c, hc⟩ := hz y hy
        refine ⟨b + c, ?_⟩
        rw [map_add, add_mul, ← hb, ← hc]
      smul_mem' := fun b x hx y hy => by
        obtain ⟨c, hc⟩ := hx y hy
        refine ⟨b * c, ?_⟩
        rw [show b • x = iB b * x by
          exact Algebra.smul_def b x]
        rw [map_mul, mul_assoc, ← hc] }

/-- An element lies in the Dedekind different exactly when multiplication by it carries the
complementary module into the canonical image of `B` in the generic fibre. -/
@[simp]
theorem mem_dedekindDifferent (setup : DedekindDifferentSetup A B)
    (x : B ⊗[A] FractionRing A) :
    x ∈ setup.dedekindDifferent ↔
      ∀ y ∈ setup.complementaryModule,
        x * y ∈ Set.range (algebraMap B (B ⊗[A] FractionRing A)) := by
  rfl

end DedekindDifferentSetup

end Stacks.Discriminant
