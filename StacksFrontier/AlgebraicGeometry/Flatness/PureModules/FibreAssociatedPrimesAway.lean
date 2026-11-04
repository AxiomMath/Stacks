module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange

/-!
# Associated primes of a fibre after an étale base change inverting a chosen element

Let `R → S` be a finitely presented ring map, let `N` be a finitely presented `S`-module and
let `q` be a prime of `S` lying over a prime `p` of `R`. Choose `g ∈ S` as in Tag 0CU6: it lies
outside `q`, and its image in the fibre ring `κ(p) ⊗[R] S` belongs to every associated prime of
the fibre module which is not contained in the extension of `q`. If `B` is an étale algebra over
the fibre ring in which the image of `g` becomes a unit, then every associated prime of the
base-changed fibre module contracts to a prime contained in that extension of `q`.

## Main results

* `Stacks.PureModules.comap_associatedPrime_le_fiberIdeal_of_isUnit` is the key observation of
  Tag 0CU7.

## Implementation notes

The fibre ring is Mathlib's `Ideal.Fiber`, with `p.Fiber S = κ(p) ⊗[R] S`, the fibre module is
the base change `(p.Fiber S) ⊗[S] N` and the extension of `q` is its image under the right
tensor-factor map `Algebra.TensorProduct.includeRight`, exactly as in Tag 0CU6. The source's
étale fibre map `S̄ → S̄'` is kept abstract as an arbitrary étale `p.Fiber S`-algebra `B`, so the
statement applies to any étale base change of the fibre which inverts the chosen element.

## References

* [Stacks Project, Tag 0CU7](https://stacks.math.columbia.edu/tag/0CU7)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.PureModules

/-- Restriction of scalars along `R → S` contracts a prime associated to an `S`-module `X` to a
prime associated to `X` viewed as an `R`-module: the `R`-colon ideal of a witness is the
contraction of its `S`-colon ideal. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
private theorem comap_mem_associatedPrimes_of_scalarTower
    {R S X : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    {q : Ideal S} (hq : q ∈ associatedPrimes S X) :
    q.comap (algebraMap R S) ∈ associatedPrimes R X := by
  obtain ⟨hqp, z, hz⟩ := hq
  refine ⟨hqp.comap _, z, ?_⟩
  have hcolon : (⊥ : Submodule R X).colon {z}
      = ((⊥ : Submodule S X).colon {z}).comap (algebraMap R S) := by
    ext r
    simp [Ideal.mem_comap, Submodule.mem_colon_singleton, algebraMap_smul]
  rw [hcolon, ← Ideal.comap_radical, hz]

/-- **Stacks Project, Tag 0CU7.** With `g ∈ S` chosen as in Tag 0CU6, let `B` be an étale algebra
over the fibre ring `p.Fiber S` in which the image of `g` is a unit. Then every prime of `B`
associated to the base change of the fibre module contracts to a prime of `p.Fiber S` contained
in the extension of `q`.

Indeed, such a contraction is associated to the fibre module itself, because `B` is flat over the
fibre ring and the fibre ring is Noetherian; were it not contained in the extension of `q`, the
choice of `g` would put the image of `g` inside it, contradicting the fact that the image of `g`
in `B` is a unit. -/
@[stacks 0CU7]
theorem comap_associatedPrime_le_fiberIdeal_of_isUnit
    {R S N B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup N] [Module S N]
    [Module.FinitePresentation S N]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [CommRing B] [Algebra (p.Fiber S) B] [Algebra.Etale (p.Fiber S) B]
    (g : S)
    (hg : letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
      g ∉ q ∧
        (∀ r ∈ associatedPrimes (p.Fiber S)
          (TensorProduct S (p.Fiber S) N),
          (¬ r ≤ Ideal.map
            (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom q →
            (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g ∈ r)))
    (hunit : IsUnit ((algebraMap (p.Fiber S) B)
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g))) :
    letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
    ∀ r' ∈ associatedPrimes B
      (TensorProduct (p.Fiber S) B (TensorProduct S (p.Fiber S) N)),
      Ideal.comap (algebraMap (p.Fiber S) B) r' ≤
        Ideal.map
          (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom q := by
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  intro r' hr'
  let A := p.Fiber S
  let M := TensorProduct S A N
  have : IsNoetherianRing A :=
    Algebra.FiniteType.isNoetherianRing p.ResidueField A
  have : Module.Finite A M := Module.Finite.base_change S A N
  have hbase : Ideal.comap (algebraMap A B) r' ∈ associatedPrimes A M :=
    Stacks.AssociatedPrimes.FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat
      (comap_mem_associatedPrimes_of_scalarTower hr')
  by_contra hn
  have : r'.IsPrime := hr'.1
  exact (r'.notMem_of_isUnit hunit)
    (hg.2 (Ideal.comap (algebraMap A B) r') hbase hn)

end Stacks.PureModules
