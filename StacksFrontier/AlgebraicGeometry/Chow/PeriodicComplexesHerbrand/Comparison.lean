module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthSubquotient

/-!
# Comparing multiplicities of two-periodic complexes

A morphism of `(2, 1)`-periodic complexes whose kernel and cokernel have finite length
preserves the multiplicity of the complexes, provided their cohomology modules have finite
length.

## Main results

* `AlgebraicGeometry.periodicLength_eq_of_finite_length_kernel_cokernel` compares the periodic
  lengths on the source and target of such a morphism.

## Implementation notes

Two-periodic complexes are represented by homological complexes indexed by `ZMod 2`. Rather
than requiring the two terms to be definitionally the same module, the `(2, 1)`-periodicity of
the kernel and cokernel is expressed invariantly by isomorphisms between their terms. Thus it
is enough to assume finite length in degree zero.

## References

* [Stacks Project, Tag 0EA9](https://stacks.math.columbia.edu/tag/0EA9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ModuleCat ShortComplex

universe u v

namespace AlgebraicGeometry

/-- A two-periodic complex whose two terms are isomorphic and of finite length has
finite-length cohomology. -/
private lemma finiteLengthHomology_of_finiteLength_terms
    {R : Type u} [Ring R]
    (K : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)))
    (h : IsFiniteLength R (K.X (0 : ZMod 2)))
    (e : K.X (0 : ZMod 2) ≅ K.X (1 : ZMod 2)) :
    HasFiniteLengthHomology K := by
  intro i
  have h' : IsFiniteLength R (K.X i) := by
    fin_cases i
    · exact h
    · exact e.toLinearEquiv.isFiniteLength h
  exact (h'.of_injective ((mono_iff_injective (K.iCycles i)).mp inferInstance)).of_surjective
    ((epi_iff_surjective (K.homologyπ i)).mp inferInstance)

/-- A morphism between `(2, 1)`-periodic complexes with finite-length kernel and cokernel
preserves their periodic length when the cohomology modules of both complexes have finite
length. -/
@[stacks 0EA9]
public theorem periodicLength_eq_of_finite_length_kernel_cokernel
    {R : Type u} [Ring R]
    {C D : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))}
    (f : C ⟶ D)
    (hC : ∀ i, IsFiniteLength R (C.homology i))
    (hD : ∀ i, IsFiniteLength R (D.homology i))
    (hker : IsFiniteLength R ((kernel f).X (0 : ZMod 2)))
    (hcoker : IsFiniteLength R ((cokernel f).X (0 : ZMod 2)))
    (eker : (kernel f).X (0 : ZMod 2) ≅ (kernel f).X (1 : ZMod 2))
    (ecoker : (cokernel f).X (0 : ZMod 2) ≅ (cokernel f).X (1 : ZMod 2)) :
    periodicLength C = periodicLength D := by
  let S₁ := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (by simp)
  let S₂ := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (kernel.condition (cokernel.π f))
  have h₁ := periodicLength_additive_of_shortExact S₁
    (ShortExact.mk'
      (exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι f))) inferInstance inferInstance)
    (Or.inl ⟨finiteLengthHomology_of_finiteLength_terms (kernel f) hker eker, hC⟩)
  have h₂ := periodicLength_additive_of_shortExact S₂
    (ShortExact.mk'
      (exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f))) inferInstance inferInstance)
    (Or.inr (Or.inr ⟨hD, finiteLengthHomology_of_finiteLength_terms (cokernel f) hcoker ecoker⟩))
  have zker := periodicLength_eq_zero_of_iso (kernel f) hker eker
  have zcoker := periodicLength_eq_zero_of_iso (cokernel f) hcoker ecoker
  have hcoim : periodicLength (Abelian.coimage f) = periodicLength (Abelian.image f) :=
    periodicLength_eq_of_iso (Abelian.coimageIsoImage f)
  dsimp [S₁] at h₁
  dsimp [S₂] at h₂
  omega

end AlgebraicGeometry
