module

public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.Homology.Perfect.Regular
public import StacksFrontier.RingTheory.PseudoCoherentMap.Noetherian
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

@[expose] public section

/-!
# Finite type maps from regular rings are perfect

Let `A` be a regular ring. Every finite-type `A`-algebra `B` is a perfect ring map: it is
pseudo-coherent, and `B` has finite Tor dimension as an `A`-module.

## Main results

* `RingHom.isPerfectRingMap_of_finiteType_of_isRegularRing` (Stacks 067K).

## Implementation notes

Pseudo-coherence is Stacks 067I: a regular ring is Noetherian, so a finite-type ring map out of
it is pseudo-coherent.

Finite Tor dimension comes from Stacks 068Y: `A → B` is perfect exactly when some presentation
`B = A[x_1, …, x_n]/I` exhibits `B` as a module with a finite resolution by finite projective
`A[x_1, …, x_n]`-modules. The polynomial ring over a regular ring is regular
(`MvPolynomial.isRegularRing_of_isRegularRing`), and over a regular ring the perfect modules are
exactly the finite ones, which is Stacks 066Z
(`StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology`);
`B` is finite over `A[x_1, …, x_n]` because the presentation is surjective.

This is why the source's hypothesis that `A` have finite Krull dimension is not needed: the
uniform bound on the length of the resolution comes from quasi-compactness of
`Spec A[x_1, …, x_n]`, inside the proof of Stacks 066Z, and not from a global dimension bound. A
regular ring of infinite Krull dimension has infinite global dimension, but each of its local
rings is a regular local ring and hence of finite global dimension, which is all 066Z uses.

The derived tensor product is not canonical in this development, so — as in
`RingHom.IsPerfectRingMap` itself and in `RingHom.isPerfectRingMap_of_flat_of_finitePresentation`
— the bifunctor, its comparison with termwise tensoring and the universal property making each
`- ⊗ᴸ N[0]` a total left derived functor are supplied as data, and the conclusion holds for every
such datum.

## References

* [The Stacks Project, Lemma 15.83.5 (067K)](https://stacks.math.columbia.edu/tag/067K)
* [The Stacks Project, Lemma 15.74.16 (066Z)](https://stacks.math.columbia.edu/tag/066Z)
* [The Stacks Project, Lemma 15.83.2 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
-/

open CategoryTheory CategoryTheory.Limits

namespace RingHom

universe u

attribute [local instance] HasDerivedCategory.standard


/-! ### The theorem -/

/-- **Stacks 067K.** A finite-type ring map out of a regular ring is perfect: it is
pseudo-coherent, and its target has finite Tor dimension as a module over its source, for every
certified derived tensor product.

The source assumes in addition that the regular ring has finite Krull dimension; that hypothesis
is not needed, because the bound on the length of the resolution is produced from
quasi-compactness of the prime spectrum of the polynomial ring rather than from a bound on its
global dimension. -/
@[stacks 067K]
public theorem isPerfectRingMap_of_finiteType_of_isRegularRing
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B]
    (derivedTensor : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsPerfectRingMap A B derivedTensor comparison isLeftDerived := by
  rw [isPerfectRingMap_iff_exists_finite_projective_resolution]
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  refine ⟨n, α, hα, ?_⟩
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  let αₗ : MvPolynomial (Fin n) A →ₗ[MvPolynomial (Fin n) A] B :=
    { toFun := α
      map_add' := fun p q => map_add α p q
      map_smul' := fun p q => map_mul α p q }
  have : Module.Finite (MvPolynomial (Fin n) A) B := Module.Finite.of_surjective αₗ hα
  rw [← StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B]
  exact (StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology
    (R := MvPolynomial (Fin n) A)).1 B |>.2 inferInstance

end RingHom
