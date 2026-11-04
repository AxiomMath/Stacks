module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# Flat local deformations of a Koszul complex

Let `R → A` be a flat local homomorphism of local rings which is essentially of finite
presentation, and let `K` be a perfect object of the derived category of `A`-modules whose derived
restriction to the closed fibre `A / 𝔪_R A` is the Koszul complex on a regular sequence. This file
packages that standing situation as a single structure, which is the interface used by the lifting
results for such deformations.

## Main definitions

* `AlgebraicGeometry.FlatLocalKoszulDeformationSituation`: the standing data and hypotheses of a
  flat local deformation of a Koszul complex.

## Implementation notes

The closed-fibre hypothesis is phrased with derived extension of scalars directly, and the
homological Koszul complex is placed in cohomological degree `-i` in degree `i` by the standard
embedding `ComplexShape.embeddingDownNat`.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The standing situation of a flat local deformation of a Koszul complex. -/
public structure FlatLocalKoszulDeformationSituation where
  /-- The base local ring. -/
  R : Type u
  /-- The local algebra. -/
  A : Type u
  [commRingR : CommRing R]
  [commRingA : CommRing A]
  [localRingR : IsLocalRing R]
  [localRingA : IsLocalRing A]
  [algebra : Algebra R A]
  /-- The algebra map is local. -/
  [localHom : IsLocalHom (algebraMap R A)]
  /-- The algebra is flat over the base. -/
  [flat : Module.Flat R A]
  /-- The algebra map is essentially of finite presentation. -/
  essentiallyOfFinitePresentation :
    IsEssentiallyOfFinitePresentation R A (algebraMap R A)
  /-- The length of the sequence on the closed fibre. -/
  r : ℕ
  /-- The sequence in `A / 𝔪 A`. -/
  residueSequence : Fin r →
    A ⧸ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)
  /-- Every member of the sequence belongs to `𝔫 / 𝔪 A`. -/
  residueSequence_mem : ∀ i, residueSequence i ∈
    (IsLocalRing.maximalIdeal A).map
      (Ideal.Quotient.mk (Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)))
  /-- The sequence is regular in the closed-fibre ring. -/
  residueSequence_regular : RingTheory.Sequence.IsRegular
    (A ⧸ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R))
    (List.ofFn residueSequence)
  /-- The perfect derived object being deformed. -/
  K : DerivedCategory (ModuleCat.{u} A)
  /-- The object `K` is perfect. -/
  K_perfect : StacksDraft.Perfect.IsPerfect K
  /-- Its derived restriction to the closed fibre is the Koszul complex of the sequence. -/
  closedFiber_isKoszul : Nonempty
    ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
      (Ideal.Quotient.mk (Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)))).functor.obj
      K ≅
      DerivedCategory.Q.obj
        ((Koszul.seqComplex residueSequence).extend ComplexShape.embeddingDownNat))

attribute [instance]
  FlatLocalKoszulDeformationSituation.commRingR
  FlatLocalKoszulDeformationSituation.commRingA
  FlatLocalKoszulDeformationSituation.localRingR
  FlatLocalKoszulDeformationSituation.localRingA
  FlatLocalKoszulDeformationSituation.algebra
  FlatLocalKoszulDeformationSituation.localHom
  FlatLocalKoszulDeformationSituation.flat

end AlgebraicGeometry

end
