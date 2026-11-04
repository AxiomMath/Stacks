module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomTensorIso

/-! # The quasi-inverse of a tilting bimodule is a derived tensor product

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule satisfying the three conditions of
[Stacks, Tag 09S7]: the class of `N` is a compact object of `D(B, d)`, it weakly generates
`D(B, d)`, and the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` is bijective for every `k`.
Then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence, with quasi-inverse the derived Hom
functor `R Hom(N, -)` of Tag 09LI
(`DifferentialGraded.Bimodule.derivedTensorEquivalence`).

This file identifies that quasi-inverse as a *derived tensor product in the opposite direction*.
Assume in addition that the plain Hom complex `S = Hom^•_B(N, B)` represents `R Hom(N, B)`, the
hypothesis of [Stacks, Tag 0BZ0]. That tag makes `S` a differential graded `(B, A)`-bimodule
(`DifferentialGraded.Bimodule.homDualBimodule`) and gives an isomorphism of functors
`- ⊗_B^𝐋 S ≅ R Hom(N, -)`
(`DifferentialGraded.Bimodule.derivedTensorHomDualFunctorIso`). Composing the two:

* `- ⊗_B^𝐋 S : D(B, d) ⥤ D(A, d)` is an equivalence, and
* the two composites `(- ⊗_A^𝐋 N) ⋙ (- ⊗_B^𝐋 S)` and `(- ⊗_B^𝐋 S) ⋙ (- ⊗_A^𝐋 N)` are isomorphic
  to the identity functors of `D(A, d)` and of `D(B, d)`.

So `S` is an inverse to `N` at the level of the functors they define, and it is produced
explicitly rather than by an existence statement. There is no flatness hypothesis anywhere here.

## Main results

* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_homDualBimodule`: the derived
  tensor product with the Hom-dual bimodule is an equivalence.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompHomDualIso` and
  `DifferentialGraded.Bimodule.homDualDerivedTensorFunctorCompIso`: the two composites are the
  identity functors.

## Implementation notes

*Why this is the functor level and not the bimodule level.* A two-sided tilting complex is a
bimodule `N` together with isomorphisms `N ⊗_B^𝐋 S ≅ A` in `D(A^{opp} ⊗_R A, d)` and
`S ⊗_A^𝐋 N ≅ B` in `D(B^{opp} ⊗_R B, d)` — isomorphisms of *bimodules*. What is proved here is
weaker: the two derived tensor functors are mutually quasi-inverse. The two are not the same
statement, and the gap between them is exactly the fullness of the assignment
`N ↦ (- ⊗_A^𝐋 N)`, which this library does not have in any form: an isomorphism of derived
tensor functors is not known to come from an isomorphism of the bimodules. The forward direction,
`DifferentialGraded.Bimodule.derivedTensorNatTrans`, is all that exists. Evaluating the
isomorphisms below at the regular modules does give `N ⊗_B S ≅ A` in `D(A, d)`, but as right
modules only, with no bimodule structure, which is not what a conjugation on bimodule derived
categories can be built from.

*The three hypotheses of Tag 09S7, and the fourth of Tag 0BZ0.* The first three are exactly the
conclusions of [Stacks, Tag 09SA], so they are available for the bimodule that tag attaches to a
derived equivalence. The fourth, that the plain Hom complex computes `R Hom(N, B)`, is not among
them and is assumed here, as it is in Tag 0BZ0 itself.

*Defeq of the quasi-inverse.* `DifferentialGraded.Bimodule.derivedTensorEquivalence` is built as
`CategoryTheory.Adjunction.toEquivalence` applied to the adjunction of Tag 09LT, whose right
adjoint is the derived Hom functor of the canonical `DerivedHomData`. Its `inverse` field is
therefore that functor on the nose, which is the functor Tag 0BZ0 compares with
`- ⊗_B^𝐋 S`; no transport is needed to put the two isomorphisms together.

## References

* [Stacks Project, Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0), the identification of
  derived Hom out of a compact bimodule with a derived tensor product.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7), the criterion making
  `- ⊗_A^𝐋 N` an equivalence, and [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for the
  adjunction whose right adjoint is the quasi-inverse.
* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), which supplies the three
  hypotheses of Tag 09S7 for a bimodule representing a derived equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

section HomDualInverse

variable (N : Bimodule A B)
  [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
  (h2 : ∀ X : derivedCategory' B,
    (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
      X⟦n⟧), f = 0) → IsZero X)
  (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k))
  (hrep : IsIso ((derivedHomData A B N.rightModule N.leftAction).comparison.app
    ((toHomotopyCategory B).obj (regularModule B))))

include h2 h3 hrep

/-- **The derived tensor product with the Hom-dual bimodule is an equivalence.** Under the three
conditions of [Stacks, Tag 09S7] on `N` the functor `- ⊗_A^𝐋 N` is an equivalence whose
quasi-inverse is `R Hom(N, -)`; under the further hypothesis of [Stacks, Tag 0BZ0] that
`Hom^•_B(N, B)` represents `R Hom(N, B)`, that quasi-inverse is the derived tensor product with
the Hom-dual bimodule `S = Hom^•_B(N, B)` of
`DifferentialGraded.Bimodule.homDualBimodule`. Hence `- ⊗_B^𝐋 S` is an equivalence too. -/
theorem isEquivalence_derivedTensorFunctor_homDualBimodule :
    (derivedTensorFunctor (homDualBimodule N)).IsEquivalence :=
  have : ((derivedHomData A B N.rightModule N.leftAction).functor).IsEquivalence :=
    (derivedTensorEquivalence N h2 h3).isEquivalence_inverse
  Functor.isEquivalence_of_iso
    (derivedTensorHomDualFunctorIso N inferInstance hrep).symm

/-- **Tensoring with `N` and then with its Hom-dual is the identity of `D(A, d)`.** The
composite `(- ⊗_A^𝐋 N) ⋙ (- ⊗_B^𝐋 S)` is isomorphic to the identity functor of `D(A, d)`: by
[Stacks, Tag 0BZ0] the second factor is `R Hom(N, -)`, which is the quasi-inverse of the first by
[Stacks, Tag 09S7], and the isomorphism is the unit of the equivalence. -/
def derivedTensorFunctorCompHomDualIso :
    derivedTensorFunctor N ⋙ derivedTensorFunctor (homDualBimodule N) ≅
      𝟭 (derivedCategory' A) :=
  Functor.isoWhiskerLeft (derivedTensorFunctor N)
      (derivedTensorHomDualFunctorIso N inferInstance hrep) ≪≫
    (derivedTensorEquivalence N h2 h3).unitIso.symm

/-- **Tensoring with the Hom-dual of `N` and then with `N` is the identity of `D(B, d)`.** The
mirror of `DifferentialGraded.Bimodule.derivedTensorFunctorCompHomDualIso`, with the counit of
the equivalence in place of its unit. -/
def homDualDerivedTensorFunctorCompIso :
    derivedTensorFunctor (homDualBimodule N) ⋙ derivedTensorFunctor N ≅
      𝟭 (derivedCategory' B) :=
  Functor.isoWhiskerRight (derivedTensorHomDualFunctorIso N inferInstance hrep)
      (derivedTensorFunctor N) ≪≫
    (derivedTensorEquivalence N h2 h3).counitIso

end HomDualInverse

end DifferentialGraded.Bimodule

end
