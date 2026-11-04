module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalSheaves
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.FiniteTypeAndWords
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.LocalKernel
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalLocallyFree
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.LocalInjectivity
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.IndependentGenerators

/-!
# Characterization of quasi-regular ideal sheaves

Let `X` be a locally ringed space and `J ⊆ O_X` a sheaf of ideals.  Then `J` is quasi-regular
in the sense of Stacks tag 063D exactly when `J` is of finite type, the conormal sheaf `J/J²`
is finite locally free over `O_X/J`, and for every `n` the canonical map
`Symⁿ_(O_X/J)(J/J²) ⟶ Jⁿ/Jⁿ⁺¹` is an isomorphism.

The three conditions are built from the sectionwise quotients of the ideal: over an open `U`
the ideal of sections `J(U)` has its own powers, conormal module and symmetric powers, and the
multiplication of ideal sections gives a map from the symmetric power to the graded piece.
These assemble into presheaves of modules over the quotient presheaf of rings `O_X/J`, and the
sheaves of the statement are their sheafifications.

## Main definitions

* `Conormal.quotientSheaf`: the quotient sheaf of rings `O_X/J`.
* `Conormal.associatedGradedPiece`: the `O_X/J`-module sheaf `Jⁿ/Jⁿ⁺¹`.
* `Conormal.conormalSheaf`: the conormal sheaf `J/J²`, the degree-one graded piece.
* `Conormal.conormalSymmetricPower`: the symmetric power `Symⁿ_(O_X/J)(J/J²)`.
* `Conormal.conormalSymmetricToGradedMap`: the canonical morphism between the two.

## Main results

* `Conormal.isQuasiRegularIdealSheaf_iff`: **Stacks tag 063H**, both directions.

## Implementation notes

The symmetric power of an ideal is presented by symmetric multilinear words in ideal
elements: coefficients are reduced modulo the ideal and each letter modulo the square of the
ideal, in every degree including zero.  Multiplication of letters respects those relations and
restriction of sections, so it is a morphism of presheaves of modules, and sheafification of
presheaves of modules preserves the cokernels and coproducts the comparison needs.

## References

* [Stacks Project, Lemma 31.20.5 (Tag 063H)](https://stacks.math.columbia.edu/tag/063H)
* [Stacks Project, Lemma 10.20.1 (Tag 00DV)](https://stacks.math.columbia.edu/tag/00DV)
-/
