module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimodulePropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBaseChangeSecondVariable
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# Composition of derived tensor products when `A ⊗_R C` represents `A ⊗^𝐋_R C`

Let `R` be a ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras
such that the ordinary tensor product `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`. For a
differential graded `(A, B)`-bimodule `N` and a differential graded `(B, C)`-bimodule `N'`, the
composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to
`- ⊗_A^𝐋 N''` for the differential graded `(A, C)`-bimodule
`N'' = DifferentialGraded.Bimodule.compTensorResolution N N'`, the composite `Ñ ⊗_B Ñ'` of
property-(P) replacements of `N` and `N'`.

Representability of `A ⊗^𝐋_R C` by `A ⊗_R C` means that for a K-flat resolution `P ⟶ A` of the
complex of `R`-modules underlying `A` the induced map `Tot(P ⊗_R C) ⟶ Tot(A ⊗_R C)` is a
quasi-isomorphism. It is implied by K-flatness of `C`.

## Main definitions

* `DifferentialGraded.Bimodule.DgaResolutionRepresentsDerivedTensor`: `A ⊗_R C` represents
  `A ⊗^𝐋_R C` in `D(R)`.
* `DifferentialGraded.Bimodule.DgaResolutionRepresentsInvertsBaseChange`: representability of
  `A ⊗^𝐋_R C` makes the comparison map `derivedTensorBaseChangeComparison A B C` an isomorphism.

## Main results

* `DifferentialGraded.Bimodule.dgaResolutionRepresents_of_kFlat`: K-flatness of the complex
  underlying `C` implies that `A ⊗_R C` represents `A ⊗^𝐋_R C`, for every `A`.
* `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso`: the composite of the two
  derived tensor functors is isomorphic to `- ⊗_A^𝐋 N''`.

## Implementation notes

`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso` takes two hypotheses:
`hrep`, that `A ⊗_R C` represents `A ⊗^𝐋_R C`, and `hbridge`, that representability makes
`derivedTensorBaseChangeComparison A B C` an isomorphism
(`DifferentialGraded.Bimodule.DgaResolutionRepresentsInvertsBaseChange`). The hypothesis
`hbridge` holds when `B` is K-flat as a complex of `R`-modules, by
`DifferentialGraded.Bimodule.dgaResolutionRepresentsInvertsBaseChange_of_kFlat`.

`CochainComplex.KFlat` and the tensor-total functor `TrightCochain` are stated against the
large-universe monoidal structure on `ModuleCat`, whose module universe is independent of the
ring's, so the lifted monoidal instances are local instances for this file.

The differential graded algebras and their bimodules live in a single universe `u`, and
K-flatness is taken at `CochainComplex.KFlat.{u, u}`.

## References

* [Stacks Project, Tag 0BZ8](https://stacks.math.columbia.edu/tag/0BZ8)
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5)
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4)
* [Stacks Project, Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3)
* [Stacks Project, Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- The ordinary tensor product `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`: tensoring a K-flat
resolution `P ⟶ A` of the complex of `R`-modules underlying `A` with the complex underlying `C`
yields a quasi-isomorphism `Tot(P ⊗_R C) ⟶ Tot(A ⊗_R C)`. -/
def DgaResolutionRepresentsDerivedTensor (A C : DifferentialGradedAlgebra.{u, u} R) : Prop :=
  ∀ P : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} P →
    ∀ q : P ⟶ (regularModule A).toCochainComplex, QuasiIso q →
      QuasiIso ((TrightCochain (regularModule C).toCochainComplex).map q)

/-- If the complex of `R`-modules underlying `C` is K-flat, then `A ⊗_R C` represents
`A ⊗^𝐋_R C` in `D(R)` for every differential graded `R`-algebra `A`. -/
theorem dgaResolutionRepresents_of_kFlat (A C : DifferentialGradedAlgebra.{u, u} R)
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex) :
    DgaResolutionRepresentsDerivedTensor A C :=
  fun _ _ q _ => CochainComplex.DerivedTensor.quasiIso_tright_map.{u, u} _ hC q

/-- Representability of `A ⊗^𝐋_R C` by `A ⊗_R C` makes the canonical comparison map
`derivedTensorBaseChangeComparison A B C` an isomorphism. -/
def DgaResolutionRepresentsInvertsBaseChange
    (A B C : DifferentialGradedAlgebra.{u, u} R) : Prop :=
  DgaResolutionRepresentsDerivedTensor A C →
    IsIso (derivedTensorBaseChangeComparison A B C)

/-- Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras with `A ⊗_R C`
representing `A ⊗^𝐋_R C` in `D(R)` (`hrep`), and assume that representability makes
`derivedTensorBaseChangeComparison A B C` an isomorphism (`hbridge`). Let `N` be a differential
graded `(A, B)`-bimodule and `N'` a differential graded `(B, C)`-bimodule. Then the composition
`D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for
the differential graded `(A, C)`-bimodule `N'' = Ñ ⊗_B Ñ'` of
`DifferentialGraded.Bimodule.compTensorResolution`, the composite of property-(P) replacements. -/
@[stacks 0BZ8 "with the passage from the representability hypothesis to the Stacks 0BZ4 \
hypothesis of Stacks 0BZ5 as hbridge, which is proved for B K-flat as a complex of R-modules by \
dgaResolutionRepresentsInvertsBaseChange_of_kFlat and for a general B needs the transport along \
the Stacks 09S6 equivalence that the source's K-flat replacement of B by Stacks 0BZ7 sets up"]
def dgaResolutionDerivedTensorFunctorCompIso
    (hbridge : DgaResolutionRepresentsInvertsBaseChange A B C)
    (hrep : DgaResolutionRepresentsDerivedTensor A C)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIsoOfBaseChange A B C (hbridge hrep) N N'

end DifferentialGraded.Bimodule

end
