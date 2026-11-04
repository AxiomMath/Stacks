module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Sym(ℰ)` as a sheaf of commutative algebras

Let `S` be a scheme and `ℰ` an `𝒪_S`-module. `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`
is `Sym(ℰ)` as a sheaf of graded `𝒪_S`-algebras; its homogeneous multiplication commutes, so its
ungraded realization is a sheaf of *commutative* `𝒪_S`-algebras. That is the shape of Stacks Tag
01LM, and the shape the relative spectrum consumes, and this file puts `Sym(ℰ)` into it.

The file exists on its own, below both the proof that this algebra sheaf is quasi-coherent
([Stacks, Tag 01CK], in
`StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent`) and the
construction of `𝐕(ℰ) = Spec_S(Sym(ℰ))` from it (Tag 01M2, in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule`), so that the vector bundle
can be formed with quasi-coherence of `Sym(ℰ)` already in scope rather than hypothesised.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`: `Sym(ℰ)` as a sheaf of commutative
  `𝒪_S`-algebras.

## Main results

* `AlgebraicGeometry.Scheme.Modules.ringSheaf_symmetricAlgebraSheaf`: the sheaf of rings of
  `symmetricAlgebraSheaf` is the ungraded realization of `Sym(ℰ)`, on the nose.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf)

/-- **`Sym(ℰ)` as a sheaf of commutative `𝒪_S`-algebras**: the ungraded realization of the sheaf
of graded algebras `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`, which is commutative
because its homogeneous multiplication is. This is the input the relative spectrum takes. -/
@[sga "3 I 4.6.3.1" "Sym(F) as algebra sheaf"]
def symmetricAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf S :=
  Stacks.RelativeSpec.gradedAlgebraSheaf S (symmetricAlgebra S E) (symmetricAlgebra_mul_comm S E)

/-- The sheaf of rings of `Sym(ℰ)` as an algebra sheaf is the ungraded realization of the sheaf of
graded algebras `Sym(ℰ)`, not a copy of it. -/
theorem ringSheaf_symmetricAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (symmetricAlgebraSheaf S E) =
      (symmetricAlgebra S E).ungradedSheaf :=
  rfl

end AlgebraicGeometry.Scheme.Modules

end
