module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionTower
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat resolutions of left differential graded modules

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `N` be a **left** differential graded `A`-module. This file produces a quasi-isomorphism
`Q ⟶ N` from a left differential graded `A`-module `Q` which is K-flat on the left: tensoring an
acyclic *right* differential graded `A`-module with `Q` gives an acyclic complex.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_leftFlat_quasiIso`: **every left differential
  graded `A`-module receives a quasi-isomorphism from a left differential graded `A`-module which
  is K-flat on the left.** The module and the homomorphism are built from `N` alone; no tower, no
  generating family and no resolution datum is an argument.

## Implementation notes

The construction is the one for right modules, transported. A left differential graded
`A`-module is a right differential graded `A.op`-module, by interchanging the two factors of the
action and twisting by the Koszul sign
(`SheafOfModules.LeftDifferentialGradedModule.opRight`), and a right differential graded
`A.op`-module is a left differential graded `A`-module the same way
(`SheafOfModules.DifferentialGradedModule.unopLeft`). So the tower of the first proof of
Tag 0FSH, built over `A.op` for `N.opRight` by
`SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso`, gives a right differential
graded `A.op`-module `Q'` with a quasi-isomorphism to `N.opRight` which is K-flat over `A.op`,
and `Q := Q'.unopLeft` is the module wanted:

* the homomorphism is `SheafOfModules.DifferentialGradedModule.Hom.unopLeft` of the one
  produced, which has the same underlying morphism of cochain complexes, so it is a
  quasi-isomorphism for the same reason;
* K-flatness over `A.op` says that `Q' ⊗_{A.op} Y` is acyclic for every acyclic left
  differential graded `A.op`-module `Y`; for an acyclic right differential graded `A`-module `M`
  this applies to `Y := M.opLeft`, whose complex is that of `M`, and
  `SheafOfModules.RelativeTensor.dgTensorOpIso` identifies `Q' ⊗_{A.op} M.opLeft` with
  `M ⊗_A Q`.

The second clause of goodness for right modules — flatness as a graded module — is produced by
the tower as well and is not carried across: the statement here is the K-flatness clause, which
is what the tensor-product arguments of Tag 0FSI consume.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- **Every left differential graded `A`-module receives a quasi-isomorphism from a left
differential graded `A`-module which is K-flat on the left**: tensoring an acyclic right
differential graded `A`-module with it gives an acyclic complex.

The resolution is built from `N` alone, by transporting the tower of the first proof of
Tag 0FSH across the identification of left differential graded `A`-modules with right
differential graded `A.op`-modules. -/
theorem exists_leftFlat_quasiIso (N : LeftDifferentialGradedModule.{t, m, m} A) :
    ∃ (Q : LeftDifferentialGradedModule.{t, m, m} A) (q : Q ⟶ N),
      QuasiIso q.toHomologicalComplex ∧
        ∀ M : DifferentialGradedModule.{t, m, m} A, M.complex.Acyclic →
          (RelativeTensor.dgTensor M Q).Acyclic := by
  obtain ⟨Q, f, hqi, -, hkflat⟩ := exists_flat_quasiIso (A := A.op) N.opRight
  exact ⟨Q.unopLeft, Hom.unopLeft f, hqi, fun M hM ↦
    RelativeTensor.acyclic_dgTensor_of_acyclic_dgTensor_op M Q (hkflat M.opLeft hM)⟩

end SheafOfModules.DifferentialGradedModule

end
