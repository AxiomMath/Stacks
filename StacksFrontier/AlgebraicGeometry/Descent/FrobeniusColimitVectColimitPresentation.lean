module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitDescentTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj

/-!
# Over a qcqs scheme, the stage pseudo-cocone presents `colim_F Vect` as the colimit

`CategoryTheory.EndoColim.Pseudococone.IsColimitPresentation` is the hypothesis under which
`CategoryTheory.Pseudofunctor.StageColimitData.isStackFor_singleton` passes effective descent
from `Vect` to the finite locally free `colim_F 𝒪`-modules, at the objects the descent datum
lives on.  For the pseudo-cocone of Stacks Tag 0EXB,
`AlgebraicGeometry.frobeniusColimitVectPseudococone` (stage `n` is extension of scalars along the
stage-`n` coprojection `𝒪_X ⟶ colim_F 𝒪_X`), it holds over every quasi-compact quasi-separated
scheme, by Stacks Tag 0EXB itself.

## Main results

* `AlgebraicGeometry.isColimitPresentation_frobeniusColimitVectPseudococone`: **over a
  quasi-compact quasi-separated scheme in characteristic `p` the stage pseudo-cocone of Stacks Tag
  0EXB presents the category of finite locally free `colim_F 𝒪_X`-modules as the colimit of
  `Vect(X) →F Vect(X) →F ⋯`.**  It is
  `CategoryTheory.EndoColim.Pseudococone.isColimitPresentation_of_desc`: the induced functor
  `AlgebraicGeometry.frobeniusColimitVectComparison` is full and faithful
  (`AlgebraicGeometry.full_frobeniusColimitVectComparison`,
  `AlgebraicGeometry.faithful_frobeniusColimitVectComparison`) and every finite locally free
  module is a stage image (`AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`).

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **Over a quasi-compact quasi-separated scheme in characteristic `p`, the stage pseudo-cocone
of Stacks Tag 0EXB presents the finite locally free `colim_F 𝒪_X`-modules as the colimit of the
Frobenius diagram on `Vect(X)`.** -/
theorem isColimitPresentation_frobeniusColimitVectPseudococone [CompactSpace X]
    [QuasiSeparatedSpace X] :
    (frobeniusColimitVectPseudococone X p hX).IsColimitPresentation := by
  have : (frobeniusColimitVectPseudococone X p hX).desc.Full :=
    full_frobeniusColimitVectComparison X p hX
  have : (frobeniusColimitVectPseudococone X p hX).desc.Faithful :=
    faithful_frobeniusColimitVectComparison X p hX
  exact EndoColim.Pseudococone.isColimitPresentation_of_desc _
    (exists_frobeniusStageFunctor_obj_iso X p hX)

end AlgebraicGeometry

end
