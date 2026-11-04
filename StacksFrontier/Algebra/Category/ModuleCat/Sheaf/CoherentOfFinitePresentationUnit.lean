module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation plus a coherent structure sheaf gives coherence

On a ringed site whose structure sheaf is coherent, every sheaf of modules of finite
presentation is coherent.  This is the site-level form of Stacks 01BZ: over a coherent
structure sheaf the finite-presentation condition of Stacks 03DL (7) implies the coherence
condition of Stacks 03DL (8).

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit`: **a sheaf of
  modules of finite presentation on a ringed site with coherent structure sheaf is
  coherent.**

## Implementation notes

The proof reads the module as its own tensor product with the structure sheaf and quotes the
mixed clause of Stacks 03L6 already in the library.
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherent_of_isFinitePresentation`
says that the tensor product of a sheaf of modules of finite presentation with a coherent
sheaf of modules is coherent; taking the second factor to be the structure sheaf, whose
coherence is the hypothesis, makes the tensor product coherent, and the right unit constraint
of the tensor product of Stacks 01CA,
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso`, identifies it with the module itself.  The two
spellings of the tensor product involved are the same construction, equal by `rfl`, as
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge` records, so nothing is
transported between them: the right unit constraint is applied to the value of the tensor
product bifunctor directly.

No cover is chosen and no presentation is built here; both happen inside the quoted clause of
Stacks 03L6, which produces a covering family on whose members the module has a finite
presentation and runs the local-to-global step itself.  In particular the module universe stays
free, so none of the universe lifting of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherentOnSite` is needed.

## References

* [Stacks Project, Tag 01BZ](https://stacks.math.columbia.edu/tag/01BZ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

/-- **A sheaf of modules of finite presentation on a ringed site whose structure sheaf is
coherent is coherent.**

Tensoring with the structure sheaf gives the module back, so this is the mixed
finite-presentation/coherence clause of Stacks 03L6,
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherent_of_isFinitePresentation`,
applied with the structure sheaf as the coherent factor, followed by the right unit constraint
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` of the tensor product of Stacks 01CA. -/
@[ega "0 5.3.7" "more general"]
theorem isCoherentOnSite_of_isFinitePresentation_of_unit
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      [M.IsFinitePresentation]
    (hO : _root_.SheafOfModules.IsCoherentOnSite
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    _root_.SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_iso
    (tensorLeftFunctorObjUnitIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M)
    (TensorLocalProperties.tensorSheaf_isCoherent_of_isFinitePresentation X M
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hG := hO))

end Stacks.SheafOfModules

end
