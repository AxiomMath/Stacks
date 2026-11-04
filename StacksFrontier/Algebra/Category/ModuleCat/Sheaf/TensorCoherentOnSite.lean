module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentOnSiteFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUniverseLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two coherent sheaves of modules on a ringed site is coherent

This is the coherent clause of Stacks 03L6, for the site-level coherence predicate
`SheafOfModules.IsCoherentOnSite` of Stacks 03DL(8).

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherentOnSite`: **the tensor
  product of two coherent sheaves of modules on a ringed site is coherent.**

## Implementation notes

The source's argument is that a coherent sheaf of modules is of finite presentation, so the
mixed clause
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherent_of_isFinitePresentation`
applies.  Carrying that out needs Stacks 01BW(1) on a site,
`Stacks.SheafOfModules.isFinitePresentation_of_isCoherentOnSite`, whose presentation machinery
only typechecks when the sections of the sheaves of modules live at the universe `max u v w` at
which sheafification of abelian groups is available on every slice of the site.  Sections of a
sheaf of modules on a ringed site are not there in general, so the whole statement is moved
there first by `Stacks.SheafOfModules.CoherentLift.liftRingedSite` and
`Stacks.SheafOfModules.CoherentLift.liftModule`, proved at the lifted universe, and moved back:
`Stacks.SheafOfModules.CoherentLift.isCoherentOnSite_liftModule_iff` says that the lift neither
creates nor destroys coherence, and
`Stacks.SheafOfModules.CoherentLift.tensorLiftIso` says that it commutes with the tensor
product.

At the lifted universe the five sheafification and local-bijectivity facts for the site, its
slices and the slices of its slices are all available, but instance resolution does not find
them: the module universe is a `max`, and unifying it against the `max` of a slice's object
universe is not a problem the level unifier solves.  They are therefore supplied explicitly
from `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.TensorLocalProperties

universe u v w

open CoherentLift

/-- **Stacks Project, Tag 03L6, coherent case.**  The tensor product of two coherent sheaves of
modules on a ringed site is coherent.

Following the source: a coherent sheaf of modules is of finite presentation, so the mixed
finite-presentation/coherence clause applies.  The argument is run at the universe lift of the
ringed site, where the presentation machinery of Stacks 01BW(1) is available, and transported
back along `Stacks.SheafOfModules.CoherentLift.isCoherentOnSite_liftModule_iff` and
`Stacks.SheafOfModules.CoherentLift.tensorLiftIso`. -/
@[stacks 03L6 "coherent", instance, ega "I 9.1.1" "coherent tensor", ega "0 5.3.5" "tensor product"]
theorem tensorSheaf_isCoherentOnSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hF : _root_.SheafOfModules.IsCoherentOnSite F]
    [hG : _root_.SheafOfModules.IsCoherentOnSite G] :
    _root_.SheafOfModules.IsCoherentOnSite
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) := by
  let i1 : HasSheafify (liftRingedSite.{u, v, w} X).J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u}
      (liftRingedSite.{u, v, w} X).J
  let i2 : (liftRingedSite.{u, v, w} X).J.WEqualsLocallyBijective
      AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v}
      (liftRingedSite.{u, v, w} X).J
  let i3 : ∀ U : (liftRingedSite.{u, v, w} X).C,
      HasSheafify ((liftRingedSite.{u, v, w} X).J.over U) AddCommGrpCat.{max u v w} := fun U ↦
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v}
      ((liftRingedSite.{u, v, w} X).J.over U)
  let i4 : ∀ U : (liftRingedSite.{u, v, w} X).C,
      ((liftRingedSite.{u, v, w} X).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{max u v w} := fun U ↦
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} ((liftRingedSite.{u, v, w} X).J.over U)
  let i5 : ∀ (U : (liftRingedSite.{u, v, w} X).C) (V : Over U),
      HasSheafify (((liftRingedSite.{u, v, w} X).J.over U).over V)
        AddCommGrpCat.{max u v w} := fun U V ↦
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v}
      (((liftRingedSite.{u, v, w} X).J.over U).over V)
  let i6 : ∀ (U : (liftRingedSite.{u, v, w} X).C) (V : Over U),
      (((liftRingedSite.{u, v, w} X).J.over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{max u v w} := fun U V ↦
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (((liftRingedSite.{u, v, w} X).J.over U).over V)
  have hFl : _root_.SheafOfModules.IsCoherentOnSite (liftModule.{u, v, w} X F) :=
    (isCoherentOnSite_liftModule_iff X F).2 hF
  have hGl : _root_.SheafOfModules.IsCoherentOnSite (liftModule.{u, v, w} X G) :=
    (isCoherentOnSite_liftModule_iff X G).2 hG
  have hfp : (liftModule.{u, v, w} X F).IsFinitePresentation :=
    isFinitePresentation_of_isCoherentOnSite (liftModule.{u, v, w} X F) hFl
  exact (isCoherentOnSite_liftModule_iff X _).1
    (isCoherentOnSite_of_iso (tensorLiftIso X F G)
      (tensorSheaf_isCoherent_of_isFinitePresentation (liftRingedSite.{u, v, w} X)
        (liftModule.{u, v, w} X F) (liftModule.{u, v, w} X G)))

end Stacks.SheafOfModules.TensorLocalProperties

end
