module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.StrictFlatIdealMap

/-!
# The remark `I = f^*J` of Situation 08VV, tensored with a module

For a strict morphism `(f, f')` of first order thickenings of ringed topoi whose vertical arrow
`f'` is flat, the canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` of condition (1) of Stacks 08MV is an
isomorphism. This is the consequence of Stacks 08MQ that part (1) of Stacks 08VW consumes, named
`Deformation.ToposThickening.IsIdealComparisonIsoOfFlat` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean`; it is proved here, so that
no statement downstream needs to carry it.

## Main results

* `Deformation.ToposThickening.isIdealComparisonIsoOfFlat`: the predicate
  `IsIdealComparisonIsoOfFlat` holds for every module.

## Implementation notes

The induced map of defining ideals `f^*J ⟶ I` is itself invertible — surjective because the
square is strict, which is Stacks 08M9, and injective because `(f')^*` is exact for a flat `f'`,
which is Stacks 04JC; that is
`Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`. The canonical map of
condition (1) is its image under tensoring with `ℱ`.

## References

* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **The remark `I = f^*J` of Situation 08VV, in the tensored form part (1) of Stacks 08VW
uses.** For a strict morphism of first order thickenings whose vertical arrow `f'` is flat, the
canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` is an isomorphism: it is the image under tensoring with `ℱ` of
the induced map of defining ideals, which is invertible by
`Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`. -/
theorem isIdealComparisonIsoOfFlat (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    IsIdealComparisonIsoOfFlat i t f f' hi ht comm F := by
  intro hf' hstrict
  have := (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).isIso_idealMap
    hf' hstrict
  exact Functor.map_isIso _
    (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap

end Deformation.ToposThickening

end
