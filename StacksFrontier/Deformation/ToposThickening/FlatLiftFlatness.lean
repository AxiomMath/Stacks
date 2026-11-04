module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The flatness criterion for infinitesimal deformations of modules on ringed topoi

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, let `ℱ'` be an
`O'`-module and set `ℱ = i^*ℱ'`. Stacks 08MQ says that if `ℱ` is flat over `O_ℬ` and `(f, f')`
is strict, then `ℱ'` is flat over `O_{ℬ'}` if and only if the canonical map
`f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'` is an isomorphism, and that in that case both maps
`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'` are isomorphisms.

## Main results

* `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap_of_isStrict`: **Stacks 08MQ**.

## Implementation notes

The proof is `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`, which states the
lemma with strictness and flatness of `ℱ` over `O_ℬ` in the spellings its proof works with. The
statement here takes both hypotheses in the spellings the rest of the library uses:

* strictness is `Deformation.ToposThickening.MorphismOfThickenings.IsStrict`, Definition 08M9,
  for the square `Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings`; it
  is converted by `Deformation.ToposThickening.isStrictPullbackIdealMap_iff_isStrict`;
* flatness of `ℱ` over `O_ℬ` is `Deformation.ToposThickening.IsFlatOverBase`, flatness over
  `i_*(f⁻¹O_ℬ)`; it is converted by
  `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase`.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **Stacks 08MQ.** Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in
Situation 08M7, let `ℱ'` be an `O'`-module and set `ℱ = i^*ℱ'`. Assume that `ℱ` is flat over
`O_ℬ` and that `(f, f')` is a strict morphism of thickenings (Definition 08M9). Then the
following are equivalent:

1. `ℱ'` is flat over `O_{ℬ'}`, and
2. the canonical map `f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'` is an isomorphism.

Moreover, in this case the maps `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'` are isomorphisms.

How the source's objects are read:

* the square is `Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings`,
  built from the first order thickenings `hi` and `ht` and the commutativity `comm`;
* `O`-modules live on the thickened topos as `i_*O`-modules, as throughout this tree, and
  `ℱ = i^*ℱ'` is presented by the short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0` given by `q`,
  `hq` and `hqex` (the form `Deformation.ToposThickening.HasFlatLift` uses); the statement holds
  for every such presentation;
* "`ℱ` flat over `O_ℬ`" is `Deformation.ToposThickening.IsFlatOverBase`, and "`ℱ'` flat over
  `O_{ℬ'}`" is flatness of `Deformation.ToposThickening.baseModule`, that is, over `f⁻¹O_{ℬ'}`,
  which is the definition the source's proof opens with;
* strictness is `Deformation.ToposThickening.MorphismOfThickenings.IsStrict`, Definition 08M9;
* the canonical map is `Deformation.ToposThickening.canonicalMap`, the composite of
  `Deformation.ToposThickening.canonicalFirstFactor` (`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ`) and
  `Deformation.ToposThickening.canonicalSecondFactor` (`I ⊗_O ℱ ⟶ I·ℱ'`). Its source is written
  `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, which the source's proof identifies with `f^*𝒥 ⊗_O ℱ` ("observe that
  `f^*𝒥 ⊗_O ℱ = f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`"; in this tree
  `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`), and the composite is read
  over `f⁻¹O_{ℬ'}`, the ring over which both factors are linear; being an isomorphism does not
  depend on that reading.

The proof is the source's: strictness gives `ℱ = ℱ'/(f⁻¹𝒥)ℱ'`, and the equivalence is the
flatness criterion of Stacks 08M4 for the square-zero extension `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ`; see
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`. -/
@[stacks 08MQ]
theorem isFlat_iff_isIso_canonicalMap_of_isStrict
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
    (hq : (idealProductSubmodule hi F').ι ≫ q = 0)
    (hqex : (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hF : IsFlatOverBase i f F) :
    (AlgebraicGeometry.SheafOfModules.IsFlat (baseModule f' F') ↔
        IsIso (canonicalMap i t f f' hi ht comm F F' q hq hqex)) ∧
      (IsIso (canonicalMap i t f f' hi ht comm F F' q hq hqex) →
        IsIso (canonicalFirstFactor i t f f' hi ht comm F) ∧
          IsIso (canonicalSecondFactor i hi F F' q hq hqex)) :=
  isFlat_iff_isIso_canonicalMap i t f f' hi ht comm F F' q hq hqex
    ((isStrictPullbackIdealMap_iff_isStrict i t f f' hi ht comm).mpr hstrict)
    (isFlat_reducedBaseModule_of_isFlatOverBase i t f f' hi ht comm F hF)

end Deformation.ToposThickening

end
