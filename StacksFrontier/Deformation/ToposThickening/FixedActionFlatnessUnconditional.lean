module

public import StacksFrontier.Deformation.ToposThickening.StrictFlatIdealMap
public import StacksFrontier.Deformation.ToposThickening.FixedActionFlatness
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison
public import StacksFrontier.Deformation.ToposThickening.FlatLiftIdealTensorBridge
public import StacksFrontier.Deformation.ToposThickening.FlatLiftPullbackIdealComparison

/-!
# The flatness of an extension with action map the identity, unconditionally

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --j-->  (Sh(C'), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideals `I = Ker(j^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, and let `ℱ` be an
`O`-module presented on the thickened topos as a `j_*O`-module. Granting that `f'` is flat, that
the square is strict and that `ℱ` is flat over `O_ℬ`, an extension

`0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0`

of Stacks 08MB whose canonical action of the square-zero ideal is the identity of `I ⊗_O ℱ` has
`ℱ'` flat over `O_{ℬ'}`. That implication is
`Deformation.ToposThickening.IsFlatOfFixedActionIdentity`, and this file **proves** it, so that
it is no longer a hypothesis.

## Main results

* `Deformation.ToposThickening.isIso_pullbackBaseIdealMap_of_isFlat`: for a strict square with
  `f'` flat, the canonical map of defining ideals `f^*𝒥 ⟶ I` in the spelling that the first
  factor of Stacks 08MQ is formed from is an isomorphism.
* `Deformation.ToposThickening.isFlatOfFixedActionIdentity`:
  **`Deformation.ToposThickening.IsFlatOfFixedActionIdentity`, proved.**

## How the proof goes

`Deformation.ToposThickening.isFlatOfFixedActionIdentity_of_comparisons` already derives the
statement from three comparisons between the two presentations of Situation 08M7, and each of
the three is available from the hypotheses of `IsFlatOfFixedActionIdentity` itself:

* strictness in the pullback spelling is
  `Deformation.ToposThickening.isStrictPullbackIdealMap_iff_isStrict` applied to the strictness
  hypothesis;
* flatness of `ℱ` over the base in the reduced presentation is
  `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase` applied to the
  flatness hypothesis;
* invertibility of the first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` comes from the flatness of `f'`.
  The map of defining ideals `(f')^*𝒥 ⟶ I` is invertible for a strict square with `f'` flat,
  which is `Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`; the two spellings
  of that map differ by `Deformation.ToposThickening.pullbackIdealIso`, so `f^*𝒥 ⟶ I` is
  invertible too, and tensoring with `ℱ` and comparing the two spellings of the first factor by
  `Deformation.ToposThickening.isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor`
  gives the invertibility that
  `Deformation.ToposThickening.isFlatOfFixedActionIdentity_of_comparisons` consumes.

Nothing here appeals to Stacks 08MQ; the third comparison is the remark `I = f^*𝒥` of
Situation 08VV, got from Stacks 04JC and Stacks 03LU exactly as in
`Deformation.ToposThickening.isIdealComparisonIsoOfFlat`.

Every invertibility step is taken through a lemma carrying its hypotheses explicitly
(`CategoryTheory.isIso_of_isIso_comp_left` and its companions): at the size of
these terms instance search on a composite does not terminate.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
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
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  (j : RingedToposHom X X') (t : RingedToposHom S S') (fb : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hj : FirstOrderThickening j) (ht : FirstOrderThickening t)
  (comm : f'.comp j = t.comp fb)

include comm

/-- **The remark `I = f^*𝒥` of Situation 08VV**, in the spelling the first factor of the
canonical map of Stacks 08MQ is formed from. For a strict morphism of first order thickenings
whose vertical arrow `f'` is flat, the canonical map of defining ideals
`Deformation.ToposThickening.pullbackBaseIdealMap` is an isomorphism.

The induced map `(f')^*𝒥 ⟶ I` of the morphism of thickenings is invertible — surjective because
the square is strict, which is Stacks 08M9, and injective because `(f')^*` is exact for a flat
`f'`, which is Stacks 04JC — and the two spellings differ by the isomorphism
`Deformation.ToposThickening.pullbackIdealIso`. -/
theorem isIso_pullbackBaseIdealMap_of_isFlat (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings j t fb f' hj ht comm).IsStrict) :
    IsIso (pullbackBaseIdealMap j t fb f' hj ht comm) := by
  refine AlgebraicGeometry.RingedSpaceThickening.isIso_of_isIso_comp_left _ _
    (pullbackIdealIso t f' ht).isIso_hom ?_
  rw [pullbackIdealIso_hom_comp_pullbackBaseIdealMap j t fb f' hj ht comm]
  exact (MorphismOfThickenings.ofFirstOrderThickenings j t fb f' hj ht comm).isIso_idealMap
    hf' hstrict

/-- **`Deformation.ToposThickening.IsFlatOfFixedActionIdentity`, proved**: the "if" half of
Stacks 08MQ read per module. Granting that `f'` is flat, that the square is strict and that `ℱ`
is flat over `O_ℬ`, an extension `0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0` over the thickening whose canonical
action of the square-zero ideal is the identity has `ℱ'` flat over `O_{ℬ'}`.

This is `Deformation.ToposThickening.isFlatOfFixedActionIdentity_of_comparisons` with its three
comparison hypotheses supplied: strictness in the pullback spelling, flatness of `ℱ` over the
base in the reduced presentation, and the invertibility of the first factor of the canonical map
of Stacks 08MQ, the last coming from the flatness of `f'` through
`Deformation.ToposThickening.isIso_pullbackBaseIdealMap_of_isFlat`. -/
theorem isFlatOfFixedActionIdentity
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing j))) :
    IsFlatOfFixedActionIdentity j t fb f' hj ht comm F := by
  intro hf' hstrict hflat
  have hcff : IsIso (canonicalFirstFactor j t fb f' hj ht comm F) :=
    (isIso_tensor_pullbackBaseIdealMap_iff_isIso_canonicalFirstFactor
        j t fb f' hj ht comm F).mp
      (Functor.isIso_map_of_isIso _ _
        (isIso_pullbackBaseIdealMap_of_isFlat j t fb f' hj ht comm hf' hstrict))
  exact isFlatOfFixedActionIdentity_of_comparisons hj F t fb f' ht comm
    ((isStrictPullbackIdealMap_iff_isStrict j t fb f' hj ht comm).mpr hstrict)
    (isFlat_reducedBaseModule_of_isFlatOverBase j t fb f' hj ht comm F hflat)
    hcff hf' hstrict hflat

end Deformation.ToposThickening

end
