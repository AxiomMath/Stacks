module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Deformation.ToposThickening.ModuleMapObstruction

/-!
# The obstruction to lifting a map of modules across a first order thickening, unconditionally

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, let `F'`, `G'` be `O'`-modules and let `φ : i^*F' ⟶ i^*G'` be `O`-linear. Stacks 08MS
produces a class

```
  o(φ) ∈ Ext¹_O(Li^*F', I·G')
```

whose vanishing is necessary and sufficient for `φ` to lift to an `O'`-linear map `F' ⟶ G'`.

`StacksFrontier/Deformation/ToposThickening/ModuleMapObstruction.lean` constructs this class
relative to a `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback i`, the bundle in which
Stacks 06YY was to supply `Li^*`, so its `Ext` group is taken against whatever functor that
bundle carries. This file removes that argument: the class lives in the `Ext` group against the
derived pullback `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback i` itself, which
exists along every morphism of ringed topoi (Stacks 06YY, with K-flat resolutions from
Stacks 06YS), and the adjunction `Li^* ⊣ Ri_*` it is read across is the unconditional
Stacks 07A6, `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`.

## Main definitions

* `Deformation.ToposThickening.moduleMapLiftObstruction`: the class
  `o(φ) ∈ Ext¹_O(Li^*F', I·G')`.

## Main results

* `Deformation.ToposThickening.moduleMapLiftObstruction_eq_zero_iff`: **Stacks 08MS**, the
  class vanishes exactly when `φ` lifts.

## Implementation notes

The class is the one of `Deformation.ToposThickening.moduleMapObstructionClass` at the datum
`Stacks.Cohomology.DerivedPullbackOfToposHom.kFlatLeftDerivedPullback i`, whose functor is by
definition `derivedPullback i`: the connecting class of `0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0` on the
adjoint transpose of `φ`, an element of `Ext¹_{O'}(F', I·G')`, carried to
`Ext¹_O(Li^*F', I·G')` by `Li^* ⊣ Ri_*` exactly as in the Stacks proof.

`I·G'` is an `O`-module in the source; here it is the descent
`Deformation.ToposThickening.idealProductModule` of the sheaf submodule `I·G'` of `G'` along the
thickening.

The instances beyond those of `ModuleMapObstruction` are `HasSheafify _ (Type w)` on the two
sites, which the existence of `Li^*` (through `kFlatLeftDerivedPullback`) uses to form sheaves of
sets; like the other sheafification instances they only make the categories of the statement
exist.

## References

* [Stacks Project, Tag 08MS](https://stacks.math.columbia.edu/tag/08MS)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Cohomology.DerivedPullbackOfToposHom (derivedPullback kFlatLeftDerivedPullback
  hasLeftDerivedFunctor_pullbackOnHomotopy)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

universe v u v' u' w

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [UnivLE.{u, w}] [UnivLE.{v, w}]
  {i : RingedToposHom X Y}

/-- **The obstruction class `o(φ) ∈ Ext¹_O(Li^*F', I·G')`** of an `O`-linear map
`φ : i^*F' ⟶ i^*G'` along a first order thickening `i` of ringed topoi: the connecting class of
the sequence `0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0` on the adjoint transpose `F' ⟶ i_*i^*G'` of `φ`,
read across the adjunction `Li^* ⊣ Ri_*` of Stacks 07A6. Here `Li^*` is the derived pullback
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback i` of Stacks 06YY. -/
noncomputable def moduleMapLiftObstruction (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G') :
    DerivedCategory.Ext
      ((derivedPullback i).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj F'))
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (idealProductModule hi G').val) 1 :=
  moduleMapObstructionClass hi (kFlatLeftDerivedPullback i) F' G' φ

/-- **Stacks 08MS.** Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed
topoi, let `F'`, `G'` be `O'`-modules and let `φ : i^*F' ⟶ i^*G'` be `O`-linear. The element
`o(φ) ∈ Ext¹_O(Li^*F', I·G')` vanishes if and only if `φ` lifts to an `O'`-linear map
`φ' : F' ⟶ G'`, i.e. one with `i^*φ' = φ`. -/
@[stacks 08MS]
theorem moduleMapLiftObstruction_eq_zero_iff (hi : FirstOrderThickening i)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G') :
    moduleMapLiftObstruction hi F' G' φ = 0 ↔ Nonempty (ModuleMapLift F' G' φ) :=
  moduleMapObstructionClass_eq_zero_iff hi (kFlatLeftDerivedPullback i) F' G' φ

end Deformation.ToposThickening

end
