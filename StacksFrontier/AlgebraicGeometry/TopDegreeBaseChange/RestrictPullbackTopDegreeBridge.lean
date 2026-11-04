module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Two spellings of the cohomology upstairs over a compatible pair of opens

Let
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
be a square of schemes, `V` an open of `Y'` and `W` an open of `Y''` whose preimage satisfies
`f''⁻¹(W) ≤ (h')⁻¹(f'⁻¹(V))`. Two expressions for the cohomology of the pulled-back coefficient
over `f''⁻¹(W)` occur in the proof of [Stacks, Tag 0EX3] (c), and they are produced by different
parts of this library:

* `H^d(f''⁻¹(W), ((h')^* F')|)` — the `ℤ`-indexed `Functor.rightDerivedPlus` of the restriction
  to `f''⁻¹(W)` of the pullback along the whole of `h'`, which is the shape the derived-category
  computation of the top degree hands over; and
* `H^d(f''⁻¹(W), (h' ∣)^* (F'|))` — the `ℕ`-indexed `Functor.rightDerived` of the pullback along
  the restricted `h' ∣_{f'⁻¹(V)}^{f''⁻¹(W)}` of the restriction of `F'` to `f'⁻¹(V)`, which is
  the shape the Leray comparison over a pair of affine opens
  (`…TopDegreeBaseChange.cohomologyPullbackIsoTensorCohomologyAffineOpens`) speaks.

This file identifies them. Both discrepancies are already settled elsewhere and are composed
here rather than redone: the indexing by `Stacks.DerivedIndexing.rightDerivedIso`, and the
commutation of restriction with pullback by `Stacks.Modules.restrictPullbackObjIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`: the
  comparison of the two readings above, in every degree, for an arbitrary coefficient `F'` and
  with no hypothesis on the square beyond the inequality naming the fourth open.

## Implementation notes

The inequality `hle` is an explicit argument, as it is in the neighbouring files, so that the
statement names it once instead of repeating a proof of it; any two proofs of an inequality of
opens agree, so a consumer may supply whichever one is at hand.

`AlgebraicGeometry.Scheme.Modules.restrict M g` is a reducible abbreviation for
`(AlgebraicGeometry.Scheme.Modules.restrictFunctor g).obj M`, which is why
`Stacks.Modules.restrictPullbackObjIso` applies to the `restrictFunctor` spelling used here.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The cohomology upstairs over a compatible pair of opens, in its two spellings.** For a
square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an open `V` of `Y'`, an open `W` of `Y''` with `f''⁻¹(W) ≤ (h')⁻¹(f'⁻¹(V))`, an
`𝒪_{X'}`-module `F'` and a degree `d`,

`H^d(f''⁻¹(W), ((h')^* F')|) ≅ H^d(f''⁻¹(W), (h' ∣_{f'⁻¹(V)}^{f''⁻¹(W)})^* (F'|))`

as `Γ(f''⁻¹(W), ⊤)`-modules: on the left the `ℤ`-indexed derived functor of the restriction of
the pullback along the whole of `h'`, on the right the `ℕ`-indexed derived functor of the
pullback along the restricted `h'` of the restriction of `F'`. The two differ by the indexing
of the right derived functors, settled by `Stacks.DerivedIndexing.rightDerivedIso`, and by the
commutation of restriction with pullback, settled by
`Stacks.Modules.restrictPullbackObjIso`. -/
def restrictPullbackRightDerivedPlusIso
    {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} (h' : X'' ⟶ X') {f'' : X'' ⟶ Y''}
    {h : Y'' ⟶ Y'} {V : Y'.Opens} {W : Y''.Opens}
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (d : ℕ) :
    ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (d : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
          ((Scheme.Modules.pullback h').obj F')) ≅
      ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d).obj
        ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) :=
  (Stacks.DerivedIndexing.rightDerivedIso
        (moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)) d).symm.app
      ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pullback h').obj F')) ≪≫
    ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d).mapIso
      (Stacks.Modules.restrictPullbackObjIso h' hle F')

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
