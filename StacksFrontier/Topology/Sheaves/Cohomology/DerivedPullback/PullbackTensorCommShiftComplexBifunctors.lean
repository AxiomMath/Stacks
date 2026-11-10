module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoWhisker
public import StacksFrontier.CategoryTheory.CurryPostcomp
import StacksCore.Tactic.StacksAttribute

/-!
# The three bifunctors on cochain complexes of Tag 079U commute with the shifts in both variables

`Stacks.Cohomology.DerivedPullbackTensor.leftComparison` and `rightComparison` are the two
comparisons of [Stacks, Tag 079U] as transformations of functors on *pairs of cochain complexes*
of `𝒪_Y`-modules, with common target `(K, L) ↦ Q(f^*Tot(K ⊗_{𝒪_Y} L))`.  Stating that either of
them is compatible with the shifts needs `CategoryTheory.Functor.CommShift₂` data on the three
bifunctors involved, in curried form, and those are what this file supplies:

* `(K, L) ↦ Lf^*(QK ⊗^L_{𝒪_Y} QL)`, the source of `leftComparison`;
* `(K, L) ↦ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QL)`, the source of `rightComparison`;
* `(K, L) ↦ Q(f^*Tot(K ⊗_{𝒪_Y} L))`, their common target.

The first two are the restrictions along `DerivedCategory.Q` in both variables of the two data
`Stacks.Cohomology.DerivedPullbackTensor.curriedPullbackOfTensor_commShift₂Int` and
`curriedTensorOfPullbacks_commShift₂Int` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorCommShiftTwo.lean`,
exactly
as the two over the K-flat models there are their restrictions along `kFlatQY`.  The third is new:
it is `CategoryTheory.Functor.map₂CochainComplex` for the sheaf tensor product of `Y` —
which carries Mathlib's own `CategoryTheory.Functor.CommShift₂Int` — postcomposed with
`f^*` followed by `Q`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.curryComplexesPullbackOfTensor_commShift₂Int`: the
  source of `leftComparison`, curried.
* `Stacks.Cohomology.DerivedPullbackTensor.curryComplexesTensorOfPullbacks_commShift₂Int`: the
  source of `rightComparison`, curried.
* `Stacks.Cohomology.DerivedPullbackTensor.curryComplexesTotalPullback_commShift₂Int`: their
  common target, curried.
* `Stacks.Cohomology.DerivedPullbackTensor.curryComplexesDerivedTensor_commShift₂Int` and
  `curryComplexesTotal_commShift₂Int`: the source and target of `derivedToTensorNatTrans` on a
  single ringed space, curried — the bifunctors the one factor the two comparisons of Tag 079U
  *share* goes between.

## Implementation notes

**The same three steps as over the K-flat models, for the same reasons.**  Each datum is pinned in
a `def` at the spelling the closure properties of `CategoryTheory.Functor.CommShift₂` match — a
precomposition in each variable for the first two, a postcomposition for the third — then
transported to `CategoryTheory.Functor.curry.obj` of the functor on the product by
`CategoryTheory.Functor.CommShift₂.ofIsoInt` along an isomorphism which is the identity on every
object.  The reason the pinned spelling is needed rather than the curried one is recorded in
`PullbackTensorCommShiftTwo.lean`: `Functor.curry.obj` of a composite differs from the whiskered
composite by a `Functor.map_id` and a `Functor.map_comp`, so instance search does not see the
precomposition.

**Why the target's datum is a postcomposition and not a precomposition.**  `totalComplexPair` is
`CategoryTheory.Functor.uncurry` of `map₂CochainComplex`, so in curried form the target is
`map₂CochainComplex` with `f^* ⋙ Q` applied to the *value* — which is
`CategoryTheory.Functor.CommShift₂.postcompInt`, this development's answer to the postcomposition
`TODO` of `Mathlib/CategoryTheory/Shift/CommShiftTwo.lean`.  The functor being postcomposed is
additive and commutes with the shift: `f^*` degreewise because
`CategoryTheory.Functor.commShiftMapCochainComplex` makes the degreewise extension of any additive
functor shift-compatible, and `Q` because it is a localization of triangulated categories.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### `Lf^*(Q(-) ⊗^L Q(-))`, curried -/

/-- `(K, L) ↦ Lf^*(QK ⊗^L_{𝒪_Y} QL)` on pairs of cochain complexes, in curried form: the
restriction of `curriedPullbackOfTensor` along `DerivedCategory.Q` in both variables. -/
def curriedComplexesPullbackOfTensor :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      DerivedCategory (Modules X) :=
  DerivedCategory.Q ⋙ (curriedPullbackOfTensor f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))).obj
      DerivedCategory.Q)

/-- The restriction of `Lf^*(- ⊗^L -)` to pairs of cochain complexes commutes with the shifts in
both variables. -/
@[instance_reducible]
def curriedComplexesPullbackOfTensor_commShift₂Int :
    (curriedComplexesPullbackOfTensor f).CommShift₂Int :=
  haveI := curriedPullbackOfTensor_commShift₂Int f
  inferInstanceAs ((DerivedCategory.Q ⋙ (curriedPullbackOfTensor f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
      (DerivedCategory (Modules X))).obj DerivedCategory.Q)).CommShift₂Int)

/-- **The pinned complex-level form is the currying of `Q × Q ⋙ pullbackOfTensor f`.** -/
def curryComplexesPullbackOfTensorIso :
    curriedComplexesPullbackOfTensor f ≅
      Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ pullbackOfTensor f) :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight (curryPullbackOfTensorIso f)
        ((Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
          (DerivedCategory (Modules X))).obj DerivedCategory.Q)) ≪≫
    (Functor.curryObjProdComp DerivedCategory.Q DerivedCategory.Q (pullbackOfTensor f)).symm

/-- **The source of `leftComparison`, curried, commutes with the shifts in both variables.** -/
@[instance_reducible]
def curryComplexesPullbackOfTensor_commShift₂Int :
    (Functor.curry.obj
      (DerivedCategory.Q.prod DerivedCategory.Q ⋙ pullbackOfTensor f)).CommShift₂Int :=
  haveI := curriedComplexesPullbackOfTensor_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryComplexesPullbackOfTensorIso f)

/-! ### `Lf^*(Q(-)) ⊗^L Lf^*(Q(-))`, curried -/

/-- `(K, L) ↦ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QL)` on pairs of cochain complexes, in curried form. -/
def curriedComplexesTensorOfPullbacks :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      DerivedCategory (Modules X) :=
  DerivedCategory.Q ⋙ (curriedTensorOfPullbacks f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y)) (DerivedCategory (Modules X))).obj
      DerivedCategory.Q)

/-- The restriction of `Lf^*(-) ⊗^L Lf^*(-)` to pairs of cochain complexes commutes with the
shifts in both variables. -/
@[instance_reducible]
def curriedComplexesTensorOfPullbacks_commShift₂Int :
    (curriedComplexesTensorOfPullbacks f).CommShift₂Int :=
  haveI := curriedTensorOfPullbacks_commShift₂Int f
  inferInstanceAs ((DerivedCategory.Q ⋙ (curriedTensorOfPullbacks f ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
      (DerivedCategory (Modules X))).obj DerivedCategory.Q)).CommShift₂Int)

/-- **The pinned complex-level form is the currying of `Q × Q ⋙ tensorOfPullbacks f`.** -/
def curryComplexesTensorOfPullbacksIso :
    curriedComplexesTensorOfPullbacks f ≅
      Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ tensorOfPullbacks f) :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight (curryTensorOfPullbacksIso f)
        ((Functor.whiskeringLeft _ (DerivedCategory (Modules Y))
          (DerivedCategory (Modules X))).obj DerivedCategory.Q)) ≪≫
    (Functor.curryObjProdComp DerivedCategory.Q DerivedCategory.Q (tensorOfPullbacks f)).symm

/-- **The source of `rightComparison`, curried, commutes with the shifts in both variables.** -/
@[instance_reducible]
def curryComplexesTensorOfPullbacks_commShift₂Int :
    (Functor.curry.obj
      (DerivedCategory.Q.prod DerivedCategory.Q ⋙ tensorOfPullbacks f)).CommShift₂Int :=
  haveI := curriedComplexesTensorOfPullbacks_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryComplexesTensorOfPullbacksIso f)

/-! ### `Q(f^*Tot(- ⊗ -))`, curried -/

/-- `Tot(- ⊗_{𝒪_Y} -)` on pairs of cochain complexes, with the structure sheaf of `Y` named at
the *pullback* development's spelling.  Pinning it is what lets it be composed with
`pullbackComplex f`: `CategoryTheory.Functor.map₂CochainComplex` names the structure sheaf at the
tensor development's spelling, and the two are the same sheaf only up to the reducibility
attributes above, which a `Functor.whiskeringRight` whose categories are elaborated afresh does
not get the benefit of. -/
abbrev tensorComplexBifunctor :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      CochainComplex (Modules Y) ℤ :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map₂CochainComplex

/-- `(K, L) ↦ Q(f^*Tot(K ⊗_{𝒪_Y} L))` on pairs of cochain complexes, in curried form: the
bifunctor on cochain complexes induced by the sheaf tensor product of `Y`, postcomposed with the
degreewise pullback and the localization. -/
def curriedComplexesTotalPullback :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      DerivedCategory (Modules X) :=
  tensorComplexBifunctor (Y := Y) ⋙
    (Functor.whiskeringRight _ _ _).obj (pullbackComplex f ⋙ DerivedCategory.Q)

/-- `Q(f^*Tot(- ⊗ -))` commutes with the shifts in both variables: this is
`CategoryTheory.Functor.CommShift₂.postcompInt` at Mathlib's
`CategoryTheory.Functor.map₂CochainComplex.CommShift₂Int`. -/
@[instance_reducible]
def curriedComplexesTotalPullback_commShift₂Int :
    (curriedComplexesTotalPullback f).CommShift₂Int :=
  Functor.CommShift₂.postcompInt (tensorComplexBifunctor (Y := Y))
    (pullbackComplex f ⋙ DerivedCategory.Q)

/-- **The pinned complex-level form is the currying of
`totalComplexPair ⋙ pullbackComplex f ⋙ Q`.** -/
def curryComplexesTotalPullbackIso :
    curriedComplexesTotalPullback f ≅
      Functor.curry.obj
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
          pullbackComplex f ⋙ DerivedCategory.Q) :=
  Functor.curryObjUncurryObjCompIso (tensorComplexBifunctor (Y := Y))
    (pullbackComplex f ⋙ DerivedCategory.Q)

/-- **The common target of the two comparisons, curried, commutes with the shifts in both
variables.** -/
@[instance_reducible]
def curryComplexesTotalPullback_commShift₂Int :
    (Functor.curry.obj
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
        pullbackComplex f ⋙ DerivedCategory.Q)).CommShift₂Int :=
  haveI := curriedComplexesTotalPullback_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryComplexesTotalPullbackIso f)

/-! ### `Q(-) ⊗^L Q(-)` and `Q(Tot(- ⊗ -))` on one ringed space, curried

These are the source and target of `derivedToTensorNatTrans`, which is the one factor the two
comparisons of Tag 079U share.  They are stated for a single ringed space `Z`, since
`leftComparison` uses them at `Y` and `rightComparison` at `X`. -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `(K, L) ↦ QK ⊗^L_{𝒪_Z} QL` on pairs of cochain complexes, in curried form: the derived tensor
product of `Z` restricted along `DerivedCategory.Q` in both variables. -/
def curriedComplexesDerivedTensor :
    CochainComplex (Modules Z) ℤ ⥤ CochainComplex (Modules Z) ℤ ⥤
      DerivedCategory (Modules Z) :=
  DerivedCategory.Q ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf ⋙
    (Functor.whiskeringLeft _ (DerivedCategory (Modules Z)) (DerivedCategory (Modules Z))).obj
      DerivedCategory.Q)

/-- The restriction of `- ⊗^L -` to pairs of cochain complexes commutes with the shifts in both
variables. -/
@[instance_reducible]
def curriedComplexesDerivedTensor_commShift₂Int :
    (curriedComplexesDerivedTensor Z).CommShift₂Int :=
  haveI := derivedTensorCommShift₂Int Z
  inferInstanceAs ((DerivedCategory.Q ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf ⋙
      (Functor.whiskeringLeft _ (DerivedCategory (Modules Z))
        (DerivedCategory (Modules Z))).obj DerivedCategory.Q)).CommShift₂Int)

/-- **The pinned complex-level form is the currying of `Q × Q ⋙ (- ⊗^L -)`.** -/
def curryComplexesDerivedTensorIso :
    curriedComplexesDerivedTensor Z ≅
      Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)) :=
  NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)
      (by simp [curriedComplexesDerivedTensor]))
    (fun _ => by
      ext
      simp [curriedComplexesDerivedTensor])

/-- **The source of `derivedToTensorNatTrans`, curried, commutes with the shifts in both
variables.** -/
@[instance_reducible]
def curryComplexesDerivedTensor_commShift₂Int :
    (Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))).CommShift₂Int :=
  haveI := curriedComplexesDerivedTensor_commShift₂Int Z
  Functor.CommShift₂.ofIsoInt (curryComplexesDerivedTensorIso Z)

/-- `Tot(- ⊗_{𝒪_Z} -)` on pairs of cochain complexes, with the structure sheaf of `Z` named at
the pullback development's spelling; the one-space analogue of `tensorComplexBifunctor`. -/
abbrev tensorComplexBifunctorOn :
    CochainComplex (Modules Z) ℤ ⥤ CochainComplex (Modules Z) ℤ ⥤
      CochainComplex (Modules Z) ℤ :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map₂CochainComplex

/-- `(K, L) ↦ Q(Tot(K ⊗_{𝒪_Z} L))` on pairs of cochain complexes, in curried form. -/
def curriedComplexesTotal :
    CochainComplex (Modules Z) ℤ ⥤ CochainComplex (Modules Z) ℤ ⥤
      DerivedCategory (Modules Z) :=
  tensorComplexBifunctorOn Z ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

/-- `Q(Tot(- ⊗ -))` commutes with the shifts in both variables, by
`CategoryTheory.Functor.CommShift₂.postcompInt`. -/
@[instance_reducible]
def curriedComplexesTotal_commShift₂Int :
    (curriedComplexesTotal Z).CommShift₂Int :=
  Functor.CommShift₂.postcompInt (tensorComplexBifunctorOn Z) DerivedCategory.Q

/-- **The pinned complex-level form is the currying of `totalComplexPair ⋙ Q`.** -/
def curryComplexesTotalIso :
    curriedComplexesTotal Z ≅
      Functor.curry.obj
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
          DerivedCategory.Q) :=
  Functor.curryObjUncurryObjCompIso (tensorComplexBifunctorOn Z) DerivedCategory.Q

/-- **The target of `derivedToTensorNatTrans`, curried, commutes with the shifts in both
variables.** -/
@[instance_reducible]
def curryComplexesTotal_commShift₂Int :
    (Functor.curry.obj
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
        DerivedCategory.Q)).CommShift₂Int :=
  haveI := curriedComplexesTotal_commShift₂Int Z
  Functor.CommShift₂.ofIsoInt (curryComplexesTotalIso Z)

end OneSpace

/-! ### The two intermediate bifunctors of `rightComparison`, curried

The three data above are the *ends* of the two comparisons.  `rightComparison f` is a chain of
four bifunctors, and its two junctions are the source and target of the middle factor
`Functor.whiskerLeft ((pullbackComplex f).prod (pullbackComplex f)) (derivedToTensorNatTrans X)`:
the derived tensor product of `X` and the ordinary total tensor complex of `X`, each restricted
along the degreewise pullback in both variables.  So each junction is one of the two bifunctors of
`OneSpace` at `Z = X` precomposed with `pullbackComplex f` twice, which is
`CategoryTheory.Functor.CommShift₂.precomp₁` over `precomp₂`, and each is then transported to the
`CategoryTheory.Functor.curry.obj` spelling the curried chain is written at by
`CategoryTheory.Functor.CommShift₂.ofIsoInt` along the currying of a product precomposition —
the same two steps as for the ends, with `CategoryTheory.Functor.curryObjProdComp` in place of
`curryObjUncurryObjCompIso`. -/

/-- `(K, L) ↦ Q(f^*K) ⊗^L_{𝒪_X} Q(f^*L)` on pairs of cochain complexes of `𝒪_Y`-modules, in
curried form: the complex-level derived tensor product of `X` precomposed with the degreewise
pullback in both variables. -/
def curriedComplexesTensorOfPullbackComplexes :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      DerivedCategory (Modules X) :=
  pullbackComplex f ⋙ (curriedComplexesDerivedTensor X ⋙
    (Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
      (DerivedCategory (Modules X))).obj (pullbackComplex f))

/-- `Q(f^*(-)) ⊗^L Q(f^*(-))` commutes with the shifts in both variables: this is
`CategoryTheory.Functor.CommShift₂.precomp₁` after `precomp₂` at
`curriedComplexesDerivedTensor_commShift₂Int` for `X`. -/
@[instance_reducible]
def curriedComplexesTensorOfPullbackComplexes_commShift₂Int :
    (curriedComplexesTensorOfPullbackComplexes f).CommShift₂Int :=
  haveI := curriedComplexesDerivedTensor_commShift₂Int X
  Functor.CommShift₂.precomp₁ (pullbackComplex f)
    (curriedComplexesDerivedTensor X ⋙
      (Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
        (DerivedCategory (Modules X))).obj (pullbackComplex f))
    CommShift₂Setup.int

/-- **The pinned complex-level form is the currying of `f^* × f^* ⋙ Q × Q ⋙ (- ⊗^L -)`.** -/
def curryComplexesTensorOfPullbackComplexesIso :
    curriedComplexesTensorOfPullbackComplexes f ≅
      Functor.curry.obj ((pullbackComplex f).prod (pullbackComplex f) ⋙
        DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) :=
  Functor.isoWhiskerLeft (pullbackComplex f)
      (Functor.isoWhiskerRight (curryComplexesDerivedTensorIso X)
        ((Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
          (DerivedCategory (Modules X))).obj (pullbackComplex f))) ≪≫
    (Functor.curryObjProdComp (pullbackComplex f) (pullbackComplex f)
      (DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))).symm

/-- **The source of the middle factor of `rightComparison`, curried, commutes with the shifts in
both variables.** -/
@[instance_reducible]
def curryComplexesTensorOfPullbackComplexes_commShift₂Int :
    (Functor.curry.obj ((pullbackComplex f).prod (pullbackComplex f) ⋙
      DerivedCategory.Q.prod DerivedCategory.Q ⋙ Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))).CommShift₂Int :=
  haveI := curriedComplexesTensorOfPullbackComplexes_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryComplexesTensorOfPullbackComplexesIso f)

/-- `(K, L) ↦ Q(Tot(f^*K ⊗_{𝒪_X} f^*L))` on pairs of cochain complexes of `𝒪_Y`-modules, in
curried form: the complex-level total tensor complex of `X` precomposed with the degreewise
pullback in both variables. -/
def curriedComplexesTotalOfPullbackComplexes :
    CochainComplex (Modules Y) ℤ ⥤ CochainComplex (Modules Y) ℤ ⥤
      DerivedCategory (Modules X) :=
  pullbackComplex f ⋙ (curriedComplexesTotal X ⋙
    (Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
      (DerivedCategory (Modules X))).obj (pullbackComplex f))

/-- `Q(Tot(f^*(-) ⊗ f^*(-)))` commutes with the shifts in both variables: this is
`CategoryTheory.Functor.CommShift₂.precomp₁` after `precomp₂` at
`curriedComplexesTotal_commShift₂Int` for `X`. -/
@[instance_reducible]
def curriedComplexesTotalOfPullbackComplexes_commShift₂Int :
    (curriedComplexesTotalOfPullbackComplexes f).CommShift₂Int :=
  haveI := curriedComplexesTotal_commShift₂Int X
  Functor.CommShift₂.precomp₁ (pullbackComplex f)
    (curriedComplexesTotal X ⋙
      (Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
        (DerivedCategory (Modules X))).obj (pullbackComplex f))
    CommShift₂Setup.int

/-- **The pinned complex-level form is the currying of
`f^* × f^* ⋙ totalComplexPair ⋙ Q`.** -/
def curryComplexesTotalOfPullbackComplexesIso :
    curriedComplexesTotalOfPullbackComplexes f ≅
      Functor.curry.obj ((pullbackComplex f).prod (pullbackComplex f) ⋙
        totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) ⋙
          DerivedCategory.Q) :=
  Functor.isoWhiskerLeft (pullbackComplex f)
      (Functor.isoWhiskerRight (curryComplexesTotalIso X)
        ((Functor.whiskeringLeft _ (CochainComplex (Modules X) ℤ)
          (DerivedCategory (Modules X))).obj (pullbackComplex f))) ≪≫
    (Functor.curryObjProdComp (pullbackComplex f) (pullbackComplex f)
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) ⋙
        DerivedCategory.Q)).symm

/-- **The target of the middle factor of `rightComparison`, curried, commutes with the shifts in
both variables.** -/
@[instance_reducible]
def curryComplexesTotalOfPullbackComplexes_commShift₂Int :
    (Functor.curry.obj ((pullbackComplex f).prod (pullbackComplex f) ⋙
      totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) ⋙
        DerivedCategory.Q)).CommShift₂Int :=
  haveI := curriedComplexesTotalOfPullbackComplexes_commShift₂Int f
  Functor.CommShift₂.ofIsoInt (curryComplexesTotalOfPullbackComplexesIso f)

end Stacks.Cohomology.DerivedPullbackTensor

end
