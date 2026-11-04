module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineChosenPullback
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineModuleCancelBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StackReduction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineFamily

/-!
# Descent data for quasi-coherent modules along `Spec B ⟶ Spec R`

For a ring map `R → B`, this file compares the descent data of
`Stacks.Descent.qcohPseudofunctor` for the one-element family `Spec B ⟶ Spec R` with the module
descent data `ModuleCat.DescentData` for `R → B`, in the direction from module descent data to
geometric ones.

## Main results

* `Stacks.Descent.qcohPseudofunctor_map_specMap`: the pullback functors of
  `Stacks.Descent.qcohPseudofunctor` along a morphism of affine schemes are
  `Stacks.Descent.pullbackQcoh`.
* `Stacks.Descent.specTensorDescentDataEquivalence`: the descent data of
  `Stacks.Descent.qcohPseudofunctor` for the one-element family `Spec B ⟶ Spec R` are the descent
  data expressed over the chosen pullbacks `Spec (B ⊗[R] B)` and `Spec (B ⊗[R] (B ⊗[R] B))`.
* `Stacks.Descent.extendScalarsTransitionEquiv`: for a `B`-module `N`, the transition morphisms
  of such a descent datum at `N^~` are exactly the `B ⊗[R] B`-linear maps between the two
  extensions of scalars of `N` along `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`.
* `Stacks.Descent.extendScalarsTransitionEquiv_hom`: that bijection carries an isomorphism of
  the two extensions of scalars to the underlying morphism of an explicit isomorphism of the two
  pullbacks.
* `Stacks.Descent.extendScalarsInlSourceIso` and `Stacks.Descent.extendScalarsInrTargetIso`: the
  extension of scalars of a `B`-module `N` along `b ↦ b ⊗ 1` is
  `ModuleCat.restrictModule R B N ⊗[R] B` with the `B ⊗[R] B`-action of
  `ModuleCat.sourceTensorModule`, and its extension of scalars along `b ↦ 1 ⊗ b` is
  `B ⊗[R] ModuleCat.restrictModule R B N` with the action of `ModuleCat.targetTensorModule`.
* `Stacks.Descent.extendScalarsTransitionOfDescentData`,
  `Stacks.Descent.specTransitionIsoOfDescentData` and
  `Stacks.Descent.specSingletonHomOfDescentData`: the transition data over
  `Stacks.Descent.specSingletonSq` attached to a module descent datum `D`, namely
  `ModuleCat.DescentData.transition` conjugated by those two isomorphisms and transported by
  `Stacks.Descent.extendScalarsTransitionEquiv`;
  `Stacks.Descent.specTransitionIsoOfDescentData_hom` identifies the geometric transition with the
  image of the algebraic one.
* `Stacks.Descent.pullHom'_self_of_pullHom'_comp`: the unit condition of
  `CategoryTheory.Pseudofunctor.DescentData'` follows from its cocycle condition, for an
  arbitrary pseudofunctor, as soon as the transition morphisms are isomorphisms.
* `Stacks.Descent.smulOneTmulMap`: the comparison of `A ⊗[R] N` with an extension of scalars of
  `N`, for a ring map out of an `R`-algebra `A`.
* `Stacks.Descent.extendScalarsTripleTransition` and
  `Stacks.Descent.extendScalarsTripleTransition_comp`: the cocycle condition of a module descent
  datum read over `B ⊗[R] (B ⊗[R] B)`, as an identity between the three base changes of
  `ModuleCat.DescentData.transition` along `Stacks.Descent.tensorMap₀₁`,
  `Stacks.Descent.tensorMap₁₂` and `Stacks.Descent.tensorMap₀₂`, each read as a morphism between
  the direct extensions of scalars of `D.module` along the three inclusions of `B`.
* `Stacks.Descent.specSingletonDescentData'`: the descent datum of
  `Stacks.Descent.qcohPseudofunctor` for the one-element family attached to a module descent
  datum, assuming the cocycle condition `Stacks.Descent.SpecSingletonCocycle`; its unit condition
  is `Stacks.Descent.specSingletonPullHom'_self`.

## Implementation notes

The `Module B (B ⊗[R] B)` that `ModuleCat.extendScalars` uses is
`Module.compHom _ (tensorInl R B).hom`, which is not definitionally the one coming from
`Algebra.TensorProduct.leftAlgebra`. No second `Algebra B (B ⊗[R] B)` is named:
`Stacks.Descent.tensorInlModule` and `Stacks.Descent.tensorInrModule` are `B ⊗[R] B` as a
`B`-module through `b ↦ b ⊗ 1` and through `b ↦ 1 ⊗ b`, each written as a
`ModuleCat.restrictScalars`, so the two module structures live on different `ModuleCat B`
objects. The forward comparisons `Stacks.Descent.sourceModelHom` and
`Stacks.Descent.targetModelHom` are `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars`
of the `B`-linear units `n ↦ n ⊗ 1` and `n ↦ 1 ⊗ n`; the inverses are `TensorProduct.lift` over
`R` into the restriction of scalars `Stacks.Descent.tensorInlTargetR`, upgraded to
`B ⊗[R] B`-linear maps.

Every element-level statement takes its module argument at `ModuleCat.restrictModule R B N`
rather than at `N`, even though the two carriers are definitionally equal: a term of type `↑N` in
a position declared `↑(ModuleCat.restrictModule R B N)` is not type-correct at implicit
transparency, so `rw` refuses it.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite
  TensorProduct
open Pseudofunctor.LocallyDiscreteOpToCat

universe t v' v u' u

namespace Stacks.Descent

/-- The pullback functors of `Stacks.Descent.qcohPseudofunctor` along a morphism of affine
schemes are `Stacks.Descent.pullbackQcoh`.  See the implementation notes. -/
theorem qcohPseudofunctor_map_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (qcohPseudofunctor.map (Spec.map φ).op.toLoc).toFunctor = pullbackQcoh φ :=
  rfl

/-- The quasi-coherent module `N^~` on `Spec B` attached to a `B`-module `N`. -/
abbrev tildeQcoh (B : Type u) [CommRing B] (N : ModuleCat.{u} B) :
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of B)).ringCatSheaf).FullSubcategory :=
  (tildeEquiv (R := CommRingCat.of B)).functor.obj N

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The one-element covering family consisting of `Spec B ⟶ Spec R`. -/
abbrev specSingleton :
    PUnit.{u + 1} → (Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :=
  fun _ ↦ Spec.map (algHom R B)

/-- The chosen pullbacks `Spec (B ⊗[R] B)` for the one-element family `Spec B ⟶ Spec R`. -/
abbrev specSingletonSq (i j : PUnit.{u + 1}) :
    ChosenPullback (specSingleton R B i) (specSingleton R B j) :=
  specTensorChosenPullback R B

/-- The chosen threefold wide pullbacks `Spec (B ⊗[R] (B ⊗[R] B))` for the one-element family
`Spec B ⟶ Spec R`. -/
abbrev specSingletonSq₃ (i j k : PUnit.{u + 1}) :
    ChosenPullback₃ (specSingletonSq R B i j) (specSingletonSq R B j k)
      (specSingletonSq R B i k) :=
  specTensorChosenPullback₃ R B

/-- Descent data for quasi-coherent modules along `Spec B ⟶ Spec R`, over the chosen tensor
pullbacks `Stacks.Descent.specTensorChosenPullback` and
`Stacks.Descent.specTensorChosenPullback₃`: a descent datum is a quasi-coherent module on
`Spec B` together with a transition morphism over `Spec (B ⊗[R] B)` satisfying the cocycle
condition over `Spec (B ⊗[R] (B ⊗[R] B))`. -/
def specTensorDescentDataEquivalence :
    qcohPseudofunctor.DescentData' (specSingletonSq R B) (specSingletonSq₃ R B) ≌
      qcohPseudofunctor.DescentData (specSingleton R B) :=
  Pseudofunctor.DescentData'.descentDataEquivalence _ _ _

/-- The pullback of `N^~` to `Spec (B ⊗[R] B)` along the first inclusion is the extension of
scalars of `N` along `b ↦ b ⊗ 1`. -/
def tildeExtendScalarsInlIso (N : ModuleCat.{u} B) :
    (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.obj
        ((ModuleCat.extendScalars (tensorInl R B).hom).obj N) ≅
      (pullbackQcoh (tensorInl R B)).obj (tildeQcoh B N) :=
  (extendScalarsCompTildeEquivIso (tensorInl R B)).app N

/-- The comparison of `Stacks.Descent.tildeExtendScalarsInlIso` at the second inclusion. -/
def tildeExtendScalarsInrIso (N : ModuleCat.{u} B) :
    (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.obj
        ((ModuleCat.extendScalars (tensorInr R B).hom).obj N) ≅
      (pullbackQcoh (tensorInr R B)).obj (tildeQcoh B N) :=
  (extendScalarsCompTildeEquivIso (tensorInr R B)).app N

/-- For a `B`-module `N`, morphisms from the pullback of `N^~` along `b ↦ b ⊗ 1` to its pullback
along `b ↦ 1 ⊗ b` — the type of the `hom` field of `CategoryTheory.Pseudofunctor.DescentData'`
at the chosen pullback `Spec (B ⊗[R] B)` — are exactly morphisms between the two extensions of
scalars of `N`. -/
def extendScalarsTransitionEquiv (N : ModuleCat.{u} B) :
    ((ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
        (ModuleCat.extendScalars (tensorInr R B).hom).obj N) ≃
      ((qcohPseudofunctor.map (Spec.map (tensorInl R B)).op.toLoc).toFunctor.obj
          (tildeQcoh B N) ⟶
        (qcohPseudofunctor.map (Spec.map (tensorInr R B)).op.toLoc).toFunctor.obj
          (tildeQcoh B N)) :=
  (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (tildeExtendScalarsInlIso R B N) (tildeExtendScalarsInrIso R B N))

/-- The value of `Stacks.Descent.extendScalarsTransitionEquiv`. -/
theorem extendScalarsTransitionEquiv_apply (N : ModuleCat.{u} B)
    (α : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N) :
    extendScalarsTransitionEquiv R B N α =
      (tildeExtendScalarsInlIso R B N).inv ≫
        (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.map α ≫
          (tildeExtendScalarsInrIso R B N).hom :=
  rfl

/-- `Stacks.Descent.extendScalarsTransitionEquiv` carries isomorphisms to isomorphisms: the
transition attached to an isomorphism of the two extensions of scalars is the underlying morphism
of an explicit isomorphism of the two pullbacks. -/
theorem extendScalarsTransitionEquiv_hom (N : ModuleCat.{u} B)
    (e : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N) :
    extendScalarsTransitionEquiv R B N e.hom =
      ((tildeExtendScalarsInlIso R B N).symm ≪≫
        (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.mapIso e ≪≫
          tildeExtendScalarsInrIso R B N).hom :=
  rfl

/-! ### The dictionary between `ModuleCat.extendScalars` and `ModuleCat.DescentData`

The two pullbacks of a `B`-module `N` to `Spec (B ⊗[R] B)` have two models:
`ModuleCat.extendScalars` of `N` along `Stacks.Descent.tensorInl` and
`Stacks.Descent.tensorInr`, and `ModuleCat.restrictModule R B N ⊗[R] B` and
`B ⊗[R] ModuleCat.restrictModule R B N`. This section identifies them. -/

/-- `B ⊗[R] B` as a `B`-module through `b ↦ b ⊗ 1`, as a restriction of scalars. -/
abbrev tensorInlModule : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (tensorInl R B).hom).obj
    (ModuleCat.of (B ⊗[R] B) (B ⊗[R] B))

/-- `B ⊗[R] B` as a `B`-module through `b ↦ 1 ⊗ b`. -/
abbrev tensorInrModule : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (tensorInr R B).hom).obj
    (ModuleCat.of (B ⊗[R] B) (B ⊗[R] B))

/-- An element of `B ⊗[R] B` read in `Stacks.Descent.tensorInlModule`. -/
def toTensorInlModule (t : B ⊗[R] B) : (tensorInlModule R B : Type u) := t

/-- An element of `B ⊗[R] B` read in `Stacks.Descent.tensorInrModule`. -/
def toTensorInrModule (t : B ⊗[R] B) : (tensorInrModule R B : Type u) := t

/-- The `B ⊗[R] B`-action on `Stacks.Descent.tensorInlModule` is multiplication. -/
theorem smul_toTensorInlModule (x t : B ⊗[R] B) :
    x • toTensorInlModule R B t = toTensorInlModule R B (x * t) := rfl

/-- The `B ⊗[R] B`-action on `Stacks.Descent.tensorInrModule` is multiplication. -/
theorem smul_toTensorInrModule (x t : B ⊗[R] B) :
    x • toTensorInrModule R B t = toTensorInrModule R B (x * t) := rfl

/-- An element `b : B` acts on `Stacks.Descent.tensorInlModule` as multiplication by `b ⊗ 1`. -/
theorem smul_toTensorInlModule_left (b : B) (t : B ⊗[R] B) :
    b • toTensorInlModule R B t = toTensorInlModule R B ((b ⊗ₜ[R] (1 : B)) * t) := rfl

/-- An element `b : B` acts on `Stacks.Descent.tensorInrModule` as multiplication by `1 ⊗ b`. -/
theorem smul_toTensorInrModule_left (b : B) (t : B ⊗[R] B) :
    b • toTensorInrModule R B t = toTensorInrModule R B (((1 : B) ⊗ₜ[R] b) * t) := rfl

/-- `Stacks.Descent.toTensorInlModule` is additive. -/
theorem toTensorInlModule_add (t t' : B ⊗[R] B) :
    toTensorInlModule R B (t + t') = toTensorInlModule R B t + toTensorInlModule R B t' := rfl

/-- `Stacks.Descent.toTensorInrModule` is additive. -/
theorem toTensorInrModule_add (t t' : B ⊗[R] B) :
    toTensorInrModule R B (t + t') = toTensorInrModule R B t + toTensorInrModule R B t' := rfl

/-- The structure map `R → B ⊗[R] B` sends `r` to `r ⊗ 1`. -/
theorem algebraMap_tensorProduct (r : R) :
    (algebraMap R (B ⊗[R] B)) r = (algebraMap R B r) ⊗ₜ[R] (1 : B) :=
  Algebra.TensorProduct.algebraMap_apply r

/-- The element `1 ⊗ r` of `B ⊗[R] B` is the image of `r` under the structure map. -/
theorem one_tmul_algebraMap (r : R) :
    (((1 : B) ⊗ₜ[R] (algebraMap R B r)) : B ⊗[R] B) = (algebraMap R (B ⊗[R] B)) r :=
  (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B)).commutes r

/-- In `B ⊗[R] B`, `1 ⊗ (r • c)` is the product of the image of `r` with `1 ⊗ c`. -/
theorem one_tmul_smul (r : R) (c : B) :
    ((1 : B) ⊗ₜ[R] (r • c) : B ⊗[R] B) =
      (algebraMap R (B ⊗[R] B)) r * ((1 : B) ⊗ₜ[R] c) := by
  rw [algebraMap_tensorProduct, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- In `B ⊗[R] B`, `(r • c) ⊗ 1` is the product of the image of `r` with `c ⊗ 1`. -/
theorem tmul_one_smul (r : R) (c : B) :
    (((r • c) ⊗ₜ[R] (1 : B)) : B ⊗[R] B) =
      (algebraMap R (B ⊗[R] B)) r * (c ⊗ₜ[R] (1 : B)) := by
  rw [algebraMap_tensorProduct, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact congrArg (fun z : B => z ⊗ₜ[R] (1 : B)) (Algebra.smul_def r c)

variable (N : ModuleCat.{u} B)

/-! #### The comparison at `tensorInl` -/

/-- A pure tensor of `(ModuleCat.extendScalars (tensorInl R B).hom).obj N`. -/
def tensorInlElt (t : (tensorInlModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((ModuleCat.extendScalars (tensorInl R B).hom).obj N : Type u) :=
  t ⊗ₜ[B] (show (N : Type u) from n)

/-- `B ⊗[R] B` acts on `Stacks.Descent.tensorInlElt` through its first argument. -/
theorem tensorInlElt_smul (x : B ⊗[R] B) (t : (tensorInlModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    x • tensorInlElt R B N t n = tensorInlElt R B N (x • t) n := rfl

/-- A scalar `b : B` moves across the tensor sign in `Stacks.Descent.tensorInlElt`. -/
theorem tensorInlElt_smul_right (t : (tensorInlModule R B : Type u)) (b : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInlElt R B N t (b • n) = tensorInlElt R B N (b • t) n :=
  (TensorProduct.smul_tmul b t (show (N : Type u) from n)).symm

/-- `Stacks.Descent.tensorInlElt` is additive in its first argument. -/
theorem tensorInlElt_add_left (t t' : (tensorInlModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInlElt R B N (t + t') n = tensorInlElt R B N t n + tensorInlElt R B N t' n :=
  TensorProduct.add_tmul _ _ _

/-- `Stacks.Descent.tensorInlElt` is additive in its second argument. -/
theorem tensorInlElt_add_right (t : (tensorInlModule R B : Type u))
    (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInlElt R B N t (n + n') = tensorInlElt R B N t n + tensorInlElt R B N t n' :=
  TensorProduct.tmul_add _ _ _

/-- `Stacks.Descent.tensorInlElt` vanishes when its first argument is zero. -/
theorem tensorInlElt_zero_left (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInlElt R B N (toTensorInlModule R B 0) n = 0 :=
  TensorProduct.zero_tmul _ _

/-- The pure tensor `n ⊗ c` of the source model `ModuleCat.restrictModule R B N ⊗[R] B`. -/
def sourceModelElt (n : (ModuleCat.restrictModule R B N : Type u)) (c : B) :
    ModuleCat.restrictModule R B N ⊗[R] B :=
  n ⊗ₜ[R] c

/-- The pure tensor `a ⊗ b` acts on `n ⊗ c` of the source model as `(a • n) ⊗ (b * c)`. -/
theorem sourceModelElt_smul (a b : B) (n : (ModuleCat.restrictModule R B N : Type u)) (c : B) :
    ((a ⊗ₜ[R] b : B ⊗[R] B)) • sourceModelElt R B N n c =
      sourceModelElt R B N (a • n) (b * c) :=
  ModuleCat.sourceTensor_smul_tmul R B N a b c n

/-- `Stacks.Descent.sourceModelElt` is additive in the module argument. -/
theorem sourceModelElt_add_left (n n' : (ModuleCat.restrictModule R B N : Type u)) (c : B) :
    sourceModelElt R B N (n + n') c = sourceModelElt R B N n c + sourceModelElt R B N n' c :=
  TensorProduct.add_tmul _ _ _

/-- The unit `n ↦ n ⊗ 1` of the source model, as a `B`-linear map. -/
def sourceModelUnit :
    N ⟶ (ModuleCat.restrictScalars (tensorInl R B).hom).obj
      (ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B)) :=
  ModuleCat.ofHom (X := N)
    (Y := (ModuleCat.restrictScalars (tensorInl R B).hom).obj
      (ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B)))
    { toFun := fun n => sourceModelElt R B N n 1
      map_add' := fun n n' => sourceModelElt_add_left R B N n n' 1
      map_smul' := fun b n => ((sourceModelElt_smul R B N b 1 n 1).trans
        (congrArg (sourceModelElt R B N (b • n)) (one_mul 1))).symm }

/-- The comparison `(ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
ModuleCat.restrictModule R B N ⊗[R] B`, obtained from
`ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars` at
`Stacks.Descent.sourceModelUnit`. -/
def sourceModelHom : (ModuleCat.extendScalars (tensorInl R B).hom).obj N ⟶
    ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars _ (sourceModelUnit R B N)

/-- `Stacks.Descent.sourceModelHom` sends `t ⊗ n` to `t • (n ⊗ 1)`. -/
theorem sourceModelHom_tensorInlElt (t : B ⊗[R] B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelHom R B N (tensorInlElt R B N (toTensorInlModule R B t) n) =
      t • sourceModelElt R B N n 1 := rfl

/-- The value `(1 ⊗ c) ⊗ n` of the inverse comparison on a pure tensor. -/
def sourceModelInvElt (c : B) (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((ModuleCat.extendScalars (tensorInl R B).hom).obj N : Type u) :=
  tensorInlElt R B N (toTensorInlModule R B ((1 : B) ⊗ₜ[R] c)) n

/-- `Stacks.Descent.sourceModelInvElt` is additive in `c`. -/
theorem sourceModelInvElt_add_left (c c' : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelInvElt R B N (c + c') n =
      sourceModelInvElt R B N c n + sourceModelInvElt R B N c' n := by
  rw [sourceModelInvElt, TensorProduct.tmul_add, toTensorInlModule_add, tensorInlElt_add_left]
  rfl

/-- `Stacks.Descent.sourceModelInvElt` is additive in `n`. -/
theorem sourceModelInvElt_add_right (c : B)
    (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelInvElt R B N c (n + n') =
      sourceModelInvElt R B N c n + sourceModelInvElt R B N c n' :=
  tensorInlElt_add_right R B N _ n n'

/-- `Stacks.Descent.sourceModelInvElt` is `R`-linear in `c`. -/
theorem sourceModelInvElt_smul_left (r : R) (c : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelInvElt R B N (r • c) n =
      (algebraMap R (B ⊗[R] B)) r • sourceModelInvElt R B N c n := by
  rw [sourceModelInvElt, sourceModelInvElt, one_tmul_smul, ← smul_toTensorInlModule,
    tensorInlElt_smul]

/-- `Stacks.Descent.sourceModelInvElt` is `R`-linear in `n`. -/
theorem sourceModelInvElt_smul_right (r : R) (c : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelInvElt R B N c (r • n) =
      (algebraMap R (B ⊗[R] B)) r • sourceModelInvElt R B N c n := by
  rw [sourceModelInvElt, sourceModelInvElt,
    show (r • n : (ModuleCat.restrictModule R B N : Type u)) = (algebraMap R B r) • n from rfl,
    tensorInlElt_smul_right, smul_toTensorInlModule_left, ← algebraMap_tensorProduct,
    ← smul_toTensorInlModule, tensorInlElt_smul]

/-- `(ModuleCat.extendScalars (tensorInl R B).hom).obj N` as an `R`-module, as a restriction of
scalars. -/
abbrev tensorInlTargetR : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R (B ⊗[R] B))).obj
    ((ModuleCat.extendScalars (tensorInl R B).hom).obj N)

/-- The `R`-bilinear map underlying the inverse of `Stacks.Descent.sourceModelHom`. -/
def sourceModelInvBil :
    (ModuleCat.restrictModule R B N : Type u) →ₗ[R] B →ₗ[R]
      (tensorInlTargetR R B N : Type u) where
  toFun n :=
    { toFun := fun c => sourceModelInvElt R B N c n
      map_add' := fun c c' => sourceModelInvElt_add_left R B N c c' n
      map_smul' := fun r c => sourceModelInvElt_smul_left R B N r c n }
  map_add' n n' := LinearMap.ext fun c => sourceModelInvElt_add_right R B N c n n'
  map_smul' r n := LinearMap.ext fun c => sourceModelInvElt_smul_right R B N r c n

/-- The inverse of `Stacks.Descent.sourceModelHom`, as an additive map. -/
def sourceModelInvAdd :
    (ModuleCat.restrictModule R B N ⊗[R] B) →+
      ((ModuleCat.extendScalars (tensorInl R B).hom).obj N : Type u) :=
  (TensorProduct.lift (sourceModelInvBil R B N)).toAddMonoidHom

/-- `Stacks.Descent.sourceModelInvAdd` sends `n ⊗ c` to `(1 ⊗ c) ⊗ n`. -/
theorem sourceModelInvAdd_sourceModelElt (n : (ModuleCat.restrictModule R B N : Type u))
    (c : B) :
    sourceModelInvAdd R B N (sourceModelElt R B N n c) = sourceModelInvElt R B N c n := rfl

/-- `Stacks.Descent.sourceModelInvAdd` is a right inverse of `Stacks.Descent.sourceModelHom`. -/
theorem sourceModelHom_sourceModelInvAdd (z : ModuleCat.restrictModule R B N ⊗[R] B) :
    sourceModelHom R B N (sourceModelInvAdd R B N z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul n c =>
    rw [show (n ⊗ₜ[R] c : ModuleCat.restrictModule R B N ⊗[R] B) = sourceModelElt R B N n c
        from rfl,
      sourceModelInvAdd_sourceModelElt, sourceModelInvElt, sourceModelHom_tensorInlElt,
      sourceModelElt_smul, mul_one, one_smul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- `Stacks.Descent.sourceModelInvAdd` is `B ⊗[R] B`-linear. -/
theorem sourceModelInvAdd_smul (x : B ⊗[R] B) (z : ModuleCat.restrictModule R B N ⊗[R] B) :
    sourceModelInvAdd R B N (x • z) = x • sourceModelInvAdd R B N z := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | tmul a b =>
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul n c =>
      rw [show (n ⊗ₜ[R] c : ModuleCat.restrictModule R B N ⊗[R] B) = sourceModelElt R B N n c
          from rfl,
        sourceModelElt_smul, sourceModelInvAdd_sourceModelElt,
        sourceModelInvAdd_sourceModelElt, sourceModelInvElt, sourceModelInvElt,
        tensorInlElt_smul_right, smul_toTensorInlModule_left, tensorInlElt_smul,
        smul_toTensorInlModule, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add z z' hz hz' => rw [smul_add, map_add, map_add, smul_add, hz, hz']
  | add x x' hx hx' => rw [add_smul, map_add, hx, hx', add_smul]

/-- `Stacks.Descent.sourceModelInvAdd` undoes `Stacks.Descent.sourceModelHom` on `1 ⊗ n`. -/
theorem sourceModelInvAdd_sourceModelHom_one (n : (ModuleCat.restrictModule R B N : Type u)) :
    sourceModelInvAdd R B N
        (sourceModelHom R B N (tensorInlElt R B N (toTensorInlModule R B 1) n)) =
      tensorInlElt R B N (toTensorInlModule R B 1) n := by
  rw [sourceModelHom_tensorInlElt, one_smul, sourceModelInvAdd_sourceModelElt,
    sourceModelInvElt]
  rfl

/-- The inverse of `Stacks.Descent.sourceModelHom`, as a morphism of `B ⊗[R] B`-modules. -/
def sourceModelInv :
    ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B) ⟶
      (ModuleCat.extendScalars (tensorInl R B).hom).obj N :=
  ModuleCat.ofHom
    (X := ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B))
    (Y := (ModuleCat.extendScalars (tensorInl R B).hom).obj N)
    { toFun := sourceModelInvAdd R B N
      map_add' := fun z z' => map_add _ z z'
      map_smul' := sourceModelInvAdd_smul R B N }

/-- The extension of scalars of a `B`-module `N` along `b ↦ b ⊗ 1` is
`ModuleCat.restrictModule R B N ⊗[R] B` with the `B ⊗[R] B`-action of
`ModuleCat.sourceTensorModule`. -/
def extendScalarsInlSourceIso :
    (ModuleCat.extendScalars (tensorInl R B).hom).obj N ≅
      ModuleCat.of (B ⊗[R] B) (ModuleCat.restrictModule R B N ⊗[R] B) where
  hom := sourceModelHom R B N
  inv := sourceModelInv R B N
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext (sourceModelInvAdd_sourceModelHom_one R B N)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (sourceModelHom_sourceModelInvAdd R B N))

/-! #### The comparison at `tensorInr` -/

/-- A pure tensor of `(ModuleCat.extendScalars (tensorInr R B).hom).obj N`. -/
def tensorInrElt (t : (tensorInrModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((ModuleCat.extendScalars (tensorInr R B).hom).obj N : Type u) :=
  t ⊗ₜ[B] (show (N : Type u) from n)

/-- `B ⊗[R] B` acts on `Stacks.Descent.tensorInrElt` through its first argument. -/
theorem tensorInrElt_smul (x : B ⊗[R] B) (t : (tensorInrModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    x • tensorInrElt R B N t n = tensorInrElt R B N (x • t) n := rfl

/-- A scalar `b : B` moves across the tensor sign in `Stacks.Descent.tensorInrElt`. -/
theorem tensorInrElt_smul_right (t : (tensorInrModule R B : Type u)) (b : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInrElt R B N t (b • n) = tensorInrElt R B N (b • t) n :=
  (TensorProduct.smul_tmul b t (show (N : Type u) from n)).symm

/-- `Stacks.Descent.tensorInrElt` is additive in its first argument. -/
theorem tensorInrElt_add_left (t t' : (tensorInrModule R B : Type u))
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInrElt R B N (t + t') n = tensorInrElt R B N t n + tensorInrElt R B N t' n :=
  TensorProduct.add_tmul _ _ _

/-- `Stacks.Descent.tensorInrElt` is additive in its second argument. -/
theorem tensorInrElt_add_right (t : (tensorInrModule R B : Type u))
    (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInrElt R B N t (n + n') = tensorInrElt R B N t n + tensorInrElt R B N t n' :=
  TensorProduct.tmul_add _ _ _

/-- `Stacks.Descent.tensorInrElt` vanishes when its first argument is zero. -/
theorem tensorInrElt_zero_left (n : (ModuleCat.restrictModule R B N : Type u)) :
    tensorInrElt R B N (toTensorInrModule R B 0) n = 0 :=
  TensorProduct.zero_tmul _ _

/-- The pure tensor `c ⊗ n` of the target model `B ⊗[R] ModuleCat.restrictModule R B N`. -/
def targetModelElt (c : B) (n : (ModuleCat.restrictModule R B N : Type u)) :
    B ⊗[R] ModuleCat.restrictModule R B N :=
  c ⊗ₜ[R] n

/-- The pure tensor `a ⊗ b` acts on `c ⊗ n` of the target model as `(a * c) ⊗ (b • n)`. -/
theorem targetModelElt_smul (a b c : B) (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((a ⊗ₜ[R] b : B ⊗[R] B)) • targetModelElt R B N c n =
      targetModelElt R B N (a * c) (b • n) :=
  ModuleCat.targetTensor_smul_tmul R B N a b c n

/-- `Stacks.Descent.targetModelElt` is additive in the module argument. -/
theorem targetModelElt_add_right (c : B) (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelElt R B N c (n + n') = targetModelElt R B N c n + targetModelElt R B N c n' :=
  TensorProduct.tmul_add _ _ _

/-- The unit `n ↦ 1 ⊗ n` of the target model, as a `B`-linear map. -/
def targetModelUnit :
    N ⟶ (ModuleCat.restrictScalars (tensorInr R B).hom).obj
      (ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N)) :=
  ModuleCat.ofHom (X := N)
    (Y := (ModuleCat.restrictScalars (tensorInr R B).hom).obj
      (ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N)))
    { toFun := fun n => targetModelElt R B N 1 n
      map_add' := fun n n' => targetModelElt_add_right R B N 1 n n'
      map_smul' := fun b n => ((targetModelElt_smul R B N 1 b 1 n).trans
        (congrArg (fun z : B => targetModelElt R B N z (b • n)) (one_mul 1))).symm }

/-- The comparison `(ModuleCat.extendScalars (tensorInr R B).hom).obj N ⟶
B ⊗[R] ModuleCat.restrictModule R B N`. -/
def targetModelHom : (ModuleCat.extendScalars (tensorInr R B).hom).obj N ⟶
    ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars _ (targetModelUnit R B N)

/-- `Stacks.Descent.targetModelHom` sends `t ⊗ n` to `t • (1 ⊗ n)`. -/
theorem targetModelHom_tensorInrElt (t : B ⊗[R] B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelHom R B N (tensorInrElt R B N (toTensorInrModule R B t) n) =
      t • targetModelElt R B N 1 n := rfl

/-- The value `(c ⊗ 1) ⊗ n` of the inverse comparison on a pure tensor. -/
def targetModelInvElt (c : B) (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((ModuleCat.extendScalars (tensorInr R B).hom).obj N : Type u) :=
  tensorInrElt R B N (toTensorInrModule R B (c ⊗ₜ[R] (1 : B))) n

/-- `Stacks.Descent.targetModelInvElt` is additive in `c`. -/
theorem targetModelInvElt_add_left (c c' : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvElt R B N (c + c') n =
      targetModelInvElt R B N c n + targetModelInvElt R B N c' n := by
  rw [targetModelInvElt, TensorProduct.add_tmul, toTensorInrModule_add, tensorInrElt_add_left]
  rfl

/-- `Stacks.Descent.targetModelInvElt` is additive in `n`. -/
theorem targetModelInvElt_add_right (c : B)
    (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvElt R B N c (n + n') =
      targetModelInvElt R B N c n + targetModelInvElt R B N c n' :=
  tensorInrElt_add_right R B N _ n n'

/-- `Stacks.Descent.targetModelInvElt` is `R`-linear in `c`. -/
theorem targetModelInvElt_smul_left (r : R) (c : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvElt R B N (r • c) n =
      (algebraMap R (B ⊗[R] B)) r • targetModelInvElt R B N c n := by
  rw [targetModelInvElt, targetModelInvElt, tmul_one_smul, ← smul_toTensorInrModule,
    tensorInrElt_smul]

/-- `Stacks.Descent.targetModelInvElt` is `R`-linear in `n`. -/
theorem targetModelInvElt_smul_right (r : R) (c : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvElt R B N c (r • n) =
      (algebraMap R (B ⊗[R] B)) r • targetModelInvElt R B N c n := by
  rw [targetModelInvElt, targetModelInvElt, tensorInrElt_smul, smul_toTensorInrModule,
    show (r • n : (ModuleCat.restrictModule R B N : Type u)) = (algebraMap R B r) • n from rfl,
    tensorInrElt_smul_right, smul_toTensorInrModule_left, one_tmul_algebraMap]

/-- `(ModuleCat.extendScalars (tensorInr R B).hom).obj N` as an `R`-module. -/
abbrev tensorInrTargetR : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R (B ⊗[R] B))).obj
    ((ModuleCat.extendScalars (tensorInr R B).hom).obj N)

/-- The `R`-bilinear map underlying the inverse of `Stacks.Descent.targetModelHom`. -/
def targetModelInvBil :
    B →ₗ[R] (ModuleCat.restrictModule R B N : Type u) →ₗ[R]
      (tensorInrTargetR R B N : Type u) where
  toFun c :=
    { toFun := fun n => targetModelInvElt R B N c n
      map_add' := fun n n' => targetModelInvElt_add_right R B N c n n'
      map_smul' := fun r n => targetModelInvElt_smul_right R B N r c n }
  map_add' c c' := LinearMap.ext fun n => targetModelInvElt_add_left R B N c c' n
  map_smul' r c := LinearMap.ext fun n => targetModelInvElt_smul_left R B N r c n

/-- The inverse of `Stacks.Descent.targetModelHom`, as an additive map. -/
def targetModelInvAdd :
    (B ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars (tensorInr R B).hom).obj N : Type u) :=
  (TensorProduct.lift (targetModelInvBil R B N)).toAddMonoidHom

/-- `Stacks.Descent.targetModelInvAdd` sends `c ⊗ n` to `(c ⊗ 1) ⊗ n`. -/
theorem targetModelInvAdd_targetModelElt (c : B)
    (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvAdd R B N (targetModelElt R B N c n) = targetModelInvElt R B N c n := rfl

/-- `Stacks.Descent.targetModelInvAdd` is a right inverse of `Stacks.Descent.targetModelHom`. -/
theorem targetModelHom_targetModelInvAdd (z : B ⊗[R] ModuleCat.restrictModule R B N) :
    targetModelHom R B N (targetModelInvAdd R B N z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c n =>
    rw [show (c ⊗ₜ[R] n : B ⊗[R] ModuleCat.restrictModule R B N) = targetModelElt R B N c n
        from rfl,
      targetModelInvAdd_targetModelElt, targetModelInvElt, targetModelHom_tensorInrElt,
      targetModelElt_smul, mul_one, one_smul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- `Stacks.Descent.targetModelInvAdd` is `B ⊗[R] B`-linear. -/
theorem targetModelInvAdd_smul (x : B ⊗[R] B)
    (z : B ⊗[R] ModuleCat.restrictModule R B N) :
    targetModelInvAdd R B N (x • z) = x • targetModelInvAdd R B N z := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | tmul a b =>
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul c n =>
      rw [show (c ⊗ₜ[R] n : B ⊗[R] ModuleCat.restrictModule R B N) = targetModelElt R B N c n
          from rfl,
        targetModelElt_smul, targetModelInvAdd_targetModelElt,
        targetModelInvAdd_targetModelElt, targetModelInvElt, targetModelInvElt,
        tensorInrElt_smul_right, smul_toTensorInrModule_left, tensorInrElt_smul,
        smul_toTensorInrModule, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add z z' hz hz' => rw [smul_add, map_add, map_add, smul_add, hz, hz']
  | add x x' hx hx' => rw [add_smul, map_add, hx, hx', add_smul]

/-- `Stacks.Descent.targetModelInvAdd` undoes `Stacks.Descent.targetModelHom` on `1 ⊗ n`. -/
theorem targetModelInvAdd_targetModelHom_one (n : (ModuleCat.restrictModule R B N : Type u)) :
    targetModelInvAdd R B N
        (targetModelHom R B N (tensorInrElt R B N (toTensorInrModule R B 1) n)) =
      tensorInrElt R B N (toTensorInrModule R B 1) n := by
  rw [targetModelHom_tensorInrElt, one_smul, targetModelInvAdd_targetModelElt,
    targetModelInvElt]
  rfl

/-- The inverse of `Stacks.Descent.targetModelHom`, as a morphism of `B ⊗[R] B`-modules. -/
def targetModelInv :
    ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N) ⟶
      (ModuleCat.extendScalars (tensorInr R B).hom).obj N :=
  ModuleCat.ofHom
    (X := ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N))
    (Y := (ModuleCat.extendScalars (tensorInr R B).hom).obj N)
    { toFun := targetModelInvAdd R B N
      map_add' := fun z z' => map_add _ z z'
      map_smul' := targetModelInvAdd_smul R B N }

/-- The extension of scalars of a `B`-module `N` along `b ↦ 1 ⊗ b` is
`B ⊗[R] ModuleCat.restrictModule R B N` with the `B ⊗[R] B`-action of
`ModuleCat.targetTensorModule`. -/
def extendScalarsInrTargetIso :
    (ModuleCat.extendScalars (tensorInr R B).hom).obj N ≅
      ModuleCat.of (B ⊗[R] B) (B ⊗[R] ModuleCat.restrictModule R B N) where
  hom := targetModelHom R B N
  inv := targetModelInv R B N
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext (targetModelInvAdd_targetModelHom_one R B N)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (targetModelHom_targetModelInvAdd R B N))

/-! #### The transition of a module descent datum, read geometrically -/

/-- The transition of a module descent datum, as an isomorphism of the two extensions of
scalars: `ModuleCat.DescentData.transition` conjugated by
`Stacks.Descent.extendScalarsInlSourceIso` and `Stacks.Descent.extendScalarsInrTargetIso`. -/
def extendScalarsTransitionOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B) :
    (ModuleCat.extendScalars (tensorInl R B).hom).obj D.module ≅
      (ModuleCat.extendScalars (tensorInr R B).hom).obj D.module :=
  extendScalarsInlSourceIso R B D.module ≪≫ D.transition.toModuleIso ≪≫
    (extendScalarsInrTargetIso R B D.module).symm

/-- The transition morphism over `Spec (B ⊗[R] B)` attached to a module descent datum: the
isomorphism between the two pullbacks of `(D.module)^~` along the two projections of
`Stacks.Descent.specTensorChosenPullback`. -/
def specTransitionIsoOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B) :
    (qcohPseudofunctor.map (Spec.map (tensorInl R B)).op.toLoc).toFunctor.obj
        (tildeQcoh B D.module) ≅
      (qcohPseudofunctor.map (Spec.map (tensorInr R B)).op.toLoc).toFunctor.obj
        (tildeQcoh B D.module) :=
  (tildeExtendScalarsInlIso R B D.module).symm ≪≫
    (tildeEquiv (R := CommRingCat.of (B ⊗[R] B))).functor.mapIso
      (extendScalarsTransitionOfDescentData R B D) ≪≫
    tildeExtendScalarsInrIso R B D.module

/-- The transition data of `CategoryTheory.Pseudofunctor.DescentData'` for the one-element
family attached to a module descent datum: the `hom` field of a descent datum of
`Stacks.Descent.qcohPseudofunctor` over `Stacks.Descent.specSingletonSq`. -/
def specSingletonHomOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B) :
    ∀ i j : PUnit.{u + 1},
      (qcohPseudofunctor.map (specSingletonSq R B i j).p₁.op.toLoc).toFunctor.obj
          (tildeQcoh B D.module) ⟶
        (qcohPseudofunctor.map (specSingletonSq R B i j).p₂.op.toLoc).toFunctor.obj
          (tildeQcoh B D.module) :=
  fun _ _ => (specTransitionIsoOfDescentData R B D).hom

/-- `Stacks.Descent.specTransitionIsoOfDescentData` is the image of
`Stacks.Descent.extendScalarsTransitionOfDescentData` under
`Stacks.Descent.extendScalarsTransitionEquiv`. -/
theorem specTransitionIsoOfDescentData_hom (D : ModuleCat.DescentData.{u, u, u} R B) :
    (specTransitionIsoOfDescentData R B D).hom =
      extendScalarsTransitionEquiv R B D.module
        (extendScalarsTransitionOfDescentData R B D).hom :=
  (extendScalarsTransitionEquiv_hom R B D.module
    (extendScalarsTransitionOfDescentData R B D)).symm

/-! ### The `pullHom` calculus behind the unit condition -/

section PullHomCalculus

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- An idempotent isomorphism is the identity. -/
theorem eq_id_of_comp_self {D : Type*} [Category D] {Z : D} (x : Z ⟶ Z) [IsIso x]
    (h : x ≫ x = x) : x = 𝟙 Z := by
  rw [← cancel_epi x, h, Category.comp_id]

variable {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
  {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

/-- Pulling back an isomorphism gives an isomorphism, with inverse the pullback of the inverse. -/
theorem isIso_pullHom
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) := by
  refine ⟨pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁, ?_, ?_⟩
  · rw [← pullHom_comp φ (inv φ) g gf₁ gf₂ gf₁ hgf₁ hgf₂ hgf₁, IsIso.hom_inv_id,
      pullHom_id' g gf₁ hgf₁]
  · rw [← pullHom_comp (inv φ) φ g gf₂ gf₁ gf₂ hgf₂ hgf₁ hgf₂, IsIso.inv_hom_id,
      pullHom_id' g gf₂ hgf₂]

end PullHomCalculus

section UnitFromCocycle

open Pseudofunctor.DescentData'

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
  {obj : ∀ i, F.obj (.mk (op (X i)))}

/-- The unit condition `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_self` follows
from the cocycle condition `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_comp` as soon
as the transition morphisms are isomorphisms. -/
theorem pullHom'_self_of_pullHom'_comp
    (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hiso : ∀ i j, IsIso (hom i j))
    (hcomp : ∀ i₁ i₂ i₃ : ι,
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃) (i : ι) :
    pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) (Category.id_comp _) (Category.id_comp _) = 𝟙 _ := by
  have : IsIso (pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i))
      (Category.id_comp _) (Category.id_comp _)) := by
    have := hiso i i
    exact isIso_pullHom (hom i i) _ _ _ _ _
  exact eq_id_of_comp_self _
    (comp_pullHom'' (sq₃ := sq₃) hom hcomp (f i) (𝟙 (X i)) (𝟙 (X i)) (𝟙 (X i))
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _))

end UnitFromCocycle

/-! ### The dictionary over the threefold tensor power

For a ring map `θ` out of an `R`-algebra `A` and a ring map `j : B ⟶ T`,
`Stacks.Descent.smulOneTmulMap` compares `A ⊗[R] N` with the extension of scalars of `N` along
`j`. At `A = B` its source is the target of `ModuleCat.DescentData.transition`; at
`A = B ⊗[R] B` it is the common target of `ModuleCat.transition12` and
`ModuleCat.transition02`. -/

section TripleDictionary

variable {T : Type u} [CommRing T] [Algebra R T] {A : Type u} [CommRing A] [Algebra R A]
  (θ : A →+* T) (j : B →+* T)

/-- The element `θ a • (1 ⊗ n)` of the extension of scalars of `N` along `j`. -/
def smulOneTmul (a : A) (n : (ModuleCat.restrictModule R B N : Type u)) :
    ((ModuleCat.extendScalars j).obj N : Type u) :=
  θ a • ModuleCat.ExtendScalars.oneTmul j (show (N : Type u) from n)

omit [Algebra R A] [Algebra R T] in
/-- `Stacks.Descent.smulOneTmul` vanishes when `a = 0`. -/
theorem smulOneTmul_zero_left (n : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmul R B N θ j 0 n = 0 := by
  rw [smulOneTmul, map_zero, zero_smul]

omit [Algebra R A] [Algebra R T] in
/-- `Stacks.Descent.smulOneTmul` vanishes when `n = 0`. -/
theorem smulOneTmul_zero_right (a : A) :
    smulOneTmul R B N θ j a 0 = 0 := by
  rw [smulOneTmul, show ModuleCat.ExtendScalars.oneTmul j
      (show (N : Type u) from (0 : (ModuleCat.restrictModule R B N : Type u))) = 0 from
    TensorProduct.tmul_zero _ _, smul_zero]

omit [Algebra R A] [Algebra R T] in
/-- `Stacks.Descent.smulOneTmul` is additive in `a`. -/
theorem smulOneTmul_add_left (a a' : A) (n : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmul R B N θ j (a + a') n =
      smulOneTmul R B N θ j a n + smulOneTmul R B N θ j a' n := by
  rw [smulOneTmul, smulOneTmul, smulOneTmul, map_add, add_smul]

omit [Algebra R A] [Algebra R T] in
/-- `Stacks.Descent.smulOneTmul` is additive in `n`. -/
theorem smulOneTmul_add_right (a : A) (n n' : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmul R B N θ j a (n + n') =
      smulOneTmul R B N θ j a n + smulOneTmul R B N θ j a n' := by
  rw [smulOneTmul, smulOneTmul, smulOneTmul,
    show (show (N : Type u) from (n + n')) =
      (show (N : Type u) from n) + (show (N : Type u) from n') from rfl,
    ModuleCat.ExtendScalars.oneTmul_add, smul_add]

/-- When `θ` is compatible with the structure maps from `R`, `Stacks.Descent.smulOneTmul` is
`R`-linear in `a`. -/
theorem smulOneTmul_smul_left (hθ : ∀ r : R, θ (algebraMap R A r) = algebraMap R T r)
    (r : R) (a : A) (n : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmul R B N θ j (r • a) n = algebraMap R T r • smulOneTmul R B N θ j a n := by
  rw [smulOneTmul, smulOneTmul, Algebra.smul_def, map_mul, hθ, mul_smul]

omit [Algebra R A] in
/-- When `j` is compatible with the structure maps from `R`, `Stacks.Descent.smulOneTmul` is
`R`-linear in `n`. -/
theorem smulOneTmul_smul_right (hj : ∀ r : R, j (algebraMap R B r) = algebraMap R T r)
    (r : R) (a : A) (n : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmul R B N θ j a (r • n) = algebraMap R T r • smulOneTmul R B N θ j a n := by
  rw [smulOneTmul, smulOneTmul,
    show (show (N : Type u) from (r • n : (ModuleCat.restrictModule R B N : Type u))) =
      (algebraMap R B r) • (show (N : Type u) from n) from rfl,
    ModuleCat.ExtendScalars.oneTmul_smul, hj, smul_comm]

/-- `Stacks.Descent.smulOneTmul` as a bi-additive map. -/
def smulOneTmulAddHom :
    A →+ (ModuleCat.restrictModule R B N : Type u) →+
      ((ModuleCat.extendScalars j).obj N : Type u) where
  toFun a :=
    { toFun := fun n => smulOneTmul R B N θ j a n
      map_zero' := smulOneTmul_zero_right R B N θ j a
      map_add' := fun n n' => smulOneTmul_add_right R B N θ j a n n' }
  map_zero' := AddMonoidHom.ext fun n => smulOneTmul_zero_left R B N θ j n
  map_add' a a' := AddMonoidHom.ext fun n => smulOneTmul_add_left R B N θ j a a' n

variable (hθ : ∀ r : R, θ (algebraMap R A r) = algebraMap R T r)
  (hj : ∀ r : R, j (algebraMap R B r) = algebraMap R T r)

/-- The additive map `A ⊗[R] N → (ModuleCat.extendScalars j).obj N` sending `a ⊗ n` to
`θ a • (1 ⊗ n)`. -/
def smulOneTmulMap :
    (A ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars j).obj N : Type u) :=
  TensorProduct.liftAddHom (R := R) (smulOneTmulAddHom R B N θ j)
    fun r a n => by
      change smulOneTmul R B N θ j (r • a) n = smulOneTmul R B N θ j a (r • n)
      rw [smulOneTmul_smul_left R B N θ j hθ, smulOneTmul_smul_right R B N θ j hj]

/-- `Stacks.Descent.smulOneTmulMap` sends `a ⊗ n` to `θ a • (1 ⊗ n)`. -/
@[simp]
theorem smulOneTmulMap_tmul (a : A) (n : (ModuleCat.restrictModule R B N : Type u)) :
    smulOneTmulMap R B N θ j hθ hj (a ⊗ₜ[R] n) = smulOneTmul R B N θ j a n :=
  TensorProduct.liftAddHom_tmul _ _ a n

end TripleDictionary

/-! #### The base change of the transition along a ring map out of `B ⊗[R] B` -/

section TripleTransition

variable {T : Type u} [CommRing T] [Algebra R T]

/-- The value of `Stacks.Descent.extendScalarsTransitionOfDescentData` on `1 ⊗ n`: the
transition of the module descent datum at `n ⊗ 1`, read in the target model. -/
theorem extendScalarsTransitionOfDescentData_hom_oneTmul
    (D : ModuleCat.DescentData.{u, u, u} R B)
    (n : (ModuleCat.restrictModule R B D.module : Type u)) :
    (extendScalarsTransitionOfDescentData R B D).hom
        (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom
          (show (D.module : Type u) from n)) =
      targetModelInvAdd R B D.module (D.transition (n ⊗ₜ[R] (1 : B))) := by
  have h : sourceModelHom R B D.module
      (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom
        (show (D.module : Type u) from n)) = n ⊗ₜ[R] (1 : B) :=
    (sourceModelHom_tensorInlElt R B D.module 1 n).trans (one_smul _ _)
  show targetModelInvAdd R B D.module (D.transition (sourceModelHom R B D.module
    (ModuleCat.ExtendScalars.oneTmul (tensorInl R B).hom
      (show (D.module : Type u) from n)))) = _
  rw [h]

/-- The base change along `ψ` of an element
of the target model `B ⊗[R] N`, read in the extension of scalars of `N` along `j₂`, is
`Stacks.Descent.smulOneTmulMap` at the pair `(j₁, j₂)`. -/
theorem cancelExtendScalars_hom_oneTmul_targetModelInvAdd
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂)
    (hj₁ : ∀ r : R, j₁ (algebraMap R B r) = algebraMap R T r)
    (hj₂ : ∀ r : R, j₂ (algebraMap R B r) = algebraMap R T r)
    (w : B ⊗[R] ModuleCat.restrictModule R B N) :
    (ModuleCat.cancelExtendScalars (tensorInr R B).hom ψ h₂ N).hom
        (ModuleCat.ExtendScalars.oneTmul ψ (targetModelInvAdd R B N w)) =
      smulOneTmulMap R B N j₁ j₂ hj₁ hj₂ w := by
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, show ModuleCat.ExtendScalars.oneTmul ψ
        (0 : ((ModuleCat.extendScalars (tensorInr R B).hom).obj N : Type u)) = 0 from
      TensorProduct.tmul_zero _ _, map_zero, map_zero]
  | tmul c n =>
    have e1 : ((c ⊗ₜ[R] (1 : B) : B ⊗[R] B)) •
        ModuleCat.ExtendScalars.oneTmul (tensorInr R B).hom (show (N : Type u) from n) =
        targetModelInvAdd R B N (c ⊗ₜ[R] n) := by
      rw [show ModuleCat.ExtendScalars.oneTmul (tensorInr R B).hom (show (N : Type u) from n)
            = tensorInrElt R B N (toTensorInrModule R B 1) n from rfl,
        tensorInrElt_smul, smul_toTensorInrModule, mul_one]
      rfl
    rw [← e1, ModuleCat.ExtendScalars.oneTmul_smul, map_smul,
      ModuleCat.cancelExtendScalars_hom_oneTmul, smulOneTmulMap_tmul, smulOneTmul, ← h₁,
      RingHom.comp_apply]
    rfl
  | add w w' hw hw' =>
    rw [map_add, show ModuleCat.ExtendScalars.oneTmul ψ
        (targetModelInvAdd R B N w + targetModelInvAdd R B N w') =
        ModuleCat.ExtendScalars.oneTmul ψ (targetModelInvAdd R B N w) +
          ModuleCat.ExtendScalars.oneTmul ψ (targetModelInvAdd R B N w') from
      ModuleCat.ExtendScalars.oneTmul_add _ _ _, map_add, hw, hw', map_add]

/-- The transition of a module descent datum, base changed along a ring map `ψ` out of
`B ⊗[R] B` and composed with the two base-change cancellations `ModuleCat.cancelExtendScalars`:
a morphism between the two direct extensions of scalars of `D.module`, along the ring maps
`j₁ = ψ ∘ (b ↦ b ⊗ 1)` and `j₂ = ψ ∘ (b ↦ 1 ⊗ b)`. -/
def extendScalarsTripleTransition (D : ModuleCat.DescentData.{u, u, u} R B)
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂) :
    (ModuleCat.extendScalars j₁).obj D.module ⟶ (ModuleCat.extendScalars j₂).obj D.module :=
  (ModuleCat.cancelExtendScalars (tensorInl R B).hom ψ h₁ D.module).inv ≫
    (ModuleCat.extendScalars ψ).map (extendScalarsTransitionOfDescentData R B D).hom ≫
    (ModuleCat.cancelExtendScalars (tensorInr R B).hom ψ h₂ D.module).hom

/-- The value of `Stacks.Descent.extendScalarsTripleTransition` on `1 ⊗ n`, in terms of the two
ring maps `j₁` and `j₂` that `ψ` induces. -/
theorem extendScalarsTripleTransition_oneTmul (D : ModuleCat.DescentData.{u, u, u} R B)
    (ψ : (B ⊗[R] B) →+* T) {j₁ j₂ : B →+* T}
    (h₁ : ψ.comp (tensorInl R B).hom = j₁) (h₂ : ψ.comp (tensorInr R B).hom = j₂)
    (hj₁ : ∀ r : R, j₁ (algebraMap R B r) = algebraMap R T r)
    (hj₂ : ∀ r : R, j₂ (algebraMap R B r) = algebraMap R T r)
    (n : (ModuleCat.restrictModule R B D.module : Type u)) :
    extendScalarsTripleTransition R B D ψ h₁ h₂
        (ModuleCat.ExtendScalars.oneTmul j₁ (show (D.module : Type u) from n)) =
      smulOneTmulMap R B D.module j₁ j₂ hj₁ hj₂ (D.transition (n ⊗ₜ[R] (1 : B))) := by
  rw [extendScalarsTripleTransition, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.cancelExtendScalars_inv_oneTmul, ModuleCat.ExtendScalars.map_oneTmul,
    extendScalarsTransitionOfDescentData_hom_oneTmul,
    cancelExtendScalars_hom_oneTmul_targetModelInvAdd R B D.module ψ h₁ h₂ hj₁ hj₂]

end TripleTransition

/-! #### The three ring maps into the threefold tensor power -/

section TripleRingMaps

/-- `Stacks.Descent.tensorInl_comp_tensorMap₀₁` at the level of ring maps. -/
theorem tensorMap₀₁_comp_tensorInl :
    (tensorMap₀₁ R B).hom.comp (tensorInl R B).hom = (tensorIncl₀ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInl_comp_tensorMap₀₁ R B)

/-- `Stacks.Descent.tensorInr_comp_tensorMap₀₁` at the level of ring maps. -/
theorem tensorMap₀₁_comp_tensorInr :
    (tensorMap₀₁ R B).hom.comp (tensorInr R B).hom = (tensorIncl₁ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInr_comp_tensorMap₀₁ R B)

/-- `Stacks.Descent.tensorInl_comp_tensorMap₁₂` at the level of ring maps. -/
theorem tensorMap₁₂_comp_tensorInl :
    (tensorMap₁₂ R B).hom.comp (tensorInl R B).hom = (tensorIncl₁ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInl_comp_tensorMap₁₂ R B)

/-- `Stacks.Descent.tensorInr_comp_tensorMap₁₂` at the level of ring maps. -/
theorem tensorMap₁₂_comp_tensorInr :
    (tensorMap₁₂ R B).hom.comp (tensorInr R B).hom = (tensorIncl₂ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInr_comp_tensorMap₁₂ R B)

/-- `Stacks.Descent.tensorInl_comp_tensorMap₀₂` at the level of ring maps. -/
theorem tensorMap₀₂_comp_tensorInl :
    (tensorMap₀₂ R B).hom.comp (tensorInl R B).hom = (tensorIncl₀ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInl_comp_tensorMap₀₂ R B)

/-- `Stacks.Descent.tensorInr_comp_tensorMap₀₂` at the level of ring maps. -/
theorem tensorMap₀₂_comp_tensorInr :
    (tensorMap₀₂ R B).hom.comp (tensorInr R B).hom = (tensorIncl₂ R B).hom :=
  congrArg CommRingCat.Hom.hom (tensorInr_comp_tensorMap₀₂ R B)

/-- The inclusion of the first factor is an `R`-algebra map. -/
theorem tensorIncl₀_algebraMap : ∀ r : R, (tensorIncl₀ R B).hom (algebraMap R B r) =
    algebraMap R (B ⊗[R] (B ⊗[R] B)) r := fun r =>
  (Algebra.TensorProduct.algebraMap_apply (R := R) (S := R) (A := B) (B := B ⊗[R] B) r).symm

/-- The inclusion of the middle factor is an `R`-algebra map. -/
theorem tensorIncl₁_algebraMap : ∀ r : R, (tensorIncl₁ R B).hom (algebraMap R B r) =
    algebraMap R (B ⊗[R] (B ⊗[R] B)) r := fun r =>
  ((Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B ⊗[R] B)).comp
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := B))).commutes r

/-- The inclusion of the last factor is an `R`-algebra map. -/
theorem tensorIncl₂_algebraMap : ∀ r : R, (tensorIncl₂ R B).hom (algebraMap R B r) =
    algebraMap R (B ⊗[R] (B ⊗[R] B)) r := fun r =>
  ((Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B ⊗[R] B)).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := B))).commutes r

/-- The inclusion of the first two factors is an `R`-algebra map. -/
theorem tensorMap₀₁_algebraMap : ∀ r : R, (tensorMap₀₁ R B).hom (algebraMap R (B ⊗[R] B) r) =
    algebraMap R (B ⊗[R] (B ⊗[R] B)) r := fun r =>
  (Algebra.TensorProduct.map (AlgHom.id R B)
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := B))).commutes r

/-- On a pure tensor the inclusion of the first two factors is the product of the two single
inclusions. -/
theorem tensorMap₀₁_tmul (c b : B) : (tensorMap₀₁ R B).hom (c ⊗ₜ[R] b) =
    (tensorIncl₀ R B).hom c * (tensorIncl₁ R B).hom b := by
  show Algebra.TensorProduct.map _ _ (c ⊗ₜ[R] b) = _
  rw [Algebra.TensorProduct.map_tmul]
  show c ⊗ₜ[R] (b ⊗ₜ[R] (1 : B)) =
    (c ⊗ₜ[R] (1 : B ⊗[R] B)) * ((1 : B) ⊗ₜ[R] (b ⊗ₜ[R] (1 : B)))
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one]

end TripleRingMaps

/-! #### The cocycle condition over the threefold tensor power -/

section TripleCocycle

/-- `Stacks.Descent.smulOneTmulMap` at the pair of inclusions `(ι₀, ι₁)`. -/
abbrev tripleMap₀₁ :
    (B ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars (tensorIncl₁ R B).hom).obj N : Type u) :=
  smulOneTmulMap R B N (tensorIncl₀ R B).hom (tensorIncl₁ R B).hom
    (tensorIncl₀_algebraMap R B) (tensorIncl₁_algebraMap R B)

/-- `Stacks.Descent.smulOneTmulMap` at the pair of inclusions `(ι₁, ι₂)`. -/
abbrev tripleMap₁₂ :
    (B ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars (tensorIncl₂ R B).hom).obj N : Type u) :=
  smulOneTmulMap R B N (tensorIncl₁ R B).hom (tensorIncl₂ R B).hom
    (tensorIncl₁_algebraMap R B) (tensorIncl₂_algebraMap R B)

/-- `Stacks.Descent.smulOneTmulMap` at the pair of inclusions `(ι₀, ι₂)`. -/
abbrev tripleMap₀₂ :
    (B ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars (tensorIncl₂ R B).hom).obj N : Type u) :=
  smulOneTmulMap R B N (tensorIncl₀ R B).hom (tensorIncl₂ R B).hom
    (tensorIncl₀_algebraMap R B) (tensorIncl₂_algebraMap R B)

/-- `Stacks.Descent.smulOneTmulMap` out of `(B ⊗[R] B) ⊗[R] N`, which is where
`ModuleCat.transition12` and `ModuleCat.transition02` take their values. -/
abbrev tripleCocycleMap :
    ((B ⊗[R] B) ⊗[R] ModuleCat.restrictModule R B N) →+
      ((ModuleCat.extendScalars (tensorIncl₂ R B).hom).obj N : Type u) :=
  smulOneTmulMap R B N (tensorMap₀₁ R B).hom (tensorIncl₂ R B).hom
    (tensorMap₀₁_algebraMap R B) (tensorIncl₂_algebraMap R B)

/-- The comparison over the threefold tensor power, read through the swap of the last two
factors, is the comparison at `(ι₀, ι₂)`. -/
theorem tripleCocycleMap_rightComm (y : B ⊗[R] ModuleCat.restrictModule R B N) :
    tripleCocycleMap R B N
        ((TensorProduct.rightComm R B (ModuleCat.restrictModule R B N) B) (y ⊗ₜ[R] (1 : B))) =
      tripleMap₀₂ R B N y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul c n =>
    rw [TensorProduct.rightComm_tmul, smulOneTmulMap_tmul, smulOneTmulMap_tmul, smulOneTmul,
      smulOneTmul, ← tensorMap₀₁_comp_tensorInl R B, RingHom.comp_apply]
    rfl
  | add y y' hy hy' => rw [TensorProduct.add_tmul, map_add, map_add, hy, hy', map_add]

/-- The comparison over the threefold tensor power, read through the associativity that moves a
factor of `B` to the front, is the first inclusion acting on the comparison at `(ι₁, ι₂)`. -/
theorem tripleCocycleMap_assoc_symm (c : B) (z : B ⊗[R] ModuleCat.restrictModule R B N) :
    tripleCocycleMap R B N
        ((TensorProduct.assoc R B B (ModuleCat.restrictModule R B N)).symm (c ⊗ₜ[R] z)) =
      (tensorIncl₀ R B).hom c • tripleMap₁₂ R B N z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, smul_zero]
  | tmul b n =>
    rw [TensorProduct.assoc_symm_tmul, smulOneTmulMap_tmul, smulOneTmulMap_tmul, smulOneTmul,
      smulOneTmul, tensorMap₀₁_tmul, mul_smul]
  | add z z' hz hz' =>
    rw [TensorProduct.tmul_add, map_add, map_add, hz, hz', map_add, smul_add]

/-- The base change of the transition along `Stacks.Descent.tensorMap₁₂`, precomposed with the
comparison at `(ι₀, ι₁)`, is `ModuleCat.transition12`. -/
theorem extendScalarsTripleTransition₁₂_tripleMap₀₁ (D : ModuleCat.DescentData.{u, u, u} R B)
    (y : B ⊗[R] ModuleCat.restrictModule R B D.module) :
    extendScalarsTripleTransition R B D (tensorMap₁₂ R B).hom
        (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
        (tripleMap₀₁ R B D.module y) =
      tripleCocycleMap R B D.module
        (ModuleCat.transition12 R B D.module D.transition (y ⊗ₜ[R] (1 : B))) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul c n =>
    rw [show ModuleCat.transition12 R B D.module D.transition ((c ⊗ₜ[R] n) ⊗ₜ[R] (1 : B)) =
          (TensorProduct.assoc R B B (ModuleCat.restrictModule R B D.module)).symm
            (c ⊗ₜ[R] D.transition (n ⊗ₜ[R] (1 : B))) from rfl,
      tripleCocycleMap_assoc_symm, smulOneTmulMap_tmul, smulOneTmul, map_smul,
      extendScalarsTripleTransition_oneTmul R B D (tensorMap₁₂ R B).hom
        (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B)
        (tensorIncl₁_algebraMap R B) (tensorIncl₂_algebraMap R B) n]
  | add y y' hy hy' =>
    rw [TensorProduct.add_tmul, map_add, map_add, map_add, hy, hy', map_add]

/-- The cocycle condition of a module descent datum, read over the threefold tensor power: the
three base changes of `ModuleCat.DescentData.transition` along `Stacks.Descent.tensorMap₀₁`,
`Stacks.Descent.tensorMap₁₂` and `Stacks.Descent.tensorMap₀₂` — each read, by
`Stacks.Descent.extendScalarsTripleTransition`, as a morphism between the direct extensions of
scalars of `D.module` along the three inclusions `Stacks.Descent.tensorIncl₀`,
`Stacks.Descent.tensorIncl₁` and `Stacks.Descent.tensorIncl₂` of `B` into `B ⊗[R] (B ⊗[R] B)` —
satisfy the cocycle identity. -/
theorem extendScalarsTripleTransition_comp (D : ModuleCat.DescentData.{u, u, u} R B) :
    extendScalarsTripleTransition R B D (tensorMap₀₁ R B).hom
        (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B) ≫
      extendScalarsTripleTransition R B D (tensorMap₁₂ R B).hom
        (tensorMap₁₂_comp_tensorInl R B) (tensorMap₁₂_comp_tensorInr R B) =
    extendScalarsTripleTransition R B D (tensorMap₀₂ R B).hom
      (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B) := by
  refine ModuleCat.ExtendScalars.hom_ext' fun x => ?_
  rw [ModuleCat.comp_apply,
    extendScalarsTripleTransition_oneTmul R B D (tensorMap₀₁ R B).hom
      (tensorMap₀₁_comp_tensorInl R B) (tensorMap₀₁_comp_tensorInr R B)
      (tensorIncl₀_algebraMap R B) (tensorIncl₁_algebraMap R B) x,
    extendScalarsTripleTransition_oneTmul R B D (tensorMap₀₂ R B).hom
      (tensorMap₀₂_comp_tensorInl R B) (tensorMap₀₂_comp_tensorInr R B)
      (tensorIncl₀_algebraMap R B) (tensorIncl₂_algebraMap R B) x,
    extendScalarsTripleTransition₁₂_tripleMap₀₁,
    show ModuleCat.transition12 R B D.module D.transition
        (D.transition (x ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) =
      ModuleCat.transition02 R B D.module D.transition ((x ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) from
      LinearMap.congr_fun D.cocycle ((x ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)),
    show ModuleCat.transition02 R B D.module D.transition
        ((x ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) =
      (TensorProduct.rightComm R B (ModuleCat.restrictModule R B D.module) B)
        (D.transition (x ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) from rfl,
    tripleCocycleMap_rightComm]

end TripleCocycle

/-! ### The geometric descent datum attached to a module descent datum -/

section SpecSingletonDescentData

open Pseudofunctor.DescentData'

/-- The cocycle condition of `CategoryTheory.Pseudofunctor.DescentData'` for the transition
morphism supplied by a module descent datum, over the chosen threefold wide pullback
`Stacks.Descent.specTensorChosenPullback₃`. -/
abbrev SpecSingletonCocycle (D : ModuleCat.DescentData.{u, u, u} R B) : Prop :=
  ∀ i₁ i₂ i₃ : PUnit.{u + 1},
    pullHom' (F := qcohPseudofunctor.{u}) (ι := PUnit.{u + 1})
          (X := fun _ ↦ Spec (CommRingCat.of B)) (f := specSingleton R B)
          (sq := specSingletonSq R B) (obj := fun _ ↦ tildeQcoh B D.module)
          (obj' := fun _ ↦ tildeQcoh B D.module) (specSingletonHomOfDescentData R B D)
          (specSingletonSq₃ R B i₁ i₂ i₃).p (i₁ := i₁) (i₂ := i₂)
          (specSingletonSq₃ R B i₁ i₂ i₃).p₁ (specSingletonSq₃ R B i₁ i₂ i₃).p₂
          (specSingletonSq₃ R B i₁ i₂ i₃).w₁ (specSingletonSq₃ R B i₁ i₂ i₃).w₂ ≫
        pullHom' (F := qcohPseudofunctor.{u}) (ι := PUnit.{u + 1})
          (X := fun _ ↦ Spec (CommRingCat.of B)) (f := specSingleton R B)
          (sq := specSingletonSq R B) (obj := fun _ ↦ tildeQcoh B D.module)
          (obj' := fun _ ↦ tildeQcoh B D.module) (specSingletonHomOfDescentData R B D)
          (specSingletonSq₃ R B i₁ i₂ i₃).p (i₁ := i₂) (i₂ := i₃)
          (specSingletonSq₃ R B i₁ i₂ i₃).p₂ (specSingletonSq₃ R B i₁ i₂ i₃).p₃
          (specSingletonSq₃ R B i₁ i₂ i₃).w₂ (specSingletonSq₃ R B i₁ i₂ i₃).w₃ =
      pullHom' (F := qcohPseudofunctor.{u}) (ι := PUnit.{u + 1})
        (X := fun _ ↦ Spec (CommRingCat.of B)) (f := specSingleton R B)
        (sq := specSingletonSq R B) (obj := fun _ ↦ tildeQcoh B D.module)
        (obj' := fun _ ↦ tildeQcoh B D.module) (specSingletonHomOfDescentData R B D)
        (specSingletonSq₃ R B i₁ i₂ i₃).p (i₁ := i₁) (i₂ := i₃)
        (specSingletonSq₃ R B i₁ i₂ i₃).p₁ (specSingletonSq₃ R B i₁ i₂ i₃).p₃
        (specSingletonSq₃ R B i₁ i₂ i₃).w₁ (specSingletonSq₃ R B i₁ i₂ i₃).w₃

/-- The transition morphism supplied by a module descent datum is an isomorphism: it is the
`hom` of `Stacks.Descent.specTransitionIsoOfDescentData`. -/
theorem isIso_specSingletonHomOfDescentData (D : ModuleCat.DescentData.{u, u, u} R B)
    (i j : PUnit.{u + 1}) : IsIso (specSingletonHomOfDescentData R B D i j) :=
  inferInstanceAs (IsIso (specTransitionIsoOfDescentData R B D).hom)

/-- The unit condition `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_self` for the
transition morphism supplied by a module descent datum, assuming the cocycle condition. -/
theorem specSingletonPullHom'_self (D : ModuleCat.DescentData.{u, u, u} R B)
    (hcomp : SpecSingletonCocycle R B D) (i : PUnit.{u + 1}) :
    pullHom' (F := qcohPseudofunctor.{u}) (ι := PUnit.{u + 1})
      (X := fun _ ↦ Spec (CommRingCat.of B)) (f := specSingleton R B)
      (sq := specSingletonSq R B) (obj := fun _ ↦ tildeQcoh B D.module)
      (obj' := fun _ ↦ tildeQcoh B D.module) (specSingletonHomOfDescentData R B D)
      (specSingleton R B i) (i₁ := i) (i₂ := i) (𝟙 _) (𝟙 _)
      (Category.id_comp _) (Category.id_comp _) = 𝟙 _ :=
  pullHom'_self_of_pullHom'_comp (sq₃ := specSingletonSq₃ R B)
    (specSingletonHomOfDescentData R B D) (isIso_specSingletonHomOfDescentData R B D) hcomp i

/-- The descent datum of `Stacks.Descent.qcohPseudofunctor` for the one-element family
`Spec B ⟶ Spec R` attached to a module descent datum, assuming the cocycle condition
`Stacks.Descent.SpecSingletonCocycle`.  Its object is `(D.module)^~`, its transition morphism is
`Stacks.Descent.specSingletonHomOfDescentData`, and its unit condition is
`Stacks.Descent.specSingletonPullHom'_self`. -/
def specSingletonDescentData' (D : ModuleCat.DescentData.{u, u, u} R B)
    (hcomp : SpecSingletonCocycle R B D) :
    qcohPseudofunctor.DescentData' (specSingletonSq R B) (specSingletonSq₃ R B) where
  obj _ := tildeQcoh B D.module
  hom := specSingletonHomOfDescentData R B D
  pullHom'_hom_self i := specSingletonPullHom'_self R B D hcomp i
  pullHom'_hom_comp i₁ i₂ i₃ := hcomp i₁ i₂ i₃

end SpecSingletonDescentData


end Stacks.Descent

end

end
