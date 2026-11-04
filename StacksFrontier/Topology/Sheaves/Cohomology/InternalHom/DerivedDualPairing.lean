module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The duality pairing of the derived dual on a ringed space

Let `(X, O_X)` be a ringed space and let `K` be an object of the derived category `D(O_X)` of
sheaves of `O_X`-modules. The **dual** of `K` is `K^∨ = RSheafHom(K, O_X)`
(`Stacks.SheafOfModules.derivedDual`). This file supplies the **evaluation**

`ε : K^∨ ⊗^L_{O_X} K ⟶ O_X`

of the duality pairing of `K`, in the spelling of the monoidal structure
`Stacks.SheafOfModules.derivedMonoidalStructure` on `D(O_X)` whose tensor product is the derived
tensor product of Stacks 06YU and whose unit is the structure sheaf in degree zero. It also
records what the monoidal structure makes of a left dual in Stacks' sense — Mathlib's
`CategoryTheory.ExactPairing K N`, whose coevaluation is `η : O_X ⟶ K ⊗^L_{O_X} N` and whose
evaluation is `ε : N ⊗^L_{O_X} K ⟶ O_X` — namely the canonical comparison from the derived dual
to such an `N`.  (Uniqueness of a left dual up to isomorphism is a general fact about monoidal
categories and is `CategoryTheory.rightDualIso`; it is not restated here.)

A topological space with a sheaf of commutative rings *is* a ringed site, namely its site of
opens with the open-cover topology, so the evaluation is the ringed-site morphism of
Stacks 0FPU read off along `Stacks.SheafOfModules.ringedSite`, exactly as the dual itself and the
canonical map `M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)` are in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual`. No perfectness
hypothesis is needed for it: the evaluation exists for every object of `D(O_X)`.

## Main definitions

* `Stacks.SheafOfModules.derivedDualEvaluation`: the evaluation `ε : K^∨ ⊗^L_{O_X} K ⟶ O_X`.
* `Stacks.SheafOfModules.derivedDualToLeftDual`: for a left dual `N` of `K`, the canonical
  morphism `K^∨ ⟶ N` obtained by transposing the evaluation of `K^∨` across the pairing of `N`.

## Main results

* `Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure`: the unit of the monoidal
  structure is the structure sheaf in degree zero, so that `ε` has the type its monoidal
  spelling claims.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.derivedMonoidalStructure`, which is an
`@[instance_reducible] def` rather than an instance, so every statement below introduces it with
a `letI` in its own type. Its curried tensor product is `Stacks.SheafOfModules.derivedTensor` by
`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure`, an equality of bifunctors proved
by `rfl`, and its unit is `AlgebraicGeometry.RingedSite.derivedStructureSheaf` by
`tensorUnit_derivedMonoidalStructure` below, also `rfl`. Hence `A ⊗ B` *is*
`((derivedTensor Rc).obj A).obj B` and `𝟙_` *is* the derived structure sheaf, and no `eqToHom`
and no comparison layer occurs: the ringed-site evaluation of
`AlgebraicGeometry.RingedSite.derivedDualEvaluation` type-checks against the monoidal statement
directly.

**Why the tensor product and the transposition name their category.** `derivedMonoidalStructure`
is stated over `Stacks.SheafOfModules.StructureSheafModules Rc`, i.e. over
`SheafOfModules (structureSheaf Rc)` and so over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, while
`Stacks.SheafOfModules.derivedDual` is stated over
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Rc)`, which pairs
`Rc.obj ⋙ forget₂ CommRingCat RingCat` with the sheaf condition directly. The two sheaves of
rings are the same sheaf, but seeing that needs `Tensor.ringSheaf` unfolded, and it is a plain
`def`, so instance search — which runs at `instances` transparency — will not do it. Left to
itself, `derivedDual Rc K ⊗ K` therefore takes its category from the inferred type of
`derivedDual Rc K`, the second spelling, and the monoidal structure carried by the `letI` at the
first spelling is not found. A type ascription on `derivedDual Rc K` does not help: the
application elaborator reads the implicit category off the *inferred* type of the argument, not
off the ascription. So `MonoidalCategoryStruct.tensorObj` and `CategoryTheory.tensorRightHomEquiv`
are applied with their category argument named, exactly as the uses of
`Functor.uncurry.obj (Tensor.sheafTensor _)` elsewhere name the pair of objects they act on; no
instance bridges the two spellings.

Mathlib's `CategoryTheory.ExactPairing X Y` is Stacks' "`Y` is a left dual of `X`" — the same
coevaluation `𝟙_ ⟶ X ⊗ Y`, the same evaluation `Y ⊗ X ⟶ 𝟙_` and the same two triangle
identities — although Mathlib names that `Y` the *right* dual `Xᘁ`. The same reading is taken by
`StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts` and
`StacksCore.CategoryTheory.Monoidal.Rigid.Retract`, and at the level of modules by
`Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand`.

That `ε` is not an unconstrained morphism of its type is
`AlgebraicGeometry.RingedSite.derivedDualEvaluation_eq`, already in the library: the
ringed-site evaluation is by definition the morphism matched with the identity of `K^∨` by the
tensor–internal-Hom bijection of Stacks 08DI, so since that bijection is injective it is zero
only if the identity of `K^∨` is.  It is not restated here in the monoidal spelling; the
restatement is the same fact and `rfl` for it does not elaborate within the recursion budget.

`derivedDualToLeftDual` is the transpose of the evaluation of `K^∨` across the pairing of `N`,
by `CategoryTheory.tensorRightHomEquiv`; it is a morphism of `D(O_X)` with a real body, built
only from the monoidal structure and the evaluation, and it requires no hypothesis on `K` beyond
the pairing.

**The statements below carry no side condition.** `HasSheafify` and `WEqualsLocallyBijective`
for the open-cover topology are instances, and additivity of `⊗_{O_X}` in each variable and the
existence of the total tensor complex are the library's own
`Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`, pinned below as file-local instances
at the site of opens of `X` because they are stated with the sections universe tied to the site
universes as `max u v`, which synthesis cannot solve against this cluster's diagonal `u` while
those universes are metavariables. This is the same discharge that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` and
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace` already made for
their own statements; the three local instances are named with a `Pairing` suffix here because
those two files declare theirs under the `Space` names in this same namespace.

The universes are the diagonal of the derived-internal-Hom cluster, with the derived category
the **standard** model: `attribute [local instance] HasDerivedCategory.standard` is in force
below, as it is in every file of this cluster, and in particular in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom`, which supplies
the monoidal structure, and in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing`, which supplies the
evaluation. Every statement below is therefore a statement about that one model, and nothing is
composed across two derived categories.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The unit of the monoidal structure on `D(O_X)` is the structure sheaf in degree zero.**
Together with `Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure`, which identifies
its tensor product with the derived tensor product, this is what lets a morphism built for the
derived tensor product and the derived structure sheaf be read as a morphism of the monoidal
category without any comparison. -/
theorem tensorUnit_derivedMonoidalStructure :
    letI := derivedMonoidalStructure Rc
    (𝟙_ (DerivedCategory (StructureSheafModules Rc))) =
      RingedSite.derivedStructureSheaf (ringedSite Rc) :=
  rfl

/-- **The evaluation map of the derived dual.** For an object `K` of `D(O_X)` on a ringed space,
with dual `K^∨ = RSheafHom(K, O_X)`, the evaluation is the morphism

`ε : K^∨ ⊗^L_{O_X} K ⟶ O_X`

matched with the identity of `K^∨` by the tensor–internal-Hom bijection of Stacks 08DI, under
which morphisms `K^∨ ⊗^L_{O_X} K ⟶ O_X` are morphisms `K^∨ ⟶ RSheafHom(K, O_X) = K^∨`. It is
stated for the monoidal structure of Stacks 0FPT on `D(O_X)`, whose tensor product is the derived
tensor product and whose unit is the structure sheaf in degree zero.  For a perfect `K` it is the
evaluation of the left dual of Example 0FPC (`Stacks.SheafOfModules.derivedDual_isLeftDual`). -/
def derivedDualEvaluation (K : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    MonoidalCategoryStruct.tensorObj (C := DerivedCategory (StructureSheafModules Rc))
        (derivedDual Rc K) K ⟶
      𝟙_ (DerivedCategory (StructureSheafModules Rc)) :=
  RingedSite.derivedDualEvaluation (ringedSite Rc) K

section LeftDual

variable (K N : DerivedCategory (StructureSheafModules Rc))

/-- **The canonical morphism from the derived dual to a left dual.** If `N` is a left dual of `K`
in `D(O_X)` — a coevaluation `O_X ⟶ K ⊗^L_{O_X} N` and an evaluation `N ⊗^L_{O_X} K ⟶ O_X`
satisfying the two triangle identities — then transposing the evaluation
`ε : K^∨ ⊗^L_{O_X} K ⟶ O_X` of `K^∨` across that pairing gives a canonical morphism
`K^∨ ⟶ N`. -/
def derivedDualToLeftDual
    (pair : letI := derivedMonoidalStructure Rc; ExactPairing K N) :
    derivedDual Rc K ⟶ N :=
  letI := derivedMonoidalStructure Rc
  letI := pair
  tensorRightHomEquiv (C := DerivedCategory (StructureSheafModules Rc)) (derivedDual Rc K) K N
      (𝟙_ (DerivedCategory (StructureSheafModules Rc)))
      (derivedDualEvaluation Rc K) ≫
    (λ_ N).hom

end LeftDual

end Stacks.SheafOfModules

end
