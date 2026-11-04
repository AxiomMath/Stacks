module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.GradedSections.Braided
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# The commutativity constraint of `Mod(O)` is the symmetry constraint of the tensor product sheaf

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensorBraiding.lean` identifies the
commutativity constraint of `SheafOfModules.monoidalCategorySheafTensor` with the braiding of the
sheafified tensor product. This file restates that identification against
`Stacks.SheafOfModules.tensorSheafBraiding`, the spelling in which [Stacks, Tag 01CU] states the
symmetry constraint, and deduces that an invertible module has trivial self-braiding for the
re-seated structure. It is a separate module because it needs imports that
`MonoidalSheafTensorBraiding.lean` does not have.

## Main results

* `SheafOfModules.braiding_sheafTensor_eq`: the commutativity constraint of the re-seated
  monoidal structure is `Stacks.SheafOfModules.tensorSheafBraiding`.
* `SheafOfModules.hasTrivialSelfBraiding_sheafTensor`: an invertible sheaf of modules has trivial
  self-braiding for the re-seated monoidal structure.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal

universe v u

/-! ### The braiding as the tensor product sheaf's own symmetry constraint

The two comparison lemmas are proved with the localized monoidal and braided structures active as
local instances; `SheafOfModules.braiding_sheafTensor_eq` and the instance for invertible modules
are stated without them, at the re-seated structure.
-/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

section Localized

attribute [local instance] monoidalCategory braidedCategory

/-- **`SheafOfModules.sheafTensorIso` carries the localized braiding to the braiding of the
re-seated structure.**  This is `CategoryTheory.MonoidalCategory.reseat_braiding_aux` at the
re-seating that produces `SheafOfModules.monoidalCategorySheafTensor`; the one definitional
equality crossed is that the component of `SheafOfModules.sheafTensorNatIso` is
`SheafOfModules.sheafTensorIso`. -/
theorem sheafTensorIso_comp_braiding :
    (sheafTensorIso R A B).hom ≫
        (@BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
          (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
            (symmetricCategorySheafTensor R)) A B).hom =
      (β_ A B).hom ≫ (sheafTensorIso R B A).hom :=
  reseat_braiding_aux (sheafTensorNatIso R) (unitIso R) A B

end Localized

section Crossing

attribute [local instance] monoidalCategory braidedCategory
  Stacks.SheafOfModules.monoidalCategory Stacks.SheafOfModules.braidedCategory

/-- **`SheafOfModules.sheafTensorIso` carries the localized braiding to
`Stacks.SheafOfModules.tensorSheafBraiding`.**  This is
`Stacks.SheafOfModules.braiding_hom_eq`, whose two localized structures differ from the ones here
only in their unit comparison; the braidings and the two comparison isomorphisms are
definitionally equal on their `hom` fields, and that is the crossing this declaration exists to
pay. -/
theorem braiding_comp_sheafTensorIso :
    (β_ A B).hom ≫ (sheafTensorIso R B A).hom =
      (sheafTensorIso R A B).hom ≫
        (Stacks.SheafOfModules.tensorSheafBraiding R.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf R).property A B).hom :=
  Stacks.SheafOfModules.braiding_hom_eq R.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf R).property A B

end Crossing

/-- **The commutativity constraint of the re-seated monoidal structure is the symmetry constraint
`Stacks.SheafOfModules.tensorSheafBraiding` of the tensor product sheaf of [Stacks, Tag 01CA].**

This is the last structural morphism of `SheafOfModules.monoidalCategorySheafTensor` that was not
known to be the tensor product sheaf's own.  Together with
`SheafOfModules.leftUnitor_sheafTensor_eq` and `SheafOfModules.rightUnitor_sheafTensor_eq` it
makes the re-seated symmetric monoidal structure the structure of Tag 01CA on the nose. -/
theorem braiding_sheafTensor_eq :
    (@BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
        (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
          (symmetricCategorySheafTensor R)) A B).hom =
      (Stacks.SheafOfModules.tensorSheafBraiding R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A B).hom :=
  (cancel_epi (sheafTensorIso R A B).hom).mp
    ((sheafTensorIso_comp_braiding R A B).trans (braiding_comp_sheafTensorIso R A B))

/-- `SheafOfModules.braiding_sheafTensor_eq`, as an equality of isomorphisms. -/
theorem braiding_sheafTensor_eq_iso :
    @BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
        (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
          (symmetricCategorySheafTensor R)) A B =
      Stacks.SheafOfModules.tensorSheafBraiding R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A B :=
  Iso.ext (braiding_sheafTensor_eq R A B)

/-- **An invertible sheaf of modules has trivial self-braiding for the re-seated monoidal
structure.**  The braiding there is `Stacks.SheafOfModules.tensorSheafBraiding` by
`SheafOfModules.braiding_sheafTensor_eq`, and that is the identity on an invertible module by
`Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl`, the commutativity constraint of
[Stacks, Tag 01CU].

This is the hypothesis `Stacks.GradedSections.HasTrivialSelfBraiding` that the tensor-power
calculus of an invertible module carries — `Stacks.Monoidal.braiding_eval_snake` is where it is
consumed.  `Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding` supplies it for the localized
structure only, so without this instance the hypothesis is not available at the structure the
tensor product sheaf is stated over. -/
instance hasTrivialSelfBraiding_sheafTensor
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    [AlgebraicGeometry.SheafOfModules.IsInvertible R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property L] :
    @Stacks.GradedSections.HasTrivialSelfBraiding _ _ (monoidalCategorySheafTensor R)
      (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
        (symmetricCategorySheafTensor R)) L :=
  @Stacks.GradedSections.HasTrivialSelfBraiding.mk _ _ (monoidalCategorySheafTensor R)
    (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
      (symmetricCategorySheafTensor R)) L
    ((braiding_sheafTensor_eq R L L).trans
      (congrArg Iso.hom (Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property L)))

end SheafOfModules

end
