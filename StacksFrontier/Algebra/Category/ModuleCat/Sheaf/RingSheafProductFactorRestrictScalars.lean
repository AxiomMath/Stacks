module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings

/-!
# Restriction of scalars along the projection of a product presentation

Let `R ≅ ∏_i factor i` be a sheaf of commutative rings presented as a product
(`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`) and let
`projRing hp n : Tensor.ringSheaf R ⟶ Tensor.ringSheaf (factor n)` be the `n`-th projection.
The projection is surjective on sections, hence locally surjective; consequently restriction of
scalars along it is fully faithful, and extension of scalars along it is a left inverse of
restriction of scalars.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor.surjective_projRing_app`: the `n`-th projection
  of a product presentation is surjective on the sections over every object.
* `Stacks.SheafOfModules.RingSheafProductFactor.isLocallySurjective_projRing`: the `n`-th
  projection is locally surjective.
* `Stacks.SheafOfModules.RingSheafProductFactor.fullyFaithfulRestrictScalarsProjRing`:
  restriction of scalars along the projection is fully faithful.
* `Stacks.SheafOfModules.RingSheafProductFactor.extendScalarsRestrictScalarsProjRingIso`:
  `factor n ⊗_R L ≅ L` for every `factor n`-module `L` regarded as an `R`-module.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u t

namespace Stacks.SheafOfModules.RingSheafProductFactor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}
  {factor : ι → Sheaf J CommRingCat.{max u v}} {R : Sheaf J CommRingCat.{max u v}}
  (hp : ProductPresentation R factor)

/-- The `n`-th projection of a product presentation is surjective on the sections over every
object. -/
public theorem surjective_projRing_app (n : ι) (U : Cᵒᵖ) :
    Function.Surjective ((projRing hp n).hom.app U) := by
  classical
  exact fun b => ⟨hp.inclSection n U b, hp.app_inclSection_self n U b⟩

/-- The `n`-th projection of a product presentation is locally surjective. -/
public instance isLocallySurjective_projRing (n : ι) :
    Sheaf.IsLocallySurjective (projRing hp n) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_surjective J (projRing hp n).hom
    (surjective_projRing_app hp n)

/-- The `n`-th projection of a product presentation, as the morphism
`Stacks.FlatChangeOfRings.ringSheafMap (hp.π n)`, is locally surjective. -/
public instance isLocallySurjective_sheafCompose_map_pi (n : ι) :
    Sheaf.IsLocallySurjective (Stacks.FlatChangeOfRings.ringSheafMap.{v, u, max u v} (hp.π n)) :=
  isLocallySurjective_projRing hp n

/-- Restriction of scalars along the `n`-th projection of a product presentation is fully
faithful. -/
public noncomputable def fullyFaithfulRestrictScalarsProjRing (n : ι) :
    (_root_.SheafOfModules.restrictScalars.{max u v} (projRing hp n)).FullyFaithful :=
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective (projRing hp n)

section ExtendScalars

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The counit of the adjunction between extension and restriction of scalars along the `n`-th
projection is an isomorphism. -/
public instance isIso_extendScalarsAdjunction_counit (n : ι) :
    IsIso (Stacks.FlatChangeOfRings.extendScalarsAdjunction.{v, u, max u v} (hp.π n)).counit :=
  CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful _

/-- Extension of scalars along the `n`-th projection undoes restriction of scalars:
`factor n ⊗_R L ≅ L` for a `factor n`-module `L` regarded as an `R`-module, the isomorphism being
the counit of the adjunction. -/
public noncomputable def extendScalarsRestrictScalarsProjRingIso (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    (Stacks.FlatChangeOfRings.extendScalars.{v, u, max u v} (hp.π n)).obj
        ((_root_.SheafOfModules.restrictScalars.{max u v} (projRing hp n)).obj L) ≅ L :=
  (asIso (Stacks.FlatChangeOfRings.extendScalarsAdjunction.{v, u, max u v}
    (hp.π n)).counit).app L

end ExtendScalars

end Stacks.SheafOfModules.RingSheafProductFactor

end
