module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsComparisonMap
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
import StacksCore.Tactic.StacksAttribute

/-!
# Extension of scalars for sheaves of modules, by sheafification

A morphism of sheaves of commutative rings induces an extension-of-scalars functor on sheaves
of modules: the sectionwise tensor-product presheaf of Tag 03CU, followed by sheafification.
Its value is the sheaf denoted `O₂ ⊗[O₁] G` in the source.

## Main definitions

* `Stacks.Sheaves.ChangeOfRings.changeOfRings`: the extension-of-scalars functor.

## Implementation notes

The module universe is left independent of the universe of the ring sections, so that this
applies to sheaves of modules whose carriers are larger than the structure sheaf's sections.
`Stacks.Sheaves.RingedToposModules.extendScalars` is the same construction with the two
universes identified, and is the form in which tag 03CZ is registered; it cannot be used where
the universes must differ.

The index sheaf of rings is `Stacks.Sheaves.Differentials.ringSheaf`, the composite of the sheaf of
commutative rings with `forget₂ CommRingCat RingCat`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

universe v v' u

open CategoryTheory

namespace Stacks.Sheaves.ChangeOfRings

variable {C : Type u} [Category.{v'} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (f : O₁ ⟶ O₂)

/-- Extension of scalars for sheaves of modules along a morphism of sheaves of commutative
rings. It is the sectionwise tensor-product presheaf, followed by sheafification. -/
noncomputable def changeOfRings
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    SheafOfModules.{max u v} (Stacks.Sheaves.Differentials.ringSheaf O₁) ⥤
      SheafOfModules.{max u v} (Stacks.Sheaves.Differentials.ringSheaf O₂) := by
  let S := PresheafOfModules.sheafification.{max u v, v', u, u}
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf O₂).obj)
  exact SheafOfModules.forget (Stacks.Sheaves.Differentials.ringSheaf O₁) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings.{u, v', u, max u v} f.hom ⋙ S

end Stacks.Sheaves.ChangeOfRings

/-!
# Extension and restriction of scalars for sheaves of modules

A morphism of sheaves of commutative rings on a site induces an extension-of-scalars functor on
sheaves of modules, namely the sectionwise tensor product followed by sheafification, and that
functor is left adjoint to restriction of scalars. The adjunction records both the canonical
bijection `Hom_{O₁}(G, F|_{O₁}) ≃ Hom_{O₂}(O₂ ⊗_{O₁} G, F)` and its naturality.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` is the adjunction,
  registered for Stacks 03CZ.

## Implementation notes

Both the functor and the adjunction are constructed in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules`, by the route the source
prescribes: the presheaf-level change-of-rings adjunction of Stacks 03CU
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`) composed with the
sheafification adjunction for presheaves of modules, restricted along the fully faithful
inclusion of sheaves of modules into presheaves of modules. This part of the file only attaches
the tag, so that the development does not acquire a second extension-of-scalars functor.

A second construction of the same adjunction, specialised to a small site whose objects,
morphisms and ring sections all lie in one universe, is
`Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction`; it is obtained from Mathlib's
`SheafOfModules.pullbackPushforwardAdjunction` along the identity functor of the site. The
declaration tagged here is the one valid on an arbitrary site.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

add_to_stacks 03CZ Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction

end
