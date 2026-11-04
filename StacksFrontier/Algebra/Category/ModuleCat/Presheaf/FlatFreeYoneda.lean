module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.RingTheory.Flat.CategoryTheory
import StacksCore.Tactic.StacksAttribute

/-!
# The lower-shriek extension of the rank-one module is a flat presheaf of modules

For `U` an object of a site and `O` a presheaf of commutative rings, the extension by zero
`j_{U!}O_U` of the rank-one module from the slice over `U` is a flat presheaf of
`O`-modules.

## Main results

* `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeObj`: the free presheaf of modules on a
  presheaf of types is
  flat.
* `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`: `j_{U!}O_U` is a flat presheaf of
  modules.
* `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_of_iso`: flatness is invariant under isomorphism,
  so the previous
  statement holds of any presheaf of modules isomorphic to `j_{U!}O_U`.

## Implementation notes

`j_{U!}O_U` is identified with `PresheafOfModules.freeObj (yoneda.obj U)`, the free
presheaf of `O`-modules on the presheaf of types represented by `U`. That is the correct
identification, and it is Mathlib's: the whole content of `j_{U!}O_U` is its universal
property `Hom_O(j_{U!}O_U, M) ≃ M(U)`, natural in `M`, and this is exactly
`PresheafOfModules.freeYonedaEquiv` together with its naturality
`PresheafOfModules.freeYonedaEquiv_comp`. Since `freeObj` is objectwise the free module on
`(yoneda.obj U)(X)`, it is objectwise flat, and flatness of presheaves of modules is an
objectwise condition because finite limits and finite colimits of presheaves of modules are
computed objectwise. `isFlat_of_iso` is supplied so that the conclusion transports to any
other construction of `j_{U!}O_U`, which is determined up to isomorphism by that universal
property.

The identification itself is no longer only an assertion of these notes: at the sheaf level it
is `SheafOfModules.extensionByZeroIsoSheafifiedFreeYoneda`
(`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroGenerators.lean`), which exhibits
`j_{U!}O_U` as the sheafification of the free presheaf on the representable at `U`.  Both
objects corepresent `M ↦ M(U)`, the comparison matches the two generating sections, and Yoneda
finishes it.  So `isFlat_of_iso_freeYoneda` is a convenience for other presentations rather
than the only available route, and a consumer wanting flatness of the *sheaf* `j_{U!}O_U`
should chain that isomorphism with this file's `isFlat_freeYoneda` and Tag 03ET.

Flatness here is `AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat`
(Tag 03ER part (1)), exactness of the objectwise tensor endofunctor. The module universe is
taken equal to the ring universe, which is what both Mathlib's free presheaf of modules and
Mathlib's `Module.Flat`-to-exactness bridge require.

## References

* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace Stacks.PresheafOfModules.FlatFreeYoneda

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C]

/-! ### Flatness of presheaves of modules is an objectwise condition -/

section Objectwise

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Flatness of a presheaf of modules is invariant under isomorphism: the objectwise tensor
endofunctor is functorial in the tensor factor, via the identification of the objectwise
tensor product with Mathlib's monoidal one. -/
lemma isFlat_of_iso {F F' : PresheafOfModules.{w} (ringPresheaf O)} (e : F ≅ F')
    (hF : PresheafOfModules.IsFlat F) : PresheafOfModules.IsFlat F' :=
  (exactFunctor _ _).prop_of_iso
    (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso O F ≪≫ (curriedTensor _).flip.mapIso e ≪≫
      (Stacks.SheafOfModules.FlatCoproduct.tensorRightIso O F').symm) hF

end Objectwise

/-! ### The free presheaf of modules on a presheaf of types is flat -/

section Free

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- **The free presheaf of `O`-modules on a presheaf of types is flat**: over each object
of the site its sections are a free, hence flat, module. -/
lemma isFlat_freeObj (F : Cᵒᵖ ⥤ Type w) :
    PresheafOfModules.IsFlat (_root_.PresheafOfModules.freeObj (R := ringPresheaf O) F) :=
  PresheafOfModules.isFlat_of_objectwise_flat _ fun _ ↦ Module.Flat.finsupp _

end Free

/-! ### `j_{U!}O_U` is flat -/

section Yoneda

/-- **`j_{U!}O_U` is a flat presheaf of `O`-modules.** The extension by zero of the
rank-one module from the slice over `U` is the free presheaf of modules on the presheaf of
types represented by `U`; that is its universal property
`PresheafOfModules.freeYonedaEquiv`, `Hom_O(j_{U!}O_U, M) ≃ M(U)` naturally in `M` by
`PresheafOfModules.freeYonedaEquiv_comp`. The ring universe is the hom universe of the
site, which is where Mathlib states that universal property. -/
theorem isFlat_freeYoneda (O : Cᵒᵖ ⥤ CommRingCat.{v}) (U : C) :
    PresheafOfModules.IsFlat
      (_root_.PresheafOfModules.freeObj (R := ringPresheaf O) (yoneda.obj U)) :=
  isFlat_freeObj O _

/-- `j_{U!}O_U` is flat in any presentation: the universal property determines it up to
isomorphism, and flatness is invariant under isomorphism. -/
theorem isFlat_of_iso_freeYoneda (O : Cᵒᵖ ⥤ CommRingCat.{v}) (U : C)
    (P : PresheafOfModules.{v} (ringPresheaf O))
    (e : _root_.PresheafOfModules.freeObj (R := ringPresheaf O) (yoneda.obj U) ≅ P) :
    PresheafOfModules.IsFlat P :=
  isFlat_of_iso O e (isFlat_freeYoneda O U)

end Yoneda

end Stacks.PresheafOfModules.FlatFreeYoneda
