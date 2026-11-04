module

public import StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Basic
public import StacksFrontier.AlgebraicGeometry.PicardTrivialOpenUFD.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of a scheme

The Picard group of a scheme `X`: the group of isomorphism classes of invertible `𝒪_X`-modules
under tensor product, with invertibility given by `Stacks.Ample.IsInvertibleModule`.

Every declaration below specialises its counterpart in
`StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Basic`, stated there over an arbitrary ringed
site: `PicardGroup` for `schemePicardGroup`, `classOf` for `schemeClassOf`,
`classOf_eq_classOf_iff`, `classOf_tensorSheaf` and `classOf_eq_one_iff` for their
`scheme`-prefixed forms, and `subsingleton_iff` for `hasTrivialPicard_iff_subsingleton`. The
invertibility classes agree reducibly, `Stacks.Ample.IsInvertibleModule` being an `abbrev` for the
site-level `IsInvertible`.

## Main definitions

* `Stacks.SheafPicardGroup.schemePicardGroup`: **the Picard group `Pic X` of a scheme.**
* `Stacks.SheafPicardGroup.schemeClassOf`: the Picard class of an invertible `𝒪_X`-module.

## Main results

* `Stacks.SheafPicardGroup.schemeClassOf_eq_schemeClassOf_iff`: two invertible `𝒪_X`-modules
  have the same Picard class exactly when they are isomorphic.
* `Stacks.SheafPicardGroup.schemeClassOf_tensorSheaf`: multiplication is tensor product.
* `Stacks.SheafPicardGroup.hasTrivialPicard_iff_subsingleton`: **`HasTrivialPicard X` is
  exactly subsingletonity of `Pic X`.**

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Stacks.SheafOfModules.TensorSheafification AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafPicardGroup

variable (X : Scheme.{u})

/-- **The Picard group `Pic X` of a scheme**: the isomorphism classes of invertible
`𝒪_X`-modules under tensor product. -/
@[stacks 01CX "the Picard group",
  ega "0 5.4.7" "special case",
  ega "IV 21.3.2",
  sga "4 IX 3.3",
  sga "4½ Arcata 2.2.3",
  sga "6 X 5.1" "special case"]
noncomputable abbrev schemePicardGroup : Type (u + 1) :=
  PicardGroup X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

/-- The Picard class of an invertible `𝒪_X`-module. -/
@[ega "IV 21.3.2", sga "4½ Arcata 2.2.3"]
noncomputable abbrev schemeClassOf (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    schemePicardGroup X :=
  classOf X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- **Two invertible `𝒪_X`-modules have the same Picard class exactly when they are
isomorphic.** -/
@[stacks 01CX "the Picard group", ega "IV 21.3.2" "partial"]
theorem schemeClassOf_eq_schemeClassOf_iff (L N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X N] :
    schemeClassOf X L = schemeClassOf X N ↔ Nonempty (L ≅ N) :=
  classOf_eq_classOf_iff X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L N

/-- **Multiplication in `Pic X` is tensor product.** -/
@[stacks 01CX "addition is tensor product"]
theorem schemeClassOf_tensorSheaf (L N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X N]
    [Stacks.Ample.IsInvertibleModule X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj (L)).obj (N)))] :
    schemeClassOf X
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj (L)).obj (N))) =
      schemeClassOf X L * schemeClassOf X N :=
  classOf_tensorSheaf X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L N

/-- A Picard class on a scheme is trivial exactly when the module is isomorphic to `𝒪_X`. -/
theorem schemeClassOf_eq_one_iff (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    schemeClassOf X L = 1 ↔ Nonempty (L ≅ Stacks.Ample.unitModule X) :=
  classOf_eq_one_iff X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- **`Stacks.PicardTrivialOpenUFD.HasTrivialPicard X` is exactly subsingletonity of
`Pic X`.** -/
theorem hasTrivialPicard_iff_subsingleton :
    Stacks.PicardTrivialOpenUFD.HasTrivialPicard X ↔ Subsingleton (schemePicardGroup X) :=
  (subsingleton_iff X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)).symm

end Stacks.SheafPicardGroup

end
