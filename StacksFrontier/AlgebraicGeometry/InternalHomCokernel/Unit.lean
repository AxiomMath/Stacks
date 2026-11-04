module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomMonoidalComparison

/-!
# The internal Hom out of the structure sheaf is the identity

Let `O` be a presheaf of commutative rings on a category `C`.  The internal Hom of
[Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) out of the unit module `O` is the
target itself:

`Hom_O(O, G) ≅ G`.

This is the rank-one case of the identification of the dual of a finite free module with a
finite free module, which is the step that the proof of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) needs in order to read a dualized
finite presentation as a kernel of a map between finite free modules.

## Main definitions

* `unitInternalHomIso`: the isomorphism `Hom_O(O, G) ≅ G`.

## Implementation notes

The proof is two existing isomorphisms and no computation on sections.  The unit module is the
monoidal unit of presheaves of modules, `CategoryTheory.MonoidalClosed.unitNatIso` identifies
the monoidal-closed internal hom out of the monoidal unit with the identity functor, and
`Stacks.PresheafOfModules.InternalHom.ihomIsoInternalHom` --- Tag 03EO --- identifies
that internal hom with Tag 03EM's internal Hom presheaf.  In particular no section-level
formula, and no choice of a generator of the unit module, enters.

`StacksFrontier/AlgebraicGeometry/ReflexiveHull/UnitDual.lean` proves the same statement for a
scheme and the target `𝒪_X`, with the explicit section formula "a local endomorphism of `𝒪_U` is
multiplication by its value at `1`", and that explicit form is what the reflexivity arguments
there consume.  The present statement is the formula-free version over an arbitrary site.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CategoryTheory.MonoidalClosed

universe v u

namespace Stacks.PresheafOfModules.InternalHom

/-- **The internal Hom out of the unit module is the identity**: `Hom_O(O, G) ≅ G`. -/
public noncomputable def unitInternalHomIso {C : Type u} [Category.{v} C]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v}) (G : PresheafOfModules.{max u v} (Oforget O)) :
    internalHom O (PresheafOfModules.unit (Oforget O)) G ≅ G :=
  (ihomIsoInternalHom O (PresheafOfModules.unit (Oforget O)) G).symm ≪≫
    (unitNatIso (C := PresheafOfModules.{max u v} (Oforget O))).symm.app G

end Stacks.PresheafOfModules.InternalHom

end
