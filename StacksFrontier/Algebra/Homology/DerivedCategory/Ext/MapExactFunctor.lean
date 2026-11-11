module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The map on `Ext¹` induced by an exact functor sends `E` to `F(E)`

Let `F : C ⥤ D` be an exact functor between abelian categories. For objects `A, B` of `C`,
Mathlib's `CategoryTheory.Functor.mapExtAddHom` is an additive group homomorphism
`Ext¹_C(B, A) →+ Ext¹_D(F B, F A)`. Here `Ext¹` is the group of extensions of Stacks 010K: every
class is the class `extClass` of a short exact sequence `0 → A → E → B → 0`, and two such classes
agree exactly when the extensions are isomorphic
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`, in
`StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing`). This file records
that `F.mapExtAddHom` sends the class of an extension `E` to the class of its image `F(E)`, which
is Stacks 010O.

## Main results

* `CategoryTheory.Functor.mapExtAddHom_one_extClass`: the group homomorphism
  `F.mapExtAddHom B A 1` maps the class of an extension `E` to the class of `F(E)`.
-/

@[expose] public section

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- **Stacks 010O.** An exact functor `F : C ⥤ D` of abelian categories induces, for all objects
`A, B` of `C`, the abelian group homomorphism `F.mapExtAddHom B A 1 : Ext¹(B, A) →+
Ext¹(F B, F A)`, and it maps the class of an extension `0 → A → E → B → 0` to the class of the
extension `0 → F A → F E → F B → 0`. -/
@[stacks 010O "The group homomorphism is `CategoryTheory.Functor.mapExtAddHom` in degree one;
`Ext¹` is the group of extensions by `CategoryTheory.Abelian.Ext.extClass`."]
theorem Functor.mapExtAddHom_one_extClass (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {E : ShortComplex C}
    (hE : E.ShortExact) :
    F.mapExtAddHom E.X₃ E.X₁ 1 hE.extClass = (hE.map_of_exact F).extClass := by
  rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_extClass]

end CategoryTheory
