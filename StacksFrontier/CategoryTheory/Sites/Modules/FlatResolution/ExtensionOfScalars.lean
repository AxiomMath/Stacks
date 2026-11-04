module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction

/-!
# Extension of scalars for sheaves of modules, with four independent universes

A morphism `f : O₁ ⟶ O₂` of sheaves of commutative rings on a site induces the
extension-of-scalars functor `M ↦ O₂ ⊗_{O₁} M` on sheaves of modules: the sectionwise tensor
product presheaf, sheafified. It is left adjoint to restriction of scalars along `f`.

## Main definitions

* `Stacks.Sheaves.ChangeOfRings.extensionOfScalars`: the extension-of-scalars functor.

## Main results

* `Stacks.Sheaves.ChangeOfRings.extensionRestrictionAdjunction`: extension of scalars is left
  adjoint to restriction of scalars.

## Implementation notes

The construction is the one of `Stacks.Sheaves.ChangeOfRings.changeOfRings` and of
`Stacks.Sheaves.RingedToposModules.extendScalars`, and this file adds nothing to the
mathematics: the presheaf-level change of rings is Stacks 03CU
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`, with its adjunction) and sheafification of
  presheaves of modules
is Mathlib's. What is new is only that the four universes — the objects of the site, its
morphisms, the sections of the sheaves of rings, and the carriers of the modules — are left
independent of one another. `changeOfRings` ties the ring universe to the universe of objects
of the site, and `extendScalars` ties the module universe to the ring universe; neither
restriction is needed, and a consumer working with modules strictly larger than the structure
sheaf on a site whose objects are strictly smaller cannot use either.

The sheaves of rings are indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`,
the image of a sheaf of commutative rings under `sheafCompose`, which is the form the
flatness predicates of Stacks 03ER are stated at.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory

universe t v u w

namespace Stacks.Sheaves.ChangeOfRings


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The morphism of underlying sheaves of rings induced by a morphism of sheaves of
commutative rings. -/
abbrev ringSheafMap (f : O₁ ⟶ O₂) :
    Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂ :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map f

variable [HasWeakSheafify J AddCommGrpCat.{max w t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w t}]

/-- Extension of scalars for sheaves of modules along a morphism of sheaves of commutative
rings: the sectionwise tensor product `O₂ ⊗_{O₁} -` of Stacks 03CU, followed by
sheafification. -/
noncomputable def extensionOfScalars (f : O₁ ⟶ O₂) :
    _root_.SheafOfModules.{max w t} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⥤
      _root_.SheafOfModules.{max w t} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) := by
  let S := _root_.PresheafOfModules.sheafification.{max w t, v, w, u}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)
  exact _root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings.{u, v, w, max w t} f.hom ⋙ S

/-- **Stacks 03CZ.** Extension of scalars is left adjoint to restriction of scalars. The
adjunction records both the canonical bijection
`Hom_{O₂}(O₂ ⊗_{O₁} M, N) ≃ Hom_{O₁}(M, N|_{O₁})` and its naturality.

It is assembled from `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the *data*
  form of Tag 03CU, so its
unit is the computable morphism `x ↦ 1 ⊗ x` followed by sheafification; see
`Stacks.SheafOfModules.ComplexLifting.extensionRestrictionAdjunction_unit_app`. -/
noncomputable def extensionRestrictionAdjunction (f : O₁ ⟶ O₂) :
    extensionOfScalars.{t} f ⊣
      _root_.SheafOfModules.restrictScalars.{max w t} (ringSheafMap f) :=
  Adjunction.restrictFullyFaithful
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction.{u, v, w, max w t} f.hom).comp
      (_root_.PresheafOfModules.sheafificationAdjunction.{max w t, v, w, u}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)))
    (_root_.SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (Functor.FullyFaithful.id _)
    (eqToIso (Functor.comp_id (extensionOfScalars.{t} f)).symm)
    (eqToIso (Functor.id_comp _))

end Stacks.Sheaves.ChangeOfRings

end
