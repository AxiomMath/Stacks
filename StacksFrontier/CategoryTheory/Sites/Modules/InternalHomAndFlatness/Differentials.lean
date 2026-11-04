module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials

/-!
# The associated sheaf of a presheaf of commutative rings

Let `O` be a presheaf of commutative rings on a site `(C, J)`. Sheafification produces a sheaf
of commutative rings `O^#`, and forgetting commutativity turns the unit of that sheafification
into a morphism of presheaves of rings `O ⟶ (O^#)_ring`. This file constructs that morphism and
records that it is locally injective and locally surjective, which is what identifies it as the
sheafification map of the underlying presheaf of rings.

These are the comparison maps along which the presheaf of relative Kähler differentials of a
morphism `O₁ ⟶ O₂` is compared with the sheaf of relative differentials of `O₁^# ⟶ O₂^#`
(Stacks 08TP). Sheaves of modules over a sheaf of rings are formed over
`Stacks.SheafOfModules.Tensor.ringSheaf`, so that is the target used here.

## Main definitions

* `Stacks.SheafOfModules.associatedCommRingSheaf`: the associated sheaf of a presheaf of
  commutative rings.
* `Stacks.SheafOfModules.toAssociatedRingSheaf`: the sheafification map of a presheaf of
  commutative rings, read as a morphism of presheaves of rings.
* `Stacks.SheafOfModules.associatedCommRingSheafMap`: the functoriality of the associated
  sheaf.

## Main results

* `Stacks.SheafOfModules.toAssociatedRingSheaf_isLocallyInjective` and
  `Stacks.SheafOfModules.toAssociatedRingSheaf_isLocallySurjective`: the sheafification map is
  locally bijective, when sheafification on commutative rings is.

## References

* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the sheaf of relative
  differentials these maps compare with.
-/

@[expose] public section

open CategoryTheory

universe v v₁ u u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- The associated sheaf of a presheaf of commutative rings. -/
noncomputable abbrev associatedCommRingSheaf [HasWeakSheafify J CommRingCat.{u}]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj O

/-- The ring-valued sheafification map of a presheaf of commutative rings. -/
noncomputable def toAssociatedRingSheaf [HasWeakSheafify J CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    O ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (associatedCommRingSheaf J O)).obj :=
  Functor.whiskerRight ((toSheafification J CommRingCat.{u}).app O)
    (forget₂ CommRingCat.{u} RingCat.{u})

/-- The ring-valued sheafification map of a presheaf of commutative rings is locally
injective. -/
instance toAssociatedRingSheaf_isLocallyInjective [HasWeakSheafify J CommRingCat.{u}]
    [J.WEqualsLocallyBijective CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Presheaf.IsLocallyInjective J (toAssociatedRingSheaf J O) := by
  let : Presheaf.IsLocallyInjective J (toSheafify J O) :=
    (J.W_toSheafify O).isLocallyInjective
  exact ⟨fun x y h ↦
    Presheaf.equalizerSieve_mem J ((toSheafification J CommRingCat.{u}).app O) x y h⟩

/-- The ring-valued sheafification map of a presheaf of commutative rings is locally
surjective. -/
instance toAssociatedRingSheaf_isLocallySurjective [HasWeakSheafify J CommRingCat.{u}]
    [J.WEqualsLocallyBijective CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Presheaf.IsLocallySurjective J (toAssociatedRingSheaf J O) := by
  let : Presheaf.IsLocallySurjective J (toSheafify J O) :=
    (J.W_toSheafify O).isLocallySurjective
  exact ⟨fun x ↦ Presheaf.imageSieve_mem J ((toSheafification J CommRingCat.{u}).app O) x⟩

/-- The morphism between the associated sheaves induced by a morphism of presheaves. -/
noncomputable abbrev associatedCommRingSheafMap [HasWeakSheafify J CommRingCat.{u}]
    {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (f : O₁ ⟶ O₂) :
    associatedCommRingSheaf J O₁ ⟶ associatedCommRingSheaf J O₂ :=
  (presheafToSheaf J CommRingCat.{u}).map f

end Stacks.SheafOfModules
