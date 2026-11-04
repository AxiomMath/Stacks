module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Extension of scalars is the sheafified tensor product by the target ring sheaf

Let `θ : A₁ ⟶ A₂` be a morphism of sheaves of commutative rings on a site. Extension of
scalars along `θ` is the sectionwise tensor product `A₂ ⊗_{A₁} -` followed by sheafification,
and the sheafified tensor product by a module `L` is `L ⊗_{A₁} -` followed by sheafification.
Taking `L` to be `A₂` read as a sheaf of `A₁`-modules, the two constructions agree: reading an
`A₂`-module as an `A₁`-module along `θ`, extension of scalars *is* tensoring by `A₂`.

This is the identification the Stacks project makes when it writes the sheaf of meromorphic
sections of `L` as `L ⊗_{𝒪_X} K_X` rather than as the extension of scalars of `L` along
`𝒪_X ⟶ K_X`.

## Main definitions

* `Stacks.Sheaves.ChangeOfRings.tensorToExtendScalars`: the natural map from the sectionwise
  tensor product `A₂ ⊗_{A₁} M` to the sections of the extension of scalars of `M`, read as a
  map of presheaves of `A₁`-modules. It is the sheafification unit, restricted along `θ`.
* `Stacks.Sheaves.ChangeOfRings.extendScalarsTensorLeftUniversal`: the proof that extension of
  scalars, read back as a functor on `A₁`-modules, has the universal property of tensoring by
  `A₂`.

## Main results

* `Stacks.Sheaves.ChangeOfRings.extendScalarsCompRestrictScalarsIso`: the natural isomorphism
  identifying extension of scalars along `θ`, followed by restriction of scalars, with the
  sheafified tensor product by `A₂`.
* `Stacks.Sheaves.ChangeOfRings.changeOfRingsCompRestrictScalarsIso`: the same statement for
  `Stacks.Sheaves.ChangeOfRings.changeOfRings`, the form stated for sheaves of commutative
  rings rather than for presheaves carrying a sheaf hypothesis.

## Implementation notes

The isomorphism is obtained from the universal property rather than built by hand on sections.
`AlgebraicGeometry.SheafOfModules.TensorLeftUniversal` characterises a tensor functor by the
family of maps out of the sectionwise tensor products, and
`AlgebraicGeometry.SheafOfModules.TensorLeftUniversal.uniqueIso` identifies any two functors
carrying that property. So all that has to be produced is the universal property for extension
of scalars, and there it is the sheafification universal property in disguise: a morphism of
sheaves of `A₁`-modules out of the extension of scalars of `M` is a morphism of presheaves out
of `A₂ ⊗_{A₁} M`, because the sheafification unit is locally bijective and the target is a
sheaf.

Two defeq identifications carry the argument and are used silently, both checked by `rfl`:
restricting the sectionwise tensor product `A₂ ⊗_{A₁} M` back along `θ` is the monoidal
product of `A₂` with `M` in presheaves of `A₁`-modules, on objects and on morphisms alike; and
`PresheafOfModules.restrictScalars` along an identity is the identity functor.

The module tensored by, `A₂` read as a sheaf of `A₁`-modules, is spelled out as the restriction
of scalars of the unit sheaf of `A₂`-modules along `θ`.

`Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁` and
`Stacks.Sheaves.RingedToposModules.commRingSheaf J A₁ h₁` are the same sheaf of rings, but the
first is a `def` and the second an `abbrev`, so instance search — being syntactic — does not
cross between them. The local-bijectivity instances for `tensorToExtendScalars` are therefore
stated at the `Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling, which is the
one the universal property uses.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/


@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace Stacks.Sheaves.ChangeOfRings

open Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Presheaves of modules over the structure sheaf of rings are monoidal, `A₁` being
commutative. The two spellings of that sheaf of rings are the same term but not the same
syntax, so the instance is restated here. -/
noncomputable local instance :
    MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁).obj) := by
  change MonoidalCategory (PresheafOfModules.{u}
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  infer_instance

/-- The canonical map from the sectionwise tensor product `A₂ ⊗_{A₁} M` into the sections of the
extension of scalars of `M`, as a natural transformation of functors into presheaves of
`A₁`-modules. It is the unit of the sheafification of presheaves of `A₂`-modules, read along
`θ`; the source is the monoidal product of `A₂` with `M`, which is that sectionwise tensor
product read along `θ`. -/
noncomputable def tensorToExtendScalars :
    SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁) ⋙
        tensorLeft ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
          (SheafOfModules.unit (commRingSheaf J A₂ h₂))).val ⟶
      (extendScalars J θ h₁ h₂ ⋙
          SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)) ⋙
        SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁) :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
        Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ)
      (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit)
    (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ)

/-- The component of `tensorToExtendScalars` at a sheaf of `A₁`-modules `M` is locally
injective. -/
instance isLocallyInjective_tensorToExtendScalars
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁)) :
    PresheafOfModules.IsLocallyInjective J ((tensorToExtendScalars J θ h₁ h₂).app M) := by
  change Presheaf.IsLocallyInjective J
    (CategoryTheory.toSheafify J ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj
      M.val).presheaf)
  infer_instance

/-- The component of `tensorToExtendScalars` at a sheaf of `A₁`-modules `M` is locally
surjective. -/
instance isLocallySurjective_tensorToExtendScalars
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf A₁ h₁)) :
    PresheafOfModules.IsLocallySurjective J ((tensorToExtendScalars J θ h₁ h₂).app M) := by
  change Presheaf.IsLocallySurjective J
    (CategoryTheory.toSheafify J ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj
      M.val).presheaf)
  infer_instance

/-- Extension of scalars along `θ`, followed by restriction of scalars, has the universal
property of tensoring by `A₂`: every map of presheaves of `A₁`-modules out of `A₂ ⊗_{A₁} M`
into a sheaf factors uniquely through it. The factorisation is the sheafification universal
property, the `forget` functor on sheaves of modules being fully faithful and the map
`tensorToExtendScalars` locally bijective. -/
noncomputable def extendScalarsTensorLeftUniversal :
    AlgebraicGeometry.SheafOfModules.TensorLeftUniversal A₁ h₁
      ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
        (SheafOfModules.unit (commRingSheaf J A₂ h₂)))
      (extendScalars J θ h₁ h₂ ⋙
        SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)) where
  ι := tensorToExtendScalars J θ h₁ h₂
  bijective M N :=
    ((SheafOfModules.fullyFaithfulForget (commRingSheaf J A₁ h₁)).homEquiv.trans
      (PresheafOfModules.homEquivOfIsLocallyBijective
        (f := (tensorToExtendScalars J θ h₁ h₂).app M) N.isSheaf)).bijective

/-- Extension of scalars along `θ`, read back as a functor on sheaves of `A₁`-modules, is the
sheafified tensor product by `A₂`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars J θ h₁ h₂ ⋙
        SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, u, u, u}
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
          (SheafOfModules.unit (commRingSheaf J A₂ h₂))) :=
  (extendScalarsTensorLeftUniversal J θ h₁ h₂).uniqueIso
    (AlgebraicGeometry.SheafOfModules.tensorLeftFunctorUniversal A₁ h₁ _)

section SheafOfCommRings

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/-- Extension of scalars along a morphism `φ` of sheaves of commutative rings, read back as a
functor on sheaves of `O₁`-modules, is the sheafified tensor product by `O₂`. This is
`Stacks.Sheaves.ChangeOfRings.extendScalarsCompRestrictScalarsIso` at the spelling in which
`AlgebraicGeometry.meromorphicSectionSheaf` is defined, the two extension-of-scalars functors
agreeing on the nose. -/
noncomputable def changeOfRingsCompRestrictScalarsIso :
    changeOfRings.{u, v, u} J φ ⋙
        SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, u, u, u}
        ⟨O₁.obj, Presheaf.isSheaf_of_isSheaf_comp _ O₁.obj (forget₂ CommRingCat RingCat)
          (Stacks.Sheaves.Differentials.ringSheaf O₁).property⟩).obj
        ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf O₂))) :=
  extendScalarsCompRestrictScalarsIso J φ.hom
    (Stacks.Sheaves.Differentials.ringSheaf O₁).property (Stacks.Sheaves.Differentials.ringSheaf
      O₂).property

end SheafOfCommRings

end Stacks.Sheaves.ChangeOfRings
