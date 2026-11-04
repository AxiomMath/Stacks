module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Extension of scalars of a short exact sequence with flat quotient

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`.  Extension
of scalars along `α` is the sheafification of the sectionwise tensor product
`U ↦ O₂(U) ⊗_{O₁(U)} G(U)`.  This file proves that it carries a short exact sequence of sheaves
of `O₁`-modules whose third term is flat to a short exact sequence of sheaves of `O₂`-modules.

This is the tensor-exactness statement of Stacks 03EX, read at the particular tensor factor
`O₂`.  The two identifications it needs are recorded separately: the underlying abelian sheaf
of the extension of scalars *is* the tensor product with `O₂` placed on the left
(`changeOfRings_comp_toSheaf`, which holds by `rfl`), and tensoring with a fixed sheaf of
modules on the left is tensoring with it on the right, by the braiding of the tensor product
(`shortExact_map_sheafTensorObj`).

## Main results

* `Stacks.Sheaves.ChangeOfRings.changeOfRings_comp_toSheaf`: extension of scalars along `α`,
  read on underlying abelian sheaves, is the tensor product with `O₂` on the left.  Both sides
  sheafify the presheaf `U ↦ O₂(U) ⊗_{O₁(U)} G(U)`, with the tensor factors in the same order,
  so no comparison of tensor products intervenes.
* `Stacks.Sheaves.ChangeOfRings.shortExact_map_sheafTensorObj`: Stacks 03EX with the fixed
  tensor factor on the **left**.
* `Stacks.Sheaves.ChangeOfRings.shortExact_map_changeOfRings`: **Stacks 03EX for extension of
  scalars.**

## Implementation notes

No tag is placed here.  Stacks 03EX is registered where it is proved, on
`Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃`; the statements below
are that assertion read at another tensor factor and in another spelling of the functor, not
new assertions of the source.

Two spellings of the underlying sheaf of rings of a sheaf of commutative rings are in play:
`Stacks.SheafOfModules.Tensor.ringSheaf`, which supplies the composition of the sheaf condition
with `forget₂ CommRingCat RingCat` from `Stacks.hasSheafCompose_forget₂_commRingCat`, and
`Stacks.Sheaves.Differentials.ringSheaf`, which takes it as an instance binder.  Making
`Stacks.hasSheafCompose_forget₂_commRingCat` the ambient instance, rather than adding the
binder, makes the two spellings the same term and is what lets
`changeOfRings_comp_toSheaf` be `rfl`.

The module universe equals the universe of the ring sections.  That is forced twice over: the
tensor factor is `SheafOfModules.unit` of the structure sheaf, whose carrier is the sections of
that sheaf, and the flat-cover argument behind Stacks 03EX needs free modules on sets of
sections.  The two site universes stay independent of it and of each other.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sheaves.ChangeOfRings

open Stacks.SheafOfModules.Tensor (sheafTensor sheafTensorBraiding)

-- The sections universe is independent of the site universes, so Mathlib's size-restricted
-- instances do not supply this; fixing the spelling here keeps `changeOfRings` and
-- `Stacks.SheafOfModules.Tensor.ringSheaf` literally the same sheaf of rings.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Stacks 03EX with the fixed tensor factor on the left -/

section Tensor

variable (O : Sheaf J CommRingCat.{u})
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O))

/-- Tensoring on the left with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
instance preservesZeroMorphisms_sheafTensorObj :
    ((sheafTensor.{u, v, u, u, u} O).obj G).PreservesZeroMorphisms := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj O G
  infer_instance

/-- Tensoring on the right with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
instance preservesZeroMorphisms_sheafTensorFlipObj :
    ((sheafTensor.{u, v, u, u, u} O).flip.obj G).PreservesZeroMorphisms := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj O G
  infer_instance

/-- Tensoring on the left with a fixed sheaf of modules is additive: it is right exact, hence
preserves binary biproducts. -/
instance additive_sheafTensorObj : ((sheafTensor.{u, v, u, u, u} O).obj G).Additive := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj O G
  have : PreservesBinaryBiproducts ((sheafTensor.{u, v, u, u, u} O).obj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **Stacks Project, Tag 03EX, with the fixed tensor factor on the left.**  If the final term
of a short exact sequence of sheaves of modules is flat, tensoring the sequence on the right by
it — that is, placing the fixed sheaf of modules `G` on the left — gives a short exact
sequence.

This is `Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, which tensors with
`G` on the right, carried across the braiding
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the tensor product. -/
theorem shortExact_map_sheafTensorObj
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, u, u} (O := O) S.X₃) :
    (S.map ((sheafTensor.{u, v, u, u, u} O).obj G)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso ((sheafTensorBraiding.{u, v, u} O).app G))).2
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj O S hS hflat G)

end Tensor

/-! ### Stacks 03EX for extension of scalars -/

section Extension

variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (α : O₁ ⟶ O₂)

/-- `O₂`, read as a sheaf of `O₁`-modules by restriction of scalars along `α`.  This is the
tensor factor through which extension of scalars along `α` is computed. -/
abbrev restrictUnit : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁) :=
  (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂))

/-- **Extension of scalars is the tensor product with `O₂` on the left**, on underlying abelian
sheaves, on the nose.  Both sides sheafify the presheaf `U ↦ O₂(U) ⊗_{O₁(U)} G(U)`, and the
tensor factors are in the same order on the two sides, so this is `rfl`. -/
theorem changeOfRings_comp_toSheaf :
    changeOfRings.{u, v, u} J α ⋙
        SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂) =
      (sheafTensor.{u, v, u, u, u} O₁).obj (restrictUnit α) ⋙
        SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁) :=
  rfl

/-- Extension of scalars is additive.  Its composite with the underlying-abelian-sheaf functor
is the tensor product with `O₂`, which is additive, and that functor is faithful. -/
instance changeOfRings_additive : @Functor.Additive
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁))
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂))
    inferInstance inferInstance inferInstance inferInstance (changeOfRings.{u, v, u} J α) := by
  have tensorAdditive : ((sheafTensor.{u, v, u, u, u} O₁).obj (restrictUnit α) ⋙
      SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁)).Additive := by
    infer_instance
  have compositeAdditive : (changeOfRings.{u, v, u} J α ⋙
      SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂)).Additive :=
    (changeOfRings_comp_toSheaf α).symm ▸ tensorAdditive
  exact @Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _
    (changeOfRings.{u, v, u} J α)
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂))
    (show (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂) :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂) ⥤
        Sheaf J AddCommGrpCat.{u}).Additive
      from inferInstance) compositeAdditive
    (show (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂) :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂) ⥤
        Sheaf J AddCommGrpCat.{u}).Faithful
      from inferInstance)

/-- **Stacks Project, Tag 03EX for extension of scalars.**  Extension of scalars along
`α : O₁ ⟶ O₂` carries a short exact sequence of sheaves of `O₁`-modules whose third term is
flat to a short exact sequence of sheaves of `O₂`-modules.

Short exactness is read on underlying abelian sheaves, where `changeOfRings_comp_toSheaf` turns
the statement into Stacks 03EX for the tensor product (`shortExact_map_sheafTensorObj`);
`SheafOfModules.toSheaf` is exact and faithful, so it both carries and reflects short
exactness. -/
theorem shortExact_map_changeOfRings
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, u, u} (O := O₁) S.X₃) :
    (@ShortComplex.map
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁))
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂))
      inferInstance inferInstance inferInstance inferInstance S (changeOfRings.{u, v, u} J α)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (changeOfRings.{u, v, u} J α) (changeOfRings_additive α))).ShortExact := by
  let compositeZero : (changeOfRings.{u, v, u} J α ⋙
      SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂)).PreservesZeroMorphisms :=
    (changeOfRings_comp_toSheaf α).symm ▸
      (show ((sheafTensor.{u, v, u, u, u} O₁).obj (restrictUnit α) ⋙
        SheafOfModules.toSheaf.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁)).PreservesZeroMorphisms
        from inferInstance)
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₂)) ?_
  refine ShortComplex.shortExact_of_iso
    (@ShortComplex.mapNatIso _ _ _ _ _ _ S _ _ inferInstance compositeZero
      (eqToIso (changeOfRings_comp_toSheaf α)).symm) ?_
  exact (shortExact_map_sheafTensorObj O₁ (restrictUnit α) S hS hflat).map_of_exact
    (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, u} O₁))

end Extension

end Stacks.Sheaves.ChangeOfRings

end
