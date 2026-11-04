module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings

/-!
# Extension of scalars of a short exact sequence with flat quotient, at free universes

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact` proves that extension of
scalars along `α` carries a short exact sequence of sheaves of `O₁`-modules whose third term is
flat to a short exact sequence of sheaves of `O₂`-modules, for
`Stacks.Sheaves.ChangeOfRings.changeOfRings`.  That functor is declared with the sections of
`O₁` and `O₂` in the universe of the **objects** of the site and the modules at the `max` of the
object and morphism universes, so the statement has no instance at a ringed topos whose
structure sheaf takes its sections below the objects of its site — the small étale ringed topos
of an algebraic space, `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, being the standing
example.

This file proves the same thing for `Stacks.FlatChangeOfRings.extendScalars`, the extension of
scalars of Stacks 03CZ declared with the three universes of the ringed site independent.  The
two functors are the same composite — forget to presheaves, sectionwise tensor product,
sheafify — and the pullback of sheaves of modules along a morphism of ringed topoi is built on
this one (`Stacks.Sheaves.RingedToposModules.extendScalarsFSharp_eq_changeOfRings`), so this is
the form Stacks 0G6R consumes.

## Main results

* `Stacks.FlatChangeOfRings.extendScalars_comp_toSheaf`: extension of scalars along `α`, read on
  underlying abelian sheaves, is the tensor product with `O₂` on the left.  As for
  `Stacks.Sheaves.ChangeOfRings.changeOfRings_comp_toSheaf`, both sides sheafify the presheaf
  `U ↦ O₂(U) ⊗_{O₁(U)} G(U)` with the factors in the same order, so this is `rfl`.
* `Stacks.FlatChangeOfRings.extendScalars_additive`: extension of scalars is additive.
* `Stacks.FlatChangeOfRings.shortExact_map_extendScalars`: **Stacks 03EX for extension of
  scalars**, at free universes.

## Implementation notes

The proofs are those of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact`; only the spelling of the
extension-of-scalars functor differs, and with it the universes.  The inputs they rest on are
already stated at independent universes: Stacks 03EX for the tensor bifunctor is
`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, the braiding of the tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`, and the right exactness of
tensoring in either variable is `Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj`.

`Stacks.hasSheafCompose_forget₂_commRingCat` is made an ambient local instance, as it is in
`ChangeOfRingsShortExact`: that is what makes `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.commRingSheafToRingSheaf` the same term, and hence `extendScalars_comp_toSheaf` an
`rfl`.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.FlatChangeOfRings

open Stacks.SheafOfModules.Tensor (sheafTensor sheafTensorBraiding)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ### Stacks 03EX with the fixed tensor factor on the left, at free universes -/

section Tensor

variable (O : Sheaf J CommRingCat.{w})
  (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- Tensoring on the left with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
instance preservesZeroMorphisms_sheafTensorObj' :
    ((sheafTensor.{u, v, w, w, w} O).obj G).PreservesZeroMorphisms := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj O G
  infer_instance

/-- Tensoring on the right with a fixed sheaf of modules preserves zero morphisms, being right
exact. -/
instance preservesZeroMorphisms_sheafTensorFlipObj' :
    ((sheafTensor.{u, v, w, w, w} O).flip.obj G).PreservesZeroMorphisms := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj O G
  infer_instance

/-- Tensoring on the left with a fixed sheaf of modules is additive: it is right exact, hence
preserves binary biproducts. -/
instance additive_sheafTensorObj' : ((sheafTensor.{u, v, w, w, w} O).obj G).Additive := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj O G
  have : PreservesBinaryBiproducts ((sheafTensor.{u, v, w, w, w} O).obj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **Stacks Project, Tag 03EX, with the fixed tensor factor on the left**, at a section
universe independent of the two universes of the site.  If the final term of a short exact
sequence of sheaves of modules is flat, placing the fixed sheaf of modules `G` on the left gives
a short exact sequence.

This is `Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, which tensors with
`G` on the right, carried across the braiding
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`. -/
theorem shortExact_map_sheafTensorObj'
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) S.X₃) :
    (S.map ((sheafTensor.{u, v, w, w, w} O).obj G)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso ((sheafTensorBraiding O).app G))).2
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj O S hS hflat G)

end Tensor

/-! ### Stacks 03EX for extension of scalars, at free universes -/

section Extension

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)

/-- `O₂`, read as a sheaf of `O₁`-modules by restriction of scalars along `α`.  This is the
tensor factor through which extension of scalars along `α` is computed. -/
abbrev restrictUnit' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) :=
  (SheafOfModules.restrictScalars (ringSheafMap α)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- **Extension of scalars is the tensor product with `O₂` on the left**, on underlying abelian
sheaves, on the nose.  Both sides sheafify the presheaf `U ↦ O₂(U) ⊗_{O₁(U)} G(U)`, and the
tensor factors are in the same order on the two sides, so this is `rfl`. -/
theorem extendScalars_comp_toSheaf :
    extendScalars α ⋙ SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) =
      (sheafTensor.{u, v, w, w, w} O₁).obj (restrictUnit' α) ⋙
        SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) :=
  rfl

/-- Extension of scalars is additive.  Its composite with the underlying-abelian-sheaf functor
is the tensor product with `O₂`, which is additive, and that functor is faithful. -/
instance extendScalars_additive : @Functor.Additive
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    inferInstance inferInstance inferInstance inferInstance (extendScalars α) := by
  have tensorAdditive : ((sheafTensor.{u, v, w, w, w} O₁).obj (restrictUnit' α) ⋙
      SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)).Additive := by
    infer_instance
  have compositeAdditive : (extendScalars α ⋙
      SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).Additive :=
    (extendScalars_comp_toSheaf α).symm ▸ tensorAdditive
  exact @Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _
    (extendScalars α) (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (show (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⥤
        Sheaf J AddCommGrpCat.{w}).Additive
      from inferInstance) compositeAdditive
    (show (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⥤
        Sheaf J AddCommGrpCat.{w}).Faithful
      from inferInstance)

/-- **Stacks Project, Tag 03EX for extension of scalars**, at a section universe independent of
the two universes of the site.  Extension of scalars along `α : O₁ ⟶ O₂` carries a short exact
sequence of sheaves of `O₁`-modules whose third term is flat to a short exact sequence of
sheaves of `O₂`-modules.

Short exactness is read on underlying abelian sheaves, where `extendScalars_comp_toSheaf` turns
the statement into Stacks 03EX for the tensor product (`shortExact_map_sheafTensorObj'`);
`SheafOfModules.toSheaf` is exact and faithful, so it both carries and reflects short
exactness. -/
theorem shortExact_map_extendScalars
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O₁) S.X₃) :
    (@ShortComplex.map
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
      inferInstance inferInstance inferInstance inferInstance S (extendScalars α)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (extendScalars α) (extendScalars_additive α))).ShortExact := by
  have : (extendScalars α ⋙
      SheafOfModules.toSheaf.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).Additive := by
    have := extendScalars_additive α
    infer_instance
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) ?_
  refine ShortComplex.shortExact_of_iso
    (@ShortComplex.mapNatIso _ _ _ _ _ _ S _ _ inferInstance inferInstance
      (eqToIso (extendScalars_comp_toSheaf α)).symm) ?_
  exact (shortExact_map_sheafTensorObj' O₁ (restrictUnit' α) S hS hflat).map_of_exact
    (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))

end Extension

end Stacks.FlatChangeOfRings

end
