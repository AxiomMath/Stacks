module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLinePolynomial
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of a morphism over an integral base

Let `Y` be an integral scheme with function field `R(Y)`, which is the stalk of `Y` at its
generic point. The generic fibre of a morphism `f : X ⟶ Y` is the base change of `f` along the
canonical morphism `Spec R(Y) ⟶ Y`; it is a scheme over the field `R(Y)`, and every point of `X`
lying over the generic point of `Y` comes from it.

The case this file is built for is `X = 𝔸¹_Y`: the generic fibre of the affine line over `Y` is
the affine line over `R(Y)`, i.e. `Spec R(Y)[T]`. This is the fourth step of the proof of Stacks
02TT, where a prime cycle on `Y × 𝔸¹` dominating `Y` is cut out, on the generic fibre, by a
monic irreducible polynomial over `R(Y)`.

## Main definitions

* `Stacks.Chow.fromSpecFunctionField` — the canonical morphism `Spec R(Y) ⟶ Y`.
* `Stacks.Chow.genericFibre` — the fibre of `f : X ⟶ Y` over the generic point of `Y`, as the
  base change of `f` along `Spec R(Y) ⟶ Y`.
* `Stacks.Chow.genericFibreAffineLineIso` — the generic fibre of the affine line over `Y` is
  `Spec R(Y)[T]`.

## Main results

* `Stacks.Chow.exists_genericFibreι_eq` — a point of `X` lying over the generic point of `Y` is
  the image of a point of the generic fibre.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The spectrum of the function field -/

/-- The canonical morphism `Spec R(Y) ⟶ Y` from the spectrum of the function field of an
irreducible scheme: the morphism from the spectrum of the stalk at the generic point. -/
@[ega "I 2.4.2" "special case"]
def fromSpecFunctionField (Y : Scheme.{u}) [IrreducibleSpace Y] :
    Spec Y.functionField ⟶ Y :=
  Y.fromSpecStalk (genericPoint ↥Y)

/-- The image of `Spec R(Y) ⟶ Y` is the set of points whose closure contains the generic
point. -/
theorem range_fromSpecFunctionField (Y : Scheme.{u}) [IrreducibleSpace Y] :
    Set.range (fromSpecFunctionField Y) = {y | y ⤳ genericPoint ↥Y} :=
  Scheme.range_fromSpecStalk

/-- The generic point of `Y` is in the image of `Spec R(Y) ⟶ Y`. -/
theorem exists_fromSpecFunctionField_eq_genericPoint (Y : Scheme.{u}) [IrreducibleSpace Y] :
    ∃ ξ : ↥(Spec Y.functionField), fromSpecFunctionField Y ξ = genericPoint ↥Y := by
  have h : genericPoint ↥Y ∈ Set.range (fromSpecFunctionField Y) := by
    rw [range_fromSpecFunctionField]
    exact specializes_refl (genericPoint ↥Y)
  exact h

/-! ### The generic fibre -/

/-- **The generic fibre of a morphism over an irreducible base**: the base change of `f` along
`Spec R(Y) ⟶ Y`, i.e. the fibre of `f` over the generic point of `Y`. -/
abbrev genericFibre {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y) : Scheme.{u} :=
  pullback f (fromSpecFunctionField Y)

/-- The canonical morphism from the generic fibre of `f : X ⟶ Y` to `X`. -/
abbrev genericFibreι {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y) :
    genericFibre f ⟶ X :=
  pullback.fst f (fromSpecFunctionField Y)

/-- The generic fibre of `f : X ⟶ Y` is a scheme over the function field of `Y`. -/
abbrev genericFibreOver {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y) :
    genericFibre f ⟶ Spec Y.functionField :=
  pullback.snd f (fromSpecFunctionField Y)

/-- The generic fibre is a fibre: its two structure morphisms agree over `Y`. -/
theorem genericFibreι_comp {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y) :
    genericFibreι f ≫ f = genericFibreOver f ≫ fromSpecFunctionField Y :=
  pullback.condition

/-- **A point lying over the generic point of the base comes from the generic fibre.** -/
theorem exists_genericFibreι_eq {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y) (x : ↥X)
    (hx : f x = genericPoint ↥Y) :
    ∃ z : ↥(genericFibre f), genericFibreι f z = x := by
  obtain ⟨ξ, hξ⟩ := exists_fromSpecFunctionField_eq_genericPoint Y
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x ξ (by rw [hx, hξ])
  exact ⟨z, hz⟩

/-! ### The generic fibre of the affine line -/

/-- **The generic fibre of the affine line over an integral base is the affine line over the
function field.** Affine space is stable under base change, so the generic fibre of
`𝔸¹_Y ⟶ Y` is `𝔸¹_{Spec R(Y)}`, which is `Spec R(Y)[T]`. -/
def genericFibreAffineLineIso (Y : Scheme.{u}) [IsIntegral Y] :
    Spec (CommRingCat.of (Polynomial ↑Y.functionField)) ≅
      genericFibre (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) :=
  (affineLineSpecIsoSpecPolynomial Y.functionField).symm ≪≫
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (fromSpecFunctionField Y)).isoPullback

/-- **The affine line over the function field, as the generic fibre of the affine line over
`Y`.** This is the morphism `𝔸¹_{R(Y)} ⟶ 𝔸¹_Y` whose image is the fibre over the generic point
of `Y`. -/
def affineLineGenericFibreι (Y : Scheme.{u}) [IsIntegral Y] :
    Spec (CommRingCat.of (Polynomial ↑Y.functionField)) ⟶ 𝔸(ULift.{u} (Fin 1); Y) :=
  (genericFibreAffineLineIso Y).hom ≫ genericFibreι (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

/-- `Stacks.Chow.affineLineGenericFibreι` is the base change of `Spec R(Y) ⟶ Y` to affine
lines. -/
theorem affineLineGenericFibreι_eq (Y : Scheme.{u}) [IsIntegral Y] :
    affineLineGenericFibreι Y = (affineLineSpecIsoSpecPolynomial Y.functionField).inv ≫
      AffineSpace.map (ULift.{u} (Fin 1)) (fromSpecFunctionField Y) := by
  rw [affineLineGenericFibreι, genericFibreAffineLineIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, (AffineSpace.isPullback_map
      (n := ULift.{u} (Fin 1)) (fromSpecFunctionField Y)).isoPullback_hom_fst]

/-- The generic fibre of the affine line sits over `Spec R(Y) ⟶ Y`: the inclusion
`𝔸¹_{R(Y)} ⟶ 𝔸¹_Y` carries the structure morphism of `𝔸¹_Y` to the structure morphism of
`Spec R(Y)[T]` followed by `Spec R(Y) ⟶ Y`. -/
theorem affineLineGenericFibreι_over (Y : Scheme.{u}) [IsIntegral Y] :
    affineLineGenericFibreι Y ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) =
      Spec.map (CommRingCat.ofHom
          (Polynomial.C : ↑Y.functionField →+* Polynomial ↑Y.functionField)) ≫
        fromSpecFunctionField Y := by
  rw [affineLineGenericFibreι_eq, Category.assoc, AffineSpace.map_over, ← Category.assoc,
    affineLineSpecIsoSpecPolynomial_inv_over]

/-- Applying `Stacks.Chow.affineLineGenericFibreι` to a point of `Spec R(Y)[T]` read through
`Stacks.Chow.genericFibreAffineLineIso` is the inclusion of the generic fibre. -/
theorem affineLineGenericFibreι_genericFibreAffineLineIso_inv (Y : Scheme.{u}) [IsIntegral Y]
    (z : ↥(genericFibre (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))) :
    affineLineGenericFibreι Y ((genericFibreAffineLineIso Y).inv z) =
      genericFibreι (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) z := by
  have h : (genericFibreAffineLineIso Y).inv ≫ affineLineGenericFibreι Y =
      genericFibreι (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) := by
    rw [affineLineGenericFibreι, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h' := congrArg (fun φ : genericFibre (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⟶
      𝔸(ULift.{u} (Fin 1); Y) => φ z) h
  simpa using h'

end Stacks.Chow

end
