module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.RingTheory.Sequence.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular sequences in the étale local rings of a flat morphism of algebraic spaces

Let `f : F ⟶ G` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `F` at whose image `f` is flat.  A sequence of elements of the étale local ring
`𝒪_{G, f ∘ x}` is regular exactly when its image in `𝒪_{F, x}` is.

## Main results

* `AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_iff`: a sequence in the étale local
  ring of the target is regular exactly when its image under a flat comparison homomorphism of
  étale local rings is regular.
* `AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_iff_of_isFlatAt`: the same, with
  flatness of the comparison homomorphism supplied by flatness of `f` at the image of `x`.
* `AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt`: a sequence of
  germs pulled back from a common target is regular in `𝒪_{F', z}` exactly when it is regular in
  `𝒪_{F, π ∘ z}`, for `π : F' ⟶ F` flat at the image of `z`.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A sequence in a local ring is regular exactly when its image in a local ring that is flat
and local over it is regular. -/
@[ega "0 15.1.14" "special case"]
private theorem isRegular_map_algebraMap_iff_of_flat_of_isLocalHom (R T : Type*) [CommRing R]
    [CommRing T] [IsLocalRing R] [IsLocalRing T] [Algebra R T] [Module.Flat R T]
    [IsLocalHom (algebraMap R T)] (rs : List R) :
    RingTheory.Sequence.IsRegular T (rs.map (algebraMap R T)) ↔
      RingTheory.Sequence.IsRegular R rs :=
  have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  RingTheory.Sequence.isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    (IsBaseChange.linearMap R T) rs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If the canonical homomorphism `𝒪_{G, f ∘ x} ⟶ 𝒪_{F, x}` of étale local rings induced by a
morphism `f : F ⟶ G` of algebraic spaces at a geometric point `x` of `F` is flat, then a sequence
in `𝒪_{G, f ∘ x}` is regular exactly when its image in `𝒪_{F, x}` is. -/
theorem isRegular_map_etaleLocalRingMap_iff (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : GeometricPoint B S hS F)
    (hf : (etaleLocalRingMap hF f x).Flat)
    (rs : List (etaleLocalRing B S hS G (geometricPointMap f x))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F x)
        (rs.map (etaleLocalRingMap hF f x)) ↔
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS G (geometricPointMap f x)) rs := by
  let A := etaleLocalRing B S hS G (geometricPointMap f x)
  let M := etaleLocalRing B S hS F x
  let _ : Algebra A M := (etaleLocalRingMap hF f x).toAlgebra
  have : IsLocalRing A := isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f x)
  have : IsLocalRing M := isLocalRing_etaleLocalRing B S hS F hF x
  have : Module.Flat A M := hf
  have : IsLocalHom (algebraMap A M) := isLocalHom_etaleLocalRingMap B S hS hF hG f x
  exact isRegular_map_algebraMap_iff_of_flat_of_isLocalHom A M rs

/-- Let `f : F ⟶ G` be a morphism of algebraic spaces that is flat at the image of a geometric
point `x` of `F`. Then a sequence in `𝒪_{G, f ∘ x}` is regular exactly when its image in
`𝒪_{F, x}` is. -/
theorem isRegular_map_etaleLocalRingMap_iff_of_isFlatAt (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : GeometricPoint B S hS F)
    (hf : IsFlatAt B S hS f x.image)
    (rs : List (etaleLocalRing B S hS G (geometricPointMap f x))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F x)
        (rs.map (etaleLocalRingMap hF f x)) ↔
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS G (geometricPointMap f x)) rs :=
  isRegular_map_etaleLocalRingMap_iff B S hS hF hG f x
    ((isFlatAt_iff_etaleLocalRingMap_flat hF hG f x).mp hf) rs

/-- Let `π : F' ⟶ F` and `p : F ⟶ H` be morphisms of algebraic spaces over `S`, let
`z` be a geometric point of `F'` at whose image `π` is flat, and let `rs` be a sequence in the
étale local ring of `H` at the image of `z`.  Then the image of `rs` in `𝒪_{F', z}` is regular
exactly when its image in `𝒪_{F, π ∘ z}` is. -/
theorem isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt
    {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF' : IsAlgebraicSpace B S hS F') (hF : IsAlgebraicSpace B S hS F)
    (π : F' ⟶ F) (p : F ⟶ H)
    (z : GeometricPoint B S hS F') (hπ : IsFlatAt B S hS π z.image)
    (rs : List (etaleLocalRing B S hS H (geometricPointMap p (geometricPointMap π z)))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F' z)
        (rs.map (etaleLocalRingMap hF' (π ≫ p) z)) ↔
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F (geometricPointMap π z))
        (rs.map (etaleLocalRingMap hF p (geometricPointMap π z))) := by
  rw [← isRegular_map_etaleLocalRingMap_iff_of_isFlatAt B S hS hF' hF π z hπ
    (rs.map (etaleLocalRingMap hF p (geometricPointMap π z))), List.map_map,
    ← RingHom.coe_comp, etaleLocalRingMap_comp hF' hF π p z]
  exact Iff.rfl

end AlgebraicGeometry.Space

end
