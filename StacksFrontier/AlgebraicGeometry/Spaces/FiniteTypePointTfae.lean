module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteTypePointMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# The three characterizations of a finite type point of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `x` be a point of `X`. Three
conditions on `x` are equivalent: `x` is a finite type point; `x` is the image of an
algebraic space with a single point which is locally of finite type over `X`; and `x` is the
image of a field-valued point of an algebraic space `Z` carrying a surjective étale morphism
from a field spectrum, along a monomorphism `Z ⟶ X` which is locally of finite type.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypePoint_tfae` is the three-way equivalence, assembled
  from the equivalence of its first two conditions and the two implications between its first
  and third.

## Implementation notes

The three conditions are spelled exactly as the two source files spell them, so that the
equivalence is the conjunction of what they prove and nothing is restated. That `|Z|` be a
singleton is the conjunction of `Nonempty` and `Subsingleton` on its points, as in
Stacks 06QW, and the surjective étale morphism from a field spectrum of the third condition is
recorded as a field-valued point of `Z` whose morphism is surjective and étale; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PointsOfFiniteType.lean`.

The equivalence of the first two conditions is
`AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_singleton_space`, the implication from
the first to the third is
`AlgebraicGeometry.Space.exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint`,
and the implication from the third to the first is
`AlgebraicGeometry.Space.isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint`. The source
argues (1) ⟹ (3) ⟹ (2) ⟹ (1); the library proves (1) ⟺ (2) directly, which makes the
implication (3) ⟹ (2) of the source unnecessary here.

## References

* [Stacks Project, Tag 06EL](https://stacks.math.columbia.edu/tag/06EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `S` be a scheme, let `X` be an algebraic space over `S` and let `x` be a point of
`X`. The following are equivalent:

1. `x` is a finite type point;
2. there is an algebraic space `Z` whose space of points is a singleton and a morphism
   `f : Z ⟶ X` which is locally of finite type with `{x}` the image of `|f|`;
3. there is an algebraic space `Z` and a morphism `f : Z ⟶ X` such that `Z` carries a
   surjective étale morphism from the spectrum of a field, `f` is locally of finite type, `f`
   is a monomorphism, and `x` is the image under `|f|` of the point of that field spectrum.

Conditions (1) and (2) are equivalent by
`AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_singleton_space`; condition (1) implies
condition (3) by
`AlgebraicGeometry.Space.exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint`,
and condition (3) implies condition (1) by
`AlgebraicGeometry.Space.isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint`. -/
@[stacks 06EL]
theorem isFiniteTypePoint_tfae (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    [IsFiniteTypePoint B S hS X x,
      ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ X),
        Nonempty (points B S hS Z) ∧ Subsingleton (points B S hS Z) ∧
          IsLocallyOfFiniteType B S hS f ∧ Set.range (pointsMap B S hS Z f) = {x},
      ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z) (f : Z ⟶ X)
          (z : FieldValuedPoint B S hS Z),
        IsSurjective B S hS (yonedaEquiv.symm z.value) ∧
          IsEtale B S hS (yonedaEquiv.symm z.value) ∧
          IsLocallyOfFiniteType B S hS f ∧ Mono f ∧
          x = pointsMap B S hS Z f (z.class B S hS Z)].TFAE := by
  tfae_have 1 ↔ 2 := isFiniteTypePoint_iff_exists_singleton_space B S hS X hX x
  tfae_have 1 → 3 :=
    exists_mono_isLocallyOfFiniteType_etale_fieldPoint_of_isFiniteTypePoint B S hS X hX x
  tfae_have 3 → 1 := by
    rintro ⟨Z, hZ, f, z, hsurj, hetale, hflft, hmono, hx⟩
    rw [hx]
    exact isFiniteTypePoint_pointsMap_of_isSurjective_fieldPoint B S hS hX hZ f z hsurj
      hetale hflft hmono
  tfae_finish

end AlgebraicGeometry.Space

end
