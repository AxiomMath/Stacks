module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphisms
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.Terminal

/-!
# Deformations of a morphism of schemes form a deformation category

Example Stacks Tag 0E3T presents the flat families of morphisms of schemes over `𝒞_Λ` as a
category cofibered in groupoids, and defines the deformation category of a fixed morphism
`X ⟶ Y` of schemes over the residue field as the slice over that morphism, viewed as a family
over the residue-field object.

This file records the second assertion of Stacks Tag 0E3U: once the category of all flat
families of morphisms of schemes is known to satisfy the Rim-Schlessinger condition, the
deformation category of a fixed morphism of schemes over the residue field is a deformation
category, that is, a predeformation category satisfying (RS).

## Main definitions

* `Deformation.Examples.schemeMorphismDeformationCategoryProjection`: the structure functor
  of the deformation category of a morphism of schemes over the residue field.

## Main results

* `Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategory`: the
  deformation category of a morphism of schemes over the residue field is a deformation
  category, given the Rim-Schlessinger condition for the ambient category of flat families.

## Implementation notes

The (RS) condition for the ambient category of flat families of morphisms of schemes — the
first assertion of Stacks Tag 0E3U — is carried here as an explicit hypothesis rather than
proved. Its proof rests on the identification of the category of schemes flat over a fibre
product of Artinian local algebras with the fibre product of the categories of schemes flat
over the two factors, which is the flat clause of Stacks Tag 07RX and is not available in this
library.

Granting that hypothesis, the passage to the slice is the localization argument of Stacks Tag
06JC. It is applied in the form whose hypothesis on the chosen object is that its base is
terminal rather than that its base is literally `Deformation.residueFieldObject`: the base of
the special fibre of a morphism of schemes over the residue field is
`Deformation.Examples.residueFieldBase`, whose carrier is `k` itself and not the universe lift
`ULift k` appearing in `Deformation.residueFieldObject`. Those two objects of `𝒞_Λ` are
isomorphic but not equal, and the fibre of a functor is indexed by equality of objects.

## References

* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0E3U](https://stacks.math.columbia.edu/tag/0E3U)
* [Stacks Project, Tag 06JC](https://stacks.math.columbia.edu/tag/06JC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The structure functor of the deformation category of a morphism of schemes over the
residue field: forget the arrow to the special fibre, then take the base of the family. -/
def schemeMorphismDeformationCategoryProjection {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) :
    schemeMorphismDeformationCategory f pX pY hf ⥤ ArtinianLocalAlgCat.{u, v, v} Λ k :=
  objectsOverFunctor (schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k))
    (schemeMorphismFamilySpecialFiber f pX pY hf)

@[simp]
theorem schemeMorphismDeformationCategoryProjection_obj {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) (P : schemeMorphismDeformationCategory f pX pY hf) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).obj P = P.left.base := rfl

@[simp]
theorem schemeMorphismDeformationCategoryProjection_map {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) {P Q : schemeMorphismDeformationCategory f pX pY hf} (g : P ⟶ Q) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).map g = g.left.base := rfl

/-- The second assertion of Stacks Tag 0E3U. Granting the Rim-Schlessinger condition for the
category of all flat families of morphisms of schemes over `𝒞_Λ`, the deformation category of
a fixed morphism `X ⟶ Y` of schemes over the residue field is a deformation category: a
predeformation category satisfying (RS). -/
@[stacks 0E3U "the in-particular assertion only: granting (RS) for Example 0E3T as the \
hypothesis hRS, the deformation category Def_{X ⟶ Y} of a morphism of schemes X ⟶ Y over k \
is a deformation category. (RS) for Example 0E3T itself is NOT proved here"]
theorem isDeformationCategory_schemeMorphismDeformationCategory
    (hRS : SatisfiesRS (schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k)))
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) :
    IsDeformationCategory (schemeMorphismDeformationCategoryProjection f pX pY hf) := by
  let p := schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k)
  let x := schemeMorphismFamilySpecialFiber (Λ := Λ) (k := k) f pX pY hf
  let S := residueFieldObject.{u, v, v} Λ k
  have ht : IsTerminal (p.obj x) := isTerminal_residueFieldBase
  have hs : IsTerminal S :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot S
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{v} k))
  refine ⟨⟨isCofiberedInGroupoids_overForget hRS.1 x ht, ?_⟩, ?_⟩
  · exact objectsOverFunctor_fiber_equiv_punit_of_isTerminal p hRS.1 x ht S hs
  · exact satisfiesRS_objectsOverFunctor_of_isTerminal p hRS x ht

end Deformation.Examples

end
