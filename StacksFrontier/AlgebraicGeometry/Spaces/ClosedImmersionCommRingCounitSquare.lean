module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage

/-!
# The ring data of the closed-immersion transport of derivations

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces and `b : X ⟶ B` a structure morphism.
Transporting derivations of `i_*𝒪_Z` on the small étale site of `X` to derivations of `𝒪_Z` on
the site of `Z` goes through the inverse image, and the generic transport
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` asks for a commutative square of
the ring data.  This file supplies that square: the inverse image along `i` of the base map of
`i_*𝒪_Z`, followed by the commutative-ring counit `i⁻¹i_*𝒪_Z ⟶ 𝒪_Z`, is the comparison of the
iterated inverse image followed by the structure map of `i ≫ b`.

## Main results

* `AlgebraicGeometry.Space.inverseImageCommRingCounit_fSharpInverseImage`: the inverse image
  along `i` of the direct-image form of the structure map of `i`, followed by the counit, is the
  inverse-image form.  This is the hom-set bijection of the commutative-ring image adjunction,
  named.
* `AlgebraicGeometry.Space.inverseImageStructureSharpCounit_square`: the square itself.

## Implementation notes

The square is two known facts composed.  The counit half is
`CategoryTheory.Adjunction.homEquiv_counit` for
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, which says that the inverse-image form
of the structure map is the inverse image of the direct-image form followed by the counit — the
same step that `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget` takes before
forgetting to sheaves of sets, taken here *before* that forgetting, because the derivation API
lives over `CommRingCat`.  The base half is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`, the
composition law of Stacks 03G8 in inverse-image form, which carries no hypothesis on either
morphism.

The closed-immersion hypothesis enters only through
`AlgebraicGeometry.Space.commRingCounitIso`, i.e. only to know that the counit is invertible;
the equation below would hold for the counit of any morphism of algebraic spaces, but
`derivationEquivOfRingDataIso` needs it as an isomorphism, so it is stated at the isomorphism.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the composition law.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), invertibility
  of the counit.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X Bb : AlgebraicSpaces B S hS}

/-- **The inverse-image form of the structure map of `i` is the inverse image of the
direct-image form followed by the counit**, as homomorphisms of sheaves of *commutative* rings.
This is `CategoryTheory.Adjunction.homEquiv_counit` for
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`. -/
theorem inverseImageCommRingCounit_fSharpInverseImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (smallEtaleInverseImageRing B S hS i).map (structureSharpCommRing B S hS i) ≫
        (commRingCounitIso B S hS i hi (smallEtaleRingedTopos B S hS Z).O).hom =
      (smallEtaleRingedToposHom B S hS i).fSharpInverseImage :=
  ((commRingImageAdjunction (smallToposMorphismTypeU B S hS i)).homEquiv_counit
    (smallEtaleRingedTopos B S hS X).O (smallEtaleRingedTopos B S hS Z).O
    (structureSharpCommRing B S hS i)).symm

/-- **The ring data of the closed-immersion transport of derivations is a commutative square.**
The inverse image along `i` of the base map `b⁻¹𝒪_B ⟶ i_*𝒪_Z` of `i_*𝒪_Z`, followed by the
commutative-ring counit `i⁻¹i_*𝒪_Z ⟶ 𝒪_Z`, is the comparison
`i⁻¹b⁻¹𝒪_B ≅ (i ≫ b)⁻¹𝒪_B` followed by the structure map `(i ≫ b)♯`.

This is the hypothesis `AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` takes, at
`α := AlgebraicGeometry.Space.inverseImageStructureSheafCompIso` and
`β := AlgebraicGeometry.Space.commRingCounitIso`. -/
theorem inverseImageStructureSharpCounit_square (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb) :
    (smallEtaleInverseImageRing B S hS i).map
          ((smallEtaleRingedToposHom B S hS b).fSharpInverseImage ≫
            structureSharpCommRing B S hS i) ≫
        (commRingCounitIso B S hS i hi (smallEtaleRingedTopos B S hS Z).O).hom =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).hom.app
          (smallEtaleRingedTopos B S hS Bb).O ≫
        (smallEtaleRingedToposHom B S hS (i ≫ b)).fSharpInverseImage :=
  (congrArg (fun m ↦ m ≫ (commRingCounitIso B S hS i hi
        (smallEtaleRingedTopos B S hS Z).O).hom)
      ((smallEtaleInverseImageRing B S hS i).map_comp
        (smallEtaleRingedToposHom B S hS b).fSharpInverseImage
        (structureSharpCommRing B S hS i))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ (smallEtaleInverseImageRing B S hS i).map
              (smallEtaleRingedToposHom B S hS b).fSharpInverseImage ≫ m)
          (inverseImageCommRingCounit_fSharpInverseImage B S hS i hi)).trans
        (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS i b).symm))

end AlgebraicGeometry.Space

end
