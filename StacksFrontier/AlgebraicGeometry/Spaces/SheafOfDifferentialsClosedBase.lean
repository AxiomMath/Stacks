module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization

/-!
# Differentials over a closed subspace of the base

Let `q : Y ⟶ Z` be a morphism of algebraic spaces and `i : Z ⟶ Z'` a closed immersion.  Then
`Ω_{Y/Z'} = Ω_{Y/Z}`: a `Z'`-derivation of `𝒪_Y` is the same thing as a `Z`-derivation.  This is
the identification `Ω_{Y/Z'} ≅ Ω_{Y/Z}` used in [Stacks Project, Tag 0CK7], where the base of the
section is a thickening `Z ⊂ Z'` and the target is `Y = Z ×_{Z'} Y'`.

One direction is formal: a `Z`-derivation kills the image of `(q ≫ i)^♯`, because that structure
map factors through `q^♯`
(`AlgebraicGeometry.Space.structureSharpSet_comp_universalDerivationHom`). For the other, read the
vanishing of a `Z'`-derivation `D` on the image of `q^♯` in direct-image form: it is the equality
`q^♯ ≫ q_*D = q^♯ ≫ q_*0` of morphisms `𝒪_Z ⟶ q_*Ω`. After `i_*` and precomposition with
`i^♯ : 𝒪_{Z'} ⟶ i_*𝒪_Z` it becomes the vanishing of `D` on the image of `(q ≫ i)^♯`
(`AlgebraicGeometry.Space.structureSharpSet_comp_map`). For a closed immersion `i^♯` is an
epimorphism (the surjectivity clause of Stacks 03MB,
`AlgebraicGeometry.Space.epi_structureSharpSet`) and `i_*` is faithful (Stacks 04E5, part (1)), so
the equality holds before them.

## Main definitions

* `AlgebraicGeometry.Space.sheafOfDifferentialsCompClosedImmersionIso`: `Ω_{Y/Z'} ≅ Ω_{Y/Z}`.

## Main results

* `AlgebraicGeometry.Space.sheafOfDifferentialsCompClosedImmersionIso_hom_d`: it carries
  `d_{Y/Z'}(t)` to `d_{Y/Z}(t)`.

## References

* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y Z Z' : AlgebraicSpaces B S hS} (q : Y ⟶ Z) (i : Z ⟶ Z')

/-- The universal `Z`-derivation `d_{Y/Z}` kills the image of the structure map of `q ≫ i`, on
underlying sheaves of sets. -/
theorem structureSharpInverseImageSet_comp_universalDerivationHom_of_comp :
    structureSharpInverseImageSet B S hS (q ≫ i) ≫ universalDerivationHom B S hS q =
      structureSharpInverseImageSet B S hS (q ≫ i) ≫
        zeroDerivationHom (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS q) :=
  structureSharpInverseImage_of_structureSharpSetComp B S hS (q ≫ i) _ _
    (structureSharpSet_comp_universalDerivationHom B S hS q i (q ≫ i) rfl)

/-- **A `Z'`-derivation of `𝒪_Y` kills the image of `q^♯` when `i : Z ⟶ Z'` is a closed
immersion**, for the universal `Z'`-derivation `d_{Y/Z'}`, on underlying sheaves of sets. -/
theorem structureSharpInverseImageSet_comp_universalDerivationHom_of_isClosedImmersion
    (hi : IsClosedImmersion B S hS i.hom) :
    structureSharpInverseImageSet B S hS q ≫ universalDerivationHom B S hS (q ≫ i) =
      structureSharpInverseImageSet B S hS q ≫
        zeroDerivationHom (structureRingSheaf B S hS Y)
          (sheafOfDifferentials B S hS (q ≫ i)) := by
  refine structureSharpInverseImage_of_structureSharpSetComp B S hS q _ _ ?_
  have : (smallEtaleDirectImage B S hS i).Faithful :=
    (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi).faithful
  have := epi_structureSharpSet B S hS i hi
  refine (smallEtaleDirectImage B S hS i).map_injective ((cancel_epi
    (structureSharpSet B S hS i)).1 ?_)
  refine (structureSharpSet_comp_map B S hS q i _).trans (Eq.trans ?_
    (structureSharpSet_comp_map B S hS q i _).symm)
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.assoc _ _ _))
  exact congrArg (fun m ↦ m ≫ (smallToposMorphismTypeU_comp B S hS q i).inv.app
      (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)
        (sheafOfDifferentials B S hS (q ≫ i))))
    (structureSharpSet_comp_universalDerivationHom B S hS (q ≫ i) (𝟙 Z') (q ≫ i)
      (Category.comp_id _).symm)

/-- A derivation morphism killing the image of a structure map kills it on local sections. -/
private theorem sections_map_eq_zero_of_comp_eq {W V : AlgebraicSpaces B S hS} (p : Y ⟶ V)
    (r : Y ⟶ W)
    (h : structureSharpInverseImageSet B S hS r ≫ universalDerivationHom B S hS p =
      structureSharpInverseImageSet B S hS r ≫
        zeroDerivationHom (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS p))
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).obj
      ((smallEtaleRingedToposHom B S hS r).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS W))) :
    (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map
        (structureSharpInverseImageSet B S hS r ≫ universalDerivationHom B S hS p) a =
      moduleZeroObj (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS p)
        (sectionsFunctor (SmallEtale.topology B S hS Y.1) U) :=
  (congrArg (fun m ↦ (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map m a) h).trans
  (map_zeroDerivationHom (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS p)
    (sectionsFunctor (SmallEtale.topology B S hS Y.1) U)
    ((sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map
      (structureSharpInverseImageSet B S hS r) a))

/-- `d_{Y/Z}` vanishes on the image of `(q ≫ i)^♯`, on local sections. -/
theorem universalDerivationHom_app_eq_zero_of_comp (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).obj
      ((smallEtaleRingedToposHom B S hS (q ≫ i)).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS Z'))) :
    (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map
        (structureSharpInverseImageSet B S hS (q ≫ i) ≫ universalDerivationHom B S hS q) a =
      moduleZeroObj (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS q)
        (sectionsFunctor (SmallEtale.topology B S hS Y.1) U) :=
  sections_map_eq_zero_of_comp_eq B S hS q (q ≫ i)
    (structureSharpInverseImageSet_comp_universalDerivationHom_of_comp B S hS q i) U a

/-- `d_{Y/Z'}` vanishes on the image of `q^♯` for a closed immersion `i`, on local sections. -/
theorem universalDerivationHom_app_eq_zero_of_isClosedImmersion
    (hi : IsClosedImmersion B S hS i.hom) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).obj
      ((smallEtaleRingedToposHom B S hS q).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS Z))) :
    (sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map
        (structureSharpInverseImageSet B S hS q ≫ universalDerivationHom B S hS (q ≫ i)) a =
      moduleZeroObj (structureRingSheaf B S hS Y) (sheafOfDifferentials B S hS (q ≫ i))
        (sectionsFunctor (SmallEtale.topology B S hS Y.1) U) :=
  sections_map_eq_zero_of_comp_eq B S hS (q ≫ i) q
    (structureSharpInverseImageSet_comp_universalDerivationHom_of_isClosedImmersion
      B S hS q i hi) U a

/-- `d_{Y/Z}`, read as a `Z'`-derivation. -/
def universalDerivationOfComp :
    PresheafOfModulesOfCommRing.Derivation' (sheafOfDifferentials B S hS q).val
      (structureSharpInverseImage B S hS (q ≫ i)).hom where
  d := (universalDerivation B S hS q).d
  d_mul := (universalDerivation B S hS q).d_mul
  d_map := (universalDerivation B S hS q).d_map
  d_app {U} a := universalDerivationHom_app_eq_zero_of_comp B S hS q i U a

/-- `d_{Y/Z'}`, read as a `Z`-derivation, for a closed immersion `i : Z ⟶ Z'`. -/
def universalDerivationOfIsClosedImmersion (hi : IsClosedImmersion B S hS i.hom) :
    PresheafOfModulesOfCommRing.Derivation' (sheafOfDifferentials B S hS (q ≫ i)).val
      (structureSharpInverseImage B S hS q).hom where
  d := (universalDerivation B S hS (q ≫ i)).d
  d_mul := (universalDerivation B S hS (q ≫ i)).d_mul
  d_map := (universalDerivation B S hS (q ≫ i)).d_map
  d_app {U} a := universalDerivationHom_app_eq_zero_of_isClosedImmersion B S hS q i hi U a

variable (hi : IsClosedImmersion B S hS i.hom)

/-- The comparison `Ω_{Y/Z'} ⟶ Ω_{Y/Z}`: the morphism through which `d_{Y/Z}`, read as a
`Z'`-derivation, factors. -/
def sheafOfDifferentialsCompClosedImmersionHom :
    sheafOfDifferentials B S hS (q ≫ i) ⟶ sheafOfDifferentials B S hS q :=
  (differentialsHomEquiv B S hS (q ≫ i) (sheafOfDifferentials B S hS q)).symm
    (universalDerivationOfComp B S hS q i)

/-- The comparison `Ω_{Y/Z} ⟶ Ω_{Y/Z'}`: the morphism through which `d_{Y/Z'}`, read as a
`Z`-derivation, factors. -/
def sheafOfDifferentialsCompClosedImmersionInv :
    sheafOfDifferentials B S hS q ⟶ sheafOfDifferentials B S hS (q ≫ i) :=
  (differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS (q ≫ i))).symm
    (universalDerivationOfIsClosedImmersion B S hS q i hi)

/-- Postcomposing `d_{Y/Z'}` with `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` gives `d_{Y/Z}`, read as a
`Z'`-derivation. -/
lemma postcomp_sheafOfDifferentialsCompClosedImmersionHom :
    (universalDerivation B S hS (q ≫ i)).postcomp
        (sheafOfDifferentialsCompClosedImmersionHom B S hS q i).val =
      universalDerivationOfComp B S hS q i :=
  (differentialsHomEquiv B S hS (q ≫ i) (sheafOfDifferentials B S hS q)).apply_symm_apply _

/-- Postcomposing `d_{Y/Z}` with `Ω_{Y/Z} ⟶ Ω_{Y/Z'}` gives `d_{Y/Z'}`, read as a
`Z`-derivation. -/
lemma postcomp_sheafOfDifferentialsCompClosedImmersionInv :
    (universalDerivation B S hS q).postcomp
        (sheafOfDifferentialsCompClosedImmersionInv B S hS q i hi).val =
      universalDerivationOfIsClosedImmersion B S hS q i hi :=
  (differentialsHomEquiv B S hS q (sheafOfDifferentials B S hS (q ≫ i))).apply_symm_apply _

/-- **`Ω_{Y/Z'} ≅ Ω_{Y/Z}` for a closed immersion `i : Z ⟶ Z'`.** Both sheaves corepresent the
same functor of derivations of `𝒪_Y`, so the identification is the one matching the two universal
derivations (`AlgebraicGeometry.Space.sheafOfDifferentialsCompClosedImmersionIso_hom_d`). -/
def sheafOfDifferentialsCompClosedImmersionIso :
    sheafOfDifferentials B S hS (q ≫ i) ≅ sheafOfDifferentials B S hS q where
  hom := sheafOfDifferentialsCompClosedImmersionHom B S hS q i
  inv := sheafOfDifferentialsCompClosedImmersionInv B S hS q i hi
  hom_inv_id := by
    refine (differentialsHomEquiv B S hS (q ≫ i) _).injective ?_
    refine Eq.trans (PresheafOfModulesOfCommRing.Derivation'.postcomp_comp _ _ _) ?_
    refine Eq.trans ?_ (PresheafOfModulesOfCommRing.Derivation'.postcomp_id _).symm
    rw [postcomp_sheafOfDifferentialsCompClosedImmersionHom]
    apply PresheafOfModulesOfCommRing.Derivation.ext
    ext U x
    exact PresheafOfModulesOfCommRing.Derivation.congr_d
      (postcomp_sheafOfDifferentialsCompClosedImmersionInv B S hS q i hi) x
  inv_hom_id := by
    refine (differentialsHomEquiv B S hS q _).injective ?_
    refine Eq.trans (PresheafOfModulesOfCommRing.Derivation'.postcomp_comp _ _ _) ?_
    refine Eq.trans ?_ (PresheafOfModulesOfCommRing.Derivation'.postcomp_id _).symm
    rw [postcomp_sheafOfDifferentialsCompClosedImmersionInv]
    apply PresheafOfModulesOfCommRing.Derivation.ext
    ext U x
    exact PresheafOfModulesOfCommRing.Derivation.congr_d
      (postcomp_sheafOfDifferentialsCompClosedImmersionHom B S hS q i) x

/-- The identification `Ω_{Y/Z'} ≅ Ω_{Y/Z}` carries `d_{Y/Z'}(t)` to `d_{Y/Z}(t)`, so it is the
canonical one and not merely some isomorphism. -/
theorem sheafOfDifferentialsCompClosedImmersionIso_hom_d {U : (SmallEtale B S hS Y.1)ᵒᵖ}
    (x : (structureRingSheaf B S hS Y).obj.obj U) :
    (((sheafOfDifferentialsCompClosedImmersionIso B S hS q i hi).hom.val.app U).hom)
        ((universalDerivation B S hS (q ≫ i)).d x) =
      (universalDerivation B S hS q).d x :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (postcomp_sheafOfDifferentialsCompClosedImmersionHom B S hS q i) x

end AlgebraicGeometry.Space

end
