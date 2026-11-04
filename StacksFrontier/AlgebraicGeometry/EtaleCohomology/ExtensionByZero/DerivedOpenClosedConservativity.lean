module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed subscheme and its open complement on the derived category

Let `X` be a scheme, `i : Z ⟶ X` a morphism and `j : U ⟶ X` an étale morphism whose image is the
complement of the image of `i`; the case in mind is a closed immersion and the open immersion of
its complement. This file records the facts about the derived categories of abelian sheaves on the
small étale sites that the corresponding facts for sheaves give at once.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianDerivedInverseImage_of_range_eq_compl`: the
  derived inverse images `i⁻¹` and `j⁻¹` jointly reflect isomorphisms of `D(X_étale)`.
* `Stacks.EtaleCohomology.isZero_etaleAbelianDerivedInverseImage_derivedDirectImage`: for a
  closed immersion `i`, `j⁻¹ Ri_* M = 0` for every `M` in `D(Z_étale)`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedAdjunction_counit_of_isClosedImmersion`: for a
  closed immersion `i`, the counit `i⁻¹ Ri_* ⟶ 𝟭` of the derived adjunction is an isomorphism.
* `Stacks.EtaleCohomology.isIso_map_etaleAbelianDerivedAdjunction_unit_app_of_isClosedImmersion`:
  for a closed immersion `i`, the inverse image `i⁻¹` of the unit `𝟭 ⟶ Ri_* i⁻¹` is an
  isomorphism.

## Implementation notes

The inverse images are exact, so their derived versions commute with the cohomology sheaves
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`); the first two results are therefore
read off degreewise from `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage` and
`Stacks.EtaleCohomology.isZero_etaleRestriction_etaleAbelianDirectImage`, the derived direct
image along a closed immersion being the degreewise one
(`Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageIso_of_isIntegralHom`).

The counit of the derived adjunction is computed at an object represented by a complex by
`Stacks.DerivedFunctor.derivedAdjunction_counit_app`: it is the counit of the underived
adjunction applied degreewise, up to the derived-functor unit of `Ri_*` and the exactness
comparison of `i⁻¹`. The derived-functor unit is invertible on every complex for an integral
morphism, and the underived counit is invertible because `i_*` is fully faithful for a closed
immersion; every object of the derived category is represented by a complex.

## References

* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section Complementary

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- **The derived inverse images to a closed subscheme and to its open complement jointly
reflect isomorphisms.** A morphism `γ` of `D(X_étale)` such that `i⁻¹ γ` and `j⁻¹ γ` are
isomorphisms is an isomorphism: the inverse images are exact, so this holds on every cohomology
sheaf by the corresponding statement for abelian sheaves. -/
public theorem isIso_of_isIso_etaleAbelianDerivedInverseImage_of_range_eq_compl
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (γ : K ⟶ L) (hi : IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map γ))
    (hj : IsIso ((etaleAbelianDerivedInverseImage.{u, v} j).map γ)) : IsIso γ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := ((etaleAbelianInverseImage.{u, v} i).isIso_mapDerivedCategory_map_iff γ).1 hi n
  have := ((etaleAbelianInverseImage.{u, v} j).isIso_mapDerivedCategory_map_iff γ).1 hj n
  exact isIso_of_isIso_etaleAbelianInverseImage i j hij _

/-- **The open part of a direct image from the closed part vanishes, on the derived category.**
For a closed immersion `i : Z ⟶ X` and an étale `j : U ⟶ X` with complementary image,
`j⁻¹ Ri_* M = 0` for every `M` in `D(Z_étale)`: `Ri_*` is the degreewise direct image, so the
cohomology sheaves of `j⁻¹ Ri_* M` are `j⁻¹ i_* Hⁿ(M)`, which vanish. -/
public theorem isZero_etaleAbelianDerivedInverseImage_derivedDirectImage [IsClosedImmersion i]
    [Etale j] (M : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    IsZero ((etaleAbelianDerivedInverseImage.{u, v} j).obj
      ((etaleAbelianDerivedDirectImage.{u, v} i).obj M)) := by
  refine IsZero.of_iso ?_ ((etaleAbelianDerivedInverseImage.{u, v} j).mapIso
    ((etaleAbelianDerivedDirectImageIso_of_isIntegralHom.{u, v} i).app M))
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} i) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} i
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, v} j).mapDerivedCategoryHomologyIso
    n).app _)
  refine IsZero.of_iso ?_ ((etaleAbelianInverseImage.{u, v} j).mapIso
    (((etaleAbelianDirectImage.{u, v} i).mapDerivedCategoryHomologyIso n).app M))
  exact IsZero.of_iso (isZero_etaleRestriction_etaleAbelianDirectImage i j hij _)
    ((etaleAbelianInverseImageRestrictionIso.{u, v} j).app _)

end Complementary

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The counit of the inverse-image/direct-image adjunction of abelian sheaves along a closed
immersion is an isomorphism: the direct image is fully faithful. -/
@[sga "4 VIII 5.7" "special case"]
instance isIso_etaleAbelianInverseImageDirectImageAdj_counit_of_isClosedImmersion :
    IsIso (etaleAbelianInverseImageDirectImageAdj.{u, v} i).counit := by
  let ff := etaleAbelianDirectImageFullyFaithful.{u, v} i
  let _ := ff.full
  let _ := ff.faithful
  infer_instance

/-- **For a closed immersion `i`, the counit `i⁻¹ Ri_* ⟶ 𝟭` of the derived adjunction is an
isomorphism.** At an object represented by a complex `K` it is, up to the derived-functor unit of
`Ri_*` — invertible because `i` is integral — and the exactness comparison of `i⁻¹`, the
degreewise counit of `i⁻¹ ⊣ i_*`, which is invertible because `i_*` is fully faithful. -/
public instance isIso_etaleAbelianDerivedAdjunction_counit_of_isClosedImmersion :
    IsIso (etaleAbelianDerivedAdjunction.{u, v} i).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Qh.obj K ≅ M) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ))).mem_essImage M |>.getIso⟩⟩
  rw [NatTrans.isIso_app_iff_of_iso _ e.symm]
  have hcc := Stacks.DerivedFunctor.derivedAdjunction_counit_app
    (etaleAbelianInverseImageDirectImageAdj.{u, v} i)
    (etaleAbelianDerivedDirectImage.{u, v} i) (etaleAbelianDerivedDirectImageUnit.{u, v} i)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective K
  have : IsIso (etaleAbelianDerivedDirectImageUnit.{u, v} i) :=
    isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom.{u, v} i
  have : IsIso ((Adjunction.mapHomotopyCategoryAdjunction
      (etaleAbelianInverseImageDirectImageAdj.{u, v} i) (ComplexShape.up ℤ)).counit.app K) := by
    obtain ⟨K⟩ := K
    have : IsIso ((Adjunction.mapHomologicalComplexAdjunction
        (etaleAbelianInverseImageDirectImageAdj.{u, v} i) (ComplexShape.up ℤ)).counit.app K) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact Functor.map_isIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      ((Adjunction.mapHomologicalComplexAdjunction
        (etaleAbelianInverseImageDirectImageAdj.{u, v} i) (ComplexShape.up ℤ)).counit.app K)
  exact IsIso.of_isIso_fac_left hcc

/-- **For a closed immersion `i`, `i⁻¹` inverts the unit `𝟭 ⟶ Ri_* i⁻¹`** of the derived
adjunction: by the triangle identity, `i⁻¹` of the unit is a section of the counit at `i⁻¹ M`,
which is an isomorphism. -/
public instance isIso_map_etaleAbelianDerivedAdjunction_unit_app_of_isClosedImmersion
    (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map
      ((etaleAbelianDerivedAdjunction.{u, v} i).unit.app M)) := by
  have : IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map
      ((etaleAbelianDerivedAdjunction.{u, v} i).unit.app M) ≫
        (etaleAbelianDerivedAdjunction.{u, v} i).counit.app
          ((etaleAbelianDerivedInverseImage.{u, v} i).obj M)) := by
    rw [(etaleAbelianDerivedAdjunction.{u, v} i).left_triangle_components M]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((etaleAbelianDerivedAdjunction.{u, v} i).counit.app _)

end ClosedImmersion

end Stacks.EtaleCohomology

end
