module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtaleDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh

/-!
# Stacks 0DGU: ph and étale derived categories agree on torsion complexes

Let `P` be a big ph site of algebraic spaces over `S`, `E` a big étale site over the same big fppf
site of schemes, and `X` an algebraic space.

## Main results

* `Stacks.Torsion.exists_mapDerivedCategoryPlus_iso_of_torsionCohomology`: a bounded below complex
  of abelian sheaves with torsion cohomology sheaves is the image of a bounded below complex of
  torsion sheaves (Stacks 0DD7, on bounded below derived categories).
* `AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtale_derivedUnits`: **Stacks 0DGU**, for `K` in
  `D⁺(X_étale)` with torsion cohomology sheaves the maps `π_X⁻¹K ⟶ Rε_{X,*}a_X⁻¹K` and
  `K ⟶ Ra_{X,*}a_X⁻¹K` are isomorphisms.

## Implementation notes

The source's reduction to a single torsion sheaf is
`Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus` applied
along the exact inclusion of torsion sheaves, whose bounded below derived category covers the
objects with torsion cohomology by Stacks 0DD7. On a single torsion sheaf `F` the unit is
invertible by Stacks 0DGT, part (1) (`a_{X,*}a_X⁻¹F = F` and `ε_{X,*}a_X⁻¹F = π_X⁻¹F`), and
`a_X⁻¹F` is acyclic for `ε_{X,*}` by Stacks 0DGT, part (2), hence for `a_{X,*}` as
`R^q a_{X,*} = π_{X,*} R^q ε_{X,*}` with `π_{X,*}` exact (the Leray spectral sequence of the
source, Stacks 0DGC and 0734, collapses). The derived categories are in the model
`HasDerivedCategory.standard`, the model in which Stacks 0DD7 is available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Torsion

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0DD7 on bounded below derived categories.** A bounded below object `K` of the derived
category of abelian sheaves whose cohomology sheaves are torsion is the image of a bounded below
object of the derived category of torsion sheaves: the preimage of `K` under the equivalence of
Stacks 0DD7 is bounded below, because the inclusion of torsion sheaves is exact and reflects zero
objects. -/
theorem exists_mapDerivedCategoryPlus_iso_of_torsionCohomology
    (K : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{w}))
    (hK : ∀ i : ℤ, torsionSheafProperty J
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    ∃ K' : DerivedCategory.Plus (TorsionSheaf J),
      Nonempty ((torsionSheafProperty J).ι.mapDerivedCategoryPlus.obj K' ≅ K) := by
  obtain ⟨e, ⟨α⟩⟩ := exists_torsionDerivedEquivalence J
  let KT : TorsionDerivedCategory J := ⟨DerivedCategory.Plus.ι.obj K, hK⟩
  let M := e.inverse.obj KT
  let eM : (torsionSheafProperty J).ι.mapDerivedCategory.obj M ≅ DerivedCategory.Plus.ι.obj K :=
    (α.app M).symm ≪≫ (torsionCohomologyProperty J).ι.mapIso (e.counitIso.app KT)
  obtain ⟨n, hn⟩ := K.property
  have : (DerivedCategory.Plus.ι.obj K).IsGE n := hn
  have hM : M.IsGE n := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    have h1 : IsZero ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K)) :=
      DerivedCategory.isZero_of_isGE _ n i hi
    have h2 : IsZero ((torsionSheafProperty J).ι.obj
        ((DerivedCategory.homologyFunctor _ i).obj M)) :=
      h1.of_iso ((((torsionSheafProperty J).ι.mapDerivedCategoryHomologyIso i).app M).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso eM)
    rw [IsZero.iff_id_eq_zero]
    apply (torsionSheafProperty J).ι.map_injective
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact h2.eq_of_src _ _
  exact ⟨⟨M, ⟨n, hM⟩⟩, ⟨ObjectProperty.isoMk _ eM⟩⟩

end Stacks.Torsion

namespace AlgebraicGeometry.BigPHSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive
  HasDerivedCategory.standard

universe u

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite) (X : P.Spaces)

/-- The unit of `ε_X⁻¹ ⊣ ε_{X,*}` on abelian sheaves is invertible at `π_X⁻¹F`, for every abelian
sheaf `F` on `X_étale`: `π_X⁻¹F = ε_{X,*}a_X⁻¹F` is in the essential image of the fully faithful
`ε_{X,*}` (Stacks 0DGT, part (1), for abelian sheaves). -/
theorem isIso_phToBigEtaleAbelianAdjunction_unit_app_inverseImage
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1}) :
    IsIso ((phToBigEtaleAbelianAdjunction P E h X).unit.app
      ((CategoryTheory.Sites.abelianInverseImage
        (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).obj F)) :=
  ((phToBigEtaleAbelianAdjunction P E h X).isIso_unit_app_iff_mem_essImage).2
    ⟨_, ⟨(phToSmallEtale_abelianInverseImage_comp_pushforwardIso P E h X).app F⟩⟩

/-- The unit of `a_X⁻¹ ⊣ a_{X,*}` on abelian sheaves is invertible: `a_{X,*}a_X⁻¹ = 𝟭`
(Stacks 0DGT, part (1), for abelian sheaves). -/
theorem isIso_phToSmallEtaleAbelianAdjunction_unit :
    IsIso (phToSmallEtaleAbelianAdjunction P E h X).unit :=
  Stacks.Adjunction.isIso_unit_of_comp_iso_id (phToSmallEtaleAbelianAdjunction P E h X)
    (phToSmallEtale_abelianInverseImage_comp_restrictionIso P E h X)

/-- **`a_X⁻¹F` is acyclic for `ε_{X,*}`** for a torsion abelian sheaf `F` on `X_étale`: Stacks
0DGT, part (2). -/
theorem rightAcyclic_phToBigEtaleAbelianPushforward_of_torsion
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    (phToBigEtaleAbelianPushforward P E h X).rightAcyclic
      ((CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)).obj F) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp ↦
    isZero_rightDerived_phToBigEtale_abelianInverseImage P E h X F hF p hp

/-- **`a_X⁻¹F` is acyclic for `a_{X,*}`** for a torsion abelian sheaf `F` on `X_étale`:
`R^q a_{X,*}` is `π_{X,*} ∘ R^q ε_{X,*}`, the restriction `π_{X,*}` being exact. -/
theorem rightAcyclic_phToSmallEtaleAbelianPushforward_of_torsion
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    (phToSmallEtaleAbelianPushforward P E h X).rightAcyclic
      ((CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)).obj F) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp ↦
    ((E.bigToSmallEtaleRestriction (etaleSpace P E h X)).map_isZero
      (isZero_rightDerived_phToBigEtale_abelianInverseImage P E h X F hF p hp)).of_iso
      ((Functor.rightDerivedCompIso (phToBigEtaleAbelianPushforward P E h X)
        (E.bigToSmallEtaleRestriction (etaleSpace P E h X)) p).app _)

/-- Let `X` be an algebraic space over `S` and `K` an object of `D⁺(X_étale)` whose cohomology
sheaves are torsion. Then the maps `π_X⁻¹K ⟶ Rε_{X,*}a_X⁻¹K` and `K ⟶ Ra_{X,*}a_X⁻¹K` are
isomorphisms, for the comparison morphisms `ε_X` and `a_X = π_X ∘ ε_X` from the big ph topos of `X`
(Stacks 0DGW). The two maps are the units of the derived adjunctions `ε_X⁻¹ ⊣ Rε_{X,*}` at `π_X⁻¹K`
and `a_X⁻¹ ⊣ Ra_{X,*}` at `K` on bounded below derived categories. -/
@[stacks 0DGU]
theorem isIso_phToSmallEtale_derivedUnits
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h X)) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (phToBigEtaleAbelianAdjunction P E h X)).unit.app
          ((CategoryTheory.Sites.abelianInverseImage
            (E.bigToSmallEtaleMorphism (etaleSpace P E h X))).mapDerivedCategoryPlus.obj K)) ∧
      IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
        (phToSmallEtaleAbelianAdjunction P E h X)).unit.app K) := by
  let J := Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X)
  obtain ⟨K', ⟨eK⟩⟩ := Stacks.Torsion.exists_mapDerivedCategoryPlus_iso_of_torsionCohomology J K hK
  let ι := (Stacks.Torsion.torsionSheafProperty J).ι
  let πinv := CategoryTheory.Sites.abelianInverseImage
    (E.bigToSmallEtaleMorphism (etaleSpace P E h X))
  have : PreservesFiniteLimits πinv :=
    CategoryTheory.Sites.abelianInverseImage_preservesFiniteLimits _
  have : PreservesFiniteColimits πinv :=
    have := (E.bigToSmallEtaleAbelianAdjunction (etaleSpace P E h X)).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} πinv
  have hu₁ : ∀ F : Stacks.Torsion.TorsionSheaf J,
      IsIso ((phToBigEtaleAbelianAdjunction P E h X).unit.app ((ι ⋙ πinv).obj F)) :=
    fun F ↦ isIso_phToBigEtaleAbelianAdjunction_unit_app_inverseImage P E h X (ι.obj F)
  have hac₁ : ∀ F : Stacks.Torsion.TorsionSheaf J,
      (phToBigEtaleAbelianPushforward P E h X).rightAcyclic
        ((CategoryTheory.Sites.abelianInverseImage (phToBigEtaleMorphism P E h X)).obj
          ((ι ⋙ πinv).obj F)) :=
    fun F ↦ (phToBigEtaleAbelianPushforward P E h X).rightAcyclic.prop_of_iso
      ((phToSmallEtale_abelianInverseImageCompIso P E h X).app (ι.obj F)).symm
      (rightAcyclic_phToBigEtaleAbelianPushforward_of_torsion P E h X (ι.obj F) F.property)
  have hu₂ := isIso_phToSmallEtaleAbelianAdjunction_unit P E h X
  have hac₂ : ∀ F : Stacks.Torsion.TorsionSheaf J,
      (phToSmallEtaleAbelianPushforward P E h X).rightAcyclic
        ((CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)).obj
          (ι.obj F)) :=
    fun F ↦ rightAcyclic_phToSmallEtaleAbelianPushforward_of_torsion P E h X (ι.obj F) F.property
  let e₁ : (ι ⋙ πinv).mapDerivedCategoryPlus.obj K' ≅ πinv.mapDerivedCategoryPlus.obj K :=
    ((Functor.mapDerivedCategoryPlusCompIsoh (Iso.refl (ι ⋙ πinv))).app K').symm ≪≫
      πinv.mapDerivedCategoryPlus.mapIso eK
  refine ⟨(NatTrans.isIso_app_iff_of_iso _ e₁).1 ?_, (NatTrans.isIso_app_iff_of_iso _ eK).1 ?_⟩
  · exact Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus
      (ι ⋙ πinv) (phToBigEtaleAbelianAdjunction P E h X) hu₁ hac₁ K'
  · exact Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus
      ι (phToSmallEtaleAbelianAdjunction P E h X) (fun F ↦ inferInstance) hac₂ K'

end AlgebraicGeometry.BigPHSpaceSite

end
