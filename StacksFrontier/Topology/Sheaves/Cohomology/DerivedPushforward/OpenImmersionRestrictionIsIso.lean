module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OpenImmersionDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.IsoOnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# Restriction to an open subspace and derived sections over the opens it covers

Let `h : X' ⟶ X` be an open immersion of ringed spaces. Restriction `h^* : D(𝒪_X) ⥤ D(𝒪_{X'})`
is left adjoint to `Rh_*`, and the unit `K ⟶ Rh_*h^*K` induces isomorphisms on derived sections
over every open `W ⊆ h(X')` ([Stacks, Tag 0D5V]). Consequently a morphism `φ` of `D(𝒪_X)` which
induces bijections on `H^k(W, -)` for all opens `W ⊆ h(X')` restricts to an isomorphism
`h^*φ` of `D(𝒪_{X'})`: the hypercohomology of `h^*φ` over an open `V` of `X'` is that of
`Rh_*h^*φ` over `h(V)` ([Stacks, Tag 0D5W]), which is that of `φ` over `h(V)`.

## Main definitions

* `Stacks.Cohomology.OpenImmersionSections.restrictionAdjunction`: the adjunction
  `h^* ⊣ Rh_*` on derived categories.

## Main results

* `Stacks.Cohomology.OpenImmersionSections.isIso_derivedSectionsOverOpen_map_unit_app`: the unit
  induces isomorphisms on derived sections over the opens inside the image of `h`.
* `Stacks.Cohomology.OpenImmersionSections.isIso_mapDerivedCategory_map_of_bijective`: a morphism
  bijective on hypercohomology over the opens inside the image of `h` restricts to an
  isomorphism.

## References

* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Cohomology.OpenImmersionSections

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X) [hh : SheafedSpace.IsOpenImmersion h]

/-- Pullback of sheaves of modules along an open immersion preserves finite limits. -/
instance preservesFiniteLimits_modulePullback : PreservesFiniteLimits (modulePullback h) :=
  (modulePullback h).preservesFiniteLimits_of_preservesHomology

/-- **The adjunction `h^* ⊣ Rh_*`** on derived categories, for an open immersion `h` of ringed
spaces, induced by the adjunction `h^* ⊣ h_*` and the exactness of `h^*`. -/
abbrev restrictionAdjunction :
    (modulePullback h).mapDerivedCategory ⊣ derivedPushforward h :=
  Stacks.DerivedFunctor.derivedAdjunction (modulePullbackPushforwardAdjunction h)
    (derivedPushforward h) (derivedPushforwardUnit h) (exists_quasiIso_isKInjective X')

/-- The unit of `h^* ⊣ Rh_*` at the class of a complex `M` is, up to the identifications of `Q`
with `Qh ∘ quotient` and of `h^*` on derived categories with `h^*` on complexes, the unit
`M ⟶ h_*h^*M` followed by the comparison `h_* ⟶ Rh_*`. -/
theorem pullbackUnitQ_eq_unit_app
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    pullbackUnitQ h M =
      (DerivedCategory.quotientCompQhIso _).inv.app M ≫
        (restrictionAdjunction h).unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward h).map
          ((modulePullback h).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward h).map ((DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
  have hu := Stacks.DerivedFunctor.derivedAdjunction_unit_app
    (modulePullbackPushforwardAdjunction h) (derivedPushforward h) (derivedPushforwardUnit h)
    (exists_quasiIso_isKInjective X') ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)
  rw [Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient] at hu
  have hn : DerivedCategory.Q.map (pullbackUnitComplex h M) ≫
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
        (((modulePushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app M ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (pullbackUnitComplex h M)) :=
    DerivedCategory.quotientCompQhIso_inv_naturality (pullbackUnitComplex h M)
  have e₁ : pullbackUnitQ h M = DerivedCategory.Q.map (pullbackUnitComplex h M) ≫
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
        (((modulePushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (derivedPushforwardUnit h).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (derivedPushforward h).map
        ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X'))).hom.app
          (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := rfl
  refine (e₁.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    (Category.assoc _ _ _)))).trans ?_
  exact congrArg (_ ≫ ·) (((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu).trans
    (Category.assoc _ _ _))).symm)

/-- **The unit of `h^* ⊣ Rh_*` induces isomorphisms on derived sections over the opens inside
the image of `h`** ([Stacks, Tag 0D5V]). -/
theorem isIso_derivedSectionsOverOpen_map_unit_app (W : Opens X.carrier)
    (hW : (W : Set X.carrier) ⊆ Set.range h.hom.base)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedSectionsOverOpen X W).map ((restrictionAdjunction h).unit.app K)) := by
  let N := DerivedCategory.Qh.objPreimage K
  let e : DerivedCategory.Qh.obj N ≅ K := DerivedCategory.Qh.objObjPreimageIso K
  have hnat := (restrictionAdjunction h).unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hnat
  suffices hN : IsIso ((derivedSectionsOverOpen X W).map
      ((restrictionAdjunction h).unit.app (DerivedCategory.Qh.obj N))) by
    have h₁ : (derivedSectionsOverOpen X W).map ((restrictionAdjunction h).unit.app K) =
        (derivedSectionsOverOpen X W).map e.inv ≫
          (derivedSectionsOverOpen X W).map
            ((restrictionAdjunction h).unit.app (DerivedCategory.Qh.obj N)) ≫
          (derivedSectionsOverOpen X W).map ((derivedPushforward h).map
            ((modulePullback h).mapDerivedCategory.map e.hom)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← hnat, Iso.inv_hom_id_assoc]
    rw [h₁]
    infer_instance
  have hP := isIso_derivedSectionsOverOpen_map_pullbackUnitQ h W hW N.as
  rw [pullbackUnitQ_eq_unit_app] at hP
  simp only [Functor.map_comp] at hP
  have h₂ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hP
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      ((derivedSectionsOverOpen X W).mapIso ((derivedPushforward h).mapIso
        ((modulePullback h).mapDerivedCategoryFactorsh.app _))).isIso_hom
      ((derivedSectionsOverOpen X W).mapIso ((derivedPushforward h).mapIso
        ((DerivedCategory.quotientCompQhIso _).app _))).isIso_hom) h₂

/-- The open of `X` which is the image of an open `V` of `X'`. -/
abbrev imageOpen (V : Opens X'.carrier) : Opens X.carrier :=
  hh.base_open.functor.obj V

/-- The image `h(V)` of an open `V` of `X'` is contained in the range of `h`. -/
theorem imageOpen_subset_range (V : Opens X'.carrier) :
    ((imageOpen h V : Opens X.carrier) : Set X.carrier) ⊆ Set.range h.hom.base := by
  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

/-- The preimage under `h` of the image `h(V)` of an open `V` of `X'` is `V`. -/
theorem opensMap_obj_imageOpen (V : Opens X'.carrier) :
    (opensMap h).obj (imageOpen h V) = V :=
  Opens.ext (Set.preimage_image_eq _ hh.base_open.injective)

/-- **A morphism of `D(𝒪_X)` inducing bijections on hypercohomology over the opens inside the
image of an open immersion `h` restricts to an isomorphism `h^*φ`.** -/
theorem isIso_mapDerivedCategory_map_of_bijective
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hφ : ∀ (W : Opens X.carrier), (W : Set X.carrier) ⊆ Set.range h.hom.base → ∀ k : ℤ,
      Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
        ((derivedSectionsOverOpen X W).map φ))) :
    IsIso ((modulePullback h).mapDerivedCategory.map φ) := by
  refine Stacks.Cohomology.DerivedIsoOnABasis.isIso_of_bijective_homology_derivedSectionsOverOpen
    (B := Set.univ) (Opens.isBasis_iff_nbhd.2 fun {U} {x} hx => ⟨U, Set.mem_univ _, hx, le_rfl⟩)
    _ fun V _ k => ?_
  let W := imageOpen h V
  have hW := imageOpen_subset_range h V
  let H := derivedSectionsOverOpen X W ⋙ DerivedCategory.homologyFunctor _ k
  have hnat := (restrictionAdjunction h).unit.naturality φ
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hunit (M) : Function.Bijective (H.map ((restrictionAdjunction h).unit.app M)) := by
    have := isIso_derivedSectionsOverOpen_map_unit_app h W hW M
    exact (ConcreteCategory.isIso_iff_bijective _).1 (Functor.map_isIso
      (DerivedCategory.homologyFunctor _ k)
      ((derivedSectionsOverOpen X W).map ((restrictionAdjunction h).unit.app M)))
  have hcomp : Function.Bijective (H.map ((restrictionAdjunction h).unit.app K) ≫
      H.map ((derivedPushforward h).map ((modulePullback h).mapDerivedCategory.map φ))) := by
    rw [← H.map_comp, ← hnat, H.map_comp]
    exact (hunit L).comp (hφ W hW k)
  have key := (bijective_homology_map_derivedPushforward_iff h W
    ((modulePullback h).mapDerivedCategory.map φ) k).1
    ((Function.Bijective.of_comp_iff _ (hunit K)).mp hcomp)
  rwa [opensMap_obj_imageOpen] at key

end Stacks.Cohomology.OpenImmersionSections

end
