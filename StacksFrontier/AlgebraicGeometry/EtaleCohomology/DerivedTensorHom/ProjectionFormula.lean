module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.CategoryTheory.Adjunction.ExtensionProjectionMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# The projection formula for extension by zero along an open immersion, on `D(X_étale, Λ)`

Let `j : U ⟶ X` be an open immersion of schemes and `Λ` a commutative ring. For `L` in
`D(X_étale, Λ)` and `Z` in `D(U_étale, Λ)` the projection map

`j_!(j^{-1}L ⊗^L_Λ Z) ⟶ L ⊗^L_Λ j_!Z`

(`CategoryTheory.extensionProjectionMap`, for the adjunction `j_! ⊣ j^{-1}` and the
compatibility of `j^{-1}` with `⊗^L_Λ`) is an isomorphism: this is [Stacks, Tag 0GL1] for the
localization of the small étale site of `X` at `U`, with the extension by zero in the second
tensor factor. Combined with `j^{-1}Rj_* = id`, it gives the identification

`Rj_*M ⊗^L_Λ j_!B ≅ j_!(M ⊗^L_Λ B)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleDerivedExtensionByZeroAdj`: `j_! ⊣ j^{-1}` on unbounded derived
  categories.
* `Stacks.EtaleCohomology.etaleDerivedProjectionMap`: the projection map
  `j_!(j^{-1}L ⊗^L_Λ Z) ⟶ L ⊗^L_Λ j_!Z`.
* `Stacks.EtaleCohomology.etaleDerivedProjectionIso`: the projection formula, as an isomorphism
  of bifunctors.
* `Stacks.EtaleCohomology.etaleDerivedPushforwardProjectionIso`:
  `Rj_*M ⊗^L_Λ j_!B ≅ j_!(M ⊗^L_Λ B)`, as an isomorphism of bifunctors.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleDerivedProjectionMap_app_app`: the projection map is an
  isomorphism.
* `Stacks.EtaleCohomology.isIso_etaleDerivedInverseImageCounit`: `j^{-1}Rj_* = id`.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleDerivedInverseImage`: the inverse images to
  `U` and to its closed complement jointly reflect isomorphisms of `D(X_étale, Λ)`.

## References

* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard
universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ]

section Conservative

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij in
/-- **The inverse images to an open and to its closed complement jointly reflect isomorphisms of
`D(X_étale, Λ)`**. -/
theorem isIso_of_isIso_etaleModuleDerivedInverseImage
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X)} (φ : K ⟶ L)
    (hi : IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ i).map φ))
    (hj : IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ j).map φ)) : IsIso φ := by
  refine (DerivedCategory.isIso_iff _ φ).2 fun n => ?_
  have key : ∀ {V : Scheme.{u}} (f : V ⟶ X),
      IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ f).map φ) →
        IsIso ((etaleModuleInverseImage.{u, r} Λ f).map
          ((DerivedCategory.homologyFunctor _ n).map φ)) := fun f hf =>
    (NatIso.isIso_map_iff (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (etaleModuleInverseImage.{u, r} Λ f) n) φ).1
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((etaleModuleDerivedInverseImage.{u, r} Λ f).map φ))))
  have := key i hi
  have := key j hj
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

/-- An object of the derived category all of whose cohomology objects vanish is zero. -/
theorem isZero_of_isZero_homology {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (hK : ∀ n, IsZero ((DerivedCategory.homologyFunctor A n).obj K)) :
    IsZero K := by
  have : IsIso (0 : K ⟶ K) :=
    (DerivedCategory.isIso_iff _ _).2 fun n => ⟨⟨0, (hK n).eq_of_src _ _, (hK n).eq_of_src _ _⟩⟩
  exact IsZero.of_mono_zero K K

variable [Etale j]

include hij in
/-- **The inverse image to the closed complement kills extensions by zero**, on
`D(U_étale, Λ)`. -/
theorem isZero_etaleModuleDerivedInverseImage_extensionByZero
    (W : DerivedCategory (EtaleModules.{u, r} Λ U)) :
    IsZero ((etaleModuleDerivedInverseImage.{u, r} Λ i).obj
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj W)) := by
  refine isZero_of_isZero_homology _ fun n => ?_
  refine IsZero.of_iso ?_ ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (etaleModuleInverseImage.{u, r} Λ i) n).app _)
  refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, r} Λ i).mapIso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).app W) ≪≫
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (etaleModuleExtensionByZero.{u, r} Λ j) n).app W))
  exact isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _

end Conservative

section Tensor

variable (X : Scheme.{u})

/-- The derived tensor product on `D(X_étale, Λ)` is symmetric, objectwise. -/
def etaleDerivedTensorBraidingIso (A B : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ((etaleDerivedTensor.{u, r} Λ X).obj A).obj B ≅ ((etaleDerivedTensor.{u, r} Λ X).obj B).obj A :=
  (etaleDerivedEquivalence.{u, r} Λ X).inverse.mapIso
    (((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (etaleRingedSite.{u, r} Λ X)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (etaleRingedSite.{u, r} Λ X).O)).app _).app _)

/-- **Tensoring with a zero object gives zero**, on either side. -/
theorem isZero_etaleDerivedTensor_obj_obj (A B : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hB : IsZero B) : IsZero (((etaleDerivedTensor.{u, r} Λ X).obj A).obj B) := by
  have := (TensorHomAdjunction.flipAdjunction
    (etaleTensorHomAdjunction.{u, r} Λ X) A).isLeftAdjoint
  exact (Functor.map_isZero ((etaleDerivedTensor.{u, r} Λ X).flip.obj A) hB).of_iso
    (etaleDerivedTensorBraidingIso.{u, r} Λ X A B)

end Tensor

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local instance] etaleModuleExtensionByZero_preservesFiniteLimits
  etaleModuleExtensionByZero_preservesFiniteColimits
  etaleModuleRestriction_preservesFiniteLimits etaleModuleRestriction_preservesFiniteColimits

/-- **Extension by zero is left adjoint to the inverse image**, `j_! ⊣ j^{-1}`, on unbounded
derived categories. -/
def etaleDerivedExtensionByZeroAdj :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⊣
      etaleModuleDerivedInverseImage.{u, r} Λ j :=
  ((StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
      (etaleModuleExtensionByZeroAdj.{u, r} Λ j)).ofNatIsoLeft
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm).ofNatIsoRight
    (Dualizing.mapDerivedCategoryNatIso _ _ (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm)

/-- The unit `id ⟶ j^{-1}j_!` of `j_! ⊣ j^{-1}` on unbounded derived categories is an
isomorphism. -/
instance isIso_etaleDerivedExtensionByZeroAdj_unit :
    IsIso (etaleDerivedExtensionByZeroAdj.{u, r} Λ j).unit := by
  have h := StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_unit
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j) inferInstance
  let ff := ((StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j)).fullyFaithfulLOfIsIsoUnit).ofIso
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm
  have := ff.full
  have := ff.faithful
  infer_instance

/-- The adjoint triple `j_! ⊣ j^{-1} ⊣ Rj_*`. -/
def etaleDerivedOpenImmersionTriple :
    Adjunction.Triple (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j)
      (etaleModuleDerivedInverseImage.{u, r} Λ j)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j) :=
  ⟨etaleDerivedExtensionByZeroAdj.{u, r} Λ j, etaleModuleDerivedInverseImageAdj.{u, r} Λ j⟩

/-- **`j^{-1}Rj_* = id`** for an open immersion `j`, on `D(U_étale, Λ)`. -/
instance isIso_etaleDerivedInverseImageCounit :
    IsIso (etaleModuleDerivedInverseImageAdj.{u, r} Λ j).counit :=
  (etaleDerivedOpenImmersionTriple.{u, r} Λ j).isIso_unit_iff_isIso_counit.1
    (isIso_etaleDerivedExtensionByZeroAdj_unit.{u, r} Λ j)

/-- The projection map `j_!(j^{-1}L ⊗^L_Λ Z) ⟶ L ⊗^L_Λ j_!Z`. -/
abbrev etaleDerivedProjectionMap :=
  extensionProjectionMap (etaleDerivedExtensionByZeroAdj.{u, r} Λ j)
    (etaleDerivedTensor.{u, r} Λ X) (etaleDerivedTensor.{u, r} Λ U)
    (etaleDerivedInverseImageTensorIso.{u, r} Λ j)

/-- **The projection formula [Stacks, Tag 0GL1] for extension by zero along an open immersion**:
the projection map `j_!(j^{-1}L ⊗^L_Λ Z) ⟶ L ⊗^L_Λ j_!Z` is an isomorphism. -/
instance isIso_etaleDerivedProjectionMap_app_app (L : DerivedCategory (EtaleModules.{u, r} Λ X))
    (Z : DerivedCategory (EtaleModules.{u, r} Λ U)) :
    IsIso (((etaleDerivedProjectionMap.{u, r} Λ j).app L).app Z) := by
  let i := closedComplementι j
  have hij := range_eq_compl_range_closedComplementι j
  refine isIso_of_isIso_etaleModuleDerivedInverseImage Λ i j hij _ ?_ ?_
  · have hS := isZero_etaleModuleDerivedInverseImage_extensionByZero Λ i j hij
      (((etaleDerivedTensor.{u, r} Λ U).obj
        ((etaleModuleDerivedInverseImage.{u, r} Λ j).obj L)).obj Z)
    have hT : IsZero ((etaleModuleDerivedInverseImage.{u, r} Λ i).obj
        (((etaleDerivedTensor.{u, r} Λ X).obj L).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj Z))) :=
      (isZero_etaleDerivedTensor_obj_obj.{u, r} Λ _ _ _
        (isZero_etaleModuleDerivedInverseImage_extensionByZero Λ i j hij Z)).of_iso
        ((etaleDerivedInverseImageTensorIso.{u, r} Λ i).app
          (L, (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj Z))
    exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  · exact isIso_map_extensionProjectionMapApp (etaleDerivedExtensionByZeroAdj.{u, r} Λ j) _ _ _ L Z

/-- For fixed `L`, the projection map `j_!(j^{-1}L ⊗^L_Λ -) ⟶ L ⊗^L_Λ j_!(-)` is a natural
isomorphism. -/
instance isIso_etaleDerivedProjectionMap_app (L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    IsIso ((etaleDerivedProjectionMap.{u, r} Λ j).app L) :=
  NatIso.isIso_of_isIso_app _

/-- The projection map `j_!(j^{-1}L ⊗^L_Λ Z) ⟶ L ⊗^L_Λ j_!Z` is an isomorphism of
bifunctors. -/
instance isIso_etaleDerivedProjectionMap : IsIso (etaleDerivedProjectionMap.{u, r} Λ j) :=
  NatIso.isIso_of_isIso_app _

/-- **The projection formula [Stacks, Tag 0GL1]**, `j_!(j^{-1}L ⊗^L_Λ Z) ≅ L ⊗^L_Λ j_!Z`, as an
isomorphism of bifunctors. -/
def etaleDerivedProjectionIso :=
  asIso (etaleDerivedProjectionMap.{u, r} Λ j)

/-- **`Rj_*M ⊗^L_Λ j_!B ≅ j_!(M ⊗^L_Λ B)`**, as an isomorphism of bifunctors: the projection
formula at `L = Rj_*M`, followed by `j^{-1}Rj_*M = M`. -/
def etaleDerivedPushforwardProjectionIso :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j ⋙ etaleDerivedTensor.{u, r} Λ X) ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j) ≅
      etaleDerivedTensor.{u, r} Λ U ⋙
        (Functor.whiskeringRight _ _ _).obj
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j) :=
  (Functor.isoWhiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j)
      (etaleDerivedProjectionIso.{u, r} Λ j)).symm ≪≫
    Functor.isoWhiskerRight (asIso (etaleModuleDerivedInverseImageAdj.{u, r} Λ j).counit)
      (etaleDerivedTensor.{u, r} Λ U ⋙
        (Functor.whiskeringRight _ _ _).obj
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j)) ≪≫
    Functor.leftUnitor _

end OpenImmersion

end Stacks.EtaleCohomology

end
