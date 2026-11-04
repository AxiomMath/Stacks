module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingHomothety
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingUniqueness
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation morphism of two dualizing complexes on an affine scheme

Let `R` be a Noetherian ring, `X = Spec R`, and let `ω`, `ω'` be dualizing complexes for `R`. The
evaluation morphism

`e_{ω̃, ω̃'} : R𝓗om_{𝒪_X}(ω̃, ω̃') ⊗^L_{𝒪_X} ω̃ ⟶ ω̃'`

is an isomorphism, and `ω̃' ≅ ω̃ ⊗^L_{𝒪_X} L` for an invertible object `L` of `D(𝒪_X)`. On the
way, the derived tensor product of the complexes of sheaves associated to `M, K ∈ D(R)` is
identified with the complex associated to `M ⊗^L_R K`, at the standard model
`CategoryTheory.HasDerivedCategory.standard` of the derived category.

## Main definitions

* `AlgebraicGeometry.affineDerivedTensorIsoStandard`:
  `M̃ ⊗^L_{𝒪_{Spec R}} K̃ ≅ (M ⊗^L_R K)~`, at the standard model.
* `Stacks.Duality.derivedTildeTensorIsoStandard` and
  `Stacks.Duality.derivedTildeUnitIsoStandard`: derived sheafification carries the tensor product
  and the unit of `D(R)` to those of `D(𝒪_{Spec R})`, at the standard model.

## Main results

* `Stacks.Duality.exists_isInvertible_tensor_iso_derivedTildeStandard`: there is an invertible
  object `L` of `D(𝒪_X)` with `ω̃ ⊗^L_{𝒪_X} L ≅ ω̃'`.
* `Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde_pair`: the evaluation morphism
  `e_{ω̃, ω̃'}` is an isomorphism.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules
open CochainComplex.DerivedTensor

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-! ### The comparison on K-flat complexes -/

/-- For K-flat complexes `P^•` and `P'^•` of `R`-modules, the derived tensor product of the
associated complexes of sheaves on `Spec R` is the complex associated to the derived tensor
product of `P^•` and `P'^•` over `R`, at the standard model. -/
def affineDerivedTensorIsoOfKFlatStandard
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P') :
    ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.obj
          ((Stacks.Duality.derivedTildeStructureSheafModules R).obj
            (DerivedCategory.Q.obj P))).obj
        ((Stacks.Duality.derivedTildeStructureSheafModules R).obj
          (DerivedCategory.Q.obj P')) ≅
      (Stacks.Duality.derivedTildeStructureSheafModules R).obj
        (((canonicalDerivedTensorProduct (R : Type u)).tensor.obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj P')) :=
  ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P)).app _ ≪≫
    ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.obj
        (DerivedCategory.Q.obj (tildeComplexMod (A := R) P))).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P') ≪≫
    (derivedTensorAsSiteDatum (Spec R).sheaf).comparison _ _
      (kFlat_tilde P hP) (kFlat_tilde P' hP') ≪≫
    DerivedCategory.Q.mapIso (affineTensorComplexIso R P P').1.symm ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app (P ⊗ P')).symm ≪≫
    (Stacks.Duality.derivedTildeStructureSheafModules R).mapIso
      ((canonicalDerivedTensorProduct (R : Type u)).comparison P P' hP hP').symm

/-- A K-flat complex of `R`-modules representing an object `M` of `D(R)`, together with the
isomorphism between its image in `D(R)` and `M`. -/
def kFlatRepresentativeStandard (M : DerivedCategory (ModuleCat.{u} R)) :
    Σ' P : CochainComplex (ModuleCat.{u} R) ℤ,
      PProd (CochainComplex.KFlat.{u, u} P) (DerivedCategory.Q.obj P ≅ M) :=
  let C := DerivedCategory.Q.objPreimage M
  let res := CochainComplex.KFlat.chosenResolution.{u, u} C
  ⟨res.complex, ⟨res.kFlat,
    haveI := res.quasiIso
    (asIso (DerivedCategory.Q.map res.π)) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

/-! ### The comparison on arbitrary objects -/

/-- On the spectrum of a commutative ring `R`, the derived tensor product of the complexes of
sheaves of modules associated to `M` and `K` is the complex associated to their derived tensor
product over `R`, at the standard model:

`M̃^• ⊗^L_{𝒪_{Spec R}} K̃^•  ≅  (M^• ⊗^L_R K^•)~`. -/
@[stacks 08DX "part (2): the affine comparison, at the standard model"]
def affineDerivedTensorIsoStandard (M K : DerivedCategory (ModuleCat.{u} R)) :
    ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.obj
          ((Stacks.Duality.derivedTildeStructureSheafModules R).obj M)).obj
        ((Stacks.Duality.derivedTildeStructureSheafModules R).obj K) ≅
      (Stacks.Duality.derivedTildeStructureSheafModules R).obj
        (((canonicalDerivedTensorProduct (R : Type u)).tensor.obj M).obj K) :=
  let rP := kFlatRepresentativeStandard R M
  let rK := kFlatRepresentativeStandard R K
  ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.mapIso
      ((Stacks.Duality.derivedTildeStructureSheafModules R).mapIso rP.2.2.symm)).app _ ≪≫
    ((derivedTensorAsSiteDatum (Spec R).sheaf).tensor.obj
        ((Stacks.Duality.derivedTildeStructureSheafModules R).obj
          (DerivedCategory.Q.obj rP.1))).mapIso
      ((Stacks.Duality.derivedTildeStructureSheafModules R).mapIso rK.2.2.symm) ≪≫
    affineDerivedTensorIsoOfKFlatStandard R rP.1 rK.1 rP.2.1 rK.2.1 ≪≫
    (Stacks.Duality.derivedTildeStructureSheafModules R).mapIso
      (((canonicalDerivedTensorProduct (R : Type u)).tensor.mapIso rP.2.2).app _ ≪≫
        ((canonicalDerivedTensorProduct (R : Type u)).tensor.obj M).mapIso rK.2.2)

end AlgebraicGeometry

namespace Stacks.Duality

variable (R : CommRingCat.{u})
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-! ### Derived sheafification is monoidal on objects, at the standard model -/

/-- Derived sheafification carries the derived tensor product of `D(R)` to the derived tensor
product of `D(𝒪_{Spec R})`, at the standard model. -/
def derivedTildeTensorIsoStandard (K L : DObj (R : Type u)) :
    letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
    letI := derivedMonoidalStructure (Spec R).sheaf
    (derivedTildeStructureSheafModules R).obj (K ⊗ L) ≅
      (derivedTildeStructureSheafModules R).obj K ⊗
        (derivedTildeStructureSheafModules R).obj L := by
  letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  letI := derivedMonoidalStructure (Spec R).sheaf
  exact (derivedTildeStructureSheafModules R).mapIso
      (((canonicalDerivedMonoidalTensorIso.{u, u} (R : Type u)).app K).app L ≪≫
        derivedTensorGeneralCompare (R : Type u)
          (canonicalDerivedTensorProductGeneral.{u, u} (R : Type u))
          (canonicalDerivedTensorProduct (R : Type u)).toGeneral K L) ≪≫
    (affineDerivedTensorIsoStandard R K L).symm

/-- Derived sheafification carries the unit of `D(R)` to the unit of `D(𝒪_{Spec R})`, at the
standard model. -/
def derivedTildeUnitIsoStandard :
    letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
    letI := derivedMonoidalStructure (Spec R).sheaf
    (derivedTildeStructureSheafModules R).obj (𝟙_ (DObj (R : Type u))) ≅
      𝟙_ (DerivedCategory (StructureSheafModules (Spec R).sheaf)) := by
  letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  letI := derivedMonoidalStructure (Spec R).sheaf
  exact (derivedTildeStructureSheafModules R).mapIso
      (canonicalDerivedMonoidalUnitIso.{u, u} (R : Type u) ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (R : Type u)) 0).mapIso
          (ULift.moduleEquiv :
            ULift.{u} (R : Type u) ≃ₗ[(R : Type u)] (R : Type u)).toModuleIso) ≪≫
    ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of (R : Type u) R) ≪≫
    (DerivedCategory.singleFunctor (StructureSheafModules (Spec R).sheaf) 0).mapIso tildeSelf

/-! ### Invertibility of the difference of two dualizing complexes -/

/-- Let `R` be a Noetherian ring and let `ω` and `ω'` be dualizing complexes for `R`. Then there
is an invertible object `L` of `D(𝒪_X)` on `X = Spec R` with `ω̃ ⊗^L_{𝒪_X} L ≅ ω̃'`, at the
standard model. -/
theorem exists_isInvertible_tensor_iso_derivedTildeStandard [IsNoetherianRing R]
    {ω ω' : DObj (R : Type u)}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω') :
    letI := derivedMonoidalStructure (Spec R).sheaf
    ∃ L : DerivedCategory (StructureSheafModules (Spec R).sheaf),
      MonoidalCategory.IsInvertible L ∧
        Nonempty ((derivedTildeStructureSheafModules R).obj ω ⊗ L ≅
          (derivedTildeStructureSheafModules R).obj ω') := by
  let := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  let := derivedMonoidalStructure (Spec R).sheaf
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (R : Type u)
  let J := d.hom.obj (op ω, ω')
  refine ⟨(derivedTildeStructureSheafModules R).obj J,
    isInvertible_obj_of_tensorIso (derivedTildeStructureSheafModules R)
      (derivedTildeTensorIsoStandard R) (derivedTildeUnitIsoStandard R)
      (Dualizing.isInvertible_derivedHom.{u, u} (R : Type u) hω hω'),
    ⟨(derivedTildeTensorIsoStandard R ω J).symm ≪≫
      (derivedTildeStructureSheafModules R).mapIso
        (Dualizing.monoidalTensorIso.{u, u} (R : Type u) ω J ≪≫
          (Dualizing.dualizingIsoTensorDerivedHom.{u, u} (R : Type u) hω hω').symm)⟩⟩

/-! ### The evaluation hypothesis at a general pair -/

/-- Let `R` be a Noetherian ring and let `ω`, `ω'` be dualizing complexes for `R`. Then the
evaluation morphism

`e_{ω̃, ω̃'} : R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃') ⊗^L_{𝒪_{Spec R}} ω̃ ⟶ ω̃'`

is an isomorphism. -/
theorem isIso_derivedSheafHomCounit_derivedTilde_pair [IsNoetherianRing R]
    {ω ω' : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω') :
    IsIso (derivedSheafHomCounit (Spec R).sheaf
      ((derivedTildeStructureSheafModules R).obj ω)
      ((derivedTildeStructureSheafModules R).obj ω')) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_isInvertible_tensor_iso_derivedTildeStandard R hω hω'
  exact isIso_derivedSheafHomCounit_derivedTilde R hω _ hL e

end Stacks.Duality

end
