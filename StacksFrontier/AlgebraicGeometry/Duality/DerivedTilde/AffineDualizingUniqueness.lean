module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.KFlat.ChosenResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.EvaluationTensorHomBijection
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
import StacksCore.Tactic.StacksAttribute

/-!
# Two dualizing complexes on an affine scheme differ by an invertible object

Let `R` be a Noetherian ring and let `ω`, `ω'` be dualizing complexes for `R` in the sense of
[Stacks, Tag 0A7B]. Their associated complexes of sheaves on `X = Spec R` differ by derived
tensoring with an invertible object of `D(𝒪_X)`: there is an invertible `L` with
`ω̃' ≅ ω̃ ⊗^L_{𝒪_X} L`, namely the associated complex of `RHom_R(ω, ω')`.

## Main definitions

* `Stacks.Duality.derivedTensorGeneralCompare`: the isomorphism between the values of any two
  derived tensor products of `R`-modules in the sense of [Stacks, Tag 0BYI] on a pair of objects.
* `Stacks.Duality.derivedTildeTensorIso` and `Stacks.Duality.derivedTildeUnitIso`: derived
  sheafification carries the monoidal structure of `D(R)` to that of `D(𝒪_{Spec R})` on objects
  and on the unit.
* `Stacks.Duality.derivedTildeEvaluationTensorMap`: the evaluation morphism
  `RHom_R(ω, ω') ⊗^L_R ω ⟶ ω'` carried to `D(𝒪_{Spec R})`.

## Main results

* `Stacks.Duality.isInvertible_obj_of_tensorIso`: a functor carrying tensor products and the
  unit to tensor products and the unit, objectwise, preserves invertible objects.
* `Stacks.Duality.exists_isInvertible_tensor_iso_derivedTilde`: the invertible object relating
  the complexes on `Spec R` associated to two dualizing complexes for `R`.
* `Stacks.Duality.isIso_derivedTildeEvaluationTensorMap_of_isDualizingComplex`: for dualizing
  complexes `ω`, `ω'` the evaluation morphism carried to `Spec R` is an isomorphism.

## References

* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor Opposite
open AlgebraicGeometry

universe u

open scoped AlgebraicGeometry.StandardDerivedModuleCat

attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace Stacks.Duality

/-! ### Transport of invertibility along a functor -/

/-- An invertible object of a monoidal category stays invertible under a functor which carries
tensor products to tensor products and the unit to the unit, objectwise. -/
theorem isInvertible_obj_of_tensorIso {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (t : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B) (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    {J : C} (hJ : MonoidalCategory.IsInvertible J) :
    MonoidalCategory.IsInvertible (F.obj J) := by
  obtain ⟨d⟩ := hJ
  exact ⟨{ inv := F.obj d.inv
           isoLeft := (t J d.inv).symm ≪≫ F.mapIso d.isoLeft ≪≫ e
           isoRight := (t d.inv J).symm ≪≫ F.mapIso d.isoRight ≪≫ e }⟩

/-! ### Comparing two derived tensor products of modules -/

/-- **Any two derived tensor products of `R`-modules agree on a pair of objects**: the
isomorphism between their values, through the total tensor complex of the chosen K-flat
resolutions of representatives of the two objects. -/
def derivedTensorGeneralCompare (A : Type u) [CommRing A]
    (T S : DerivedTensorProductGeneral.{u, u} A) (K L : DObj A) :
    (T.tensor.obj K).obj L ≅ (S.tensor.obj K).obj L := by
  let rK := CochainComplex.KFlat.chosenResolution.{u, u} (DerivedCategory.Q.objPreimage K)
  let rL := CochainComplex.KFlat.chosenResolution.{u, u} (DerivedCategory.Q.objPreimage L)
  haveI := rK.quasiIso
  haveI := rL.quasiIso
  let eK : DerivedCategory.Q.obj rK.complex ≅ K :=
    asIso (DerivedCategory.Q.map rK.π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eL : DerivedCategory.Q.obj rL.complex ≅ L :=
    asIso (DerivedCategory.Q.map rL.π) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  exact (T.tensor.mapIso eK.symm).app L ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj rK.complex)).mapIso eL.symm ≪≫
    T.comparison rK.complex rL.complex rK.kFlat rL.kFlat ≪≫
    (S.comparison rK.complex rL.complex rK.kFlat rL.kFlat).symm ≪≫
    (S.tensor.mapIso eK).app (DerivedCategory.Q.obj rL.complex) ≪≫
    (S.tensor.obj K).mapIso eL

/-! ### Derived sheafification is monoidal on objects -/

/-- **Derived sheafification carries the derived tensor product of `D(R)` to the derived tensor
product of `D(𝒪_{Spec R})`**: `(K ⊗^L_R L)~ ≅ K̃ ⊗^L_{𝒪_{Spec R}} L̃`, [Stacks, Tag 08DX]
part (2). -/
def derivedTildeTensorIso (R : CommRingCat.{u}) (K L : DObj (R : Type u)) :
    letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
    letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
      (specCommRingSheaf R)
    (tildeDS R).obj (K ⊗ L) ≅ (tildeDS R).obj K ⊗ (tildeDS R).obj L := by
  letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (specCommRingSheaf R)
  exact (tildeDS R).mapIso (((canonicalDerivedMonoidalTensorIso.{u, u} (R : Type u)).app K).app L
    ≪≫ derivedTensorGeneralCompare (R : Type u)
      (canonicalDerivedTensorProductGeneral.{u, u} (R : Type u))
      (canonicalDerivedTensorProduct (R : Type u)).toGeneral K L) ≪≫
    (affineDerivedTensorIso R K L).symm

/-- **Derived sheafification carries the unit of `D(R)` to the unit of `D(𝒪_{Spec R})`**: the
sheaf associated to `R` in degree zero is the structure sheaf in degree zero. -/
def derivedTildeUnitIso (R : CommRingCat.{u}) :
    letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
    letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
      (specCommRingSheaf R)
    (tildeDS R).obj (𝟙_ (DObj (R : Type u))) ≅ 𝟙_ (DerivedCategory (SpecModules R)) := by
  letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (specCommRingSheaf R)
  exact (tildeDS R).mapIso (canonicalDerivedMonoidalUnitIso.{u, u} (R : Type u) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (R : Type u)) 0).mapIso
        (ULift.moduleEquiv : ULift.{u} (R : Type u) ≃ₗ[(R : Type u)] (R : Type u)).toModuleIso) ≪≫
    ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of (R : Type u) R) ≪≫
    (DerivedCategory.singleFunctor (SpecModules R) 0).mapIso tildeSelf

/-! ### The affine case of Tag 0ATP -/

/-- **The affine case of [Stacks, Tag 0ATP].** Let `R` be a Noetherian ring and let `ω` and `ω'`
be dualizing complexes for `R`. The complexes of sheaves they define on `X = Spec R` differ by
derived tensoring with an invertible object of `D(𝒪_X)`: there is an invertible `L` with
`ω̃' ≅ ω̃ ⊗^L_{𝒪_X} L`, namely the complex associated to `RHom_R(ω, ω')`. -/
theorem exists_isInvertible_tensor_iso_derivedTilde (R : CommRingCat.{u}) [IsNoetherianRing R]
    {ω ω' : DObj (R : Type u)}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω') :
    letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
      (specCommRingSheaf R)
    ∃ L : DerivedCategory (SpecModules R), MonoidalCategory.IsInvertible L ∧
      Nonempty ((tildeDS R).obj ω' ≅ (tildeDS R).obj ω ⊗ L) := by
  let _ := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  let _ := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (specCommRingSheaf R)
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (R : Type u)
  let J := d.hom.obj (op ω, ω')
  refine ⟨(tildeDS R).obj J,
    isInvertible_obj_of_tensorIso (tildeDS R) (derivedTildeTensorIso R)
      (derivedTildeUnitIso R) (Dualizing.isInvertible_derivedHom.{u, u} (R : Type u) hω hω'),
    ⟨(tildeDS R).mapIso
        (Dualizing.dualizingIsoTensorDerivedHom.{u, u} (R : Type u) hω hω' ≪≫
          (Dualizing.monoidalTensorIso.{u, u} (R : Type u) ω J).symm) ≪≫
      derivedTildeTensorIso R ω J⟩⟩

/-! ### The evaluation morphism carried to `Spec R` -/

/-- **The evaluation morphism of two objects of `D(R)`, carried to `Spec R`.** Over the ring the
evaluation morphism is `Dualizing.evaluationTensorMap`,

`R𝐻om_R(ω, ω') ⊗^L_R ω ⟶ ω'`,

a morphism of the monoidal category `D(R)`. Derived sheafification carries the derived tensor
product of `D(R)` to that of `D(𝒪_{Spec R})` on objects
(`Stacks.Duality.derivedTildeTensorIso`), so the image of that morphism is a morphism

`(R𝐻om_R(ω, ω'))~ ⊗^L_{𝒪_{Spec R}} ω̃ ⟶ ω̃'`

of `D(𝒪_{Spec R})`. -/
def derivedTildeEvaluationTensorMap (R : CommRingCat.{u}) (ω ω' : DObj (R : Type u)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
      (specCommRingSheaf R)
    (tildeDS R).obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (R : Type u)).hom.obj
        (op ω, ω')) ⊗ (tildeDS R).obj ω ⟶ (tildeDS R).obj ω' :=
  letI := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (specCommRingSheaf R)
  (derivedTildeTensorIso R
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing (R : Type u)).hom.obj (op ω, ω'))
      ω).inv ≫
    (tildeDS R).map (Dualizing.evaluationTensorMap.{u, u} (A := (R : Type u)) ω ω')

/-- **The evaluation morphism of two dualizing complexes is an isomorphism on `Spec R`.** Let `R`
be a Noetherian ring and let `ω`, `ω'` be dualizing complexes for `R`. Then the image

`(R𝐻om_R(ω, ω'))~ ⊗^L_{𝒪_{Spec R}} ω̃ ⟶ ω̃'`

of the evaluation morphism `R𝐻om_R(ω, ω') ⊗^L_R ω ⟶ ω'` is an isomorphism of
`D(𝒪_{Spec R})`. -/
theorem isIso_derivedTildeEvaluationTensorMap_of_isDualizingComplex (R : CommRingCat.{u})
    [IsNoetherianRing R] {ω ω' : DObj (R : Type u)}
    (hω : Dualizing.IsDualizingComplex ω) (hω' : Dualizing.IsDualizingComplex ω') :
    IsIso (derivedTildeEvaluationTensorMap R ω ω') := by
  let := canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (specCommRingSheaf R)
  have : IsIso (Dualizing.evaluationTensorMap.{u, u} (A := (R : Type u)) ω ω') :=
    Dualizing.isIso_evaluationTensorMap_of_isDualizingComplex.{u, u} ω ω' hω hω'
  change IsIso (_ ≫ _)
  infer_instance

end Stacks.Duality

end
