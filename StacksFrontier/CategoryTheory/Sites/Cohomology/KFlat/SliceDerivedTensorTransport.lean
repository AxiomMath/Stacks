module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SliceRestrictionKFlat
public import StacksFrontier.Homology.KFlat.BifunctorTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product commutes with restriction to a slice site, on arbitrary objects

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction of sheaves of modules to
the localized site `C/U` — Mathlib's `SheafOfModules.overFunctor`, which is
`Stacks.DerivedTensor.ExtensionByZero.restriction` — is exact, carries `⊗_O` to `⊗_{O|_U}`
(`Stacks.SheafOfModules.TensorPower.overTensorSheafIso`) and preserves K-flatness in both
variables (`Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`, [Stacks, Tag 0E8K],
and `kFlatLeft_restrictionComplex`). Therefore

`(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U`

as an isomorphism of **bifunctors on the unbounded derived categories**: on arbitrary objects
`K`, `L` of `D(O)` and natural in both of them. That is
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionNatIso`.

## Main definitions

* `Stacks.Cohomology.SliceDerivedTensor.sliceTensorIso`: the underived comparison
  `(M ⊗_O L)|_U ≅ M|_U ⊗_{O|_U} L|_U`, at the spelling of the tensor product of a ringed site.
* `Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionNatIso`: the comparison on the
  derived categories, as an isomorphism of bifunctors.
* `Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionObjIso`: its value at a pair of
  objects.

## Main results

* `Stacks.Cohomology.SliceDerivedTensor.sliceTensorIso_naturality_left` and `_right`: the
  underived comparison is natural in each variable separately.
* `Stacks.Cohomology.SliceDerivedTensor.restriction_preservesAntidiagonalCoproducts`:
  restriction to a slice preserves the coproducts occurring in a total complex.

## Implementation notes

`Stacks.SheafOfModules.TensorPower.overTensorSheafIso` is stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`, which has the same underlying
presheaf of rings as `Stacks.SheafOfModules.Tensor.ringSheaf`; with
`Stacks.Cohomology.SliceDerivedTensor.siteIsSheaf` for `hO`, `restriction X U` is
`whiskerRestriction X.O.obj (siteIsSheaf X) (Over.forget U)` by `rfl`. The identity factors left
by the naturality lemma of the tensor-power development are not removed by conversion, and are
rewritten away in `sliceTensorIso_naturality_left` and `sliceTensorIso_naturality_right`.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 079U)](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.ExtensionByZero
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction restrictionComplex)
open Stacks.SheafOfModules.TensorPower (whiskerTensorSheafIso_naturality overTensorSheafIso)

universe d u

namespace Stacks.Cohomology.SliceDerivedTensor

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The underived comparison -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sheaf condition of the structure sheaf of a ringed site, stated for the presheaf of
not-necessarily-commutative rings that
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` indexes by. -/
theorem siteIsSheaf :
    Presheaf.IsSheaf X.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O).property

/-- **`(M ⊗_O L)|_U ≅ M|_U ⊗_{O|_U} L|_U`** for restriction to the slice site `C/U`:
`Stacks.SheafOfModules.TensorPower.overTensorSheafIso`, at the restriction functor and the tensor
product of a ringed site. -/
abbrev sliceTensorIso (M L : Modules X.O) :
    (restriction X U).obj (((sheafTensor X.O).obj M).obj L) ≅
      ((sheafTensor (X.O.over U)).obj ((restriction X U).obj M)).obj
        ((restriction X U).obj L) :=
  overTensorSheafIso X.O.obj (siteIsSheaf X) U M L

/-- Joint naturality of `sliceTensorIso` in both variables, with the identity factors of
`whiskerTensorSheafIso_naturality` left in place. -/
private theorem sliceTensorIso_naturality {M M' L L' : Modules X.O} (f : M ⟶ M') (g : L ⟶ L') :
    (restriction X U).map (((sheafTensor X.O).map f).app L ≫
          ((sheafTensor X.O).obj M').map g) ≫
        (sliceTensorIso X U M' L').hom =
      (sliceTensorIso X U M L).hom ≫
        (((sheafTensor (X.O.over U)).map ((restriction X U).map f)).app
            ((restriction X U).obj L) ≫
          ((sheafTensor (X.O.over U)).obj ((restriction X U).obj M')).map
            ((restriction X U).map g)) :=
  whiskerTensorSheafIso_naturality (J' := X.J.over U) X.O.obj (siteIsSheaf X)
    (Over.forget U) f g

/-- **The comparison `Stacks.Cohomology.SliceDerivedTensor.sliceTensorIso` is natural in the
first variable.** -/
theorem sliceTensorIso_naturality_left {M M' : Modules X.O} (f : M ⟶ M') (L : Modules X.O) :
    (restriction X U).map (((sheafTensor X.O).map f).app L) ≫
        (sliceTensorIso X U M' L).hom =
      (sliceTensorIso X U M L).hom ≫
        ((sheafTensor (X.O.over U)).map ((restriction X U).map f)).app
          ((restriction X U).obj L) := by
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    sliceTensorIso_naturality X U f (𝟙 L)

/-- **The comparison `Stacks.Cohomology.SliceDerivedTensor.sliceTensorIso` is natural in the
second variable.** -/
theorem sliceTensorIso_naturality_right (M : Modules X.O) {L L' : Modules X.O} (g : L ⟶ L') :
    (restriction X U).map (((sheafTensor X.O).obj M).map g) ≫
        (sliceTensorIso X U M L').hom =
      (sliceTensorIso X U M L).hom ≫
        ((sheafTensor (X.O.over U)).obj ((restriction X U).obj M)).map
          ((restriction X U).map g) := by
  simpa only [CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
    Category.id_comp] using
    sliceTensorIso_naturality X U (𝟙 M) g

/-! ### The colimits restriction to a slice preserves -/

/-- Restriction to a slice preserves colimits of diagrams indexed by a category in `Type 0`. -/
@[sga "4 IV 11.2.2" "partial"]
lemma restriction_preservesColimitsOfSize_zero :
    PreservesColimitsOfSize.{0, 0} (restriction X U) :=
  have _h : PreservesColimitsOfSize.{u, u} (restriction X U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O).over U))
  preservesColimitsOfSize_shrink _

/-- **Restriction to a slice preserves the coproducts occurring in the total complex of a
double cochain complex over `ℤ`**: those indexed by an antidiagonal
`ComplexShape.π (up ℤ) (up ℤ) (up ℤ) ⁻¹' {n}`. -/
lemma restriction_preservesAntidiagonalCoproducts (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (restriction X U) :=
  let := restriction_preservesColimitsOfSize_zero X U
  inferInstance

/-! ### The comparison on the derived categories -/

section Tensor

variable
  [(sheafTensor X.O).Additive]
  [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive]
  [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]

/-- **The restriction of the tensor double complex of `K` and `L` has a total complex.** -/
instance hasTotal_mapBicomplex_restriction (K L : CochainComplex (Modules X.O) ℤ) :
    HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.mapBicomplex (restriction X U)
        ((((sheafTensor X.O).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso
    (Functor.mapBifunctorBicomplexIso (sheafTensor X.O) (sheafTensor (X.O.over U))
      (restriction X U) (restriction X U) (restriction X U)
      (sliceTensorIso X U) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (fun f N => sliceTensorIso_naturality_left X U f N)
      (fun M {_ _} g => sliceTensorIso_naturality_right X U M g) K L).symm
    (ComplexShape.up ℤ)

section Derived

variable [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- **The derived tensor product commutes with restriction to the slice site `C/U`, on
arbitrary objects of `D(O)` and naturally in both variables:**

`(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U`. -/
def derivedTensorRestrictionNatIso :
    CochainComplex.KFlatBifunctor.derivedTransportSource (sheafTensor X.O)
        (restriction X U) ≅
      CochainComplex.KFlatBifunctor.derivedTransportTarget (sheafTensor (X.O.over U))
        (restriction X U) (restriction X U) :=
  letI := fun n : ℤ => restriction_preservesAntidiagonalCoproducts X U n
  CochainComplex.KFlatBifunctor.derivedTransportIso (sheafTensor X.O)
    (sheafTensor (X.O.over U)) (restriction X U) (restriction X U) (restriction X U)
    (sliceTensorIso X U)
    (fun f L => sliceTensorIso_naturality_left X U f L)
    (fun M {_ _} g => sliceTensorIso_naturality_right X U M g)
    (fun K hK => Stacks.DerivedTensor.ExtensionByZero.kFlatLeft_restrictionComplex X U K hK)
    (fun L hL => Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U L hL)

/-- **`(K ⊗^𝐋_O L)|_U ≅ K|_U ⊗^𝐋_{O|_U} L|_U`** at a pair of objects of `D(O)`, read off
`Stacks.Cohomology.SliceDerivedTensor.derivedTensorRestrictionNatIso`. -/
def derivedTensorRestrictionObjIso (K L : DerivedCategory (Modules X.O)) :
    (restriction X U).mapDerivedCategory.obj
        (((CochainComplex.KFlatBifunctor.derivedBifunctor (sheafTensor X.O)).obj K).obj L) ≅
      ((CochainComplex.KFlatBifunctor.derivedBifunctor
            (sheafTensor (X.O.over U))).obj
          ((restriction X U).mapDerivedCategory.obj K)).obj
        ((restriction X U).mapDerivedCategory.obj L) :=
  ((derivedTensorRestrictionNatIso X U).app K).app L

end Derived

end Tensor

end Stacks.Cohomology.SliceDerivedTensor

end
