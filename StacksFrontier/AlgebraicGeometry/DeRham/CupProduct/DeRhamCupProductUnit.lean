module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductLaws

/-!
# The unit of the cup product on de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. The class `1 ∈ H^0_{dR}` of the global section `1` of `Ω^0`
is a two-sided unit for the cup product of Section 50.4: `1 ∪ η = η = η ∪ 1`.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_one_left`: `1 ∪ η = η`.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_one_right`: `η ∪ 1 = η`.

Both are stated with the product transported from degree `0 + m`, respectively `m + 0`, to
degree `m`.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.Cohomology.RealizationShift

variable {C : Type*} [Category* C] [HasShift C ℤ] {B : Type*} [Category* B] [Abelian B]
  [HasDerivedCategory B] (F : C ⥤ DerivedCategory B) [F.CommShift ℤ]

/-- In every degree `m`, the map induced on `Hᵐ(F(-))` by the identity `X ⟶ X[0]`, read through
`Hᵐ(F(X[0])) = Hᵐ(F X)`, is the identity. -/
theorem homologyMap_mk₀_id_shiftHomologyIsoU_of_degree (X : C) (m : ℤ) :
    (DerivedCategory.homologyFunctor B m).map (F.map (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X))) ≫
        (shiftHomologyIsoU F X 0 m m (zero_add m)).hom = 𝟙 _ := by
  rw [shiftHomologyIsoU_zero_hom, ← Functor.map_comp, ← Functor.map_comp]
  simp [ShiftedHom.mk₀, shiftFunctorZero']

end Stacks.Cohomology.RealizationShift

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- Transporting along two equalities of degrees is transporting along their composite. -/
@[simp]
theorem reindexDeRhamCohomology_reindexDeRhamCohomology {l m n : ℤ} (h : l = m) (h' : m = n)
    (x : deRhamCohomology B D l) :
    reindexDeRhamCohomology B D h' (reindexDeRhamCohomology B D h x) =
      reindexDeRhamCohomology B D (h.trans h') x := by
  subst h h'
  rfl

/-- Transporting along an equality of degrees is additive. -/
theorem reindexDeRhamCohomology_add {m n : ℤ} (h : m = n) (x y : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h (x + y) =
      reindexDeRhamCohomology B D h x + reindexDeRhamCohomology B D h y := by
  subst h
  rfl

/-- Transporting along an equality of degrees commutes with the scalar action of `ℤ`. -/
theorem reindexDeRhamCohomology_zsmul {m n : ℤ} (h : m = n) (c : ℤ) (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h (c • x) = c • reindexDeRhamCohomology B D h x := by
  subst h
  rfl

/-- The identification `H^m(X, Ω^•[0]) = H^k_{dR}` for `0 + m = k`, read in degree `m` after
transport. -/
theorem reindexDeRhamCohomology_deRhamShiftHomologyIso_zero {m k : ℤ} (h : 0 + m = k) (e : k = m)
    (y : (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) m).obj
      ((derivedSectionsBase A).obj ((deRhamDerivedObject B D)⟦(0 : ℤ)⟧))) :
    reindexDeRhamCohomology B D e ((deRhamShiftHomologyIso B D 0 m k h).hom y) =
      (deRhamShiftHomologyIso B D 0 m m (zero_add m)).hom y := by
  subst e
  rfl

/-- The morphism `Ω^• ⟶ Ω^•[0]` attached to the unit induces, through
`H^m(X, Ω^•[0]) = H^m_{dR}`, the identity of `H^m_{dR}`. -/
theorem deRhamShiftHomologyIso_homologyMap_mk₀_id (m : ℤ) (η : deRhamCohomology B D m) :
    (deRhamShiftHomologyIso B D 0 m m (zero_add m)).hom
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) m).map
          ((derivedSectionsBase A).map
            (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (deRhamDerivedObject B D)))) η) =
      η :=
  ConcreteCategory.congr_hom
    (Stacks.Cohomology.RealizationShift.homologyMap_mk₀_id_shiftHomologyIsoU_of_degree
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤)
      (deRhamDerivedObject (X := X) (A := A) (φ := φ) B D) m) η

/-- The unit is a left unit for the cup product: `1 ∪ η = η` for `η ∈ H^m_{dR}`, the product
read in degree `m`. -/
theorem deRhamCohomologyCup_one_left (m : ℤ) (η : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D (zero_add m)
        (deRhamCohomologyCup B D 0 m (deRhamOneClass B D) η) = η := by
  rw [deRhamCohomologyCup_eq_deRhamClassMorphism, deRhamClassMorphism_one,
    reindexDeRhamCohomology_deRhamShiftHomologyIso_zero]
  exact deRhamShiftHomologyIso_homologyMap_mk₀_id B D m η

/-- The unit is a right unit for the cup product: `η ∪ 1 = η` for `η ∈ H^m_{dR}`, the product
read in degree `m`. -/
theorem deRhamCohomologyCup_one_right (m : ℤ) (η : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D (add_zero m)
        (deRhamCohomologyCup B D m 0 η (deRhamOneClass B D)) = η := by
  rw [deRhamCohomologyCup_comm, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul,
    reindexDeRhamCohomology_reindexDeRhamCohomology]
  exact deRhamCohomologyCup_one_left B D m η

end AlgebraicGeometry.SheafOfModules
