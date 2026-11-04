module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex

/-!
# The map of first vertices of the fundamental triangle is the intrinsic one

Let `k : A₁ ⟶ A₂`, `g : A₂ ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings
on a site. The map of first vertices `L_{B/A₁} ⊗_B D ⟶ L_{B/A₂} ⊗_B D` of the towers
`A₁ ⟶ B ⟶ D` and `A₂ ⟶ B ⟶ D`, `CategoryTheory.Sheaf.baseChangedCotangentBaseMap`, is defined
through the identifications of Tag 08SX with the sheafified sectionwise complexes. This file
states that it is the degreewise extension of scalars along `h` of the change-of-base map
`L_{B/A₁} ⟶ L_{B/A₂}` of Tag 08SZ.

## Main definitions

* `CategoryTheory.Sheaf.BaseChangedCotangentBaseMapIntrinsic`: the statement that
  `baseChangedCotangentBaseMap J k g h` is `towerCotangentChangeOfBase J k g ⊗_B D`, read through
  `towerExtendScalarsCotangentComplexIso`.

## Main results

* `CategoryTheory.Sheaf.baseChangedCotangentBaseMapIntrinsic`: that statement holds. The
  identification of Tag 08SX for `A ⟶ B ⟶ D` is the change of rings of that for `A ⟶ B`, read
  through `towerExtendScalarsCotangentComplexIso`, and the latter commutes with change of base
  (`sheafification_map_sectionwiseTowerChangeOfBaseMap_f`).

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ B D : Sheaf J CommRingCat.{max u v w}} (k : A₁ ⟶ A₂) (g : A₂ ⟶ B) (h : B ⟶ D)

/-- **The map of first vertices is the intrinsic one**: the map
`L_{B/A₁} ⊗_B D ⟶ L_{B/A₂} ⊗_B D` of `baseChangedCotangentBaseMap`, defined through Tag 08SX, is
the degreewise extension of scalars along `h` of the change-of-base map `L_{B/A₁} ⟶ L_{B/A₂}`,
read through `towerExtendScalarsCotangentComplexIso`. -/
def BaseChangedCotangentBaseMapIntrinsic : Prop :=
  baseChangedCotangentBaseMap.{u, v, w} J k g h =
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J (k ≫ g) h).inv ≫
      ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (towerCotangentChangeOfBase.{u, v, w} J k g) ≫
      (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom

variable {J} in
/-- In every degree the identification of Tag 08SX for the first vertex is the commutation of
change of rings with sheafification, followed by the extension of scalars of the identification
for `A ⟶ B` and by `towerExtendScalarsCotangentComplexIso`. -/
theorem sheafifiedSectionwiseBaseChangedCotangentComplexIso_hom_f
    {A : Sheaf J CommRingCat.{max u v w}} (g' : A ⟶ B) (j : ℤ) :
    (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g' h).hom.f j =
      (towerSheafifyChangeOfRingsIso J h).hom.app ((sectionwiseCotangentModuleComplex J g').X j) ≫
        (towerExtendScalars.{u, v, w} J h).map
          ((sheafifiedSectionwiseCotangentModuleComplexIso J g').hom.f j) ≫
        (towerExtendScalarsCotangentComplexIso.{u, v, w} J g' h).hom.f j :=
  congrArg (_ ≫ ·) (Category.id_comp _)

/-- **The map of first vertices is the intrinsic one.** -/
theorem baseChangedCotangentBaseMapIntrinsic :
    BaseChangedCotangentBaseMapIntrinsic.{u, v, w} J k g h := by
  unfold BaseChangedCotangentBaseMapIntrinsic baseChangedCotangentBaseMap
  rw [Iso.inv_comp_eq]
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  have hn := (towerSheafifyChangeOfRingsIso J h).hom.naturality
    ((sectionwiseTowerChangeOfBaseMap J k g).f j)
  have hs := sheafification_map_sectionwiseTowerChangeOfBaseMap_f J k g j
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    sheafifiedSectionwiseBaseChangedCotangentComplexIso_hom_f]
  have hT := HomologicalComplex.congr_hom
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J (k ≫ g) h).hom_inv_id j
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hT
  simp only [Functor.comp_map] at hn
  refine ((reassoc_of% hn) _).trans ?_
  rw [← Functor.map_comp_assoc, hs, Functor.map_comp_assoc]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  exact ((reassoc_of% hT) _).symm

end CategoryTheory.Sheaf

end
