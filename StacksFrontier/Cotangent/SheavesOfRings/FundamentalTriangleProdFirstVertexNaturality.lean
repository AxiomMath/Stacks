module

public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentBaseMapIntrinsic
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveMapConormal
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleThirdVertexNaturality

/-!
# Naturality in the base ring of the product-graph reduction of the fundamental triangle

Let `k : A₁ ⟶ A₂`, `g : A₂ ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings
on a site. The connecting morphism `CategoryTheory.Sheaf.towerConnecting` of Tag 08SZ is obtained
from the tower `A ⟶ B ⟶ B × D` through the second summand functor and the identification
`towerProdFirstVertexIso` of first vertices. This file proves that this identification is
compatible with change of base along `k` (`CategoryTheory.Sheaf.TowerProdFirstVertexNatural`),
and, together with `CategoryTheory.Sheaf.towerThirdVertexNatural`, that the connecting morphism
is natural in the base ring.

## Main results

* `CategoryTheory.Sheaf.baseChangedCotangentBaseMap_f`: in degree `-n` the map of first vertices
  is the extension of scalars of the change-of-base map of cotangent terms.
* `CategoryTheory.Sheaf.prodGraphBaseChangedIso_naturality`: the identification
  `prodGraphBaseChangedIso` of first vertices commutes with the maps of first vertices.
* `CategoryTheory.Sheaf.towerProdFirstVertexNatural`: `TowerProdFirstVertexNatural J k g h`.
* `CategoryTheory.Sheaf.towerConnecting_naturality_baseChange`: **the connecting morphism of the
  fundamental triangle is natural in the base ring**.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite Simplicial

namespace CategoryTheory.Sheaf

universe t u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ B D : Sheaf J CommRingCat.{max u v w}} (k : A₁ ⟶ A₂) (g : A₂ ⟶ B) (h : B ⟶ D)

/-- The change-of-base map `L_{B/A₁} ⟶ L_{B/A₂}` in degree `-n`, read through the degree
isomorphisms on the terms of the cotangent simplicial modules. -/
def cotangentChangeOfBaseTerm (n : ℕ) :
    (cotangentSimplicialModule.{u, v, w} J (k ≫ g)).object.obj (op ⦋n⦌) ⟶
      (cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌) :=
  (cotangentComplex_degreeIso.{u, v, w} J (k ≫ g) n).inv ≫
    (towerCotangentChangeOfBase.{u, v, w} J k g).f (-(n : ℤ)) ≫
      (cotangentComplex_degreeIso.{u, v, w} J g n).hom

/-- **The map of first vertices in degree `-n`**: the extension of scalars along `h` of the
change-of-base map of the degree-`n` terms of the cotangent simplicial modules, read through the
degree isomorphisms of the first vertices. -/
theorem baseChangedCotangentBaseMap_f (n : ℕ) :
    (baseChangedCotangentBaseMap.{u, v, w} J k g h).f (-(n : ℤ)) =
      (baseChangedCotangentComplex_degreeIso.{u, v, w} J (k ≫ g) h n).hom ≫
        (towerExtendScalars.{u, v, w} J h).map (cotangentChangeOfBaseTerm.{u, v, w} J k g n) ≫
          (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).inv := by
  have e := HomologicalComplex.congr_hom
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J (k ≫ g) h).inv_hom_id (-(n : ℤ))
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    towerExtendScalarsCotangentComplexIso_hom_f] at e
  have hinv := (Iso.comp_hom_eq_id ((towerExtendScalars.{u, v, w} J h).mapIso
    (cotangentComplex_degreeIso.{u, v, w} J (k ≫ g) n) ≪≫
      (baseChangedCotangentComplex_degreeIso.{u, v, w} J (k ≫ g) h n).symm)).1 e
  rw [baseChangedCotangentBaseMapIntrinsic.{u, v, w} J k g h, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, towerExtendScalarsCotangentComplexIso_hom_f, hinv,
    Functor.mapHomologicalComplex_map_f]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
    cotangentChangeOfBaseTerm]

/-- **The identification of first vertices of the product-graph reduction commutes with change of
base**: the second summand of the map of first vertices of the towers `Aᵢ ⟶ B ⟶ B × D` is,
through `prodGraphBaseChangedIso`, the map of first vertices of the towers `Aᵢ ⟶ B ⟶ D`. -/
theorem prodGraphBaseChangedIso_naturality :
    (prodSndSummandComplex.{u, v, w} J (B := B) (D := D)).map
        (baseChangedCotangentBaseMap.{u, v, w} J k g (prodGraph J h)) ≫
      (prodGraphBaseChangedIso J g h).hom =
    (prodGraphBaseChangedIso J (k ≫ g) h).hom ≫ baseChangedCotangentBaseMap.{u, v, w} J k g h := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  by_cases hj : 0 < j
  · exact ((prodSndSummand.{u, v, w} J (B := B) (D := D)).map_isZero
      (baseChangedCotangentComplex_isZero_pos.{u, v, w} J (k ≫ g) (prodGraph J h) j hj)).eq_of_src
        _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
  have hnat := (prodGraphSummandIso J h).hom.naturality
    (cotangentChangeOfBaseTerm.{u, v, w} J k g n)
  simp only [Functor.comp_map] at hnat
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    baseChangedCotangentBaseMap_f, prodGraphBaseChangedIso_hom_f, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc, reassoc_of% hnat]

/-- **The first-vertex identifications of the product-graph reduction are compatible with change
of base**: `TowerProdFirstVertexNatural J k g h` holds. -/
theorem towerProdFirstVertexNatural [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)] :
    TowerProdFirstVertexNatural.{t, u, v, w} J k g h := by
  -- `TowerProdFirstVertexNatural` is stated in the standard model of `D(B × D)`.
  let := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  have H := prodGraphBaseChangedIso_naturality.{u, v, w} J k g h
  dsimp only [TowerProdFirstVertexNatural, towerProdFirstVertexIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp, H,
    Functor.map_comp, Category.assoc]

/-- **The connecting morphism of the fundamental triangle is natural in the base ring**: change of
base along `k` carries the connecting morphism of `A₁ ⟶ B ⟶ D` to that of `A₂ ⟶ B ⟶ D`. -/
theorem towerConnecting_naturality_baseChange
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)] :
    towerConnecting J (k ≫ g) h ≫
        (DerivedCategory.Q.map (baseChangedCotangentBaseMap.{u, v, w} J k g h))⟦(1 : ℤ)⟧' =
      towerConnecting J g h :=
  towerConnecting_naturality J k g h
    (by
      -- `towerConnecting_naturality` takes this argument in the standard model of `D(B × D)`.
      let := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
      exact towerThirdVertexNatural J k g (prodGraph J h) (injective_prodGraph J h))
    (towerProdFirstVertexNatural J k g h)

end CategoryTheory.Sheaf
