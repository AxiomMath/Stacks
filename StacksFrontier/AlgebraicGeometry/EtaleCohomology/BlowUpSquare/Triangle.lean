module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedOpenClosedConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DerivedBaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.CategoryTheory.Preadditive.AdditiveFunctorBiprod
public import StacksFrontier.CategoryTheory.Triangulated.FibreOfBiproductDesc

/-!
# The Mayer–Vietoris triangle of a square that is an isomorphism off a closed subscheme

Consider a cartesian square of schemes

```
E --j--> X'
|π       |b
v        v
Z --i--> X
```

with `i` a closed immersion, `c = π ≫ i = j ≫ b`, and suppose `b` is an isomorphism over the
open complement `U` of `Z`. If cohomology commutes with base change for `b`
(`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange`), then for every bounded below `K` in
`D(X_étale)` with torsion cohomology sheaves there is a distinguished triangle

`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K[1]`

whose first map is formed by the two adjunction units and whose second map is the difference of
the two comparison maps `Ri_*(K|_Z) ⟶ Rc_*(K|_E)` and `Rb_*(K|_{X'}) ⟶ Rc_*(K|_E)`. The blowup
of `X` in a quasi-coherent ideal of finite type is such a square, the hypothesis on `b` being
the proper base change theorem; this is the content of Stacks Tag 0EW5.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDerivedUnitCompMap`: for `c = π ≫ i`, the comparison
  `Ri_* i⁻¹ ⟶ Rc_* c⁻¹`, which is `Ri_*` of the unit of `π⁻¹ ⊣ Rπ_*`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedAdjunction_unit_app_comp_unitCompMap`: the
  comparison carries the unit of `i` to the unit of `c`.
* `Stacks.EtaleCohomology.exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange`:
  the distinguished triangle above.

## Implementation notes

The source represents `K` by a complex and checks the triangle on stalks. Here the argument is
made in the derived category directly. The composite of the two maps vanishes because both
comparison maps carry the units to the unit of `c`. Completing the second map to a
distinguished triangle `F ⟶ A ⊕ B ⟶ C ⟶ F[1]`, the first map factors through a map `K ⟶ F`,
which is shown to be an isomorphism after restriction to `Z` and to `U`; these restrictions
jointly reflect isomorphisms
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianDerivedInverseImage_of_range_eq_compl`).

* Over `U` the two direct images from `Z` and from `E` vanish, so the triangle reduces to the
  unit of `b` over `U`, which is invertible because `b` is an isomorphism there (open base
  change, `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion`).
* Over `Z` the comparison `Rb_*(K|_{X'}) ⟶ Rc_*(K|_E)` becomes invertible: by the horizontal
  description of the base change map
  (`etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange`)
  it is the base change map `i⁻¹ Rb_* ⟶ Rπ_* j⁻¹`, invertible on bounded below complexes with
  torsion cohomology (Stacks 0DDE,
  `isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange`). The fibre of a
  map `A ⊕ B ⟶ C` whose second component is invertible is `A`
  (`CategoryTheory.Pretriangulated.isIso_mor₁_comp_biprod_fst_of_isIso`), and `i⁻¹` of the unit
  of `i` is invertible.

## References

* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-! ### The comparison `Ri_* i⁻¹ ⟶ Rc_* c⁻¹` for a factorization `c = π ≫ i` -/

section UnitComp

variable {E Z X : Scheme.{u}} (π : E ⟶ Z) (i : Z ⟶ X) (c : E ⟶ X) (hc : c = π ≫ i)

/-- For a factorization `c = π ≫ i`, the comparison `Ri_* i⁻¹ ⟶ Rc_* c⁻¹` on derived categories
of abelian étale sheaves: `Ri_*` of the unit `𝟭 ⟶ Rπ_* π⁻¹` at `i⁻¹ K`, read through the
identifications `c⁻¹ ≅ π⁻¹ i⁻¹` and `Rc_* ≅ Ri_* Rπ_*`. -/
public def etaleAbelianDerivedUnitCompMap :
    etaleAbelianDerivedInverseImage.{u, v} i ⋙ etaleAbelianDerivedDirectImage.{u, v} i ⟶
      etaleAbelianDerivedInverseImage.{u, v} c ⋙ etaleAbelianDerivedDirectImage.{u, v} c :=
  Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} i)
      (Functor.whiskerRight (etaleAbelianDerivedAdjunction.{u, v} π).unit
        (etaleAbelianDerivedDirectImage.{u, v} i)) ≫
    Functor.whiskerRight (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).inv
      (etaleAbelianDerivedDirectImage.{u, v} π ⋙ etaleAbelianDerivedDirectImage.{u, v} i) ≫
    Functor.whiskerLeft (etaleAbelianDerivedInverseImage.{u, v} c)
      (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).inv

/-- The component of `Stacks.EtaleCohomology.etaleAbelianDerivedUnitCompMap`, written out. -/
public theorem etaleAbelianDerivedUnitCompMap_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedUnitCompMap.{u, v} π i c hc).app K =
      (etaleAbelianDerivedDirectImage.{u, v} i).map
          ((etaleAbelianDerivedAdjunction.{u, v} π).unit.app
            ((etaleAbelianDerivedInverseImage.{u, v} i).obj K)) ≫
        (etaleAbelianDerivedDirectImage.{u, v} i).map
          ((etaleAbelianDerivedDirectImage.{u, v} π).map
            ((etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).inv.app K)) ≫
        (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).inv.app
          ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) := by
  simp [etaleAbelianDerivedUnitCompMap]

/-- **The comparison `Ri_* i⁻¹ ⟶ Rc_* c⁻¹` carries the unit of `i` to the unit of `c`.** The
composite `K ⟶ Ri_* i⁻¹ K ⟶ Rc_* c⁻¹ K` is the unit of `c⁻¹ ⊣ Rc_*`: the composite of the units
of `i` and of `π` is the unit of the composite adjunction, and `Rc_* ≅ Ri_* Rπ_*` is by
construction the conjugate of `c⁻¹ ≅ π⁻¹ i⁻¹`. -/
public theorem etaleAbelianDerivedAdjunction_unit_app_comp_unitCompMap
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedAdjunction.{u, v} i).unit.app K ≫
        (etaleAbelianDerivedUnitCompMap.{u, v} π i c hc).app K =
      (etaleAbelianDerivedAdjunction.{u, v} c).unit.app K := by
  have h := unit_conjugateEquiv (etaleAbelianDerivedAdjunction.{u, v} c)
    ((etaleAbelianDerivedAdjunction.{u, v} i).comp (etaleAbelianDerivedAdjunction.{u, v} π))
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).inv K
  have hD : conjugateEquiv (etaleAbelianDerivedAdjunction.{u, v} c)
      ((etaleAbelianDerivedAdjunction.{u, v} i).comp (etaleAbelianDerivedAdjunction.{u, v} π))
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).inv =
      (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).hom := rfl
  rw [hD, Adjunction.comp_unit_app] at h
  rw [etaleAbelianDerivedUnitCompMap_app, ← cancel_mono
    ((etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hc).hom.app
      ((etaleAbelianDerivedInverseImage.{u, v} c).obj K)), h]
  simp only [Functor.comp_map, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Functor.comp_obj]

/-- **The comparison along the upper side of a commutative square is base change followed by a
unit.** For a commutative square `j ≫ b = π ≫ i` with common composite `c`, the comparison
`Rb_* b⁻¹ K ⟶ Rc_* c⁻¹ K` along `c = j ≫ b` is the unit of `i` at `Rb_* b⁻¹ K` followed by
`Ri_*` of the base change map `i⁻¹ Rb_* ⟶ Rπ_* j⁻¹` at `b⁻¹ K`, read through the
identifications `j⁻¹ b⁻¹ ≅ c⁻¹` and `Ri_* Rπ_* ≅ Rc_*`. -/
public theorem etaleAbelianDerivedUnitCompMap_app_eq_baseChange {E Z X X' : Scheme.{u}}
    (i : Z ⟶ X) (b : X' ⟶ X) (j : E ⟶ X') (π : E ⟶ Z) (w : j ≫ b = π ≫ i) (c : E ⟶ X)
    (hcj : c = j ≫ b) (hcπ : c = π ≫ i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedUnitCompMap.{u, v} j b c hcj).app K =
      (etaleAbelianDerivedAdjunction.{u, v} i).unit.app
          ((etaleAbelianDerivedDirectImage.{u, v} b).obj
            ((etaleAbelianDerivedInverseImage.{u, v} b).obj K)) ≫
        (etaleAbelianDerivedDirectImage.{u, v} i).map
          ((etaleAbelianDerivedBaseChange.{u, v} b i j π w).app
              ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ≫
            (etaleAbelianDerivedDirectImage.{u, v} π).map
              ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K)) ≫
        (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hcπ).inv.app
          ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) := by
  have key := etaleAbelianDerivedAdjunction_unit_app_comp_map_etaleAbelianDerivedBaseChange.{u, v}
    b i j π w c hcj hcπ ((etaleAbelianDerivedInverseImage.{u, v} b).obj K)
  have n₁ := (etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hcπ).hom.naturality
    ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K)
  have n₂ := (etaleAbelianDerivedDirectImageCompIso'.{u, v} j b c hcj).inv.naturality
    ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at n₁ n₂
  rw [etaleAbelianDerivedUnitCompMap_app, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% key, ← reassoc_of% n₁]
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  rw [n₂]

end UnitComp

/-! ### The open part -/

section OpenPart

/-- **Over an open subscheme on which `b` is an isomorphism, the unit of `b` is invertible.**
For a cartesian square `o' ≫ b = bU ≫ o` with `o` an open immersion and `bU` an isomorphism,
`o⁻¹` of the unit `K ⟶ Rb_* b⁻¹ K` is invertible: by open base change it is identified with the
unit of `bU⁻¹ ⊣ RbU_*`, and inverse image along an isomorphism is an equivalence. -/
public theorem isIso_map_etaleAbelianDerivedAdjunction_unit_of_isPullback_of_isIso
    {X X' U U' : Scheme.{u}} (b : X' ⟶ X) (o : U ⟶ X) [IsOpenImmersion o] (o' : U' ⟶ X')
    (bU : U' ⟶ U) (sq : IsPullback o' bU b o) [IsIso bU]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((etaleAbelianDerivedInverseImage.{u, v} o).map
      ((etaleAbelianDerivedAdjunction.{u, v} b).unit.app K)) := by
  let α := etaleAbelianDerivedSquare.{u, v} b o o' bU (o' ≫ b) rfl sq.w
  have hα : IsIso α := by
    dsimp only [α, etaleAbelianDerivedSquare]
    infer_instance
  have hβ : IsIso (etaleAbelianDerivedBaseChange.{u, v} b o o' bU sq.w) :=
    isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} b o o' bU sq
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, v} b o o' bU (o' ≫ b) rfl sq.w] at hβ
  have hdense := isDenseSubsite_smallEtaleBaseChange_of_isIso bU
  have : (etaleAbelianDirectImage.{u, v} bU).IsEquivalence :=
    inferInstanceAs ((smallEtaleBaseChange bU).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology U) (smallEtaleTopology U')).IsEquivalence
  have : (etaleAbelianInverseImage.{u, v} bU).IsEquivalence :=
    Functor.isEquivalence_of_iso (Adjunction.leftAdjointUniq
      (etaleAbelianInverseImageDirectImageAdj.{u, v} bU)
      (etaleAbelianDirectImage.{u, v} bU).asEquivalence.symm.toAdjunction).symm
  have : (etaleAbelianDerivedInverseImage.{u, v} bU).IsEquivalence :=
    Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory _
  have h := unit_mateEquiv (etaleAbelianDerivedAdjunction.{u, v} b)
    (etaleAbelianDerivedAdjunction.{u, v} bU) α K
  have : IsIso ((etaleAbelianDerivedAdjunction.{u, v} bU).unit.app
      ((etaleAbelianDerivedInverseImage.{u, v} o).obj K)) := inferInstance
  have : IsIso ((mateEquiv (etaleAbelianDerivedAdjunction.{u, v} b)
      (etaleAbelianDerivedAdjunction.{u, v} bU) α).app
        ((etaleAbelianDerivedInverseImage.{u, v} b).obj K)) := inferInstance
  have : IsIso (α.app K) := inferInstance
  dsimp only [Functor.id_obj, Functor.comp_obj] at h
  exact IsIso.of_isIso_fac_right h

end OpenPart

/-! ### The triangle -/

section Triangle

variable {X Z X' E : Scheme.{u}} (i : Z ⟶ X) (b : X' ⟶ X) (j : E ⟶ X') (π : E ⟶ Z)
  (c : E ⟶ X) (hcπ : c = π ≫ i) (hcj : c = j ≫ b)

/-- The first map `K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'})` of the Mayer–Vietoris triangle of a square:
the two adjunction units. -/
public def etaleAbelianDerivedSquareUnits
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    K ⟶ (etaleAbelianDerivedDirectImage.{u, v} i).obj
        ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ⊞
      (etaleAbelianDerivedDirectImage.{u, v} b).obj
        ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) :=
  biprod.lift ((etaleAbelianDerivedAdjunction.{u, v} i).unit.app K)
    ((etaleAbelianDerivedAdjunction.{u, v} b).unit.app K)

/-- The second map `Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E)` of the Mayer–Vietoris triangle of
a square with common composite `c = π ≫ i = j ≫ b`: the difference of the two comparison maps
`Stacks.EtaleCohomology.etaleAbelianDerivedUnitCompMap`. -/
public def etaleAbelianDerivedSquareDifference
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleAbelianDerivedDirectImage.{u, v} i).obj
        ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ⊞
      (etaleAbelianDerivedDirectImage.{u, v} b).obj
        ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ⟶
      (etaleAbelianDerivedDirectImage.{u, v} c).obj
        ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) :=
  biprod.desc ((etaleAbelianDerivedUnitCompMap.{u, v} π i c hcπ).app K)
    (-(etaleAbelianDerivedUnitCompMap.{u, v} j b c hcj).app K)

/-- The two maps of the Mayer–Vietoris triangle compose to zero: both comparison maps carry the
units to the unit of `c`. -/
public theorem etaleAbelianDerivedSquareUnits_comp_difference
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    etaleAbelianDerivedSquareUnits.{u, v} i b K ≫
      etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K = 0 := by
  rw [etaleAbelianDerivedSquareUnits, etaleAbelianDerivedSquareDifference, biprod.lift_desc,
    etaleAbelianDerivedAdjunction_unit_app_comp_unitCompMap, Preadditive.comp_neg,
    etaleAbelianDerivedAdjunction_unit_app_comp_unitCompMap, add_neg_cancel]

/-- If `biprod.lift f g` factors as `φ' ≫ α`, then any functor sends `φ' ≫ α ≫ fst` to `f` and
`φ' ≫ α ≫ snd` to `g`. -/
private theorem map_comp_map_biprod_eq_of_lift_eq {C D : Type*} [Category C] [Category D]
    [Preadditive C] [HasBinaryBiproducts C] (G : C ⥤ D) {K F P Q : C} {f : K ⟶ P} {g : K ⟶ Q}
    {φ' : K ⟶ F} {α : F ⟶ P ⊞ Q} (h : biprod.lift f g = φ' ≫ α) :
    G.map φ' ≫ G.map (α ≫ biprod.fst) = G.map f ∧
      G.map φ' ≫ G.map (α ≫ biprod.snd) = G.map g := by
  simp only [← Functor.map_comp, ← Category.assoc, ← h, biprod.lift_fst, biprod.lift_snd, and_self]

/-- **The Mayer–Vietoris triangle of a square that is an isomorphism off a closed subscheme.**
Let
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
be a cartesian square of schemes with `i` a closed immersion and common composite `c`, let
`o : U ⟶ X` be an open immersion onto the complement of `Z`, and suppose `b` is an isomorphism
over `U` (the base change `bU` of `b` to `U` is invertible) and cohomology commutes with base
change for `b`. Then for every bounded below `K` in `D(X_étale)` with torsion cohomology sheaves
there is a distinguished triangle
`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K[1]`
whose first map is formed by the units and whose second map is the difference of the two
comparison maps to `Rc_*(K|_E)`. -/
public theorem exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange
    [IsClosedImmersion i] {U U' : Scheme.{u}} (o : U ⟶ X) [IsOpenImmersion o]
    (hio : Set.range o.base = (Set.range i.base)ᶜ) (sq : IsPullback j π b i)
    (o' : U' ⟶ X') (bU : U' ⟶ U) (sqU : IsPullback o' bU b o) [IsIso bU]
    (hb : CohomologyCommutesWithBaseChange.{u, v} b)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (n : ℤ)
    (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology K) :
    ∃ δ : (etaleAbelianDerivedDirectImage.{u, v} c).obj
        ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk (etaleAbelianDerivedSquareUnits.{u, v} i b K)
        (etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K) δ ∈
        distTriang
          (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) := by
  set φ := etaleAbelianDerivedSquareUnits.{u, v} i b K with hφdef
  obtain ⟨F, α, δ', hT'⟩ := distinguished_cocone_triangle₁
    (etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K)
  obtain ⟨φ', hφ'⟩ := Triangle.coyoneda_exact₂ _ hT' φ
    (etaleAbelianDerivedSquareUnits_comp_difference.{u, v} i b j π c hcπ hcj K)
  change φ = φ' ≫ α at hφ'
  have hiso : IsIso φ' := by
    refine isIso_of_isIso_etaleAbelianDerivedInverseImage_of_range_eq_compl i o hio φ' ?_ ?_
    · -- over the closed subscheme
      have hK' : ((etaleAbelianDerivedInverseImage.{u, v} b).obj K).IsGE n :=
        Functor.isGE_obj_mapDerivedCategory (etaleAbelianInverseImage.{u, v} b) K n hK
      have hβ := isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, v}
        hb sq _ n hK' (torsionCohomologyProperty_etaleAbelianDerivedInverseImage.{u, v} b K hT)
      have : IsIso ((etaleAbelianDerivedInverseImage.{u, v} i).map
          (-(etaleAbelianDerivedUnitCompMap.{u, v} j b c hcj).app K)) := by
        rw [Functor.map_neg,
          etaleAbelianDerivedUnitCompMap_app_eq_baseChange.{u, v} i b j π sq.w c hcj hcπ K]
        simp only [Functor.map_comp]
        infer_instance
      have hfst := isIso_map_mor₁_comp_biprod_fst_of_isIso
        (etaleAbelianDerivedInverseImage.{u, v} i) α
        ((etaleAbelianDerivedUnitCompMap.{u, v} π i c hcπ).app K)
        (-(etaleAbelianDerivedUnitCompMap.{u, v} j b c hcj).app K) δ' hT'
      exact IsIso.of_isIso_fac_right (map_comp_map_biprod_eq_of_lift_eq _ hφ').1
    · -- over the open complement
      have hC : IsZero ((etaleAbelianDerivedInverseImage.{u, v} o).obj
          ((etaleAbelianDerivedDirectImage.{u, v} c).obj
            ((etaleAbelianDerivedInverseImage.{u, v} c).obj K))) :=
        IsZero.of_iso (isZero_etaleAbelianDerivedInverseImage_derivedDirectImage.{u, v} i o hio _)
          ((etaleAbelianDerivedInverseImage.{u, v} o).mapIso
            ((etaleAbelianDerivedDirectImageCompIso'.{u, v} π i c hcπ).app _))
      have hsnd := isIso_map_mor₁_comp_biprod_snd_of_isZero
        (etaleAbelianDerivedInverseImage.{u, v} o) α _ δ' hT'
        (isZero_etaleAbelianDerivedInverseImage_derivedDirectImage.{u, v} i o hio _) hC
      have hηb := isIso_map_etaleAbelianDerivedAdjunction_unit_of_isPullback_of_isIso.{u, v} b o o'
        bU sqU K
      exact IsIso.of_isIso_fac_right (map_comp_map_biprod_eq_of_lift_eq _ hφ').2
  refine ⟨δ' ≫ (inv φ')⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT' _
    (Triangle.isoMk _ _ (asIso φ') (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simp [hφ']
  · simp
  · simp

end Triangle


end Stacks.EtaleCohomology

end
