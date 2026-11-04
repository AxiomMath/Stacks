module

public import StacksFrontier.Cotangent.Spaces.FibreProductCorner
public import StacksFrontier.Cotangent.Spaces.DerivedStalkHomology
public import StacksFrontier.Cotangent.SheavesOfRings.PointStalkBaseChangeMap

/-!
# The right column of Stacks 09DK at a geometric point

Let `p : W ⟶ X`, `q : W ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z` be morphisms of algebraic spaces with
`p ≫ f = q ≫ g`, and let `E` be the object of the upper right corner of the diagram of
[Stacks, Tag 09DK] (`AlgebraicGeometry.Space.fibreProductCotangentCorner`). Its right column
`Lq^*L_{Y/Z} ⟶ L_{W/X} ⟶ E ⟶` is distinguished. This file computes the first arrow of that
column at a geometric point `w̄` of `W`.

At the sheaf level the arrow is the first arrow of the fundamental triangle of Tag 08SZ for the
tower `q⁻¹g⁻¹𝒪_Z ⟶ q⁻¹𝒪_Y ⟶ 𝒪_W` of the second projection, read through
`Lq^*L_{Y/Z} ≅ L_{q⁻¹𝒪_Y/q⁻¹g⁻¹𝒪_Z} ⊗ 𝒪_W`, followed by a string of changes of the base ring and
of identifications of cotangent complexes ending in `L_{W/X}`
(`AlgebraicGeometry.Space.fibreProductColumnUnit_comp_transitivityCounit`). Each map of that
string changes the base at every point of the small étale site of `W`, in the sense of
`CategoryTheory.Sheaf.IsPointStalkBaseMap`: its stalk is the change-of-base map of Tag 08PN of the
stalk rings. These are the pieces from which the stalk of the arrow at a geometric point is read
off as `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}`, the stalks at `w̄` of `q⁻¹g⁻¹𝒪_Z`, `q⁻¹𝒪_Y`, `𝒪_W`
and `p⁻¹𝒪_X` being `R`, `B`, `C` and `A`.

## Main results

* `AlgebraicGeometry.Space.fibreProductColumnUnit_comp_transitivityCounit`: the arrow at the
  sheaf level.
* `AlgebraicGeometry.Space.isPointStalkBaseMap_compCotangentComplexULiftIso_hom`,
  `..._inv`, `AlgebraicGeometry.Space.isPointStalkBaseMap_eqToHom`,
  `AlgebraicGeometry.Space.isPointStalkBaseMap_compCotangentComplexIso_hom`, `..._inv`,
  `AlgebraicGeometry.Space.isPointStalkBaseMap_towerCotangentChangeOfBase`,
  `AlgebraicGeometry.Space.isPointStalkBaseMap_cotangentComplexIso`: each map of the string
  changes the base at every point.

## References

* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance high] hasSheafify_smallEtaleRingedToposULift
  wEqualsLocallyBijective_smallEtaleRingedToposULift

/-- **The first arrow of the right column of Stacks 09DK at the sheaf level.** The composite
`Lq^*L_{Y/Z} ⟶ L_{W/Z} ⟶ L_{W/X}` is the identification
`Lq^*L_{Y/Z} ≅ L_{q⁻¹𝒪_Y/q⁻¹g⁻¹𝒪_Z} ⊗ 𝒪_W`, followed by the first arrow of Tag 08SZ for the tower
of the second projection and a string of changes of base ring and of identifications of
cotangent complexes ending in `L_{W/X}`. -/
theorem fibreProductColumnUnit_comp_transitivityCounit (h : p ≫ f = q ≫ g) :
    fibreProductColumnUnit h ≫ transitivityCounit p f =
      (derivedPullbackCotangentComplexIso q g).hom ≫
        DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u + 1, u, u}
            (SmallEtale.topology B S hS W.1)
            (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
              (smallEtaleRingedToposHomULift g) (smallEtaleRingedToposHomULift q))
            (smallEtaleRingedToposHomULift q).fSharpInverseImage) ≫
        DerivedCategory.Q.map
          (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1} _ _).inv ≫
        DerivedCategory.Q.map (compCotangentComplexULiftIso q g).hom ≫
        DerivedCategory.Q.map (eqToHom (congrArg (cotangentComplex B S hS) h.symm)) ≫
        DerivedCategory.Q.map (compCotangentComplexULiftIso p f).inv ≫
        DerivedCategory.Q.map
          (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1} _ _).hom ≫
        DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u + 1, u, u}
          (SmallEtale.topology B S hS W.1)
          (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
            (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p))
          (smallEtaleRingedToposHomULift p).fSharpInverseImage) ≫
        DerivedCategory.Q.map (smallEtaleRingedToposHomULift_cotangentComplexIso p).hom := by
  simp only [fibreProductColumnUnit, transitivityUnit, transitivityCounit,
    RingedToposHom.transitivityUnit, RingedToposHom.transitivityCounit,
    derivedPullbackCotangentComplexIso, cotangentComplexDerivedCongr,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, eqToIso.inv,
    Functor.mapIso_hom, Category.assoc, eqToHom_map]
  rfl

section Pieces

variable (Φ : (SmallEtale.topology B S hS W.1).Point.{u + 1})

/-- The base ring `l⁻¹𝒪_Z` of `L_{W/Z}`, lifted to the universe of the site, for `l : W ⟶ Z`. -/
abbrev liftedBaseRing (l : W ⟶ Z) : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).obj
    ((smallEtaleInverseImageRing B S hS l).obj (smallEtaleRingedTopos B S hS Z).O)

/-- The structure map `l⁻¹𝒪_Z ⟶ 𝒪_W` of `L_{W/Z}`, lifted to the universe of the site. -/
abbrev liftedStructureMap (l : W ⟶ Z) :
    liftedBaseRing (B := B) (S := S) (hS := hS) l ⟶ smallEtaleStructureSheafULift B S hS W :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
    (smallEtaleRingedToposHom B S hS l).fSharpInverseImage

/-- For `k : W ⟶ Y` and `l : Y ⟶ Z`, the structure map of the tower of the lifted morphisms of
ringed topoi is the comparison `towerBaseULiftIso k l` of base rings followed by the lifted
structure map of `k ≫ l`. -/
theorem towerStructureMap_eq (k : W ⟶ Y) (l : Y ⟶ Z) :
    (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k) ≫
      (smallEtaleRingedToposHomULift k).fSharpInverseImage) ≫ 𝟙 _ =
      (towerBaseULiftIso k l).hom ≫ liftedStructureMap (k ≫ l) := by
  refine (Category.comp_id _).trans ?_
  rw [← towerBaseMap_comp_fSharpInverseImage_ulift,
    ← smallEtaleRingedToposHomULift_fSharpInverseImage,
    ← smallEtaleRingedToposHomULift_fSharpInverseImage]
  rfl

/-- The cotangent complex of the tower of `k` and `l` is `L_{W/Z}`: the comparison of the base
rings, followed by restriction of scalars along the identity. -/
abbrev towerULiftCotangentIso (k : W ⟶ Y) (l : Y ⟶ Z) :
    Sheaf.cotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
        (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
            (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k) ≫
          (smallEtaleRingedToposHomULift k).fSharpInverseImage) ≅
      Sheaf.cotangentComplex.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
        (liftedStructureMap (k ≫ l)) :=
  Sheaf.squareCotangentComplexIso.{u + 1, u, u} (J := SmallEtale.topology B S hS W.1)
      (a := (towerBaseULiftIso k l).hom) (b := 𝟙 _) (towerStructureMap_eq k l) ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

/-- The comparison of the iterated inverse image along `k` and `l` with the inverse image along
the composite of the lifted morphisms of ringed topoi, as an isomorphism of base rings. -/
abbrev compBaseIso (k : W ⟶ Y) (l : Y ⟶ Z) :=
  ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingComp
    (smallEtaleRingedToposHomULift l).toToposHom (smallEtaleRingedToposHomULift k).toToposHom).app
      (smallEtaleRingedToposULift B S hS Z).O).symm

/-- The identification of the cotangent complex of the composite of the lifted morphisms of
ringed topoi with that of their tower changes the base along the comparison of base rings. -/
theorem isPointStalkBaseMap_compCotangentComplexIso_hom (k : W ⟶ Y) (l : Y ⟶ Z) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (compBaseIso k l).hom
      (RingedToposHom.comp_fSharpInverseImage_eq_tower.{u, u + 1, u, u, u + 1} _ _)
      (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1}
        (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k)).hom :=
  Sheaf.isPointStalkBaseMap_squareCotangentComplexIso.{u + 1, u, u} _ Φ _ _

/-- The inverse form of `isPointStalkBaseMap_compCotangentComplexIso_hom`. -/
theorem isPointStalkBaseMap_compCotangentComplexIso_inv (k : W ⟶ Y) (l : Y ⟶ Z)
    (hsq : _ ≫ 𝟙 _ = (compBaseIso k l).inv ≫ _) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (compBaseIso k l).inv hsq
      (RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1}
        (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k)).inv :=
  (isPointStalkBaseMap_compCotangentComplexIso_hom Φ k l).iso_inv.{u + 1, u, u} _ Φ hsq

/-- The comparison of the cotangent complex of the composite of the lifted morphisms with
`L_{W/Z}` changes the base along the composite comparison of base rings. -/
theorem isPointStalkBaseMap_compCotangentComplexULiftIso_hom (k : W ⟶ Y) (l : Y ⟶ Z)
    (hsq : _ ≫ 𝟙 _ = ((compBaseIso k l).hom ≫ (towerBaseULiftIso k l).hom) ≫
      liftedStructureMap (k ≫ l)) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      ((compBaseIso k l).hom ≫ (towerBaseULiftIso k l).hom) hsq
      (compCotangentComplexULiftIso k l).hom :=
  (isPointStalkBaseMap_compCotangentComplexIso_hom Φ k l).comp.{u + 1, u, u} _ Φ
    (Sheaf.isPointStalkBaseMap_squareCotangentComplexIso_hom.{u + 1, u, u} _ Φ
      (towerBaseULiftIso k l) (towerStructureMap_eq k l)) hsq

/-- A square over `D` along an isomorphism of base rings gives one along its inverse. -/
private theorem square_inv_of_iso
    {A₁ A₂ D : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u + 1}}
    {f₁ : A₁ ⟶ D} {f₂ : A₂ ⟶ D} (e : A₁ ≅ A₂) (hsq : f₁ ≫ 𝟙 D = e.hom ≫ f₂) :
    f₂ ≫ 𝟙 D = e.inv ≫ f₁ :=
  (Category.comp_id _).trans ((Iso.eq_inv_comp e).mpr (hsq.symm.trans (Category.comp_id _)))

/-- The inverse form of `isPointStalkBaseMap_compCotangentComplexULiftIso_hom`. -/
theorem isPointStalkBaseMap_compCotangentComplexULiftIso_inv (k : W ⟶ Y) (l : Y ⟶ Z)
    (hsq : liftedStructureMap (k ≫ l) ≫ 𝟙 _ =
      ((towerBaseULiftIso k l).inv ≫ (compBaseIso k l).inv) ≫ _) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      ((towerBaseULiftIso k l).inv ≫ (compBaseIso k l).inv) hsq
      (compCotangentComplexULiftIso k l).inv := by
  have h₁ : Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (towerBaseULiftIso k l).hom (towerStructureMap_eq k l) (towerULiftCotangentIso k l).hom :=
    Sheaf.isPointStalkBaseMap_squareCotangentComplexIso_hom.{u + 1, u, u} _ Φ
      (towerBaseULiftIso k l) (towerStructureMap_eq k l)
  have h₂ := h₁.iso_inv.{u + 1, u, u} _ Φ
    (square_inv_of_iso _ (towerStructureMap_eq k l))
  exact h₂.comp.{u + 1, u, u} _ Φ (isPointStalkBaseMap_compCotangentComplexIso_inv Φ k l
    (square_inv_of_iso _
      (RingedToposHom.comp_fSharpInverseImage_eq_tower.{u, u + 1, u, u, u + 1} _ _))) hsq

/-- Transport along an equality of morphisms of algebraic spaces changes the base along the
corresponding transport of base rings. -/
theorem isPointStalkBaseMap_eqToHom {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂)
    (hsq : liftedStructureMap k₁ ≫ 𝟙 _ =
      eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) e) ≫
        liftedStructureMap k₂) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (eqToHom (congrArg (fun k => liftedBaseRing (B := B) (S := S) (hS := hS) k) e)) hsq
      (eqToHom (congrArg (cotangentComplex B S hS) e)) := by
  subst e
  exact Sheaf.isPointStalkBaseMap_id.{u + 1, u, u} _ Φ hsq

/-- The second arrow of Tag 08SZ for the tower of `k` and `l` changes the base along the lower
homomorphism of the tower. -/
theorem isPointStalkBaseMap_towerCotangentChangeOfBase (k : W ⟶ Y) (l : Y ⟶ Z) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
        (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k)) (by simp)
      (Sheaf.towerCotangentChangeOfBase.{u + 1, u, u} (SmallEtale.topology B S hS W.1)
        (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
          (smallEtaleRingedToposHomULift l) (smallEtaleRingedToposHomULift k))
        (smallEtaleRingedToposHomULift k).fSharpInverseImage) :=
  Sheaf.isPointStalkBaseMap_squareCotangentComplexMap.{u + 1, u, u} _ Φ _ _

/-- The identification of the cotangent complex of the lifted morphism of ringed topoi of `k`
with `L_{W/Y}` changes the base along the comparison of the inverse images at the two
universes. -/
theorem isPointStalkBaseMap_cotangentComplexIso (k : W ⟶ Y) (hsq) :
    Sheaf.IsPointStalkBaseMap.{u + 1, u, u} (SmallEtale.topology B S hS W.1) Φ
      ((smallEtaleInverseImageRingULiftIso k).inv.app (smallEtaleRingedTopos B S hS Y).O) hsq
      (smallEtaleRingedToposHomULift_cotangentComplexIso k).hom :=
  Sheaf.isPointStalkBaseMap_squareCotangentComplexIso.{u + 1, u, u} _ Φ _ _

end Pieces

end AlgebraicGeometry.Space
