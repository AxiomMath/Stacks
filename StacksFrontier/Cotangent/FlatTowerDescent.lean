module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Cotangent.EtaleVanishingUnconditional
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# The displayed morphisms of the fundamental triangle along a flat base change

Let `K → A → D` and `K → B → D` be ring maps and let `D → C` be a flat ring map, with `C` an
algebra over `K`, `A` and `B` through `D`. Base change along `D → C` is exact, so it acts on
`D(D)` as the functor `(C ⊗_D -).mapDerivedCategory`, and this file computes what it does to the
two displayed morphisms of [Stacks, Tag 08QS]:

* the first morphism `L_{A/K} ⊗^𝐋_A D ⟶ L_{D/K}` of the tower `K → A → D`, base changed to `C`
  and followed by the canonical map `L_{D/K} ⊗_D C ⟶ L_{C/K}`, is the first morphism
  `L_{A/K} ⊗^𝐋_A C ⟶ L_{C/K}` of the tower `K → A → C`, read through the cancellation of the
  two base changes;
* the second morphism `L_{D/K} ⟶ L_{D/B}` of the tower `K → B → D`, base changed to `C` and
  followed by `L_{D/B} ⊗_D C ⟶ L_{C/B}`, is `L_{D/K} ⊗_D C ⟶ L_{C/K}` followed by the second
  morphism `L_{C/K} ⟶ L_{C/B}` of the tower `K → B → C`.

This is the computation behind the proof of [Stacks, Tag 09DM]: the stalk of the object `E` of
Equation 92.28.0.1 at a geometric point is the cone of `L_{A/R} ⊗^𝐋_A C ⟶ L_{C/B}` for the
étale local rings, and these two identities show that this map is the base change along the
flat map `A ⊗_R B → C` of the map `L_{A/R} ⊗^𝐋_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}` whose cone is the
object `E` of Equation 92.15.0.1. The proof is the one of
`CommAlgCat.productDisplayMor₁_eq_fundamentalMor₁` and
`CommAlgCat.productDisplayMor₂_eq_fundamentalMor₂`, with the flat projection `B × C → C` replaced
by an arbitrary flat ring map.

## Main definitions

* `CommAlgCat.flatTowerVertex₁Iso`: `(L_{A/K} ⊗^𝐋_A D) ⊗_D C ≅ L_{A/K} ⊗^𝐋_A C`.
* `CommAlgCat.flatTowerVertexMap K D C`: the canonical map `L_{D/K} ⊗_D C ⟶ L_{C/K}`, read from
  the derived base change.

## Main results

* `CommAlgCat.flatTowerVertexMap_fundamentalMor₁`: the first displayed morphism descends.
* `CommAlgCat.flatTowerVertexMap_fundamentalMor₂`: the second displayed morphism descends.
* `CommAlgCat.isIso_flatTowerVertexMap_of_isZero`: `L_{D/B} ⊗_D C ⟶ L_{C/B}` is an isomorphism
  when `L_{C/D} = 0`, by [Stacks, Tag 08R3].
* `CommAlgCat.flatTowerVertexMap_rightColumn`: the map `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/R} ⟶ L_{C/A}` is
  the base change of `L_{B/R} ⊗^𝐋_B D ⟶ L_{D/R} ⟶ L_{D/A}`.
* `CommAlgCat.nonempty_iso_mapDerivedCategory_cone_of_isZero` and
  `CommAlgCat.nonempty_homology_cone_iso_extendScalars_of_isZero`: when `L_{C/D} = 0`, a cone of
  the first map is the base change of a cone of the second, and its cohomology is
  `H^i(E_D) ⊗_D C`.
* `CommAlgCat.nonempty_homology_cone_iso_extendScalars_of_weaklyEtale`: the same for a weakly
  étale `D → C`, which is the case of the étale local rings of a fibre product.

## Implementation notes

The algebra structures of `C` over `K`, `A` and `B` are arbitrary instances subject to the scalar
tower conditions. The proofs first replace them by the composites through `D`, which is possible
because an algebra structure is determined by its structure map: the chain-level composition
law of [Stacks, Tag 08PN], `CommAlgCat.squareCotangentComplexMap_counit_comp_iterated'`, is
stated for a composite square, and the composite of the squares of the two towers is the square
of the composite tower definitionally only for the composite structure maps.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

section Flat

variable (D C : Type u) [CommRing D] [CommRing C] [Algebra D C]

/-- Base change along a flat ring map preserves finite limits. -/
theorem preservesFiniteLimits_extendScalars_algebraMap [Module.Flat D C] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

end Flat

section Tower

variable (K : Type u) [CommRing K] (D : Type u) [CommRing D] [Algebra K D]
  (C : Type u) [CommRing C] [Algebra D C] [Algebra K C] [IsScalarTower K D C] [Module.Flat D C]

attribute [local instance] preservesFiniteLimits_extendScalars_algebraMap

/-- **The canonical map `L_{D/K} ⊗_D C ⟶ L_{C/K}`**, out of the base change of `L_{D/K}` along
the flat map `D → C`: the comparison of the derived with the degreewise base change, followed by
the functoriality map of [Stacks, Tag 08PN] for the square `(𝟙_K, D → C)` in its adjoint shape.
It is the first displayed morphism of the tower `K → D → C` read out of the exact base change. -/
def flatTowerVertexMap :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.obj
        (cotangentComplexDerived.{u, u} K (CommAlgCat.of K D)) ⟶
      cotangentComplexDerived.{u, u} K (CommAlgCat.of K C) :=
  (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryFactors.hom.app
      (cotangentComplex.{u, u} K (CommAlgCat.of K D)) ≫
    DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (A := K) (A' := K)
      (B := CommAlgCat.of K D) (B' := CommAlgCat.of K C) (IsScalarTower.toAlgHom K D C))

/-- `CommAlgCat.flatTowerVertexMap` is `CommAlgCat.fundamentalMor₁` up to the two comparisons of
the derived base change with the degreewise one: they share the chain-level map. -/
theorem flatTowerVertexMap_eq :
    flatTowerVertexMap K D C =
      (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryFactors.hom.app
          (cotangentComplex.{u, u} K (CommAlgCat.of K D)) ≫
        (cotangentComplexDerivedBaseChangeTermwiseIso K (CommAlgCat.of K D) C).inv ≫
          fundamentalMor₁.{u} K D C := by
  rw [fundamentalMor₁, Iso.inv_hom_id_assoc]
  rfl

/-- **[Stacks, Tag 08R3] read out of the exact base change.** If `L_{C/D} = 0` then the canonical
map `L_{D/K} ⊗_D C ⟶ L_{C/K}` is an isomorphism. -/
theorem isIso_flatTowerVertexMap_of_isZero
    (h : IsZero (cotangentComplexDerived.{u, u} D (CommAlgCat.of D C))) :
    IsIso (flatTowerVertexMap K D C) := by
  have := isIso_fundamentalMor₁_of_isZero_fundamentalVertex₃.{u} K D C h
  rw [flatTowerVertexMap_eq]
  infer_instance

end Tower

section Congr

variable {A A' : Type u} [CommRing A] [CommRing A'] {B : CommAlgCat.{u} A}
  {B' : CommAlgCat.{u} A'}

/-- Two commutative squares of ring maps with the same two maps are equal. -/
theorem AlgebraSquare.ext_of_eq {sq₁ sq₂ : AlgebraSquare.{u, u, u} A A' B B'}
    (hb : sq₁.base = sq₂.base) (hm : sq₁.map = sq₂.map) : sq₁ = sq₂ := by
  cases sq₁
  cases sq₂
  cases hb
  cases hm
  rfl

/-- The adjoint shape `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of the functoriality map of [Stacks, Tag 08PN]
depends on the square only through the square: equal squares give equal maps, up to the
identification of the two sources. -/
theorem squareCotangentComplexMap_counit_congr {sq₁ sq₂ : AlgebraSquare.{u, u, u} A A' B B'}
    (h : sq₁ = sq₂) :
    ((ModuleCat.extendScalars sq₁.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} sq₁) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex sq₁.map (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A' B') =
      eqToHom (by rw [h]) ≫
        ((ModuleCat.extendScalars sq₂.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} sq₂) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex sq₂.map (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A' B') := by
  subst h
  simp

end Congr

section FirstMorphism

variable (K : Type u) [CommRing K] (A : Type u) [CommRing A] [Algebra K A]
  (D : Type u) [CommRing D] [Algebra K D] [Algebra A D] [IsScalarTower K A D]
  (C : Type u) [CommRing C] [Algebra D C] [Algebra K C] [IsScalarTower K D C]
  [Algebra A C] [IsScalarTower A D C] [IsScalarTower K A C] [Module.Flat D C]

attribute [local instance] preservesFiniteLimits_extendScalars_algebraMap

/-- **The first vertex descends.** Base change along the flat map `D → C` carries
`L_{A/K} ⊗^𝐋_A D` to `L_{A/K} ⊗^𝐋_A C`: the terms of `L_{A/K}` are projective, so both derived
base changes are computed degreewise, and the two degreewise base changes cancel. -/
def flatTowerVertex₁Iso :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.obj
        (fundamentalVertex₁.{u, u, u + 1, u + 1} K A D) ≅
      fundamentalVertex₁.{u, u, u + 1, u + 1} K A C :=
  (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.mapIso
      (cotangentComplexDerivedBaseChangeTermwiseIso K (CommAlgCat.of K A) D) ≪≫
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap A D)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} K (CommAlgCat.of K A))) ≪≫
    DerivedCategory.Q.mapIso
      ((ModuleCat.extendScalarsCompComplexIso (algebraMap A D) (algebraMap D C)
        (ComplexShape.up ℤ)).app (cotangentComplex.{u, u} K (CommAlgCat.of K A))) ≪≫
    eqToIso (by rw [← IsScalarTower.algebraMap_eq]) ≪≫
    (cotangentComplexDerivedBaseChangeTermwiseIso K (CommAlgCat.of K A) C).symm

omit [Module.Flat D C] in
/-- **The first morphism descends, at chain level**, for the composite algebra structure of `C`
over `A`: the functoriality map of [Stacks, Tag 08PN] for `A → D` in the adjoint shape, base
changed along `D → C` and followed by the one for `D → C`, is the one for `A → C`, read through
the cancellation of the two base changes. This is
`CommAlgCat.squareCotangentComplexMap_counit_comp_iterated'` at the squares
`CommAlgCat.displaySquare₁` of the two towers. -/
theorem flatTower_cotangentExtendScalars_comp :
    ((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K A)
            (B' := CommAlgCat.of K D) (IsScalarTower.toAlgHom K A D)) ≫
        cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K D)
          (B' := CommAlgCat.of K C) (IsScalarTower.toAlgHom K D C) =
      (ModuleCat.extendScalarsCompComplexIso (algebraMap A D) (algebraMap D C)
            (ComplexShape.up ℤ)).hom.app (cotangentComplex.{u, u} K (CommAlgCat.of K A)) ≫
        eqToHom (by rw [← IsScalarTower.algebraMap_eq]; rfl) ≫
        cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K A)
          (B' := CommAlgCat.of K C) (IsScalarTower.toAlgHom K A C) := by
  have hsq : (displaySquare₁ K A D).comp (displaySquare₁ K D C) = displaySquare₁ K A C :=
    AlgebraSquare.ext_of_eq (RingHom.id_comp _) (IsScalarTower.algebraMap_eq A D C).symm
  simp only [cotangentExtendScalarsComplexMap_eq_counit]
  exact (squareCotangentComplexMap_counit_comp_iterated'.{u} (displaySquare₁ K A D)
    (displaySquare₁ K D C)).trans (whisker_eq _ (squareCotangentComplexMap_counit_congr hsq))

/-- **The first displayed morphism descends along a flat base change.** For towers
`K → A → D → C` with `D → C` flat, the first displayed morphism `L_{A/K} ⊗^𝐋_A D ⟶ L_{D/K}`,
base changed to `C` and followed by `L_{D/K} ⊗_D C ⟶ L_{C/K}`, is the first displayed morphism
`L_{A/K} ⊗^𝐋_A C ⟶ L_{C/K}`, read through `CommAlgCat.flatTowerVertex₁Iso`. -/
theorem flatTowerVertexMap_fundamentalMor₁ :
    (flatTowerVertex₁Iso K A D C).inv ≫
        (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.map
          (fundamentalMor₁.{u} K A D) ≫ flatTowerVertexMap K D C =
      fundamentalMor₁.{u} K A C := by
  have hkey := (ModuleCat.extendScalars.{u, u, u}
      (algebraMap D C)).mapDerivedCategoryFactors_hom_app_comp
    (cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K A)
      (B' := CommAlgCat.of K D) (IsScalarTower.toAlgHom K A D))
    (cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K D)
      (B' := CommAlgCat.of K C) (IsScalarTower.toAlgHom K D C))
  rw [Iso.inv_comp_eq, flatTowerVertex₁Iso, flatTowerVertexMap, fundamentalMor₁, fundamentalMor₁]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  refine congrArg (fun z =>
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.map
      (cotangentComplexDerivedBaseChangeTermwiseIso K (CommAlgCat.of K A) D).hom ≫ z) ?_
  refine Eq.trans hkey ?_
  refine congrArg (fun z =>
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars (algebraMap A D)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} K (CommAlgCat.of K A))) ≫ z) ?_
  rw [flatTower_cotangentExtendScalars_comp]
  exact (DerivedCategory.Q.map_comp _ _).trans (whisker_eq _
    ((DerivedCategory.Q.map_comp _ _).trans (eq_whisker (eqToHom_map _ _) _)))

end FirstMorphism

section SecondMorphism

variable (K : Type u) [CommRing K] (B : Type u) [CommRing B] [Algebra K B]
  (D : Type u) [CommRing D] [Algebra K D] [Algebra B D] [IsScalarTower K B D]
  (C : Type u) [CommRing C] [Algebra D C] [Algebra K C] [IsScalarTower K D C]
  [Algebra B C] [IsScalarTower B D C] [IsScalarTower K B C] [Module.Flat D C]

attribute [local instance] preservesFiniteLimits_extendScalars_algebraMap

omit [Module.Flat D C] in
/-- **The second morphism descends, at chain level.** The functoriality map of
[Stacks, Tag 08PN] for the change of base ring `K → B` at `D`, base changed along `D → C` and
followed by the adjoint map of `(𝟙_B, D → C)`, is the adjoint map of `(𝟙_K, D → C)` followed by
the functoriality map for the change of base ring at `C`. Both composites are the adjoint map of
the square `(K → B, D → C)`. -/
theorem flatTower_cotangentComplexBaseRingMap_comp :
    ((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (cotangentComplexBaseRingMap K B D) ≫
        cotangentExtendScalarsComplexMap (A := B) (A' := B) (B := CommAlgCat.of B D)
          (B' := CommAlgCat.of B C) (IsScalarTower.toAlgHom B D C) =
      cotangentExtendScalarsComplexMap (A := K) (A' := K) (B := CommAlgCat.of K D)
          (B' := CommAlgCat.of K C) (IsScalarTower.toAlgHom K D C) ≫
        cotangentComplexBaseRingMap K B C := by
  have hc := squareCotangentComplexMap_comp_counit.{u}
    (displaySquare₁ K D C) (displaySquare₂ K B C)
  have hcomp := squareCotangentComplexMap_comp'.{u} (displaySquare₂ K B D)
    (displaySquare₁ B D C)
  simp only [cotangentExtendScalarsComplexMap_eq_counit]
  refine Eq.trans ?_ hc
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ ModuleCat.extendRestrictScalarsAdjCounitComplex
      (algebraMap D C) (ComplexShape.up ℤ) (cotangentComplex.{u, u} B (CommAlgCat.of B C)))
    (((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp _ _).symm) ?_
  exact congrArg (fun z =>
      ((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map z ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (algebraMap D C) (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} B (CommAlgCat.of B C)))
    hcomp.symm

/-- **The second displayed morphism descends along a flat base change.** For towers
`K → B → D → C` with `D → C` flat, the second displayed morphism `L_{D/K} ⟶ L_{D/B}`, base
changed to `C` and followed by `L_{D/B} ⊗_D C ⟶ L_{C/B}`, is `L_{D/K} ⊗_D C ⟶ L_{C/K}` followed
by the second displayed morphism `L_{C/K} ⟶ L_{C/B}`. -/
theorem flatTowerVertexMap_fundamentalMor₂ :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.map
          (fundamentalMor₂.{u} K B D) ≫ flatTowerVertexMap B D C =
      flatTowerVertexMap K D C ≫ fundamentalMor₂.{u} K B C := by
  have hkey := (ModuleCat.extendScalars.{u, u, u}
      (algebraMap D C)).mapDerivedCategoryFactors_hom_app_comp
    (cotangentComplexBaseRingMap K B D)
    (cotangentExtendScalarsComplexMap (A := B) (A' := B) (B := CommAlgCat.of B D)
      (B' := CommAlgCat.of B C) (IsScalarTower.toAlgHom B D C))
  rw [flatTowerVertexMap, flatTowerVertexMap, fundamentalMor₂, fundamentalMor₂]
  simp only [Category.assoc]
  rw [hkey]
  exact whisker_eq _ ((congrArg DerivedCategory.Q.map
    (flatTower_cotangentComplexBaseRingMap_comp K B D C)).trans (DerivedCategory.Q.map_comp _ _))

end SecondMorphism

section Cone

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (B : Type u) [CommRing B] [Algebra R B]
  (D : Type u) [CommRing D] [Algebra R D] [Algebra A D] [Algebra B D]
  [IsScalarTower R A D] [IsScalarTower R B D]
  (C : Type u) [CommRing C] [Algebra D C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R D C] [IsScalarTower A D C] [IsScalarTower B D C]
  [IsScalarTower R A C] [IsScalarTower R B C] [Module.Flat D C]

attribute [local instance] preservesFiniteLimits_extendScalars_algebraMap

/-- **The map `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` is the flat base change of
`L_{B/R} ⊗^𝐋_B D ⟶ L_{D/A}`.** For towers `R → B → D → C` and `R → A → D → C` with `D → C` flat,
the composite of the first displayed morphism of `R → B → C` with the second displayed morphism
of `R → A → C` is the base change along `D → C` of the corresponding composite for `D`, read
through `CommAlgCat.flatTowerVertex₁Iso` and `L_{D/A} ⊗_D C ⟶ L_{C/A}`. -/
theorem flatTowerVertexMap_rightColumn :
    (flatTowerVertex₁Iso R B D C).inv ≫
        (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.map
          (fundamentalMor₁.{u} R B D ≫ fundamentalMor₂.{u} R A D) ≫ flatTowerVertexMap A D C =
      fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C := by
  rw [Functor.map_comp, Category.assoc, flatTowerVertexMap_fundamentalMor₂ R A D C,
    ← Category.assoc, ← Category.assoc, Category.assoc (flatTowerVertex₁Iso R B D C).inv,
    flatTowerVertexMap_fundamentalMor₁ R B D C]

/-- **The cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` is the flat base change of the cone of
`L_{B/R} ⊗^𝐋_B D ⟶ L_{D/A}`**, when `L_{C/D} = 0`. Any two objects completing the two maps to
distinguished triangles are related by base change along `D → C`. -/
theorem nonempty_iso_mapDerivedCategory_cone_of_isZero
    (hL : IsZero (cotangentComplexDerived.{u, u} D (CommAlgCat.of D C)))
    {ED : DerivedCategory (ModuleCat.{u} D)}
    {b : cotangentComplexDerived.{u, u} A (CommAlgCat.of A D) ⟶ ED}
    {e : ED ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B D)⟦(1 : ℤ)⟧}
    (hD : Triangle.mk (fundamentalMor₁.{u} R B D ≫ fundamentalMor₂.{u} R A D) b e ∈
      distTriang (DerivedCategory (ModuleCat.{u} D)))
    {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) :
    Nonempty (EC ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.obj ED) := by
  have := isIso_flatTowerVertexMap_of_isZero A D C hL
  let m := asIso (flatTowerVertexMap A D C)
  obtain ⟨e'', -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _ hC
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategory.map_distinguished
      _ hD)
    (Arrow.isoMk (flatTowerVertex₁Iso R B D C).symm m.symm (by
      change _ = _ ≫ m.inv
      exact (Iso.eq_comp_inv m).2 ((Category.assoc _ _ _).trans
        (flatTowerVertexMap_rightColumn R A B D C))))
  exact ⟨Triangle.π₃.mapIso e''⟩

/-- **Cohomology of the cone along a flat base change.** Under the hypotheses of
`CommAlgCat.nonempty_iso_mapDerivedCategory_cone_of_isZero`, the `i`-th cohomology of the cone
of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` is `H^i(E_D) ⊗_D C`. -/
theorem nonempty_homology_cone_iso_extendScalars_of_isZero
    (hL : IsZero (cotangentComplexDerived.{u, u} D (CommAlgCat.of D C)))
    {ED : DerivedCategory (ModuleCat.{u} D)}
    {b : cotangentComplexDerived.{u, u} A (CommAlgCat.of A D) ⟶ ED}
    {e : ED ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B D)⟦(1 : ℤ)⟧}
    (hD : Triangle.mk (fundamentalMor₁.{u} R B D ≫ fundamentalMor₂.{u} R A D) b e ∈
      distTriang (DerivedCategory (ModuleCat.{u} D)))
    {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj EC ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} D) i).obj ED)) := by
  obtain ⟨φ⟩ := nonempty_iso_mapDerivedCategory_cone_of_isZero R A B D C hL hD hC
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).mapIso φ ≪≫
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryHomologyIso i).app ED⟩

end Cone

section WeaklyEtale

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (B : Type u) [CommRing B] [Algebra R B]
  (D : Type u) [CommRing D] [Algebra R D] [Algebra A D] [Algebra B D]
  [IsScalarTower R A D] [IsScalarTower R B D]
  (C : Type u) [CommRing C] [Algebra D C] [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R D C] [IsScalarTower A D C] [IsScalarTower B D C]
  [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.WeaklyEtale D C]

/-- **Cohomology of the cone along a weakly étale base change.** If `D → C` is weakly étale,
the `i`-th cohomology of any cone of `L_{B/R} ⊗^𝐋_B C ⟶ L_{C/A}` is `H^i(E_D) ⊗_D C` for any cone
`E_D` of `L_{B/R} ⊗^𝐋_B D ⟶ L_{D/A}`: a weakly étale algebra is flat, and its cotangent complex
vanishes by item (7) of [Stacks, Tag 08R2]. This is the computation of the stalks of the object
`E` of Equation 92.28.0.1 in the proof of [Stacks, Tag 09DM], where `C` is the étale local ring
of the fibre product, weakly étale over the tensor product of the other two by
`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`. -/
theorem nonempty_homology_cone_iso_extendScalars_of_weaklyEtale
    {ED : DerivedCategory (ModuleCat.{u} D)}
    {b : cotangentComplexDerived.{u, u} A (CommAlgCat.of A D) ⟶ ED}
    {e : ED ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B D)⟦(1 : ℤ)⟧}
    (hD : Triangle.mk (fundamentalMor₁.{u} R B D ≫ fundamentalMor₂.{u} R A D) b e ∈
      distTriang (DerivedCategory (ModuleCat.{u} D)))
    {EC : DerivedCategory (ModuleCat.{u} C)}
    {b' : cotangentComplexDerived.{u, u} A (CommAlgCat.of A C) ⟶ EC}
    {e' : EC ⟶ (fundamentalVertex₁.{u, u, u + 1, u + 1} R B C)⟦(1 : ℤ)⟧}
    (hC : Triangle.mk (fundamentalMor₁.{u} R B C ≫ fundamentalMor₂.{u} R A C) b' e' ∈
      distTriang (DerivedCategory (ModuleCat.{u} C))) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj EC ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} D) i).obj ED)) :=
  nonempty_homology_cone_iso_extendScalars_of_isZero R A B D C
    (isZero_cotangentComplexDerived_of_weaklyEtale_unconditional D C) hD hC i

end WeaklyEtale

end CommAlgCat

end
