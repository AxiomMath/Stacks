module

public import StacksFrontier.Cotangent.BaseChangeCompositionCounit
public import StacksFrontier.Cotangent.Localization
public import StacksFrontier.Cotangent.SheavesOfRings.StalkwiseChangeOfBase
public import StacksFrontier.Cotangent.Triangle.ProductDescent
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction

/-!
# The cotangent complex of a square of localizations

Let `A → A'`, `B → B'` be a commutative square of ring maps in which `A' = S⁻¹A` and
`B' = T⁻¹B` are localizations. This file proves that the functoriality map of Tag 08PN,
read as the adjoint map

`B' ⊗_B L_{B/A} ⟶ L_{B'/A'}`,

is a quasi-isomorphism. This is the ring-level input of the stalkwise step of Tag 08T3, where
`B → B'` is `𝒪_X(U) → 𝒪_{X,x}` and `A → A'` is `𝒪_Y(V) → (f⁻¹𝒪_Y)_x`.

The proof factors the map through `L_{B'/A}`. The first factor `B' ⊗_B L_{B/A} ⟶ L_{B'/A}` is
the first displayed morphism of the fundamental triangle of `A → B → B'` (Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished`), whose third vertex `L_{B'/B}` vanishes
because `B → B'` is a localization (Tag 08R2,
`CommAlgCat.isZero_cotangentComplexDerived_localization`), so it is an isomorphism in `D(B')`.
The second factor `L_{B'/A} ⟶ L_{B'/A'}` is the change of base ring along a map with vanishing
cotangent complex (`CommAlgCat.quasiIso_cotangentComplexBaseRingMap_of_isZero`). That the
composite is the map of the square is the composition law
`CommAlgCat.squareCotangentComplexMap_comp_counit`.

## Main definitions

* `CommAlgCat.squareCotangentExtendScalarsMap`: the adjoint map `B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` of
  the functoriality map of a commutative square.

## Main results

* `CommAlgCat.quasiIso_squareCotangentExtendScalarsMap_of_isLocalization`: for a square of
  localizations the adjoint map is a quasi-isomorphism.

## References

* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable {A A' : Type u} [CommRing A] [CommRing A'] {B : CommAlgCat.{u} A}
  {B' : CommAlgCat.{u} A'}

/-- The adjoint map `B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` of the functoriality map of Tag 08PN for a
commutative square of ring maps: extension of scalars along `B → B'` of the `B`-linear map,
followed by the counit. -/
abbrev squareCotangentExtendScalarsMap (sq : AlgebraSquare.{u, u, u} A A' B B') :
    ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, u} A B) ⟶ cotangentComplex.{u, u} A' B' :=
  ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (squareCotangentComplexMap.{u, u, u} sq) ≫
    ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} A' B')

/-- Two commutative squares with the same base map and the same map of algebras are equal. -/
theorem algebraSquare_ext {sq sq' : AlgebraSquare.{u, u, u} A A' B B'}
    (hbase : sq.base = sq'.base) (hmap : sq.map = sq'.map) : sq = sq' := by
  obtain ⟨b, m, hbm⟩ := sq
  obtain ⟨b', m', hbm'⟩ := sq'
  subst hbase hmap
  rfl

/-- **The cotangent complex of a square of localizations.** If in the commutative square
`A → A'`, `B → B'` the ring `A'` is a localization of `A` and `B'` is a localization of `B`,
then the adjoint functoriality map `B' ⊗_B L_{B/A} ⟶ L_{B'/A'}` is a quasi-isomorphism. -/
theorem quasiIso_squareCotangentExtendScalarsMap_of_isLocalization
    (sq : AlgebraSquare.{u, u, u} A A' B B') (S : Submonoid A) (T : Submonoid B)
    (hA : @IsLocalization A _ S A' _ sq.base.toAlgebra)
    (hB : @IsLocalization B _ T B' _ sq.map.toAlgebra) :
    QuasiIso (squareCotangentExtendScalarsMap sq) := by
  let iAA' : Algebra A A' := sq.base.toAlgebra
  let iBB' : Algebra B B' := sq.map.toAlgebra
  let iAB' : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq fun a => (sq.map_algebraMap a).symm
  let b : (B : Type u) →ₐ[A] (B' : Type u) := IsScalarTower.toAlgHom A B B'
  -- The first factor `B' ⊗_B L_{B/A} ⟶ L_{B'/A}`.
  have hE : QuasiIso (cotangentExtendScalarsComplexMap (A := A) (A' := A)
      (B := CommAlgCat.of A B) (B' := CommAlgCat.of A B') b) := by
    have h1 : IsIso (fundamentalMor₁.{u} A (B : Type u) (B' : Type u)) :=
      (Triangle.isZero₃_iff_isIso₁ _
        (productFundamentalTriangle_distinguished A (B : Type u) (B' : Type u))).1
        (isZero_cotangentComplexDerived_localization (B : Type u) T (B' : Type u))
    have h2 : IsIso (DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (A := A) (A' := A)
        (B := CommAlgCat.of A B) (B' := CommAlgCat.of A B') b)) :=
      @IsIso.of_isIso_comp_left _ _ _ _ _
        (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) (B' : Type u)).hom _
        _ h1
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 h2
  -- The composite is the map of the square.
  have heq : squareCotangentExtendScalarsMap sq =
      cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
          (B' := CommAlgCat.of A B') b ≫
        cotangentComplexBaseRingMap A A' (B' : Type u) := by
    rw [cotangentExtendScalarsComplexMap_eq_counit]
    exact squareCotangentComplexMap_comp_counit
      (algebraSquareOfAlgHom (A := A) (A' := A) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of A B') b) (displaySquare₂ A A' (B' : Type u))
  rw [heq]
  exact quasiIso_comp _ _ (hφ := hE) (hφ' := quasiIso_cotangentComplexBaseRingMap_of_isZero A A'
    (B' : Type u) (isZero_cotangentComplexDerived_localization A S A'))

/-- **The identity square induces the identity.** The map of cotangent complexes of abelian
groups attached to the identity square of `A → B` is the identity. -/
theorem cotangentComplexAbMap_algebraSquareId (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    cotangentComplexAbMap.{u, u, u} (AlgebraSquare.id.{u, u} A B) = 𝟙 _ := by
  ext degree x
  by_cases hdegree : 0 < degree
  · obtain rfl : x = 0 := (ModuleCat.isZero_iff_subsingleton.mp
      (cotangentComplex_isZero_pos.{u, u} A B degree hdegree)).elim _ _
    simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, degree = -(n : ℤ) := ⟨(-degree).toNat, by omega⟩
    set e := cotangentComplex_degreeIso.{u, u} A B n
    set mapId := (squareFunctoriality.{u, u, u} (AlgebraSquare.id.{u, u} A B)).complexMap.f
      (-(n : ℤ))
    have heq : e.inv ≫ mapId =
        e.inv ≫ (ModuleCat.restrictScalarsId'App (AlgebraSquare.id.{u, u} A B).map rfl
          ((cotangentComplex.{u, u} A B).X (-(n : ℤ)))).inv := by
      refine cotangentTerm_hom_ext.{u, u} _ _ _ _ _ fun p => ?_
      have hp :=
        (squareFunctoriality.{u, u, u} (AlgebraSquare.id.{u, u} A B)).complexMap_differential n p
      rw [squareFunctoriality_resolution_id.{u, u}] at hp
      exact CategoryTheory.Sheaf.eq_inv_apply_of_hom_apply_eq' e hp
    exact ConcreteCategory.congr_hom ((cancel_epi e.inv).mp heq) x

variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] {B₁ : CommAlgCat.{u} A₁}
  {B₂ : CommAlgCat.{u} A₂}

/-- A pair of mutually inverse commutative squares of ring maps induces an isomorphism of
cotangent complexes of abelian groups. -/
def cotangentComplexAbIsoOfSquares (sq : AlgebraSquare.{u, u, u} A₁ A₂ B₁ B₂)
    (sq' : AlgebraSquare.{u, u, u} A₂ A₁ B₂ B₁) (h₁ : sq.comp sq' = AlgebraSquare.id.{u, u} A₁ B₁)
    (h₂ : sq'.comp sq = AlgebraSquare.id.{u, u} A₂ B₂) :
    cotangentComplexAb.{u, u} A₁ B₁ ≅ cotangentComplexAb.{u, u} A₂ B₂ where
  hom := cotangentComplexAbMap.{u, u, u} sq
  inv := cotangentComplexAbMap.{u, u, u} sq'
  hom_inv_id := by
    rw [← cotangentComplexAbMap_comp, h₁, cotangentComplexAbMap_algebraSquareId]
  inv_hom_id := by
    rw [← cotangentComplexAbMap_comp, h₂, cotangentComplexAbMap_algebraSquareId]

end CommAlgCat

end
