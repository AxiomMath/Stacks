module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.TensorProductDifferentials
public import StacksFrontier.Cotangent.Triangle.BaseChangeComparison

/-!
# Functoriality of the complex of an augmented simplicial algebra in the base

For a ring `R` and an `R`-algebra `D`, an augmented simplicial `R`-algebra `ε : P_• ⟶ D` has the
complex `Ω[P_•⁄R] ⊗_{P_•} D` of `CommAlgCat.augmentedCotangentCochainComplex`. This file makes
it functorial in a commutative square of bases `R → R'`, `D → D'`: a map of simplicial rings
`P_• ⟶ P'_•` compatible with the two structure maps and the two augmentations induces a
`D`-linear map `Ω[P_•⁄R] ⊗ D ⟶ Ω[P'_•⁄R'] ⊗ D'`, given on pure differentials by
`1 ⊗ d p ↦ 1 ⊗ d (φ p)`.

## Main definitions

* `CommAlgCat.overDifferentialsSquareMap`: the map of base-changed differentials of a single
  algebra over a square of bases.
* `CommAlgCat.augmentedCotangentSquareMap`: the induced map of complexes.

## Main results

* `CommAlgCat.overDifferentialsSquareMap_mk`: the map sends `1 ⊗ d p` to `1 ⊗ d (φ p)`.
* `CommAlgCat.augmentedCotangentSquareMap_f_mk`: the same, for the map of complexes in every
  cohomological degree.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe u

namespace CommAlgCat

variable {R R' : Type u} [CommRing R] [CommRing R'] {D : CommAlgCat.{u} R} {D' : CommAlgCat.{u} R'}
  (sq : AlgebraSquare.{u, u, u} R R' D D')

section Single

variable {X : Over D} {X' : Over D'} (φ : (X.left : Type u) →+* (X'.left : Type u))
  (hφR : ∀ r : R, φ (algebraMap R (X.left : Type u) r) =
    algebraMap R' (X'.left : Type u) (sq.base r))
  (hφD : ∀ x, augmentationRingHom X' (φ x) = sq.map (augmentationRingHom X x))

/-- The `D`-linear map `D ⊗_P Ω[P⁄R] ⟶ D' ⊗_{P'} Ω[P'⁄R']` induced by a ring map `φ : P ⟶ P'`
over a commutative square of bases, `1 ⊗ d p ↦ 1 ⊗ d (φ p)`. -/
noncomputable def overDifferentialsSquareMap :
    overDifferentials X ⟶ (ModuleCat.restrictScalars sq.map).obj (overDifferentials X') :=
  overDifferentialsDesc X
    (N := (ModuleCat.restrictScalars sq.map).obj (overDifferentials X'))
    (AddMonoidHom.mk' (fun p => overDifferentialsMk X' (φ p)) fun p q => by
      rw [map_add, overDifferentialsMk_add]
      rfl)
    (fun r => by
      change overDifferentialsMk X' (φ (algebraMap R (X.left : Type u) r)) = 0
      rw [hφR, overDifferentialsMk_algebraMap])
    (fun p q => by
      change overDifferentialsMk X' (φ (p * q)) =
        sq.map (augmentationRingHom X p) • overDifferentialsMk X' (φ q) +
          sq.map (augmentationRingHom X q) • overDifferentialsMk X' (φ p)
      rw [map_mul, overDifferentialsMk_mul, hφD, hφD])

/-- The map of base-changed differentials over a square sends `1 ⊗ d p` to `1 ⊗ d (φ p)`. -/
@[simp]
theorem overDifferentialsSquareMap_mk (p : (X.left : Type u)) :
    overDifferentialsSquareMap sq φ hφR hφD (overDifferentialsMk X p) =
      overDifferentialsMk X' (φ p) :=
  overDifferentialsDesc_mk _ _ _ _ p

end Single

section Simplicial

variable {P : SimplicialObject (CommAlgCat.{u} R)} {P' : SimplicialObject (CommAlgCat.{u} R')}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj D)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} R')).obj D')
  (φ : ∀ n, (P.obj n : Type u) →+* (P'.obj n : Type u))
  (hφR : ∀ n (r : R), φ n (algebraMap R (P.obj n : Type u) r) =
    algebraMap R' (P'.obj n : Type u) (sq.base r))
  (hφD : ∀ n x, (ε'.app n) (φ n x) = sq.map ((ε.app n) x))
  (hφnat : ∀ {i j : SimplexCategoryᵒᵖ} (k : i ⟶ j) (x : (P.obj i : Type u)),
    φ j (P.map k x) = P'.map k (φ i x))

/-- The map of base-changed differentials over a square of bases in simplicial degree `n`. -/
noncomputable def augmentedCotangentSquareTermMap (n : SimplexCategoryᵒᵖ) :
    overDifferentials ((resolutionOver ε).obj n) ⟶
      (ModuleCat.restrictScalars sq.map).obj (overDifferentials ((resolutionOver ε').obj n)) :=
  overDifferentialsSquareMap (X := (resolutionOver ε).obj n) (X' := (resolutionOver ε').obj n)
    sq (φ n) (hφR n) (hφD n)

/-- In simplicial degree `n` the map over a square sends `1 ⊗ d p` to `1 ⊗ d (φ p)`. -/
theorem augmentedCotangentSquareTermMap_mk (n : SimplexCategoryᵒᵖ)
    (p : (((resolutionOver ε).obj n).left : Type u)) :
    augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD n
        (overDifferentialsMk ((resolutionOver ε).obj n) p) =
      overDifferentialsMk ((resolutionOver ε').obj n) (φ n p) :=
  overDifferentialsSquareMap_mk _ _ _ _ p

include hφnat in
/-- The degreewise maps of base-changed differentials over a square of bases, as a map of
simplicial `D`-modules. -/
noncomputable def augmentedCotangentSquareSimplicialMap :
    resolutionOver ε ⋙ overDifferentialsFunctor ⟶
      (resolutionOver ε' ⋙ overDifferentialsFunctor) ⋙ ModuleCat.restrictScalars sq.map where
  app n := augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD n
  naturality {i j} k := overDifferentials_hom_ext (X := (resolutionOver ε).obj i)
    (N := (ModuleCat.restrictScalars sq.map).obj (overDifferentials ((resolutionOver ε').obj j)))
    _ _ fun p => by
      change augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD j
          (overDifferentialsFunctor.map ((resolutionOver ε).map k) (overDifferentialsMk _ p)) =
        overDifferentialsFunctor.map ((resolutionOver ε').map k)
          (augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD i (overDifferentialsMk _ p))
      exact (congrArg (augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD j)
        (overDifferentialsFunctor_map_mk _ p)).trans
          ((augmentedCotangentSquareTermMap_mk sq ε ε' φ hφR hφD j _).trans
            ((congrArg (overDifferentialsMk ((resolutionOver ε').obj j)) (hφnat k p)).trans
              ((overDifferentialsFunctor_map_mk ((resolutionOver ε').map k) (φ i p)).symm.trans
                (congrArg (overDifferentialsFunctor.map ((resolutionOver ε').map k))
                  (augmentedCotangentSquareTermMap_mk sq ε ε' φ hφR hφD i p).symm))))

/-- **The map of complexes `Ω[P_•⁄R] ⊗ D ⟶ Ω[P'_•⁄R'] ⊗ D'` induced over a square of bases**, the
target read over `D` along `D → D'`. -/
noncomputable def augmentedCotangentSquareMap :
    augmentedCotangentCochainComplex ε ⟶
      ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (augmentedCotangentCochainComplex ε') :=
  HomologicalComplex.extendMap
      ((alternatingFaceMapComplex (ModuleCat.{u} (D : Type u))).map
          (augmentedCotangentSquareSimplicialMap sq ε ε' φ hφR hφD hφnat) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso
          (ModuleCat.restrictScalars sq.map)).app
            (resolutionOver ε' ⋙ overDifferentialsFunctor)).inv)
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.restrictScalars sq.map)
      ((alternatingFaceMapComplex (ModuleCat.{u} (D' : Type u))).obj
        (resolutionOver ε' ⋙ overDifferentialsFunctor))
      (ComplexShape.embeddingUpIntLE 0)).hom

/-- The pure differential `1 ⊗ d p` in cohomological degree `-n` of
`Ω[P_•⁄R] ⊗_{P_•} D`. -/
noncomputable def augmentedCotangentMk (n : ℕ) (p : (P.obj (op ⦋n⦌) : Type u)) :
    (augmentedCotangentCochainComplex ε).X (-(n : ℤ)) :=
  (((alternatingFaceMapComplex (ModuleCat.{u} (D : Type u))).obj
      (resolutionOver ε ⋙ overDifferentialsFunctor)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp)).inv
    (overDifferentialsMk ((resolutionOver ε).obj (op ⦋n⦌)) p)

/-- Two module maps out of a term of `Ω[P_•⁄R] ⊗ D` agree as soon as they agree on the pure
differentials. -/
theorem augmentedCotangent_hom_ext (n : ℕ) {N : ModuleCat.{u} (D : Type u)}
    (α β : (augmentedCotangentCochainComplex ε).X (-(n : ℤ)) ⟶ N)
    (h : ∀ p, α (augmentedCotangentMk ε n p) = β (augmentedCotangentMk ε n p)) : α = β := by
  refine (cancel_epi (((alternatingFaceMapComplex (ModuleCat.{u} (D : Type u))).obj
      (resolutionOver ε ⋙ overDifferentialsFunctor)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp)).inv).mp ?_
  exact overDifferentials_hom_ext _ _ h

/-- **The map of complexes over a square sends `1 ⊗ d p` to `1 ⊗ d (φ p)`.** -/
theorem augmentedCotangentSquareMap_f_mk (n : ℕ) (p : (P.obj (op ⦋n⦌) : Type u)) :
    (augmentedCotangentSquareMap sq ε ε' φ hφR hφD hφnat).f (-(n : ℤ))
        (augmentedCotangentMk ε n p) =
      augmentedCotangentMk ε' n (φ (op ⦋n⦌) p) := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  rw [augmentedCotangentSquareMap,
    HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ hn]
  change (((alternatingFaceMapComplex (ModuleCat.{u} (D' : Type u))).obj
      (resolutionOver ε' ⋙ overDifferentialsFunctor)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) hn).inv
      (augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD (op ⦋n⦌)
        ((((alternatingFaceMapComplex (ModuleCat.{u} (D : Type u))).obj
          (resolutionOver ε ⋙ overDifferentialsFunctor)).extendXIso
            (ComplexShape.embeddingUpIntLE 0) hn).hom (augmentedCotangentMk ε n p))) = _
  exact congrArg _ ((congrArg (augmentedCotangentSquareTermMap sq ε ε' φ hφR hφD (op ⦋n⦌))
    (Iso.inv_hom_id_apply _ _)).trans (augmentedCotangentSquareTermMap_mk sq ε ε' φ hφR hφD _ p))

end Simplicial

section Resolution

variable {E : CommAlgCat.{u} R} {P P' : SimplicialObject (CommAlgCat.{u} R)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj E)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj E)

/-- The map of complexes induced by a morphism of augmented simplicial algebras sends `1 ⊗ d p`
to `1 ⊗ d (w p)`. -/
theorem resolutionCotangentComplexMap_f_mk (w : P ⟶ P') (hw : w ≫ ε' = ε) (n : ℕ)
    (p : (P.obj (op ⦋n⦌) : Type u)) :
    (resolutionCotangentComplexMap ε ε' w hw).f (-(n : ℤ)) (augmentedCotangentMk ε n p) =
      augmentedCotangentMk ε' n (w.app (op ⦋n⦌) p) := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  rw [resolutionCotangentComplexMap, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ hn]
  have h₁ := Iso.inv_hom_id_apply (((alternatingFaceMapComplex (ModuleCat.{u} (E : Type u))).obj
      (resolutionOver ε ⋙ overDifferentialsFunctor)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) hn)
    (overDifferentialsMk ((resolutionOver ε).obj (op ⦋n⦌)) p)
  have h₂ := overDifferentialsFunctor_map_mk ((resolutionOverMap ε ε' w hw).app (op ⦋n⦌)) p
  exact congrArg (((alternatingFaceMapComplex (ModuleCat.{u} (E : Type u))).obj
      (resolutionOver ε' ⋙ overDifferentialsFunctor)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) hn).inv
    ((congrArg (((alternatingFaceMapComplex (ModuleCat.{u} (E : Type u))).map
      (Functor.whiskerRight (resolutionOverMap ε ε' w hw) overDifferentialsFunctor)).f n) h₁).trans
        h₂)

end Resolution

section Standard

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A} (f : B ⟶ C)

/-- The identification `Ω[R_•⁄B] ⊗ C ≅ L_{C/B}` of the standard resolution sends `1 ⊗ d r` to the
pure differential `1 ⊗ d r` of the cotangent complex. -/
theorem standardCotangentComplexIso_hom_f_mk (n : ℕ)
    (r : ((standardResolution.{u, u} (B : Type u) (algebraOver f)).left.obj (op ⦋n⦌) : Type u)) :
    (standardCotangentComplexIso f).hom.f (-(n : ℤ))
        (augmentedCotangentMk (standardResolution.{u, u} (B : Type u) (algebraOver f)).hom n r) =
      (cotangentComplex_degreeIso.{u, u} (B : Type u) (algebraOver f) n).inv
        (cotangentTermDifferential.{u, u} (B : Type u) (algebraOver f) (op ⦋n⦌) r) := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  rw [standardCotangentComplexIso, Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ hn, augmentedCotangentMk]
  exact (congrArg (fun y => (HomologicalComplex.extendXIso
      ((alternatingFaceMapComplex (ModuleCat.{u} (algebraOver f))).obj
        (cotangentSimplicialModule.{u, u} (B : Type u) (algebraOver f)).object)
      (ComplexShape.embeddingUpIntLE 0) hn).inv
        ((((alternatingFaceMapComplex (ModuleCat.{u} (algebraOver f))).mapIso
          (standardResolutionOverDifferentialsIso.{u} (B : Type u) (algebraOver f))).hom.f n) y))
    (Iso.inv_hom_id_apply (HomologicalComplex.extendXIso
      ((alternatingFaceMapComplex (ModuleCat.{u} (algebraOver f))).obj
        (resolutionOver (standardResolution.{u, u} (B : Type u) (algebraOver f)).hom ⋙
          overDifferentialsFunctor)) (ComplexShape.embeddingUpIntLE 0) hn) _))

end Standard

end CommAlgCat

end
