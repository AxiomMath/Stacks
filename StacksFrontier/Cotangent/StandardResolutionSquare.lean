module

public import StacksFrontier.Cotangent.Complex

/-!
# The standard resolution in higher degrees, and squares of ring maps

The standard resolution of `B` over `A` is built from the iterates of the comonad `C ↦ A[C]`, so
passing from simplicial degree `n` to `n + 1` adjoins one layer of variables indexed by the
elements of the degree-`n` term: `P_0 = A[B]` and `P_{n+1} = A[P_n]`. This file records that
identification and names the resulting variables. It also defines commutative squares of ring
maps `A → A'`, `B → B'` and the data of a map of standard resolutions over such a square, taking
variables to variables, together with the induced map of cotangent complexes.

## Main definitions

* `CommAlgCat.standardResolutionSuccAlgEquiv`: the identification of `P_{n+1}` with the polynomial
  algebra `A[P_n]`, the degreewise successor of `CommAlgCat.standardResolutionZeroAlgEquiv`.
* `CommAlgCat.standardResolutionX`: the variable `[q]` of `P_{n+1}` indexed by an element `q`
  of `P_n`.
* `CommAlgCat.AlgebraSquare`: a commutative square of ring maps `A → A'`, `B → B'` compatible with
  the two algebra structures.
* `CommAlgCat.SquareFunctorialityData`: a map of standard resolutions over such a square, taking
  variables to variables, together with the induced map of cotangent complexes.

## Main results

* `CommAlgCat.standardResolution_obj_succ`: `P_{n+1} = A[P_n]` as algebras over `A`.

## References

* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w

namespace CommAlgCat

/-- The degree-`n + 1` term of the standard resolution is the polynomial algebra on the
underlying set of the degree-`n` term. -/
theorem standardResolution_obj_succ (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌) =
      CommAlgCat.of A
        (MvPolynomial ((standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) A) := by
  rw [standardResolution_obj A B (n + 1), standardResolution_obj A B n]
  rfl

/-- The algebra equivalence identifying the degree-`n + 1` term of the standard resolution with
the polynomial algebra `A[P_n]` on the degree-`n` term, the degreewise successor of
`CommAlgCat.standardResolutionZeroAlgEquiv`. -/
noncomputable abbrev standardResolutionSuccAlgEquiv (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌) ≃ₐ[A]
      MvPolynomial ((standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) A :=
  CommAlgCat.algEquivOfIso (eqToIso (standardResolution_obj_succ.{u, v} A B n))

/-- The variable `[q]` of the degree-`n + 1` term of the standard resolution indexed by an
element `q` of the degree-`n` term. -/
noncomputable def standardResolutionX (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ)
    (q : (standardResolution.{u, v} A B).left.obj (op ⦋n⦌)) :
    (standardResolution.{u, v} A B).left.obj (op ⦋n + 1⦌) :=
  (standardResolutionSuccAlgEquiv.{u, v} A B n).symm (MvPolynomial.X q)

/-- A commutative square of ring maps `A → A'`, `B → B'`, whose vertical maps are the algebra
structures `A → B` and `A' → B'`. -/
structure AlgebraSquare (A : Type u) [CommRing A] (A' : Type w) [CommRing A']
    (B : CommAlgCat.{max u w v} A) (B' : CommAlgCat.{max u w v} A') where
  /-- The map of base rings `A → A'`. -/
  base : A →+* A'
  /-- The map of algebras `B → B'`. -/
  map : B →+* B'
  /-- The square commutes: `B → B'` is compatible with the two algebra structures. -/
  map_algebraMap (a : A) : map (algebraMap A B a) = algebraMap A' B' (base a)

/-- The identity square on the algebra `B` over `A`. -/
def AlgebraSquare.id (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    AlgebraSquare.{u, v, u} A A B B where
  base := RingHom.id A
  map := RingHom.id B
  map_algebraMap _ := rfl

/-- The horizontal composition of two commutative squares of ring maps. -/
def AlgebraSquare.comp {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
    {B : CommAlgCat.{max u v} A} {B' : CommAlgCat.{max u v} A'} {B'' : CommAlgCat.{max u v} A''}
    (sq : AlgebraSquare.{u, v, u} A A' B B') (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'') :
    AlgebraSquare.{u, v, u} A A'' B B'' where
  base := sq'.base.comp sq.base
  map := sq'.map.comp sq.map
  map_algebraMap a := (congrArg sq'.map (sq.map_algebraMap a)).trans (sq'.map_algebraMap _)

/-- The canonical functoriality datum of a commutative square `sq` of ring maps: the map
`P_• → P'_•` of the two standard resolutions over `sq`, which is simplicial and compatible with
the base rings and the augmentations and takes variables to variables, together with the
`B`-linear map of cotangent complexes `L_{B/A} → L_{B'/A'}` that it induces on differentials. -/
structure SquareFunctorialityData {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
    {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}
    (sq : AlgebraSquare.{u, v, w} A A' B B') where
  /-- The induced map `P_n → P'_n` of the two standard resolutions. -/
  resolution (n : SimplexCategoryᵒᵖ) :
    (standardResolution.{u, max w v} A B).left.obj n →+*
      (standardResolution.{w, max u v} A' B').left.obj n
  /-- `P_• → P'_•` is a map of simplicial rings. -/
  resolution_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
      (p : (standardResolution.{u, max w v} A B).left.obj i) :
    resolution j ((standardResolution.{u, max w v} A B).left.map g p) =
      (standardResolution.{w, max u v} A' B').left.map g (resolution i p)
  /-- `P_• → P'_•` is compatible with the maps from the two base rings. -/
  resolution_algebraMap (n : SimplexCategoryᵒᵖ) (a : A) :
    resolution n (algebraMap A ((standardResolution.{u, max w v} A B).left.obj n) a) =
      algebraMap A' ((standardResolution.{w, max u v} A' B').left.obj n) (sq.base a)
  /-- `P_• → P'_•` is compatible with the two augmentations. -/
  resolution_augmentation (n : SimplexCategoryᵒᵖ)
      (p : (standardResolution.{u, max w v} A B).left.obj n) :
    standardResolutionAugmentationHom.{w, max u v} A' B' n (resolution n p) =
      sq.map (standardResolutionAugmentationHom.{u, max w v} A B n p)
  /-- `P_• → P'_•` sends variables to variables in degree zero: the variable `[b]` of
  `P_0 = A[B]` indexed by `b ∈ B` goes to the variable `[sq.map b]` of `P'_0 = A'[B']` indexed by
  its image. -/
  resolution_zero_X (b : B) :
    resolution (op ⦋0⦌)
        ((standardResolutionZeroAlgEquiv.{u, max w v} A B).symm (MvPolynomial.X b)) =
      (standardResolutionZeroAlgEquiv.{w, max u v} A' B').symm
        (MvPolynomial.X (sq.map b))
  /-- `P_• → P'_•` sends variables to variables in every higher degree: the variable `[q]` of
  `P_{n+1} = A[P_n]` indexed by `q ∈ P_n` goes to the variable `[u q]` of `P'_{n+1} = A'[P'_n]`
  indexed by the image of `q`. -/
  resolution_succ_X (n : ℕ)
      (q : (standardResolution.{u, max w v} A B).left.obj (op ⦋n⦌)) :
    resolution (op ⦋n + 1⦌) (standardResolutionX.{u, max w v} A B n q) =
      standardResolutionX.{w, max u v} A' B' n (resolution (op ⦋n⦌) q)
  /-- The induced `B`-linear map of cotangent complexes `L_{B/A} → L_{B'/A'}`. -/
  complexMap : cotangentComplex.{u, max w v} A B ⟶
    ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{w, max u v} A' B')
  /-- In simplicial degree `n` the map of complexes sends `1 ⊗ d p` to `1 ⊗ d (u p)`, where
  `u : P_n → P'_n` is the map of standard resolutions. -/
  complexMap_differential (n : ℕ)
      (p : (standardResolution.{u, max w v} A B).left.obj (op ⦋n⦌)) :
    (cotangentComplex_degreeIso.{w, max u v} A' B' n).hom
        (complexMap.f (-(n : ℤ)) ((cotangentComplex_degreeIso.{u, max w v} A B n).inv
          (cotangentTermDifferential.{u, max w v} A B (op ⦋n⦌) p))) =
      cotangentTermDifferential.{w, max u v} A' B' (op ⦋n⦌) (resolution (op ⦋n⦌) p)

end CommAlgCat

end
