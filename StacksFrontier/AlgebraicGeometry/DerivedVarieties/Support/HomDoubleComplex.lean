module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The Hom double complex attached to two distinguished triangles

A distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in a pretriangulated category extends to a
bi-infinite, three-periodic sequence `… ⟶ Xᵖ ⟶ Xᵖ⁺¹ ⟶ …` in which the object in degree `3n + i`
is the `i`-th object of the triangle shifted by `n`. Given two distinguished triangles, this file
packages the groups of morphisms between the two resulting sequences together with the two maps
obtained by pre- and postcomposition.

## Main definitions

* `AlgebraicGeometry.HomDoubleComplexSetup`: a pair of distinguished triangles.
* `AlgebraicGeometry.HomDoubleComplexSetup.triangleObject` and
  `AlgebraicGeometry.HomDoubleComplexSetup.triangleMap`: the three-periodic sequence of a
  triangle and its transition maps.
* `AlgebraicGeometry.HomDoubleComplexSetup.term`: the morphism group in a bidegree.
* `AlgebraicGeometry.HomDoubleComplexSetup.d₁` and
  `AlgebraicGeometry.HomDoubleComplexSetup.d₂`: its two differentials.

## Implementation notes

The transition maps of the periodic sequence are the morphisms of the shifted triangle. At the
third transition, the standard associativity isomorphism for shifts identifies `(X⟦n⟧)⟦1⟧` with
`X⟦n + 1⟧`, so the construction retains the canonical shift identifications needed by subsequent
periodicity statements.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A pair of distinguished triangles, the input to the Hom double-complex construction. -/
public structure HomDoubleComplexSetup where
  /-- The triangle supplying the first (contravariant) direction. -/
  X : Triangle C
  /-- The triangle supplying the second (covariant) direction. -/
  Y : Triangle C
  /-- The first triangle is distinguished. -/
  X_distinguished : X ∈ distTriang C
  /-- The second triangle is distinguished. -/
  Y_distinguished : Y ∈ distTriang C

namespace HomDoubleComplexSetup

/-- The object in degree `p` of the three-periodic sequence associated to a triangle. -/
@[implicit_reducible]
public noncomputable def triangleObject (T : Triangle C) (p : ℤ) : C :=
  let S := (Triangle.shiftFunctor C (p / 3)).obj T
  if p % 3 = 0 then S.obj₁ else if p % 3 = 1 then S.obj₂ else S.obj₃

/-- The map from degree `p` to degree `p+1` in the three-periodic sequence associated
to a triangle. -/
@[implicit_reducible]
public noncomputable def triangleMap (T : Triangle C) (p : ℤ) :
    triangleObject T p ⟶ triangleObject T (p + 1) := by
  let n := p / 3
  let S := (Triangle.shiftFunctor C n).obj T
  by_cases h₀ : p % 3 = 0
  · have hs : triangleObject T p = S.obj₁ := by simp [triangleObject, S, n, h₀]
    have ht : triangleObject T (p + 1) = S.obj₂ := by
      simp [triangleObject, S, n, show (p + 1) / 3 = p / 3 by omega,
        show (p + 1) % 3 = 1 by omega]
    exact eqToHom hs ≫ S.mor₁ ≫ eqToHom ht.symm
  · by_cases h₁ : p % 3 = 1
    · have hs : triangleObject T p = S.obj₂ := by simp [triangleObject, S, n, h₁]
      have ht : triangleObject T (p + 1) = S.obj₃ := by
        simp [triangleObject, S, n, show (p + 1) / 3 = p / 3 by omega,
          show (p + 1) % 3 = 2 by omega]
      exact eqToHom hs ≫ S.mor₂ ≫ eqToHom ht.symm
    · have hs : triangleObject T p = S.obj₃ := by simp [triangleObject, S, n, h₀, h₁]
      have ht : triangleObject T (p + 1) =
          (shiftFunctor C (n + 1)).obj T.obj₁ := by
        simp [triangleObject, n, show (p + 1) / 3 = p / 3 + 1 by omega,
          show (p + 1) % 3 = 0 by omega]
      exact eqToHom hs ≫ S.mor₃ ≫
        (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ ≫ eqToHom ht.symm

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Reindexing a transition map of the periodic sequence along an equality of degrees. -/
public lemma triangleMap_eqToHom (T : Triangle C) {i j k : ℤ} (h : i = j) (hk : j + 1 = k) :
    triangleMap T i ≫ eqToHom (congrArg (triangleObject T) (show i + 1 = k by omega)) =
      eqToHom (congrArg (triangleObject T) h) ≫ triangleMap T j ≫
        eqToHom (congrArg (triangleObject T) hk) := by
  cases h
  cases hk
  simp

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- In a degree divisible by three, the transition map of the periodic sequence is the first map
of the shifted triangle. -/
public lemma triangleMap_of_eq_three_mul (T : Triangle C) (p n : ℤ) (h : p = 3 * n) :
    triangleMap T p =
      eqToHom (by
        have hn : p / 3 = n := by omega
        have hr : p % 3 = 0 := by omega
        simp [triangleObject, hn, hr]) ≫
        ((Triangle.shiftFunctor C n).obj T).mor₁ ≫
        eqToHom (by
          have hn : (p + 1) / 3 = n := by omega
          have hr : (p + 1) % 3 = 1 := by omega
          simp [triangleObject, hn, hr]) := by
  have hr : p % 3 = 0 := by omega
  have hr' : (p + 1) % 3 = 1 := by omega
  obtain rfl : p / 3 = n := by omega
  simp [triangleMap, triangleObject, hr, hr']

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- In a degree congruent to one modulo three, the transition map of the periodic sequence is the
second map of the shifted triangle. -/
public lemma triangleMap_of_eq_three_mul_add_one (T : Triangle C) (p n : ℤ) (h : p = 3 * n + 1) :
    triangleMap T p =
      eqToHom (by
        have hn : p / 3 = n := by omega
        have hr : p % 3 = 1 := by omega
        simp [triangleObject, hn, hr]) ≫
        ((Triangle.shiftFunctor C n).obj T).mor₂ ≫
        eqToHom (by
          have hn : (p + 1) / 3 = n := by omega
          have hr : (p + 1) % 3 = 2 := by omega
          simp [triangleObject, hn, hr]) := by
  have hr : p % 3 = 1 := by omega
  have hr' : (p + 1) % 3 = 2 := by omega
  obtain rfl : p / 3 = n := by omega
  simp [triangleMap, triangleObject, hr, hr']

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- In a degree congruent to two modulo three, the transition map of the periodic sequence is the
third map of the shifted triangle, followed by the shift identification. -/
public lemma triangleMap_of_eq_three_mul_add_two (T : Triangle C) (p n : ℤ) (h : p = 3 * n + 2) :
    triangleMap T p =
      eqToHom (by
        have hn : p / 3 = n := by omega
        have hr : p % 3 = 2 := by omega
        simp [triangleObject, hn, hr]) ≫
        ((Triangle.shiftFunctor C n).obj T).mor₃ ≫
        (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ ≫
        eqToHom (by
          have hn : (p + 1) / 3 = n + 1 := by omega
          have hr : (p + 1) % 3 = 0 := by omega
          simp [triangleObject, hn, hr]) := by
  have hr : p % 3 = 2 := by omega
  have hr' : (p + 1) % 3 = 0 := by omega
  obtain rfl : p / 3 = n := by omega
  simp [triangleMap, triangleObject, hr, hr']

/-- The object `X^p` in the extended first triangle. -/
public noncomputable abbrev XObject (K : HomDoubleComplexSetup (C := C)) (p : ℤ) : C :=
  triangleObject K.X p

/-- The object `Y^q` in the extended second triangle. -/
public noncomputable abbrev YObject (K : HomDoubleComplexSetup (C := C)) (q : ℤ) : C :=
  triangleObject K.Y q

/-- The abelian group `K^{p,q} = Hom(X^{-p},Y^q)`. -/
public noncomputable abbrev term (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :=
  K.XObject (-p) ⟶ K.YObject q

/-- The horizontal map, given by precomposition with the preceding map of the extended
first triangle. -/
public noncomputable def d₁ (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    K.term p q →+ K.term (p + 1) q :=
  Preadditive.leftComp _ (triangleMap K.X (-(p + 1)) ≫
    eqToHom (congrArg (triangleObject K.X) (show -(p + 1) + 1 = -p by omega)))

/-- The vertical map, given by postcomposition with the next map of the extended second
triangle. -/
public noncomputable def d₂ (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    K.term p q →+ K.term p (q + 1) :=
  Preadditive.rightComp _ (triangleMap K.Y q)

end HomDoubleComplexSetup

end AlgebraicGeometry

end
