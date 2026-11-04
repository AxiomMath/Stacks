module

public import Mathlib.Algebra.Exact.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.HomDoubleComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the rows and columns of the Hom double complex

Every row and every column of the double complex of morphism groups attached to a pair of
distinguished triangles is exact. This is the long exact sequence of a distinguished triangle in
both variables: three consecutive transition maps of a periodic sequence are the three maps of a
distinguished triangle, so pre- and postcomposition with them give exact sequences of morphism
groups.

## Main results

* `AlgebraicGeometry.HomDoubleComplexSetup.d₁_exact`: every row is exact.
* `AlgebraicGeometry.HomDoubleComplexSetup.d₂_exact`: every column is exact.

## Implementation notes

Exactness is expressed for the underlying maps of additive groups, as `Function.Exact`. The two
assertions are kept separate so that either direction of the double complex can be used on its
own. Both reduce to the exactness of pre- or postcomposition along a distinguished triangle,
proved for each of the three residues of the degree modulo three.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.HomDoubleComplexSetup

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Exactness of postcomposition is invariant under conjugating the maps by isomorphisms. -/
private lemma exact_postcomp_of_iso {C' : Type*} [Category C'] [Preadditive C']
    {X A A' B B' D D' : C'} (eA : A' ≅ A) (eB : B' ≅ B) (eD : D' ≅ D) (f : A ⟶ B) (g : B ⟶ D)
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} (hf : f' = eA.hom ≫ f ≫ eB.inv)
    (hg : g' = eB.hom ≫ g ≫ eD.inv)
    (h : Function.Exact (fun x : X ⟶ A => x ≫ f) (fun y => y ≫ g)) :
    Function.Exact (fun x : X ⟶ A' => x ≫ f') (fun y => y ≫ g') := by
  subst hf hg
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h (y ≫ eB.hom)).1 (by simpa using congrArg (· ≫ eD.hom) hy)
    refine ⟨x ≫ eA.inv, ?_⟩
    simp [reassoc_of% (hx : x ≫ f = y ≫ eB.hom)]
  · rintro ⟨x, rfl⟩
    have h₀ : ((x ≫ eA.hom) ≫ f) ≫ g = 0 := (h _).2 ⟨x ≫ eA.hom, rfl⟩
    simp only [Category.assoc] at h₀
    simp [reassoc_of% h₀]

/-- Exactness of precomposition is invariant under conjugating the maps by isomorphisms. -/
private lemma exact_precomp_of_iso {C' : Type*} [Category C'] [Preadditive C']
    {X A A' B B' D D' : C'} (eA : A' ≅ A) (eB : B' ≅ B) (eD : D' ≅ D) (f : A ⟶ B) (g : B ⟶ D)
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} (hf : f' = eA.hom ≫ f ≫ eB.inv)
    (hg : g' = eB.hom ≫ g ≫ eD.inv)
    (h : Function.Exact (fun y : D ⟶ X => g ≫ y) (fun z => f ≫ z)) :
    Function.Exact (fun y : D' ⟶ X => g' ≫ y) (fun z => f' ≫ z) := by
  subst hf hg
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := (h (eB.inv ≫ z)).1 (by simpa using congrArg (eA.inv ≫ ·) hz)
    refine ⟨eD.hom ≫ y, ?_⟩
    simp [(hy : g ≫ y = eB.inv ≫ z)]
  · rintro ⟨y, rfl⟩
    have h₀ : f ≫ g ≫ eD.inv ≫ y = 0 := (h _).2 ⟨eD.inv ≫ y, rfl⟩
    simp [h₀]

/-- Postcomposition with the first two maps of a distinguished triangle is exact. -/
private lemma exact_postcomp_mor₁_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (X : C) :
    Function.Exact (fun x : X ⟶ T.obj₁ => x ≫ T.mor₁) (fun y => y ≫ T.mor₂) := by
  refine fun y => ⟨fun hy => (Triangle.coyoneda_exact₂ T hT y hy).imp fun _ => Eq.symm, ?_⟩
  rintro ⟨x, rfl⟩
  simp [comp_distTriang_mor_zero₁₂ T hT]

/-- Precomposition with the first two maps of a distinguished triangle is exact. -/
private lemma exact_precomp_mor₂_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (X : C) :
    Function.Exact (fun y : T.obj₃ ⟶ X => T.mor₂ ≫ y) (fun z => T.mor₁ ≫ z) := by
  refine fun z => ⟨fun hz => (Triangle.yoneda_exact₂ T hT z hz).imp fun _ => Eq.symm, ?_⟩
  rintro ⟨y, rfl⟩
  simp [reassoc_of% comp_distTriang_mor_zero₁₂ T hT]

/-- In a degree divisible by three, two consecutive transition maps of the periodic sequence are
conjugate to the first two maps of a distinguished triangle. -/
private lemma exists_distTriang_triangleMap_of_eq_three_mul
    (T : Triangle C) (hT : T ∈ distTriang C) (p n : ℤ)
    (h : p = 3 * n) :
    ∃ (R : Triangle C) (_ : R ∈ distTriang C) (eA : triangleObject T p ≅ R.obj₁)
      (eB : triangleObject T (p + 1) ≅ R.obj₂) (eD : triangleObject T (p + 1 + 1) ≅ R.obj₃),
      triangleMap T p = eA.hom ≫ R.mor₁ ≫ eB.inv ∧
        triangleMap T (p + 1) = eB.hom ≫ R.mor₂ ≫ eD.inv := by
  subst h
  let S := (Triangle.shiftFunctor C n).obj T
  let e₀ : triangleObject T (3 * n) ≅ S.obj₁ :=
    eqToIso (by simp [triangleObject, show (3 * n) / 3 = n by omega,
      show (3 * n) % 3 = 0 by omega, S])
  let e₁ : triangleObject T (3 * n + 1) ≅ S.obj₂ :=
    eqToIso (by simp [triangleObject, show (3 * n + 1) / 3 = n by omega,
      show (3 * n + 1) % 3 = 1 by omega, S])
  let e₂ : triangleObject T (3 * n + 1 + 1) ≅ S.obj₃ :=
    eqToIso (by simp [triangleObject, show (3 * n + 1 + 1) / 3 = n by omega,
      show (3 * n + 1 + 1) % 3 = 2 by omega, S])
  exact ⟨S, Triangle.shift_distinguished T hT n, e₀, e₁, e₂,
    by simpa [e₀, e₁, S] using triangleMap_of_eq_three_mul T (3 * n) n rfl,
    by simpa [e₁, e₂, S] using triangleMap_of_eq_three_mul_add_one T (3 * n + 1) n rfl⟩

/-- In a degree congruent to one modulo three, two consecutive transition maps of the periodic
sequence are conjugate to the first two maps of a distinguished triangle. -/
private lemma exists_distTriang_triangleMap_of_eq_three_mul_add_one
    (T : Triangle C) (hT : T ∈ distTriang C) (p n : ℤ)
    (h : p = 3 * n + 1) :
    ∃ (R : Triangle C) (_ : R ∈ distTriang C) (eA : triangleObject T p ≅ R.obj₁)
      (eB : triangleObject T (p + 1) ≅ R.obj₂) (eD : triangleObject T (p + 1 + 1) ≅ R.obj₃),
      triangleMap T p = eA.hom ≫ R.mor₁ ≫ eB.inv ∧
        triangleMap T (p + 1) = eB.hom ≫ R.mor₂ ≫ eD.inv := by
  subst h
  let S := (Triangle.shiftFunctor C n).obj T
  let α := shiftFunctorAdd' C n (1 : ℤ) (n + 1) rfl
  let e₀ : triangleObject T (3 * n + 1) ≅ S.obj₂ :=
    eqToIso (by simp [triangleObject, show (3 * n + 1) / 3 = n by omega,
      show (3 * n + 1) % 3 = 1 by omega, S])
  let e₁ : triangleObject T (3 * n + 1 + 1) ≅ S.obj₃ :=
    eqToIso (by simp [triangleObject, show (3 * n + 1 + 1) / 3 = n by omega,
      show (3 * n + 1 + 1) % 3 = 2 by omega, S])
  let e₂ : triangleObject T (3 * n + 1 + 1 + 1) ≅ (shiftFunctor C (n + 1)).obj T.obj₁ :=
    eqToIso (by simp [triangleObject, show (3 * n + 1 + 1 + 1) / 3 = n + 1 by omega,
      show (3 * n + 1 + 1 + 1) % 3 = 0 by omega])
  exact ⟨S.rotate, rot_of_distTriang S (Triangle.shift_distinguished T hT n), e₀, e₁,
    e₂ ≪≫ α.app T.obj₁,
    (by simpa [e₀, e₁] using triangleMap_of_eq_three_mul_add_one T (3 * n + 1) n rfl :
      triangleMap T _ = e₀.hom ≫ S.mor₂ ≫ e₁.inv),
    (by simpa [e₁, e₂, α] using
        triangleMap_of_eq_three_mul_add_two T (3 * n + 1 + 1) n (by omega) :
      triangleMap T _ = e₁.hom ≫ S.mor₃ ≫ α.inv.app T.obj₁ ≫ e₂.inv)⟩

/-- In a degree congruent to two modulo three, two consecutive transition maps of the periodic
sequence are conjugate to the first two maps of a distinguished triangle. -/
private lemma exists_distTriang_triangleMap_of_eq_three_mul_add_two
    (T : Triangle C) (hT : T ∈ distTriang C) (p n : ℤ)
    (h : p = 3 * n + 2) :
    ∃ (R : Triangle C) (_ : R ∈ distTriang C) (eA : triangleObject T p ≅ R.obj₁)
      (eB : triangleObject T (p + 1) ≅ R.obj₂) (eD : triangleObject T (p + 1 + 1) ≅ R.obj₃),
      triangleMap T p = eA.hom ≫ R.mor₁ ≫ eB.inv ∧
        triangleMap T (p + 1) = eB.hom ≫ R.mor₂ ≫ eD.inv := by
  subst h
  let S := (Triangle.shiftFunctor C n).obj T
  let U := (Triangle.shiftFunctor C n ⋙ Triangle.shiftFunctor C 1).obj T
  let V := (Triangle.shiftFunctor C (n + 1)).obj T
  let R : Triangle C := Triangle.mk S.mor₂ S.mor₃ (-(shiftFunctor C (1 : ℤ)).map S.mor₁)
  let β := Triangle.shiftFunctorAdd' C n (1 : ℤ) (n + 1) rfl
  have hR : R ∈ distTriang C := by
    simpa [R, Triangle.rotate] using rot_of_distTriang S (Triangle.shift_distinguished T hT n)
  let ε₁ : V.obj₁ ≅ R.obj₃ := ⟨(β.hom.app T).hom₁, (β.inv.app T).hom₁,
    Iso.hom_inv_id_triangle_hom₁ (β.app T), Iso.inv_hom_id_triangle_hom₁ (β.app T)⟩
  let ε₂ : V.obj₂ ≅ (shiftFunctor C (1 : ℤ)).obj R.obj₁ := ⟨(β.hom.app T).hom₂,
    (β.inv.app T).hom₂, Iso.hom_inv_id_triangle_hom₂ (β.app T),
    Iso.inv_hom_id_triangle_hom₂ (β.app T)⟩
  let e₀ : triangleObject T (3 * n + 2) ≅ S.obj₃ :=
    eqToIso (by simp [triangleObject, show (3 * n + 2) / 3 = n by omega,
      show (3 * n + 2) % 3 = 2 by omega, S])
  let e₁ : triangleObject T (3 * n + 2 + 1) ≅ V.obj₁ :=
    eqToIso (by simp [triangleObject, show (3 * n + 2 + 1) / 3 = n + 1 by omega,
      show (3 * n + 2 + 1) % 3 = 0 by omega, V])
  let e₂ : triangleObject T (3 * n + 2 + 1 + 1) ≅ V.obj₂ :=
    eqToIso (by simp [triangleObject, show (3 * n + 2 + 1 + 1) / 3 = n + 1 by omega,
      show (3 * n + 2 + 1 + 1) % 3 = 1 by omega, V])
  have hUR : U.mor₁ = R.mor₃ := by
    dsimp [U, R, Triangle.shiftFunctor]
    simp [S, Triangle.shiftFunctor]
    rfl
  have hbridge : ε₁.hom ≫ R.mor₃ = V.mor₁ ≫ ε₂.hom := by
    rw [← hUR]
    exact (β.hom.app T).comm₁.symm
  have hm₁ : triangleMap T (3 * n + 2 + 1) = e₁.hom ≫ V.mor₁ ≫ e₂.inv := by
    simpa [e₁, e₂, V] using triangleMap_of_eq_three_mul T (3 * n + 2 + 1) (n + 1) (by omega)
  exact ⟨R.rotate, rot_of_distTriang R hR, e₀, e₁ ≪≫ ε₁, e₂ ≪≫ ε₂,
    (triangleMap_of_eq_three_mul_add_two T (3 * n + 2) n rfl :
      triangleMap T _ = e₀.hom ≫ R.mor₂ ≫ (e₁ ≪≫ ε₁).inv),
    (by rw [hm₁]; simp [reassoc_of% hbridge] :
      triangleMap T _ = (e₁ ≪≫ ε₁).hom ≫ R.mor₃ ≫ (e₂ ≪≫ ε₂).inv)⟩

/-- Two consecutive transition maps of the periodic sequence of a distinguished triangle are
conjugate to the first two maps of a distinguished triangle. -/
private lemma exists_distTriang_triangleMap (T : Triangle C) (hT : T ∈ distTriang C) (p : ℤ) :
    ∃ (R : Triangle C) (_ : R ∈ distTriang C) (eA : triangleObject T p ≅ R.obj₁)
      (eB : triangleObject T (p + 1) ≅ R.obj₂) (eD : triangleObject T (p + 1 + 1) ≅ R.obj₃),
      triangleMap T p = eA.hom ≫ R.mor₁ ≫ eB.inv ∧
        triangleMap T (p + 1) = eB.hom ≫ R.mor₂ ≫ eD.inv := by
  obtain h | h | h : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  · exact exists_distTriang_triangleMap_of_eq_three_mul T hT p (p / 3) (by omega)
  · exact exists_distTriang_triangleMap_of_eq_three_mul_add_one T hT p (p / 3) (by omega)
  · exact exists_distTriang_triangleMap_of_eq_three_mul_add_two T hT p (p / 3) (by omega)

/-- Postcomposition with two consecutive transition maps of the periodic sequence of a
distinguished triangle is exact. -/
private lemma postcomp_triangleMap_exact (T : Triangle C) (hT : T ∈ distTriang C) (p : ℤ)
    (X : C) :
    Function.Exact (fun f : X ⟶ triangleObject T p => f ≫ triangleMap T p)
      (fun f => f ≫ triangleMap T (p + 1)) := by
  obtain ⟨R, hR, eA, eB, eD, hf, hg⟩ := exists_distTriang_triangleMap T hT p
  exact exact_postcomp_of_iso eA eB eD _ _ hf hg (exact_postcomp_mor₁_mor₂ R hR X)

/-- Precomposition with two consecutive transition maps of the periodic sequence of a
distinguished triangle is exact. -/
private lemma precomp_triangleMap_exact (T : Triangle C) (hT : T ∈ distTriang C) (p : ℤ)
    (X : C) :
    Function.Exact (fun f : triangleObject T (p + 1 + 1) ⟶ X => triangleMap T (p + 1) ≫ f)
      (fun f => triangleMap T p ≫ f) := by
  obtain ⟨R, hR, eA, eB, eD, hf, hg⟩ := exists_distTriang_triangleMap T hT p
  exact exact_precomp_of_iso eA eB eD _ _ hf hg (exact_precomp_mor₂_mor₁ R hR X)

/-- Consecutive horizontal differentials in the Hom double complex are exact. -/
@[stacks 0H8B "exact_rows_columns"]
theorem d₁_exact (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    Function.Exact (K.d₁ p q) (K.d₁ (p + 1) q) :=
  exact_precomp_of_iso (Iso.refl (triangleObject K.X (-(p + 1 + 1))))
    (eqToIso (congrArg (triangleObject K.X) (by omega : -(p + 1) = -(p + 1 + 1) + 1)))
    (eqToIso (congrArg (triangleObject K.X) (by omega : -p = -(p + 1 + 1) + 1 + 1)))
    (triangleMap K.X (-(p + 1 + 1))) (triangleMap K.X (-(p + 1 + 1) + 1))
    (f' := triangleMap K.X (-(p + 1 + 1)) ≫
      eqToHom (congrArg (triangleObject K.X) (by omega : -(p + 1 + 1) + 1 = -(p + 1))))
    (g' := triangleMap K.X (-(p + 1)) ≫
      eqToHom (congrArg (triangleObject K.X) (by omega : -(p + 1) + 1 = -p)))
    (Category.id_comp _).symm (triangleMap_eqToHom K.X (by omega) (by omega))
    (precomp_triangleMap_exact K.X K.X_distinguished _ _)

/-- Consecutive vertical differentials in the Hom double complex are exact. -/
@[stacks 0H8B "exact_rows_columns"]
theorem d₂_exact (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    Function.Exact (K.d₂ p q) (K.d₂ p (q + 1)) :=
  postcomp_triangleMap_exact K.Y K.Y_distinguished q (K.XObject (-p))

end AlgebraicGeometry.HomDoubleComplexSetup
