module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# The cone of an endomorphism, and the tower of cones of multiplications

Let `C` be a pre-triangulated category.

If `X --f--> X --g--> Z --h--> X⟦1⟧` is a distinguished triangle whose first morphism is an
*endomorphism* of `X`, then the cone `Z` carries an endomorphism `c` lifting the pair `(f, f)`,
and every such `c` has **square zero**.

In an `R`-linear pre-triangulated category whose shift functors are `R`-linear this specializes
to: **the cone of `r • 𝟙 X` is annihilated by `r ^ 2`**, and more generally the third vertex of
a distinguished triangle whose two other vertices are annihilated by a power of `r` is
annihilated by a power of `r`. Iterating gives the *tower of cones*
`E₀, E₁ = Cone(a₀ • 𝟙 E₀), E₂ = Cone(a₁ • 𝟙 E₁), …`: a power of each of `a₀, …, a_{s-1}`
annihilates the top `E_s`.

## Main results

* `CategoryTheory.Pretriangulated.sq_eq_zero_of_comp_mor₂_eq_zero_of_comp_mor₃_eq_zero`: an
  endomorphism of the third vertex of a distinguished triangle which is killed on both sides by
  the two adjacent morphisms has square zero.
* `CategoryTheory.Pretriangulated.sq_eq_zero_of_cone_endomorphism` and
  `exists_sq_eq_zero_cone_endomorphism`: an endomorphism of the cone of `f : X ⟶ X` lifting
  `(f, f)` has square zero, and one exists.
* `CategoryTheory.Pretriangulated.sq_smul_id_eq_zero_of_cone_smul_id`: the cone of `r • 𝟙 X` is
  annihilated by `r ^ 2`.
* `CategoryTheory.Pretriangulated.pow_smul_id_eq_zero_of_distTriang` and
  `exists_pow_smul_id_eq_zero_of_distTriang`: a power of `r` annihilating two vertices of a
  distinguished triangle gives one annihilating the third.
* `CategoryTheory.Pretriangulated.exists_pow_smul_id_eq_zero_of_coneTower`: the tower of cones
  of multiplications — for every `j < s` a power of `a j` annihilates `E s`.

## References

* [Stacks Project, Tag 05QP](https://stacks.math.columbia.edu/tag/05QP)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **An endomorphism of the third vertex annihilated by the two adjacent morphisms has square
zero.** Let `T = (X, Y, Z, f, g, h)` be a distinguished triangle and let `c : Z ⟶ Z` satisfy
`g ≫ c = 0` and `c ≫ h = 0`. Then `c ≫ c = 0`. -/
theorem sq_eq_zero_of_comp_mor₂_eq_zero_of_comp_mor₃_eq_zero (T : Triangle C)
    (hT : T ∈ distTriang C) (c : T.obj₃ ⟶ T.obj₃) (h₂ : T.mor₂ ≫ c = 0)
    (h₃ : c ≫ T.mor₃ = 0) : c ≫ c = 0 := by
  let φ : TriangleMorphism T.rotate T.rotate :=
    { hom₁ := 0
      hom₂ := c
      hom₃ := 0
      comm₁ := h₂.trans zero_comp.symm
      comm₂ := comp_zero.trans h₃.symm
      comm₃ := by rw [Functor.map_zero]; exact comp_zero.trans zero_comp.symm }
  exact _root_.comp_middle_zero_of_endomorphisms T.rotate (rot_of_distTriang T hT) φ φ rfl rfl

/-- **An endomorphism of a distinguished triangle whose two outer components vanish has a
square-zero middle component on the third vertex.** -/
theorem sq_eq_zero_of_hom₁_eq_zero_of_hom₂_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (φ : TriangleMorphism T T) (h₁ : φ.hom₁ = 0) (h₂ : φ.hom₂ = 0) :
    φ.hom₃ ≫ φ.hom₃ = 0 :=
  sq_eq_zero_of_comp_mor₂_eq_zero_of_comp_mor₃_eq_zero T hT φ.hom₃
    (by simp [φ.comm₂, h₂]) (by simp [← φ.comm₃, h₁])

/-- **The endomorphism induced on the cone of an endomorphism has square zero.** Let
`X --f--> X --g--> Z --h--> X⟦1⟧` be a distinguished triangle whose first morphism is an
endomorphism of `X`, and let `c : Z ⟶ Z` complete `(f, f)` to a morphism of triangles, i.e.
`g ≫ c = f ≫ g` and `c ≫ h = h ≫ f⟦1⟧'`. Then `c ≫ c = 0`. -/
theorem sq_eq_zero_of_cone_endomorphism {X Z : C} (f : X ⟶ X) (g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (c : Z ⟶ Z) (hc₂ : g ≫ c = f ≫ g)
    (hc₃ : c ≫ h = h ≫ f⟦(1 : ℤ)⟧') : c ≫ c = 0 :=
  sq_eq_zero_of_comp_mor₂_eq_zero_of_comp_mor₃_eq_zero (Triangle.mk f g h) hT c
    (by simpa [hc₂] using comp_distTriang_mor_zero₁₂ _ hT)
    (by simpa [hc₃] using comp_distTriang_mor_zero₃₁ _ hT)

/-- **The cone of an endomorphism carries a square-zero lift of it.** For a distinguished
triangle `X --f--> X --g--> Z --h--> X⟦1⟧` there is a `c : Z ⟶ Z` making `(f, f, c)` a morphism
of triangles, and any such `c` satisfies `c ≫ c = 0`. -/
theorem exists_sq_eq_zero_cone_endomorphism {X Z : C} (f : X ⟶ X) (g : X ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C) :
    ∃ c : Z ⟶ Z, g ≫ c = f ≫ g ∧ c ≫ h = h ≫ f⟦(1 : ℤ)⟧' ∧ c ≫ c = 0 := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism (Triangle.mk f g h)
    (Triangle.mk f g h) hT hT f f rfl
  exact ⟨c, hc₂, hc₃.symm, sq_eq_zero_of_cone_endomorphism f g h hT c hc₂ hc₃.symm⟩

section Linear

variable {R : Type*} [CommRing R] [CategoryTheory.Linear R C]
  [∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

/-- If `(r • 𝟙 Z) ≫ (r • 𝟙 Z) = 0` then `r ^ 2 • 𝟙 Z = 0`. -/
private theorem smul_id_sq_eq_zero_of_comp_self_eq_zero {D : Type*} [Category D] [Preadditive D]
    [CategoryTheory.Linear R D] (r : R) {Z : D}
    (h : (r • 𝟙 Z) ≫ (r • 𝟙 Z) = 0) : r ^ 2 • 𝟙 Z = 0 := by
  rwa [CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul, Category.id_comp,
    smul_smul, ← pow_two] at h

/-- **The cone of multiplication by `r` is annihilated by `r ^ 2`.** If
`X --(r • 𝟙 X)--> X --g--> Z --h--> X⟦1⟧` is distinguished then `r ^ 2 • 𝟙 Z = 0`. -/
theorem sq_smul_id_eq_zero_of_cone_smul_id (r : R) {X Z : C} (g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (r • 𝟙 X) g h ∈ distTriang C) : r ^ 2 • 𝟙 Z = 0 := by
  exact smul_id_sq_eq_zero_of_comp_self_eq_zero r
    (sq_eq_zero_of_cone_endomorphism (r • 𝟙 X) g h hT (r • 𝟙 Z) (by simp) (by simp))

/-- **A scalar annihilating two vertices of a distinguished triangle has square annihilating the
third.** -/
theorem sq_smul_id_eq_zero_of_distTriang (r : R) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : r • 𝟙 T.obj₁ = 0) (h₂ : r • 𝟙 T.obj₂ = 0) : r ^ 2 • 𝟙 T.obj₃ = 0 := by
  exact smul_id_sq_eq_zero_of_comp_self_eq_zero r <| sq_eq_zero_of_hom₁_eq_zero_of_hom₂_eq_zero T hT
    { hom₁ := r • 𝟙 T.obj₁
      hom₂ := r • 𝟙 T.obj₂
      hom₃ := r • 𝟙 T.obj₃
      comm₁ := by simp
      comm₂ := by simp
      comm₃ := by simp } h₁ h₂

/-- **Powers of a scalar annihilating two vertices of a distinguished triangle give one
annihilating the third.** -/
theorem pow_smul_id_eq_zero_of_distTriang (r : R) (T : Triangle C) (hT : T ∈ distTriang C)
    {m n : ℕ} (h₁ : r ^ m • 𝟙 T.obj₁ = 0) (h₂ : r ^ n • 𝟙 T.obj₂ = 0) :
    r ^ (max m n * 2) • 𝟙 T.obj₃ = 0 := by
  have hk : ∀ {X : C} {a : ℕ}, r ^ a • 𝟙 X = 0 → a ≤ max m n → r ^ max m n • 𝟙 X = 0 := by
    intro X a h ha
    rw [← Nat.sub_add_cancel ha, pow_add, mul_smul, h, smul_zero]
  rw [pow_mul]
  exact sq_smul_id_eq_zero_of_distTriang (r ^ max m n) T hT (hk h₁ (le_max_left _ _))
    (hk h₂ (le_max_right _ _))

/-- **A scalar with a power annihilating two vertices of a distinguished triangle has a power
annihilating the third.** -/
theorem exists_pow_smul_id_eq_zero_of_distTriang (r : R) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∃ m : ℕ, r ^ m • 𝟙 T.obj₁ = 0) (h₂ : ∃ n : ℕ, r ^ n • 𝟙 T.obj₂ = 0) :
    ∃ k : ℕ, r ^ k • 𝟙 T.obj₃ = 0 :=
  let ⟨_, hm⟩ := h₁
  let ⟨_, hn⟩ := h₂
  ⟨_, pow_smul_id_eq_zero_of_distTriang r T hT hm hn⟩

/-- **The tower of cones of multiplications.** Let `a : ℕ → R` and let
`E : ℕ → C` be a tower in which, for every `i < s`, the object `E (i + 1)` is a cone of
`a i • 𝟙 (E i)`. Then for every `j < s` a power of `a j` annihilates the top object `E s`. -/
theorem exists_pow_smul_id_eq_zero_of_coneTower {s : ℕ} (a : ℕ → R) (E : ℕ → C)
    (tri : ∀ i, i < s → ∃ (u : E i ⟶ E (i + 1)) (v : E (i + 1) ⟶ (E i)⟦(1 : ℤ)⟧),
      Triangle.mk (a i • 𝟙 (E i)) u v ∈ distTriang C)
    {j : ℕ} (hj : j < s) : ∃ k : ℕ, a j ^ k • 𝟙 (E s) = 0 := by
  suffices H : ∀ t : ℕ, j < t → t ≤ s → ∃ k : ℕ, a j ^ k • 𝟙 (E t) = 0 from H s hj le_rfl
  intro t
  induction t with
  | zero => exact fun ht => absurd ht (Nat.not_lt_zero j)
  | succ n ih =>
    intro _ hts
    obtain ⟨u, v, hT⟩ := tri n (by lia)
    rcases Nat.lt_or_ge j n with hjn | hjn
    · obtain ⟨k, hk⟩ := ih hjn (by lia)
      exact exists_pow_smul_id_eq_zero_of_distTriang (a j) (Triangle.mk (a n • 𝟙 (E n)) u v) hT
        ⟨k, hk⟩ ⟨k, hk⟩
    · obtain rfl : j = n := by lia
      exact ⟨2, sq_smul_id_eq_zero_of_cone_smul_id (a j) u v hT⟩

end Linear

end CategoryTheory.Pretriangulated

end
