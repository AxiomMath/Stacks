module

public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# The colimit statement of a system over a base, at every shift of its first argument

Let `P` be a coherent pullback pseudofunctor datum whose fibres are pretriangulated and whose
inverse images are triangulated, and let `S` be a directed system over a base `b` with a cone,
a `CategoryTheory.PullbackData.LimitSystem`.  For objects `X`, `Y` of `D b` the statement that
`Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)` is
`CategoryTheory.PullbackData.LimitSystem.IsColim`.  This file quantifies it over the shifts of
its first argument and proves that the resulting class of first arguments is a triangulated
subcategory: it is closed under isomorphism and shift, it contains the third object of a
distinguished triangle whose other two objects it contains, and hence it contains binary
biproducts of its members.

Quantifying the shifts *inside* the predicate is what makes the five lemma
`CategoryTheory.PullbackData.LimitSystem.IsColim.obj₃` usable in an induction: that lemma needs
the statement at `A₁`, `A₂`, `A₁⟦1⟧` and `A₂⟦1⟧`, and a predicate with the shift outside cannot
supply the last two.  The same shape is used by
`AlgebraicGeometry.Space.RelativeDescentSituation.ShiftedHomDescent` for Stacks 0DKV and by
`Stacks.LimitHomDescent.SchemeSystem.RestrictIsColim` for Stacks 09RE.

## Main definitions

* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`: the colimit statement at every
  shift of its first argument.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_iso` and `shift`: invariance under
  isomorphism of the first argument, and stability under its shifts.
* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.obj₃`, `obj₁`, `obj₂`: the five lemma
  at each vertex of a distinguished triangle.
* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.biprod`: closure under binary
  biproducts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData.LimitSystem

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {P : PullbackData A D} {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}
  [∀ a, HasShift (D a) ℤ]

/-- **The colimit statement at every shift of its first argument**: for every `n`,
`Hom(k^*(X⟦n⟧), k^*Y)` is the filtered colimit of the `Hom(k_j^*(X⟦n⟧), k_j^*Y)`. -/
def ShiftedIsColim (S : LimitSystem (A := A) b J) (P : PullbackData A D) (X Y : D b) : Prop :=
  ∀ n : ℤ, S.IsColim P (X⟦n⟧) Y

variable [IsDirected J (· ≤ ·)]

/-- The statement at every shift depends on its first argument only up to isomorphism. -/
theorem ShiftedIsColim.of_iso (hP : P.IsCoherent) {X X' Y : D b} (e : X ≅ X')
    (hX : ShiftedIsColim S P X Y) : ShiftedIsColim S P X' Y :=
  fun n ↦ (hX n).of_iso_fst hP ((shiftFunctor (D b) n).mapIso e)

/-- The statement at every shift is stable under shifting its first argument. -/
theorem ShiftedIsColim.shift (hP : P.IsCoherent) {X Y : D b} (hX : ShiftedIsColim S P X Y)
    (m : ℤ) : ShiftedIsColim S P (X⟦m⟧) Y :=
  fun n ↦ (hX (m + n)).of_iso_fst hP ((shiftFunctorAdd' (D b) m n (m + n) rfl).app X)

variable [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated]

/-- **The five lemma at the third vertex**: the statement at every shift holds for the third
object of a distinguished triangle as soon as it holds for the other two. -/
theorem ShiftedIsColim.obj₃ (hP : P.IsCoherent) (T : Triangle (D b)) (hT : T ∈ distTriang (D b))
    (Y : D b) (h₁ : ShiftedIsColim S P T.obj₁ Y) (h₂ : ShiftedIsColim S P T.obj₂ Y) :
    ShiftedIsColim S P T.obj₃ Y := fun n ↦
  IsColim.obj₃ hP (Triangle.shift_distinguished T hT n) (h₁ n) (h₂ n)
    (h₁.shift hP n 1) (h₂.shift hP n 1)

/-- **The five lemma at the first vertex.** -/
theorem ShiftedIsColim.obj₁ (hP : P.IsCoherent) (T : Triangle (D b)) (hT : T ∈ distTriang (D b))
    (Y : D b) (h₂ : ShiftedIsColim S P T.obj₂ Y) (h₃ : ShiftedIsColim S P T.obj₃ Y) :
    ShiftedIsColim S P T.obj₁ Y :=
  ShiftedIsColim.obj₃ hP T.invRotate.invRotate
    (inv_rot_of_distTriang _ (inv_rot_of_distTriang _ hT)) Y (h₂.shift hP (-1))
    (h₃.shift hP (-1))

/-- **The five lemma at the second vertex.** -/
theorem ShiftedIsColim.obj₂ (hP : P.IsCoherent) (T : Triangle (D b)) (hT : T ∈ distTriang (D b))
    (Y : D b) (h₁ : ShiftedIsColim S P T.obj₁ Y) (h₃ : ShiftedIsColim S P T.obj₃ Y) :
    ShiftedIsColim S P T.obj₂ Y :=
  ShiftedIsColim.obj₃ hP T.invRotate (inv_rot_of_distTriang _ hT) Y (h₃.shift hP (-1)) h₁

/-- **The statement at every shift is closed under binary biproducts of its first
argument.** -/
theorem ShiftedIsColim.biprod (hP : P.IsCoherent) {X X' Y : D b} [HasBinaryBiproduct X X']
    (hX : ShiftedIsColim S P X Y) (hX' : ShiftedIsColim S P X' Y) :
    ShiftedIsColim S P (X ⊞ X') Y :=
  ShiftedIsColim.obj₂ hP (binaryBiproductTriangle X X')
    (binaryBiproductTriangle_distinguished X X') Y hX hX'

end CategoryTheory.PullbackData.LimitSystem

end
