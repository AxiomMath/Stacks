module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndAlgebraFreePoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixFreeSheaf
public import StacksFrontier.AlgebraicGeometry.Matrix.SkolemNoetherSpread
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The sections of a matrix algebra sheaf, and automorphisms read on them

Let `S` be a scheme and let `I` be a finite type. The sheaf of `I × I` matrices over `𝒪_S` is the
endomorphism algebra sheaf `End(𝒪_S^{(I)})` of the free sheaf of modules of rank `I`, a monoid
object in the sheaves of `𝒪_S`-modules. This file reads an **automorphism of that sheaf of
algebras** as a restriction-compatible family of algebra automorphisms of
`Matrix I I Γ(S, U)`, one for each open set `U`, and feeds that family to
`Stacks.AlgebraicGeometry.exists_units_conj_eq_of_algEquiv_sheaf` — Skolem--Noether spread out
from a stalk — to obtain the **overlap step of [Stacks, Tag 0A2L]**: an automorphism of
`Mat_d(𝒪_T)` is, on a neighbourhood of any point of `T`, conjugation by a single invertible
matrix of sections.

## Main definitions

* `CategoryTheory.MonoidalCategory.dualBasisMatrix`: the matrix of an endomorphism of an object
  `F` of a preadditive monoidal category against a family of points `e i : 𝟙_ C ⟶ F` and
  coordinates `p j : F ⟶ 𝟙_ C`, with entries `e a ≫ f ≫ p b` in `End (𝟙_ C)`.
* `Stacks.Matrix.unitCombination`: the linear map of matrices prescribed on the matrix units.
* `Stacks.SheafOfModules.unitEndValue`: the section of the structure sheaf over an object of the
  site attached to an endomorphism of the unit sheaf of modules, its value on the unit section.
* `Stacks.SheafOfModules.secToMat` and `secOfMat`: sections of a sheaf of modules carrying a dual
  basis indexed by a square `I × I`, read as `I × I` matrices of sections of the structure sheaf,
  and back.
* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix`: `dualBasisMatrix` for the tautological
  points and coordinates of a finite free sheaf of `𝒪_S`-modules.
* `Stacks.EtaleCohomology.BrauerScheme.matCoord` and `matIncl`: the coordinates and the matrix
  units of `End(𝒪_S^{(I)})`, read through the identification of
  `Stacks.EtaleCohomology.BrauerScheme.freeProdIsoEndAlgebra` of that sheaf with the free sheaf of
  modules on `I × I`.
* `Stacks.EtaleCohomology.BrauerScheme.pointMatrix`: the matrix over `End(𝒪_S)` of the image of a
  matrix unit under a morphism of sheaves of algebras.
* `Stacks.EtaleCohomology.BrauerScheme.unitEndValueHom`: the ring homomorphism
  `End(𝒪_S) →+* Γ(S, U)`.
* `Stacks.EtaleCohomology.BrauerScheme.sectionAlgEquiv` and `matrixAlgebraSectionAlgEquiv`: **an
  automorphism of the matrix algebra sheaf read on the sections over an open set**, as an algebra
  automorphism of `Matrix I I Γ(S, U)`, respectively of `Matrix (Fin d) (Fin d) Γ(S, U)`.

## Main results

* `CategoryTheory.MonoidalClosed.curry'_comp_ihomCoord`: a point of the internal hom evaluated at
  a point of the source is the composite, `curry' f ≫ ihomCoord e Y = e ≫ f`.
* `CategoryTheory.MonoidalClosed.curry'_comp_ihomIsoOfDualBasis_inv_comp`: **the coordinates of a
  point of `F ⟶[C] F`, read through `MonoidalClosed.ihomIsoOfDualBasis`, are the matrix
  entries.** This is the join between the points machinery of
  `StacksFrontier.CategoryTheory.Monoidal.InternalEndPoints` and the matrix dictionary, and it is
  what makes the whole bridge an identification rather than a bijection that happens to exist.
* `CategoryTheory.MonoidalCategory.dualBasisMatrix_comp` and `dualBasisMatrix_injective`:
  composition goes to the matrix product in the same order, and an endomorphism is determined by
  its matrix.
* `Stacks.Matrix.unitCombination_one` and `unitCombination_mul`: **a linear map of matrices is
  unital and multiplicative as soon as the images of the matrix units satisfy the matrix unit
  relations.**
* `Stacks.EtaleCohomology.BrauerScheme.pointMatrix_mul` and `sum_pointMatrix`: **the images of the
  matrix units under a morphism of sheaves of algebras satisfy the matrix unit relations.**
* `Stacks.EtaleCohomology.BrauerScheme.sectionMap_res` and `matrixAlgebraSectionAlgEquiv_res`:
  **the family of algebra automorphisms is compatible with restriction.**
* `Stacks.EtaleCohomology.BrauerScheme.exists_units_conj_eq_of_iso_matrixAlgebra`: **the overlap
  step of Tag 0A2L.**

## Implementation notes

**Why the multiplication never has to be computed on sections.** The multiplication of the matrix
algebra sheaf is a morphism out of a tensor product sheaf, so the ring of sections
`Γ(End(𝒪_S^{(I)}), U)` is not available by inspection: the internal hom of
`Stacks.SheafOfModules.Strict.strictMonoidalClosed` is a right adjoint transported along an
isomorphism of left adjoints, not a sheaf given by a formula. None of that is needed. The ring
structure on `Matrix I I Γ(S, U)` is the ordinary one, and what has to be proved is that the map
induced on it by the automorphism is multiplicative. That map is `Γ(S, U)`-linear and natural in
`U` for free — it is a morphism of sheaves of modules read on sections — so multiplicativity
reduces to the matrix units (`Stacks.Matrix.unitCombination_mul`), and the matrix units are
*global* points of the sheaf. On a point the multiplication of the monoid object is composition in
the category, which is `MonoidalClosed.pointMap`. So the whole computation happens at
`End (𝟙_ C)`, where `Stacks.EtaleCohomology.BrauerScheme.pointMatrix_mul` establishes the matrix
unit relations, and `Stacks.EtaleCohomology.BrauerScheme.unitEndValueHom` carries them to
`Γ(S, U)` for every `U` at once.

**Every rewrite happens where the category is a variable.** At the scheme spelling,
`Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf` is not type-correct at the `implicit`
transparency at which `rw` builds its motive: `S.sheaf` is a `TopCat.Sheaf`, and only unfolding
that definition makes it a `Sheaf (Opens.grothendieckTopology S)`. A `rw` whose pattern is plainly
present is therefore rejected, with the mismatch reported inside the motive. This is the same
obstruction
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndAlgebraFreePoints`
records, and the same answer: the dual-basis dictionary, the points computation, the matrix-unit
algebra and the section calculus are each stated at a variable category or a variable sheaf of
rings, and the scheme-level declarations are applications of them.

**The section types are definitionally the ones the consumer names.**
`Γ(S, U)` and the sections of the unit sheaf of modules over `op U` are the same type with the
same ring structure, and the restriction map of the ring sheaf is the restriction map of the
structure sheaf, because `Stacks.SheafOfModules.Tensor.ringSheaf` is `S.sheaf` composed with the
carrier-preserving `forget₂ CommRingCat RingCat`. Nothing bridges them; the declarations below are
stated at `Γ(S, U)` directly.

**`Stacks.SheafOfModules.unitEndValue` and the global-sections form.**
`Stacks.Cohomology.SiteModules.unitEndSection` is the same construction read as a compatible
family of sections rather than at one object, with
`Stacks.Cohomology.SiteModules.unitEndEquiv` the resulting bijection with `End(𝒪)`. It is not used
here: it carries no ring structure, it is stated for the whole family rather than at the object
the matrices are indexed over, and it lives in the cohomology of sheaves of modules, whose import
closure this file has no other use for. The two agree by
`Stacks.Cohomology.SiteModules.unitEndSection_val`.

**`HasFiniteBiproducts (ModuleSheaf S)` and `MonoidalPreadditive (ModuleSheaf S)`** are
re-enabled from `MatrixFreeSheaf` with `attribute [local instance]` rather than restated: the two
declarations there are `local instance`s, hence ordinary declarations downstream, and restating
them collides.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
  TopologicalSpace

universe u w v₁ u₁

noncomputable section

/-! ### The matrix of an endomorphism with respect to a dual basis -/

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]

omit [Preadditive C] in
/-- The multiplication of `End (𝟙_ C)` is composition in either order. -/
theorem unitEnd_mul_eq_comp (x y : End (𝟙_ C)) : x * y = End.of (x.asHom ≫ y.asHom) :=
  End.ext (comp_comm_unitEnd y.asHom x.asHom)

variable {F : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
  (e : ι → (𝟙_ C ⟶ F)) (p : ι → (F ⟶ 𝟙_ C))

/-- The matrix of an endomorphism of `F` with respect to a family of points `e` and a family of
coordinates `p`: the `(a, b)` entry is `e a ≫ f ≫ p b`, an endomorphism of the monoidal unit. -/
def dualBasisMatrix (f : F ⟶ F) : Matrix ι ι (End (𝟙_ C)) := fun a b => End.of (e a ≫ f ≫ p b)

omit [Preadditive C] [Fintype ι] [DecidableEq ι] in
/-- The `(a, b)` entry of `dualBasisMatrix e p f` is `e a ≫ f ≫ p b`. -/
lemma dualBasisMatrix_apply (f : F ⟶ F) (a b : ι) :
    dualBasisMatrix e p f a b = End.of (e a ≫ f ≫ p b) := rfl

omit [Preadditive C] [Fintype ι] [DecidableEq ι] in
/-- The underlying morphism of the `(a, b)` entry of `dualBasisMatrix e p f` is `e a ≫ f ≫ p b`. -/
lemma dualBasisMatrix_apply_asHom (f : F ⟶ F) (a b : ι) :
    (dualBasisMatrix e p f a b).asHom = e a ≫ f ≫ p b := rfl

omit [Fintype ι] in
/-- **The matrix of the identity is the identity matrix.** -/
theorem dualBasisMatrix_id (hp : ∀ i j, e i ≫ p j = if i = j then 𝟙 (𝟙_ C) else 0) :
    dualBasisMatrix e p (𝟙 F) = 1 := by
  funext a b
  ext
  rw [dualBasisMatrix_apply_asHom, Category.id_comp, hp]
  rcases eq_or_ne a b with rfl | h
  · rw [ite_eq_left rfl, Matrix.one_apply_eq, End.one_asHom]
  · rw [ite_eq_right h, Matrix.one_apply_ne h]
    simp

omit [DecidableEq ι] in
/-- **Composition goes to the matrix product, in the same order.** -/
theorem dualBasisMatrix_comp (htot : ∑ i : ι, p i ≫ e i = 𝟙 F) (f g : F ⟶ F) :
    dualBasisMatrix e p (f ≫ g) = dualBasisMatrix e p f * dualBasisMatrix e p g := by
  funext a b
  ext
  have key : ∀ i : ι, (dualBasisMatrix e p f a i * dualBasisMatrix e p g i b).asHom
      = e a ≫ f ≫ (p i ≫ e i) ≫ g ≫ p b := fun i => by
    rw [unitEnd_mul_eq_comp]
    simp only [dualBasisMatrix_apply_asHom, Category.assoc]
  rw [Matrix.mul_apply, End.sum_asHom, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i,
    ← Preadditive.comp_sum, ← Preadditive.comp_sum, ← Preadditive.sum_comp, htot,
    Category.id_comp]
  simp only [dualBasisMatrix_apply_asHom, Category.assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- The matrix of a sum is the sum of the matrices. -/
theorem dualBasisMatrix_add (f g : F ⟶ F) :
    dualBasisMatrix e p (f + g) = dualBasisMatrix e p f + dualBasisMatrix e p g := by
  funext a b
  ext
  simp [dualBasisMatrix_apply_asHom, Matrix.add_apply, Preadditive.add_comp,
    Preadditive.comp_add]

omit [Fintype ι] [DecidableEq ι] in
/-- The matrix of the zero endomorphism is the zero matrix. -/
@[simp]
theorem dualBasisMatrix_zero : dualBasisMatrix e p (0 : F ⟶ F) = 0 := by
  funext a b
  ext
  simp [dualBasisMatrix_apply_asHom, Matrix.zero_apply, Limits.zero_comp, Limits.comp_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- The matrix of a finite sum of endomorphisms is the sum of their matrices. -/
theorem dualBasisMatrix_sum {κ : Type*} (t : Finset κ) (f : κ → (F ⟶ F)) :
    dualBasisMatrix e p (∑ k ∈ t, f k) = ∑ k ∈ t, dualBasisMatrix e p (f k) := by
  exact map_sum (AddMonoidHom.mk' (dualBasisMatrix e p) (dualBasisMatrix_add e p)) f t

omit [DecidableEq ι] in
/-- An endomorphism of `F` is recovered from its matrix. -/
theorem eq_sum_dualBasisMatrix (htot : ∑ i : ι, p i ≫ e i = 𝟙 F) (f : F ⟶ F) :
    f = ∑ a : ι, ∑ b : ι, p a ≫ (dualBasisMatrix e p f a b).asHom ≫ e b := by
  have h : ∀ a : ι, ∑ b : ι, p a ≫ (dualBasisMatrix e p f a b).asHom ≫ e b = p a ≫ e a ≫ f :=
    fun a => by
      simp only [dualBasisMatrix_apply_asHom, Category.assoc]
      rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, ← Preadditive.comp_sum, htot,
        Category.comp_id]
  refine Eq.symm ?_
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => h a]
  simp only [← Category.assoc]
  rw [← Preadditive.sum_comp, htot, Category.id_comp]

omit [DecidableEq ι] in
/-- **An endomorphism of `F` is determined by its matrix.** -/
theorem dualBasisMatrix_injective (htot : ∑ i : ι, p i ≫ e i = 𝟙 F) :
    Function.Injective (dualBasisMatrix e p) := fun f g h => by
  rw [eq_sum_dualBasisMatrix e p htot f, eq_sum_dualBasisMatrix e p htot g, h]

end CategoryTheory.MonoidalCategory

/-! ### Points of an internal hom and the matrix dictionary -/

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- **A point of the internal hom, evaluated at a point of the source.** -/
theorem curry'_comp_ihomCoord {F Y : C} (e : 𝟙_ C ⟶ F) (f : F ⟶ Y) :
    curry' f ≫ ihomCoord e Y = e ≫ f := by
  refine (cancel_epi (λ_ (𝟙_ C)).hom).mp ?_
  rw [← leftUnitor_naturality_assoc, leftUnitor_comp_ihomCoord, whisker_exchange_assoc,
    whiskerLeft_curry'_ihom_ev_app, rightUnitor_naturality_assoc, unitors_equal]

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The inverse of `CategoryTheory.MonoidalClosed.ihomIsoOfDualBasis`, unfolded. -/
lemma ihomIsoOfDualBasis_inv {F Q : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → (𝟙_ C ⟶ F)) (p : ι → (F ⟶ 𝟙_ C)) (htot : ∑ i, p i ≫ e i = 𝟙 F)
    (hp : ∀ i j, e i ≫ p j = if i = j then 𝟙 (𝟙_ C) else 0)
    (d : ι × ι → (𝟙_ C ⟶ Q)) (row : ι → (F ⟶ Q)) (hrow : ∀ i j, e j ≫ row i = d (i, j))
    (hF : ∀ {N : C} {u v : F ⟶ N}, (∀ i, e i ≫ u = e i ≫ v) → u = v)
    (hQ : ∀ {N : C} {u v : Q ⟶ N}, (∀ k, d k ≫ u = d k ≫ v) → u = v)
    (hom : Q ⟶ (ihom F).obj F)
    (hhom : ∀ i j, d (i, j) ≫ hom = e j ≫ ihomIncl (p i) F) :
    (ihomIsoOfDualBasis e p htot hp d row hrow hF hQ hom hhom).inv =
      ∑ i : ι, ihomCoord (e i) F ≫ row i :=
  rfl

/-- **The coordinates of a point of the internal endomorphism object, read through
`CategoryTheory.MonoidalClosed.ihomIsoOfDualBasis`, are the matrix entries.** -/
theorem curry'_comp_ihomIsoOfDualBasis_inv_comp {F Q : C} {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (e : ι → (𝟙_ C ⟶ F)) (p : ι → (F ⟶ 𝟙_ C)) (htot : ∑ i, p i ≫ e i = 𝟙 F)
    (hp : ∀ i j, e i ≫ p j = if i = j then 𝟙 (𝟙_ C) else 0)
    (d : ι × ι → (𝟙_ C ⟶ Q)) (row : ι → (F ⟶ Q)) (hrow : ∀ i j, e j ≫ row i = d (i, j))
    (hF : ∀ {N : C} {u v : F ⟶ N}, (∀ i, e i ≫ u = e i ≫ v) → u = v)
    (hQ : ∀ {N : C} {u v : Q ⟶ N}, (∀ k, d k ≫ u = d k ≫ v) → u = v)
    (hom : Q ⟶ (ihom F).obj F)
    (hhom : ∀ i j, d (i, j) ≫ hom = e j ≫ ihomIncl (p i) F)
    (q : ι × ι → (Q ⟶ 𝟙_ C))
    (hrowq : ∀ i a b, row i ≫ q (a, b) = if i = a then p b else 0)
    (f : F ⟶ F) (a b : ι) :
    curry' f ≫ (ihomIsoOfDualBasis e p htot hp d row hrow hF hQ hom hhom).inv ≫ q (a, b)
      = e a ≫ f ≫ p b := by
  have key : ∀ i : ι, curry' f ≫ (ihomCoord (e i) F ≫ row i) ≫ q (a, b)
      = if i = a then e a ≫ f ≫ p b else 0 := by
    intro i
    calc curry' f ≫ (ihomCoord (e i) F ≫ row i) ≫ q (a, b)
        = (curry' f ≫ ihomCoord (e i) F) ≫ (row i ≫ q (a, b)) := by
          simp only [Category.assoc]
      _ = (e i ≫ f) ≫ (if i = a then p b else 0) := by rw [curry'_comp_ihomCoord, hrowq]
      _ = if i = a then e a ≫ f ≫ p b else 0 := by
          rcases eq_or_ne i a with rfl | h
          · rw [ite_eq_left rfl, ite_eq_left rfl, Category.assoc]
          · rw [ite_eq_right h, ite_eq_right h, Limits.comp_zero]
  rw [ihomIsoOfDualBasis_inv, Preadditive.sum_comp, Preadditive.comp_sum,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i,
    Finset.sum_ite_eq' Finset.univ a fun _ => e a ≫ f ≫ p b,
    ite_eq_left (Finset.mem_univ a)]

/-- The map induced on endomorphisms by a morphism of internal endomorphism monoids kills
zero. -/
theorem pointMap_zero {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) :
    pointMap θ (0 : X ⟶ X) = 0 := by
  exact map_zero (AddMonoidHom.mk' (pointMap θ) (pointMap_add θ))

/-- The map induced on endomorphisms by a morphism of internal endomorphism monoids commutes
with finite sums. -/
theorem pointMap_sum {X Y : C} (θ : internalEnd X ⟶ internalEnd Y) {κ : Type*} (t : Finset κ)
    (f : κ → (X ⟶ X)) : pointMap θ (∑ k ∈ t, f k) = ∑ k ∈ t, pointMap θ (f k) := by
  exact map_sum (AddMonoidHom.mk' (pointMap θ) (pointMap_add θ)) f t

end Preadditive

end CategoryTheory.MonoidalClosed

/-! ### A linear map of matrices determined on the matrix units -/

namespace Stacks.Matrix

variable {K : Type*} [CommRing K] {I : Type*} [Fintype I] [DecidableEq I]
  (W : I × I → Matrix I I K)

/-- The `K`-linear map of matrices sending the `(c, e)` matrix unit to `W (c, e)`. -/
def unitCombination (M : Matrix I I K) : Matrix I I K := ∑ c : I, ∑ e : I, M c e • W (c, e)

omit [DecidableEq I] in
/-- The `(a, b)` entry of `unitCombination W M` is `∑ c, ∑ e, M c e * W (c, e) a b`. -/
lemma unitCombination_apply (M : Matrix I I K) (a b : I) :
    unitCombination W M a b = ∑ c : I, ∑ e : I, M c e * W (c, e) a b := by
  simp only [unitCombination, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq I] in
/-- `Stacks.Matrix.unitCombination W` is additive. -/
lemma unitCombination_add (M N : Matrix I I K) :
    unitCombination W (M + N) = unitCombination W M + unitCombination W N := by
  simp only [unitCombination, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

omit [DecidableEq I] in
/-- `Stacks.Matrix.unitCombination W` commutes with scalar multiplication. -/
lemma unitCombination_smul (r : K) (M : Matrix I I K) :
    unitCombination W (r • M) = r • unitCombination W M := by
  simp only [unitCombination, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- **The combination of the matrix units is unital** as soon as the images of the diagonal
matrix units add up to the identity matrix. -/
lemma unitCombination_one (hsum : ∑ a : I, W (a, a) = 1) : unitCombination W 1 = 1 := by
  have h : ∀ c : I, (∑ e : I, (1 : Matrix I I K) c e • W (c, e)) = W (c, c) := by
    intro c
    rw [Finset.sum_eq_single c (fun e _ he => by
        rw [Matrix.one_apply_ne (Ne.symm he), zero_smul]) (fun hc => absurd (Finset.mem_univ c) hc),
      Matrix.one_apply_eq, one_smul]
  rw [unitCombination, Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => h c, hsum]

/-- **The combination of the matrix units is multiplicative** as soon as the images of the
matrix units satisfy the matrix unit relations. -/
lemma unitCombination_mul
    (hmul : ∀ a b c e : I, W (a, b) * W (c, e) = if b = c then W (a, e) else 0)
    (M N : Matrix I I K) :
    unitCombination W (M * N) = unitCombination W M * unitCombination W N := by
  have step : unitCombination W M * unitCombination W N
      = ∑ c : I, ∑ e : I, ∑ e' : I, (M c e * N e e') • W (c, e') := by
    rw [unitCombination, unitCombination, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    have h1 : ∀ c' : I, (M c e • W (c, e)) * (∑ e' : I, N c' e' • W (c', e'))
        = ∑ e' : I, (M c e * N c' e') • (if e = c' then W (c, e') else 0) := by
      intro c'
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e' _ => by
        rw [smul_mul_smul_comm, hmul]
    rw [Finset.sum_congr rfl fun c' (_ : c' ∈ Finset.univ) => h1 c']
    rw [Finset.sum_eq_single e
      (fun c' _ hc' => Finset.sum_eq_zero fun e' _ => by
        rw [ite_eq_right (Ne.symm hc'), smul_zero])
      (fun hc => absurd (Finset.mem_univ e) hc)]
    exact Finset.sum_congr rfl fun e' _ => by rw [ite_eq_left rfl]
  rw [step, unitCombination]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [Matrix.mul_apply, ← Finset.sum_smul]

end Stacks.Matrix

/-! ### Transporting a dual basis along an isomorphism -/

namespace CategoryTheory

section Conj

variable {C : Type*} [Category C] [Preadditive C] {A P Q : C} (ψ : P ≅ Q)
  {κ : Type*} [Fintype κ] (d : κ → (A ⟶ P)) (q : κ → (P ⟶ A))

omit [Preadditive C] [Fintype κ] in
/-- Transporting `d k : A ⟶ P` and `q l : P ⟶ A` along an isomorphism `ψ : P ≅ Q` does not change
their composite: `(d k ≫ ψ.hom) ≫ ψ.inv ≫ q l = d k ≫ q l`. -/
lemma conj_inj_comp_conj_proj (k l : κ) :
    (d k ≫ ψ.hom) ≫ ψ.inv ≫ q l = d k ≫ q l := by
  rw [Category.assoc, Iso.hom_inv_id_assoc]

/-- If `∑ k, q k ≫ d k = 𝟙 P`, then the maps transported along an isomorphism `ψ : P ≅ Q` satisfy
`∑ k, (ψ.inv ≫ q k) ≫ (d k ≫ ψ.hom) = 𝟙 Q`. -/
lemma sum_conj_proj_comp_conj_inj (htot : ∑ k : κ, q k ≫ d k = 𝟙 P) :
    ∑ k : κ, (ψ.inv ≫ q k) ≫ (d k ≫ ψ.hom) = 𝟙 Q := by
  have h : ∀ k : κ, (ψ.inv ≫ q k) ≫ (d k ≫ ψ.hom) = ψ.inv ≫ (q k ≫ d k) ≫ ψ.hom :=
    fun k => by simp only [Category.assoc]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => h k, ← Preadditive.comp_sum,
    ← Preadditive.sum_comp, htot, Category.id_comp, Iso.inv_hom_id]

end Conj

end CategoryTheory

/-! ### Sections of a sheaf of modules with a dual basis indexed by a square -/

namespace Stacks.SheafOfModules

section UnitSections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The section of the structure sheaf over `V` attached to an endomorphism of the unit sheaf
of modules: its value on the unit section. -/
def unitEndValue (V : Cᵒᵖ) (r : End (_root_.SheafOfModules.unit R)) :
    ToType (R.obj.obj V) :=
  r.asHom.val.app V (unitOne V)

/-- `unitEndValue V r` is the value of `r` on the unit section over `V`. -/
lemma unitEndValue_apply (V : Cᵒᵖ) (r : End (_root_.SheafOfModules.unit R)) :
    unitEndValue V r = r.asHom.val.app V (unitOne V) := rfl

/-- The value of the identity endomorphism of the unit sheaf of modules is `1`. -/
@[simp]
lemma unitEndValue_one (V : Cᵒᵖ) : unitEndValue (R := R) V 1 = 1 := rfl

/-- The value of the zero endomorphism of the unit sheaf of modules is `0`. -/
@[simp]
lemma unitEndValue_zero (V : Cᵒᵖ) : unitEndValue (R := R) V 0 = 0 :=
  zero_app_apply V _

/-- The value of a sum of endomorphisms is the sum of their values. -/
lemma unitEndValue_add (V : Cᵒᵖ) (r r' : End (_root_.SheafOfModules.unit R)) :
    unitEndValue V (r + r') = unitEndValue V r + unitEndValue V r' := rfl

/-- The value of a finite sum of endomorphisms is the sum of their values. -/
lemma unitEndValue_sum {κ : Type*} (t : Finset κ)
    (f : κ → End (_root_.SheafOfModules.unit R)) (V : Cᵒᵖ) :
    unitEndValue V (∑ k ∈ t, f k) = ∑ k ∈ t, unitEndValue V (f k) := by
  rw [unitEndValue, End.sum_asHom]
  exact app_sum t (fun k => (f k).asHom) V (unitOne V)

/-- An endomorphism of the unit sheaf of modules acts on sections by multiplication by its
value on the unit section. -/
lemma app_toUnit (g : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R) (V : Cᵒᵖ)
    (c : ToType (R.obj.obj V)) :
    g.val.app V (toUnit V c) = toUnit V (c * unitEndValue V (End.of g)) :=
  (app_unit_eq g V c).trans (toUnit_smul V c (unitEndValue V (End.of g)))

/-- The value of a composite `r ≫ r'` is the product `unitEndValue V r * unitEndValue V r'`. -/
lemma unitEndValue_comp (V : Cᵒᵖ) (r r' : End (_root_.SheafOfModules.unit R)) :
    unitEndValue V (End.of (r.asHom ≫ r'.asHom)) = unitEndValue V r * unitEndValue V r' :=
  app_toUnit r'.asHom V (unitEndValue V r)

/-- The value of `if P then 𝟙 _ else 0` is `if P then 1 else 0`. -/
lemma unitEndValue_ite (V : Cᵒᵖ) {P : Prop} [Decidable P] :
    unitEndValue (R := R) V (End.of (if P then 𝟙 (_root_.SheafOfModules.unit R) else 0))
      = if P then 1 else 0 := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; exact zero_app_apply V _

/-- Restriction along `f : V ⟶ W` sends the value of `r` over `V` to the value of `r` over `W`. -/
lemma unitEndValue_res {V W : Cᵒᵖ} (f : V ⟶ W) (r : End (_root_.SheafOfModules.unit R)) :
    (R.obj.map f).hom (unitEndValue V r) = unitEndValue W r :=
  (PresheafOfModules.naturality_apply r.asHom.val f (unitOne V)).symm.trans
    (congrArg (fun x => r.asHom.val.app W x) (PresheafOfModules.unit_map_one R.obj f))

/-- Applying a morphism of sheaves of modules to a finite sum of sections. -/
lemma app_sum_elt {M N : _root_.SheafOfModules.{w} R} (g : M ⟶ N) (V : Cᵒᵖ) {κ : Type*}
    (t : Finset κ) (x : κ → ToType (M.val.obj V)) :
    g.val.app V (∑ k ∈ t, x k) = ∑ k ∈ t, g.val.app V (x k) :=
  map_sum (g.val.app V).hom x t

variable {A : _root_.SheafOfModules.{w} R} {I : Type*} [Fintype I] [DecidableEq I]
  (dd : I × I → (_root_.SheafOfModules.unit R ⟶ A))
  (qq : I × I → (A ⟶ _root_.SheafOfModules.unit R))

/-- A section of `A` over `V`, read as a matrix through a dual basis indexed by `I × I`. -/
def secToMat (V : Cᵒᵖ) (s : ToType (A.val.obj V)) : Matrix I I (ToType (R.obj.obj V)) :=
  fun a b => (qq (a, b)).val.app V s

/-- A matrix of sections of the structure sheaf over `V`, read as a section of `A`. -/
def secOfMat (V : Cᵒᵖ) (M : Matrix I I (ToType (R.obj.obj V))) : ToType (A.val.obj V) :=
  ∑ a : I, ∑ b : I, (dd (a, b)).val.app V (toUnit V (M a b))

omit [DecidableEq I] in
/-- **The matrix of the image of a matrix of sections under an endomorphism of `A`.** -/
lemma secToMat_app_secOfMat (V : Cᵒᵖ) (ϑ : A ⟶ A)
    (M : Matrix I I (ToType (R.obj.obj V))) (a b : I) :
    secToMat qq V (ϑ.val.app V (secOfMat dd V M)) a b
      = ∑ c : I, ∑ e : I, M c e * unitEndValue V (End.of (dd (c, e) ≫ ϑ ≫ qq (a, b))) := by
  have key : ∀ c e : I,
      (qq (a, b)).val.app V (ϑ.val.app V ((dd (c, e)).val.app V (toUnit V (M c e))))
        = M c e * unitEndValue V (End.of (dd (c, e) ≫ ϑ ≫ qq (a, b))) :=
    fun c e => app_toUnit (dd (c, e) ≫ ϑ ≫ qq (a, b)) V (M c e)
  change (qq (a, b)).val.app V (ϑ.val.app V
    (∑ c : I, ∑ e : I, (dd (c, e)).val.app V (toUnit V (M c e)))) = _
  simp only [app_sum_elt]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => key c e

/-- If `dd k ≫ qq l` is the identity for `k = l` and zero otherwise, then reading the section
`secOfMat dd V M` as a matrix gives back `M`. -/
lemma secToMat_secOfMat (hdq : ∀ k l : I × I,
      dd k ≫ qq l = if k = l then 𝟙 (_root_.SheafOfModules.unit R) else 0)
    (V : Cᵒᵖ) (M : Matrix I I (ToType (R.obj.obj V))) :
    secToMat qq V (secOfMat dd V M) = M := by
  funext a b
  have key : ∀ c e : I,
      (qq (a, b)).val.app V ((dd (c, e)).val.app V (toUnit V (M c e)))
        = if ((c, e) : I × I) = (a, b) then M c e else 0 := by
    intro c e
    have h1 : (qq (a, b)).val.app V ((dd (c, e)).val.app V (toUnit V (M c e)))
        = toUnit V (M c e * unitEndValue V (End.of (dd (c, e) ≫ qq (a, b)))) :=
      app_toUnit (dd (c, e) ≫ qq (a, b)) V (M c e)
    rw [h1, hdq, unitEndValue_ite]
    by_cases hce : ((c, e) : I × I) = (a, b)
    · rw [ite_eq_left hce, ite_eq_left hce, mul_one]; rfl
    · rw [ite_eq_right hce, ite_eq_right hce, mul_zero]; rfl
  have h2 : ∀ c : I, (∑ e : I, if ((c, e) : I × I) = (a, b) then M c e else 0)
      = if c = a then M c b else 0 := by
    intro c
    by_cases hc : c = a
    · subst hc
      rw [ite_eq_left rfl, Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) =>
        if_congr (show ((c, e) : I × I) = (c, b) ↔ e = b by simp) rfl rfl]
      exact (Finset.sum_ite_eq' Finset.univ b fun e : I => M c e).trans
        (ite_eq_left (Finset.mem_univ b))
    · rw [ite_eq_right hc]
      exact Finset.sum_eq_zero fun e _ => ite_eq_right (by simp [Prod.ext_iff, hc])
  change (qq (a, b)).val.app V
      (∑ c : I, ∑ e : I, (dd (c, e)).val.app V (toUnit V (M c e))) = M a b
  rw [app_sum_elt, Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
    (app_sum_elt (qq (a, b)) V Finset.univ
      (fun e : I => (dd (c, e)).val.app V (toUnit V (M c e)))).trans
      ((Finset.sum_congr rfl fun e _ => key c e).trans (h2 c))]
  exact (Finset.sum_ite_eq' Finset.univ a fun c : I => M c b).trans
    (ite_eq_left (Finset.mem_univ a))

omit [DecidableEq I] in
/-- If `∑ k, qq k ≫ dd k = 𝟙 A`, then a section `s` of `A` over `V` is recovered from its matrix:
`secOfMat dd V (secToMat qq V s) = s`. -/
lemma secOfMat_secToMat (htot : ∑ k : I × I, qq k ≫ dd k = 𝟙 A) (V : Cᵒᵖ)
    (s : ToType (A.val.obj V)) :
    secOfMat dd V (secToMat qq V s) = s := by
  calc secOfMat dd V (secToMat qq V s)
      = ∑ a : I, ∑ b : I, (qq (a, b) ≫ dd (a, b)).val.app V s := rfl
    _ = ∑ k : I × I, (qq k ≫ dd k).val.app V s :=
        (Fintype.sum_prod_type (f := fun k : I × I => (qq k ≫ dd k).val.app V s)).symm
    _ = (∑ k : I × I, qq k ≫ dd k).val.app V s :=
        (app_sum Finset.univ (fun k : I × I => qq k ≫ dd k) V s).symm
    _ = s := by rw [htot]; rfl

omit [Fintype I] [DecidableEq I] in
/-- The matrix of the restriction of a section is the entrywise restriction of its matrix. -/
lemma secToMat_res {V W : Cᵒᵖ} (f : V ⟶ W) (s : ToType (A.val.obj V)) (a b : I) :
    (R.obj.map f).hom (secToMat qq V s a b) = secToMat qq W (A.val.map f s) a b :=
  (PresheafOfModules.naturality_apply (qq (a, b)).val f s).symm

omit [DecidableEq I] in
/-- The restriction of the section attached to a matrix `M` is the section attached to the
entrywise restriction of `M`. -/
lemma secOfMat_res {V W : Cᵒᵖ} (f : V ⟶ W) (M : Matrix I I (ToType (R.obj.obj V))) :
    A.val.map f (secOfMat dd V M)
      = secOfMat dd W (fun a b => (R.obj.map f).hom (M a b)) := by
  change A.val.map f (∑ a : I, ∑ b : I, (dd (a, b)).val.app V (toUnit V (M a b))) = _
  simp only [map_sum (A.val.map f).hom]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    (PresheafOfModules.naturality_apply (dd (a, b)).val f (toUnit V (M a b))).symm

end UnitSections

end Stacks.SheafOfModules

/-! ### The matrix dictionary for a free sheaf of modules on a scheme -/

namespace Stacks.EtaleCohomology.BrauerScheme

open Stacks.SheafOfModules

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {S : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]

/-- The matrix of an endomorphism of a finite free sheaf of `𝒪_S`-modules with respect to the
tautological points and coordinates. -/
def freeDualMatrix (f : freeModule S I ⟶ freeModule S I) : Matrix I I (R₀ S) :=
  dualBasisMatrix (fun i => freeInj (S := S) i) (fun j => freeProj j) f

omit [Fintype I] in
/-- The matrix of the identity is the identity matrix. -/
theorem freeDualMatrix_id : freeDualMatrix (𝟙 (freeModule S I)) = 1 :=
  dualBasisMatrix_id _ _ freeInj_comp_freeProj

/-- The matrix of a composite `f ≫ g` is the product of the matrices, in the same order. -/
theorem freeDualMatrix_comp (f g : freeModule S I ⟶ freeModule S I) :
    freeDualMatrix (f ≫ g) = freeDualMatrix f * freeDualMatrix g :=
  dualBasisMatrix_comp _ _ sum_freeProj_comp_freeInj f g

omit [Fintype I] in
/-- The matrix of a sum is the sum of the matrices. -/
theorem freeDualMatrix_add (f g : freeModule S I ⟶ freeModule S I) :
    freeDualMatrix (f + g) = freeDualMatrix f + freeDualMatrix g :=
  dualBasisMatrix_add _ _ f g

omit [Fintype I] in
/-- The matrix of the zero endomorphism is the zero matrix. -/
theorem freeDualMatrix_zero :
    freeDualMatrix (0 : freeModule S I ⟶ freeModule S I) = 0 :=
  dualBasisMatrix_zero _ _

omit [Fintype I] in
/-- An endomorphism of a finite free sheaf of `𝒪_S`-modules is determined by its matrix. -/
theorem freeDualMatrix_injective [Finite I] :
    Function.Injective (freeDualMatrix (S := S) (I := I)) := by
  have := Fintype.ofFinite I
  exact dualBasisMatrix_injective _ _ sum_freeProj_comp_freeInj

/-! ### Matrix units of the matrix algebra sheaf -/

/-- The `(a, b)` coordinate of the sheaf of `I × I` matrices over `𝒪_S`, read through the
identification of `End(𝒪_S^{(I)})` with the free sheaf of modules on `I × I`. -/
def matCoord (k : I × I) :
    (endAlgebra (freeModule S I)).X ⟶ 𝟙_ (ModuleSheaf S) :=
  (freeProdIsoEndAlgebra S I).inv ≫ freeProj k

/-- The `(a, b)` matrix unit of the sheaf of `I × I` matrices over `𝒪_S`, read through the
identification of `End(𝒪_S^{(I)})` with the free sheaf of modules on `I × I`. -/
def matIncl (k : I × I) :
    𝟙_ (ModuleSheaf S) ⟶ (endAlgebra (freeModule S I)).X :=
  freeInj k ≫ (freeProdIsoEndAlgebra S I).hom

/-- The matrix units and the coordinates are dual: `matIncl k ≫ matCoord l` is the identity if
`k = l` and zero otherwise. -/
theorem matIncl_comp_matCoord (k l : I × I) :
    matIncl (S := S) k ≫ matCoord l = if k = l then 𝟙 (𝟙_ (ModuleSheaf S)) else 0 :=
  (conj_inj_comp_conj_proj _ (fun k : I × I => freeInj (S := S) k)
    (fun k : I × I => freeProj k) k l).trans (freeInj_comp_freeProj k l)

/-- The coordinates and the matrix units decompose the identity:
`∑ k, matCoord k ≫ matIncl k = 𝟙 _`. -/
theorem sum_matCoord_comp_matIncl :
    ∑ k : I × I, matCoord (S := S) k ≫ matIncl k =
      𝟙 ((endAlgebra (freeModule S I)).X) :=
  sum_conj_proj_comp_conj_inj _ (fun k : I × I => freeInj (S := S) k)
    (fun k : I × I => freeProj k) sum_freeProj_comp_freeInj

omit [Fintype I] in
/-- A row of the system of matrix units, read on a coordinate of the free sheaf of modules on
`I × I`. -/
theorem freeMap_comp_freeProj (i a b : I) :
    SheafOfModules.freeMap (R := Tensor.ringSheaf S.sheaf) (fun j : I => (i, j)) ≫
        freeProj (S := S) (a, b)
      = if i = a then freeProj (S := S) b else 0 := by
  rcases eq_or_ne i a with rfl | h
  · refine Eq.trans ?_ (ite_eq_left rfl).symm
    refine freeModule_hom_ext_inj fun j => ?_
    refine (SheafOfModules.ιFree_freeMap_assoc (fun j : I => (i, j)) j _).trans ?_
    refine (freeInj_comp_freeProj (i, j) (i, b)).trans ?_
    exact (if_congr (by simp [Prod.ext_iff]) rfl rfl).trans
      (freeInj_comp_freeProj j b).symm
  · refine Eq.trans ?_ (ite_eq_right h).symm
    refine freeModule_hom_ext_inj fun j => ?_
    refine (SheafOfModules.ιFree_freeMap_assoc (fun j : I => (i, j)) j _).trans ?_
    refine ((freeInj_comp_freeProj (i, j) (a, b)).trans
      (ite_eq_right (by simp [Prod.ext_iff, h]))).trans ?_
    exact (Limits.comp_zero).symm

/-- **The coordinates of a point of the matrix algebra sheaf are the matrix entries of the
corresponding endomorphism.** -/
theorem curry'_comp_matCoord (f : freeModule S I ⟶ freeModule S I) (a b : I) :
    MonoidalClosed.curry' f ≫ matCoord (S := S) (a, b) = (freeDualMatrix f a b).asHom :=
  MonoidalClosed.curry'_comp_ihomIsoOfDualBasis_inv_comp
    (fun i => freeInj (S := S) i) (fun j => freeProj j) sum_freeProj_comp_freeInj
    freeInj_comp_freeProj (fun k => freeInj (S := S) k)
    (fun i => SheafOfModules.freeMap (R := Tensor.ringSheaf S.sheaf) (fun j => (i, j)))
    (fun i j => SheafOfModules.ιFree_freeMap (fun j => (i, j)) j)
    (fun hd => freeModule_hom_ext_inj hd) (fun hd => freeModule_hom_ext_inj hd)
    freeProdToEndAlgebra freeInj_comp_freeProdToEndAlgebra
    (fun k => freeProj k) freeMap_comp_freeProj f a b

/-! ### The matrix units under a morphism of sheaves of algebras -/

omit [Fintype I] in
/-- The matrix of a finite sum of endomorphisms is the sum of their matrices. -/
theorem freeDualMatrix_sum {κ : Type*} (t : Finset κ)
    (f : κ → (freeModule S I ⟶ freeModule S I)) :
    freeDualMatrix (∑ k ∈ t, f k) = ∑ k ∈ t, freeDualMatrix (f k) :=
  dualBasisMatrix_sum _ _ t f

/-- The matrix, over the endomorphism ring of `𝒪_S`, of the image of the `(a, b)` matrix unit
of `Mat_I(𝒪_S)` under a morphism of sheaves of algebras. -/
def pointMatrix (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (k : I × I) :
    Matrix I I (R₀ S) :=
  freeDualMatrix (MonoidalClosed.pointMap ϑ (MonoidalClosed.uncurry' (matIncl (S := S) k)))

/-- **A morphism of sheaves of algebras is seen on the matrix units through its action on
endomorphisms.** -/
theorem matIncl_comp_comp_matCoord
    (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (k : I × I) (a b : I) :
    matIncl (S := S) k ≫ ϑ.hom ≫ matCoord (a, b) = (pointMatrix ϑ k a b).asHom :=
  have h0 : MonoidalClosed.curry' (MonoidalClosed.pointMap ϑ
        (MonoidalClosed.uncurry' (matIncl (S := S) k))) = matIncl (S := S) k ≫ ϑ.hom :=
    (MonoidalClosed.curry'_pointMap ϑ _).trans
      (congrArg (fun z => z ≫ ϑ.hom) (MonoidalClosed.curry'_uncurry' (matIncl (S := S) k)))
  (((curry'_comp_matCoord _ a b).symm.trans
    (congrArg (fun z => z ≫ matCoord (S := S) (a, b)) h0)).trans (Category.assoc _ _ _)).symm

/-- The matrix of the `(a, b)` matrix unit is the `(a, b)` matrix unit. -/
theorem freeDualMatrix_uncurry'_matIncl (a b : I) :
    freeDualMatrix (MonoidalClosed.uncurry' (matIncl (S := S) (a, b)))
      = Matrix.single a b (1 : R₀ S) := by
  funext i j
  apply End.ext
  refine (((curry'_comp_matCoord _ i j).symm.trans
    (congrArg (fun z => z ≫ matCoord (S := S) (i, j))
      (MonoidalClosed.curry'_uncurry' (matIncl (S := S) (a, b))))).trans
    (matIncl_comp_matCoord (a, b) (i, j))).trans ?_
  rw [Matrix.single_apply]
  split_ifs <;> simp_all [Prod.ext_iff]

/-- **The matrix units of the matrix algebra sheaf satisfy the matrix unit relations.** -/
theorem uncurry'_matIncl_comp (a b c e : I) :
    MonoidalClosed.uncurry' (matIncl (S := S) (a, b)) ≫
        MonoidalClosed.uncurry' (matIncl (S := S) (c, e))
      = if b = c then MonoidalClosed.uncurry' (matIncl (S := S) (a, e)) else 0 := by
  rcases eq_or_ne b c with rfl | h
  · refine Eq.trans ?_ (ite_eq_left rfl).symm
    refine freeDualMatrix_injective ((freeDualMatrix_comp _ _).trans ?_)
    rw [freeDualMatrix_uncurry'_matIncl, freeDualMatrix_uncurry'_matIncl,
      freeDualMatrix_uncurry'_matIncl, Matrix.single_mul_single_same, mul_one]
  · refine Eq.trans ?_ (ite_eq_right h).symm
    refine freeDualMatrix_injective ((freeDualMatrix_comp _ _).trans ?_)
    rw [freeDualMatrix_uncurry'_matIncl, freeDualMatrix_uncurry'_matIncl, freeDualMatrix_zero,
      Matrix.single_mul_single_of_ne (h := h)]

/-- The diagonal matrix units of the matrix algebra sheaf add up to the identity. -/
theorem sum_uncurry'_matIncl :
    ∑ a : I, MonoidalClosed.uncurry' (matIncl (S := S) (a, a)) = 𝟙 (freeModule S I) := by
  refine freeDualMatrix_injective ((freeDualMatrix_sum _ _).trans ?_)
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
      freeDualMatrix_uncurry'_matIncl (S := S) a a,
    Matrix.sum_single_one, freeDualMatrix_id]

/-- **The images of the matrix units under a morphism of sheaves of algebras satisfy the matrix
unit relations.** -/
theorem pointMatrix_mul (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I))
    (a b c e : I) :
    pointMatrix ϑ (a, b) * pointMatrix ϑ (c, e) = if b = c then pointMatrix ϑ (a, e) else 0 := by
  have hcomp : pointMatrix ϑ (a, b) * pointMatrix ϑ (c, e)
      = freeDualMatrix (MonoidalClosed.pointMap ϑ
          (MonoidalClosed.uncurry' (matIncl (S := S) (a, b)) ≫
            MonoidalClosed.uncurry' (matIncl (S := S) (c, e)))) :=
    (freeDualMatrix_comp _ _).symm.trans
      (congrArg freeDualMatrix (MonoidalClosed.pointMap_comp ϑ _ _).symm)
  rw [hcomp, uncurry'_matIncl_comp]
  rcases eq_or_ne b c with rfl | h
  · rw [ite_eq_left rfl, ite_eq_left rfl]; rfl
  · rw [ite_eq_right h, ite_eq_right h, MonoidalClosed.pointMap_zero, freeDualMatrix_zero]

/-- **The images of the diagonal matrix units add up to the identity matrix.** -/
theorem sum_pointMatrix (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) :
    ∑ a : I, pointMatrix ϑ (a, a) = 1 := by
  have h : ∑ a : I, pointMatrix ϑ (a, a)
      = freeDualMatrix (MonoidalClosed.pointMap ϑ
          (∑ a : I, MonoidalClosed.uncurry' (matIncl (S := S) (a, a)))) :=
    (freeDualMatrix_sum _ _).symm.trans
      (congrArg freeDualMatrix (MonoidalClosed.pointMap_sum ϑ Finset.univ _).symm)
  rw [h, sum_uncurry'_matIncl, MonoidalClosed.pointMap_id, freeDualMatrix_id]

/-! ### Reading an automorphism of the matrix algebra sheaf on sections -/

/-- **The ring homomorphism from the endomorphisms of `𝒪_S` to the sections of `𝒪_S` over
`U`**: evaluate at the unit section. It is multiplicative in either order because `Γ(S, U)` is
commutative, which is what absorbs the reversal in `CategoryTheory.End`'s convention. -/
def unitEndValueHom (S : Scheme.{u}) (U : S.Opens) : R₀ S →+* Γ(S, U) where
  toFun r := _root_.Stacks.SheafOfModules.unitEndValue (op U) r
  map_one' := _root_.Stacks.SheafOfModules.unitEndValue_one (op U)
  map_mul' x y := (_root_.Stacks.SheafOfModules.unitEndValue_comp (op U) y x).trans
    (@mul_comm Γ(S, U) _ _ _)
  map_zero' := _root_.Stacks.SheafOfModules.unitEndValue_zero (op U)
  map_add' x y := _root_.Stacks.SheafOfModules.unitEndValue_add (op U) x y

/-- Restricting `unitEndValueHom S U r` from `U` to an open `V ≤ U` gives
`unitEndValueHom S V r`. -/
theorem unitEndValueHom_res {S : Scheme.{u}} {U V : S.Opens} (h : V ≤ U) (r : R₀ S) :
    (S.presheaf.map (homOfLE h).op).hom (unitEndValueHom S U r) = unitEndValueHom S V r :=
  _root_.Stacks.SheafOfModules.unitEndValue_res (homOfLE h).op r

/-- The map on matrices of sections over `U` induced by an endomorphism of the sheaf of modules
underlying the matrix algebra sheaf. -/
def sectionMap (ϑ : (endAlgebra (freeModule S I)).X ⟶ (endAlgebra (freeModule S I)).X)
    (U : S.Opens) (M : Matrix I I Γ(S, U)) : Matrix I I Γ(S, U) :=
  _root_.Stacks.SheafOfModules.secToMat (fun k : I × I => matCoord (S := S) k) (op U)
    (ϑ.val.app (op U)
      (_root_.Stacks.SheafOfModules.secOfMat (fun k : I × I => matIncl (S := S) k) (op U) M))

/-- The `(a, b)` entry of `sectionMap ϑ U M` is
`∑ c, ∑ e, M c e * unitEndValueHom S U (matIncl (c, e) ≫ ϑ ≫ matCoord (a, b))`. -/
theorem sectionMap_apply
    (ϑ : (endAlgebra (freeModule S I)).X ⟶ (endAlgebra (freeModule S I)).X)
    (U : S.Opens) (M : Matrix I I Γ(S, U)) (a b : I) :
    sectionMap ϑ U M a b = ∑ c : I, ∑ e : I,
      M c e * unitEndValueHom S U (End.of (matIncl (S := S) (c, e) ≫ ϑ ≫ matCoord (a, b))) :=
  _root_.Stacks.SheafOfModules.secToMat_app_secOfMat _ _ (op U) ϑ M a b

/-- The identity endomorphism induces the identity map on matrices of sections. -/
theorem sectionMap_id (U : S.Opens) (M : Matrix I I Γ(S, U)) :
    sectionMap (𝟙 ((endAlgebra (freeModule S I)).X)) U M = M :=
  _root_.Stacks.SheafOfModules.secToMat_secOfMat _ _ matIncl_comp_matCoord (op U) M

/-- The map induced by a composite `ϑ ≫ ϑ'` is the map induced by `ϑ'` after the map induced by
`ϑ`. -/
theorem sectionMap_comp
    (ϑ ϑ' : (endAlgebra (freeModule S I)).X ⟶ (endAlgebra (freeModule S I)).X)
    (U : S.Opens) (M : Matrix I I Γ(S, U)) :
    sectionMap (ϑ ≫ ϑ') U M = sectionMap ϑ' U (sectionMap ϑ U M) :=
  congrArg (fun y => _root_.Stacks.SheafOfModules.secToMat
      (fun k : I × I => matCoord (S := S) k) (op U) (ϑ'.val.app (op U) y))
    (_root_.Stacks.SheafOfModules.secOfMat_secToMat _ _ sum_matCoord_comp_matIncl (op U) _).symm

/-- The matrix over `Γ(S, U)` of the image of the `(a, b)` matrix unit. -/
def sectionPointMatrix (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I))
    (U : S.Opens) (k : I × I) : Matrix I I Γ(S, U) :=
  (pointMatrix ϑ k).map (unitEndValueHom S U)

/-- The matrices `sectionPointMatrix ϑ U k` satisfy the matrix unit relations: the product of the
`(a, b)` and the `(c, e)` matrices is the `(a, e)` matrix if `b = c`, and zero otherwise. -/
theorem sectionPointMatrix_mul (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I))
    (U : S.Opens) (a b c e : I) :
    sectionPointMatrix ϑ U (a, b) * sectionPointMatrix ϑ U (c, e)
      = if b = c then sectionPointMatrix ϑ U (a, e) else 0 := by
  rw [sectionPointMatrix, sectionPointMatrix, ← Matrix.map_mul, pointMatrix_mul]
  rcases eq_or_ne b c with rfl | h
  · rw [ite_eq_left rfl, ite_eq_left rfl, sectionPointMatrix]
  · rw [ite_eq_right h, ite_eq_right h]
    exact Matrix.map_zero _ (map_zero _)

/-- The diagonal matrices `sectionPointMatrix ϑ U (a, a)` add up to the identity matrix. -/
theorem sum_sectionPointMatrix
    (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (U : S.Opens) :
    ∑ a : I, sectionPointMatrix ϑ U (a, a) = 1 := by
  have h : ∑ a : I, sectionPointMatrix ϑ U (a, a)
      = (∑ a : I, pointMatrix ϑ (a, a)).map (unitEndValueHom S U) := by
    funext i j
    simp only [sectionPointMatrix, Matrix.sum_apply, Matrix.map_apply, map_sum]
  rw [h, sum_pointMatrix, Matrix.map_one _ (map_zero _) (map_one _)]

/-- For a morphism `ϑ` of sheaves of algebras, `sectionMap ϑ.hom U` is the linear map of matrices
sending the `(c, e)` matrix unit to `sectionPointMatrix ϑ U (c, e)`. -/
theorem sectionMap_eq_unitCombination
    (ϑ : endAlgebra (freeModule S I) ⟶ endAlgebra (freeModule S I)) (U : S.Opens)
    (M : Matrix I I Γ(S, U)) :
    sectionMap ϑ.hom U M = _root_.Stacks.Matrix.unitCombination (sectionPointMatrix ϑ U) M := by
  funext a b
  rw [sectionMap_apply, _root_.Stacks.Matrix.unitCombination_apply]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ =>
    congrArg (fun z => M c e * unitEndValueHom S U z)
      (End.ext (matIncl_comp_comp_matCoord ϑ (c, e) a b) :
        End.of (matIncl (S := S) (c, e) ≫ ϑ.hom ≫ matCoord (a, b)) = pointMatrix ϑ (c, e) a b)

/-- **An automorphism of the matrix algebra sheaf, read on the sections over an open set**, as an
algebra automorphism of `Matrix I I Γ(S, U)`. -/
def sectionAlgEquiv (Φ : endAlgebra (freeModule S I) ≅ endAlgebra (freeModule S I))
    (U : S.Opens) : Matrix I I Γ(S, U) ≃ₐ[Γ(S, U)] Matrix I I Γ(S, U) where
  toFun := sectionMap Φ.hom.hom U
  invFun := sectionMap Φ.inv.hom U
  left_inv M :=
    have hid : Φ.hom.hom ≫ Φ.inv.hom = 𝟙 ((endAlgebra (freeModule S I)).X) :=
      congrArg Mon.Hom.hom Φ.hom_inv_id
    ((sectionMap_comp Φ.hom.hom Φ.inv.hom U M).symm.trans
      (congrArg (fun z => sectionMap z U M) hid)).trans (sectionMap_id U M)
  right_inv M :=
    have hid : Φ.inv.hom ≫ Φ.hom.hom = 𝟙 ((endAlgebra (freeModule S I)).X) :=
      congrArg Mon.Hom.hom Φ.inv_hom_id
    ((sectionMap_comp Φ.inv.hom Φ.hom.hom U M).symm.trans
      (congrArg (fun z => sectionMap z U M) hid)).trans (sectionMap_id U M)
  map_mul' M N := by
    rw [sectionMap_eq_unitCombination Φ.hom U, sectionMap_eq_unitCombination Φ.hom U,
      sectionMap_eq_unitCombination Φ.hom U]
    exact _root_.Stacks.Matrix.unitCombination_mul _
      (fun a b c e => sectionPointMatrix_mul Φ.hom U a b c e) M N
  map_add' M N := by
    rw [sectionMap_eq_unitCombination Φ.hom U, sectionMap_eq_unitCombination Φ.hom U,
      sectionMap_eq_unitCombination Φ.hom U]
    exact _root_.Stacks.Matrix.unitCombination_add _ M N
  commutes' r := by
    rw [sectionMap_eq_unitCombination Φ.hom U, Algebra.algebraMap_eq_smul_one,
      _root_.Stacks.Matrix.unitCombination_smul,
      _root_.Stacks.Matrix.unitCombination_one _ (sum_sectionPointMatrix Φ.hom U)]

/-- The map induced on matrices of sections commutes with restriction from `U` to an open `V ≤ U`,
applied entrywise. -/
theorem sectionMap_res
    (ϑ : (endAlgebra (freeModule S I)).X ⟶ (endAlgebra (freeModule S I)).X)
    {U V : S.Opens} (h : V ≤ U) (M : Matrix I I Γ(S, U)) :
    sectionMap ϑ V (M.map (S.presheaf.map (homOfLE h).op).hom)
      = (sectionMap ϑ U M).map (S.presheaf.map (homOfLE h).op).hom := by
  funext a b
  simp only [sectionMap_apply, Matrix.map_apply, map_sum, map_mul, unitEndValueHom_res]

/-! ### The overlap step of Tag 0A2L -/

/-- **An automorphism of the sheaf of `d × d` matrices over `𝒪_T`, read on the sections over an
open set**, as an algebra automorphism of `Matrix (Fin d) (Fin d) Γ(T, U)`. -/
def matrixAlgebraSectionAlgEquiv {T : Scheme.{u}} {d : ℕ}
    (Φ : matrixAlgebra T d ≅ matrixAlgebra T d) (U : T.Opens) :
    Matrix (Fin d) (Fin d) Γ(T, U) ≃ₐ[Γ(T, U)] Matrix (Fin d) (Fin d) Γ(T, U) :=
  (Matrix.reindexAlgEquiv Γ(T, U) Γ(T, U) (Equiv.ulift.{u, 0} (α := Fin d)).symm).trans
    ((sectionAlgEquiv Φ U).trans
      (Matrix.reindexAlgEquiv Γ(T, U) Γ(T, U) (Equiv.ulift.{u, 0} (α := Fin d))))

/-- **The family of algebra automorphisms is compatible with restriction.** -/
theorem matrixAlgebraSectionAlgEquiv_res {T : Scheme.{u}} {d : ℕ}
    (Φ : matrixAlgebra T d ≅ matrixAlgebra T d) (U V : T.Opens) (h : V ≤ U)
    (M : Matrix (Fin d) (Fin d) Γ(T, U)) :
    matrixAlgebraSectionAlgEquiv Φ V (M.map (T.presheaf.map (homOfLE h).op).hom)
      = (matrixAlgebraSectionAlgEquiv Φ U M).map (T.presheaf.map (homOfLE h).op).hom :=
  congrArg (Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d))
      (Equiv.ulift.{u, 0} (α := Fin d)))
    (sectionMap_res Φ.hom.hom h
      (Matrix.reindex (Equiv.ulift.{u, 0} (α := Fin d)).symm
        (Equiv.ulift.{u, 0} (α := Fin d)).symm M))

/-- **The overlap step of [Stacks, Tag 0A2L].** An automorphism of the sheaf of `d × d` matrices
over `𝒪_T` is, on a neighbourhood of any point of `T`, conjugation by a single invertible matrix
of sections of `𝒪_T`, compatibly with all further restriction.

The automorphism is read on sections by `matrixAlgebraSectionAlgEquiv`, and the conjugating matrix
is produced by `Stacks.AlgebraicGeometry.exists_units_conj_eq_of_algEquiv_sheaf`, Skolem--Noether
spread out from a stalk. -/
theorem exists_units_conj_eq_of_iso_matrixAlgebra {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (Φ : matrixAlgebra T d ≅ matrixAlgebra T d) (x : T) :
    ∃ (U : T.Opens) (_ : x ∈ U) (u : (Matrix (Fin d) (Fin d) Γ(T, U))ˣ),
      ∀ (V : T.Opens) (h : V ≤ U) (M : Matrix (Fin d) (Fin d) Γ(T, U)),
        matrixAlgebraSectionAlgEquiv Φ V (M.map (T.presheaf.map (homOfLE h).op).hom) =
          (u : Matrix (Fin d) (Fin d) Γ(T, U)).map (T.presheaf.map (homOfLE h).op).hom *
            M.map (T.presheaf.map (homOfLE h).op).hom *
            ((u⁻¹ : (Matrix (Fin d) (Fin d) Γ(T, U))ˣ) :
              Matrix (Fin d) (Fin d) Γ(T, U)).map (T.presheaf.map (homOfLE h).op).hom :=
  Stacks.AlgebraicGeometry.exists_units_conj_eq_of_algEquiv_sheaf
    (fun U => matrixAlgebraSectionAlgEquiv Φ U)
    (matrixAlgebraSectionAlgEquiv_res Φ) x

end Stacks.EtaleCohomology.BrauerScheme

end

end
