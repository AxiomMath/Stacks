module

public import StacksFrontier.CategoryTheory.Sites.CechComplexSlice

/-!
# The Čech complex of a covering: in the slice category or in the lattice

A covering of an open `V` by opens `U i` gives rise to two Čech complexes, and both are instances
of Mathlib's `CategoryTheory.cechComplexFunctor`.

* Stacks 01EP forms it in the **slice category** `Over V`, for the family
  `i ↦ Over.mk (homOfLE (hU i))` and a presheaf on `(Over V)ᵒᵖ`.
* Stacks 01FG forms it in the **lattice** `Opens X` itself, for the family `U` and a presheaf on
  `(Opens X)ᵒᵖ`.

For a presheaf on the lattice restricted along the forgetful functor, the two complexes are
isomorphic. A Čech intersection formed in `Over V` has the infimum of the selected members as its
underlying element (`interOver_left_eq_iInf`), so the two complexes have the same degreewise
factors, and since the lattice is thin the restriction maps appearing in the two differentials
agree.

All names are in the namespace `Stacks.CategoryTheory.CechComplex`.

## Main definitions

* `overFamily`: the covering family viewed in `Over V`.
* `sliceDown`, `sliceUp`: the degreewise comparison maps.
* `sliceComplexIso`: the Čech complex of the family in `Over V` is isomorphic to the Čech complex
  of the family in the lattice.

## Main results

* `interOver_left_eq`: the underlying element of a Čech intersection formed in `Over V` is the Čech
  intersection formed in the lattice.
* `map_op_eq_of_thin`: a presheaf on a complete lattice sends parallel morphisms to the same map.
* `sliceDown_comp_d`: the comparison commutes with the differentials.
* `isZero_homology_slice_iff`: the two Čech cohomology objects vanish together.

## Implementation notes

The degreewise factors are *equal* and not merely isomorphic, but no `eqToHom` is used: the
comparison maps are built from the two restriction maps `P.map` along the inequalities the equality
provides, and they are mutually inverse because their composites are `P.map` of a morphism parallel
to the identity.

Only tuples of length `n + 1` occur, which is what makes the comparison true: the empty product in
`Over V` is `V` itself while the empty infimum is `⊤`.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u u'

namespace Stacks.CategoryTheory.CechComplex

section SliceBase

variable {L : Type u} [CompleteLattice L] [HasFiniteProducts L] {V : L}
  [HasFiniteProducts (Over V)]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → L) (hU : ∀ i, U i ≤ V) (P : Lᵒᵖ ⥤ A)

omit [HasFiniteProducts L] [Preadditive A] [HasProducts.{w} A] in
/-- A presheaf on a complete lattice sends parallel morphisms to the same map. -/
theorem map_op_eq_of_thin {a b : L} (f g : a ⟶ b) : P.map f.op = P.map g.op := by
  rw [Subsingleton.elim f g]

/-- Restrictions of a presheaf along `a ≤ b` and `b ≤ a` compose to the identity. -/
private theorem map_op_comp_map_op_eq_id {L' : Type*} [CompleteLattice L'] {A' : Type*}
    [Category A'] (P' : L'ᵒᵖ ⥤ A') {a b : L'} (f : a ⟶ b) (g : b ⟶ a) :
    P'.map f.op ≫ P'.map g.op = 𝟙 _ := by
  rw [← P'.map_comp, ← op_comp, map_op_eq_of_thin P' _ (𝟙 _), op_id, P'.map_id]

include hU

/-- The members of a covering of `V`, viewed as objects of the slice category over `V`: the family
whose Čech complex Stacks 01EP forms. -/
def overFamily (i : ι) : Over V :=
  Over.mk (homOfLE (hU i))

/-- **The Čech intersections of the two families agree.** The underlying element of the Čech
intersection formed in `Over V` is the Čech intersection formed in the lattice. -/
theorem interOver_left_eq {m : ℕ} (x : Fin (m + 1) → ι) :
    (inter (overFamily U hU) x).left = inter U x :=
  (interOver_left_eq_iInf U hU x).trans (inter_eq_iInf U x).symm

/-- The restriction of sections of `P` from the Čech intersection formed in the lattice to the
underlying element of the Čech intersection formed in `Over V`, which is equal to it. -/
noncomputable def interRestrictUp {m : ℕ} (x : Fin (m + 1) → ι) :
    P.obj (op (inter U x)) ⟶ P.obj (op (inter (overFamily U hU) x).left) :=
  P.map (homOfLE (le_of_eq (interOver_left_eq U hU x))).op

/-- The restriction of sections of `P` from the underlying element of the Čech intersection formed
in `Over V` to the Čech intersection formed in the lattice, which is equal to it. -/
noncomputable def interRestrictDown {m : ℕ} (x : Fin (m + 1) → ι) :
    P.obj (op (inter (overFamily U hU) x).left) ⟶ P.obj (op (inter U x)) :=
  P.map (homOfLE (le_of_eq (interOver_left_eq U hU x).symm)).op

omit [Preadditive A] [HasProducts.{w} A] in
/-- Restricting down to the lattice intersection and back up is the identity. -/
@[simp]
theorem interRestrictDown_comp_interRestrictUp {m : ℕ} (x : Fin (m + 1) → ι) :
    interRestrictDown U hU P x ≫ interRestrictUp U hU P x = 𝟙 _ := by
  exact map_op_comp_map_op_eq_id P _ _

omit [Preadditive A] [HasProducts.{w} A] in
/-- Restricting up to the intersection formed in `Over V` and back down is the identity. -/
@[simp]
theorem interRestrictUp_comp_interRestrictDown {m : ℕ} (x : Fin (m + 1) → ι) :
    interRestrictUp U hU P x ≫ interRestrictDown U hU P x = 𝟙 _ := by
  exact map_op_comp_map_op_eq_id P _ _

/-- The projection of the degree `n` term of the Čech complex formed in `Over V` onto the factor
indexed by `x`, with its target read as the sections of `P` over the underlying element of the Čech
intersection. -/
noncomputable def πSlice (n : ℕ) (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P)).X n ⟶
      P.obj (op (inter (overFamily U hU) x).left) :=
  π (overFamily U hU) ((Over.forget V).op ⋙ P) n x

/-- The degree `n` comparison map from the Čech complex formed in `Over V` to the Čech complex
formed in the lattice. -/
noncomputable def sliceDown (n : ℕ) :
    ((cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P)).X n ⟶
      ((cechComplexFunctor U).obj P).X n :=
  lift U P fun x ↦ πSlice U hU P n x ≫ interRestrictDown U hU P x

/-- The degree `n` comparison map from the Čech complex formed in the lattice to the Čech complex
formed in `Over V`. -/
noncomputable def sliceUp (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶
      ((cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P)).X n :=
  lift (overFamily U hU) ((Over.forget V).op ⋙ P) fun x ↦
    π U P n x ≫ interRestrictUp U hU P x

/-- The comparison map followed by the projection onto the factor indexed by `x` is the projection
of the complex formed in `Over V` followed by `interRestrictDown`. -/
@[reassoc (attr := simp)]
theorem sliceDown_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    sliceDown U hU P n ≫ π U P n x = πSlice U hU P n x ≫ interRestrictDown U hU P x :=
  lift_comp_π U P _ x

/-- The comparison map followed by the projection onto the factor indexed by `x` is the projection
of the complex formed in the lattice followed by `interRestrictUp`. -/
@[reassoc (attr := simp)]
theorem sliceUp_comp_πSlice (n : ℕ) (x : Fin (n + 1) → ι) :
    sliceUp U hU P n ≫ πSlice U hU P n x = π U P n x ≫ interRestrictUp U hU P x :=
  lift_comp_π (overFamily U hU) ((Over.forget V).op ⋙ P) _ x

/-- `sliceDown` followed by `sliceUp` is the identity. -/
theorem sliceDown_comp_sliceUp (n : ℕ) :
    sliceDown U hU P n ≫ sliceUp U hU P n = 𝟙 _ :=
  hom_ext (overFamily U hU) ((Over.forget V).op ⋙ P) fun x ↦ by
    rw [Category.assoc, show π (overFamily U hU) ((Over.forget V).op ⋙ P) n x =
        πSlice U hU P n x from rfl, sliceUp_comp_πSlice, sliceDown_comp_π_assoc,
      interRestrictDown_comp_interRestrictUp, Category.comp_id, Category.id_comp]

/-- `sliceUp` followed by `sliceDown` is the identity. -/
theorem sliceUp_comp_sliceDown (n : ℕ) :
    sliceUp U hU P n ≫ sliceDown U hU P n = 𝟙 _ :=
  hom_ext U P fun x ↦ by
    rw [Category.assoc, sliceDown_comp_π, sliceUp_comp_πSlice_assoc,
      interRestrictUp_comp_interRestrictDown, Category.comp_id, Category.id_comp]

/-- The degree `n` comparison map is an isomorphism. -/
theorem isIso_sliceDown (n : ℕ) : IsIso (sliceDown U hU P n) :=
  ⟨sliceUp U hU P n, sliceDown_comp_sliceUp U hU P n, sliceUp_comp_sliceDown U hU P n⟩

omit [Preadditive A] [HasProducts.{w} A] in
/-- **The restriction maps occurring in the two Čech differentials agree.** For the face
`y ∘ i.succAbove`, the restriction of the lattice complex after `interRestrictDown` is
`interRestrictDown` after the restriction of the complex formed in `Over V`. -/
theorem interRestrictDown_comp_map_interMap (n : ℕ) (y : Fin (n + 2) → ι) (i : Fin (n + 2)) :
    interRestrictDown U hU P (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op =
      ((Over.forget V).op ⋙ P).map (interMap (overFamily U hU) y i.succAbove).op ≫
        interRestrictDown U hU P y := by
  dsimp only [interRestrictDown]
  rw [← P.map_comp, ← op_comp]
  show _ = P.map ((Over.forget V).map (interMap (overFamily U hU) y i.succAbove)).op ≫
    P.map (homOfLE (le_of_eq (interOver_left_eq U hU y).symm)).op
  rw [← P.map_comp, ← op_comp]
  exact map_op_eq_of_thin P _ _

/-- **The comparison is a chain map.** The degreewise comparison maps commute with the
differentials of the two Čech complexes. -/
theorem sliceDown_comp_d (n : ℕ) :
    sliceDown U hU P n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P)).d n (n + 1) ≫
        sliceDown U hU P (n + 1) :=
  hom_ext U P fun y ↦ by
    simp only [Category.assoc]
    rw [d_comp_π, sliceDown_comp_π, Preadditive.comp_sum,
      show πSlice U hU P (n + 1) y =
        π (overFamily U hU) ((Over.forget V).op ⋙ P) (n + 1) y from rfl,
      ← Category.assoc, d_comp_π, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    rw [← Category.assoc, sliceDown_comp_π, Category.assoc, Category.assoc,
      interRestrictDown_comp_map_interMap U hU P n y i]
    rfl

/-- The degreewise comparison maps, assembled into a morphism of cochain complexes. -/
noncomputable def sliceDownHom :
    (cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P) ⟶
      (cechComplexFunctor U).obj P where
  f := sliceDown U hU P
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact sliceDown_comp_d U hU P i

/-- **The two Čech complexes of a covering agree.** The Čech complex of the covering family in the
slice category `Over V`, with coefficients in a presheaf on the lattice restricted along the
forgetful functor, is the Čech complex of the covering family in the lattice itself. -/
noncomputable def sliceComplexIso :
    (cechComplexFunctor (overFamily U hU)).obj ((Over.forget V).op ⋙ P) ≅
      (cechComplexFunctor U).obj P :=
  haveI (n : ℕ) : IsIso ((sliceDownHom U hU P).f n) := isIso_sliceDown U hU P n
  haveI := HomologicalComplex.Hom.isIso_of_components (sliceDownHom U hU P)
  asIso (sliceDownHom U hU P)

/-- The two Čech cohomology objects of a covering vanish together. -/
theorem isZero_homology_slice_iff [CategoryWithHomology A] (n : ℕ) :
    IsZero (((cechComplexFunctor (overFamily U hU)).obj
        ((Over.forget V).op ⋙ P)).homology n) ↔
      IsZero (((cechComplexFunctor U).obj P).homology n) :=
  (HomologicalComplex.homologyMapIso (sliceComplexIso U hU P) n).isZero_iff

end SliceBase

end Stacks.CategoryTheory.CechComplex

end
