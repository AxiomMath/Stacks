module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexCompShift
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.TriangulatedIso

/-!
# Axiom (B) for the differential graded category of complexes

`CochainComplex.dgCategory B` — the differential graded category of complexes of Tag 09L9, and
the `C` of Tag 09LK — carries no `DGCategory.ShiftAxiomB`: that structure asks of the shift the
strict equalities of objects `X[0] = X` and `X[n + m] = X[n][m]`, and Mathlib's shift reindexes a
complex by `p + n`, so those would have to be proved by transporting a whole
`HomologicalComplex` structure along `p + 0 = p` and `p + (n + m) = p + n + m`. What Mathlib has
instead are `CategoryTheory.shiftFunctorZero` and `CategoryTheory.shiftFunctorAdd`, isomorphisms.

`DGCategory.ShiftAxiomBIso` is axiom (B) with exactly those four strict fields replaced by
isomorphisms of `Comp(A)` and their naturality for homogeneous morphisms of every degree. This
file builds that datum for the differential graded category of complexes.

## Main definitions

* `CochainComplex.dgZeroIso` and `CochainComplex.dgAddIso`: the comparisons `X[0] ≅ X` and
  `X[n + m] ≅ X[n][m]` of the category of complexes of `CochainComplex.dgCategory B`, read off
  from Mathlib's `CategoryTheory.shiftFunctorZero` and `CategoryTheory.shiftFunctorAdd` through
  `CochainComplex.cochainToComplexFunctor`.
* `CochainComplex.dgShiftAxiomBIso`: **axiom (B), in its isomorphism-valued form, for the
  differential graded category of complexes.**

## Main results

* `CochainComplex.dgZeroIso_natural` and `CochainComplex.dgAddIso_natural`: the two comparisons
  are natural for homogeneous morphisms of every degree, not only for maps of complexes. Both are
  sign-free: the Koszul sign of `CochainComplex.dgShiftFunctor` is additive in the shift index,
  `(-1)^((n + m)k) = (-1)^(nk) (-1)^(mk)`, so the signs on the two sides of `dgAddIso_natural`
  agree before any computation on components, and `(-1)^(0 · k) = 1`.
* `CochainComplex.rightShift_comp_left_eq`: shifting the target of a composite shifts its right
  factor on the nose and its left factor by `CochainComplex.HomComplex.Cochain.shift`, with no
  sign. The Koszul sign `(-1)^(nm)` in `DGCategory.ShiftAxiomBIso.toShift_comp_left` is the one
  `CochainComplex.dgShiftFunctor` puts on the left factor, and the two cancel.

## Implementation notes

Composition in `CochainComplex.dgCategory B` is `CochainComplex.HomComplex.Cochain.comp`, which
is diagrammatic, while `DGCategory.comp` is written in the order of composition of functions; and
the objects `(CochainComplex.dgShiftFunctor B n).obj x` and
`(CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).obj x` are equal only by unfolding a
semireducible definition. Each statement about components is stated in Mathlib's vocabulary, and
the fields of the structure are obtained from it at default transparency.

The identification of Hom modules and its compatibilities `toShift`, `toShift_d` and
`toShift_comp_right` are those of `CochainComplex.dgShiftComparisonData`, and the shift functors
are `CochainComplex.dgShiftFunctor`.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK).
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

open CochainComplex.HomComplex

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-- Applying the sign `(-1)^n` twice is the identity. -/
private alias negOnePow_smul_involutive := CochainComplex.negOnePow_smul_cancel

variable (B) in
/-- The comparison `X[0] ≅ X` of the category of complexes of `CochainComplex.dgCategory B`,
the image of `CategoryTheory.shiftFunctorZero` under `CochainComplex.cochainToComplexFunctor`. -/
noncomputable def dgZeroIso (x : CochainComplex B ℤ) :
    (show (dgCategory B).Comp from (dgShiftFunctor B 0).obj x) ≅
      (show (dgCategory B).Comp from x) :=
  (cochainToComplexFunctor B).mapIso
    ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).app x)

variable (B) in
/-- The comparison `X[n + m] ≅ X[n][m]` of the category of complexes of
`CochainComplex.dgCategory B`, the image of `CategoryTheory.shiftFunctorAdd` under
`CochainComplex.cochainToComplexFunctor`. -/
noncomputable def dgAddIso (n m : ℤ) (x : CochainComplex B ℤ) :
    (show (dgCategory B).Comp from (dgShiftFunctor B (n + m)).obj x) ≅
      (show (dgCategory B).Comp from (dgShiftFunctor B m).obj ((dgShiftFunctor B n).obj x)) :=
  (cochainToComplexFunctor B).mapIso
    ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).app x)

/-- The underlying cochain of `CochainComplex.dgZeroIso B x` is that of
`CategoryTheory.shiftFunctorZero`. -/
theorem dgZeroIso_hom_val (x : CochainComplex B ℤ) :
    (dgZeroIso B x).hom.1 =
      Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app x) :=
  rfl

/-- The underlying cochain of `CochainComplex.dgAddIso B n m x` is that of
`CategoryTheory.shiftFunctorAdd`. -/
theorem dgAddIso_hom_val (n m : ℤ) (x : CochainComplex B ℤ) :
    (dgAddIso B n m x).hom.1 =
      Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app x) :=
  rfl

/-- The comparison of `CategoryTheory.shiftFunctorZero` is natural for cochains of every degree,
with the Koszul sign of the shift by `0` included. -/
private theorem dgZeroIso_natural_aux {x y : CochainComplex B ℤ} {k : ℤ} (f : Cochain x y k) :
    ((((0 : ℤ) * k).negOnePow • f.shift 0).comp
        (Cochain.ofHom ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app y))
        (add_zero k)) =
      (Cochain.ofHom
          ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app x)).comp f
        (zero_add k) := by
  rw [zero_mul, Int.negOnePow_zero, one_smul]
  ext p q hpq
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.shift_v f 0 p q hpq p q (add_zero p).symm (add_zero q).symm,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftFunctorZero_hom_app_f, shiftFunctorZero_hom_app_f]
  simp

/-- The comparison of `CategoryTheory.shiftFunctorAdd` is natural for cochains of every degree,
without signs: shifting by `n + m` is shifting by `n` and then by `m`. -/
private theorem shift_add_comp_eq (n m : ℤ) {x y : CochainComplex B ℤ} {k : ℤ}
    (f : Cochain x y k) :
    (f.shift (n + m)).comp
        (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app y))
        (add_zero k) =
      (Cochain.ofHom
          ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app x)).comp
        ((f.shift n).shift m) (zero_add k) := by
  ext p q hpq
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.shift_v f (n + m) p q hpq (p + m + n) (q + m + n) (by ring) (by ring),
    Cochain.shift_v (f.shift n) m p q hpq (p + m) (q + m) rfl rfl,
    Cochain.shift_v f n (p + m) (q + m) (by lia) (p + m + n) (q + m + n) rfl rfl,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftFunctorAdd_hom_app_f, shiftFunctorAdd_hom_app_f]
  simp [HomologicalComplex.XIsoOfEq]

/-- The comparison of `CategoryTheory.shiftFunctorAdd` is natural for cochains of every degree,
with the Koszul signs of the shifts included. -/
private theorem dgAddIso_natural_aux (n m : ℤ) {x y : CochainComplex B ℤ} {k : ℤ}
    (f : Cochain x y k) :
    (((n + m) * k).negOnePow • f.shift (n + m)).comp
        (Cochain.ofHom ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app y))
        (add_zero k) =
      (Cochain.ofHom
          ((CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).hom.app x)).comp
        ((m * k).negOnePow • ((n * k).negOnePow • f.shift n).shift m) (zero_add k) := by
  rw [Cochain.shift_units_smul, smul_smul, ← Int.negOnePow_add,
    show m * k + n * k = (n + m) * k by ring, Cochain.units_smul_comp, Cochain.comp_units_smul]
  exact congrArg _ (shift_add_comp_eq n m f)

/-- Shifting the target of a composite of cochains shifts the right factor on the nose and the
left factor by `CochainComplex.HomComplex.Cochain.shift`, with no sign. -/
theorem rightShift_comp_left_eq {X Y Z : CochainComplex B ℤ} {l m n : ℤ}
    (g : Cochain Y Z m) (f : Cochain X Y (l + n)) (h : (l + n) + m = (m + l) + n)
    (h' : l + m = m + l) :
    (f.comp g h).rightShift n (m + l) rfl =
      (f.rightShift n l rfl).comp (g.shift n) h' := by
  ext p q hpq
  rw [(f.comp g h).rightShift_v n (m + l) rfl p q hpq (q + n) (by lia),
    Cochain.comp_v f g h p (p + l + n) (q + n) (by lia) (by lia),
    Cochain.comp_v (f.rightShift n l rfl) (g.shift n) h' p (p + l) q rfl (by lia),
    f.rightShift_v n l rfl p (p + l) rfl (p + l + n) (by lia),
    Cochain.shift_v g n (p + l) q (by lia) (p + l + n) (q + n) rfl rfl]
  simp

/-- Shifting the target of a composite of cochains, with the sign `(-1)^(nm)` and the Koszul sign
of `CochainComplex.dgShiftFunctor` on the left factor, which cancel. -/
private theorem toShift_comp_left_aux (n : ℤ) {x y z : CochainComplex B ℤ} {l m : ℤ}
    (g : Cochain y z m) (f : Cochain x y (l + n)) :
    (f.comp g (by omega : (l + n) + m = (m + l) + n)).rightShift n (m + l) rfl =
      (-1 : ℤ) ^ (n * m).natAbs •
        ((f.rightShift n l rfl).comp ((n * m).negOnePow • g.shift n)
          (by omega : l + m = m + l)) := by
  rw [Cochain.comp_units_smul, negOnePow_smul_involutive]
  exact rightShift_comp_left_eq g f (by lia) (by lia)

/-- The comparison `X[0] ≅ X` is natural for homogeneous morphisms of every degree. -/
theorem dgZeroIso_natural {x y : CochainComplex B ℤ} {k : ℤ} (f : (dgCategory B).Hom x y k) :
    (dgCategory B).comp (zero_add k) (dgZeroIso B y).hom.1 ((dgShiftFunctor B 0).map f) =
      (dgCategory B).comp (add_zero k) f (dgZeroIso B x).hom.1 :=
  dgZeroIso_natural_aux f

/-- The comparison `X[n + m] ≅ X[n][m]` is natural for homogeneous morphisms of every
degree. -/
theorem dgAddIso_natural (n m : ℤ) {x y : CochainComplex B ℤ} {k : ℤ}
    (f : (dgCategory B).Hom x y k) :
    (dgCategory B).comp (zero_add k) (dgAddIso B n m y).hom.1
        ((dgShiftFunctor B (n + m)).map f) =
      (dgCategory B).comp (add_zero k)
        ((dgShiftFunctor B m).map ((dgShiftFunctor B n).map f)) (dgAddIso B n m x).hom.1 :=
  dgAddIso_natural_aux n m f

/-- Axiom (B) for the differential graded category of complexes, with the shift additive on
objects up to isomorphism. The shift functors are `CochainComplex.dgShiftFunctor`, the
translations of `Comp(A)` and `K(A)` are `CochainComplex.dgCompShift` and
`CochainComplex.dgCategoryKShift`, the identification of Hom modules together with its
compatibility with the differential and with composition on the right is
`CochainComplex.dgShiftComparisonData`, and the two comparisons of objects are
`CochainComplex.dgZeroIso` and `CochainComplex.dgAddIso`. -/
noncomputable def dgShiftAxiomBIso (B : Type u) [Category.{v} B] [Preadditive B] :
    DGCategory.ShiftAxiomBIso (dgCategory B) where
  shiftFunctor := dgShiftFunctor B
  compShift := dgCompShift B
  kShift := dgCategoryKShift B
  compShift_functor := dgCompShift_shiftFunctor B
  kShift_functor := dgCategoryKShift_shiftFunctor B
  zeroIso := dgZeroIso B
  zeroIso_natural := dgZeroIso_natural
  addIso := dgAddIso B
  addIso_natural := dgAddIso_natural
  toShift := (dgShiftComparisonData B).toShift
  toShift_d := (dgShiftComparisonData B).toShift_d
  toShift_comp_right := (dgShiftComparisonData B).toShift_comp_right
  toShift_comp_left := by
    intro n x y z l m g f
    exact toShift_comp_left_aux n g f

end CochainComplex
