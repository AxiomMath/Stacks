module

public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Axiom (B) with the shift additive on objects only up to isomorphism

`DGCategory.ShiftAxiomB` asks of the shift functors `x ↦ x[n]` of a differential graded category
that they be *strictly* additive on objects: `x[0] = x` and `x[n + m] = x[n][m]` as equalities of
objects, with the corresponding heterogeneous equalities for the action on homogeneous
morphisms. In the isomorphism-valued variant `DGCategory.ShiftAxiomBIso`, each strict equality of
objects becomes an isomorphism of `Comp(A)`, that is, a closed degree-zero morphism with a closed
degree-zero inverse, and each heterogeneous equality of homogeneous morphisms becomes an equation
inside a single Hom module of `A`, with the comparison inserted.

## Main definitions

* `DGCategory.ShiftAxiomBIso`: axiom (B) with the shift additive on objects up to isomorphism.
* `DGCategory.ShiftAxiomB.toShiftAxiomBIso`: the strict form implies this one, the comparisons
  being the identities read along the equalities of objects.
* `DGCategory.ShiftAxiomBIso.unshiftIso` and `DGCategory.ShiftAxiomBIso.reshiftIso`: the two
  round trips `x[1][-1] ≅ x` and `z[-1][1] ≅ z`.
* `DGCategory.ShiftAxiomBIso.indexIso`: the comparison `x[n] ≅ x[m]` for equal indices, and
  `DGCategory.eqCompIso`, an equality of objects read as an isomorphism of `Comp(A)`.

## Main results

* `DGCategory.ShiftAxiomBIso.unshiftIso_natural` and
  `DGCategory.ShiftAxiomBIso.reshiftIso_natural`: the two round trips are natural for
  homogeneous morphisms of every degree.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded category of
  complexes.
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- **Axiom (B) with the shift additive on objects only up to isomorphism.** The shift functors
and their identifications of Hom complexes, as in `DGCategory.ShiftAxiomB`, except that the two
equalities of objects `x[0] = x` and `x[n + m] = x[n][m]` are replaced by isomorphisms of
`Comp(A)` and the two heterogeneous equalities of homogeneous morphisms by the corresponding
equations with the comparison inserted. -/
structure ShiftAxiomBIso (A : DGCategory.{v, u} R) where
  /-- The shift functors `x ↦ x[n]`. -/
  shiftFunctor : ℤ → DGCategory.DGFunctor A A
  /-- The translation of the category of complexes. -/
  compShift : HasShift A.Comp ℤ
  /-- The translation of the homotopy category. -/
  kShift : HasShift A.K ℤ
  /-- The translation of `Comp(A)` is the shift functor. -/
  compShift_functor : ∀ n : ℤ,
    letI := compShift
    CategoryTheory.shiftFunctor A.Comp n = (shiftFunctor n).onComp
  /-- The translation of `K(A)` is the shift functor. -/
  kShift_functor : ∀ n : ℤ,
    letI := kShift
    CategoryTheory.shiftFunctor A.K n = (shiftFunctor n).onK
  /-- The comparison `x[0] ≅ x`. -/
  zeroIso : ∀ x : A.Obj, (show A.Comp from (shiftFunctor 0).obj x) ≅ (show A.Comp from x)
  /-- It is natural for homogeneous morphisms of every degree. -/
  zeroIso_natural : ∀ {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    A.comp (zero_add k) (zeroIso y).hom.1 ((shiftFunctor 0).map f) =
      A.comp (add_zero k) f (zeroIso x).hom.1
  /-- The comparison `x[n + m] ≅ x[n][m]`. -/
  addIso : ∀ (n m : ℤ) (x : A.Obj),
    (show A.Comp from (shiftFunctor (n + m)).obj x) ≅
      (show A.Comp from (shiftFunctor m).obj ((shiftFunctor n).obj x))
  /-- It is natural for homogeneous morphisms of every degree. -/
  addIso_natural : ∀ (n m : ℤ) {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    A.comp (zero_add k) (addIso n m y).hom.1 ((shiftFunctor (n + m)).map f) =
      A.comp (add_zero k) ((shiftFunctor m).map ((shiftFunctor n).map f))
        (addIso n m x).hom.1
  /-- A degree `k + n` morphism `x ⟶ y` is a degree `k` morphism `x ⟶ y[n]`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ),
    A.Hom x y (k + n) ≃ₗ[R] A.Hom x ((shiftFunctor n).obj y) k
  /-- The identification multiplies the differential by `(-1)^n`. -/
  toShift_d : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)),
    toShift n x y (k + 1) (A.d' (by omega : (k + n) + 1 = (k + 1) + n) f) =
      (-1 : R) ^ n.natAbs • A.d (toShift n x y k f)
  /-- The identification does not change composition on the right. -/
  toShift_comp_right : ∀ (n : ℤ) {x y z : A.Obj} {l m : ℤ}
    (g : A.Hom y z (m + n)) (f : A.Hom x y l),
    toShift n x z (m + l) (A.comp (by omega : (m + n) + l = (m + l) + n) g f) =
      A.comp (by omega : m + l = m + l) (toShift n y z m g) f
  /-- The identification changes composition on the left by the Koszul sign. -/
  toShift_comp_left : ∀ (n : ℤ) {x y z : A.Obj} {l m : ℤ}
    (g : A.Hom y z m) (f : A.Hom x y (l + n)),
    toShift n x z (m + l) (A.comp (by omega : m + (l + n) = (m + l) + n) g f) =
      (-1 : R) ^ (n * m).natAbs •
        A.comp (by omega : m + l = m + l) ((shiftFunctor n).map g) (toShift n x y l f)

/-- An equality of objects of a differential graded category, read as an isomorphism of its
category of complexes: the identity transported along the equality. -/
def eqCompIso {x y : A.Obj} (h : x = y) :
    (show A.Comp from x) ≅ (show A.Comp from y) :=
  eqToIso (congrArg (fun t : A.Obj => (show A.Comp from t)) h)

private lemma eqCompIso_hom_val {x y : A.Obj} (h : x = y) :
    (eqCompIso (A := A) h).hom.1 = h ▸ A.id x := by
  cases h
  rfl

/-- A heterogeneous equality of homogeneous morphisms over two equalities of objects, read as an
equation inside one Hom module with the comparison isomorphisms inserted. -/
private lemma comp_eqCompIso_of_heq {u u' v v' : A.Obj} {k : ℤ} (hu : u = u') (hv : v = v')
    (g : A.Hom u v k) (f : A.Hom u' v' k) (h : HEq g f) :
    A.comp (zero_add k) (eqCompIso (A := A) hv).hom.1 g =
      A.comp (add_zero k) f (eqCompIso (A := A) hu).hom.1 := by
  subst hu hv
  obtain rfl : g = f := eq_of_heq h
  rw [eqCompIso_hom_val, eqCompIso_hom_val]
  show A.comp (zero_add k) (A.id v) g = A.comp (add_zero k) g (A.id u)
  rw [A.id_comp, A.comp_id]

/-- **The strict form of axiom (B) implies the isomorphism-valued form.** Both comparisons are
the identity read along the corresponding equality of objects. -/
@[reducible] def ShiftAxiomB.toShiftAxiomBIso (S : ShiftAxiomB A) : ShiftAxiomBIso A where
  shiftFunctor := S.shiftFunctor
  compShift := S.compShift
  kShift := S.kShift
  compShift_functor := S.compShift_functor
  kShift_functor := S.kShift_functor
  zeroIso x := eqCompIso (S.zero_obj x)
  zeroIso_natural := by
    intro x y k f
    exact comp_eqCompIso_of_heq (S.zero_obj x) (S.zero_obj y) _ f (S.zero_map f)
  addIso n m x := eqCompIso (by rw [add_comm n m]; exact S.add_obj m n x)
  addIso_natural := by
    intro n m x y k f
    refine comp_eqCompIso_of_heq _ _ ((S.shiftFunctor (n + m)).map f) _ ?_
    refine HEq.trans ?_ (S.add_map m n f)
    rw [add_comm n m]
  toShift := S.toShift
  toShift_d := S.toShift_d
  toShift_comp_right := S.toShift_comp_right
  toShift_comp_left := S.toShift_comp_left

/-! ### Naturality for homogeneous morphisms of every degree

Naturality of comparison isomorphisms of `Comp(A)` for homogeneous morphisms of a fixed degree
composes and inverts. -/

/-- The underlying homogeneous morphism of a composite isomorphism of `Comp(A)`. -/
private lemma isoTrans_hom_val {u v w : A.Obj}
    (α : (show A.Comp from u) ≅ (show A.Comp from v))
    (β : (show A.Comp from v) ≅ (show A.Comp from w)) :
    (α ≪≫ β).hom.1 = A.comp (by omega : (0 : ℤ) + 0 = 0) β.hom.1 α.hom.1 := rfl

private lemma iso_hom_inv_val {u v : A.Obj}
    (α : (show A.Comp from u) ≅ (show A.Comp from v)) :
    A.comp (by omega : (0 : ℤ) + 0 = 0) α.inv.1 α.hom.1 = A.id u :=
  congrArg Subtype.val α.hom_inv_id

private lemma iso_inv_hom_val {u v : A.Obj}
    (α : (show A.Comp from u) ≅ (show A.Comp from v)) :
    A.comp (by omega : (0 : ℤ) + 0 = 0) α.hom.1 α.inv.1 = A.id v :=
  congrArg Subtype.val α.inv_hom_id

/-- Naturality for homogeneous morphisms of a fixed degree composes. -/
private lemma comp_iso_trans {u u' u'' v v' v'' : A.Obj} {k : ℤ}
    (αu : (show A.Comp from u) ≅ (show A.Comp from u'))
    (αv : (show A.Comp from v) ≅ (show A.Comp from v'))
    (βu : (show A.Comp from u') ≅ (show A.Comp from u''))
    (βv : (show A.Comp from v') ≅ (show A.Comp from v''))
    (g : A.Hom u v k) (g' : A.Hom u' v' k) (g'' : A.Hom u'' v'' k)
    (h₁ : A.comp (zero_add k) αv.hom.1 g = A.comp (add_zero k) g' αu.hom.1)
    (h₂ : A.comp (zero_add k) βv.hom.1 g' = A.comp (add_zero k) g'' βu.hom.1) :
    A.comp (zero_add k) (αv ≪≫ βv).hom.1 g =
      A.comp (add_zero k) g'' (αu ≪≫ βu).hom.1 := by
  rw [isoTrans_hom_val, isoTrans_hom_val,
    ← A.assoc (by omega : (0 : ℤ) + k = k) (by omega : (0 : ℤ) + k = k)
      (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + k = k) βv.hom.1 αv.hom.1 g,
    h₁,
    A.assoc (by omega : k + (0 : ℤ) = k) (by omega : (0 : ℤ) + k = k)
      (by omega : (0 : ℤ) + k = k) (by omega : k + (0 : ℤ) = k) βv.hom.1 g' αu.hom.1,
    h₂,
    ← A.assoc (by omega : (0 : ℤ) + 0 = 0) (by omega : k + (0 : ℤ) = k)
      (by omega : k + (0 : ℤ) = k) (by omega : k + (0 : ℤ) = k) g'' βu.hom.1 αu.hom.1]

/-- Naturality for homogeneous morphisms of a fixed degree inverts. -/
private lemma comp_iso_symm {u u' v v' : A.Obj} {k : ℤ}
    (αu : (show A.Comp from u) ≅ (show A.Comp from u'))
    (αv : (show A.Comp from v) ≅ (show A.Comp from v'))
    (g : A.Hom u v k) (g' : A.Hom u' v' k)
    (h : A.comp (zero_add k) αv.hom.1 g = A.comp (add_zero k) g' αu.hom.1) :
    A.comp (zero_add k) αv.symm.hom.1 g' = A.comp (add_zero k) g αu.symm.hom.1 := by
  have key : A.comp (zero_add k) αv.hom.1 (A.comp (add_zero k) g αu.inv.1) = g' := by
    rw [A.assoc (by omega : k + (0 : ℤ) = k) (by omega : (0 : ℤ) + k = k)
        (by omega : (0 : ℤ) + k = k) (by omega : k + (0 : ℤ) = k) αv.hom.1 g αu.inv.1,
      h,
      ← A.assoc (by omega : (0 : ℤ) + 0 = 0) (by omega : k + (0 : ℤ) = k)
        (by omega : k + (0 : ℤ) = k) (by omega : k + (0 : ℤ) = k) g' αu.hom.1 αu.inv.1,
      iso_inv_hom_val, A.comp_id]
  show A.comp (zero_add k) αv.inv.1 g' = A.comp (add_zero k) g αu.inv.1
  rw [← key,
    A.assoc (by omega : (0 : ℤ) + k = k) (by omega : (0 : ℤ) + k = k)
      (by omega : (0 : ℤ) + 0 = 0) (by omega : (0 : ℤ) + k = k) αv.inv.1 αv.hom.1
      (A.comp (add_zero k) g αu.inv.1),
    iso_hom_inv_val, A.id_comp]

namespace ShiftAxiomBIso

variable (S : ShiftAxiomBIso A)

/-- The comparison `x[n] ≅ x[m]` for equal indices: the identity read along the equality. -/
def indexIso {n m : ℤ} (h : n = m) (x : A.Obj) :
    (show A.Comp from (S.shiftFunctor n).obj x) ≅
      (show A.Comp from (S.shiftFunctor m).obj x) :=
  eqCompIso (congrArg (fun j : ℤ => (S.shiftFunctor j).obj x) h)

private lemma indexIso_natural {n m : ℤ} (h : n = m) {x y : A.Obj} {k : ℤ}
    (f : A.Hom x y k) :
    A.comp (zero_add k) (S.indexIso h y).hom.1 ((S.shiftFunctor n).map f) =
      A.comp (add_zero k) ((S.shiftFunctor m).map f) (S.indexIso h x).hom.1 := by
  refine comp_eqCompIso_of_heq _ _ ((S.shiftFunctor n).map f) _ ?_
  rw [h]

/-- **The round trip `x[1][-1] ≅ x`.** -/
def unshiftIso (x : A.Obj) :
    (show A.Comp from (S.shiftFunctor (-1)).obj ((S.shiftFunctor 1).obj x)) ≅
      (show A.Comp from x) :=
  (S.addIso 1 (-1) x).symm ≪≫ S.indexIso (by omega : (1 : ℤ) + -1 = 0) x ≪≫ S.zeroIso x

/-- **The round trip `z[-1][1] ≅ z`.** -/
def reshiftIso (z : A.Obj) :
    (show A.Comp from (S.shiftFunctor 1).obj ((S.shiftFunctor (-1)).obj z)) ≅
      (show A.Comp from z) :=
  (S.addIso (-1) 1 z).symm ≪≫ S.indexIso (by omega : (-1 : ℤ) + 1 = 0) z ≪≫ S.zeroIso z

/-- Naturality of the round trip `(S.addIso n m x).symm ≪≫ S.indexIso h x ≪≫ S.zeroIso x`. -/
private lemma roundTrip_natural {n m : ℤ} (h : n + m = 0) {x y : A.Obj} {k : ℤ}
    (f : A.Hom x y k) :
    A.comp (zero_add k)
        ((S.addIso n m y).symm ≪≫ S.indexIso h y ≪≫ S.zeroIso y).hom.1
        ((S.shiftFunctor m).map ((S.shiftFunctor n).map f)) =
      A.comp (add_zero k) f
        ((S.addIso n m x).symm ≪≫ S.indexIso h x ≪≫ S.zeroIso x).hom.1 :=
  comp_iso_trans _ _ _ _ _ ((S.shiftFunctor (n + m)).map f) _
    (comp_iso_symm _ _ _ _ (S.addIso_natural n m f))
    (comp_iso_trans _ _ _ _ _ ((S.shiftFunctor 0).map f) _
      (S.indexIso_natural h f) (S.zeroIso_natural f))

/-- `DGCategory.ShiftAxiomBIso.unshiftIso` is natural for homogeneous morphisms of every
degree. -/
theorem unshiftIso_natural {x y : A.Obj} {k : ℤ} (f : A.Hom x y k) :
    A.comp (zero_add k) (S.unshiftIso y).hom.1
        ((S.shiftFunctor (-1)).map ((S.shiftFunctor 1).map f)) =
      A.comp (add_zero k) f (S.unshiftIso x).hom.1 :=
  S.roundTrip_natural (by omega) f

/-- `DGCategory.ShiftAxiomBIso.reshiftIso` is natural for homogeneous morphisms of every
degree. -/
theorem reshiftIso_natural {x y : A.Obj} {k : ℤ} (f : A.Hom x y k) :
    A.comp (zero_add k) (S.reshiftIso y).hom.1
        ((S.shiftFunctor 1).map ((S.shiftFunctor (-1)).map f)) =
      A.comp (add_zero k) f (S.reshiftIso x).hom.1 :=
  S.roundTrip_natural (by omega) f

end ShiftAxiomBIso

end DGCategory
