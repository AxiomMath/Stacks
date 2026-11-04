module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftAxiomBIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.ShiftRoundTripCoherence

/-!
# The round-trip coherence of axiom (B) for the differential graded category of complexes

`DGCategory.ShiftAxiomBIso.RoundTripCoherent` is the one identity that an isomorphism-valued
axiom (B) does not imply and that the cone layer of Tag 09QU needs: the shift of the round trip
`x[1][-1] ≅ x` is the round trip `z[-1][1] ≅ z` at `z = x[1]`. For strict data it is automatic
(`DGCategory.ShiftAxiomB.roundTripCoherent`). This file discharges it for
`CochainComplex.dgShiftAxiomBIso`, the axiom (B) datum of the differential graded category of
complexes — the `C` of Tag 09LK, which has no strict axiom (B).

The identity is Mathlib's `CategoryTheory.shift_shiftFunctorCompIsoId_hom_app`, so all that is
needed is to recognise `DGCategory.ShiftAxiomBIso.unshiftIso` and
`DGCategory.ShiftAxiomBIso.reshiftIso` of `CochainComplex.dgShiftAxiomBIso` as
`CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) n m` applied at the object. Both are
composites of the same three arrows: the inverse of the comparison for `n + m`, the index change
`n + m = 0`, and the comparison for `0`.

## Main results

* `CochainComplex.dgUnshiftIso_hom_val` and `CochainComplex.dgReshiftIso_hom_val`: the two round
  trips of `CochainComplex.dgShiftAxiomBIso` are `CategoryTheory.shiftFunctorCompIsoId`.
* `CochainComplex.dgShiftAxiomBIso_roundTripCoherent`: **the round-trip coherence holds for the
  differential graded category of complexes.**

## Implementation notes

The objects `(CochainComplex.dgShiftFunctor B n).obj x` and
`(CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).obj x` are equal only by unfolding a
semireducible definition, so, as in
`StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftAxiomBIso`, every step is
phrased in one vocabulary and the gap is crossed once, by `exact`. In particular the proof of the
coherence rewrites only inside `CochainComplex.HomComplex.Cochain.ofHom`, where no object of the
differential graded category occurs.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK).
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

open CochainComplex.HomComplex

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-- An equality of cochain complexes, read as an isomorphism of the category of complexes of
`CochainComplex.dgCategory B`, has `CategoryTheory.eqToHom` for its underlying cochain. -/
private lemma eqCompIso_hom_val_ofHom {X Y : CochainComplex B ℤ} (e : X = Y) :
    (DGCategory.eqCompIso (A := dgCategory B) e).hom.1 = Cochain.ofHom (eqToHom e) := by
  cases e
  rfl

/-- The underlying cochain of a composite isomorphism of the category of complexes. -/
private lemma compIso_hom_val {X Y Z : (dgCategory B).Comp} (α : X ≅ Y) (β : Y ≅ Z) :
    (α ≪≫ β).hom.1 = (α.hom.1).comp (β.hom.1) (zero_add 0) := rfl

/-- **`CategoryTheory.shiftFunctorCompIsoId` is the composite of the inverse of the comparison
for `n + m`, the index change and the comparison for `0`**, which is the shape in which
`DGCategory.ShiftAxiomBIso.unshiftIso` is built. -/
private lemma shiftFunctorCompIsoId_hom_app_eq (n m : ℤ) (h : n + m = 0)
    (x : CochainComplex B ℤ) :
    (CategoryTheory.shiftFunctorAdd (CochainComplex B ℤ) n m).inv.app x ≫
        eqToHom (congrArg (fun j : ℤ =>
          (CategoryTheory.shiftFunctor (CochainComplex B ℤ) j).obj x) h) ≫
        (CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).hom.app x =
      (CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) n m h).hom.app x := by
  dsimp [CategoryTheory.shiftFunctorCompIsoId, CategoryTheory.shiftFunctorAdd']
  simp [eqToHom_app]

/-- **The round trip of `CochainComplex.dgShiftAxiomBIso` at a pair of opposite indices is
`CategoryTheory.shiftFunctorCompIsoId`**, as an equality of underlying cochains. Both
`DGCategory.ShiftAxiomBIso.unshiftIso` and `DGCategory.ShiftAxiomBIso.reshiftIso` are instances
of the left-hand side. -/
private lemma roundTripIso_hom_val (n m : ℤ) (h : n + m = 0) (x : CochainComplex B ℤ) :
    (((dgAddIso B n m x).symm ≪≫
        DGCategory.eqCompIso (A := dgCategory B)
          (congrArg (fun j : ℤ => (dgShiftFunctor B j).obj x) h) ≪≫
        dgZeroIso B x).hom).1 =
      Cochain.ofHom ((CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) n m
        h).hom.app x) := by
  rw [compIso_hom_val, compIso_hom_val, eqCompIso_hom_val_ofHom,
    ← shiftFunctorCompIsoId_hom_app_eq n m h x, Cochain.ofHom_comp, Cochain.ofHom_comp]
  rfl

/-- **The round trip `x[1][-1] ≅ x` of `CochainComplex.dgShiftAxiomBIso` is
`CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) 1 (-1)`.** -/
theorem dgUnshiftIso_hom_val (x : CochainComplex B ℤ) :
    ((dgShiftAxiomBIso B).unshiftIso x).hom.1 =
      Cochain.ofHom ((CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (1 : ℤ) (-1)
        (by omega)).hom.app x) :=
  roundTripIso_hom_val 1 (-1) (by omega) x

/-- **The round trip `z[-1][1] ≅ z` of `CochainComplex.dgShiftAxiomBIso` is
`CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (-1) 1`.** -/
theorem dgReshiftIso_hom_val (z : CochainComplex B ℤ) :
    ((dgShiftAxiomBIso B).reshiftIso z).hom.1 =
      Cochain.ofHom ((CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1
        (by omega)).hom.app z) :=
  roundTripIso_hom_val (-1) 1 (by omega) z

/-- **The round-trip coherence holds for the differential graded category of complexes.** By
`CochainComplex.dgUnshiftIso_hom_val` and `CochainComplex.dgReshiftIso_hom_val` the two sides are
the two sides of Mathlib's `CategoryTheory.shift_shiftFunctorCompIsoId_hom_app`, the Koszul sign
of `CochainComplex.dgShiftFunctor` being trivial in degree zero
(`CochainComplex.cochainToComplexFunctor_map_shift`). -/
theorem dgShiftAxiomBIso_roundTripCoherent (B : Type u) [Category.{v} B] [Preadditive B] :
    (dgShiftAxiomBIso B).RoundTripCoherent := by
  intro x
  apply Subtype.ext
  have h1 : (dgShiftFunctor B 1).map (((dgShiftAxiomBIso B).unshiftIso x).hom.1) =
      Cochain.ofHom ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).map
        ((CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (1 : ℤ) (-1)
          (by omega)).hom.app x)) := by
    rw [dgUnshiftIso_hom_val]
    exact cochainToComplexFunctor_map_shift B 1 _
  have h2 : (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).map
        ((CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (1 : ℤ) (-1)
          (by omega)).hom.app x) =
      (CategoryTheory.shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1
        (by omega)).hom.app ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).obj x) :=
    CategoryTheory.shift_shiftFunctorCompIsoId_hom_app _ _ _ _
  refine Eq.trans ?_ (dgReshiftIso_hom_val
    ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).obj x)).symm
  exact h1.trans (congrArg Cochain.ofHom h2)

end CochainComplex
