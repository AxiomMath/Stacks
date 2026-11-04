module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.CategoryTheory.DifferentialGraded.Biproduct
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Axiom (A) for the differential graded category of complexes

Axiom (A) of Tag 09P6 asks of a differential graded category a zero object, with no homogeneous
morphisms to or from it in any degree, and a direct sum of any two objects whose inclusions and
projections are closed and of degree zero. For `CochainComplex.dgCategory B` both are supplied
by `B`: the zero object is the zero complex, and the direct sum is the degreewise biproduct, all
of whose structure maps are maps of complexes and hence closed degree-zero cochains.

The hypotheses on `B` are a zero object and binary biproducts. The latter gives binary products
of complexes degreewise, and in a preadditive category binary products are biproducts, so
`CategoryTheory.Limits.HasBinaryBiproducts (CochainComplex B ℤ)` follows by
`CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts`, which is a local instance here
but not a global one.

## Main definitions

* `CochainComplex.dgBinaryBiproductData`: the degreewise biproduct of two complexes, as a direct
  sum of the differential graded category of complexes.
* `CochainComplex.dgDirectSumAxiomA`: **axiom (A) for the differential graded category of
  complexes.**

## Implementation notes

Every structure map is a `CochainComplex.HomComplex.Cochain.ofHom`, and
`CochainComplex.HomComplex.Cochain.ofHom` turns composition into composition
(`ofHom_comp`), addition into addition (`ofHom_add`) and identities into identities, and kills the
Hom differential (`δ_ofHom`). So each of the nine conditions is the corresponding identity of
`CategoryTheory.Limits.biprod` with `ofHom` applied to it, modulo the fact that
`DGCategory.comp h g f` is `g` after `f` while `CochainComplex.HomComplex.Cochain.comp` is
diagrammatic.

The zero object is `HomologicalComplex.zero` rather than `0`, so that its components are
definitionally the zero object of `B` and the vanishing of the homogeneous morphisms is
`CategoryTheory.Limits.IsZero.eq_of_src` applied componentwise.

## References

* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (A);
  [Tag 09P4](https://stacks.math.columbia.edu/tag/09P4), direct sums in a differential graded
  category; [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded
  category of complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

open CochainComplex.HomComplex

variable {B : Type u} [Category.{v} B] [Preadditive B]

section Biproduct

variable [HasBinaryBiproducts B]

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

omit [HasBinaryBiproducts B] in
/-- The cochain of a map of complexes is closed. -/
theorem dgCategory_d_ofHom {X Y : CochainComplex B ℤ} (φ : X ⟶ Y) :
    (dgCategory B).d (Cochain.ofHom φ) = 0 :=
  δ_ofHom φ

omit [HasBinaryBiproducts B] in
/-- The composite of the cochains of two maps of complexes, in the order `DGCategory.comp` uses:
`DGCategory.comp h g f` is `g` after `f`. -/
theorem dgCategory_comp_ofHom {X Y Z : CochainComplex B ℤ} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (dgCategory B).comp (show (0 : ℤ) + 0 = 0 from rfl) (Cochain.ofHom ψ) (Cochain.ofHom φ) =
      Cochain.ofHom (φ ≫ ψ) :=
  (Cochain.ofHom_comp φ ψ).symm

/-- **The degreewise biproduct of two complexes is a direct sum of the differential graded
category of complexes.** All four structure maps are maps of complexes, hence closed. -/
noncomputable def dgBinaryBiproductData (X Y : CochainComplex B ℤ) :
    DGCategory.BinaryBiproductData (dgCategory B) X Y where
  pt := (biprod X Y : CochainComplex B ℤ)
  inl := Cochain.ofHom biprod.inl
  inr := Cochain.ofHom biprod.inr
  fst := Cochain.ofHom biprod.fst
  snd := Cochain.ofHom biprod.snd
  inl_closed := dgCategory_d_ofHom _
  inr_closed := dgCategory_d_ofHom _
  fst_closed := dgCategory_d_ofHom _
  snd_closed := dgCategory_d_ofHom _
  inl_fst := by rw [dgCategory_comp_ofHom, biprod.inl_fst]; rfl
  inr_fst := by rw [dgCategory_comp_ofHom, biprod.inr_fst, Cochain.ofHom_zero]
  inl_snd := by rw [dgCategory_comp_ofHom, biprod.inl_snd, Cochain.ofHom_zero]
  inr_snd := by rw [dgCategory_comp_ofHom, biprod.inr_snd]; rfl
  fst_inl_add_snd_inr := by
    rw [dgCategory_comp_ofHom, dgCategory_comp_ofHom, ← Cochain.ofHom_add, biprod.total]
    rfl

end Biproduct

/-- **Axiom (A) for the differential graded category of complexes.** The zero object is the zero
complex and the direct sums are the degreewise biproducts. -/
noncomputable def dgDirectSumAxiomA (B : Type u) [Category.{v} B] [Preadditive B]
    [HasZeroObject B] [HasBinaryBiproducts B] :
    DGCategory.DirectSumAxiomA (dgCategory B) where
  zero := HomologicalComplex.zero
  zero_from _ _ := ⟨fun f g =>
    Cochain.ext f g (fun _ _ _ => (isZero_zero B).eq_of_src _ _)⟩
  zero_to _ _ := ⟨fun f g =>
    Cochain.ext f g (fun _ _ _ => (isZero_zero B).eq_of_tgt _ _)⟩
  binaryBiproduct x y := ⟨dgBinaryBiproductData x y⟩

end CochainComplex
