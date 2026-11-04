module

public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyI

/-! # Shifting the graded dual of a direct sum of shifts of the algebra

Let `(A, d)` be a differential graded algebra. `DifferentialGraded.LeftModule.directSumShifts`
is the left differential graded `A`-module `⨁ᵢ A[jᵢ]`, and
`DifferentialGradedModule.productDualShifts` is the product `∏ᵢ A^∨[kᵢ]` of shifts of the graded
dual of `A`, presented as the graded dual `(⨁ᵢ A[-kᵢ])^∨`.

Reindexing the shifts of `⨁ᵢ A[jᵢ]` by a constant `e` changes neither its underlying module nor
its differential — only its grading, by `(⨁ᵢ A[jᵢ + e])^n = (⨁ᵢ A[jᵢ])^{n+e}`. On the graded
dual this is exactly a shift, and this file proves it:

`(⨁ᵢ A[jᵢ + e])^∨ ≅ ((⨁ᵢ A[jᵢ])^∨)[-e]`, hence `∏ᵢ A^∨[kᵢ + c] ≅ (∏ᵢ A^∨[kᵢ])[c]`.

The second form is the identification called `dualShift_iso` in the implementation notes of
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyI.lean` and left unproved there. It is
what recognises a *shift* of a product of shifts of `A^∨` as again a product of shifts of
`A^∨` — needed, for instance, to present the graded pieces of the filtration of Tag 09KU, which
are shifts `I''ᵢ[-i]` of such products, in the form the field
`DifferentialGradedModule.PropertyIFiltration.quotientMap` demands.

## Main definitions

* `DifferentialGraded.LeftModule.dualShiftTransport`: the point of one graded dual carrying the
  same character as a given point of the other.
* `DifferentialGraded.LeftModule.dualDirectSumShiftsIso`: the isomorphism
  `(⨁ᵢ A[jᵢ + e])^∨ ≅ ((⨁ᵢ A[jᵢ])^∨)[-e]`.
* `DifferentialGradedModule.productDualShiftsShiftIso`: the isomorphism
  `∏ᵢ A^∨[kᵢ + c] ≅ (∏ᵢ A^∨[kᵢ])[c]`.

## Main results

* `DifferentialGraded.LeftModule.directSumShifts_grading_congr`: reindexing the shifts by `e`
  reindexes the grading by `e`.
* `DifferentialGraded.LeftModule.dualPiece_directSumShifts_congr` and
  `DifferentialGraded.LeftModule.dualCarrier_directSumShifts_congr`: the graded pieces of the
  dual are reindexed by `-e`, while the carrier of the dual does not change at all.
* `DifferentialGraded.LeftModule.signedDifferential_directSumShifts_congr` and
  `DifferentialGraded.LeftModule.dualD0_directSumShifts_congr`: the signed differential, and
  with it the differential of the dual, picks up the sign `(-1)^e`.

## Implementation notes

*Where the two halves of a shift come from.* The graded dual reads the grading twice. Once to
cut out the characters supported in a single degree, which is where the reindexing of
`dualPiece` shows up; and once through the parity operator inside
`DifferentialGraded.LeftModule.signedDifferential`, which is where the sign `(-1)^e` comes from.
Those are precisely the grading and the sign of a shift, which is why the two modules are
isomorphic. They are not *equal*: their carriers are subtypes of the same character module cut
out by two submodules that are only propositionally equal, so the comparison has to be written
down as a map.

*Why no structure field below is proved by `rfl`.* The map is the identity on underlying
characters, so every field is `rfl` in principle. In practice the kernel does not survive it:
unfolding `DifferentialGraded.LeftModule.dualChar` at a *concrete* `directSumShifts` forces the
whole `DifferentialGraded.LeftModule.dual` structure — including the chosen direct-sum
decomposition of the shifted grading — through `whnf`, and a one-line `rfl` of this shape
exhausts the kernel's budget (while the same term with the projection spelled as a
bare `Subtype.val` checks in a second). The fix is the standard one: every step is a *lemma*
stated at a generic left module, where no such term can appear, applied here. `dualChar_dualOf`,
`dualChar_add`, `dualChar_smul`, `dualChar_d` already exist for this purpose;
`DifferentialGraded.LeftModule.dualChar_zsmul` and
`DifferentialGraded.LeftModule.dualChar_shift_d` are added below for the same reason.

## References

* [Stacks Project, Tag 0FQD](https://stacks.math.columbia.edu/tag/0FQD), the graded dual and the
  modules `A^∨[k]`.
* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL), the shift.
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped DirectSum

universe u

namespace Int

/-- `(-1)^e · (-1)^{n+e} = (-1)^n`: the two copies of `e` contribute an even amount. -/
theorem negOnePow_mul_negOnePow_add (n e : ℤ) :
    e.negOnePow * (n + e).negOnePow = n.negOnePow := by
  rw [← Int.negOnePow_add, show e + (n + e) = n + 2 * e from by ring, Int.negOnePow_add,
    Int.negOnePow_two_mul, mul_one]

end Int

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Two facts about the graded dual, stated generically

These are the generic lemmas the construction below needs in place of `rfl`; see the
implementation notes. -/

/-- A `ℤ`-multiple of a point of the graded dual, read on underlying characters. -/
theorem dualChar_zsmul {M : LeftModule A} (c : ℤ) (x : (dual M).M) :
    dualChar (c • x) = c • dualChar x := rfl

/-- The differential of a shift of the graded dual, read on underlying characters: the dual
differential multiplied by the sign of the shift. -/
theorem dualChar_shift_d {M : LeftModule A} (c : ℤ)
    (x : (DifferentialGradedModule.shift (dual M) c).M) :
    dualChar ((DifferentialGradedModule.shift (dual M) c).d x)
      = (c.negOnePow : ℤ) • dualD0 M (dualChar x) := by
  rw [show (DifferentialGradedModule.shift (dual M) c).d x = (c.negOnePow : ℤ) • (dual M).d x
    from rfl, dualChar_zsmul, dualChar_d]

/-- Homogeneity in a shift of the graded dual is support of the underlying character in a single
degree, shifted. -/
theorem mem_shift_dual_grading {M : LeftModule A} {c n : ℤ}
    {x : (DifferentialGradedModule.shift (dual M) c).M} :
    x ∈ (DifferentialGradedModule.shift (dual M) c).grading n ↔
      dualChar x ∈ dualPiece M (n + c) := mem_dual_grading

/-! ### Reindexing the shifts of `⨁ᵢ A[jᵢ]` -/

variable {ι : Type u} [DecidableEq ι] {j j' : ι → ℤ} {e : ℤ}

/-- **Reindexing the shifts of `⨁ᵢ A[jᵢ]` by a constant reindexes its grading.** If
`jᵢ' = jᵢ + e` for every `i`, then `(⨁ᵢ A[jᵢ'])^n = (⨁ᵢ A[jᵢ])^{n+e}`. -/
theorem directSumShifts_grading_congr (hj : ∀ i, j' i = j i + e) (n : ℤ) :
    (directSumShifts A j').grading n = (directSumShifts A j).grading (n + e) := by
  refine Submodule.ext fun x => ?_
  rw [mem_directSumShifts_grading, mem_directSumShifts_grading]
  refine forall_congr' fun i => ?_
  rw [hj i, show n + (j i + e) = n + e + j i from by ring]

omit [DecidableEq ι] in
/-- The reindexed hypothesis, read from the other side: `jᵢ = jᵢ' + (-e)`. -/
theorem directSumShifts_congr_symm (hj : ∀ i, j' i = j i + e) : ∀ i, j i = j' i + -e :=
  fun i => by rw [hj i]; ring

/-- The differential of `⨁ᵢ A[jᵢ]` does not depend on the shifts: it is the componentwise `d_A`
for every choice of `j`. -/
theorem directSumShifts_d_congr (x : (directSumShifts A j').M) :
    (directSumShifts A j').d x = (directSumShifts A j).d x := rfl

/-- **Reindexing the shifts multiplies the parity operator by `(-1)^e`.** A point homogeneous of
degree `n` for `j'` is homogeneous of degree `n + e` for `j`, and the two signs differ by
`(-1)^e`. -/
theorem parity_directSumShifts_congr (hj : ∀ i, j' i = j i + e)
    (x : (directSumShifts A j').M) :
    DirectSum.parity (directSumShifts A j').grading x
      = (e.negOnePow : ℤ) • DirectSum.parity (directSumShifts A j).grading x := by
  refine induction_homogeneous (M := directSumShifts A j')
    (p := fun y => DirectSum.parity (directSumShifts A j').grading y
      = (e.negOnePow : ℤ) • DirectSum.parity (directSumShifts A j).grading y) x
    (fun n y hy => ?_) (by simp) (fun y z hy hz => by
      simp only [map_add, hy, hz, smul_add])
  have hy' : y ∈ (directSumShifts A j).grading (n + e) := by
    rw [← directSumShifts_grading_congr hj]; exact hy
  rw [DirectSum.parity_apply_of_mem _ hy, DirectSum.parity_apply_of_mem _ hy', smul_smul,
    ← Units.val_mul, Int.negOnePow_mul_negOnePow_add]

/-- **Reindexing the shifts multiplies the signed differential by `(-1)^e`.** This is the
operator whose `ℚ/ℤ`-dual is the differential of the graded dual, so it is the source of the
sign of a shift on the dual side. -/
theorem signedDifferential_directSumShifts_congr (hj : ∀ i, j' i = j i + e)
    (x : (directSumShifts A j').M) :
    signedDifferential (directSumShifts A j') x
      = (e.negOnePow : ℤ) • signedDifferential (directSumShifts A j) x := by
  rw [signedDifferential, signedDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    parity_directSumShifts_congr hj, map_zsmul, directSumShifts_d_congr (j' := j') (j := j)]

/-- **Reindexing the shifts reindexes the graded pieces of the dual in the opposite
direction.** A character of `⨁ᵢ A[jᵢ']` supported in degree `n` is a character of `⨁ᵢ A[jᵢ]`
supported in degree `n - e`. -/
theorem dualPiece_directSumShifts_congr (hj : ∀ i, j' i = j i + e) (n : ℤ) :
    dualPiece (directSumShifts A j') n = dualPiece (directSumShifts A j) (n - e) := by
  refine Submodule.ext fun l => ?_
  rw [mem_dualPiece, mem_dualPiece]
  constructor
  · intro h m hm x hx
    refine h (m - e) (by omega) x ?_
    rwa [directSumShifts_grading_congr hj, show m - e + e = m by ring]
  · intro h m hm x hx
    rw [directSumShifts_grading_congr hj] at hx
    exact h (m + e) (by omega) x hx

/-- The characters supported in single degrees of `⨁ᵢ A[jᵢ']` are sums of such for `⨁ᵢ A[jᵢ]`. -/
private theorem dualCarrier_directSumShifts_le (hj : ∀ i, j' i = j i + e) :
    dualCarrier (directSumShifts A j') ≤ dualCarrier (directSumShifts A j) :=
  iSup_le fun n => le_iSup_of_le (n - e) (dualPiece_directSumShifts_congr hj n).le

/-- **Reindexing the shifts does not change the carrier of the dual.** The graded pieces are
only relabelled, so their supremum — the characters that are sums of homogeneous ones — is the
same submodule of `CharacterModule (⨁ᵢ A)`. -/
theorem dualCarrier_directSumShifts_congr (hj : ∀ i, j' i = j i + e) :
    dualCarrier (directSumShifts A j') = dualCarrier (directSumShifts A j) :=
  le_antisymm (dualCarrier_directSumShifts_le hj)
    (dualCarrier_directSumShifts_le (directSumShifts_congr_symm hj))

/-- **Reindexing the shifts multiplies the differential of the dual by `(-1)^e`**, that
differential being precomposition with the signed differential. -/
theorem dualD0_directSumShifts_congr (hj : ∀ i, j' i = j i + e)
    (l : CharacterModule (directSumShifts A j').M) :
    dualD0 (directSumShifts A j') l = (e.negOnePow : ℤ) • dualD0 (directSumShifts A j) l := by
  ext y
  simp only [dualD0_apply, zsmul_char_apply, signedDifferential_directSumShifts_congr hj,
    map_zsmul]

/-! ### The comparison isomorphism -/

/-- **The point of `(⨁ᵢ A[jᵢ])^∨` carrying the same character as a given point of
`(⨁ᵢ A[jᵢ'])^∨`.** The two carriers are cut out of the same character module by the same
submodule, by `DifferentialGraded.LeftModule.dualCarrier_directSumShifts_congr`. -/
def dualShiftTransport (hj : ∀ i, j' i = j i + e) (x : (dual (directSumShifts A j')).M) :
    (dual (directSumShifts A j)).M :=
  dualOf (M := directSumShifts A j) (dualChar (M := directSumShifts A j') x)
    (by rw [← dualCarrier_directSumShifts_congr hj]
        exact dualChar_mem (M := directSumShifts A j') x)

/-- The transport does not change the underlying character. -/
@[simp] theorem dualChar_dualShiftTransport (hj : ∀ i, j' i = j i + e)
    (x : (dual (directSumShifts A j')).M) :
    dualChar (M := directSumShifts A j) (dualShiftTransport hj x)
      = dualChar (M := directSumShifts A j') x := dualChar_dualOf _ _

/-- The transport, as an `R`-linear map. -/
def dualShiftTransportLinear (hj : ∀ i, j' i = j i + e) :
    (dual (directSumShifts A j')).M →ₗ[R] (dual (directSumShifts A j)).M where
  toFun := dualShiftTransport hj
  map_add' x y := dualChar_injective (M := directSumShifts A j) (by
    rw [dualChar_dualShiftTransport, dualChar_add (M := directSumShifts A j),
      dualChar_dualShiftTransport, dualChar_dualShiftTransport,
      dualChar_add (M := directSumShifts A j') x y])
  map_smul' r x := dualChar_injective (M := directSumShifts A j) (by
    rw [dualChar_dualShiftTransport, dualChar_smul (M := directSumShifts A j),
      dualChar_dualShiftTransport, dualChar_smul (M := directSumShifts A j') r x]
    rfl)

/-- The transport, read as a linear map, is the transport. -/
@[simp] theorem dualShiftTransportLinear_apply (hj : ∀ i, j' i = j i + e)
    (x : (dual (directSumShifts A j')).M) :
    dualShiftTransportLinear hj x = dualShiftTransport hj x := rfl

/-- **`(⨁ᵢ A[jᵢ + e])^∨ ⟶ ((⨁ᵢ A[jᵢ])^∨)[-e]`**, the identity on underlying characters. -/
def dualShiftTransportHom (hj : ∀ i, j' i = j i + e) :
    dual (directSumShifts A j') ⟶ DifferentialGradedModule.shift (dual (directSumShifts A j))
      (-e) where
  toFun := dualShiftTransportLinear hj
  map_smul x a := dualChar_injective (M := directSumShifts A j) (by
    rw [dualShiftTransportLinear_apply, dualChar_dualShiftTransport,
      dualChar_op_smul (M := directSumShifts A j') a x,
      dualChar_op_smul (M := directSumShifts A j) a (dualShiftTransportLinear hj x),
      dualShiftTransportLinear_apply, dualChar_dualShiftTransport]
    rfl)
  map_grading n x hx := by
    refine mem_shift_dual_grading.mpr ?_
    rw [dualShiftTransportLinear_apply, dualChar_dualShiftTransport,
      show n + -e = n - e from by ring, ← dualPiece_directSumShifts_congr hj]
    exact mem_dual_grading.mp hx
  map_d := by
    refine LinearMap.ext fun x => dualChar_injective (M := directSumShifts A j) ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dualShiftTransportLinear_apply,
      dualChar_dualShiftTransport, dualChar_d, dualD0_directSumShifts_congr hj,
      dualChar_shift_d, dualShiftTransportLinear_apply, dualChar_dualShiftTransport,
      Int.negOnePow_neg]

/-- **`((⨁ᵢ A[jᵢ])^∨)[-e] ⟶ (⨁ᵢ A[jᵢ + e])^∨`**, the identity on underlying characters. -/
def dualShiftTransportInvHom (hj : ∀ i, j' i = j i + e) :
    DifferentialGradedModule.shift (dual (directSumShifts A j)) (-e) ⟶
      dual (directSumShifts A j') where
  toFun := dualShiftTransportLinear (directSumShifts_congr_symm hj)
  map_smul x a := dualChar_injective (M := directSumShifts A j') (by
    rw [dualShiftTransportLinear_apply, dualChar_dualShiftTransport,
      dualChar_op_smul (M := directSumShifts A j) a x,
      dualChar_op_smul (M := directSumShifts A j') a
        (dualShiftTransportLinear (directSumShifts_congr_symm hj) x),
      dualShiftTransportLinear_apply, dualChar_dualShiftTransport]
    rfl)
  map_grading n x hx := by
    refine mem_dual_grading.mpr ?_
    rw [dualShiftTransportLinear_apply, dualChar_dualShiftTransport,
      dualPiece_directSumShifts_congr hj, show n - e = n + -e from by ring]
    exact mem_shift_dual_grading.mp hx
  map_d := by
    refine LinearMap.ext fun x => dualChar_injective (M := directSumShifts A j') ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, dualShiftTransportLinear_apply,
      dualChar_dualShiftTransport, dualChar_shift_d, dualChar_d,
      dualD0_directSumShifts_congr hj, dualShiftTransportLinear_apply,
      dualChar_dualShiftTransport, Int.negOnePow_neg]

/-- **The graded dual turns a reindexing of the shifts into a shift:**
`(⨁ᵢ A[jᵢ + e])^∨ ≅ ((⨁ᵢ A[jᵢ])^∨)[-e]`. The isomorphism is the identity on underlying
characters. -/
def dualDirectSumShiftsIso (hj : ∀ i, j' i = j i + e) :
    dual (directSumShifts A j') ≅
      DifferentialGradedModule.shift (dual (directSumShifts A j)) (-e) where
  hom := dualShiftTransportHom hj
  inv := dualShiftTransportInvHom hj
  hom_inv_id := DifferentialGradedModule.Hom.ext (LinearMap.ext fun x =>
    dualChar_injective (M := directSumShifts A j') (by
      rw [DifferentialGradedModule.Hom.comp_toFun_apply]
      exact (dualChar_dualShiftTransport (directSumShifts_congr_symm hj)
          (dualShiftTransport hj x)).trans (dualChar_dualShiftTransport hj x)))
  inv_hom_id := DifferentialGradedModule.Hom.ext (LinearMap.ext fun x =>
    dualChar_injective (M := directSumShifts A j) (by
      rw [DifferentialGradedModule.Hom.comp_toFun_apply]
      exact (dualChar_dualShiftTransport hj
          (dualShiftTransport (directSumShifts_congr_symm hj) x)).trans
        (dualChar_dualShiftTransport (directSumShifts_congr_symm hj) x)))

end DifferentialGraded.LeftModule

namespace DifferentialGradedModule

open DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R]

/-- **A shift of a product of shifts of `A^∨` is again a product of shifts of `A^∨`:**
`∏ᵢ A^∨[kᵢ + c] ≅ (∏ᵢ A^∨[kᵢ])[c]`. This is the identification `dualShift_iso` named in the
implementation notes of `StacksFrontier/Algebra/DifferentialGraded/Module/PropertyI.lean`, and it
is the identity on underlying characters. -/
def productDualShiftsShiftIso (A : DifferentialGradedAlgebra R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) (c : ℤ) :
    productDualShifts A (fun i => k i + c) ≅ shift (productDualShifts A k) c :=
  dualDirectSumShiftsIso (A := A) (j := fun i => -k i) (j' := fun i => -(k i + c)) (e := -c)
      (fun _ => by ring) ≪≫
    eqToIso (congrArg (shift (productDualShifts A k)) (neg_neg c))

end DifferentialGradedModule

end
