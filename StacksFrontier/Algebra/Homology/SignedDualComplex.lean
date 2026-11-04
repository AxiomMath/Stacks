module

public import StacksFrontier.Algebra.Homology.AssembleLeftDual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dual complex built out of a family of degreewise duals

Let `C` be a monoidal preadditive category carrying the coproducts that make both
`GradedObject ℤ C` and `CochainComplex C ℤ` monoidal, and let `K` be a cochain complex in `C`.
Suppose given a family of objects `D : ℤ → C` and, for each pair of degrees `i + j = 0`, a
pairing exhibiting `D j` as a dual of `K^i`. This file assembles `D` into a *complex* `D^•` whose
differential is the signed transpose of the differential of `K`, and shows that `D^•` is a dual
of `K` once both vanish outside a finite set of degrees.

`StacksFrontier/Algebra/Homology/AssembleLeftDual.lean` does the analytic half of this: given a
second complex `L` whose differential is the signed transpose, it produces the pairing of `K`
with `L`. What is added here is the *construction* of that second complex — the step at which the
index flip `j ↦ -j` of [Stacks, Tag 0FNK] and [Stacks, Tag 0FPR] is performed, so that the term
in degree `j` of the dual is a dual of the term in degree `-j` of `K`.

## Main definitions

* `CochainComplex.dualComplex`: the complex with `j`-th term `D j` and differential the signed
  transpose. Its underlying family of objects is `D` itself, on the nose.
* `CochainComplex.dualPairing`: the pairing of `K^n` with the degree-`-n` term of the dual, read
  off the given family at `i = n`, `j = -n`.
* `CochainComplex.exactPairingDualComplex`: **the dual complex is a dual of `K`** when both
  vanish outside a finite set of degrees.

## Main results

* `CochainComplex.signedTransposeAt_comp`: two consecutive signed transposes compose to zero —
  the mate of a composition being the composition of the mates in the other order, and the mate
  of the zero morphism being zero.
* `CochainComplex.dualComplex_d`: the differential of the dual complex from degree `-(n+1)` to
  degree `-n` is `(-1)^n` times the mate of `d_K^n`.
* `CochainComplex.isSignedTranspose_dualComplex`: the dual complex satisfies the
  signed-transpose condition of `CochainComplex.IsSignedTranspose`, which is what makes the
  summed coevaluation and evaluation morphisms of complexes.
* `CochainComplex.isZero_of_exactPairing_of_isZero`: a dual of a zero object is a zero object,
  so the dual complex inherits the support bound of `K`.

## Implementation notes

**The index flip, and why the pairings are indexed by an equation.** The interface of
`CochainComplex.exactPairingOfSignedTranspose` asks for pairings of `K^n` with `L^{-n}`, so the
dual complex must have `D (-n)` in degree `-n`; taking its underlying family of objects to be
`D` itself — rather than `fun j => D' (-j)` for a family `D'` indexed by the degrees of `K` —
is what keeps `L.X (-n)` equal to `D (-n)` *syntactically*, with no transport. The flip then has
to happen somewhere, and it happens in the hypothesis: the family of pairings is indexed by a
pair of degrees `i`, `j` together with `i + j = 0`, which a consumer discharges by `subst`
against its own indexing. This is the device the `ModuleCat` analogue of [Stacks, Tag 0FNK] in
`StacksFrontier/Homology/LeftDual.lean` uses for the same purpose.

**Why the differential carries its degrees as equations too.** `signedTransposeAt n` naturally
has type `D (-(n+1)) ⟶ D (-n)`, while a differential of a complex is a map `D j ⟶ D j'` for
`j + 1 = j'`; the two descriptions of one object differ by `- -n` versus `n`, which is not a
definitional equality on `ℤ`. `signedTransposeIn` therefore takes `n`, `j` and `j'` with the two
equations `n + j' = 0` and `n + 1 + j = 0` and substitutes them away. Its *type* does not mention
`n`, so two instances of it at propositionally equal `n` are equal by `subst` alone — no
`eqToHom` appears anywhere below, and none is needed.

## References

* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

universe v u

namespace CochainComplex

section Construction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-- **The mate of the zero morphism is zero.** -/
theorem rightAdjointMate_zero (X Y : C) (dX : HasRightDual X) (dY : HasRightDual Y) :
    @rightAdjointMate C _ _ X Y dX dY 0 = 0 := by
  let := dX
  let := dY
  simp [rightAdjointMate]

/-- **A dual of a zero object is a zero object.** -/
theorem isZero_of_exactPairing_of_isZero (X Y : C) (e : ExactPairing X Y) (hX : IsZero X) :
    IsZero Y := by
  let := e
  have hXY : IsZero (X ⊗ Y) := by
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← MonoidalCategory.id_whiskerRight X Y, hX, MonoidalPreadditive.zero_whiskerRight]
  have key := ExactPairing.coevaluation_evaluation X Y
  rw [hXY.eq_of_tgt (η_ X Y) 0, MonoidalPreadditive.whiskerLeft_zero, zero_comp] at key
  have hρ : (ρ_ Y).hom = 0 := by
    rw [← Category.comp_id (ρ_ Y).hom, ← (λ_ Y).inv_hom_id, ← Category.assoc, ← key, zero_comp]
  rw [IsZero.iff_id_eq_zero, ← (ρ_ Y).inv_hom_id, hρ, comp_zero]

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))

/-- The pairing of the term `K^n` with the term of the dual family in degree `-n`. -/
@[instance_reducible]
def dualPairing (n : ℤ) : ExactPairing (K.X n) (D (-n)) := q n (-n) (by omega)

/-- The term of the dual family in degree `-n`, read as a right dual of `K^n`. Mathlib's
`rightDual` is the Stacks *left* dual. -/
abbrev hasRightDualD (n : ℤ) : HasRightDual (K.X n) :=
  letI := dualPairing K D q n
  ⟨D (-n)⟩

/-- **The signed transpose of `d_K^n`**: `(-1)^n` times the right adjoint mate of
`d_K^n : K^n ⟶ K^{n+1}`, a morphism from the degree `-(n+1)` term of the dual family to its
degree `-n` term. -/
noncomputable def signedTransposeAt (n : ℤ) : D (-(n + 1)) ⟶ D (-n) :=
  (n.negOnePow : ℤˣ) • @rightAdjointMate C _ _ (K.X n) (K.X (n + 1))
    (hasRightDualD K D q n) (hasRightDualD K D q (n + 1)) (K.d n (n + 1))

/-- **Two consecutive signed transposes compose to zero.** -/
theorem signedTransposeAt_comp (n : ℤ) :
    signedTransposeAt K D q (n + 1) ≫ signedTransposeAt K D q n = 0 := by
  have h : @rightAdjointMate C _ _ (K.X (n + 1)) (K.X (n + 1 + 1))
        (hasRightDualD K D q (n + 1)) (hasRightDualD K D q (n + 1 + 1))
        (K.d (n + 1) (n + 1 + 1)) ≫
      @rightAdjointMate C _ _ (K.X n) (K.X (n + 1))
        (hasRightDualD K D q n) (hasRightDualD K D q (n + 1)) (K.d n (n + 1)) = 0 := by
    rw [← @comp_rightAdjointMate C _ _ (K.X n) (K.X (n + 1)) (K.X (n + 1 + 1))
        (hasRightDualD K D q n) (hasRightDualD K D q (n + 1))
        (hasRightDualD K D q (n + 1 + 1)),
      K.d_comp_d n (n + 1) (n + 1 + 1),
      rightAdjointMate_zero (K.X n) (K.X (n + 1 + 1)) (hasRightDualD K D q n)
        (hasRightDualD K D q (n + 1 + 1))]
  rw [signedTransposeAt, signedTransposeAt, Linear.units_smul_comp, Linear.comp_units_smul, h,
    smul_zero, smul_zero]

/-- The signed transpose read as a morphism from degree `j` to degree `j'` of the dual complex,
the two degrees being pinned to `-(n+1)` and `-n` by the equations. -/
noncomputable def signedTransposeIn (n j j' : ℤ) (h : n + j' = 0) (h' : n + 1 + j = 0) :
    D j ⟶ D j' := by
  obtain rfl : j' = -n := by omega
  obtain rfl : j = -(n + 1) := by omega
  exact signedTransposeAt K D q n

omit [MonoidalPreadditive C] in
/-- At the degrees it is designed for, the re-indexed signed transpose is the signed
transpose. -/
theorem signedTransposeIn_eq (n : ℤ) (h : n + -n = 0) (h' : n + 1 + -(n + 1) = 0) :
    signedTransposeIn K D q n (-(n + 1)) (-n) h h' = signedTransposeAt K D q n := rfl

/-- The differential of the dual complex: the signed transpose between consecutive degrees, and
zero elsewhere. -/
noncomputable def dualD (j j' : ℤ) : D j ⟶ D j' :=
  if h : j + 1 = j' then signedTransposeIn K D q (-j') j j' (by omega) (by omega) else 0

omit [MonoidalPreadditive C] in
/-- The differential of the dual complex between consecutive degrees, with the degree of `K` it
transposes supplied as a parameter. -/
theorem dualD_eq (n j j' : ℤ) (h : n + j' = 0) (h' : n + 1 + j = 0) :
    dualD K D q j j' = signedTransposeIn K D q n j j' h h' := by
  obtain rfl : n = -j' := by omega
  exact dif_pos (show j + 1 = j' by omega)

/-- Two consecutive differentials of the dual complex compose to zero. -/
theorem dualD_comp_dualD (n i j k : ℤ) (hi : n + 1 + 1 + i = 0) (hj : n + 1 + j = 0)
    (hk : n + k = 0) : dualD K D q i j ≫ dualD K D q j k = 0 := by
  obtain rfl : i = -(n + 1 + 1) := by omega
  obtain rfl : j = -(n + 1) := by omega
  obtain rfl : k = -n := by omega
  rw [dualD_eq K D q (n + 1) _ _ (by omega) (by omega),
    dualD_eq K D q n _ _ (by omega) (by omega), signedTransposeIn_eq, signedTransposeIn_eq]
  exact signedTransposeAt_comp K D q n

/-- **The dual complex.** Its term in degree `j` is the given object `D j`, and its differential
is the signed transpose of the differential of `K`: the `(-1)^n`-multiple of the mate of
`d_K^n : K^n ⟶ K^{n+1}` from degree `-(n+1)` to degree `-n`, which is the sign convention of
[Stacks, Tag 0FNK]. -/
@[sga "4 XVII 1.1.6" "special case"]
noncomputable def dualComplex : CochainComplex C ℤ where
  X := D
  d := dualD K D q
  shape _ _ hij := dif_neg hij
  d_comp_d' i j k hij hjk := by
    have h1 : i + 1 = j := hij
    have h2 : j + 1 = k := hjk
    exact dualD_comp_dualD K D q (-k) i j k (by omega) (by omega) (by omega)

/-- The terms of the dual complex are the given family of objects. -/
theorem dualComplex_X (j : ℤ) : (dualComplex K D q).X j = D j := rfl

/-- **The differential of the dual complex is the signed transpose.** -/
theorem dualComplex_d (n : ℤ) :
    (dualComplex K D q).d (-(n + 1)) (-n) = signedTransposeAt K D q n :=
  (dualD_eq K D q n (-(n + 1)) (-n) (by omega) (by omega)).trans
    (signedTransposeIn_eq K D q n _ _)

/-- **The dual complex satisfies the signed-transpose condition.** This is what makes the sums
`η = ∑ ηₙ` and `ε = ∑ εₙ` morphisms of complexes. -/
theorem isSignedTranspose_dualComplex :
    IsSignedTranspose K (dualComplex K D q) (dualPairing K D q) := fun n =>
  dualComplex_d K D q n

end Construction

section Pairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))

/-- **The dual complex is a dual of `K`.** If `K` vanishes outside a finite set `s` of degrees
and in every degree `n` the object `D (-n)` is a dual of `K^n`, then the complex with terms `D`
and the signed-transpose differential is a dual of `K` in the monoidal category of complexes:
both triangle identities hold for `η = ∑ ηₙ` and `ε = ∑ εₙ`.

The support hypothesis is only needed on `K`: the dual of a zero object is zero, so the dual
complex vanishes wherever `K` does. -/
@[instance_reducible]
noncomputable def exactPairingDualComplex (s : Finset ℤ)
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) :
    ExactPairing K (dualComplex K D q) :=
  exactPairingOfSignedTranspose K (dualComplex K D q) (dualPairing K D q) s hK
    (fun m hm => isZero_of_exactPairing_of_isZero (K.X m) (D (-m)) (dualPairing K D q m)
      (hK m hm))
    (isSignedTranspose_dualComplex K D q)

/-- **The dual complex is a dual of `K` with no boundedness of `K`.** What replaces the finite
set of degrees is a coevaluation whose component on each summand `K^n ⊗ D^{-n}` is the
degreewise `ηₙ`, together with the separation of the degree-one part of `K ⊗ D`; both hold when
the summands are only *locally* finitely many, which is the generality [Stacks, Tag 0FPR] states
its example in. The signed-transpose condition is the same one as above, so this is the same
complex, the same `η` and the same `ε` as `exactPairingDualComplex`. -/
@[instance_reducible]
noncomputable def exactPairingDualComplexOfComponents
    (coev : 𝟙_ C ⟶ GradedObject.Monoidal.tensorObj K.X D 0)
    (hc : GradedObject.Monoidal.IsAssembledCoev K.X D (dualPairing K D q) coev)
    (hsep : IsSeparatedDegOne K (dualComplex K D q)) :
    ExactPairing K (dualComplex K D q) :=
  exactPairingOfSignedTransposeOfComponents K (dualComplex K D q) (dualPairing K D q) coev hc
    hsep (isSignedTranspose_dualComplex K D q)

end Pairing

end CochainComplex

end
