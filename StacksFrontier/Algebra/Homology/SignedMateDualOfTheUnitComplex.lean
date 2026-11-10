module

public import StacksFrontier.Algebra.Homology.DualComplexOfSignedMateDuals

/-!
# The unit complex as a witness for the signed-transpose dual assembly

`CochainComplex.exactPairingOfSignedMateDual` takes a complex `K` bounded by a `Finset`, a
complex `L` with degreewise duals `L^{-n}` of `K^n`, and the signed-transpose condition on the
differential of `L`, and produces a left dual of `K` in the monoidal category of complexes.
This file exhibits an inhabitant of that hypothesis set assuming nothing about the ambient
monoidal category: the monoidal unit placed in degree zero, self-dual, bounded by `{0}`, with
the signed-transpose condition holding because every differential of a single complex is zero.

The point is that the hypotheses of the assembly are not met only by zero complexes, which no
build, axiom check or binder scan can detect: the witness is degenerate exactly when `𝟙_ C` is a
zero object (`Stacks.SignedMateDual.isZero_unitComplex_X_zero_iff`), and in degree zero the
degreewise datum it supplies is the unit pairing of `C` and not a pairing of zero objects
(`Stacks.SignedMateDual.unitPairing_zero`).

It also records why the Koszul sign in `CochainComplex.IsSignedMateDual` cannot be dropped:
holding the signed and the unsigned condition at once makes the mate of the differential
2-torsion in every odd degree
(`Stacks.SignedMateDual.two_torsion_of_signed_and_unsigned`).

**Nothing here is a clause of [Stacks, Tag 0FP9] and nothing here is tagged.**  The witness is an
instance of the assembly's hypotheses, not part of any assertion.

## Main results

* `Stacks.SignedMateDual.exactPairingOfIsZero`: two zero objects are an exact pairing.
* `Stacks.SignedMateDual.exactPairingUnitComplex`: every binder of
  `CochainComplex.exactPairingOfSignedMateDual` instantiated at once.
* `Stacks.SignedMateDual.isZero_unitComplex_X_zero_iff` and
  `Stacks.SignedMateDual.not_isZero_unitComplex_X_zero`: the witness is non-degenerate as soon as
  `𝟙_ C` is.
* `Stacks.SignedMateDual.two_torsion_of_signed_and_unsigned`: the Koszul sign is not removable.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category Limits MonoidalCategory GradedObject

universe v u

namespace Stacks.SignedMateDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- PROVED NEGATION of the unsigned variant: if the differential of `L` were BOTH the signed and
the unsigned mate of the differential of `K`, then in every odd degree that mate would be
2-torsion.  So the Koszul sign in `CochainComplex.IsSignedMateDual` is not removable: dropping it
changes the hypothesis, and in a 2-torsion-free category the two are incompatible unless the
differential's mate vanishes. -/
theorem two_torsion_of_signed_and_unsigned (K L : CochainComplex C ℤ)
    (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))
    (hd : CochainComplex.IsSignedMateDual K L p)
    (hd' : ∀ n : ℤ, L.d (-(n + 1)) (-n) =
      CategoryTheory.ExactPairing.mate (p n) (p (n + 1)) (K.d n (n + 1)))
    (n : ℤ) (hn : Odd n) :
    CategoryTheory.ExactPairing.mate (p n) (p (n + 1)) (K.d n (n + 1)) +
      CategoryTheory.ExactPairing.mate (p n) (p (n + 1)) (K.d n (n + 1)) = 0 := by
  have h := (hd n).symm.trans (hd' n)
  rw [Int.negOnePow_odd n hn, Units.neg_smul, one_smul] at h
  nth_rw 1 [← h]
  exact neg_add_cancel _

variable [MonoidalPreadditive C]

/-- A tensor product with a zero factor on the right is a zero object. -/
lemma isZero_tensor_of_isZero_right (X Y : C) (h : IsZero Y) : IsZero (X ⊗ Y) :=
  (IsZero.iff_id_eq_zero _).2 <| by
    rw [← MonoidalCategory.whiskerLeft_id X Y, h.eq_of_src (𝟙 Y) 0,
      MonoidalPreadditive.whiskerLeft_zero]

/-- **Two zero objects are an exact pairing.**  Both candidate morphisms are zero and both
triangle identities are identities between morphisms out of a zero object. -/
@[instance_reducible]
def exactPairingOfIsZero (X Y : C) (hX : IsZero X) (hY : IsZero Y) : ExactPairing X Y where
  coevaluation' := 0
  evaluation' := 0
  coevaluation_evaluation' :=
    (ExactPairing.isZero_tensor_of_isZero_left Y (𝟙_ C) hY).eq_of_src _ _
  evaluation_coevaluation' := (isZero_tensor_of_isZero_right (𝟙_ C) X hX).eq_of_src _ _

variable [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- The unit complex `𝟙_[0]`, which is the witness below. -/
noncomputable abbrev unitComplex : CochainComplex C ℤ := 𝟙_ (CochainComplex C ℤ)

/-- The degreewise self-pairings of the unit complex: the unit pairing in degree zero, the
pairing of two zero objects elsewhere. -/
@[instance_reducible]
noncomputable def unitPairing (n : ℤ) :
    ExactPairing ((unitComplex (C := C)).X n) ((unitComplex (C := C)).X (-n)) :=
  if h : n = 0 then by
    subst h
    exact exactPairingCongr
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C))
  else
    exactPairingOfIsZero _ _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) n h)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) (-n)
        (by omega))

/-- The unit complex has zero differentials, so the signed-transpose condition holds. -/
lemma isSignedMateDual_unitPairing :
    CochainComplex.IsSignedMateDual (unitComplex (C := C)) (unitComplex (C := C)) unitPairing := by
  intro n
  rw [show (unitComplex (C := C)).d (-(n + 1)) (-n) = 0 from HomologicalComplex.single_obj_d ..,
    show (unitComplex (C := C)).d n (n + 1) = 0 from HomologicalComplex.single_obj_d ..,
    CategoryTheory.ExactPairing.mate_zero, smul_zero]

/-- The unit complex vanishes outside degree zero. -/
lemma isZero_unitComplex_X (m : ℤ) (hm : m ∉ ({0} : Finset ℤ)) :
    IsZero ((unitComplex (C := C)).X m) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) m (by simpa using hm)

/-- **The witness is degenerate exactly when the monoidal unit of `C` is a zero object.**  So the
hypotheses of `CochainComplex.exactPairingOfSignedMateDual` are met by a pairing of nonzero
objects whenever `C` has a nonzero unit, and the theorem is not vacuous. -/
theorem isZero_unitComplex_X_zero_iff :
    IsZero ((unitComplex (C := C)).X 0) ↔ IsZero (𝟙_ C) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C)).isZero_iff

/-- **The witness is non-degenerate** whenever `C` has a nonzero monoidal unit: the degree-zero
term of the complex the theorem is applied to is then not a zero object, so the pairing produced
is a pairing of nonzero objects. -/
theorem not_isZero_unitComplex_X_zero (h : ¬ IsZero (𝟙_ C)) :
    ¬ IsZero ((unitComplex (C := C)).X 0) :=
  fun hz => h (isZero_unitComplex_X_zero_iff.1 hz)

/-- In degree zero the witness pairing is the unit pairing of `C`, transported along the two
isomorphisms `𝟙_[0]^0 ≅ 𝟙_ C`: the degreewise datum the theorem consumes is the unit pairing,
not a pairing of zero objects. -/
theorem unitPairing_zero :
    unitPairing (C := C) 0 =
      exactPairingCongr
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C))
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ C)) := by
  rw [unitPairing, dite_eq_left rfl]

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- **Every binder of `CochainComplex.exactPairingOfSignedMateDual` is inhabited at once.**
`K = L = 𝟙_[0]`, the degreewise duals are the unit pairing in degree zero and the zero pairing
elsewhere, the bound is `{0}`, and the signed-transpose condition holds because every differential
of the unit complex is zero.  The conclusion is a genuine left dual in the monoidal category of
complexes. -/
@[instance_reducible]
noncomputable def exactPairingUnitComplex :
    ExactPairing (unitComplex (C := C)) (unitComplex (C := C)) :=
  CochainComplex.exactPairingOfSignedMateDual (unitComplex (C := C)) (unitComplex (C := C))
    unitPairing {0} isZero_unitComplex_X isSignedMateDual_unitPairing

end Stacks.SignedMateDual

end
