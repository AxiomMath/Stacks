module

public import StacksCore.CategoryTheory.GradedObject.Monoidal.Dual
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Assembling a graded dual out of degreewise duals

Let `V` be a graded object of a monoidal preadditive category, supported in finitely many
degrees, and suppose that in every degree `n` the object `W (-n)` is a dual of `V n`, with
coevaluation `ηₙ : 𝟙 ⟶ V n ⊗ W (-n)` and evaluation `εₙ : W (-n) ⊗ V n ⟶ 𝟙`.  Then the sum
`η = ∑ ηₙ` and the morphism `ε` assembled from the `εₙ` exhibit `W` as a dual of `V`.

This is the converse of `CategoryTheory.GradedObject.Monoidal.exactPairingApply`, which reads a
graded dual degree by degree, and it is the verification that [Stacks, Tag 0FP9] omits: there
`V` is a bounded complex of `𝒪_X`-modules whose terms are locally direct summands of finite free
modules, `W (-n)` is the dual of the term `V n`, and the `ηₙ`, `εₙ` are the pairings of
[Stacks, Tag 0FNV].  Nothing below needs sheaves, a differential, or `ℤ` in particular: the
statements hold for any `AddGroup` grading and any monoidal preadditive category carrying the
standard graded-monoidal hypotheses.

## Main results

* `CategoryTheory.GradedObject.Monoidal.exactPairingOfDegreewise`: the two triangle identities
  for `η = ∑ ηₙ` and `ε = ∑ εₙ`, packaged as a `CategoryTheory.ExactPairing`.
* `CategoryTheory.GradedObject.Monoidal.coevaluation_exactPairingOfDegreewise` and
  `evaluation_exactPairingOfDegreewise`: the assembled coevaluation is the sum of the `ηₙ`, and
  the assembled evaluation restricts on the `(-n, n)` summand to `εₙ`.
* `CategoryTheory.GradedObject.Monoidal.coevApply_exactPairingOfDegreewise` and
  `evalApply_exactPairingOfDegreewise`: reading the assembled pairing degreewise returns the
  `ηₙ` and `εₙ` it was built from.
* `CategoryTheory.GradedObject.Monoidal.exactPairingOfComponents`: **the same conclusion with no
  finiteness whatsoever**, from any coevaluation whose component on the summand `V n ⊗ W (-n)`
  is `ηₙ` — the predicate
  `CategoryTheory.GradedObject.Monoidal.IsAssembledCoev`. `exactPairingOfDegreewise` is the case
  of `∑ ηₙ`, and `coevaluation_exactPairingOfComponents`,
  `coevApply_exactPairingOfComponents` and `evalApply_exactPairingOfComponents` read it back.

## Implementation notes

The argument is element-free and dual to the one reading a graded pairing degreewise.  A
triangle identity for graded objects is an identity of morphisms out of a tensor product, so it
is checked summand by summand: away from degree zero the graded unit is initial and both sides
vanish, and on the surviving summand the coevaluation is contracted against `V n`.  In that
contraction every term of `η = ∑ ηₙ` but the `n`-th is killed for degree reasons, so the
identity reduces to the ungraded triangle identity for the `n`-th pairing.  Finiteness of the
support enters only through the sum defining `η`, and the vanishing hypotheses on `V` and `W`
outside the support are what make the identities hold in the degrees that contribute nothing.
**Boundedness is a hypothesis on the coevaluation, not on the grading.** Because the contraction
kills every summand but one, it factors through that summand's *projection*
(`CategoryTheory.GradedObject.Monoidal.eq_πTensorObj_whiskerRight_comp`), and the coevaluation
then enters only through its component there.  So the triangle identities hold for *any*
coevaluation with the right components, bounded grading or not; that is
`exactPairingOfComponents`, and `exactPairingOfDegreewise` is the case where the components are
those of the finite sum `∑ ηₙ`.  What a bounded grading really buys is the *existence* of such a
morphism, the sum being finite; for a locally finite grading it has to be produced some other
way, which is what [Stacks, Tag 0FPR] needs over a site.

The evaluation needs no finiteness: it is a morphism *out* of a tensor product, hence given by
its components.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FFV](https://stacks.math.columbia.edu/tag/0FFV)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.GradedObject

universe w v u

namespace CategoryTheory.GradedObject.Monoidal

section Ungraded

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The triangle identity of an exact pairing, with the right unitor moved across. -/
private lemma triangle_right {X Y : C} (q : ExactPairing X Y) :
    (q.coevaluation' ▷ X) ≫ (α_ X Y X).hom ≫ (X ◁ q.evaluation') ≫ (ρ_ X).hom =
      (λ_ X).hom :=
  calc (q.coevaluation' ▷ X) ≫ (α_ X Y X).hom ≫ (X ◁ q.evaluation') ≫ (ρ_ X).hom
      = ((q.coevaluation' ▷ X) ≫ (α_ X Y X).hom ≫ (X ◁ q.evaluation')) ≫ (ρ_ X).hom := by
        simp only [assoc]
    _ = ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by rw [q.evaluation_coevaluation']
    _ = (λ_ X).hom := by simp

/-- The other triangle identity of an exact pairing, with the left unitor moved across. -/
private lemma triangle_left {X Y : C} (q : ExactPairing X Y) :
    (Y ◁ q.coevaluation') ≫ (α_ Y X Y).inv ≫ (q.evaluation' ▷ Y) ≫ (λ_ Y).hom =
      (ρ_ Y).hom :=
  calc (Y ◁ q.coevaluation') ≫ (α_ Y X Y).inv ≫ (q.evaluation' ▷ Y) ≫ (λ_ Y).hom
      = ((Y ◁ q.coevaluation') ≫ (α_ Y X Y).inv ≫ (q.evaluation' ▷ Y)) ≫ (λ_ Y).hom := by
        simp only [assoc]
    _ = ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫ (λ_ Y).hom := by rw [q.coevaluation_evaluation']
    _ = (ρ_ Y).hom := by simp

/-- **A dual of a zero object is a zero object.**  If `X` is zero then so is the whole of
`X ⊗ Y`, hence the coevaluation vanishes; feeding that into the second triangle identity
collapses the right unitor of `Y`, and an object whose unitor vanishes is zero. -/
lemma isZero_of_exactPairing_of_isZero [Preadditive C] [MonoidalPreadditive C] {X Y : C}
    (q : ExactPairing X Y) (hX : IsZero X) : IsZero Y := by
  have htensor : IsZero (X ⊗ Y) := (IsZero.iff_id_eq_zero _).2 <| by
    rw [← MonoidalCategory.id_whiskerRight X Y, hX.eq_of_src (𝟙 X) 0,
      MonoidalPreadditive.zero_whiskerRight]
  have hrho : (ρ_ Y).hom = 0 := by
    have h0 := q.coevaluation_evaluation'
    rw [htensor.eq_of_tgt q.coevaluation' 0, MonoidalPreadditive.whiskerLeft_zero,
      zero_comp] at h0
    simpa using congrArg (fun φ => φ ≫ (λ_ Y).hom) h0.symm
  exact (IsZero.iff_id_eq_zero _).2 <| by
    rw [← Iso.inv_hom_id (ρ_ Y), hrho, comp_zero]

end Ungraded

variable {I : Type w} [AddGroup I] [DecidableEq I] {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] [HasInitial C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (V W : GradedObject I C) (s : Finset I) (p : ∀ n : I, ExactPairing (V n) (W (-n)))

/-- The sum `∑ ηₙ` of the degreewise coevaluations over the degrees in `s`, landing in the
degree-zero part of `V ⊗ W`. -/
noncomputable def totalCoev : 𝟙_ C ⟶ tensorObj V W 0 :=
  ∑ n ∈ s, (p n).coevaluation' ≫ ιTensorObj V W n (-n) 0 (add_neg_cancel n)

/-- The morphism out of the degree-zero part of `W ⊗ V` whose component on the summand
indexed by `(-n, n)` is the degreewise evaluation `εₙ`. -/
noncomputable def totalEval : tensorObj W V 0 ⟶ 𝟙_ C :=
  tensorObjDesc (X₁ := W) (X₂ := V) (fun a b h =>
    eqToHom (by rw [show a = -b from by rwa [eq_neg_iff_add_eq_zero]]) ≫ (p b).evaluation')

/-- The candidate graded coevaluation attached to an arbitrary morphism into the degree-zero
part of `V ⊗ W`: that morphism in degree zero, and the unique morphism out of an initial object
elsewhere. Nothing is assumed of `coev`; the components it must have are
`IsAssembledCoev`. -/
noncomputable def gradedCoevOf (coev : 𝟙_ C ⟶ tensorObj V W 0) :
    𝟙_ (GradedObject I C) ⟶ V ⊗ W := fun j =>
  if hj : j = 0 then
    eqToHom (show (𝟙_ (GradedObject I C)) j = (𝟙_ (GradedObject I C)) 0 by rw [hj]) ≫
      tensorUnit₀.hom ≫ coev ≫
      eqToHom (show (V ⊗ W) 0 = (V ⊗ W) j by rw [hj])
  else (isInitialTensorUnitApply j hj).to _

/-- The candidate graded coevaluation: `∑ ηₙ` in degree zero, and the unique morphism out of an
initial object elsewhere. -/
noncomputable def gradedCoev : 𝟙_ (GradedObject I C) ⟶ V ⊗ W :=
  gradedCoevOf V W (totalCoev V W s p)

/-- The candidate graded evaluation: `totalEval` in degree zero, and the zero morphism into the
zero object elsewhere. -/
noncomputable def gradedEval : W ⊗ V ⟶ 𝟙_ (GradedObject I C) := fun j =>
  if hj : j = 0 then
    eqToHom (show (W ⊗ V) j = (W ⊗ V) 0 by rw [hj]) ≫ totalEval V W p ≫
      tensorUnit₀.inv ≫ eqToHom (show (𝟙_ (GradedObject I C)) 0 = (𝟙_ (GradedObject I C)) j by
        rw [hj])
  else ((isInitialTensorUnitApply j hj).isZero).from_ _

omit [Preadditive C] [MonoidalPreadditive C] in
/-- In degree zero the candidate graded coevaluation is the morphism it was built from, read
through `tensorUnit₀`. -/
lemma gradedCoevOf_zero (coev : 𝟙_ C ⟶ tensorObj V W 0) :
    gradedCoevOf V W coev 0 = tensorUnit₀.hom ≫ coev := by
  simp [gradedCoevOf]

omit [MonoidalPreadditive C] in
/-- In degree zero the graded coevaluation is `∑ ηₙ`, read through `tensorUnit₀`. -/
lemma gradedCoev_zero :
    gradedCoev V W s p 0 = tensorUnit₀.hom ≫ totalCoev V W s p :=
  gradedCoevOf_zero V W _

omit [MonoidalPreadditive C] in
/-- In degree zero the graded evaluation is `totalEval`, read through `tensorUnit₀`. -/
lemma gradedEval_zero :
    gradedEval V W p 0 = totalEval V W p ≫ tensorUnit₀.inv := by
  simp [gradedEval]

/-- Contracting the degree-zero part of `V ⊗ W` against `V n` on the right. -/
private noncomputable abbrev contractRight (n : I) : tensorObj V W 0 ⊗ V n ⟶ V n :=
  ιTensorObj (tensorObj V W) V 0 n n (zero_add n) ≫
    (α_ V W V).hom n ≫ (V ◁ gradedEval V W p) n ≫ (ρ_ V).hom n

/-- Contracting the degree-zero part of `V ⊗ W` against `W (-n)` on the left. -/
private noncomputable abbrev contractLeft (n : I) : W (-n) ⊗ tensorObj V W 0 ⟶ W (-n) :=
  ιTensorObj W (tensorObj V W) (-n) 0 (-n) (add_zero _) ≫
    (α_ W V W).inv (-n) ≫ (gradedEval V W p ▷ W) (-n) ≫ (λ_ W).hom (-n)

/-- The `(-n, n)` component of the graded evaluation. -/
private noncomputable abbrev evalApplyOf (n : I) : W (-n) ⊗ V n ⟶ 𝟙_ C :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ gradedEval V W p 0 ≫ tensorUnit₀.hom

omit [MonoidalPreadditive C] in
/-- The `(-n, n)` component of the graded evaluation is the degreewise evaluation `εₙ`. -/
private lemma evalApplyOf_eq (n : I) : evalApplyOf V W p n = (p n).evaluation' := by
  rw [evalApplyOf, gradedEval_zero, totalEval]
  simp

omit [MonoidalPreadditive C] in
/-- On the `(n, -n)` summand, the right contraction is the degreewise evaluation. -/
private lemma ι_contractRight (n : I) :
    (ιTensorObj V W n (-n) 0 (add_neg_cancel n) ▷ V n) ≫ contractRight V W p n =
      (α_ (V n) (W (-n)) (V n)).hom ≫ ((V n) ◁ evalApplyOf V W p n) ≫ (ρ_ (V n)).hom := by
  rw [contractRight, associator_hom_apply, rightUnitor_hom_apply, whiskerLeft_apply, ← assoc,
    ← ιTensorObj₃'_eq V W V n (-n) n n (by simp) 0 (by simp),
    ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq V W V n (-n) n n (by simp) 0 (by simp)]
  simp [evalApplyOf, ιTensorObj_rightUnitor_hom, whiskerLeft_comp]

omit [MonoidalPreadditive C] in
/-- Every other summand is killed, because the unit is initial away from degree zero. -/
private lemma ι_contractRight_eq_zero (n a b : I) (hab : a + b = 0) (hne : ¬ (a = n ∧ b = -n)) :
    (ιTensorObj V W a b 0 hab ▷ V n) ≫ contractRight V W p n = 0 := by
  have hb : b + n ≠ 0 := fun h0 ↦ hne <| by
    obtain rfl := add_eq_zero_iff_eq_neg.1 h0; exact ⟨add_neg_eq_zero.1 hab, rfl⟩
  have hzero : ιTensorObj V (𝟙_ (GradedObject I C)) a (b + n) n
      (by rw [← add_assoc, hab, zero_add]) ≫ (rightUnitor V).hom n = 0 :=
    (IsInitial.isInitialObj ((curriedTensor C).obj (V a)) _
      (isInitialTensorUnitApply (b + n) hb)).hom_ext _ _
  rw [contractRight, associator_hom_apply, rightUnitor_hom_apply, whiskerLeft_apply, ← assoc,
    ← ιTensorObj₃'_eq V W V a b n n (by simp [hab]) 0 hab, ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq V W V a b n n (by simp [hab]) (b + n) rfl, assoc, ι_tensorHom_assoc, hzero]
  simp

omit [MonoidalPreadditive C] in
/-- On the `(n, -n)` summand, the left contraction is the degreewise evaluation. -/
private lemma ι_contractLeft (n : I) :
    (W (-n) ◁ ιTensorObj V W n (-n) 0 (add_neg_cancel n)) ≫ contractLeft V W p n =
      (α_ (W (-n)) (V n) (W (-n))).inv ≫ (evalApplyOf V W p n ▷ W (-n)) ≫
        (λ_ (W (-n))).hom := by
  rw [contractLeft, ← assoc, ← ιTensorObj₃_eq W V W (-n) n (-n) (-n) (by simp) 0
      (add_neg_cancel n), associator_inv_apply, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq W V W (-n) n (-n) (-n) (by simp) 0 (neg_add_cancel n), assoc,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom]
  simp [evalApplyOf, comp_whiskerRight]

omit [MonoidalPreadditive C] in
/-- Every other summand is killed, because the unit is initial away from degree zero. -/
private lemma ι_contractLeft_eq_zero (n a b : I) (hab : a + b = 0) (hne : ¬ (a = n ∧ b = -n)) :
    (W (-n) ◁ ιTensorObj V W a b 0 hab) ≫ contractLeft V W p n = 0 := by
  have ha : -n + a ≠ 0 := fun h0 ↦ hne <| by
    obtain rfl := (neg_add_eq_zero.1 h0).symm; exact ⟨rfl, eq_neg_of_add_eq_zero_right hab⟩
  have hzero : ιTensorObj (𝟙_ (GradedObject I C)) W (-n + a) b (-n)
      (by rw [add_assoc, hab, add_zero]) ≫ (leftUnitor W).hom (-n) = 0 :=
    (IsInitial.isInitialObj ((curriedTensor C).flip.obj (W b)) _
      (isInitialTensorUnitApply (-n + a) ha)).hom_ext _ _
  rw [contractLeft, ← assoc, ← ιTensorObj₃_eq W V W (-n) a b (-n) (by simp [add_assoc, hab]) 0 hab,
    associator_inv_apply, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq W V W (-n) a b (-n) (by simp [add_assoc, hab]) (-n + a) rfl, assoc,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, hzero]
  simp

/-- The `(n, -n)` component of `∑ ηₙ`, for `n` in the range of summation, is `ηₙ`. -/
private lemma totalCoev_comp_πTensorObj {J : Type w} [AddGroup J] [DecidableEq J] {D : Type u}
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [∀ X₁ X₂ : GradedObject J D, HasTensor X₁ X₂] (V W : GradedObject J D) (s : Finset J)
    (p : ∀ n : J, ExactPairing (V n) (W (-n))) (n : J) (hn : n ∈ s) :
    totalCoev V W s p ≫ πTensorObj V W n (-n) 0 (add_neg_cancel n) = (p n).coevaluation' := by
  rw [totalCoev, Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem n hn (fun m _ hmn => by
      rw [assoc, ιTensorObj_πTensorObj_ne V W n (-n) m (-m) 0 (add_neg_cancel m)
        (add_neg_cancel n) (fun h => hmn h.1), comp_zero])]
  simp

/-- Contracting `∑ ηₙ` against `V n` on the right, for `n` in the range of summation, leaves the
left unitor: all terms but the `n`-th die for degree reasons, and that one is the `n`-th triangle
identity. -/
private lemma totalCoev_contractRight_of_mem (n : I) (hn : n ∈ s) :
    (totalCoev V W s p ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom := by
  rw [totalCoev, sum_whiskerRight, Preadditive.sum_comp]
  have hz : ∀ m ∈ s, m ≠ n →
      (((p m).coevaluation' ≫ ιTensorObj V W m (-m) 0 (add_neg_cancel m)) ▷ V n) ≫
        contractRight V W p n = 0 := by
    intro m _ hmn
    rw [comp_whiskerRight, assoc,
      ι_contractRight_eq_zero V W p n m (-m) (add_neg_cancel m) (fun h => hmn h.1), comp_zero]
  rw [Finset.sum_eq_single_of_mem n hn hz, comp_whiskerRight, assoc, ι_contractRight,
    evalApplyOf_eq, triangle_right (p n)]

/-- Contracting `∑ ηₙ` against `V n` on the right leaves the left unitor. -/
private lemma totalCoev_contractRight (hV : ∀ m, m ∉ s → Limits.IsZero (V m)) (n : I) :
    (totalCoev V W s p ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom := by
  by_cases hn : n ∈ s
  · exact totalCoev_contractRight_of_mem V W s p n hn
  · exact (hV n hn).eq_of_tgt _ _

/-- Contracting `∑ ηₙ` against `W (-n)` on the left, for `n` in the range of summation, leaves
the right unitor. -/
private lemma totalCoev_contractLeft_of_mem (n : I) (hn : n ∈ s) :
    (W (-n) ◁ totalCoev V W s p) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom := by
  rw [totalCoev, whiskerLeft_sum, Preadditive.sum_comp]
  have hz : ∀ m ∈ s, m ≠ n →
      (W (-n) ◁ ((p m).coevaluation' ≫ ιTensorObj V W m (-m) 0 (add_neg_cancel m))) ≫
        contractLeft V W p n = 0 := by
    intro m _ hmn
    rw [whiskerLeft_comp, assoc,
      ι_contractLeft_eq_zero V W p n m (-m) (add_neg_cancel m) (fun h => hmn h.1), comp_zero]
  rw [Finset.sum_eq_single_of_mem n hn hz, whiskerLeft_comp, assoc, ι_contractLeft,
    evalApplyOf_eq, triangle_left (p n)]

/-- Contracting `∑ ηₙ` against `W (-n)` on the left leaves the right unitor. -/
private lemma totalCoev_contractLeft (hW : ∀ m, m ∉ s → Limits.IsZero (W (-m))) (n : I) :
    (W (-n) ◁ totalCoev V W s p) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom := by
  by_cases hn : n ∈ s
  · exact totalCoev_contractLeft_of_mem V W s p n hn
  · exact (hW n hn).eq_of_tgt _ _

omit [MonoidalPreadditive C] in
/-- The first graded triangle identity, read on the `(0, n)` summand. -/
private lemma ι_evaluation_coevaluation (coev : 𝟙_ C ⟶ tensorObj V W 0) (n : I)
    (hc : (coev ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom) :
    ιTensorObj (𝟙_ (GradedObject I C)) V 0 n n (zero_add n) ≫
        (gradedCoevOf V W coev ▷ V ≫ (α_ V W V).hom ≫ V ◁ gradedEval V W p) n =
      ιTensorObj (𝟙_ (GradedObject I C)) V 0 n n (zero_add n) ≫
        ((λ_ V).hom ≫ (ρ_ V).inv) n := by
  have : IsIso ((ρ_ V).hom n) := ⟨(ρ_ V).inv n, by simp, by simp⟩
  rw [← cancel_mono ((ρ_ V).hom n)]
  simp only [categoryOfGradedObjects_comp, assoc, Iso.inv_hom_id_eval, comp_id,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom,
    categoryOfGradedObjects_id, tensorHom_id]
  rw [gradedCoevOf_zero, comp_whiskerRight, assoc]
  exact congrArg (fun φ => tensorUnit₀.hom ▷ V n ≫ φ) hc

omit [MonoidalPreadditive C] in
/-- The second graded triangle identity, read on the `(-n, 0)` summand. -/
private lemma ι_coevaluation_evaluation (coev : 𝟙_ C ⟶ tensorObj V W 0) (n : I)
    (hc : (W (-n) ◁ coev) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom) :
    ιTensorObj W (𝟙_ (GradedObject I C)) (-n) 0 (-n) (add_zero _) ≫
        (W ◁ gradedCoevOf V W coev ≫ (α_ W V W).inv ≫ gradedEval V W p ▷ W) (-n) =
      ιTensorObj W (𝟙_ (GradedObject I C)) (-n) 0 (-n) (add_zero _) ≫
        ((ρ_ W).hom ≫ (λ_ W).inv) (-n) := by
  have : IsIso ((λ_ W).hom (-n)) := ⟨(λ_ W).inv (-n), by simp, by simp⟩
  rw [← cancel_mono ((λ_ W).hom (-n))]
  simp only [categoryOfGradedObjects_comp, assoc, Iso.inv_hom_id_eval, comp_id,
    whiskerLeft_apply, ι_tensorHom_assoc, rightUnitor_hom_apply, ιTensorObj_rightUnitor_hom,
    categoryOfGradedObjects_id, id_tensorHom]
  rw [gradedCoevOf_zero, whiskerLeft_comp, assoc]
  exact congrArg (fun φ => W (-n) ◁ tensorUnit₀.hom ≫ φ) hc

omit [MonoidalPreadditive C] in
variable {V W p} in
/-- The first graded triangle identity for `gradedCoevOf θ`, from its contractions. -/
private lemma evaluation_coevaluation_of (θ : 𝟙_ C ⟶ tensorObj V W 0)
    (hθ : ∀ n, (θ ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom) :
    gradedCoevOf V W θ ▷ V ≫ (α_ V W V).hom ≫ V ◁ gradedEval V W p =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  funext n
  refine tensorObj_ext _ _ (fun a b hab => ?_)
  by_cases ha : a = 0
  · subst ha
    obtain rfl : b = n := by simpa using hab
    exact ι_evaluation_coevaluation V W p θ b (hθ b)
  · exact (IsInitial.isInitialObj ((curriedTensor C).flip.obj (V b)) _
      (isInitialTensorUnitApply a ha)).hom_ext _ _

omit [MonoidalPreadditive C] in
variable {V W p} in
/-- The second graded triangle identity for `gradedCoevOf θ`, from its contractions. -/
private lemma coevaluation_evaluation_of (θ : 𝟙_ C ⟶ tensorObj V W 0)
    (hθ : ∀ n, (W (-n) ◁ θ) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom) :
    W ◁ gradedCoevOf V W θ ≫ (α_ W V W).inv ≫ gradedEval V W p ▷ W =
      (ρ_ W).hom ≫ (λ_ W).inv := by
  funext j
  obtain ⟨n, rfl⟩ : ∃ n, j = -n := ⟨-j, (neg_neg j).symm⟩
  refine tensorObj_ext _ _ (fun a b hab => ?_)
  by_cases hb : b = 0
  · subst hb
    obtain rfl : a = -n := by simpa using hab
    exact ι_coevaluation_evaluation V W p θ n (hθ n)
  · exact (IsInitial.isInitialObj ((curriedTensor C).obj (W a)) _
      (isInitialTensorUnitApply b hb)).hom_ext _ _

/-- **Degreewise duals assemble into a graded dual.**  If `V` vanishes outside the finite set
`s`, as does `W` in the negated degrees, and `W (-n)` is a dual of `V n` for every `n`, then
`∑ ηₙ` and `∑ εₙ` satisfy the two triangle identities, so `W` is a dual of `V`. -/
@[instance_reducible]
noncomputable def exactPairingOfDegreewise (hV : ∀ m, m ∉ s → Limits.IsZero (V m))
    (hW : ∀ m, m ∉ s → Limits.IsZero (W (-m))) : ExactPairing V W where
  coevaluation' := gradedCoev V W s p
  evaluation' := gradedEval V W p
  evaluation_coevaluation' := by
    funext n
    refine tensorObj_ext _ _ (fun a b hab => ?_)
    by_cases ha : a = 0
    · subst ha
      obtain rfl : b = n := by simpa using hab
      exact ι_evaluation_coevaluation V W p (totalCoev V W s p) b
        (totalCoev_contractRight V W s p hV b)
    · exact (IsInitial.isInitialObj ((curriedTensor C).flip.obj (V b)) _
        (isInitialTensorUnitApply a ha)).hom_ext _ _
  coevaluation_evaluation' := by
    funext j
    obtain ⟨n, rfl⟩ : ∃ n, j = -n := ⟨-j, (neg_neg j).symm⟩
    refine tensorObj_ext _ _ (fun a b hab => ?_)
    by_cases hb : b = 0
    · subst hb
      obtain rfl : a = -n := by simpa using hab
      exact ι_coevaluation_evaluation V W p (totalCoev V W s p) n
        (totalCoev_contractLeft V W s p hW n)
    · exact (IsInitial.isInitialObj ((curriedTensor C).obj (W a)) _
        (isInitialTensorUnitApply b hb)).hom_ext _ _

/-- **The components a candidate coevaluation must have.** The degree-zero part of `V ⊗ W` is
the coproduct of the `V n ⊗ W (-n)`, those being its only summands, and this says that the
component of `coev` on the `n`-th of them is the degreewise coevaluation `ηₙ`.

For a bounded grading the finite sum `∑ ηₙ` has these components; in general a morphism with
them has to be produced by other means — and this is the *only* property of it that the two
triangle identities use, which is what
`CategoryTheory.GradedObject.Monoidal.exactPairingOfComponents` says. -/
def IsAssembledCoev (coev : 𝟙_ C ⟶ tensorObj V W 0) : Prop :=
  ∀ n : I, coev ≫ πTensorObj V W n (-n) 0 (add_neg_cancel n) = (p n).coevaluation'

/-- Contracting a coevaluation with the right components against `V n` on the right leaves the
left unitor: the contraction kills every summand but the `n`-th, so it factors through the
`n`-th projection, and what remains is the `n`-th triangle identity. No finiteness. -/
private lemma coev_contractRight (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) (n : I) :
    (coev ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom := by
  rw [eq_πTensorObj_whiskerRight_comp V W V n (-n) 0 n (add_neg_cancel n)
      (contractRight V W p n)
      (fun a b hab hne => ι_contractRight_eq_zero V W p n a b hab hne),
    ι_contractRight, ← comp_whiskerRight_assoc, h n, evalApplyOf_eq]
  exact triangle_right (p n)

/-- Contracting a coevaluation with the right components against `W (-n)` on the left leaves
the right unitor. -/
private lemma coev_contractLeft (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) (n : I) :
    (W (-n) ◁ coev) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom := by
  rw [eq_πTensorObj_whiskerLeft_comp W V W n (-n) 0 (-n) (add_neg_cancel n)
      (contractLeft V W p n)
      (fun a b hab hne => ι_contractLeft_eq_zero V W p n a b hab hne),
    ι_contractLeft, ← whiskerLeft_comp_assoc, h n, evalApplyOf_eq]
  exact triangle_left (p n)

/-- **Degreewise duals assemble into a graded dual as soon as a coevaluation with the right
components exists** — with no boundedness of the grading whatsoever. The two triangle
identities are read one summand at a time, and in each of them all summands but one die for
degree reasons, so the coevaluation enters only through that one component. -/
@[instance_reducible]
noncomputable def exactPairingOfComponents (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) : ExactPairing V W where
  coevaluation' := gradedCoevOf V W coev
  evaluation' := gradedEval V W p
  evaluation_coevaluation' := by
    funext n
    refine tensorObj_ext _ _ (fun a b hab => ?_)
    by_cases ha : a = 0
    · subst ha
      obtain rfl : b = n := by simpa using hab
      exact ι_evaluation_coevaluation V W p coev b (coev_contractRight V W p coev h b)
    · exact (IsInitial.isInitialObj ((curriedTensor C).flip.obj (V b)) _
        (isInitialTensorUnitApply a ha)).hom_ext _ _
  coevaluation_evaluation' := by
    funext j
    obtain ⟨n, rfl⟩ : ∃ n, j = -n := ⟨-j, (neg_neg j).symm⟩
    refine tensorObj_ext _ _ (fun a b hab => ?_)
    by_cases hb : b = 0
    · subst hb
      obtain rfl : a = -n := by simpa using hab
      exact ι_coevaluation_evaluation V W p coev n (coev_contractLeft V W p coev h n)
    · exact (IsInitial.isInitialObj ((curriedTensor C).obj (W a)) _
        (isInitialTensorUnitApply b hb)).hom_ext _ _

/-- The coevaluation of the pairing assembled from components is the morphism it was built
from. -/
lemma coevaluation_exactPairingOfComponents (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) :
    letI := exactPairingOfComponents V W p coev h
    (η_ V W) 0 = tensorUnit₀.hom ≫ coev :=
  gradedCoevOf_zero V W coev

/-- Reading the pairing assembled from components degreewise returns the degreewise
coevaluation. -/
lemma coevApply_exactPairingOfComponents (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) (n : I) :
    letI := exactPairingOfComponents V W p coev h
    coevApply V W n = (p n).coevaluation' := by
  show tensorUnit₀.inv ≫ gradedCoevOf V W coev 0 ≫
    πTensorObj V W n (-n) 0 (add_neg_cancel n) = _
  rw [gradedCoevOf_zero, assoc, Iso.inv_hom_id_assoc]
  exact h n

/-- Reading the pairing assembled from components degreewise returns the degreewise
evaluation. -/
lemma evalApply_exactPairingOfComponents (coev : 𝟙_ C ⟶ tensorObj V W 0)
    (h : IsAssembledCoev V W p coev) (n : I) :
    letI := exactPairingOfComponents V W p coev h
    evalApply V W n = (p n).evaluation' :=
  evalApplyOf_eq V W p n

/-- **Degreewise duals assemble into a graded dual, from the vanishing of `V` alone.**  The
hypothesis that `W` vanishes in the negated degrees outside `s` is redundant: in a degree where
`V` vanishes, `W (-n)` is a dual of a zero object and so is itself zero. -/
@[instance_reducible]
noncomputable def exactPairingOfDegreewiseOfIsZero
    (hV : ∀ m, m ∉ s → Limits.IsZero (V m)) : ExactPairing V W :=
  exactPairingOfDegreewise V W s p hV
    (fun m hm => isZero_of_exactPairing_of_isZero (p m) (hV m hm))

variable (hV : ∀ m, m ∉ s → Limits.IsZero (V m)) (hW : ∀ m, m ∉ s → Limits.IsZero (W (-m)))

/-- The coevaluation of the assembled pairing is the sum of the degreewise coevaluations. -/
lemma coevaluation_exactPairingOfDegreewise :
    letI := exactPairingOfDegreewise V W s p hV hW
    (η_ V W) 0 =
      tensorUnit₀.hom ≫ ∑ n ∈ s, (p n).coevaluation' ≫
        ιTensorObj V W n (-n) 0 (add_neg_cancel n) :=
  gradedCoev_zero V W s p

/-- The evaluation of the assembled pairing restricts on the `(-n, n)` summand to the degreewise
evaluation. -/
lemma evaluation_exactPairingOfDegreewise (n : I) :
    letI := exactPairingOfDegreewise V W s p hV hW
    ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (ε_ V W) 0 ≫ tensorUnit₀.hom =
      (p n).evaluation' :=
  evalApplyOf_eq V W p n

/-- Reading the assembled pairing degreewise returns the degreewise evaluation it was built
from. -/
lemma evalApply_exactPairingOfDegreewise (n : I) :
    letI := exactPairingOfDegreewise V W s p hV hW
    evalApply V W n = (p n).evaluation' :=
  evalApplyOf_eq V W p n

/-- Reading the assembled pairing degreewise returns the degreewise coevaluation it was built
from. -/
lemma coevApply_exactPairingOfDegreewise (n : I) (hn : n ∈ s) :
    letI := exactPairingOfDegreewise V W s p hV hW
    coevApply V W n = (p n).coevaluation' := by
  show tensorUnit₀.inv ≫ (gradedCoev V W s p) 0 ≫ πTensorObj V W n (-n) 0 _ = _
  rw [gradedCoev_zero]
  simp only [assoc, Iso.inv_hom_id_assoc]
  exact totalCoev_comp_πTensorObj V W s p n hn

section LocallyFinite

/-! ### Locally finite sums

When `V` is supported in finitely many degrees only after applying each member of a jointly
faithful family of monoidal functors `Fᵢ`, the sum `∑ ηₙ` has no global meaning, but any
`θ : 𝟙 ⟶ (V ⊗ W) 0` whose image under `Fᵢ` is the image of the finite sum over the degrees
surviving `Fᵢ` serves in its place. -/

universe w' v' u'

variable {ι : Type w'} {D : ι → Type u'} [∀ i, Category.{v'} (D i)]
  [∀ i, MonoidalCategory (D i)] [∀ i, Preadditive (D i)] [∀ i, MonoidalPreadditive (D i)]
  (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]

omit [Preadditive C] [MonoidalPreadditive C] [HasInitial C]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)] in
/-- The image of a tensor product one factor of which is killed by a monoidal functor into a
monoidal preadditive category is a zero object. -/
lemma isZero_map_tensor_of_isZero_map_left (i : ι) (X Y : C) (hX : IsZero ((F i).obj X)) :
    IsZero ((F i).obj (X ⊗ Y)) :=
  ((IsZero.iff_id_eq_zero _).2 <| by
    rw [← MonoidalCategory.id_whiskerRight ((F i).obj X) ((F i).obj Y), hX.eq_of_src (𝟙 _) 0,
      MonoidalPreadditive.zero_whiskerRight]).of_iso (Functor.Monoidal.μIso (F i) X Y).symm

omit [Preadditive C] [MonoidalPreadditive C] [HasInitial C]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)] in
/-- A dual of an object killed by a monoidal functor into a monoidal preadditive category is
killed by it. -/
lemma isZero_map_of_exactPairing (i : ι) {X Y : C} (q : ExactPairing X Y)
    (hX : IsZero ((F i).obj X)) : IsZero ((F i).obj Y) :=
  isZero_of_exactPairing_of_isZero (ExactPairing.map (F i) X Y) hX

variable (hF : JointlyFaithful F) (t : ι → Finset I)
  (ht : ∀ i, ∀ n, n ∉ t i → IsZero ((F i).obj (V n)))
  (θ : 𝟙_ C ⟶ tensorObj V W 0) (hθ : ∀ i, (F i).map θ = (F i).map (totalCoev V W (t i) p))

omit [∀ i, Preadditive (D i)] [∀ i, MonoidalPreadditive (D i)] in
include hF ht hθ in
private lemma contractRight_of_locallyFinite (n : I) :
    (θ ▷ V n) ≫ contractRight V W p n = (λ_ (V n)).hom :=
  hF.map_injective fun i => by
    by_cases hn : n ∈ t i
    · rw [Functor.map_comp, Functor.Monoidal.map_whiskerRight, hθ i,
        ← Functor.Monoidal.map_whiskerRight, ← Functor.map_comp,
        totalCoev_contractRight_of_mem V W (t i) p n hn]
    · exact (ht i n hn).eq_of_tgt _ _

include hF ht hθ in
private lemma contractLeft_of_locallyFinite (n : I) :
    (W (-n) ◁ θ) ≫ contractLeft V W p n = (ρ_ (W (-n))).hom :=
  hF.map_injective fun i => by
    by_cases hn : n ∈ t i
    · rw [Functor.map_comp, Functor.Monoidal.map_whiskerLeft, hθ i,
        ← Functor.Monoidal.map_whiskerLeft, ← Functor.map_comp,
        totalCoev_contractLeft_of_mem V W (t i) p n hn]
    · exact (isZero_map_of_exactPairing F i (p n) (ht i n hn)).eq_of_tgt _ _

/-- **Degreewise duals assemble into a graded dual along a locally finite sum.**  Let
`Fᵢ : C ⥤ Dᵢ` be a jointly faithful family of monoidal functors into monoidal preadditive
categories, let `W (-n)` be a dual of `V n` in every degree, and suppose `Fᵢ` kills `V n` for
`n` outside a finite set `tᵢ`.  If `θ : 𝟙 ⟶ (V ⊗ W) 0` is carried by every `Fᵢ` to the image of
the finite sum `∑_{n ∈ tᵢ} ηₙ`, then `θ` and `ε = ∑ εₙ` exhibit `W` as a dual of `V`. -/
@[instance_reducible]
noncomputable def exactPairingOfLocallyFinite : ExactPairing V W where
  coevaluation' := gradedCoevOf V W θ
  evaluation' := gradedEval V W p
  evaluation_coevaluation' := by
    exact evaluation_coevaluation_of θ (contractRight_of_locallyFinite V W p F hF t ht θ hθ)
  coevaluation_evaluation' := by
    exact coevaluation_evaluation_of θ (contractLeft_of_locallyFinite V W p F hF t ht θ hθ)

/-- The coevaluation of `exactPairingOfLocallyFinite` is `θ` in degree zero. -/
lemma coevaluation_exactPairingOfLocallyFinite :
    letI := exactPairingOfLocallyFinite V W p F hF t ht θ hθ
    (η_ V W) 0 = tensorUnit₀.hom ≫ θ :=
  gradedCoevOf_zero V W θ

/-- The evaluation of `exactPairingOfLocallyFinite` restricts on the `(-n, n)` summand to the
degreewise evaluation `εₙ`. -/
lemma evaluation_exactPairingOfLocallyFinite (n : I) :
    letI := exactPairingOfLocallyFinite V W p F hF t ht θ hθ
    ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (ε_ V W) 0 ≫ tensorUnit₀.hom =
      (p n).evaluation' :=
  evalApplyOf_eq V W p n

omit [MonoidalPreadditive C] [HasInitial C]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
include hF ht hθ in
/-- **`θ` is `∑ ηₙ`, component by component**: its component on the summand `(n, -n)` of
`(V ⊗ W) 0` is the degreewise coevaluation `ηₙ`. -/
lemma comp_πTensorObj_of_locallyFinite (n : I) :
    θ ≫ πTensorObj V W n (-n) 0 (add_neg_cancel n) = (p n).coevaluation' :=
  hF.map_injective fun i => by
    by_cases hn : n ∈ t i
    · rw [Functor.map_comp, hθ i, ← Functor.map_comp, totalCoev_comp_πTensorObj V W (t i) p n hn]
    · exact (isZero_map_tensor_of_isZero_map_left F i (V n) (W (-n)) (ht i n hn)).eq_of_tgt _ _

end LocallyFinite

end CategoryTheory.GradedObject.Monoidal

end
