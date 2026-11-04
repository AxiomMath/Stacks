module

public import StacksFrontier.Algebra.Homology.AssembleLeftDual
public import StacksFrontier.Algebra.Homology.DualAssemblyOfComplexes
public import StacksFrontier.Algebra.Homology.InternalHomComplex

/-!
# A dual pair of complexes out of degreewise duals and the signed transpose

Let `C` be a monoidal preadditive category carrying the coproducts that make both
`GradedObject ℤ C` and `CochainComplex C ℤ` monoidal.  Let `K` be a cochain complex vanishing
outside a finite set of degrees and let `L` be a second complex with a chosen dual pairing
`pₙ : ExactPairing (K^n) (L^{-n})` in every degree.  Then `η = ∑ ηₙ` and `ε = ∑ εₙ` are
morphisms **of complexes**, and `L` is a left dual of `K` in `CochainComplex C ℤ`, as soon as the
differential of `L` is the *signed transpose* of the differential of `K`:
`d_L^{-(n+1), -n} = (-1)^n (d_K^{n, n+1})^∨`, the mate being taken for the pairings `pₙ`,
`p_{n+1}`.

This is the verification [Stacks, Tag 0FP9] omits, at the level of complexes.

## Main definitions

* `CategoryTheory.ExactPairing.mate`: the right adjoint mate `f^∨ : Y' ⟶ X'` of `f : X ⟶ Y` for
  chosen duals `X'` of `X` and `Y'` of `Y`.
* `CochainComplex.IsSignedMateDual`: the signed-transpose condition on the differential of `L`.
* `CochainComplex.dualCoeval` and `CochainComplex.dualEval`: `η = ∑ ηₙ` and `ε = ∑ εₙ` as
  morphisms of complexes.
* `CochainComplex.dualCoevalOf`: the morphism of complexes `𝟙 ⟶ K ⊗ L` with a given degree-zero
  component `θ`.

## Main results

* `CochainComplex.coevSum_comp_d`: `(∑ ηₙ) ≫ d_{K ⊗ L} = 0`.
* `CochainComplex.d_comp_evalZero_of_isSignedMateDual`: `d_{L ⊗ K} ≫ (∑ εₙ) = 0`.
* `CochainComplex.exactPairingOfSignedMateDual`: `L` is a left dual of `K` in the monoidal category
  of complexes.
* `CochainComplex.exactPairingOfSignedMateDualOfLocallyFinite`: the same when `K` is bounded
  only after applying each member of a jointly faithful family of monoidal functors, with
  `η = ∑ ηₙ` a locally finite sum.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0FFV](https://stacks.math.columbia.edu/tag/0FFV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category Limits MonoidalCategory GradedObject
open CategoryTheory.GradedObject.Monoidal
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The right-dual structure that an exact pairing carries. -/
abbrev hasRightDual {X Y : C} (p : ExactPairing X Y) : HasRightDual X where
  rightDual := Y
  exact := p

variable {X Y X' Y' : C}

/-- **The mate of a morphism** for chosen duals of its source and target: `f^∨ : Y' ⟶ X'` for
`f : X ⟶ Y`, `X'` a dual of `X` and `Y'` a dual of `Y`. -/
noncomputable def mate (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) : Y' ⟶ X' :=
  @rightAdjointMate _ _ _ X Y (hasRightDual pX) (hasRightDual pY) f

/-- The coevaluation of the target pairing, contracted against the mate, is the coevaluation of
the source pairing contracted against the morphism. -/
lemma coevaluation_comp_mate (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    pY.coevaluation' ≫ Y ◁ mate pX pY f = pX.coevaluation' ≫ f ▷ X' :=
  @coevaluation_comp_rightAdjointMate _ _ _ X Y (hasRightDual pX) (hasRightDual pY) f

/-- The mate contracted against the evaluation of the source pairing is the morphism contracted
against the evaluation of the target pairing. -/
lemma mate_comp_evaluation (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y) :
    mate pX pY f ▷ X ≫ pX.evaluation' = Y' ◁ f ≫ pY.evaluation' :=
  @rightAdjointMate_comp_evaluation _ _ _ X Y (hasRightDual pX) (hasRightDual pY) f

/-- The mate of a composite is the composite of the mates, in the other order. -/
lemma comp_mate {Z Z' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y')
    (pZ : ExactPairing Z Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    mate pX pZ (f ≫ g) = mate pY pZ g ≫ mate pX pY f :=
  @comp_rightAdjointMate _ _ _ X Y Z (hasRightDual pX) (hasRightDual pY) (hasRightDual pZ) f g

/-- The mate of the zero morphism is zero. -/
@[simp]
lemma mate_zero [Preadditive C] [MonoidalPreadditive C]
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') : mate pX pY (0 : X ⟶ Y) = 0 := by
  simp [mate, rightAdjointMate]

/-- A tensor product with a zero factor on the left is a zero object. -/
lemma isZero_tensor_of_isZero_left [Preadditive C] [MonoidalPreadditive C] (X Y : C)
    (h : IsZero X) : IsZero (X ⊗ Y) :=
  (IsZero.iff_id_eq_zero _).2 <| by
    rw [← MonoidalCategory.id_whiskerRight X Y, h.eq_of_src (𝟙 X) 0,
      MonoidalPreadditive.zero_whiskerRight]

end CategoryTheory.ExactPairing

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (K L : CochainComplex C ℤ) (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- **The signed-transpose condition.**  The differential of `L` from degree `-(n+1)` to degree
`-n` is `(-1)^n` times the mate of the differential of `K` from degree `n` to degree `n+1`.  The
differential of `SheafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FP9] has this form. -/
def IsSignedMateDual : Prop :=
  ∀ n : ℤ, L.d (-(n + 1)) (-n) =
    (n.negOnePow : ℤˣ) • ExactPairing.mate (p n) (p (n + 1)) (K.d n (n + 1))

/-- The `(n+1, -n)` component of `ηₙ` followed by the differential of `K ⊗ L`. -/
noncomputable def coevD (n : ℤ) : 𝟙_ C ⟶ (K ⊗ L).X 1 :=
  (p n).coevaluation' ≫ K.d n (n + 1) ▷ L.X (-n) ≫
    HomologicalComplex.ιTensorObj K L (n + 1) (-n) 1 (by omega)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- In a degree where `K` vanishes, `ηₙ` vanishes, hence so does the component. -/
lemma coevD_eq_zero_of_isZero (n : ℤ) (h : IsZero (K.X n)) : coevD K L p n = 0 := by
  rw [coevD, (ExactPairing.isZero_tensor_of_isZero_left (K.X n) (L.X (-n)) h).eq_of_tgt
    (p n).coevaluation' 0, zero_comp]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- In a degree where the next term of `K` vanishes, the differential does, hence so does the
component. -/
lemma coevD_eq_zero_of_isZero_succ (n : ℤ) (h : IsZero (K.X (n + 1))) : coevD K L p n = 0 := by
  rw [coevD, h.eq_of_tgt (K.d n (n + 1)) 0, MonoidalPreadditive.zero_whiskerRight, zero_comp,
    comp_zero]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The `1 ⊗ d_L` term of `η_{m+1}` is the negative of the `d_K ⊗ 1` term of `ηₘ`, both on the
summand `(m+1, -m)`. -/
lemma coevD_shift (hd : IsSignedMateDual K L p) (n m b : ℤ)
    (hnm : m + 1 = n) (hb : b = -m) (hab : n + b = 1) :
    (p n).coevaluation' ≫ ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) b ≫
      HomologicalComplex.ιTensorObj K L n b 1 hab)) = - coevD K L p m := by
  subst hb
  subst hnm
  rw [hd m]
  simp only [units_smul_whiskerLeft, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [← assoc, ExactPairing.coevaluation_comp_mate (p m) (p (m + 1)) (K.d m (m + 1)), coevD,
    Int.negOnePow_succ]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The Koszul differential of `K ⊗ L` read on the summand `(n, -n)` of degree zero. -/
lemma ι_comp_d_zero_one (n : ℤ) :
    HomologicalComplex.ιTensorObj K L n (-n) 0 (by omega) ≫ (K ⊗ L).d 0 1 =
      (K.d n (n + 1) ▷ L.X (-n) ≫
          HomologicalComplex.ιTensorObj K L (n + 1) (-n) 1 (by omega)) +
        ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) (-n + 1) ≫
          HomologicalComplex.ιTensorObj K L n (-n + 1) 1 (by omega))) :=
  CochainComplex.ιTensorObj_comp_d K L n (-n) 0 1 (by omega) (by omega)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- **`η = ∑ ηₙ` commutes with the differentials.**  The sum of the degreewise coevaluations,
followed by the differential of `K ⊗ L` out of degree zero, vanishes. -/
lemma coevSum_comp_d (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hd : IsSignedMateDual K L p) :
    (∑ n ∈ s, (p n).coevaluation' ≫
        HomologicalComplex.ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1 = 0 := by
  have hsplit : (∑ n ∈ s, (p n).coevaluation' ≫
        HomologicalComplex.ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1 =
      (∑ n ∈ s, coevD K L p n) +
        ∑ n ∈ s, ((p n).coevaluation' ≫
          ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) (-n + 1) ≫
            HomologicalComplex.ιTensorObj K L n (-n + 1) 1 (by omega)))) := by
    rw [Preadditive.sum_comp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [assoc, ι_comp_d_zero_one K L n, Preadditive.comp_add, coevD]
  rw [hsplit]
  have hB : ∀ n : ℤ, ((p n).coevaluation' ≫
      ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) (-n + 1) ≫
        HomologicalComplex.ιTensorObj K L n (-n + 1) 1 (by omega)))) =
      - coevD K L p (n - 1) :=
    fun n => coevD_shift K L p hd n (n - 1) (-n + 1) (by omega) (by omega) (by omega)
  rw [Finset.sum_congr rfl (fun n (_ : n ∈ s) => hB n), Finset.sum_neg_distrib]
  have hA0 : ∀ n : ℤ, n ∉ s.filter (fun m => m + 1 ∈ s) → coevD K L p n = 0 := by
    intro n hn
    by_cases h : n ∈ s
    · refine coevD_eq_zero_of_isZero_succ K L p n (hbd (n + 1) ?_)
      simp only [Finset.mem_filter, h, true_and] at hn
      exact hn
    · exact coevD_eq_zero_of_isZero K L p n (hbd n h)
  have e1 : ∑ n ∈ s.filter (fun m => m + 1 ∈ s), coevD K L p n = ∑ n ∈ s, coevD K L p n :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => hA0 x hx)
  have hsub : s.filter (fun m => m + 1 ∈ s) ⊆ s.image (fun m => m - 1) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact Finset.mem_image.2 ⟨n + 1, hn.2, by omega⟩
  have e2 : ∑ n ∈ s.filter (fun m => m + 1 ∈ s), coevD K L p n =
      ∑ n ∈ s.image (fun m => m - 1), coevD K L p n :=
    Finset.sum_subset hsub (fun x _ hx => hA0 x hx)
  have e3 : ∑ n ∈ s.image (fun m => m - 1), coevD K L p n =
      ∑ n ∈ s, coevD K L p (n - 1) :=
    Finset.sum_image (fun x _ y _ h => by omega)
  rw [← e3, ← e2, e1, add_neg_cancel]

omit [HasZeroObject C]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The evaluation in degree zero reads off the degreewise evaluation on the summand `(-b, b)`. -/
lemma ι_comp_totalEval (b : ℤ) (h : -b + b = 0) :
    HomologicalComplex.ιTensorObj L K (-b) b 0 h ≫
        GradedObject.Monoidal.totalEval K.X L.X p = (p b).evaluation' := by
  rw [GradedObject.Monoidal.totalEval]
  refine Eq.trans (GradedObject.Monoidal.ι_tensorObjDesc
    (X₁ := L.X) (X₂ := K.X) _ (-b) b h) ?_
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] [HasZeroObject C]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), X₁.HasGoodTensor₁₂Tensor X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), X₁.HasGoodTensorTensor₂₃ X₂ X₃]
  [∀ (X₁ : C), PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)] in
/-- The same, with a differential `L^A ⟶ L^c` of `L` prefixed, for any `c = -b`. -/
lemma d_ι_comp_totalEval (b c A : ℤ) (hc : c = -b) (h : c + b = 0) :
    (L.d A c ▷ K.X b) ≫ HomologicalComplex.ιTensorObj L K c b 0 h ≫
        GradedObject.Monoidal.totalEval K.X L.X p =
      (L.d A (-b) ▷ K.X b) ≫ (p b).evaluation' := by
  subst hc
  rw [ι_comp_totalEval K L p b h]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The summed evaluation `evalZero` reads off the degreewise evaluation on the summand `(-b, b)`
of `(L ⊗ K)^0`. -/
lemma ι_comp_evalZero (b : ℤ) (h : -b + b = 0) :
    HomologicalComplex.ιTensorObj L K (-b) b 0 h ≫ evalZero K L p = (p b).evaluation' :=
  ι_comp_totalEval K L p b h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The same, with a differential `L^A ⟶ L^c` of `L` prefixed, for any `c = -b`. -/
lemma d_ι_comp_evalZero (b c A : ℤ) (hc : c = -b) (h : c + b = 0) :
    (L.d A c ▷ K.X b) ≫ HomologicalComplex.ιTensorObj L K c b 0 h ≫ evalZero K L p =
      (L.d A (-b) ▷ K.X b) ≫ (p b).evaluation' :=
  d_ι_comp_totalEval K L p b c A hc h

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- On the summand `(-(n+1), n)` of `(L ⊗ K)^{-1}`, the differential of `L ⊗ K` followed by the
summed evaluation vanishes: its `d_L ⊗ 1` term and its `1 ⊗ d_K` term are opposite. -/
lemma evalSummand (hd : IsSignedMateDual K L p) (n a : ℤ)
    (ha : a = -(n + 1)) (hab : a + n = -1) :
    HomologicalComplex.ιTensorObj L K a n (-1) hab ≫
      ((L ⊗ K).d (-1) 0 ≫ evalZero K L p) = 0 := by
  subst ha
  rw [← assoc, CochainComplex.ιTensorObj_comp_d L K (-(n + 1)) n (-1) 0 hab (by omega),
    Preadditive.add_comp, assoc, Linear.units_smul_comp, assoc,
    d_ι_comp_evalZero K L p n (-(n + 1) + 1) (-(n + 1)) (by omega) (by omega),
    ι_comp_evalZero K L p (n + 1) (by omega)]
  rw [hd n, units_smul_whiskerRight, Linear.units_smul_comp,
    ExactPairing.mate_comp_evaluation (p n) (p (n + 1)) (K.d n (n + 1)),
    show (-(n + 1) : ℤ).negOnePow = -(n.negOnePow) from by
      rw [Int.negOnePow_neg, Int.negOnePow_succ]]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- **`ε = ∑ εₙ` commutes with the differentials.**  The differential of `L ⊗ K` into degree zero,
followed by the assembled evaluation, vanishes. -/
lemma d_comp_evalZero_of_isSignedMateDual (hd : IsSignedMateDual K L p) :
    (L ⊗ K).d (-1) 0 ≫ evalZero K L p = 0 :=
  GradedObject.Monoidal.tensorObj_ext _ _ (fun a b hab =>
    (evalSummand K L p hd b a (by omega) hab).trans comp_zero.symm)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The total coevaluation `∑_{n ∈ s} ηₙ` followed by the differential of `K ⊗ L` out of degree
zero vanishes. -/
lemma totalCoev_comp_d_of_isSignedMateDual (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hd : IsSignedMateDual K L p) :
    GradedObject.Monoidal.totalCoev K.X L.X s p ≫ (K ⊗ L).d 0 1 = 0 :=
  coevSum_comp_d K L p s hbd hd

/-- The degree-zero component of the graded coevaluation followed by the differential of `K ⊗ L`
out of degree zero vanishes. -/
lemma gradedCoev_comp_d (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hd : IsSignedMateDual K L p) :
    GradedObject.Monoidal.gradedCoev K.X L.X s p 0 ≫ (K ⊗ L).d 0 1 = 0 :=
  Eq.trans
    (congrArg (fun φ => φ ≫ (K ⊗ L).d 0 1)
      (GradedObject.Monoidal.gradedCoev_zero K.X L.X s p))
    (Eq.trans (assoc _ _ _)
      (Eq.trans (congrArg (fun φ => GradedObject.Monoidal.tensorUnit₀.hom ≫ φ)
        (totalCoev_comp_d_of_isSignedMateDual K L p s hbd hd)) comp_zero))

/-- The differential of `L ⊗ K` into degree zero followed by the degree-zero component of the
graded evaluation vanishes. -/
lemma d_comp_gradedEval (hd : IsSignedMateDual K L p) :
    (L ⊗ K).d (-1) 0 ≫ GradedObject.Monoidal.gradedEval K.X L.X p 0 = 0 :=
  Eq.trans
    (congrArg (fun φ => (L ⊗ K).d (-1) 0 ≫ φ)
      (GradedObject.Monoidal.gradedEval_zero K.X L.X p))
    (Eq.trans (assoc _ _ _).symm
      (Eq.trans (congrArg (fun φ => φ ≫ GradedObject.Monoidal.tensorUnit₀.inv)
        (d_comp_evalZero_of_isSignedMateDual K L p hd)) zero_comp))

/-- The degree-`i` component of the candidate coevaluation of complexes. -/
noncomputable def dualCoevX (s : Finset ℤ) (i : ℤ) :
    (𝟙_ (CochainComplex C ℤ)).X i ⟶ (K ⊗ L).X i :=
  (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
    GradedObject.Monoidal.gradedCoev K.X L.X s p i

/-- The degree-`i` component of the candidate evaluation of complexes. -/
noncomputable def dualEvalX (i : ℤ) : (L ⊗ K).X i ⟶ (𝟙_ (CochainComplex C ℤ)).X i :=
  GradedObject.Monoidal.gradedEval K.X L.X p i ≫
    (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom i

/-- The degree-zero component of the candidate coevaluation of complexes followed by the
differential of `K ⊗ L` out of degree zero vanishes. -/
lemma dualCoevX_zero_comp_d (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hd : IsSignedMateDual K L p) : dualCoevX K L p s 0 ≫ (K ⊗ L).d 0 1 = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (CategoryStruct.comp
        ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv 0))
      (gradedCoev_comp_d K L p s hbd hd)).trans comp_zero)

/-- The differential of `L ⊗ K` into degree zero followed by the degree-zero component of the
candidate evaluation of complexes vanishes. -/
lemma d_comp_dualEvalX_zero (hd : IsSignedMateDual K L p) :
    (L ⊗ K).d (-1) 0 ≫ dualEvalX K L p 0 = 0 :=
  (Category.assoc _ _ _).symm.trans
    ((eq_whisker (d_comp_gradedEval K L p hd)
      ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom 0)).trans zero_comp)

/-- **`η = ∑ ηₙ` as a morphism of complexes** `𝟙 ⟶ K ⊗ L`, for `K` vanishing outside `s` and the
differential of `L` the signed transpose of that of `K`. -/
noncomputable def dualCoeval (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hd : IsSignedMateDual K L p) : 𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ L where
  f i := dualCoevX K L p s i
  comm' i j hij := by
    rw [show (𝟙_ (CochainComplex C ℤ)).d i j = 0 from HomologicalComplex.single_obj_d .., zero_comp]
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by simpa using hij.symm
      exact dualCoevX_zero_comp_d K L p s hbd hd
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) i
        hi).eq_of_src _ _

/-- **`ε = ∑ εₙ` as a morphism of complexes** `L ⊗ K ⟶ 𝟙`, for the differential of `L` the signed
transpose of that of `K`. -/
noncomputable def dualEval (hd : IsSignedMateDual K L p) :
    L ⊗ K ⟶ 𝟙_ (CochainComplex C ℤ) where
  f i := dualEvalX K L p i
  comm' i j hij := by
    rw [show (𝟙_ (CochainComplex C ℤ)).d i j = 0 from HomologicalComplex.single_obj_d .., comp_zero]
    by_cases hj : j = 0
    · subst hj
      obtain rfl : i = -1 := by
        have := hij
        simp only [ComplexShape.up_Rel] at this
        omega
      exact (d_comp_dualEvalX_zero K L p hd).symm
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) j
        hj).eq_of_tgt _ _

/-- **Degreewise duals with the signed-transpose differential assemble into a left dual in the
monoidal category of complexes.**  `L^{-n}` is a dual of `K^n` in every degree, `K` vanishes
outside the finite set `s`, and the differential of `L` is the signed transpose of that of `K`;
then `η = ∑ ηₙ` and `ε = ∑ εₙ` are morphisms of complexes and exhibit `L` as a left dual of `K`
in `CochainComplex C ℤ`. -/
@[instance_reducible]
noncomputable def exactPairingOfSignedMateDual (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m)) (hd : IsSignedMateDual K L p) :
    ExactPairing K L :=
  CochainComplex.exactPairingOfDegreewiseOfChainMaps K L s p hbd
    (dualCoeval K L p s hbd hd) (dualEval K L p hd)
    (by
      funext i
      change (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
          GradedObject.Monoidal.gradedCoev K.X L.X s p i =
        (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
          (GradedObject.Monoidal.gradedCoev K.X L.X s p i ≫ 𝟙 _)
      exact (whisker_eq ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i)
        (Category.comp_id (GradedObject.Monoidal.gradedCoev K.X L.X s p i))).symm)
    (by
      funext i
      change GradedObject.Monoidal.gradedEval K.X L.X p i ≫
          (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom i =
        𝟙 _ ≫ (GradedObject.Monoidal.gradedEval K.X L.X p i ≫
          (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom i)
      exact (Category.id_comp _).symm)

section LocallyFinite

/-! ### Locally finite sums

The same assembly when `K` is bounded only after applying each member of a jointly faithful
family of monoidal functors: the coevaluation is then any `θ : 𝟙 ⟶ (K ⊗ L)^0` carried by each
functor to the image of the finite sum over the degrees it does not kill. -/

universe w' v' u'

variable {ι : Type w'} {D : ι → Type u'} [∀ i, Category.{v'} (D i)]
  [∀ i, MonoidalCategory (D i)] [∀ i, Preadditive (D i)] [∀ i, MonoidalPreadditive (D i)]
  (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal] [∀ i, (F i).Additive]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- **`∑ ηₙ` commutes with the differentials after applying a functor that bounds `K`.**  If
`Fᵢ` kills `K^m` for every `m` outside the finite set `s`, the image under `Fᵢ` of the sum
`∑_{n ∈ s} ηₙ` followed by the differential of `K ⊗ L` out of degree zero vanishes. -/
lemma map_coevSum_comp_d (i : ι) (s : Finset ℤ) (hbd : ∀ m : ℤ, m ∉ s → IsZero ((F i).obj (K.X m)))
    (hd : IsSignedMateDual K L p) :
    (F i).map ((∑ n ∈ s, (p n).coevaluation' ≫
        HomologicalComplex.ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1) = 0 := by
  have hsplit : (∑ n ∈ s, (p n).coevaluation' ≫
        HomologicalComplex.ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1 =
      (∑ n ∈ s, coevD K L p n) +
        ∑ n ∈ s, ((p n).coevaluation' ≫
          ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) (-n + 1) ≫
            HomologicalComplex.ιTensorObj K L n (-n + 1) 1 (by omega)))) := by
    rw [Preadditive.sum_comp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [assoc, ι_comp_d_zero_one K L n, Preadditive.comp_add, coevD]
  have hB : ∀ n : ℤ, ((p n).coevaluation' ≫
      ((n.negOnePow : ℤˣ) • (K.X n ◁ L.d (-n) (-n + 1) ≫
        HomologicalComplex.ιTensorObj K L n (-n + 1) 1 (by omega)))) =
      - coevD K L p (n - 1) :=
    fun n => coevD_shift K L p hd n (n - 1) (-n + 1) (by omega) (by omega) (by omega)
  rw [hsplit, Finset.sum_congr rfl (fun n (_ : n ∈ s) => hB n), Finset.sum_neg_distrib,
    Functor.map_add, Functor.map_neg, Functor.map_sum, Functor.map_sum]
  have hA0 : ∀ n : ℤ, n ∉ s.filter (fun m => m + 1 ∈ s) → (F i).map (coevD K L p n) = 0 := by
    intro n hn
    by_cases h : n ∈ s
    · simp only [Finset.mem_filter, h, true_and] at hn
      rw [coevD, Functor.map_comp, Functor.map_comp, Functor.Monoidal.map_whiskerRight,
        (hbd (n + 1) hn).eq_of_tgt ((F i).map (K.d n (n + 1))) 0,
        MonoidalPreadditive.zero_whiskerRight]
      simp
    · rw [coevD, Functor.map_comp,
        (GradedObject.Monoidal.isZero_map_tensor_of_isZero_map_left F i (K.X n) (L.X (-n))
          (hbd n h)).eq_of_tgt ((F i).map (p n).coevaluation') 0, zero_comp]
  have e1 : ∑ n ∈ s.filter (fun m => m + 1 ∈ s), (F i).map (coevD K L p n) =
      ∑ n ∈ s, (F i).map (coevD K L p n) :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => hA0 x hx)
  have hsub : s.filter (fun m => m + 1 ∈ s) ⊆ s.image (fun m => m - 1) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact Finset.mem_image.2 ⟨n + 1, hn.2, by omega⟩
  have e2 : ∑ n ∈ s.filter (fun m => m + 1 ∈ s), (F i).map (coevD K L p n) =
      ∑ n ∈ s.image (fun m => m - 1), (F i).map (coevD K L p n) :=
    Finset.sum_subset hsub (fun x _ hx => hA0 x hx)
  have e3 : ∑ n ∈ s.image (fun m => m - 1), (F i).map (coevD K L p n) =
      ∑ n ∈ s, (F i).map (coevD K L p (n - 1)) :=
    Finset.sum_image (fun x _ y _ h => by omega)
  rw [← e3, ← e2, e1, add_neg_cancel]

variable (hF : JointlyFaithful F) (t : ι → Finset ℤ)
  (ht : ∀ i, ∀ n, n ∉ t i → IsZero ((F i).obj (K.X n)))
  (θ : 𝟙_ C ⟶ (K ⊗ L).X 0)
  (hθ : ∀ i, (F i).map θ = (F i).map (GradedObject.Monoidal.totalCoev K.X L.X (t i) p))

include hF ht hθ in
omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- **A locally finite sum `θ` of the `ηₙ` commutes with the differentials.** -/
lemma comp_d_of_locallyFinite (hd : IsSignedMateDual K L p) : θ ≫ (K ⊗ L).d 0 1 = 0 :=
  hF.map_injective fun i =>
    calc (F i).map (θ ≫ (K ⊗ L).d 0 1) = (F i).map θ ≫ (F i).map ((K ⊗ L).d 0 1) :=
          (F i).map_comp _ _
      _ = (F i).map (GradedObject.Monoidal.totalCoev K.X L.X (t i) p) ≫
            (F i).map ((K ⊗ L).d 0 1) := congrArg (· ≫ (F i).map ((K ⊗ L).d 0 1)) (hθ i)
      _ = (F i).map (GradedObject.Monoidal.totalCoev K.X L.X (t i) p ≫ (K ⊗ L).d 0 1) :=
          ((F i).map_comp _ _).symm
      _ = 0 := map_coevSum_comp_d K L p F i (t i) (ht i) hd
      _ = (F i).map 0 := ((F i).map_zero _ _).symm

/-- `gradedCoevOf θ` followed by the differential out of degree zero vanishes when `θ` followed by
it does. -/
lemma gradedCoevOf_comp_d (hθd : θ ≫ (K ⊗ L).d 0 1 = 0) :
    GradedObject.Monoidal.gradedCoevOf K.X L.X θ 0 ≫ (K ⊗ L).d 0 1 = 0 :=
  Eq.trans
    (congrArg (fun φ => φ ≫ (K ⊗ L).d 0 1) (GradedObject.Monoidal.gradedCoevOf_zero K.X L.X θ))
    (Eq.trans (assoc _ _ _)
      (Eq.trans (congrArg (fun φ => GradedObject.Monoidal.tensorUnit₀.hom ≫ φ) hθd) comp_zero))

/-- The coevaluation of complexes whose degree-zero component is `θ`. -/
noncomputable def dualCoevalOf (hθd : θ ≫ (K ⊗ L).d 0 1 = 0) : 𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ L where
  f i := (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
    GradedObject.Monoidal.gradedCoevOf K.X L.X θ i
  comm' i j hij := by
    rw [show (𝟙_ (CochainComplex C ℤ)).d i j = 0 from HomologicalComplex.single_obj_d .., zero_comp]
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by simpa using hij.symm
      exact (Category.assoc _ _ _).trans
        ((congrArg (CategoryStruct.comp
            ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv 0))
          (gradedCoevOf_comp_d K L θ hθd)).trans comp_zero)
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) i
        hi).eq_of_src _ _

/-- **Degreewise duals with the signed-transpose differential assemble into a left dual in the
monoidal category of complexes, along a locally finite sum.**  Let `Fᵢ` be a jointly faithful
family of additive monoidal functors out of `C`, each killing all but the finitely many terms
`K^n`, `n ∈ tᵢ`; let `L^{-n}` be a dual of `K^n` in every degree, with the differential of `L`
the signed transpose of that of `K`.  If `θ : 𝟙 ⟶ (K ⊗ L)^0` is carried by each `Fᵢ` to the
image of `∑_{n ∈ tᵢ} ηₙ`, then `θ` and `ε = ∑ εₙ` are morphisms of complexes exhibiting `L` as a
left dual of `K` in `CochainComplex C ℤ`. -/
@[instance_reducible]
noncomputable def exactPairingOfSignedMateDualOfLocallyFinite (hd : IsSignedMateDual K L p) :
    ExactPairing K L :=
  letI := forgetMonoidal (C := C)
  letI : ExactPairing ((forgetGraded (C := C)).obj K) ((forgetGraded (C := C)).obj L) :=
    GradedObject.Monoidal.exactPairingOfLocallyFinite (toGradedObject K) (toGradedObject L) p
      F hF t ht θ hθ
  ExactPairing.ofFaithful (forgetGraded (C := C)) (dualEval K L p hd)
    (dualCoevalOf K L θ (comp_d_of_locallyFinite K L p F hF t ht θ hθ hd))
    (by
      funext i
      change GradedObject.Monoidal.gradedEval K.X L.X p i ≫
          (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom i =
        𝟙 _ ≫ (GradedObject.Monoidal.gradedEval K.X L.X p i ≫
          (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom i)
      exact (Category.id_comp _).symm)
    (by
      funext i
      change (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
          GradedObject.Monoidal.gradedCoevOf K.X L.X θ i =
        (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i ≫
          (GradedObject.Monoidal.gradedCoevOf K.X L.X θ i ≫ 𝟙 _)
      exact (whisker_eq ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv i)
        (Category.comp_id (GradedObject.Monoidal.gradedCoevOf K.X L.X θ i))).symm)

/-- The coevaluation of `exactPairingOfSignedMateDualOfLocallyFinite` is `θ` in degree zero. -/
lemma coevaluation_exactPairingOfSignedMateDualOfLocallyFinite (hd : IsSignedMateDual K L p) :
    letI := exactPairingOfSignedMateDualOfLocallyFinite K L p F hF t ht θ hθ hd
    (η_ K L).f 0 = (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫
      GradedObject.Monoidal.tensorUnit₀.hom ≫ θ := by
  change (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫
      GradedObject.Monoidal.gradedCoevOf K.X L.X θ 0 = _
  exact whisker_eq _ (GradedObject.Monoidal.gradedCoevOf_zero K.X L.X θ)

/-- The evaluation of `exactPairingOfSignedMateDualOfLocallyFinite` is `ε = ∑ εₙ`. -/
lemma evaluation_exactPairingOfSignedMateDualOfLocallyFinite (hd : IsSignedMateDual K L p) :
    letI := exactPairingOfSignedMateDualOfLocallyFinite K L p F hF t ht θ hθ hd
    ε_ K L = dualEval K L p hd :=
  rfl

include hF ht hθ in
/-- **The coevaluation of `exactPairingOfSignedMateDualOfLocallyFinite` is `∑ ηₙ`**: its
degree-zero component on the summand `(n, -n)` of `(K ⊗ L)^0` is `ηₙ`. -/
lemma coevaluation_comp_πTensorObj_exactPairingOfSignedMateDualOfLocallyFinite
    (hd : IsSignedMateDual K L p) (n : ℤ) :
    letI := exactPairingOfSignedMateDualOfLocallyFinite K L p F hF t ht θ hθ hd
    (η_ K L).f 0 ≫ GradedObject.Monoidal.πTensorObj K.X L.X n (-n) 0 (add_neg_cancel n) =
      ((HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫
        GradedObject.Monoidal.tensorUnit₀.hom) ≫ (p n).coevaluation' := by
  rw [coevaluation_exactPairingOfSignedMateDualOfLocallyFinite]
  exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (GradedObject.Monoidal.comp_πTensorObj_of_locallyFinite K.X L.X p F hF t ht θ
      hθ n)))).trans (Category.assoc _ _ _).symm)

/-- **The evaluation of `exactPairingOfSignedMateDualOfLocallyFinite` is `∑ εₙ`**: its
degree-zero component on the summand `(-n, n)` of `(L ⊗ K)^0` is `εₙ`. -/
lemma ιTensorObj_comp_evaluation_exactPairingOfSignedMateDualOfLocallyFinite
    (hd : IsSignedMateDual K L p) (n : ℤ) :
    letI := exactPairingOfSignedMateDualOfLocallyFinite K L p F hF t ht θ hθ hd
    HomologicalComplex.ιTensorObj L K (-n) n 0 (neg_add_cancel n) ≫ (ε_ K L).f 0 =
      (p n).evaluation' ≫ GradedObject.Monoidal.tensorUnit₀.inv ≫
        (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom 0 := by
  change HomologicalComplex.ιTensorObj L K (-n) n 0 (neg_add_cancel n) ≫
      (GradedObject.Monoidal.gradedEval K.X L.X p 0 ≫
        (HomologicalComplex.tensorUnitIso C (ComplexShape.up ℤ)).hom 0) = _
  rw [GradedObject.Monoidal.gradedEval_zero]
  exact (whisker_eq _ (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
    (eq_whisker (ι_comp_totalEval K L p n (neg_add_cancel n)) _))

end LocallyFinite

end CochainComplex

end
