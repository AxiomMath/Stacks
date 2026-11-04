module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.Algebra.Homology.DegreewiseLeftDual
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.CategoryTheory.Graded.DualAssembly
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assembling a dual complex out of degreewise duals

Let `C` be a monoidal preadditive category carrying the coproducts that make both
`GradedObject ℤ C` and `CochainComplex C ℤ` monoidal, the tensor product of complexes being the
total complex of the degreewise tensor product. Let `K` be a cochain complex, let `L` be a
second one, and suppose that in every degree `n` the term `L^{-n}` is a dual of `K^n`, with
coevaluation `ηₙ : 𝟙 ⟶ K^n ⊗ L^{-n}` and evaluation `εₙ : L^{-n} ⊗ K^n ⟶ 𝟙`. If both complexes
vanish outside a finite set of degrees, then the sums `η = ∑ ηₙ` and `ε = ∑ εₙ` exhibit `L` as a
dual of `K` — provided they are morphisms of *complexes*, which is one linear condition on the
differentials in each degree. The same holds without boundedness, given a coevaluation with
component `ηₙ` on each summand `K^n ⊗ L^{-n}` and the separation of the degree-one part of `K ⊗ L`.

## Main definitions

* `CochainComplex.coevaluationHom`: the sum `η = ∑ ηₙ` as a morphism of complexes
  `𝟙 ⟶ K ⊗ L`.
* `CochainComplex.evaluationHom`: the sum `ε = ∑ εₙ` as a morphism of complexes
  `L ⊗ K ⟶ 𝟙`.
* `CochainComplex.exactPairingOfDegreewise`: the triangle identities for `η` and `ε`, packaged as
  an `ExactPairing K L` in the monoidal category of complexes.
* `CochainComplex.IsSignedTranspose`: the differential of `L` is the signed transpose
  `d_L^{-n-1} = (-1)^n · (d_K^n)ᘁ` of the differential of `K`.
* `CochainComplex.exactPairingOfSignedTranspose`: the same conclusion from the signed-transpose
  condition.
* `CochainComplex.IsSeparatedDegOne`: morphisms into the degree-one part of `K ⊗ L` are
  determined by their components.
* `CochainComplex.exactPairingOfComponents` and
  `CochainComplex.exactPairingOfSignedTransposeOfComponents`: the same two conclusions with no
  boundedness of the complex, from a coevaluation whose component on each summand
  `K^n ⊗ L^{-n}` is `ηₙ` (`CategoryTheory.GradedObject.Monoidal.IsAssembledCoev`) together with
  `IsSeparatedDegOne`.

## Main results

* `CochainComplex.ιTensorObj_d_koszul`: the restriction of the differential of a tensor product of
  complexes to the summand `K^a ⊗ L^b` is `d_K ▷ L^b + (-1)^a • (K^a ◁ d_L)`.
* `CochainComplex.totalCoev_comp_d`: the sum `∑ ηₙ` is a cocycle.
* `CochainComplex.d_comp_evalZero`: the sum `∑ εₙ` kills the incoming differential.
* `CochainComplex.coevaluationHom_f_zero` and `CochainComplex.ι_evaluationHom_f_zero`: the
  assembled morphisms are the sums of the degreewise ones.
* `CochainComplex.dZeroOne_comp_πTensorObj`: the components of the differential out of the
  degree-zero part of `K ⊗ L`.
* `CochainComplex.isCoevaluationCocycle_of_signedTranspose` and
  `CochainComplex.isEvaluationCocycle_of_signedTranspose`: the signed transpose makes the two
  sums chain maps.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject
open CategoryTheory.GradedObject.Monoidal
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The restriction of the differential of a tensor product of cochain complexes to the summand
`K^a ⊗ L^b`: the first factor is differentiated with sign `+1`, the second with sign `(-1)^a`. -/
@[sga "4 XVII 1.1.10"]
theorem ιTensorObj_d_koszul (K L : CochainComplex C ℤ) (a b j a' b' j' : ℤ)
    (h : a + b = j) (ha : a + 1 = a') (hb : b + 1 = b') (hj : j + 1 = j') :
    ιTensorObj K L a b j h ≫ (K ⊗ L).d j j' =
      (K.d a a' ▷ L.X b) ≫ ιTensorObj K L a' b j' (by omega) +
        a.negOnePow • ((K.X a ◁ L.d b b') ≫ ιTensorObj K L a b' j' (by omega)) := by
  subst ha hb hj
  have hd : (K ⊗ L).d j (j + 1) =
      mapBifunctor.D₁ K L (curriedTensor C) (ComplexShape.up ℤ) j (j + 1) +
      mapBifunctor.D₂ K L (curriedTensor C) (ComplexShape.up ℤ) j (j + 1) :=
    mapBifunctor.d_eq K L (curriedTensor C) (ComplexShape.up ℤ) j (j + 1)
  rw [hd, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl)
      b (j + 1) (by change a + 1 + b = j + 1; omega),
    mapBifunctor.d₂_eq _ _ _ _ a (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl)
      (j + 1) (by change a + (b + 1) = j + 1; omega)]
  show (1 : ℤˣ) • _ + a.negOnePow • _ = _
  rw [one_smul]
  rfl

section

variable (K L : CochainComplex C ℤ) (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- The chain-map condition on the degreewise coevaluations: in each degree the two ways the
differential of `K ⊗ L` can reach the summand `K^{n+1} ⊗ L^{-n}` from the coevaluations cancel.
-/
abbrev IsCoevaluationCocycle : Prop :=
  ∀ n : ℤ, (p n).coevaluation' ≫ (K.d n (n + 1) ▷ L.X (-n)) +
    ((n + 1).negOnePow : ℤˣ) •
      ((p (n + 1)).coevaluation' ≫ (K.X (n + 1) ◁ L.d (-(n + 1)) (-n))) = 0

/-- The chain-map condition on the degreewise evaluations: in each degree the two ways the
summand `L^{-n-1} ⊗ K^n` of degree `-1` can be differentiated into the degree-zero part cancel
against the evaluations. -/
abbrev IsEvaluationCocycle : Prop :=
  ∀ n : ℤ, (L.d (-(n + 1)) (-n) ▷ K.X n) ≫ (p n).evaluation' +
    ((n + 1).negOnePow : ℤˣ) •
      ((L.X (-(n + 1)) ◁ K.d n (n + 1)) ≫ (p (n + 1)).evaluation') = 0

/-- The part of the differential applied to `ηₙ` that differentiates the first factor. -/
noncomputable def coevD₁ (n : ℤ) : 𝟙_ C ⟶ (K ⊗ L).X 1 :=
  (p n).coevaluation' ≫ (K.d n (n + 1) ▷ L.X (-n)) ≫ ιTensorObj K L (n + 1) (-n) 1 (by omega)

/-- The part of the differential applied to `ηₙ` that differentiates the second factor, landing
in the summand indexed by `(n, -m)` for `m + 1 = n`. -/
noncomputable def coevD₂ (n m : ℤ) (h : m + 1 = n) : 𝟙_ C ⟶ (K ⊗ L).X 1 :=
  (n.negOnePow : ℤˣ) • ((p n).coevaluation' ≫ (K.X n ◁ L.d (-n) (-m)) ≫
    ιTensorObj K L n (-m) 1 (by omega))

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The second-factor term does not depend on which proof of `m + 1 = n` names its summand. -/
theorem coevD₂_congr (n m m' : ℤ) (h : m + 1 = n) (h' : m' + 1 = n) :
    coevD₂ K L p n m h = coevD₂ K L p n m' h' := by
  obtain rfl : m = m' := by omega
  rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The differential applied to the `n`-th degreewise coevaluation splits into its two
summands. -/
theorem coev_ι_comp_d (n : ℤ) :
    (p n).coevaluation' ≫ ιTensorObj K L n (-n) 0 (by omega) ≫ (K ⊗ L).d 0 1 =
      coevD₁ K L p n + coevD₂ K L p n (n - 1) (by omega) := by
  rw [ιTensorObj_d_koszul K L n (-n) 0 (n + 1) (-(n - 1)) 1 (by omega) rfl (by omega) (by omega),
    Preadditive.comp_add, Linear.comp_units_smul, coevD₁, coevD₂]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Outside the support of `K` the second-factor term vanishes, the coevaluation landing in a
zero object. -/
theorem coevD₂_eq_zero_of_isZero_X {n m : ℤ} {h : m + 1 = n} (hz : IsZero (K.X n)) :
    coevD₂ K L p n m h = 0 := by
  rw [coevD₂, show (p n).coevaluation' = 0 from
    (HomologicalComplex.Monoidal.isZero_tensorObj_of_isZero_left
      (E := C) hz (L.X (-n))).eq_of_tgt _ _, zero_comp, smul_zero]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Outside the support of the dual the second-factor term vanishes, the differential of `L`
landing in a zero object. -/
theorem coevD₂_eq_zero_of_isZero_dual {n m : ℤ} {h : m + 1 = n}
    (hz : IsZero (L.X (-m))) : coevD₂ K L p n m h = 0 := by
  rw [coevD₂, show L.d (-n) (-m) = 0 from hz.eq_of_tgt _ _,
    MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero, smul_zero]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The chain-map condition, read on the summand `K^{n+1} ⊗ L^{-n}` of degree one. -/
theorem coevD₁_add_coevD₂_succ (hη : IsCoevaluationCocycle K L p) (n : ℤ) :
    coevD₁ K L p n + coevD₂ K L p (n + 1) n (by omega) = 0 := by
  rw [coevD₁, coevD₂, ← Category.assoc, ← Category.assoc, ← Linear.units_smul_comp,
    ← Preadditive.add_comp, hη n, zero_comp]

variable (s : Finset ℤ)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Under the chain-map condition `hη`, the degree-zero coevaluation `∑ ηₙ` assembled from the
degreewise ones is killed by the differential of `K ⊗ L`. -/
theorem totalCoev_comp_d
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (hL : ∀ m, m ∉ s → IsZero (L.X (-m)))
    (hη : IsCoevaluationCocycle K L p) (j : ℤ) :
    totalCoev K.X L.X s p ≫ (K ⊗ L).d 0 j = 0 := by
  classical
  by_cases hj : (ComplexShape.up ℤ).Rel 0 j
  swap
  · exact (congrArg (fun x => totalCoev K.X L.X s p ≫ x)
      ((K ⊗ L).shape 0 j hj)).trans comp_zero
  have hj' : (0 : ℤ) + 1 = j := hj
  obtain rfl : j = 1 := by omega
  have expand : totalCoev K.X L.X s p ≫ (K ⊗ L).d 0 1 =
      ∑ n ∈ s, ((p n).coevaluation' ≫ ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1 :=
    Preadditive.sum_comp s _ _
  have step : ∀ n ∈ s,
      ((p n).coevaluation' ≫ ιTensorObj K L n (-n) 0 (by omega)) ≫ (K ⊗ L).d 0 1 =
        coevD₁ K L p n + coevD₂ K L p n (n - 1) (by omega) :=
    fun n _ => (Category.assoc _ _ _).trans (coev_ι_comp_d K L p n)
  have h1 : ∑ n ∈ s, coevD₂ K L p n (n - 1) (by omega) =
      ∑ n ∈ s ∪ s.image (· + 1), coevD₂ K L p n (n - 1) (by omega) :=
    Finset.sum_subset Finset.subset_union_left fun x _ hx =>
      coevD₂_eq_zero_of_isZero_X K L p (hK x hx)
  have h2 : ∑ n ∈ s.image (· + 1), coevD₂ K L p n (n - 1) (by omega) =
      ∑ n ∈ s ∪ s.image (· + 1), coevD₂ K L p n (n - 1) (by omega) :=
    Finset.sum_subset Finset.subset_union_right fun x _ hx =>
      coevD₂_eq_zero_of_isZero_dual K L p
        (hL (x - 1) fun hm => hx (Finset.mem_image.2 ⟨x - 1, hm, by omega⟩))
  have key : ∑ n ∈ s, coevD₂ K L p n (n - 1) (by omega) =
      ∑ n ∈ s, coevD₂ K L p (n + 1) n (by omega) := by
    rw [h1, ← h2, Finset.sum_image (by
      intro x _ y _ hxy
      have h' : x + 1 = y + 1 := hxy
      omega)]
    exact Finset.sum_congr rfl fun x _ => coevD₂_congr K L p (x + 1) _ _ _ _
  refine expand.trans ?_
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, key, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun n _ => coevD₁_add_coevD₂_succ K L p hη n

/-- A morphism `𝟙 ⟶ (K ⊗ L)^0` killed by the differential, as a morphism of complexes
`𝟙 ⟶ K ⊗ L`. It is concentrated in degree zero, where it is the given morphism read through the
identification of the unit of complexes with the unit of graded objects. -/
noncomputable def coevaluationHomOf (coev : 𝟙_ C ⟶ tensorObj K.X L.X 0)
    (hd : ∀ j, coev ≫ (K ⊗ L).d 0 j = 0) :
    𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ L where
  f j := (tensorUnitIso C (ComplexShape.up ℤ)).inv j ≫ gradedCoevOf K.X L.X coev j
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [show (𝟙_ (CochainComplex C ℤ)).d i (i + 1) = 0 from
      single_obj_d (ComplexShape.up ℤ) 0 (𝟙_ C) i (i + 1), zero_comp]
    by_cases hi : i = 0
    · subst hi
      have h0 : gradedCoevOf K.X L.X coev 0 ≫ (K ⊗ L).d 0 (0 + 1) = 0 := by
        rw [gradedCoevOf_zero]
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun x => tensorUnit₀.hom ≫ x) (hd (0 + 1))).trans comp_zero)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun x => (tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫ x) h0).trans
          comp_zero)
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) i hi).eq_of_src _ _

/-- The summed coevaluation `η = ∑ ηₙ`, as a morphism of complexes. It is concentrated in degree
zero, where it is the sum of the degreewise coevaluations read through the identification of the
unit of complexes with the unit of graded objects. -/
noncomputable def coevaluationHom
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (hL : ∀ m, m ∉ s → IsZero (L.X (-m)))
    (hη : IsCoevaluationCocycle K L p) :
    𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ L :=
  coevaluationHomOf K L (totalCoev K.X L.X s p) (totalCoev_comp_d K L p s hK hL hη)

/-- In degree zero, `coevaluationHom` is the sum of the degreewise coevaluations. -/
theorem coevaluationHom_f_zero
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (hL : ∀ m, m ∉ s → IsZero (L.X (-m)))
    (hη : IsCoevaluationCocycle K L p) :
    (coevaluationHom K L p s hK hL hη).f 0 =
      (tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫ tensorUnit₀.hom ≫
        ∑ n ∈ s, (p n).coevaluation' ≫ ιTensorObj K L n (-n) 0 (by omega) :=
  congrArg (fun x => (tensorUnitIso C (ComplexShape.up ℤ)).inv 0 ≫ x)
    (gradedCoev_zero K.X L.X s p)

end

section

variable (K L : CochainComplex C ℤ) (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- The summed evaluation `∑ εₙ` out of the degree-zero part of `L ⊗ K`. -/
noncomputable def evalZero : (L ⊗ K).X 0 ⟶ 𝟙_ C := totalEval K.X L.X p

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- On the summand `L^{-m} ⊗ K^m` the summed evaluation is the degreewise evaluation `εₘ`. -/
theorem ι_evalZero (m : ℤ) :
    ιTensorObj L K (-m) m 0 (by omega) ≫ evalZero K L p = (p m).evaluation' := by
  show GradedObject.Monoidal.ιTensorObj L.X K.X (-m) m 0 (by omega) ≫ totalEval K.X L.X p = _
  rw [totalEval, ι_tensorObjDesc]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Under the chain-map condition `hε`, the summed evaluation `∑ εₙ` kills the differential of
`L ⊗ K` into degree zero. -/
theorem d_comp_evalZero (hε : IsEvaluationCocycle K L p) (i : ℤ) :
    (L ⊗ K).d i 0 ≫ evalZero K L p = 0 := by
  by_cases hi : (ComplexShape.up ℤ).Rel i 0
  swap
  · rw [(L ⊗ K).shape i 0 hi, zero_comp]
  have hi' : i + 1 = 0 := hi
  obtain rfl : i = -1 := by omega
  refine mapBifunctor.hom_ext fun a b hab => ?_
  have hab' : a + b = -1 := hab
  obtain rfl : a = -(b + 1) := by omega
  rw [comp_zero, ← Category.assoc,
    ιTensorObj_d_koszul L K (-(b + 1)) b (-1) (-b) (b + 1) 0 (by omega) (by omega) rfl (by omega),
    Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
    ι_evalZero K L p b, ι_evalZero K L p (b + 1), Int.negOnePow_neg]
  exact hε b

/-- The degree-`j` component of the summed evaluation `L ⊗ K ⟶ 𝟙`. -/
noncomputable def evalF (j : ℤ) : (L ⊗ K).X j ⟶ (𝟙_ (CochainComplex C ℤ)).X j :=
  gradedEval K.X L.X p j ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom j

/-- Outside degree zero the evaluation vanishes, the unit complex being concentrated there. -/
theorem evalF_eq_zero {j : ℤ} (hj : j ≠ 0) : evalF K L p j = 0 :=
  (isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ C) j hj).eq_of_tgt _ _

/-- In degree zero the evaluation is the summed evaluation, read through the identification of
the two units. -/
theorem evalF_zero : evalF K L p 0 =
    evalZero K L p ≫ tensorUnit₀.inv ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom 0 :=
  (congrArg (fun x => x ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom 0)
    (gradedEval_zero K.X L.X p)).trans (Category.assoc _ _ _)

/-- The summed evaluation kills the differential in every degree. -/
theorem d_comp_evalF (hε : IsEvaluationCocycle K L p) (i j : ℤ) :
    (L ⊗ K).d i j ≫ evalF K L p j = 0 := by
  by_cases hj : j = 0
  · subst hj
    rw [evalF_zero, ← Category.assoc, d_comp_evalZero K L p hε i, zero_comp]
  · rw [evalF_eq_zero K L p hj, comp_zero]

/-- The summed evaluation `ε = ∑ εₙ`, as a morphism of complexes. It is concentrated in degree
zero, where its restriction to the summand `L^{-n} ⊗ K^n` is the degreewise evaluation `εₙ`. -/
noncomputable def evaluationHom (hε : IsEvaluationCocycle K L p) :
    L ⊗ K ⟶ 𝟙_ (CochainComplex C ℤ) where
  f j := evalF K L p j
  comm' i j _ := by
    rw [show (𝟙_ (CochainComplex C ℤ)).d i j = 0 from
      single_obj_d (ComplexShape.up ℤ) 0 (𝟙_ C) i j, comp_zero, d_comp_evalF K L p hε i j]

/-- In degree zero, `evaluationHom` restricts on the summand `L^{-m} ⊗ K^m` to the degreewise
evaluation `εₘ`. -/
theorem ι_evaluationHom_f_zero (hε : IsEvaluationCocycle K L p) (m : ℤ) :
    ιTensorObj L K (-m) m 0 (by omega) ≫ (evaluationHom K L p hε).f 0 =
      (p m).evaluation' ≫ tensorUnit₀.inv ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom 0 := by
  show ιTensorObj L K (-m) m 0 (by omega) ≫ evalF K L p 0 = _
  rw [evalF_zero, ← Category.assoc, ι_evalZero]

end

/-- If `K` and `L` vanish outside a finite set `s` of degrees, if `L^{-n}` is a dual of `K^n` in
every degree, and if the two chain-map conditions hold, then the sums `η = ∑ ηₙ` and `ε = ∑ εₙ`
satisfy both triangle identities, so `L` is a dual of `K` in the monoidal category of complexes.
-/
@[instance_reducible]
noncomputable def exactPairingOfDegreewise (K L : CochainComplex C ℤ)
    (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n))) (s : Finset ℤ)
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (hL : ∀ m, m ∉ s → IsZero (L.X (-m)))
    (hη : IsCoevaluationCocycle K L p) (hε : IsEvaluationCocycle K L p) :
    ExactPairing K L :=
  letI := CochainComplex.forgetMonoidal (C := C)
  letI : ExactPairing ((HomologicalComplex.forget C (ComplexShape.up ℤ)).obj K)
      ((HomologicalComplex.forget C (ComplexShape.up ℤ)).obj L) :=
    GradedObject.Monoidal.exactPairingOfDegreewise K.X L.X s p hK hL
  ExactPairing.ofFaithful (HomologicalComplex.forget C (ComplexShape.up ℤ))
    (evaluationHom K L p hε) (coevaluationHom K L p s hK hL hη)
    (by
      ext j
      exact (Category.id_comp
        (gradedEval K.X L.X p j ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom j)).symm)
    (by
      ext j
      exact congrArg (fun x => (tensorUnitIso C (ComplexShape.up ℤ)).inv j ≫ x)
        (Category.comp_id (gradedCoev K.X L.X s p j)).symm)

section Components

variable (K L : CochainComplex C ℤ) (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- The differential of `K ⊗ L` from degree zero to degree one, as a morphism
`tensorObj K.X L.X 0 ⟶ tensorObj K.X L.X 1` of the underlying graded objects. -/
noncomputable def dZeroOne : tensorObj K.X L.X 0 ⟶ tensorObj K.X L.X 1 := (K ⊗ L).d 0 1

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The restriction of `dZeroOne` to the summand `K^c ⊗ L^{-c}`: the first factor is
differentiated with sign `+1`, the second with sign `(-1)^c`. -/
theorem ι_dZeroOne (c b' : ℤ) (hb' : -c + 1 = b') :
    GradedObject.Monoidal.ιTensorObj K.X L.X c (-c) 0 (by omega) ≫ dZeroOne K L =
      (K.d c (c + 1) ▷ L.X (-c)) ≫
          GradedObject.Monoidal.ιTensorObj K.X L.X (c + 1) (-c) 1 (by omega) +
        c.negOnePow • ((K.X c ◁ L.d (-c) b') ≫
          GradedObject.Monoidal.ιTensorObj K.X L.X c b' 1 (by omega)) :=
  ιTensorObj_d_koszul K L c (-c) 0 (c + 1) b' 1 (by omega) rfl hb' (by omega)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The projection of `dZeroOne K L` onto the summand `K^{n+1} ⊗ L^{-n}` of degree one is the
sum of the projection onto `K^n ⊗ L^{-n}` differentiated in the first factor and, with the
Koszul sign `(-1)^{n+1}`, the projection onto `K^{n+1} ⊗ L^{-(n+1)}` differentiated in the
second. -/
theorem dZeroOne_comp_πTensorObj (n : ℤ) :
    dZeroOne K L ≫ GradedObject.Monoidal.πTensorObj K.X L.X (n + 1) (-n) 1 (by omega) =
      GradedObject.Monoidal.πTensorObj K.X L.X n (-n) 0 (by omega) ≫
          (K.d n (n + 1) ▷ L.X (-n)) +
        ((n + 1).negOnePow : ℤˣ) •
          (GradedObject.Monoidal.πTensorObj K.X L.X (n + 1) (-(n + 1)) 0 (by omega) ≫
            (K.X (n + 1) ◁ L.d (-(n + 1)) (-n))) := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ (fun c d hcd => ?_)
  obtain rfl : d = -c := by omega
  obtain ⟨b', hb'⟩ : ∃ b', -c + 1 = b' := ⟨_, rfl⟩
  rw [← Category.assoc, ι_dZeroOne K L c b' hb']
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    Preadditive.comp_add, Linear.comp_units_smul]
  rcases eq_or_ne c n with rfl | hc
  · subst hb'
    rw [GradedObject.Monoidal.ιTensorObj_πTensorObj_self,
      GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X L.X (c + 1) (-c) c (-c + 1) 1
        (by omega) (by omega) (by omega),
      GradedObject.Monoidal.ιTensorObj_πTensorObj_self_assoc,
      GradedObject.Monoidal.ιTensorObj_πTensorObj_ne_assoc K.X L.X (c + 1) (-(c + 1)) c (-c) 0
        (by omega) (by omega) (by omega)]
    simp
  · rcases eq_or_ne c (n + 1) with rfl | hc'
    · obtain rfl : b' = -n := by omega
      rw [GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X L.X (n + 1) (-n) (n + 1 + 1)
          (-(n + 1)) 1 (by omega) (by omega) (by omega),
        GradedObject.Monoidal.ιTensorObj_πTensorObj_self,
        GradedObject.Monoidal.ιTensorObj_πTensorObj_ne_assoc K.X L.X n (-n) (n + 1) (-(n + 1)) 0
          (by omega) (by omega) (by omega),
        GradedObject.Monoidal.ιTensorObj_πTensorObj_self_assoc]
      simp
    · subst hb'
      rw [GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X L.X (n + 1) (-n) (c + 1) (-c) 1
          (by omega) (by omega) (by omega),
        GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X L.X (n + 1) (-n) c (-c + 1) 1
          (by omega) (by omega) (by omega),
        GradedObject.Monoidal.ιTensorObj_πTensorObj_ne_assoc K.X L.X n (-n) c (-c) 0
          (by omega) (by omega) (by omega),
        GradedObject.Monoidal.ιTensorObj_πTensorObj_ne_assoc K.X L.X (n + 1) (-(n + 1)) c (-c) 0
          (by omega) (by omega) (by omega)]
      simp

/-- Morphisms `𝟙 ⟶ tensorObj K.X L.X 1` into the degree-one part of `K ⊗ L` are determined by
their projections onto the summands `K^u ⊗ L^v`. -/
def IsSeparatedDegOne : Prop :=
  ∀ f g : 𝟙_ C ⟶ tensorObj K.X L.X 1,
    (∀ (u v : ℤ) (h : u + v = 1),
      f ≫ GradedObject.Monoidal.πTensorObj K.X L.X u v 1 h =
        g ≫ GradedObject.Monoidal.πTensorObj K.X L.X u v 1 h) → f = g

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- A morphism `𝟙 ⟶ tensorObj K.X L.X 0` whose component on each summand `K^n ⊗ L^{-n}` is `ηₙ`
is killed by the differential of `K ⊗ L`, given the chain-map condition `hη` and the separation
of the degree-one part. -/
theorem comp_d_eq_zero_of_isAssembledCoev (coev : 𝟙_ C ⟶ tensorObj K.X L.X 0)
    (hc : GradedObject.Monoidal.IsAssembledCoev K.X L.X p coev)
    (hsep : IsSeparatedDegOne K L) (hη : IsCoevaluationCocycle K L p) (j : ℤ) :
    coev ≫ (K ⊗ L).d 0 j = 0 := by
  by_cases hj : (ComplexShape.up ℤ).Rel 0 j
  swap
  · exact (congrArg (fun x => coev ≫ x) ((K ⊗ L).shape 0 j hj)).trans comp_zero
  have hj' : (0 : ℤ) + 1 = j := hj
  obtain rfl : j = 1 := by omega
  show coev ≫ dZeroOne K L = 0
  refine hsep _ _ (fun u v h => ?_)
  obtain ⟨n, rfl⟩ : ∃ n, v = -n := ⟨-v, (neg_neg v).symm⟩
  obtain rfl : u = n + 1 := by omega
  rw [zero_comp, Category.assoc, dZeroOne_comp_πTensorObj K L n, Preadditive.comp_add,
    Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, hc n, hc (n + 1)]
  exact hη n

/-- If `L^{-n}` is a dual of `K^n` in every degree, `coev` has component `ηₙ` on each summand
`K^n ⊗ L^{-n}`, the degree-one part of `K ⊗ L` is separated and the two chain-map conditions
hold, then `coev` and `ε = ∑ εₙ` exhibit `L` as a dual of `K` in the monoidal category of
complexes. -/
@[instance_reducible]
noncomputable def exactPairingOfComponents (coev : 𝟙_ C ⟶ tensorObj K.X L.X 0)
    (hc : GradedObject.Monoidal.IsAssembledCoev K.X L.X p coev)
    (hsep : IsSeparatedDegOne K L) (hη : IsCoevaluationCocycle K L p)
    (hε : IsEvaluationCocycle K L p) :
    ExactPairing K L :=
  letI := CochainComplex.forgetMonoidal (C := C)
  letI : ExactPairing ((HomologicalComplex.forget C (ComplexShape.up ℤ)).obj K)
      ((HomologicalComplex.forget C (ComplexShape.up ℤ)).obj L) :=
    GradedObject.Monoidal.exactPairingOfComponents K.X L.X p coev hc
  ExactPairing.ofFaithful (HomologicalComplex.forget C (ComplexShape.up ℤ))
    (evaluationHom K L p hε)
    (coevaluationHomOf K L coev (comp_d_eq_zero_of_isAssembledCoev K L p coev hc hsep hη))
    (by
      ext j
      exact (Category.id_comp
        (gradedEval K.X L.X p j ≫ (tensorUnitIso C (ComplexShape.up ℤ)).hom j)).symm)
    (by
      ext j
      exact congrArg (fun x => (tensorUnitIso C (ComplexShape.up ℤ)).inv j ≫ x)
        (Category.comp_id (gradedCoevOf K.X L.X coev j)).symm)

end Components

section SignedTranspose

variable (K L : CochainComplex C ℤ) (p : ∀ n : ℤ, ExactPairing (K.X n) (L.X (-n)))

/-- The chosen dual of a term of `K`, packaged as a `HasRightDual`. -/
abbrev hasRightDualX (n : ℤ) : HasRightDual (K.X n) :=
  letI := p n
  ⟨L.X (-n)⟩

/-- The differential `L^{-n-1} ⟶ L^{-n}` is `(-1)^n` times the right adjoint mate of the
differential `K^n ⟶ K^{n+1}`, the duals being the given degreewise ones; in the degrees of `L`,
`d_L^m = -(-1)^m · (d_K^{-m-1})ᘁ`. -/
abbrev IsSignedTranspose : Prop :=
  ∀ n : ℤ, L.d (-(n + 1)) (-n) =
    (n.negOnePow : ℤˣ) • @rightAdjointMate C _ _ (K.X n) (K.X (n + 1))
      (hasRightDualX K L p n) (hasRightDualX K L p (n + 1)) (K.d n (n + 1))

omit [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- If the differential of `L` is the signed transpose of that of `K`, the degreewise
coevaluations satisfy `IsCoevaluationCocycle`. -/
theorem isCoevaluationCocycle_of_signedTranspose (hd : IsSignedTranspose K L p) :
    IsCoevaluationCocycle K L p := by
  intro n
  have hmate : (p (n + 1)).coevaluation' ≫ (K.X (n + 1) ◁ @rightAdjointMate C _ _
        (K.X n) (K.X (n + 1)) (hasRightDualX K L p n) (hasRightDualX K L p (n + 1))
        (K.d n (n + 1))) =
      (p n).coevaluation' ≫ (K.d n (n + 1) ▷ L.X (-n)) :=
    @coevaluation_comp_rightAdjointMate C _ _ (K.X n) (K.X (n + 1))
      (hasRightDualX K L p n) (hasRightDualX K L p (n + 1)) (K.d n (n + 1))
  rw [hd n, units_smul_whiskerLeft, Linear.comp_units_smul, hmate, smul_smul,
    Int.negOnePow_succ, neg_mul, Int.units_mul_self, Units.neg_smul, one_smul, add_neg_cancel]

omit [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- If the differential of `L` is the signed transpose of that of `K`, the degreewise
evaluations satisfy `IsEvaluationCocycle`. -/
theorem isEvaluationCocycle_of_signedTranspose (hd : IsSignedTranspose K L p) :
    IsEvaluationCocycle K L p := by
  intro n
  have hmate : (@rightAdjointMate C _ _ (K.X n) (K.X (n + 1)) (hasRightDualX K L p n)
        (hasRightDualX K L p (n + 1)) (K.d n (n + 1)) ▷ K.X n) ≫ (p n).evaluation' =
      (L.X (-(n + 1)) ◁ K.d n (n + 1)) ≫ (p (n + 1)).evaluation' :=
    @rightAdjointMate_comp_evaluation C _ _ (K.X n) (K.X (n + 1))
      (hasRightDualX K L p n) (hasRightDualX K L p (n + 1)) (K.d n (n + 1))
  rw [hd n, units_smul_whiskerRight, Linear.units_smul_comp, hmate, Int.negOnePow_succ,
    Units.neg_smul, add_neg_cancel]

/-- If `K` and `L` vanish outside a finite set `s` of degrees, `L^{-n}` is a dual of `K^n` in
every degree and the differential of `L` is the signed transpose of that of `K`, then
`η = ∑ ηₙ` and `ε = ∑ εₙ` exhibit `L` as a dual of `K` in the monoidal category of complexes. -/
@[instance_reducible]
noncomputable def exactPairingOfSignedTranspose (s : Finset ℤ)
    (hK : ∀ m, m ∉ s → IsZero (K.X m)) (hL : ∀ m, m ∉ s → IsZero (L.X (-m)))
    (hd : IsSignedTranspose K L p) :
    ExactPairing K L :=
  exactPairingOfDegreewise K L p s hK hL
    (isCoevaluationCocycle_of_signedTranspose K L p hd)
    (isEvaluationCocycle_of_signedTranspose K L p hd)

/-- If `L^{-n}` is a dual of `K^n` in every degree, the differential of `L` is the signed
transpose of that of `K`, `coev` has component `ηₙ` on each summand `K^n ⊗ L^{-n}` and the
degree-one part of `K ⊗ L` is separated, then `L` is a dual of `K` in the monoidal category of
complexes. -/
@[instance_reducible]
noncomputable def exactPairingOfSignedTransposeOfComponents
    (coev : 𝟙_ C ⟶ tensorObj K.X L.X 0)
    (hc : GradedObject.Monoidal.IsAssembledCoev K.X L.X p coev)
    (hsep : IsSeparatedDegOne K L) (hd : IsSignedTranspose K L p) :
    ExactPairing K L :=
  _root_.CochainComplex.exactPairingOfComponents K L p coev hc hsep
    (isCoevaluationCocycle_of_signedTranspose K L p hd)
    (isEvaluationCocycle_of_signedTranspose K L p hd)

end SignedTranspose

end CochainComplex

end
