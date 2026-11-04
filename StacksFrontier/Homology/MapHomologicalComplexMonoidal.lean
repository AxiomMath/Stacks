module

public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# A monoidal functor acts monoidally on homological complexes

Let `C` and `D` be monoidal preadditive categories whose tensor products commute with the
coproducts needed for `Mathlib.Algebra.Homology.Monoidal`, so that `HomologicalComplex C c` and
`HomologicalComplex D c` carry the total tensor product.  If `F : C ⥤ D` is additive, monoidal,
and preserves the antidiagonal coproducts occurring in a total complex, then

  `F.mapHomologicalComplex c : HomologicalComplex C c ⥤ HomologicalComplex D c`

is monoidal for those structures.  The comparison morphism itself is
`CategoryTheory.Functor.mapBifunctorTotalIso` from `StacksFrontier.Homology.TotalComplexTransport`,
applied to `F = F' = curriedTensor` and to `Φ₁ = Φ₂ = Φ = F`; what this file adds is the
coherence, i.e. the associativity and the two unitality axioms, and hence the
`Functor.CoreMonoidal` and `Functor.Monoidal` structures.

Mathlib has the monoidal category structure on `HomologicalComplex C c` but no monoidal functor
structure on `mapHomologicalComplex`; the "good tensor" conditions are carried there as
hypotheses rather than instances, and they are carried that way here too.

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexTensorator`: the tensorator
  `F K₁ ⊗ F K₂ ≅ F (K₁ ⊗ K₂)` of `F.mapHomologicalComplex c`, obtained from
  `Functor.mapBifunctorTotalIso`.
* `CategoryTheory.Functor.mapHomologicalComplexSingleIso`: an additive functor commutes with
  `HomologicalComplex.single`.
* `CategoryTheory.Functor.mapHomologicalComplexUnitIso`: the unit comparison
  `𝟙_ ≅ F.mapHomologicalComplex c |>.obj 𝟙_`.
* `CategoryTheory.Functor.mapHomologicalComplexCoreMonoidal` and
  `CategoryTheory.Functor.mapHomologicalComplexMonoidal`: **the monoidal functor structure.**

## Main results

* `CategoryTheory.Functor.mapHomologicalComplexTensorator_associativity`,
  `..._left_unitality`, `..._right_unitality`: the three coherence axioms.

## Implementation notes

The three axioms are proved by extensionality on the summands of the *source* of each axiom,
which is always a total complex in `D` and therefore a coproduct on the nose: no hypothesis on
`F` beyond preservation of the antidiagonal coproducts is needed for that, and in particular the
image `F (Tot …)` — which is a coproduct only because `F` preserves these coproducts — never has
to be taken apart.  On a summand, each axiom becomes the corresponding axiom for `F` itself
(`Functor.LaxMonoidal.associativity`, `left_unitality`, `right_unitality`) together with the
naturality of `μ F`.

The bridge lemmas in `HomologicalComplex.Monoidal` record the induced monoidal structure of
`Mathlib.Algebra.Homology.Monoidal` on the summands of the total tensor complex: Mathlib builds
it by `Monoidal.induced` along `HomologicalComplex.forget`, which keeps the
`MonoidalCategoryStruct`, so `⊗`, `α_`, `λ_` and `ρ_` really are `mapBifunctor`,
`mapBifunctorAssociator`, `leftUnitor` and `rightUnitor` and Mathlib's `ι`-level
characterisations apply directly.  Mathlib characterises the two unitors only on their
inverses, so `ι_leftUnitor_hom` and `ι_rightUnitor_hom` invert those by hand.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

/-! ## Bridge lemmas for the induced monoidal structure on `HomologicalComplex` -/

namespace HomologicalComplex.Monoidal

private theorem comp_eq_hom_of_inv_comp_eq_id {A : Type*} [Category A]
    {X Y T : A} (e : Y ≅ X) (ι : Y ⟶ T) (H : T ⟶ X) (h : e.inv ≫ ι ≫ H = 𝟙 X) :
    ι ≫ H = e.hom :=
  (cancel_epi e.inv).1 (by rw [h, e.inv_hom_id])

variable {E : Type u} [Category.{v} E] [MonoidalCategory E] [Preadditive E] [HasZeroObject E]
  [(curriedTensor E).Additive] [∀ X₁ : E, ((curriedTensor E).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I E), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂ : E, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I E, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I E, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I E, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Whiskering on the right of homological complexes is the degreewise bifunctor map. -/
public lemma whiskerRight_f {K L : HomologicalComplex E c} (φ : K ⟶ L)
    (M : HomologicalComplex E c) (n : I) :
    (φ ▷ M).f n = (HomologicalComplex.mapBifunctorMap φ (𝟙 M) (curriedTensor E) c).f n := rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Whiskering on the left of homological complexes is the degreewise bifunctor map. -/
public lemma whiskerLeft_f (M : HomologicalComplex E c) {K L : HomologicalComplex E c}
    (φ : K ⟶ L) (n : I) :
    (M ◁ φ).f n = (HomologicalComplex.mapBifunctorMap (𝟙 M) φ (curriedTensor E) c).f n := rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The associator of homological complexes, degreewise. -/
public lemma associator_hom_f (K₁ K₂ K₃ : HomologicalComplex E c) (n : I) :
    (α_ K₁ K₂ K₃).hom.f n =
      (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso E)
        K₁ K₂ K₃ c c c n).hom := rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Right whiskering on the summands of the total tensor complex. -/
@[reassoc]
public lemma ι_whiskerRight {K L : HomologicalComplex E c} (φ : K ⟶ L)
    (M : HomologicalComplex E c) (p q n : I) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K M p q n h ≫ (φ ▷ M).f n =
      (φ.f p ▷ M.X q) ≫ HomologicalComplex.ιTensorObj L M p q n h := by
  rw [whiskerRight_f, HomologicalComplex.ι_mapBifunctorMap]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Left whiskering on the summands of the total tensor complex. -/
@[reassoc]
public lemma ι_whiskerLeft (M : HomologicalComplex E c) {K L : HomologicalComplex E c}
    (φ : K ⟶ L) (p q n : I) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M K p q n h ≫ (M ◁ φ).f n =
      (M.X p ◁ φ.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
  rw [whiskerLeft_f, HomologicalComplex.ι_mapBifunctorMap]
  simp

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The associator on the summands of the iterated total tensor complex. -/
@[reassoc]
public lemma ι₁₂_associator_hom (K₁ K₂ K₃ : HomologicalComplex E c) (i₁ i₂ i₃ n : I)
    (h : ComplexShape.r c c c c c (i₁, i₂, i₃) = n) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃ c c
        i₁ i₂ i₃ n h ≫ (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃ c c c
          i₁ i₂ i₃ n h := by
  rw [associator_hom_f, HomologicalComplex.ι_mapBifunctorAssociatorX_hom]
  rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The associator on the summands of the iterated total tensor complex, in terms of the
inclusions of the two-fold total complexes. -/
@[reassoc]
public lemma ι_associator_hom (K₁ K₂ K₃ : HomologicalComplex E c) (i₁ i₂ i₃ n : I)
    (h₁ : i₁ + i₂ + i₃ = n) (h₂ : i₁ + (i₂ + i₃) = n) :
    (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
        HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n h₁ ≫
          (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n h₂ := by
  have e1 : HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃ c c
        i₁ i₂ i₃ n h₁ =
      (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
        HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n h₁ :=
    HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor E) (curriedTensor E)
      K₁ K₂ K₃ c c i₁ i₂ i₃ (i₁ + i₂) n rfl h₁
  have e2 : HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃
        c c c i₁ i₂ i₃ n h₁ =
      (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
        HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n h₂ :=
    HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor E) (curriedTensor E)
      K₁ K₂ K₃ c c c i₁ i₂ i₃ (i₂ + i₃) n rfl h₂
  have e3 : HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃ c c
        i₁ i₂ i₃ n h₁ ≫ (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor E) (curriedTensor E) K₁ K₂ K₃
          c c c i₁ i₂ i₃ n h₁ :=
    ι₁₂_associator_hom K₁ K₂ K₃ i₁ i₂ i₃ n h₁
  rw [← Category.assoc, ← e1, e3, e2]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The left unitor of homological complexes, degreewise. -/
public lemma leftUnitor_hom_f (K : HomologicalComplex E c) (i : I) :
    (λ_ K).hom.f i = (HomologicalComplex.leftUnitor' K).hom i := rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The right unitor of homological complexes, degreewise. -/
public lemma rightUnitor_hom_f (K : HomologicalComplex E c) (i : I) :
    (ρ_ K).hom.f i = (HomologicalComplex.rightUnitor' K).hom i := rfl

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The left unitor on the summand of the total tensor complex indexed by `(0, i)`. -/
@[reassoc]
public lemma ι_leftUnitor_hom (K : HomologicalComplex E c) (i : I) :
    HomologicalComplex.ιTensorObj (HomologicalComplex.tensorUnit E c) K 0 i i (zero_add i) ≫
        (λ_ K).hom.f i =
      ((HomologicalComplex.singleObjXSelf c 0 (𝟙_ E)).hom ▷ K.X i) ≫ (λ_ (K.X i)).hom := by
  rw [leftUnitor_hom_f]
  refine comp_eq_hom_of_inv_comp_eq_id
    (whiskerRightIso (HomologicalComplex.singleObjXSelf c 0 (𝟙_ E)) (K.X i) ≪≫ λ_ (K.X i)) _ _ ?_
  have hB : (HomologicalComplex.leftUnitor' K).inv i ≫
      (HomologicalComplex.leftUnitor' K).hom i = 𝟙 (K.X i) :=
    ((GradedObject.eval (C := E) i).mapIso (HomologicalComplex.leftUnitor' K)).inv_hom_id
  rw [HomologicalComplex.leftUnitor'_inv] at hB
  simpa using hB

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The right unitor on the summand of the total tensor complex indexed by `(i, 0)`. -/
@[reassoc]
public lemma ι_rightUnitor_hom (K : HomologicalComplex E c) (i : I) :
    HomologicalComplex.ιTensorObj K (HomologicalComplex.tensorUnit E c) i 0 i (add_zero i) ≫
        (ρ_ K).hom.f i =
      (K.X i ◁ (HomologicalComplex.singleObjXSelf c 0 (𝟙_ E)).hom) ≫ (ρ_ (K.X i)).hom := by
  rw [rightUnitor_hom_f]
  refine comp_eq_hom_of_inv_comp_eq_id
    (whiskerLeftIso (K.X i) (HomologicalComplex.singleObjXSelf c 0 (𝟙_ E)) ≪≫ ρ_ (K.X i)) _ _ ?_
  have hB : (HomologicalComplex.rightUnitor' K).inv i ≫
      (HomologicalComplex.rightUnitor' K).hom i = 𝟙 (K.X i) :=
    ((GradedObject.eval (C := E) i).mapIso (HomologicalComplex.rightUnitor' K)).inv_hom_id
  rw [HomologicalComplex.rightUnitor'_inv] at hB
  simpa using hB

omit [HasZeroObject E] [∀ (X₁ : E), ((curriedTensor E).obj X₁).Additive]
  [∀ (X₁ : E), PreservesColimit (Functor.empty E) ((curriedTensor E).obj X₁)]
  [∀ (X₂ : E), PreservesColimit (Functor.empty E) ((curriedTensor E).flip.obj X₂)] in
/-- A tensor product with a zero object is zero. -/
public lemma isZero_tensorObj_of_isZero_left {X : E} (hX : IsZero X) (Y : E) :
    IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← MonoidalCategory.id_whiskerRight X Y, hX]
  have h0 : ((curriedTensor E).map (0 : X ⟶ X)).app Y = 0 := by simp
  exact h0

omit [HasZeroObject E] [(curriedTensor E).Additive]
  [∀ (X₁ : E), PreservesColimit (Functor.empty E) ((curriedTensor E).obj X₁)]
  [∀ (X₂ : E), PreservesColimit (Functor.empty E) ((curriedTensor E).flip.obj X₂)] in
/-- A tensor product with a zero object is zero. -/
public lemma isZero_tensorObj_of_isZero_right (X : E) {Y : E} (hY : IsZero Y) :
    IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at hY ⊢
  rw [← MonoidalCategory.whiskerLeft_id X Y, hY]
  exact ((curriedTensor E).obj X).map_zero Y Y

end HomologicalComplex.Monoidal

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- The degreewise comparison `F(a ⊗ b) ≅ F a ⊗ F b`, in the shape in which
`Functor.mapBifunctorTotalIso` consumes it. -/
public noncomputable def mapHomologicalComplexTensorComparison (a b : C) :
    F.obj (((curriedTensor C).obj a).obj b) ≅ ((curriedTensor D).obj (F.obj a)).obj (F.obj b) :=
  (Functor.Monoidal.μIso F a b).symm

omit [HasZeroObject C] [HasZeroObject D] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive] [(curriedTensor D).Additive]
  [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [F.Additive] [Preadditive C] [Preadditive D] in
/-- The forward map of `mapHomologicalComplexTensorComparison` is the oplax structure map `δ`. -/
@[simp] public lemma mapHomologicalComplexTensorComparison_hom (a b : C) :
    (mapHomologicalComplexTensorComparison F a b).hom = δ F a b := rfl

omit [HasZeroObject C] [HasZeroObject D] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive] [(curriedTensor D).Additive]
  [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [F.Additive] [Preadditive C] [Preadditive D] in
/-- The inverse of `mapHomologicalComplexTensorComparison` is the lax structure map `μ`. -/
@[simp] public lemma mapHomologicalComplexTensorComparison_inv (a b : C) :
    (mapHomologicalComplexTensorComparison F a b).inv = μ F a b := rfl

omit [HasZeroObject C] [HasZeroObject D] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive] [(curriedTensor D).Additive]
  [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [F.Additive] [Preadditive C] [Preadditive D] in
/-- Naturality of `mapHomologicalComplexTensorComparison` in the first variable. -/
public lemma mapHomologicalComplexTensorComparison_naturality_left :
    ∀ {a a' : C} (f : a ⟶ a') (b : C),
      F.map (((curriedTensor C).map f).app b) ≫
          (mapHomologicalComplexTensorComparison F a' b).hom =
        (mapHomologicalComplexTensorComparison F a b).hom ≫
          ((curriedTensor D).map (F.map f)).app (F.obj b) :=
  fun {_ _} f b => (δ_natural_left F f b).symm

omit [HasZeroObject C] [HasZeroObject D] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive] [(curriedTensor D).Additive]
  [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [F.Additive] [Preadditive C] [Preadditive D] in
/-- Naturality of `mapHomologicalComplexTensorComparison` in the second variable. -/
public lemma mapHomologicalComplexTensorComparison_naturality_right :
    ∀ (a : C) {b b' : C} (g : b ⟶ b'),
      F.map (((curriedTensor C).obj a).map g) ≫
          (mapHomologicalComplexTensorComparison F a b').hom =
        (mapHomologicalComplexTensorComparison F a b).hom ≫
          ((curriedTensor D).obj (F.obj a)).map (F.map g) :=
  fun a {_ _} g => (δ_natural_right F a g).symm

/-- An additive functor commutes with the single-degree complex functor. -/
public noncomputable def mapHomologicalComplexSingleIso (j : I) (X : C) :
    (F.mapHomologicalComplex c).obj ((HomologicalComplex.single C c j).obj X) ≅
      (HomologicalComplex.single D c j).obj (F.obj X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = j then
        (F.mapIso (HomologicalComplex.singleObjXIsoOfEq c j X i h)).trans
          (HomologicalComplex.singleObjXIsoOfEq c j (F.obj X) i h).symm
      else
        IsZero.iso (by
            dsimp only [Functor.mapHomologicalComplex_obj_X]
            rw [IsZero.iff_id_eq_zero, ← F.map_id,
              (HomologicalComplex.isZero_single_obj_X c j X i h).eq_of_src (𝟙 _) 0, F.map_zero])
          (HomologicalComplex.isZero_single_obj_X c j (F.obj X) i h))
    (fun i i' _ => by
      simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.single_obj_d,
        Functor.map_zero, comp_zero, zero_comp])

omit [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [AddMonoid I]
  [c.TensorSigns] [F.Monoidal] [MonoidalCategory C] [MonoidalCategory D] in
/-- In degree `j`, the forward map of `mapHomologicalComplexSingleIso` is the image of the
identification of the single complex in its own degree. -/
@[simp] public lemma mapHomologicalComplexSingleIso_hom_f_self (j : I) (X : C) :
    (mapHomologicalComplexSingleIso F j X).hom.f j =
      F.map (HomologicalComplex.singleObjXSelf c j X).hom ≫
        (HomologicalComplex.singleObjXSelf c j (F.obj X)).inv := by
  dsimp [mapHomologicalComplexSingleIso, HomologicalComplex.singleObjXSelf]
  rw [dite_eq_left rfl]
  rfl

omit [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive] [AddMonoid I]
  [c.TensorSigns] [F.Monoidal] [MonoidalCategory C] [MonoidalCategory D] in
/-- In degree `j`, the inverse of `mapHomologicalComplexSingleIso` is the image of the
identification of the single complex in its own degree. -/
@[simp] public lemma mapHomologicalComplexSingleIso_inv_f_self (j : I) (X : C) :
    (mapHomologicalComplexSingleIso F j X).inv.f j =
      (HomologicalComplex.singleObjXSelf c j (F.obj X)).hom ≫
        F.map (HomologicalComplex.singleObjXSelf c j X).inv := by
  dsimp [mapHomologicalComplexSingleIso, HomologicalComplex.singleObjXSelf]
  rw [dite_eq_left rfl]
  rfl

section

variable [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject I D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I D, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) F]

/-- The transported bicomplex `F(K₁ ⊗ K₂)` has a total complex, because it is isomorphic
to the bicomplex computing `F K₁ ⊗ F K₂`. -/
public instance hasTotal_mapBicomplex_curriedTensor
    (K₁ K₂ : HomologicalComplex C c) :
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex F
      ((((curriedTensor C).mapBifunctorHomologicalComplex c c).obj K₁).obj K₂)) c :=
  HomologicalComplex₂.hasTotal_of_iso
    (mapBifunctorBicomplexIso (curriedTensor C) (curriedTensor D) F F F
      (mapHomologicalComplexTensorComparison F) c c
      (mapHomologicalComplexTensorComparison_naturality_left F)
      (mapHomologicalComplexTensorComparison_naturality_right F) K₁ K₂).symm c

/-- **The tensorator of `F.mapHomologicalComplex c`.** -/
public noncomputable def mapHomologicalComplexTensorator
    (K₁ K₂ : HomologicalComplex C c) :
    (F.mapHomologicalComplex c).obj K₁ ⊗ (F.mapHomologicalComplex c).obj K₂ ≅
      (F.mapHomologicalComplex c).obj (K₁ ⊗ K₂) :=
  (mapBifunctorTotalIso (curriedTensor C) (curriedTensor D) F F F
    (mapHomologicalComplexTensorComparison F) c c c
    (mapHomologicalComplexTensorComparison_naturality_left F)
    (mapHomologicalComplexTensorComparison_naturality_right F) K₁ K₂).symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- The tensorator on the summands of its source. -/
@[reassoc]
public lemma ι_mapHomologicalComplexTensorator_hom
    (K₁ K₂ : HomologicalComplex C c) (p q n : I) (h : p + q = n) :
    HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex c).obj K₁)
        ((F.mapHomologicalComplex c).obj K₂) p q n h ≫
      (mapHomologicalComplexTensorator F K₁ K₂).hom.f n =
      μ F (K₁.X p) (K₂.X q) ≫ F.map (HomologicalComplex.ιTensorObj K₁ K₂ p q n h) :=
  ι_mapBifunctorTotalIso_inv (curriedTensor C) (curriedTensor D) F F F
    (mapHomologicalComplexTensorComparison F) c c
    (mapHomologicalComplexTensorComparison_naturality_left F)
    (mapHomologicalComplexTensorComparison_naturality_right F) K₁ K₂ p q n h

/-- **The unit comparison of `F.mapHomologicalComplex c`.** -/
public noncomputable def mapHomologicalComplexUnitIso :
    𝟙_ (HomologicalComplex D c) ≅
      (F.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)) :=
  (HomologicalComplex.single D c 0).mapIso (Functor.Monoidal.εIso F) ≪≫
    (mapHomologicalComplexSingleIso F 0 (𝟙_ C)).symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (n : I), PreservesColimitsOfShape (Discrete ↑(c.π c c ⁻¹' {n})) F] in
/-- The unit comparison in degree zero. -/
public lemma mapHomologicalComplexUnitIso_hom_f_zero :
    (mapHomologicalComplexUnitIso F).hom.f 0 ≫
        F.map (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom =
      (HomologicalComplex.singleObjXSelf c 0 (𝟙_ D)).hom ≫ ε F := by
  have h : (mapHomologicalComplexUnitIso F).hom.f 0 =
      ((HomologicalComplex.single D c 0).map (Functor.Monoidal.εIso F).hom).f 0 ≫
        (mapHomologicalComplexSingleIso F 0 (𝟙_ C)).inv.f 0 := rfl
  rw [h, mapHomologicalComplexSingleIso_inv_f_self, HomologicalComplex.single_map_f_self]
  simp [← Functor.map_comp]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Associativity of the tensorator. -/
public lemma mapHomologicalComplexTensorator_associativity
    (K₁ K₂ K₃ : HomologicalComplex C c) :
    (mapHomologicalComplexTensorator F K₁ K₂).hom ▷ (F.mapHomologicalComplex c).obj K₃ ≫
        (mapHomologicalComplexTensorator F (K₁ ⊗ K₂) K₃).hom ≫
          (F.mapHomologicalComplex c).map (α_ K₁ K₂ K₃).hom =
      (α_ ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
            ((F.mapHomologicalComplex c).obj K₃)).hom ≫
        (F.mapHomologicalComplex c).obj K₁ ◁ (mapHomologicalComplexTensorator F K₂ K₃).hom ≫
          (mapHomologicalComplexTensorator F K₁ (K₂ ⊗ K₃)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i₁ i₂ i₃ h
  have hL : ComplexShape.π c c c (i₁ + i₂, i₃) = n := h
  have hR : ComplexShape.π c c c (i₁, i₂ + i₃) = n := by
    dsimp only [ComplexShape.π] at hL ⊢; rw [← hL]; exact (add_assoc i₁ i₂ i₃).symm
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.Monoidal.ι₁₂_associator_hom_assoc,
    HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor D) (curriedTensor D)
      ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
      ((F.mapHomologicalComplex c).obj K₃) c c c i₁ i₂ i₃ (i₂ + i₃) n rfl hR,
    HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor D) (curriedTensor D)
      ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
      ((F.mapHomologicalComplex c).obj K₃) c c i₁ i₂ i₃ (i₁ + i₂) n rfl hL]
  simp only [Category.assoc]
  rw [HomologicalComplex.Monoidal.ι_whiskerRight_assoc,
    ι_mapHomologicalComplexTensorator_hom_assoc,
    HomologicalComplex.Monoidal.ι_whiskerLeft_assoc,
    ι_mapHomologicalComplexTensorator_hom]
  simp only [curriedTensor_map_app, curriedTensor_obj_map,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_mapHomologicalComplexTensorator_hom,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ι_mapHomologicalComplexTensorator_hom]
  have hassoc : (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
      HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n hL ≫ (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n hR :=
    HomologicalComplex.Monoidal.ι_associator_hom K₁ K₂ K₃ i₁ i₂ i₃ n hL hR
  have hmapL : F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
      F.map (HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n hL) ≫
        F.map ((α_ K₁ K₂ K₃).hom.f n) =
      F.map (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        F.map (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          F.map (HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n hR) := by
    simp only [← Functor.map_comp]
    exact congrArg F.map hassoc
  have hμL : F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl) ▷
        F.obj (K₃.X i₃) ≫ μ F ((K₁ ⊗ K₂).X (i₁ + i₂)) (K₃.X i₃) =
      μ F (K₁.X i₁ ⊗ K₂.X i₂) (K₃.X i₃) ≫
        F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) :=
    Functor.LaxMonoidal.μ_natural_left F _ _
  have hμR : F.obj (K₁.X i₁) ◁
        F.map (HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          μ F (K₁.X i₁) ((K₂ ⊗ K₃).X (i₂ + i₃)) =
      μ F (K₁.X i₁) (K₂.X i₂ ⊗ K₃.X i₃) ≫
        F.map (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) :=
    Functor.LaxMonoidal.μ_natural_right F _ _
  rw [MonoidalCategory.comp_whiskerRight_assoc, reassoc_of% hμL, hmapL,
    MonoidalCategory.whiskerLeft_comp_assoc, reassoc_of% hμR,
    reassoc_of% Functor.LaxMonoidal.associativity F (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Left unitality of the tensorator. -/
public lemma mapHomologicalComplexTensorator_left_unitality (K : HomologicalComplex C c) :
    (λ_ ((F.mapHomologicalComplex c).obj K)).hom =
      (mapHomologicalComplexUnitIso F).hom ▷ (F.mapHomologicalComplex c).obj K ≫
        (mapHomologicalComplexTensorator F (𝟙_ (HomologicalComplex C c)) K).hom ≫
          (F.mapHomologicalComplex c).map (λ_ K).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ HomologicalComplex.mapBifunctor.hom_ext ?_
  intro p q hpq
  by_cases hp : p = 0
  · subst hp
    obtain rfl : n = q := by rw [← hpq]; exact zero_add q
    have hιL : HomologicalComplex.ιMapBifunctor (𝟙_ (HomologicalComplex D c))
          ((F.mapHomologicalComplex c).obj K) (curriedTensor D) c 0 n n hpq ≫
          (λ_ ((F.mapHomologicalComplex c).obj K)).hom.f n =
        ((HomologicalComplex.singleObjXSelf c 0 (𝟙_ D)).hom ▷ F.obj (K.X n)) ≫
          (λ_ (F.obj (K.X n))).hom :=
      HomologicalComplex.Monoidal.ι_leftUnitor_hom _ n
    have hιW : HomologicalComplex.ιMapBifunctor (𝟙_ (HomologicalComplex D c))
          ((F.mapHomologicalComplex c).obj K) (curriedTensor D) c 0 n n hpq ≫
          ((mapHomologicalComplexUnitIso F).hom ▷ (F.mapHomologicalComplex c).obj K).f n =
        ((mapHomologicalComplexUnitIso F).hom.f 0 ▷ F.obj (K.X n)) ≫
          HomologicalComplex.ιMapBifunctor
            ((F.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)))
            ((F.mapHomologicalComplex c).obj K) (curriedTensor D) c 0 n n hpq :=
      HomologicalComplex.Monoidal.ι_whiskerRight _ _ 0 n n hpq
    have hιT : HomologicalComplex.ιMapBifunctor
          ((F.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)))
          ((F.mapHomologicalComplex c).obj K) (curriedTensor D) c 0 n n hpq ≫
          (mapHomologicalComplexTensorator F (𝟙_ (HomologicalComplex C c)) K).hom.f n =
        μ F ((𝟙_ (HomologicalComplex C c)).X 0) (K.X n) ≫
          F.map (HomologicalComplex.ιMapBifunctor (𝟙_ (HomologicalComplex C c)) K
            (curriedTensor C) c 0 n n hpq) :=
      ι_mapHomologicalComplexTensorator_hom F _ K 0 n n hpq
    have hιLC : F.map (HomologicalComplex.ιMapBifunctor (𝟙_ (HomologicalComplex C c)) K
          (curriedTensor C) c 0 n n hpq) ≫
          F.map ((λ_ K).hom.f n) =
        F.map ((HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom ▷ K.X n) ≫
          F.map (λ_ (K.X n)).hom := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (HomologicalComplex.Monoidal.ι_leftUnitor_hom K n)
    have hμ : F.map (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom ▷ F.obj (K.X n) ≫
          μ F (𝟙_ C) (K.X n) =
        μ F ((𝟙_ (HomologicalComplex C c)).X 0) (K.X n) ≫
          F.map ((HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom ▷ K.X n) :=
      Functor.LaxMonoidal.μ_natural_left F _ _
    rw [hιL]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [reassoc_of% hιW, reassoc_of% hιT, hιLC, ← reassoc_of% hμ,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      mapHomologicalComplexUnitIso_hom_f_zero,
      MonoidalCategory.comp_whiskerRight_assoc,
      ← Functor.LaxMonoidal.left_unitality F (K.X n)]
  · exact (HomologicalComplex.Monoidal.isZero_tensorObj_of_isZero_left
      (HomologicalComplex.isZero_single_obj_X c 0 (𝟙_ D) p hp) _).eq_of_src _ _

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄] in
/-- Right unitality of the tensorator. -/
public lemma mapHomologicalComplexTensorator_right_unitality (K : HomologicalComplex C c) :
    (ρ_ ((F.mapHomologicalComplex c).obj K)).hom =
      (F.mapHomologicalComplex c).obj K ◁ (mapHomologicalComplexUnitIso F).hom ≫
        (mapHomologicalComplexTensorator F K (𝟙_ (HomologicalComplex C c))).hom ≫
          (F.mapHomologicalComplex c).map (ρ_ K).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ HomologicalComplex.mapBifunctor.hom_ext ?_
  intro p q hpq
  by_cases hq : q = 0
  · subst hq
    obtain rfl : n = p := by rw [← hpq]; exact add_zero p
    have hιL : HomologicalComplex.ιMapBifunctor ((F.mapHomologicalComplex c).obj K)
          (𝟙_ (HomologicalComplex D c)) (curriedTensor D) c n 0 n hpq ≫
          (ρ_ ((F.mapHomologicalComplex c).obj K)).hom.f n =
        (F.obj (K.X n) ◁ (HomologicalComplex.singleObjXSelf c 0 (𝟙_ D)).hom) ≫
          (ρ_ (F.obj (K.X n))).hom :=
      HomologicalComplex.Monoidal.ι_rightUnitor_hom _ n
    have hιW : HomologicalComplex.ιMapBifunctor ((F.mapHomologicalComplex c).obj K)
          (𝟙_ (HomologicalComplex D c)) (curriedTensor D) c n 0 n hpq ≫
          ((F.mapHomologicalComplex c).obj K ◁ (mapHomologicalComplexUnitIso F).hom).f n =
        (F.obj (K.X n) ◁ (mapHomologicalComplexUnitIso F).hom.f 0) ≫
          HomologicalComplex.ιMapBifunctor ((F.mapHomologicalComplex c).obj K)
            ((F.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)))
            (curriedTensor D) c n 0 n hpq :=
      HomologicalComplex.Monoidal.ι_whiskerLeft _ _ n 0 n hpq
    have hιT : HomologicalComplex.ιMapBifunctor ((F.mapHomologicalComplex c).obj K)
          ((F.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)))
          (curriedTensor D) c n 0 n hpq ≫
          (mapHomologicalComplexTensorator F K (𝟙_ (HomologicalComplex C c))).hom.f n =
        μ F (K.X n) ((𝟙_ (HomologicalComplex C c)).X 0) ≫
          F.map (HomologicalComplex.ιMapBifunctor K (𝟙_ (HomologicalComplex C c))
            (curriedTensor C) c n 0 n hpq) :=
      ι_mapHomologicalComplexTensorator_hom F K _ n 0 n hpq
    have hιLC : F.map (HomologicalComplex.ιMapBifunctor K (𝟙_ (HomologicalComplex C c))
          (curriedTensor C) c n 0 n hpq) ≫ F.map ((ρ_ K).hom.f n) =
        F.map (K.X n ◁ (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom) ≫
          F.map (ρ_ (K.X n)).hom := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (HomologicalComplex.Monoidal.ι_rightUnitor_hom K n)
    have hμ : F.obj (K.X n) ◁ F.map (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom ≫
          μ F (K.X n) (𝟙_ C) =
        μ F (K.X n) ((𝟙_ (HomologicalComplex C c)).X 0) ≫
          F.map (K.X n ◁ (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom) :=
      Functor.LaxMonoidal.μ_natural_right F _ _
    rw [hιL]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [reassoc_of% hιW, reassoc_of% hιT, hιLC, ← reassoc_of% hμ,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      mapHomologicalComplexUnitIso_hom_f_zero,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← Functor.LaxMonoidal.right_unitality F (K.X n)]
  · exact (HomologicalComplex.Monoidal.isZero_tensorObj_of_isZero_right _
      (HomologicalComplex.isZero_single_obj_X c 0 (𝟙_ D) q hq)).eq_of_src _ _

/-- **`F.mapHomologicalComplex c` is a monoidal functor** for the total tensor product of
homological complexes, when `F` is monoidal, additive, and preserves the antidiagonal
coproducts occurring in the total complex. -/
public noncomputable def mapHomologicalComplexCoreMonoidal :
    (F.mapHomologicalComplex c).CoreMonoidal where
  εIso := mapHomologicalComplexUnitIso F
  μIso := mapHomologicalComplexTensorator F
  μIso_hom_natural_left f X' := by
    have h := mapBifunctorTotalIso_inv_naturality (curriedTensor C) (curriedTensor D) F F F
      (mapHomologicalComplexTensorComparison F) c c (c := c)
      (mapHomologicalComplexTensorComparison_naturality_left F)
      (mapHomologicalComplexTensorComparison_naturality_right F) _ _ _ _ f (𝟙 X')
    simp only [Functor.map_id] at h
    exact h
  μIso_hom_natural_right X' f := by
    have h := mapBifunctorTotalIso_inv_naturality (curriedTensor C) (curriedTensor D) F F F
      (mapHomologicalComplexTensorComparison F) c c (c := c)
      (mapHomologicalComplexTensorComparison_naturality_left F)
      (mapHomologicalComplexTensorComparison_naturality_right F) _ _ _ _ (𝟙 X') f
    simp only [Functor.map_id] at h
    exact h
  associativity := mapHomologicalComplexTensorator_associativity F
  left_unitality := mapHomologicalComplexTensorator_left_unitality F
  right_unitality := mapHomologicalComplexTensorator_right_unitality F

/-- The monoidal functor structure on `F.mapHomologicalComplex c`, as an instance. -/
public noncomputable instance mapHomologicalComplexMonoidal :
    (F.mapHomologicalComplex c).Monoidal :=
  (mapHomologicalComplexCoreMonoidal F).toMonoidal

end

end CategoryTheory.Functor

end
