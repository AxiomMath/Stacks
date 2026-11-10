module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebraWeight
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAdmissibleGood
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitColimit

/-!
# The weight filtration of a free differential graded algebra

Let `(C, O)` be a ringed site, let `𝒮 : I → SheafOfGradedSets J` be a family of sheaves of graded
sets indexed by a linearly ordered set of levels, and let `δ` be a closed triangular derivation
datum, so that `O⟨S⟩` with the Leibniz extension of `δ` is a sheaf of differential graded
algebras. For a set `D` of weights, `F_D O⟨S⟩` is the part of `O⟨S⟩` spanned by the words of
weight in `D`: degreewise the sheafification of the free `O`-module on those words. When `D` is
closed under passing to smaller weights the differential of `O⟨S⟩` preserves `F_D`, because it
strictly lowers the weight, so `F_D` is a complex of `O`-modules and a direct summand of `O⟨S⟩`
degree by degree.

For a weight `w` the admissible short exact sequence

`0 ⟶ F_{<w} ⟶ F_{≤w} ⟶ (the weight w part) ⟶ 0`

is split in every degree, and its third term `F_{=w}` is the free complex with zero differential
on the words of weight `w`, again because the differential strictly lowers the weight.

## Main definitions

* `SheafOfModules.wordsIn D n`: the words of degree `n` and weight in `D`, a subfunctor of the
  presheaf of words.
* `SheafOfModules.filtPiece D n`, with `filtIncl` into `O⟨S⟩` and `filtProj` out of it.
* `SheafOfModules.filtComplex D`: the complex `F_D`, for `D` closed downwards, and
  `filtComplexIncl`, `filtComplexMap` its inclusions.
* `SheafOfModules.weightShortComplex w` and `weightSplitting w`: the split short exact sequence
  at `w`.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe t v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

/-! ### The pieces -/

/-- The words of degree `n` whose weight lies in `D`, as a subfunctor of the presheaf of words. -/
def wordsIn (D : Set (I →₀ ℕ)) (n : ℤ) : Subfunctor (wordPresheaf 𝒮 n) where
  obj U := {w | wordWt w.1 ∈ D}
  map {U V} f w hw := by
    change wordWt (wordMap f w.1) ∈ D
    rw [wordWt_wordMap]
    exact hw

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The words of weight in `D` are among those of weight in `E` when `D ⊆ E`. -/
theorem wordsIn_mono {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (n : ℤ) : wordsIn 𝒮 D n ≤ wordsIn 𝒮 E n :=
  fun _ _ hw => h hw

variable (Osharp)

/-- The degree-`n` piece of `F_D O⟨S⟩`. -/
noncomputable abbrev filtPiece (D : Set (I →₀ ℕ)) (n : ℤ) :
    SheafOfModules.{t} (toRingCat J Osharp) :=
  freePieceOf Osharp (wordsIn 𝒮 D n).toFunctor

/-- The inclusion of `F_D` into `O⟨S⟩` in degree `n`. -/
noncomputable def filtIncl (D : Set (I →₀ ℕ)) (n : ℤ) :
    filtPiece Osharp 𝒮 D n ⟶ algPiece (Osharp := Osharp) 𝒮 n :=
  freePieceMap (Osharp := Osharp) (wordsIn 𝒮 D n).ι

/-- The inclusion of `F_D` into `F_E` for `D ⊆ E`. -/
noncomputable def filtMap {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (n : ℤ) :
    filtPiece Osharp 𝒮 D n ⟶ filtPiece Osharp 𝒮 E n :=
  freePieceMap (Osharp := Osharp) (Subfunctor.homOfLe (wordsIn_mono 𝒮 h n))

/-- The projection of a word on `F_D`: the word itself when its weight is in `D`, and zero
otherwise. -/
noncomputable def filtProjNat (D : Set (I →₀ ℕ)) (n : ℤ) :
    wordPresheaf 𝒮 n ⟶ (filtPiece Osharp 𝒮 D n).val.presheaf ⋙ CategoryTheory.forget _ where
  app U := ↾fun w => by
    classical
    exact if h : wordWt w.1 ∈ D then freeGen Osharp (⟨w, h⟩ : (wordsIn 𝒮 D n).toFunctor.obj U)
      else 0
  naturality {U V} f := by
    classical
    ext w
    change (if h : wordWt (wordMap f w.1) ∈ D then freeGen Osharp
        (⟨(wordPresheaf 𝒮 n).map f w, h⟩ : (wordsIn 𝒮 D n).toFunctor.obj V) else 0) =
      (filtPiece Osharp 𝒮 D n).val.map f (if h : wordWt w.1 ∈ D then
        freeGen Osharp (⟨w, h⟩ : (wordsIn 𝒮 D n).toFunctor.obj U) else 0)
    by_cases h : wordWt w.1 ∈ D
    · rw [dite_eq_left ((wordWt_wordMap f w.1).symm ▸ h), dite_eq_left h]
      exact (freeGen_naturality (F := (wordsIn 𝒮 D n).toFunctor) f
        (⟨w, h⟩ : (wordsIn 𝒮 D n).toFunctor.obj U)).symm
    · rw [dite_eq_right (by rw [wordWt_wordMap]; exact h), dite_eq_right h]
      exact (map_zero _).symm

/-- The projection of `O⟨S⟩` on `F_D` in degree `n`. -/
noncomputable def filtProj (D : Set (I →₀ ℕ)) (n : ℤ) :
    algPiece (Osharp := Osharp) 𝒮 n ⟶ filtPiece Osharp 𝒮 D n :=
  freePieceDesc (filtPiece Osharp 𝒮 D n) (filtProjNat Osharp 𝒮 D n)

variable {Osharp}

/-- The canonical local section of the presheaf of words is the section attached to the word. -/
theorem freeGen_eq_algToSheaf {n : ℤ} {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) :
    freeGen Osharp (F := wordPresheaf 𝒮 n) w = (algToSheaf (Osharp := Osharp) 𝒮 n).app U
      (algOf 𝒮 n w 1) :=
  rfl

/-- The inclusion of `F_D` into `O⟨S⟩` sends the generator of a word to the generator of the
same word. -/
@[simp] theorem filtIncl_gen (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ}
    (w : (wordsIn 𝒮 D n).toFunctor.obj U) :
    (filtIncl Osharp 𝒮 D n).val.app U (freeGen Osharp w) =
      freeGen Osharp (F := wordPresheaf 𝒮 n) w.1 :=
  freePieceMap_gen _ w

/-- The inclusion of `F_D` into `F_E` sends the generator of a word to the generator of the same
word. -/
@[simp] theorem filtMap_gen {D E : Set (I →₀ ℕ)} (h : D ⊆ E) {n : ℤ} {U : Cᵒᵖ}
    (w : (wordsIn 𝒮 D n).toFunctor.obj U) :
    (filtMap Osharp 𝒮 h n).val.app U (freeGen Osharp w) =
      freeGen Osharp (⟨w.1, h w.2⟩ : (wordsIn 𝒮 E n).toFunctor.obj U) :=
  freePieceMap_gen _ w

/-- The projection on `F_D` sends the generator of a word of weight in `D` to its generator in
`F_D`. -/
theorem filtProj_gen_of_mem (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ} (w : WordIdx 𝒮 n U)
    (hw : wordWt w.1 ∈ D) :
    (filtProj Osharp 𝒮 D n).val.app U (freeGen Osharp (F := wordPresheaf 𝒮 n) w) =
      freeGen Osharp (⟨w, hw⟩ : (wordsIn 𝒮 D n).toFunctor.obj U) := by
  refine (freePieceDesc_gen (filtPiece Osharp 𝒮 D n) (filtProjNat Osharp 𝒮 D n) w).trans ?_
  exact dite_eq_left hw

/-- The projection on `F_D` kills the generator of a word of weight not in `D`. -/
theorem filtProj_gen_of_not_mem (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ} (w : WordIdx 𝒮 n U)
    (hw : wordWt w.1 ∉ D) :
    (filtProj Osharp 𝒮 D n).val.app U (freeGen Osharp (F := wordPresheaf 𝒮 n) w) = 0 := by
  refine (freePieceDesc_gen (filtPiece Osharp 𝒮 D n) (filtProjNat Osharp 𝒮 D n) w).trans ?_
  exact dite_eq_right hw

/-! ### The relations between the inclusions and the projections -/

/-- The projection on `F_D` is a retraction of the inclusion of `F_D` into `O⟨S⟩`. -/
@[reassoc (attr := simp)]
theorem filtIncl_filtProj (D : Set (I →₀ ℕ)) (n : ℤ) :
    filtIncl Osharp 𝒮 D n ≫ filtProj Osharp 𝒮 D n = 𝟙 _ :=
  freePieceOf_hom_ext fun U w =>
    ((congrArg (fun z => (filtProj Osharp 𝒮 D n).val.app U z) (filtIncl_gen 𝒮 D w)).trans
      (filtProj_gen_of_mem 𝒮 D w.1 w.2))

/-- For disjoint `D` and `E`, the inclusion of `F_D` followed by the projection on `F_E` is
zero. -/
theorem filtIncl_filtProj_of_disjoint {D E : Set (I →₀ ℕ)} (h : Disjoint D E) (n : ℤ) :
    filtIncl Osharp 𝒮 D n ≫ filtProj Osharp 𝒮 E n = 0 :=
  freePieceOf_hom_ext fun U w =>
    ((congrArg (fun z => (filtProj Osharp 𝒮 E n).val.app U z) (filtIncl_gen 𝒮 D w)).trans
      (filtProj_gen_of_not_mem 𝒮 E w.1 (Set.disjoint_left.mp h w.2))).trans
        (DifferentialGradedModule.zero_val_app U _).symm

/-- The inclusion of `F_D` into `F_E` followed by that of `F_E` into `O⟨S⟩` is the inclusion of
`F_D` into `O⟨S⟩`. -/
@[reassoc (attr := simp)]
theorem filtMap_filtIncl {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (n : ℤ) :
    filtMap Osharp 𝒮 h n ≫ filtIncl Osharp 𝒮 E n = filtIncl Osharp 𝒮 D n :=
  freePieceOf_hom_ext fun U w =>
    ((congrArg (fun z => (filtIncl Osharp 𝒮 E n).val.app U z) (filtMap_gen 𝒮 h w)).trans
      (filtIncl_gen 𝒮 E _)).trans (filtIncl_gen 𝒮 D w).symm

/-- The inclusions `F_D ⟶ F_E ⟶ F_G` compose to the inclusion `F_D ⟶ F_G`. -/
theorem filtMap_filtMap {D E G : Set (I →₀ ℕ)} (h : D ⊆ E) (h' : E ⊆ G) (n : ℤ) :
    filtMap Osharp 𝒮 h n ≫ filtMap Osharp 𝒮 h' n = filtMap Osharp 𝒮 (h.trans h') n :=
  freePieceOf_hom_ext fun U w =>
    ((congrArg (fun z => (filtMap Osharp 𝒮 h' n).val.app U z) (filtMap_gen 𝒮 h w)).trans
      (filtMap_gen 𝒮 h' _)).trans (filtMap_gen 𝒮 (h.trans h') w).symm

/-- The inclusion of `F_D` into itself is the identity. -/
theorem filtMap_refl (D : Set (I →₀ ℕ)) (n : ℤ) :
    filtMap Osharp 𝒮 (subset_refl D) n = 𝟙 _ :=
  freePieceOf_hom_ext fun _ w => filtMap_gen 𝒮 (subset_refl D) w

/-- The inclusion of `F_D` into `F_E` is the restriction of the projection on `F_E`. -/
theorem filtIncl_filtProj_of_subset {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (n : ℤ) :
    filtIncl Osharp 𝒮 D n ≫ filtProj Osharp 𝒮 E n = filtMap Osharp 𝒮 h n := by
  rw [← filtMap_filtIncl 𝒮 h, Category.assoc, filtIncl_filtProj, Category.comp_id]

/-! ### The projection fixes the sections of weights in `D` -/

/-- The image of a presentation element, as the sum of the images of its summands. -/
theorem algToSheaf_eq_sum {n : ℤ} {U : Cᵒᵖ} (a : algSections Osharp 𝒮 n U) :
    (algToSheaf (Osharp := Osharp) 𝒮 n).app U a =
      ∑ w ∈ a.support, (a w) • freeGen Osharp (F := wordPresheaf 𝒮 n)
        (w : (wordPresheaf 𝒮 n).obj U) := by
  change algToSheafAdd 𝒮 n U a = _
  conv_lhs => rw [IsPresIn.eq_sum a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [algToSheafAdd_apply, algToSheaf_algOf, ← algToSheaf_algOf_one]
  rfl

/-- Two morphisms out of `O⟨S⟩` that agree on the generators of words of weight in `D` agree on
the image of a presentation element whose words all have weight in `D`. -/
private theorem hom_app_algToSheaf_eq {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ}
    {P : SheafOfModules.{t} (toRingCat J Osharp)} (f g : algPiece (Osharp := Osharp) 𝒮 n ⟶ P)
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a)
    (h : ∀ w : WordIdx 𝒮 n U, wordWt w.1 ∈ D →
      f.val.app U (freeGen Osharp (F := wordPresheaf 𝒮 n) w) =
        g.val.app U (freeGen Osharp (F := wordPresheaf 𝒮 n) w)) :
    f.val.app U ((algToSheaf (Osharp := Osharp) 𝒮 n).app U a) =
      g.val.app U ((algToSheaf (Osharp := Osharp) 𝒮 n).app U a) := by
  rw [algToSheaf_eq_sum]
  refine (map_sum (f.val.app U).hom _ _).trans
    (Eq.trans (Finset.sum_congr rfl fun w hw => ?_) (map_sum (g.val.app U).hom _ _).symm)
  refine ((f.val.app U).hom.map_smul _ _).trans
    (Eq.trans ?_ ((g.val.app U).hom.map_smul _ _).symm)
  exact congrArg (fun z => a w • z) (h w (ha w hw))

/-- Two morphisms out of `O⟨S⟩` that agree on the image of every presentation element of weights
in `D` agree on every local section of weights in `D`. -/
private theorem hom_app_eq_of_isLocallyIn {D : Set (I →₀ ℕ)} {n : ℤ} {U : Cᵒᵖ}
    {P : SheafOfModules.{t} (toRingCat J Osharp)} (f g : algPiece (Osharp := Osharp) 𝒮 n ⟶ P)
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z)
    (h : ∀ (V : Cᵒᵖ) (a : algSections Osharp 𝒮 n V), IsPresIn 𝒮 D a →
      f.val.app V ((algToSheaf (Osharp := Osharp) 𝒮 n).app V a) =
        g.val.app V ((algToSheaf (Osharp := Osharp) 𝒮 n).app V a)) :
    f.val.app U z = g.val.app U z := by
  obtain ⟨S, hS, h'⟩ := hz
  refine P.isSheaf.isSeparated _ _ hS _ _ fun V f' hf => ?_
  obtain ⟨a, ha, hfa⟩ := h' f' hf
  change Stacks.sectionRestrict P.val f'.op (f.val.app U z) =
    Stacks.sectionRestrict P.val f'.op (g.val.app U z)
  refine (PresheafOfModules.naturality_apply f.val f'.op z).symm.trans
    (Eq.trans ?_ (PresheafOfModules.naturality_apply g.val f'.op z))
  exact (congrArg (f.val.app (op V)) hfa.symm).trans ((h (op V) a ha).trans
    (congrArg (g.val.app (op V)) hfa))

/-- The idempotent `π_D ∘ ι_D` fixes the image of a presentation element whose words all have
weight in `D`. -/
theorem filtProj_filtIncl_algToSheaf (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ}
    {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    (filtProj Osharp 𝒮 D n ≫ filtIncl Osharp 𝒮 D n).val.app U
        ((algToSheaf (Osharp := Osharp) 𝒮 n).app U a) =
      (algToSheaf (Osharp := Osharp) 𝒮 n).app U a :=
  hom_app_algToSheaf_eq 𝒮 (filtProj Osharp 𝒮 D n ≫ filtIncl Osharp 𝒮 D n) (𝟙 _) ha fun w hw =>
    (congrArg (fun z => (filtIncl Osharp 𝒮 D n).val.app _ z)
      (filtProj_gen_of_mem 𝒮 D w hw)).trans (filtIncl_gen 𝒮 D _)

/-- The projection on `F_E` kills the image of a presentation element whose words all have weight
in a set disjoint from `E`. -/
theorem filtProj_algToSheaf_eq_zero {D E : Set (I →₀ ℕ)} (hDE : Disjoint D E) {n : ℤ}
    {U : Cᵒᵖ} {a : algSections Osharp 𝒮 n U} (ha : IsPresIn 𝒮 D a) :
    (filtProj Osharp 𝒮 E n).val.app U ((algToSheaf (Osharp := Osharp) 𝒮 n).app U a) = 0 :=
  (hom_app_algToSheaf_eq 𝒮 (filtProj Osharp 𝒮 E n) 0 ha fun w hw =>
    (filtProj_gen_of_not_mem 𝒮 E w (Set.disjoint_left.mp hDE hw)).trans
      (DifferentialGradedModule.zero_val_app _ _).symm).trans
    (DifferentialGradedModule.zero_val_app _ _)

/-- **The idempotent `π_D ∘ ι_D` fixes every local section of weights in `D`.** -/
theorem filtProj_filtIncl_of_isLocallyIn (D : Set (I →₀ ℕ)) {n : ℤ} {U : Cᵒᵖ}
    {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    (filtProj Osharp 𝒮 D n ≫ filtIncl Osharp 𝒮 D n).val.app U z = z :=
  hom_app_eq_of_isLocallyIn 𝒮 (filtProj Osharp 𝒮 D n ≫ filtIncl Osharp 𝒮 D n) (𝟙 _) hz
    fun _ _ ha => filtProj_filtIncl_algToSheaf 𝒮 D ha

/-- **The projection on `F_E` kills every local section of weights in a set disjoint from
`E`.** -/
theorem filtProj_eq_zero_of_isLocallyIn {D E : Set (I →₀ ℕ)} (hDE : Disjoint D E) {n : ℤ}
    {U : Cᵒᵖ} {z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U} (hz : IsLocallyIn 𝒮 D z) :
    (filtProj Osharp 𝒮 E n).val.app U z = 0 :=
  (hom_app_eq_of_isLocallyIn 𝒮 (filtProj Osharp 𝒮 E n) 0 hz
    fun _ _ ha => (filtProj_algToSheaf_eq_zero 𝒮 hDE ha).trans
      (DifferentialGradedModule.zero_val_app _ _).symm).trans
    (DifferentialGradedModule.zero_val_app _ _)

/-! ### The complexes `F_D` -/

section Complex

variable [LinearOrder I] (δ : DerivationDatum (Osharp := Osharp) 𝒮)
  (hδ : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
    (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
  (htri : DerivationDatum.IsTriangular 𝒮 δ)

/-- A set of weights is **closed downwards** when it contains every weight strictly below one of
its elements. -/
def IsWeightLower (D : Set (I →₀ ℕ)) : Prop := strictBelow D ⊆ D

variable (Osharp) in
/-- The differential of `F_D`: the differential of `O⟨S⟩` restricted to `F_D` and projected back
on it. -/
noncomputable def filtD (D : Set (I →₀ ℕ)) (n : ℤ) :
    filtPiece Osharp 𝒮 D n ⟶ filtPiece Osharp 𝒮 D (n + 1) :=
  filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n ≫ filtProj Osharp 𝒮 D (n + 1)

include htri in
/-- **The differential of `O⟨S⟩` preserves `F_D`** when `D` is closed downwards: the projection
on `F_D` fixes the differential of a section of `F_D`. -/
@[reassoc]
theorem filtIncl_algD_filtProj_filtIncl {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) (n : ℤ) :
    filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n ≫ filtProj Osharp 𝒮 D (n + 1) ≫
        filtIncl Osharp 𝒮 D (n + 1) =
      filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n :=
  freePieceOf_hom_ext fun U w => by
    have h1 : (filtIncl Osharp 𝒮 D n).val.app U (freeGen Osharp w) =
        (algToSheaf (Osharp := Osharp) 𝒮 n).app U (algOf 𝒮 n w.1 1) :=
      (filtIncl_gen 𝒮 D w).trans (freeGen_eq_algToSheaf 𝒮 w.1)
    change (filtProj Osharp 𝒮 D (n + 1) ≫ filtIncl Osharp 𝒮 D (n + 1)).val.app U
        ((algD 𝒮 δ n).val.app U ((filtIncl Osharp 𝒮 D n).val.app U (freeGen Osharp w))) =
      (algD 𝒮 δ n).val.app U ((filtIncl Osharp 𝒮 D n).val.app U (freeGen Osharp w))
    rw [h1]
    exact filtProj_filtIncl_of_isLocallyIn 𝒮 D
      ((algD_isLocallyIn δ htri (IsPresIn.algOf (D := D) w.1 w.2 1)).mono hD)

include htri in
/-- For `D` closed downwards, the inclusion of `F_D` into `O⟨S⟩` commutes with the
differentials. -/
@[reassoc]
theorem filtD_filtIncl {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) (n : ℤ) :
    filtD Osharp 𝒮 δ D n ≫ filtIncl Osharp 𝒮 D (n + 1) =
      filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n := by
  rw [filtD, Category.assoc, Category.assoc, filtIncl_algD_filtProj_filtIncl 𝒮 δ htri hD]

include hδ htri in
/-- For `D` closed downwards, the differential of `F_D` squares to zero. -/
theorem filtD_comp_filtD {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) (n : ℤ) :
    filtD Osharp 𝒮 δ D n ≫ filtD Osharp 𝒮 δ D (n + 1) = 0 := by
  rw [filtD, filtD, Category.assoc, Category.assoc,
    ← Category.assoc (filtProj Osharp 𝒮 D (n + 1)) (filtIncl Osharp 𝒮 D (n + 1)),
    ← Category.assoc (algD 𝒮 δ n), ← Category.assoc (filtIncl Osharp 𝒮 D n),
    show filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n ≫ filtProj Osharp 𝒮 D (n + 1) ≫
        filtIncl Osharp 𝒮 D (n + 1) = filtIncl Osharp 𝒮 D n ≫ algD 𝒮 δ n from
      filtIncl_algD_filtProj_filtIncl 𝒮 δ htri hD n,
    Category.assoc, ← Category.assoc (algD 𝒮 δ n), algD_comp_algD 𝒮 δ hδ, zero_comp,
    comp_zero]

variable (Osharp) in
/-- **The complex `F_D`** of `O`-modules, for `D` closed downwards. -/
noncomputable def filtComplex {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) :
    CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ :=
  CochainComplex.of (filtPiece Osharp 𝒮 D) (filtD Osharp 𝒮 δ D)
    (filtD_comp_filtD 𝒮 δ hδ htri hD)

/-- The degree-`n` term of `F_D` is `filtPiece D n`. -/
theorem filtComplex_X {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) (n : ℤ) :
    (filtComplex Osharp 𝒮 δ hδ htri hD).X n = filtPiece Osharp 𝒮 D n := rfl

/-- The differential of the complex `F_D` in degree `n` is `filtD D n`. -/
@[simp] theorem filtComplex_d {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) (n : ℤ) :
    (filtComplex Osharp 𝒮 δ hδ htri hD).d n (n + 1) = filtD Osharp 𝒮 δ D n :=
  CochainComplex.of_d _ _ n

/-- **The inclusion of `F_D` into `O⟨S⟩` is a morphism of complexes.** -/
noncomputable def filtComplexIncl {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) :
    filtComplex Osharp 𝒮 δ hδ htri hD ⟶ algComplex 𝒮 δ hδ where
  f n := filtIncl Osharp 𝒮 D n
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [filtComplex_d, algComplex_d]
    exact (filtD_filtIncl 𝒮 δ htri hD i).symm

include htri in
/-- For `D ⊆ E` with `D` closed downwards, the inclusion of `F_D` into `F_E` commutes with the
differentials. -/
theorem filtMap_filtD {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (hD : IsWeightLower D) (n : ℤ) :
    filtMap Osharp 𝒮 h n ≫ filtD Osharp 𝒮 δ E n =
      filtD Osharp 𝒮 δ D n ≫ filtMap Osharp 𝒮 h (n + 1) := by
  rw [filtD, filtD, filtMap_filtIncl_assoc,
    ← filtIncl_algD_filtProj_filtIncl_assoc 𝒮 δ htri hD n, filtIncl_filtProj_of_subset 𝒮 h]
  simp only [Category.assoc]

/-- **The inclusion of `F_D` into `F_E` is a morphism of complexes.** -/
noncomputable def filtComplexMap {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (hD : IsWeightLower D)
    (hE : IsWeightLower E) :
    filtComplex Osharp 𝒮 δ hδ htri hD ⟶ filtComplex Osharp 𝒮 δ hδ htri hE where
  f n := filtMap Osharp 𝒮 h n
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [filtComplex_d, filtComplex_d]
    exact filtMap_filtD 𝒮 δ htri h hD i

/-- The degree-`n` component of `filtComplexMap` is `filtMap`. -/
theorem filtComplexMap_f {D E : Set (I →₀ ℕ)} (h : D ⊆ E) (hD : IsWeightLower D)
    (hE : IsWeightLower E) (n : ℤ) :
    (filtComplexMap 𝒮 δ hδ htri h hD hE).f n = filtMap Osharp 𝒮 h n := rfl

/-- The inclusions of complexes `F_D ⟶ F_E ⟶ F_G` compose to the inclusion `F_D ⟶ F_G`. -/
theorem filtComplexMap_comp {D E G : Set (I →₀ ℕ)} (h : D ⊆ E) (h' : E ⊆ G)
    (hD : IsWeightLower D) (hE : IsWeightLower E) (hG : IsWeightLower G) :
    filtComplexMap 𝒮 δ hδ htri h hD hE ≫ filtComplexMap 𝒮 δ hδ htri h' hE hG =
      filtComplexMap 𝒮 δ hδ htri (h.trans h') hD hG :=
  HomologicalComplex.hom_ext _ _ fun n => filtMap_filtMap 𝒮 h h' n

/-- The inclusion of the complex `F_D` into itself is the identity. -/
theorem filtComplexMap_refl {D : Set (I →₀ ℕ)} (hD : IsWeightLower D) :
    filtComplexMap 𝒮 δ hδ htri (subset_refl D) hD hD = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n => filtMap_refl 𝒮 D n

/-! ### The split short exact sequence at a weight -/

/-- The weights at most `w`. -/
def weightLE (w : Colex (I →₀ ℕ)) : Set (I →₀ ℕ) := {v | toColex v ≤ w}

/-- The weights strictly below `w`. -/
def weightLT (w : Colex (I →₀ ℕ)) : Set (I →₀ ℕ) := {v | toColex v < w}

/-- The weight `w`. -/
def weightEQ (w : Colex (I →₀ ℕ)) : Set (I →₀ ℕ) := {v | toColex v = w}

/-- The weights at most `w` are closed downwards. -/
theorem isWeightLower_weightLE (w : Colex (I →₀ ℕ)) : IsWeightLower (weightLE w) := by
  rintro v ⟨u, hu, hvu⟩
  exact le_of_lt (lt_of_lt_of_le hvu (show toColex u ≤ w from hu))

/-- The weights strictly below `w` are closed downwards. -/
theorem isWeightLower_weightLT (w : Colex (I →₀ ℕ)) : IsWeightLower (weightLT w) := by
  rintro v ⟨u, hu, hvu⟩
  exact lt_trans hvu (show toColex u < w from hu)

/-- A weight strictly below `w` is at most `w`. -/
theorem weightLT_subset_weightLE (w : Colex (I →₀ ℕ)) : weightLT w ⊆ weightLE w :=
  fun _ h => le_of_lt (show _ < w from h)

/-- No weight strictly below `w` equals `w`. -/
theorem disjoint_weightLT_weightEQ (w : Colex (I →₀ ℕ)) : Disjoint (weightLT w) (weightEQ w) :=
  Set.disjoint_left.mpr fun _ h h' => (ne_of_lt (show _ < w from h)) h'

/-- No weight strictly below a weight at most `w` equals `w`. -/
theorem disjoint_strictBelow_weightLE_weightEQ (w : Colex (I →₀ ℕ)) :
    Disjoint (strictBelow (weightLE w)) (weightEQ w) :=
  Set.disjoint_left.mpr fun _ ⟨_, hu, hvu⟩ h' =>
    (ne_of_lt (lt_of_lt_of_le hvu (show _ ≤ w from hu))) h'

/-- The weights at most `v` are at most `v'` when `v ≤ v'`. -/
theorem weightLE_mono {v v' : Colex (I →₀ ℕ)} (h : v ≤ v') : weightLE v ⊆ weightLE v' :=
  fun _ hu => le_trans (show _ ≤ v from hu) h

/-- Every weight is at most itself. -/
theorem mem_weightLE_self (u : I →₀ ℕ) : u ∈ weightLE (toColex u) :=
  show toColex u ≤ toColex u from le_refl _

/-- The weights at most `v` are strictly below `w` when `v < w`. -/
theorem weightLE_subset_weightLT {v w : Colex (I →₀ ℕ)} (h : v < w) : weightLE v ⊆ weightLT w :=
  fun _ hu => lt_of_le_of_lt (show _ ≤ v from hu) h

/-- A weight equal to `w` is at most `w`. -/
theorem weightEQ_subset_weightLE (w : Colex (I →₀ ℕ)) : weightEQ w ⊆ weightLE w :=
  fun _ h => le_of_eq (show _ = w from h)

/-- The words of weight `w`, degree by degree. -/
noncomputable abbrev weightPiecePresheaves (w : Colex (I →₀ ℕ)) : ℤ → (Cᵒᵖ ⥤ Type t) :=
  fun n => (wordsIn 𝒮 (weightEQ w) n).toFunctor

section Generators

variable (w : Colex (I →₀ ℕ)) (n : ℤ) {U : Cᵒᵖ}

/-- The map `F_{≤w} ⟶ F_{<w}` sends the generator of a word of weight below `w` to its
generator. -/
theorem gen_LE_LT (u : (wordsIn 𝒮 (weightLE w) n).toFunctor.obj U)
    (h : u.1 ∈ (wordsIn 𝒮 (weightLT w) n).obj U) :
    (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightLT w) n).val.app U
        (freeGen Osharp u) =
      freeGen Osharp (⟨u.1, h⟩ : (wordsIn 𝒮 (weightLT w) n).toFunctor.obj U) :=
  (congrArg (fun z => (filtProj Osharp 𝒮 (weightLT w) n).val.app U z) (filtIncl_gen 𝒮 _ u)).trans
    (filtProj_gen_of_mem 𝒮 _ u.1 h)

/-- The map `F_{≤w} ⟶ F_{<w}` kills the generator of a word not of weight below `w`. -/
theorem gen_LE_LT_zero (u : (wordsIn 𝒮 (weightLE w) n).toFunctor.obj U)
    (h : u.1 ∉ (wordsIn 𝒮 (weightLT w) n).obj U) :
    (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightLT w) n).val.app U
        (freeGen Osharp u) = 0 :=
  (congrArg (fun z => (filtProj Osharp 𝒮 (weightLT w) n).val.app U z) (filtIncl_gen 𝒮 _ u)).trans
    (filtProj_gen_of_not_mem 𝒮 _ u.1 h)

/-- The map `F_{≤w} ⟶ F_{=w}` sends the generator of a word of weight `w` to its generator. -/
theorem gen_LE_EQ (u : (wordsIn 𝒮 (weightLE w) n).toFunctor.obj U)
    (h : u.1 ∈ (wordsIn 𝒮 (weightEQ w) n).obj U) :
    (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n).val.app U
        (freeGen Osharp u) =
      freeGen Osharp (⟨u.1, h⟩ : (wordsIn 𝒮 (weightEQ w) n).toFunctor.obj U) :=
  (congrArg (fun z => (filtProj Osharp 𝒮 (weightEQ w) n).val.app U z) (filtIncl_gen 𝒮 _ u)).trans
    (filtProj_gen_of_mem 𝒮 _ u.1 h)

/-- The map `F_{≤w} ⟶ F_{=w}` kills the generator of a word not of weight `w`. -/
theorem gen_LE_EQ_zero (u : (wordsIn 𝒮 (weightLE w) n).toFunctor.obj U)
    (h : u.1 ∉ (wordsIn 𝒮 (weightEQ w) n).obj U) :
    (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n).val.app U
        (freeGen Osharp u) = 0 :=
  (congrArg (fun z => (filtProj Osharp 𝒮 (weightEQ w) n).val.app U z) (filtIncl_gen 𝒮 _ u)).trans
    (filtProj_gen_of_not_mem 𝒮 _ u.1 h)

/-- The map `F_{=w} ⟶ F_{≤w}` sends the generator of a word to the generator of the same word. -/
theorem gen_EQ_LE (u : (wordsIn 𝒮 (weightEQ w) n).toFunctor.obj U) :
    (filtIncl Osharp 𝒮 (weightEQ w) n ≫ filtProj Osharp 𝒮 (weightLE w) n).val.app U
        (freeGen Osharp u) = freeGen Osharp (⟨u.1, weightEQ_subset_weightLE w u.2⟩ :
          (wordsIn 𝒮 (weightLE w) n).toFunctor.obj U) :=
  (congrArg (fun z => (filtProj Osharp 𝒮 (weightLE w) n).val.app U z) (filtIncl_gen 𝒮 _ u)).trans
    (filtProj_gen_of_mem 𝒮 _ u.1 _)

end Generators

include htri in
/-- The differential of `F_{≤w}` followed by the projection on the weight `w` part is zero. -/
theorem weightProj_d (w : Colex (I →₀ ℕ)) (i : ℤ) :
    filtD Osharp 𝒮 δ (weightLE w) i ≫ filtIncl Osharp 𝒮 (weightLE w) (i + 1) ≫
      filtProj Osharp 𝒮 (weightEQ w) (i + 1) = 0 := by
  rw [filtD_filtIncl_assoc 𝒮 δ htri (isWeightLower_weightLE w)]
  refine freePieceOf_hom_ext fun U u => ?_
  change (filtProj Osharp 𝒮 (weightEQ w) (i + 1)).val.app U
      ((algD 𝒮 δ i).val.app U ((filtIncl Osharp 𝒮 (weightLE w) i).val.app U (freeGen Osharp u))) =
    (0 : filtPiece Osharp 𝒮 (weightLE w) i ⟶ _).val.app U (freeGen Osharp u)
  rw [(filtIncl_gen 𝒮 _ u).trans (freeGen_eq_algToSheaf 𝒮 u.1),
    filtProj_eq_zero_of_isLocallyIn 𝒮 (disjoint_strictBelow_weightLE_weightEQ w)
      (algD_isLocallyIn δ htri (IsPresIn.algOf (D := weightLE w) u.1 u.2 1))]
  rfl

/-- The projection of `F_{≤w}` on its weight `w` part, a morphism of complexes onto the free
complex with zero differential on the words of weight `w`. -/
noncomputable def weightProj (w : Colex (I →₀ ℕ)) :
    filtComplex Osharp 𝒮 δ hδ htri (isWeightLower_weightLE w) ⟶
      freeOnPresheavesComplex Osharp (weightPiecePresheaves 𝒮 w) where
  f n := filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [freeOnPresheavesComplex_d, comp_zero, filtComplex_d]
    exact (weightProj_d 𝒮 δ htri w i).symm

/-- The degree-`n` component of `weightProj w`. -/
theorem weightProj_f (w : Colex (I →₀ ℕ)) (n : ℤ) :
    (weightProj 𝒮 δ hδ htri w).f n =
      filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n := rfl

/-- In each degree, the inclusion `F_{<w} ⟶ F_{≤w}` followed by the projection on the weight `w`
part is zero. -/
theorem weightIncl_weightProj_f (w : Colex (I →₀ ℕ)) (n : ℤ) :
    filtMap Osharp 𝒮 (weightLT_subset_weightLE w) n ≫ filtIncl Osharp 𝒮 (weightLE w) n ≫
      filtProj Osharp 𝒮 (weightEQ w) n = 0 :=
  (filtMap_filtIncl_assoc 𝒮 _ n _).trans
    (filtIncl_filtProj_of_disjoint 𝒮 (disjoint_weightLT_weightEQ w) n)

/-- The inclusion of complexes `F_{<w} ⟶ F_{≤w}` followed by `weightProj w` is zero. -/
theorem weightIncl_weightProj (w : Colex (I →₀ ℕ)) :
    filtComplexMap 𝒮 δ hδ htri (weightLT_subset_weightLE w) (isWeightLower_weightLT w)
        (isWeightLower_weightLE w) ≫ weightProj 𝒮 δ hδ htri w = 0 :=
  HomologicalComplex.hom_ext _ _ fun n => weightIncl_weightProj_f 𝒮 w n

/-- **The short exact sequence `0 ⟶ F_{<w} ⟶ F_{≤w} ⟶ (weight w part) ⟶ 0`.** -/
noncomputable abbrev weightShortComplex (w : Colex (I →₀ ℕ)) :
    ShortComplex (CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ) :=
  ShortComplex.mk _ _ (weightIncl_weightProj 𝒮 δ hδ htri w)

/-- The projection `F_{≤w} ⟶ F_{<w}` is a retraction of the inclusion `F_{<w} ⟶ F_{≤w}`. -/
theorem weightSplitting_f_r (w : Colex (I →₀ ℕ)) (n : ℤ) :
    filtMap Osharp 𝒮 (weightLT_subset_weightLE w) n ≫ filtIncl Osharp 𝒮 (weightLE w) n ≫
      filtProj Osharp 𝒮 (weightLT w) n = 𝟙 _ := by
  rw [filtMap_filtIncl_assoc, filtIncl_filtProj]

/-- The map `F_{=w} ⟶ F_{≤w}` is a section of the projection on the weight `w` part. -/
theorem weightSplitting_s_g (w : Colex (I →₀ ℕ)) (n : ℤ) :
    (filtIncl Osharp 𝒮 (weightEQ w) n ≫ filtProj Osharp 𝒮 (weightLE w) n) ≫
      filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n = 𝟙 _ :=
  freePieceOf_hom_ext fun U u =>
    (congrArg (fun z => (filtIncl Osharp 𝒮 (weightLE w) n ≫
        filtProj Osharp 𝒮 (weightEQ w) n).val.app U z) (gen_EQ_LE 𝒮 w n u)).trans
      (gen_LE_EQ 𝒮 w n _ u.2)

/-- In each degree, `F_{≤w}` is the direct sum of `F_{<w}` and the weight `w` part: the two
idempotents sum to the identity. -/
theorem weightSplitting_id (w : Colex (I →₀ ℕ)) (n : ℤ) :
    (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightLT w) n) ≫
        filtMap Osharp 𝒮 (weightLT_subset_weightLE w) n +
      (filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n) ≫
        filtIncl Osharp 𝒮 (weightEQ w) n ≫ filtProj Osharp 𝒮 (weightLE w) n = 𝟙 _ := by
  refine freePieceOf_hom_ext fun U u => ?_
  rw [SheafOfModules.add_val, PresheafOfModules.add_app]
  change (filtMap Osharp 𝒮 (weightLT_subset_weightLE w) n).val.app U
      ((filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightLT w) n).val.app U
        (freeGen Osharp u)) +
    (filtIncl Osharp 𝒮 (weightEQ w) n ≫ filtProj Osharp 𝒮 (weightLE w) n).val.app U
      ((filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightEQ w) n).val.app U
        (freeGen Osharp u)) = freeGen Osharp u
  rcases lt_or_eq_of_le (show toColex (wordWt u.1.1) ≤ w from u.2) with h | h
  · rw [gen_LE_LT 𝒮 w n u h, gen_LE_EQ_zero 𝒮 w n u (ne_of_lt h), map_zero, add_zero]
    exact filtMap_gen 𝒮 (weightLT_subset_weightLE w)
      (⟨u.1, h⟩ : (wordsIn 𝒮 (weightLT w) n).toFunctor.obj U)
  · rw [gen_LE_LT_zero 𝒮 w n u (fun h' => ne_of_lt (show _ < w from h') h),
      gen_LE_EQ 𝒮 w n u h, map_zero, zero_add]
    exact gen_EQ_LE 𝒮 w n (⟨u.1, h⟩ : (wordsIn 𝒮 (weightEQ w) n).toFunctor.obj U)

/-- **The short exact sequence at `w` is split in every degree.** -/
noncomputable def weightSplitting (w : Colex (I →₀ ℕ)) (n : ℤ) :
    ((weightShortComplex 𝒮 δ hδ htri w).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := filtIncl Osharp 𝒮 (weightLE w) n ≫ filtProj Osharp 𝒮 (weightLT w) n
  s := filtIncl Osharp 𝒮 (weightEQ w) n ≫ filtProj Osharp 𝒮 (weightLE w) n
  f_r := weightSplitting_f_r 𝒮 w n
  s_g := weightSplitting_s_g 𝒮 w n
  id := weightSplitting_id 𝒮 w n

/-! ### Diagrams of stages of the weight filtration -/

section Diagram

variable {K : Type t} [Preorder K] (D : K → Set (I →₀ ℕ)) (hmono : Monotone D)
  (hD : ∀ k, IsWeightLower (D k))

/-- The stages `F_{D k}` of the weight filtration along a monotone family of sets of weights. -/
noncomputable def filtDiagram : K ⥤ DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp) where
  obj k := ofComplex (filtComplex Osharp 𝒮 δ hδ htri (hD k))
  map {k k'} h := homMk (filtComplexMap 𝒮 δ hδ htri (hmono (leOfHom h)) (hD k) (hD k'))
  map_id k := DifferentialGradedModule.Hom.ext fun n => filtMap_refl 𝒮 (D k) n
  map_comp h h' := DifferentialGradedModule.Hom.ext fun n =>
    (filtMap_filtMap 𝒮 (hmono (leOfHom h)) (hmono (leOfHom h')) n).symm

/-- The cocone of the stages `F_{D k}` to `F_E`, for `D k ⊆ E`. -/
noncomputable def filtCocone (E : Set (I →₀ ℕ)) (hE : IsWeightLower E) (hle : ∀ k, D k ⊆ E) :
    Cocone (filtDiagram 𝒮 δ hδ htri D hmono hD) where
  pt := ofComplex (filtComplex Osharp 𝒮 δ hδ htri hE)
  ι :=
    { app k := homMk (filtComplexMap 𝒮 δ hδ htri (hle k) (hD k) hE)
      naturality {k k'} h := DifferentialGradedModule.Hom.ext fun n => by
        change filtMap Osharp 𝒮 (hmono (leOfHom h)) n ≫ filtMap Osharp 𝒮 (hle k') n =
          filtMap Osharp 𝒮 (hle k) n ≫ 𝟙 _
        rw [Category.comp_id]
        exact filtMap_filtMap 𝒮 (hmono (leOfHom h)) (hle k') n }

/-- **`F_E` is the colimit of the `F_{D k}` when the `D k` exhaust `E`**, the index set being
directed: degreewise, the words of weight in `E` are the directed union of those of weight in
some `D k`, and the sheafified free module functor preserves colimits. -/
noncomputable def filtCocone_isColimit [IsDirected K (· ≤ ·)] [Nonempty K]
    (E : Set (I →₀ ℕ)) (hE : IsWeightLower E) (hle : ∀ k, D k ⊆ E)
    (hcov : ∀ v ∈ E, ∃ k, v ∈ D k) :
    IsColimit (filtCocone 𝒮 δ hδ htri D hmono hD E hE hle) :=
  isColimitOfDegreewise _ fun n =>
    isColimit_freePieceMapCocone (Osharp := Osharp)
      (isColimitSubfunctorUnion (fun k => wordsIn 𝒮 (D k) n) (wordsIn 𝒮 E n)
        (fun _ _ h => wordsIn_mono 𝒮 (hmono h) n) (fun k => wordsIn_mono 𝒮 (hle k) n)
        (fun _ _ hx => hcov _ hx |>.imp fun _ h => h))

end Diagram

/-! ### The induction over the weights -/

/-- When no weight lies strictly below `w`, the differential of `F_{<w}` is zero. -/
theorem filtD_eq_zero_of_minimal (w : Colex (I →₀ ℕ)) (hw : ∀ v, ¬ v < w) (i : ℤ) :
    filtD Osharp 𝒮 δ (weightLT w) i = 0 :=
  freePieceOf_hom_ext fun _ (u : (wordsIn 𝒮 (weightLT w) i).toFunctor.obj _) =>
    absurd (show toColex (wordWt u.1.1) < w from u.2) (hw _)

/-- When no weight lies strictly below `w`, the stage `F_{<w}` has no generators, and is the
free complex with zero differential on the empty presheaves. -/
noncomputable def filtLTIsoOfMinimal (w : Colex (I →₀ ℕ)) (hw : ∀ v, ¬ v < w) :
    filtComplex Osharp 𝒮 δ hδ htri (isWeightLower_weightLT w) ≅
      freeOnPresheavesComplex Osharp (fun n => (wordsIn 𝒮 (weightLT w) n).toFunctor) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    have hij' : i + 1 = j := hij
    subst hij'
    simp only [Iso.refl_hom]
    rw [filtComplex_d, filtD_eq_zero_of_minimal 𝒮 δ w hw i]
    rfl)

/-- The stage `F_D` for `D` all weights is `O⟨S⟩` itself. -/
noncomputable def filtUnivIso :
    filtComplex Osharp 𝒮 δ hδ htri (D := Set.univ) (fun _ _ => trivial) ≅
      algComplex (Osharp := Osharp) 𝒮 δ hδ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := filtIncl Osharp 𝒮 Set.univ n
        inv := filtProj Osharp 𝒮 Set.univ n
        hom_inv_id := filtIncl_filtProj 𝒮 Set.univ n
        inv_hom_id := freePieceOf_hom_ext fun U u =>
          (congrArg (fun z => (filtIncl Osharp 𝒮 Set.univ n).val.app U z)
            (filtProj_gen_of_mem 𝒮 Set.univ u trivial)).trans (filtIncl_gen 𝒮 Set.univ _) })
    (fun i j _ => (filtComplexIncl 𝒮 δ hδ htri (D := Set.univ) (fun _ _ => trivial)).comm i j)

/-! ### The stages `Aᵢ` of the tower -/

/-- The weights of the words in letters of level at most `i`. -/
def levelLE (i : I) : Set (I →₀ ℕ) := {v | ∀ j ∈ v.support, j ≤ i}

/-- The words in letters of level at most `i` span a subcomplex: a weight colexicographically
below one supported on levels `≤ i` is again supported on levels `≤ i`. -/
theorem isWeightLower_levelLE (i : I) : IsWeightLower (levelLE i) := by
  rintro v ⟨u, hu, hvu⟩ j hj
  obtain ⟨j₀, hj₀, hlt⟩ := Finsupp.Colex.lt_iff.mp hvu
  by_contra hji
  have hij : i < j := lt_of_not_ge hji
  have hu0 : ∀ k, i < k → u k = 0 := fun k hk =>
    Finsupp.notMem_support_iff.mp fun hk' => absurd (hu k hk') (not_le.mpr hk)
  by_cases hj₀j : j₀ < j
  · have := hj₀ j hj₀j
    change v j = u j at this
    exact (Finsupp.mem_support_iff.mp hj) (this.trans (hu0 j hij))
  · have hj₀i : i < j₀ := lt_of_lt_of_le hij (not_lt.mp hj₀j)
    change v j₀ < u j₀ at hlt
    rw [hu0 j₀ hj₀i] at hlt
    exact Nat.not_lt_zero _ hlt

/-- The weights supported on levels at most `i` grow with `i`. -/
theorem levelLE_mono : Monotone (levelLE (I := I)) :=
  fun _ _ h _ hv j hj => le_trans (hv j hj) h

/-- **`O⟨S⟩` is the colimit of the stages `Aᵢ`**, the subcomplexes spanned by the words in
letters of level at most `i`: `A = colim Aᵢ`. -/
noncomputable def stagesCocone_isColimit [Nonempty I] :
    IsColimit (filtCocone 𝒮 δ hδ htri levelLE levelLE_mono isWeightLower_levelLE Set.univ
      (fun _ _ => trivial) (fun _ _ _ => trivial)) := by
  refine filtCocone_isColimit 𝒮 δ hδ htri _ _ _ _ _ _ fun v _ => ?_
  by_cases hv : v.support.Nonempty
  · exact ⟨v.support.max' hv, fun j hj => v.support.le_max' j hj⟩
  · obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨i, fun j hj => absurd ⟨j, hj⟩ hv⟩

end Complex

end SheafOfModules

end
