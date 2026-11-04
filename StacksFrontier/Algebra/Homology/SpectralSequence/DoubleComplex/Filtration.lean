module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksCore.Algebra.Homology.TotalComplex

/-!
# Spectral sequences of double complexes: the filtrations

For a double complex `K^{•,•}`, the total complex `Tot(K^{•,•})` carries the two filtrations
`F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}` and `F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j}`,
whose steps are the images of idempotents of `Tot^n` projecting onto sets of summands. The
zero-th page object of the associated spectral sequence in position `(p, n)` is `K^{i,j}` when
this is the only summand of `Tot^n` of weight `p`.

## Main definitions

* `HomologicalComplex₂.totalProjector`: the idempotent of `Tot^n` projecting onto the summands
  `K^{i,j}` satisfying a predicate.
* `HomologicalComplex₂.totalFiltration`: the filtration of the total complex by a weight which
  increases along both differentials.
* `HomologicalComplex₂.totalFiltration₁`, `HomologicalComplex₂.totalFiltration₂`: the filtrations
  by the first and the second coordinate.
* `HomologicalComplex₂.zeroPageObjectIso`: the identification of a zero-th page object with a
  summand `K^{i,j}`.

## Main results

* `HomologicalComplex₂.isLeast_totalFiltration₁`, `HomologicalComplex₂.isLeast_totalFiltration₂`:
  the steps of the two filtrations are the least subobjects containing the relevant summands.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The restriction of `f : X ⟶ Y` to the image of `e : X ⟶ X` factors through the image of
`e' : Y ⟶ Y` as soon as `e ≫ f ≫ e' = e ≫ f`. -/
lemma imageSubobject_factors_arrow_comp_of_comp_eq {X Y : C} (e : X ⟶ X) (e' : Y ⟶ Y) (f : X ⟶ Y)
    (h : e ≫ f ≫ e' = e ≫ f) :
    (imageSubobject e').Factors ((imageSubobject e).arrow ≫ f) := by
  have hfac : (imageSubobject e).arrow ≫ f =
      ((imageSubobject e).arrow ≫ f ≫ factorThruImageSubobject e') ≫
        (imageSubobject e').arrow := by
    rw [Category.assoc, Category.assoc, imageSubobject_arrow_comp,
      ← cancel_epi (factorThruImageSubobject e), ← Category.assoc, imageSubobject_arrow_comp,
      ← Category.assoc, imageSubobject_arrow_comp, h]
  rw [hfac]
  exact Subobject.factors_comp_arrow _

end CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} {c : ComplexShape I}

/-- The subcomplex of a homological complex `L` cut out by a family of subobjects `F n ⊆ L.X n`
stable under the differential. -/
noncomputable abbrev subcomplexOfSubobjects (L : HomologicalComplex C c)
    (F : ∀ n, Subobject (L.X n)) (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) :
    HomologicalComplex C c where
  X n := (F n : C)
  d i j := (F j).factorThru ((F i).arrow ≫ L.d i j) (hF i j)
  shape i j h := by simp [L.shape i j h]
  d_comp_d' i j k _ _ := by
    rw [← cancel_mono (F k).arrow, Category.assoc, Subobject.factorThru_arrow, zero_comp,
      ← Category.assoc, Subobject.factorThru_arrow, Category.assoc, L.d_comp_d, comp_zero]

/-- The inclusion of `subcomplexOfSubobjects L F hF` into `L`. -/
noncomputable abbrev subcomplexOfSubobjectsι (L : HomologicalComplex C c)
    (F : ∀ n, Subobject (L.X n)) (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) :
    subcomplexOfSubobjects L F hF ⟶ L where
  f n := (F n).arrow
  comm' i j _ := (Subobject.factorThru_arrow _ _ (hF i j)).symm

@[simp]
lemma subcomplexOfSubobjectsι_f (L : HomologicalComplex C c)
    (F : ∀ n, Subobject (L.X n)) (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) (n : I) :
    (subcomplexOfSubobjectsι L F hF).f n = (F n).arrow :=
  rfl

instance (L : HomologicalComplex C c) (F : ∀ n, Subobject (L.X n))
    (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) :
    Mono (subcomplexOfSubobjectsι L F hF) :=
  mono_of_mono_f _ fun n => inferInstanceAs (Mono (F n).arrow)

/-- The inclusion of subcomplexes induced by an inclusion of the families of subobjects. -/
noncomputable def subcomplexOfSubobjectsMap (L : HomologicalComplex C c)
    {F G : ∀ n, Subobject (L.X n)} (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j))
    (hG : ∀ i j, (G j).Factors ((G i).arrow ≫ L.d i j)) (h : ∀ n, F n ≤ G n) :
    subcomplexOfSubobjects L F hF ⟶ subcomplexOfSubobjects L G hG where
  f n := Subobject.ofLE _ _ (h n)
  comm' i j _ := by
    rw [← cancel_mono (G j).arrow]
    simp

@[simp]
lemma subcomplexOfSubobjectsMap_f (L : HomologicalComplex C c)
    {F G : ∀ n, Subobject (L.X n)} (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j))
    (hG : ∀ i j, (G j).Factors ((G i).arrow ≫ L.d i j)) (h : ∀ n, F n ≤ G n) (n : I) :
    (subcomplexOfSubobjectsMap L hF hG h).f n = Subobject.ofLE _ _ (h n) :=
  rfl

@[reassoc (attr := simp)]
lemma subcomplexOfSubobjectsMap_ι (L : HomologicalComplex C c)
    {F G : ∀ n, Subobject (L.X n)} (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j))
    (hG : ∀ i j, (G j).Factors ((G i).arrow ≫ L.d i j)) (h : ∀ n, F n ≤ G n) :
    subcomplexOfSubobjectsMap L hF hG h ≫ subcomplexOfSubobjectsι L G hG =
      subcomplexOfSubobjectsι L F hF := by
  ext n
  simp

end HomologicalComplex

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

section Projector

/-- The idempotent of `Tot^n` projecting onto the summands `K^{i,j}` with `P i j`. -/
noncomputable def totalProjector (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (K.total (ComplexShape.up ℤ)).X n :=
  K.totalDesc fun i j h => if P i j then K.ιTotal (ComplexShape.up ℤ) i j n h else 0

variable {K}

@[reassoc]
lemma ι_totalProjector (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (i j n : ℤ)
    (h : i + j = n) :
    K.ιTotal (ComplexShape.up ℤ) i j n h ≫ K.totalProjector P n =
      if P i j then K.ιTotal (ComplexShape.up ℤ) i j n h else 0 :=
  K.ι_totalDesc _ i j h

private theorem totalProjector_comp_totalProjector (P Q : ℤ → ℤ → Prop)
    [∀ i j, Decidable (P i j)] [∀ i j, Decidable (Q i j)] (hPQ : ∀ i j, P i j → Q i j) (n : ℤ) :
    K.totalProjector P n ≫ K.totalProjector Q n = K.totalProjector P n := by
  refine HomologicalComplex₂.total.hom_ext _ fun i j h => ?_
  rw [ι_totalProjector_assoc, ι_totalProjector]
  split_ifs with hP
  · rw [ι_totalProjector, ite_eq_left (hPQ i j hP)]
  · exact zero_comp

lemma totalProjector_idempotent (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ) :
    K.totalProjector P n ≫ K.totalProjector P n = K.totalProjector P n :=
  K.totalProjector_comp_totalProjector P P (fun _ _ => id) n

/-- The summand inclusions of the total complex followed by its differential. -/
@[reassoc]
lemma ι_total_d (i j n : ℤ) (h : i + j = n) :
    K.ιTotal (ComplexShape.up ℤ) i j n h ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1) =
      (K.d i (i + 1)).f j ≫ K.ιTotal (ComplexShape.up ℤ) (i + 1) j (n + 1) (by dsimp; omega) +
        i.negOnePow • ((K.X i).d j (j + 1) ≫
          K.ιTotal (ComplexShape.up ℤ) i (j + 1) (n + 1) (by dsimp; omega)) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂,
    K.d₁_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl) j (n + 1) (by dsimp; omega),
    K.d₂_eq _ i (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl) (n + 1) (by dsimp; omega)]
  simp

/-- A projector onto a set of summands closed under raising either coordinate commutes with the
differential of the total complex, in the sense that its image is a subcomplex. -/
lemma totalProjector_d (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    (h₁ : ∀ i j, P i j → P (i + 1) j) (h₂ : ∀ i j, P i j → P i (j + 1)) (n m : ℤ) :
    K.totalProjector P n ≫ (K.total (ComplexShape.up ℤ)).d n m ≫ K.totalProjector P m =
      K.totalProjector P n ≫ (K.total (ComplexShape.up ℤ)).d n m := by
  by_cases h : n + 1 = m
  · subst h
    refine HomologicalComplex₂.total.hom_ext _ fun i j hij => ?_
    rw [ι_totalProjector_assoc, ι_totalProjector_assoc]
    split_ifs with hP
    · rw [ι_total_d_assoc, ι_total_d, Preadditive.add_comp, Linear.units_smul_comp,
        Category.assoc, Category.assoc, ι_totalProjector, ι_totalProjector, ite_eq_left (h₁ i j hP),
        ite_eq_left (h₂ i j hP)]
    · simp
  · simp [(K.total (ComplexShape.up ℤ)).shape n m h]

lemma totalProjector_le (P Q : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    [∀ i j, Decidable (Q i j)] (hPQ : ∀ i j, P i j → Q i j) (n : ℤ) :
    imageSubobject (K.totalProjector P n) ≤ imageSubobject (K.totalProjector Q n) := by
  refine imageSubobject_le _ (K.totalProjector P n ≫ factorThruImageSubobject _) ?_
  rw [Category.assoc, imageSubobject_arrow_comp]
  exact K.totalProjector_comp_totalProjector P Q hPQ n

/-- The image of `totalProjector P` contains the summands `K^{i,j}` with `P i j`. -/
lemma imageSubobject_ιTotal_le_totalProjector (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    (i j n : ℤ) (h : i + j = n) (hP : P i j) :
    imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≤
      imageSubobject (K.totalProjector P n) := by
  refine imageSubobject_le _ (K.ιTotal (ComplexShape.up ℤ) i j n h ≫ factorThruImageSubobject _) ?_
  rw [Category.assoc, imageSubobject_arrow_comp, ι_totalProjector, ite_eq_left hP]

/-- The image of `totalProjector P` is the least subobject of `Tot^n` containing the summands
`K^{i,j}` with `P i j`. -/
lemma totalProjector_le_of_forall (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    (n : ℤ) (Z : Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hZ : ∀ i j (h : i + j = n), P i j →
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≤ Z) :
    imageSubobject (K.totalProjector P n) ≤ Z := by
  refine imageSubobject_le _ (K.totalDesc fun i j h =>
    if hP : P i j then factorThruImageSubobject _ ≫ Subobject.ofLE _ _ (hZ i j h hP) else 0) ?_
  refine HomologicalComplex₂.total.hom_ext _ fun i j h => ?_
  rw [HomologicalComplex₂.ι_totalDesc_assoc, ι_totalProjector]
  split_ifs <;> simp

end Projector

section Filtration

variable (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))

/-- The `p`-th step `⨁_{w(i, j) ≥ p} K^{i,j}` of the filtration of the total complex by a weight
`w` which increases along both differentials. -/
noncomputable abbrev totalFiltrationStep (p : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.subcomplexOfSubobjects (K.total (ComplexShape.up ℤ))
    (fun n => imageSubobject (K.totalProjector (fun i j => p ≤ w i j) n))
    (fun n m => CategoryTheory.Limits.imageSubobject_factors_arrow_comp_of_comp_eq _ _ _
      (K.totalProjector_d (fun i j => p ≤ w i j) (fun i j h => h.trans (h₁ i j))
        (fun i j h => h.trans (h₂ i j)) n m))

/-- The filtration of the total complex by a weight `w` which increases along both
differentials. -/
noncomputable abbrev totalFiltration : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ where
  X := K.total (ComplexShape.up ℤ)
  filtration := Filtration.ofDiagram
    { obj p := K.totalFiltrationStep w h₁ h₂ p.unop
      map f := HomologicalComplex.subcomplexOfSubobjectsMap _ _ _
        fun n => K.totalProjector_le _ _ (fun _ _ hi => (leOfHom f.unop).trans hi) n
      map_id _ := by ext n; simp
      map_comp _ _ := by ext n; simp }
    { app p := HomologicalComplex.subcomplexOfSubobjectsι _ _ _
      naturality _ _ _ := by ext n; simp }

lemma mk_totalFiltration_ι_f (p n : ℤ) :
    Subobject.mk (((K.totalFiltration w h₁ h₂).filtration.ι.app (op p)).f n) =
      imageSubobject (K.totalProjector (fun i j => p ≤ w i j) n) :=
  Subobject.mk_arrow _

end Filtration

/-- The total complex of a double complex filtered by the first coordinate:
`F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}`. -/
noncomputable abbrev totalFiltration₁ : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ :=
  K.totalFiltration (fun i _ => i) (fun _ _ => by omega) (fun _ _ => le_rfl)

/-- The total complex of a double complex filtered by the second coordinate:
`F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j}`. -/
noncomputable abbrev totalFiltration₂ : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ :=
  K.totalFiltration (fun _ j => j) (fun _ _ => le_rfl) (fun _ _ => by omega)

/-- The characterization of the steps of the filtration by a weight `w`, shared by the two
filtrations by a coordinate. -/
private theorem isLeast_totalFiltration_aux (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j)
    (h₂ : ∀ i j, w i j ≤ w i (j + 1))
    (F : ∀ (_p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hF : ∀ p n : ℤ,
      F p n = Subobject.mk (((K.totalFiltration w h₁ h₂).filtration.ι.app (op p)).f n)) :
    (∀ (p i j n : ℤ) (hij : i + j = n), p ≤ w i j →
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ F p n) ∧
    (∀ (p n : ℤ) (W : Subobject ((K.total (ComplexShape.up ℤ)).X n)),
      (∀ (i j : ℤ) (hij : i + j = n), p ≤ w i j →
        imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ W) → F p n ≤ W) ∧
    (∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) := by
  refine ⟨fun p i j n hij hi => ?_, fun p n W hW => ?_, fun p p' n hp => ?_⟩
  · rw [hF, K.mk_totalFiltration_ι_f]
    exact K.imageSubobject_ιTotal_le_totalProjector _ i j n hij hi
  · rw [hF, K.mk_totalFiltration_ι_f]
    exact K.totalProjector_le_of_forall _ n W hW
  · rw [hF, hF, K.mk_totalFiltration_ι_f, K.mk_totalFiltration_ι_f]
    exact K.totalProjector_le _ _ (fun _ _ hi => hp.trans hi) n

/-- **Stacks 0130, the first filtration is the one intended.** The degreewise steps `F p n` of the
filtration of `Tot(K^{•,•})` by the first coordinate are `F_I^p Tot^n = ⨁_{i + j = n, i ≥ p}
K^{i,j}`, characterized without arbitrary suprema of subobjects: `F p n` contains the image of
every summand inclusion `K^{i,j} ⟶ Tot^n` with `i ≥ p`, and it is the least subobject of `Tot^n`
that does. Consequently the filtration is decreasing in `p`. Together with
`exists_iso_pages_totalFiltration₁`, which is stated for the same `F` under the same hypothesis
`hF`, this is the content of [Stacks, Tag 0130] for the first filtration: the identifications of
the pages there are identifications for *this* filtration. -/
@[stacks 0130 "the first filtration is ⨁_{i ≥ p} K^{i,j}"]
public theorem isLeast_totalFiltration₁
    (F : ∀ (_p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₁.filtration.ι.app (op p)).f n)) :
    (∀ (p i j n : ℤ) (hij : i + j = n), p ≤ i →
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ F p n) ∧
    (∀ (p n : ℤ) (W : Subobject ((K.total (ComplexShape.up ℤ)).X n)),
      (∀ (i j : ℤ) (hij : i + j = n), p ≤ i →
        imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ W) → F p n ≤ W) ∧
    (∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) :=
  K.isLeast_totalFiltration_aux _ (fun _ _ => by omega) (fun _ _ => le_rfl) F hF

/-- **Stacks 0130, the second filtration is the one intended.** The degreewise steps `F p n` of the
filtration of `Tot(K^{•,•})` by the second coordinate are `F_{II}^p Tot^n =
⨁_{i + j = n, j ≥ p} K^{i,j}`, characterized without arbitrary suprema of subobjects: `F p n`
contains the image of every summand inclusion `K^{i,j} ⟶ Tot^n` with `j ≥ p`, and it is the least
subobject of `Tot^n` that does. Consequently the filtration is decreasing in `p`. Together with
`exists_iso_pages_totalFiltration₂`, which is stated for the same `F` under the same hypothesis
`hF`, this is the content of [Stacks, Tag 0130] for the second filtration: the identifications of
the pages there are identifications for *this* filtration. -/
@[stacks 0130 "the second filtration is ⨁_{j ≥ p} K^{i,j}"]
public theorem isLeast_totalFiltration₂
    (F : ∀ (_p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₂.filtration.ι.app (op p)).f n)) :
    (∀ (p i j n : ℤ) (hij : i + j = n), p ≤ j →
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ F p n) ∧
    (∀ (p n : ℤ) (W : Subobject ((K.total (ComplexShape.up ℤ)).X n)),
      (∀ (i j : ℤ) (hij : i + j = n), p ≤ j →
        imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ W) → F p n ≤ W) ∧
    (∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) :=
  K.isLeast_totalFiltration_aux _ (fun _ _ => le_rfl) (fun _ _ => by omega) F hF

section Summands

variable {K}

/-- The projection of `Tot^n` onto its summand `K^{i,j}`, for `i + j = n`. -/
noncomputable def totalSummandπ (i j n : ℤ) (h : i + j = n) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X i).X j :=
  K.totalDesc fun a b hab =>
    if ha : a = i then (K.XXIsoOfEq _ _ _ ha (by dsimp at hab; omega)).hom else 0

@[reassoc (attr := simp)]
lemma ι_totalSummandπ (i j n : ℤ) (h : i + j = n) :
    K.ιTotal (ComplexShape.up ℤ) i j n h ≫ totalSummandπ i j n h = 𝟙 _ := by
  simp [totalSummandπ]

@[reassoc]
lemma ι_totalSummandπ_of_ne (i j a b n : ℤ) (h : i + j = n) (hab : a + b = n) (ha : a ≠ i) :
    K.ιTotal (ComplexShape.up ℤ) a b n hab ≫ totalSummandπ i j n h = 0 := by
  simp [totalSummandπ, ha]

@[reassoc]
lemma totalProjector_totalSummandπ (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (i j n : ℤ)
    (h : i + j = n) (hP : P i j) :
    K.totalProjector P n ≫ totalSummandπ i j n h = totalSummandπ i j n h := by
  refine HomologicalComplex₂.total.hom_ext _ fun a b hab => ?_
  rw [ι_totalProjector_assoc]
  by_cases ha : a = i
  · subst ha
    obtain rfl : b = j := by dsimp at hab; omega
    rw [ite_eq_left hP]
  · split_ifs
    · rfl
    · rw [zero_comp, ι_totalSummandπ_of_ne i j a b n h hab ha]

lemma totalProjector_totalSummandπ_of_not (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    (i j n : ℤ) (h : i + j = n) (hP : ¬ P i j) :
    K.totalProjector P n ≫ totalSummandπ i j n h = 0 := by
  refine HomologicalComplex₂.total.hom_ext _ fun a b hab => ?_
  rw [ι_totalProjector_assoc, comp_zero]
  by_cases ha : a = i
  · subst ha
    obtain rfl : b = j := by dsimp at hab; omega
    rw [ite_eq_right hP, zero_comp]
  · split_ifs
    · exact ι_totalSummandπ_of_ne i j a b n h hab ha
    · rw [zero_comp]

/-- Splitting off the summand `K^{i,j}` of weight `p` from `⨁_{w ≥ p}`, when it is the only summand
of weight `p` in degree `n`. -/
lemma totalProjector_add_totalSummandπ_ιTotal (w : ℤ → ℤ → ℤ) (p i j n : ℤ) (h : i + j = n)
    (hp : w i j = p) (hw : ∀ a b, a + b = n → w a b = p → a = i) :
    K.totalProjector (fun a b => p + 1 ≤ w a b) n +
        totalSummandπ i j n h ≫ K.ιTotal (ComplexShape.up ℤ) i j n h =
      K.totalProjector (fun a b => p ≤ w a b) n := by
  refine HomologicalComplex₂.total.hom_ext _ fun a b hab => ?_
  rw [Preadditive.comp_add, ι_totalProjector, ι_totalProjector]
  by_cases ha : a = i
  · subst ha
    obtain rfl : b = j := by dsimp at hab; omega
    simp [hp]
  · have hne : w a b ≠ p := fun he => ha (hw a b (by dsimp at hab; omega) he)
    rw [ι_totalSummandπ_of_ne_assoc i j a b n h hab ha, zero_comp, add_zero]
    by_cases hle : p ≤ w a b
    · rw [ite_eq_left (show p + 1 ≤ w a b by omega), ite_eq_left hle]
    · rw [ite_eq_right (show ¬ p + 1 ≤ w a b by omega), ite_eq_right hle]

end Summands

section CokernelOfProjectors

variable {D : Type*} [Category* D] [Abelian D]

/-- A retraction of a monomorphism `a` onto the image of an idempotent `e` it represents. -/
noncomputable def imageRetraction {X A : D} (e : X ⟶ X) (a : A ⟶ X) [Mono a]
    (h : Subobject.mk a = imageSubobject e) : X ⟶ A :=
  factorThruImageSubobject e ≫ (Subobject.isoOfEqMk _ a h.symm).hom

@[reassoc]
lemma imageRetraction_arrow {X A : D} (e : X ⟶ X) (a : A ⟶ X) [Mono a]
    (h : Subobject.mk a = imageSubobject e) : imageRetraction e a h ≫ a = e := by
  simp [imageRetraction]

instance {X A : D} (e : X ⟶ X) (a : A ⟶ X) [Mono a]
    (h : Subobject.mk a = imageSubobject e) : Epi (imageRetraction e a h) := by
  dsimp only [imageRetraction]
  infer_instance

lemma comp_idempotent_of_mk_eq {X A : D} (e : X ⟶ X) (he : e ≫ e = e) (a : A ⟶ X)
    [Mono a] (h : Subobject.mk a = imageSubobject e) : a ≫ e = a := by
  have hi : (imageSubobject e).arrow ≫ e = (imageSubobject e).arrow := by
    rw [← cancel_epi (factorThruImageSubobject e), ← Category.assoc, imageSubobject_arrow_comp,
      he]
  rw [← Subobject.ofMkLE_arrow h.le, Category.assoc, hi]

/-- The cokernel of `f : A ⟶ B` is `Q` when `B` splits as `A ⊕ Q` compatibly with `f`. -/
noncomputable def cokernelIsoOfComplement {A B Q : D} (f : A ⟶ B) (g : B ⟶ Q)
    (w : f ≫ g = 0) (s : Q ⟶ B) (r : B ⟶ A) (hs : s ≫ g = 𝟙 Q) (hr : r ≫ f + g ≫ s = 𝟙 B) :
    cokernel f ≅ Q where
  hom := cokernel.desc f g w
  inv := s ≫ cokernel.π f
  hom_inv_id := by
    rw [← cancel_epi (cokernel.π f), cokernel.π_desc_assoc, Category.comp_id]
    conv_rhs => rw [← Category.id_comp (cokernel.π f), ← hr]
    rw [Preadditive.add_comp, Category.assoc, cokernel.condition, comp_zero, zero_add,
      Category.assoc]
  inv_hom_id := by rw [Category.assoc, cokernel.π_desc, hs]

@[reassoc]
lemma cokernelIsoOfComplement_π {A B Q : D} (f : A ⟶ B) (g : B ⟶ Q)
    (w : f ≫ g = 0) (s : Q ⟶ B) (r : B ⟶ A) (hs : s ≫ g = 𝟙 Q) (hr : r ≫ f + g ≫ s = 𝟙 B) :
    cokernel.π f ≫ (cokernelIsoOfComplement f g w s r hs hr).hom = g :=
  cokernel.π_desc _ _ _

/-- For idempotents `e' ≤ e` of `X` whose difference `e - e'` is `π ≫ ι` with `ι ≫ π = 𝟙`, the
quotient of the image of `e` by that of `e'` is `Q`. -/
noncomputable def cokernelIsoOfProjectors {X A B Q : D} (e e' : X ⟶ X) (a : A ⟶ X)
    (b : B ⟶ X) [Mono a] [Mono b] (ha : Subobject.mk a = imageSubobject e)
    (hb : Subobject.mk b = imageSubobject e') (f : B ⟶ A) (hf : f ≫ a = b) (ι : Q ⟶ X)
    (π : X ⟶ Q) (he : e ≫ e = e) (hιe : ι ≫ e = ι) (hιπ : ι ≫ π = 𝟙 Q) (he'π : e' ≫ π = 0)
    (hsplit : e' + π ≫ ι = e) : cokernel f ≅ Q :=
  cokernelIsoOfComplement f (a ≫ π)
    (by rw [← Category.assoc, hf, ← cancel_epi (imageRetraction e' b hb), ← Category.assoc,
      imageRetraction_arrow, he'π, comp_zero])
    (ι ≫ imageRetraction e a ha) (a ≫ imageRetraction e' b hb)
    (by rw [Category.assoc, ← Category.assoc (imageRetraction e a ha), imageRetraction_arrow,
      ← Category.assoc, hιe, hιπ])
    (by
      rw [← cancel_mono a]
      simp only [Preadditive.add_comp, Category.assoc, hf, imageRetraction_arrow, hιe]
      rw [← Preadditive.comp_add, hsplit, comp_idempotent_of_mk_eq e he a ha,
        Category.id_comp])

@[reassoc]
lemma cokernelIsoOfProjectors_π {X A B Q : D} (e e' : X ⟶ X) (a : A ⟶ X)
    (b : B ⟶ X) [Mono a] [Mono b] (ha : Subobject.mk a = imageSubobject e)
    (hb : Subobject.mk b = imageSubobject e') (f : B ⟶ A) (hf : f ≫ a = b) (ι : Q ⟶ X)
    (π : X ⟶ Q) (he : e ≫ e = e) (hιe : ι ≫ e = ι) (hιπ : ι ≫ π = 𝟙 Q) (he'π : e' ≫ π = 0)
    (hsplit : e' + π ≫ ι = e) :
    cokernel.π f ≫ (cokernelIsoOfProjectors e e' a b ha hb f hf ι π he hιe hιπ he'π hsplit).hom =
      a ≫ π :=
  cokernelIsoOfComplement_π _ _ _ _ _ _ _

end CokernelOfProjectors

section ZeroPage

variable (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))


/-- The degreewise steps `⨁_{w ≥ p} K^{i,j} ⊆ Tot^n` of the filtration by `w`. -/
noncomputable abbrev stepSubobject (p n : ℤ) :
    Subobject ((K.total (ComplexShape.up ℤ)).X n) :=
  imageSubobject (K.totalProjector (fun i j => p ≤ w i j) n)

include h₁ h₂ in
lemma stepSubobject_eq (p n : ℤ) :
    stepSubobject K w p n =
      Subobject.mk (((K.totalFiltration w h₁ h₂).filtration.ι.app (op p)).f n) :=
  (K.mk_totalFiltration_ι_f w h₁ h₂ p n).symm

include h₁ h₂ in
lemma cycles_zero_stepSubobject (p n : ℤ) :
    FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p n =
      stepSubobject K w p n :=
  FilteredComplexSpectralSequence.cycles_zero_eq (K.totalFiltration w h₁ h₂) _
    (stepSubobject_eq K w h₁ h₂) p n

include h₁ h₂ in
lemma boundaries_inf_cycles_zero_stepSubobject (p n : ℤ) :
    FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0
        p n ⊓
      FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          n =
      stepSubobject K w (p + 1) n :=
  FilteredComplexSpectralSequence.boundaries_zero_inf_cycles_zero (K.totalFiltration w h₁ h₂) _
    (stepSubobject_eq K w h₁ h₂) p n

/-- `Z_0^{p,q}/D_0^{p,q} = K^{i,j}` when `K^{i,j}` is the only summand of `Tot^n` of weight `p`. -/
noncomputable def zeroPageObjectIso (p n i j : ℤ) (hij : i + j = n) (hp : w i j = p)
    (hw : ∀ a b, a + b = n → w a b = p → a = i) :
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
          0 p n ⊓
        FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0
            p n ≤
      FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          n)) ≅ (K.X i).X j :=
  cokernelIsoOfProjectors (K.totalProjector (fun a b => p ≤ w a b) n)
    (K.totalProjector (fun a b => p + 1 ≤ w a b) n) _ _
    (by rw [Subobject.mk_arrow, cycles_zero_stepSubobject K w h₁ h₂])
    (by rw [Subobject.mk_arrow, boundaries_inf_cycles_zero_stepSubobject K w h₁ h₂])
    _ (Subobject.ofLE_arrow _) (K.ιTotal (ComplexShape.up ℤ) i j n hij) (totalSummandπ i j n hij)
    (K.totalProjector_idempotent _ n)
    (by rw [ι_totalProjector, ite_eq_left (show p ≤ w i j by omega)])
    (ι_totalSummandπ _ _ _ _) (totalProjector_totalSummandπ_of_not _ _ _ _ _ (by omega))
    (totalProjector_add_totalSummandπ_ιTotal w p i j n hij hp hw)

@[reassoc]
lemma π_zeroPageObjectIso_hom (p n i j : ℤ) (hij : i + j = n) (hp : w i j = p)
    (hw : ∀ a b, a + b = n → w a b = p → a = i) :
    cokernel.π _ ≫ (zeroPageObjectIso K w h₁ h₂ p n i j hij hp hw).hom =
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          n).arrow ≫
        totalSummandπ i j n hij :=
  cokernelIsoOfProjectors_π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end ZeroPage

end HomologicalComplex₂
