module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Power

/-!
# The matching map of a power by a standard cosimplex

For a constant simplicial object `T` of a finitely complete category `D` and the standard
cosimplicial set `C[k]`, the map from the `(n + 1)`-simplices of `Hom(C[k], T)` to its
`n`-coskeletal matching object is a coordinate projection. The retained coordinates are the
non-surjective maps `[k] ⟶ [n + 1]`, a finite set independent of `T`, and the identification is
natural in `T`.

## Main results

* `power_cosk_unit_isProjection` identifies the canonical matching map with a finite-product
  projection, naturally in the constant object.

## Implementation notes

The canonical map is the component of the unit of `truncation n ⊣ cosk n`. An arbitrary finitely
complete category is allowed in place of the semi-representable objects over `X`. The index set
and its injection are chosen once for fixed `k` and `n`, before `T` varies; naturality is
expressed against every morphism of powered constant objects whose components are the degreewise
product maps.

The matching object is computed by exhibiting the cone over
`StructuredArrow (op [n + 1]) (inclusion n).op` assembled from the `n + 2` face projections as a
limit, through the simplicial identity `δ i ≫ δ j`, and comparing it with
`Functor.ranObjObjIsoLimit`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

/- The statements below mix the two spellings of a degree of a power: `(V.power U).obj r`, which is
how a structure map presents its source and target, and `∏ᶜ fun _ : U.obj r.unop => V.obj r`, which
is how a projection presents them. `SimplicialObject.power` is semireducible, so the two are equal
only at default transparency, and `rw`/`simp only` refuse to rewrite across the mismatch with
"not type-correct under the `implicit` transparency level". Making that one declaration implicitly
reducible for this file resolves this; it is narrower than file-scope
`backward.defeqAttrib.useBackward` / `backward.isDefEq.respectTransparency` options, being scoped
to a single declaration rather than to every defeq check in the file. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power

universe u v w

/-- Reassociation of a four-fold composite, pulling the last factor out.

A degree of a power is the product it is only at default transparency, so at a composite whose last
factor is a coordinate projection `rw [Category.assoc]` is refused as not type-correct even where
the goal displays the pattern `(a ≫ b) ≫ c` literally. Stating the identity for abstract morphisms
and applying it by `exact` runs the check at default transparency instead. -/
lemma assoc_out {C : Type*} [Category C] {V W X Y Z : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by simp

/-- Reassociation of a four-fold composite whose first two factors are already grouped; the
companion of `assoc_out`, used for the same reason. -/
private lemma assoc_out' {C : Type*} [Category C] {V W X Y Z : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) :
    (a ≫ b) ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by simp

/-- A face omits its indexing vertex. -/
private alias delta_apply_ne := CategoryTheory.SimplicialObject.Truncated.δ_apply_ne

/-- Two factorizations through distinct faces have a common factorization through their
intersection. -/
private lemma exists_common_face_factor {m : ℕ} {i j : Fin (m + 2)} (hij : i ≤ j)
    {Δ : SimplexCategory} {ψ φ : Δ ⟶ ⦋m + 1⦌}
    (h : ψ ≫ SimplexCategory.δ i.castSucc = φ ≫ SimplexCategory.δ j.succ) :
    ∃ ξ : Δ ⟶ ⦋m⦌, ψ = ξ ≫ SimplexCategory.δ j ∧ φ = ξ ≫ SimplexCategory.δ i := by
  have hφ : ∀ x, φ.toOrderHom x ≠ i := by
    intro x hx
    refine delta_apply_ne i.castSucc (ψ.toOrderHom x) ?_
    have hval : (SimplexCategory.δ j.succ).toOrderHom (φ.toOrderHom x) = i.castSucc := by
      rw [hx]
      dsimp [SimplexCategory.δ]
      rw [OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
      exact Fin.succAbove_of_castSucc_lt _ _ (by rwa [Fin.castSucc_lt_succ_iff])
    have hx' := congrArg (fun θ : Δ ⟶ ⦋m + 2⦌ => θ.toOrderHom x) h
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at hx'
    exact hx'.trans hval
  obtain ⟨ξ, hξ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' φ i hφ
  refine ⟨ξ, (cancel_mono (SimplexCategory.δ i.castSucc)).mp ?_, hξ⟩
  rw [h, hξ, Category.assoc, SimplexCategory.δ_comp_δ hij, Category.assoc]

/-- The standard cosimplicial set `C[k]` of [Stacks, Tag 0B13], which indexes the degreewise
powers. -/
abbrev simplexPowerIndex (k : ℕ) : CosimplicialObject (Type w) :=
  uliftCoyoneda.obj (op ⦋k⦌)

/-- The degree-`m` coordinate of `Hom(C[k], -)` attached to a map `β : ⦋k⦌ ⟶ m`. The coordinates
are `ULift (⦋k⦌ ⟶ m)`, but only after `uliftYoneda` is unfolded, which happens at default
transparency only; carrying the identification in this abbreviation's result type is what makes an
index elaborate at the spelling the product families below are indexed by, instead of at
`ULift (⦋k⦌ ⟶ m)` and then failing to match. -/
private abbrev coord {k : ℕ} {m : SimplexCategory} (β : ⦋k⦌ ⟶ m) :
    (simplexPowerIndex.{w} k).obj m :=
  ULift.up β

/-- The products that `Hom(C[k], T)` is built from, in the spelling `SimplicialObject.power`
expects. For a constant simplicial object the factor `((SimplicialObject.const D).obj T).obj m` is
`T`, so this is the hypothesis of `constantSimplexPower` read through `Functor.const`; naming the
translation once is what keeps every statement below in the single spelling `fun _ => T`. -/
private lemma hasProduct_constObj {D : Type u} [Category.{v} D] (k : ℕ) (T : D)
    (inst : ∀ m : SimplexCategoryᵒᵖ,
      HasProduct (fun _ : (simplexPowerIndex.{w} k).obj m.unop => T)) :
    ∀ m : SimplexCategoryᵒᵖ, HasProduct
      (fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
        ((SimplicialObject.const D).obj T).obj m) :=
  inst

private noncomputable abbrev constantSimplexPower {D : Type u} [Category.{v} D] (k : ℕ) (T : D)
    [inst : ∀ m : SimplexCategoryᵒᵖ, HasProduct
      (fun _ : (simplexPowerIndex k).obj m.unop =>
        T)] :=
  letI := hasProduct_constObj k T inst
  ((SimplicialObject.const D).obj T).power (simplexPowerIndex k)

/-- Two morphisms into a degree of `Hom(C[k], T)` agree as soon as their coordinates do. This is
`Limits.Pi.hom_ext` for the product that a degree of the power *is*; stating it here is what keeps
the coordinates in the spelling `fun _ => T` rather than the `fun _ => ((const D).obj T).obj r`
that unfolding `SimplicialObject.power` would otherwise introduce into every goal. -/
private lemma constantSimplexPower_hom_ext {D : Type u} [Category.{v} D] (k : ℕ) (T : D)
    [inst : ∀ m : SimplexCategoryᵒᵖ,
      HasProduct (fun _ : (simplexPowerIndex k).obj m.unop => T)]
    {r : SimplexCategoryᵒᵖ} {X : D} {g h : X ⟶ (constantSimplexPower k T).obj r}
    (w : ∀ α : (simplexPowerIndex k).obj r.unop,
      g ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj r.unop => T) α =
        h ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj r.unop => T) α) : g = h := by
  have := hasProduct_constObj k T inst
  exact Limits.Pi.hom_ext _ _ w

private lemma constantSimplexPower_face_π {D : Type u} [Category.{v} D]
    (k n : ℕ) [HasFiniteProducts D]
    (T : D)
    [inst : ∀ m : SimplexCategoryᵒᵖ, HasProduct (fun _ : (simplexPowerIndex k).obj m.unop =>
      T)]
    (i : Fin (n + 2)) (α : (simplexPowerIndex k).obj ⦋n⦌) :
    (constantSimplexPower k T).map (SimplexCategory.δ i).op ≫
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋n⦌ =>
          T) α =
      Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋n + 1⦌ =>
          T)
        ((simplexPowerIndex k).map (SimplexCategory.δ i) α) := by
  have := hasProduct_constObj k T inst
  simpa [constantSimplexPower, simplexPowerIndex] using
    (CategoryTheory.SimplicialObject.power_map_π ((SimplicialObject.const D).obj T)
      (simplexPowerIndex k) (φ := (SimplexCategory.δ i).op) α)

private lemma exists_face_factor {k n : ℕ}
    (α : ⦋k⦌ ⟶ ⦋n + 1⦌)
    (hα : ¬ Function.Surjective α.toOrderHom) :
    ∃ p : Σ _ : Fin (n + 2), (⦋k⦌ ⟶ ⦋n⦌),
      α = p.2 ≫ SimplexCategory.δ p.1 := by
  have hmiss : ∃ i : Fin (n + 2), ∀ x, α.toOrderHom x ≠ i := by
    by_contra h
    push Not at h
    exact hα h
  obtain ⟨i, hi⟩ := hmiss
  obtain ⟨β, hβ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' α i hi
  exact ⟨⟨i, β⟩, hβ⟩

private noncomputable def face_factor {k n : ℕ}
    (α : ⦋k⦌ ⟶ ⦋n + 1⦌)
    (hα : ¬ Function.Surjective α.toOrderHom) :
    Σ _ : Fin (n + 2), (⦋k⦌ ⟶ ⦋n⦌) :=
  Classical.choose (exists_face_factor α hα)

private lemma face_factor_spec {k n : ℕ}
    (α : ⦋k⦌ ⟶ ⦋n + 1⦌)
    (hα : ¬ Function.Surjective α.toOrderHom) :
    α = (face_factor α hα).2 ≫ SimplexCategory.δ (face_factor α hα).1 :=
  Classical.choose_spec (exists_face_factor α hα)

private abbrev ProperSimplexCoordinate (k m : ℕ) :=
  {α : ⦋k⦌ ⟶ ⦋m + 2⦌ // ¬ Function.Surjective α.toOrderHom}

private def FaceCoordinateMatching {k m : ℕ} {A : Type*}
    (f : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A) : Prop :=
  ∀ i j : Fin (m + 2), i ≤ j → ∀ β : ⦋k⦌ ⟶ ⦋m⦌,
    f i.castSucc (β ≫ SimplexCategory.δ j) =
      f j.succ (β ≫ SimplexCategory.δ i)

private lemma face_comp_not_surjective {k m : ℕ}
    (β : ⦋k⦌ ⟶ ⦋m + 1⦌) (i : Fin (m + 3)) :
    ¬ Function.Surjective (β ≫ SimplexCategory.δ i).toOrderHom := by
  intro h
  obtain ⟨x, hx⟩ := h i
  have hx' : (SimplexCategory.δ i).toOrderHom (β.toOrderHom x) = i := by
    simpa only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] using hx
  exact delta_apply_ne (m := m + 1) i (β.toOrderHom x) hx'

private def restrictProperCoordinates {k m : ℕ} {A : Type*}
    (g : ProperSimplexCoordinate k m → A) :
    Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A :=
  fun i β => g ⟨β ≫ SimplexCategory.δ i, face_comp_not_surjective β i⟩

private lemma restrictProperCoordinates_matching {k m : ℕ} {A : Type*}
    (g : ProperSimplexCoordinate k m → A) :
    FaceCoordinateMatching (restrictProperCoordinates (k := k) (m := m) g) := by
  intro i j hij β
  apply congrArg g
  apply Subtype.ext
  simp only [Category.assoc]
  rw [SimplexCategory.δ_comp_δ hij]

private lemma faceValues_eq_of_factor_lt {k m : ℕ} {A : Type*}
    (f : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A)
    (hf : FaceCoordinateMatching f) {I J : Fin (m + 3)} (hIJ : I < J)
    {α β : ⦋k⦌ ⟶ ⦋m + 1⦌}
    (h : α ≫ SimplexCategory.δ I = β ≫ SimplexCategory.δ J) :
    f I α = f J β := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 2), I = i.castSucc :=
    ⟨I.castPred (Fin.ne_last_of_lt hIJ), (Fin.castSucc_castPred I _).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin (m + 2), J = j.succ :=
    ⟨J.pred (Fin.ne_of_gt ((Fin.zero_le _).trans_lt hIJ)), (Fin.succ_pred J _).symm⟩
  obtain ⟨ξ, hα, hβ⟩ := exists_common_face_factor
    (Fin.castSucc_lt_succ_iff.mp hIJ) h
  rw [hα, hβ]
  exact hf i j (Fin.castSucc_lt_succ_iff.mp hIJ) ξ

private lemma faceValues_eq_of_factor {k m : ℕ} {A : Type*}
    (f : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A)
    (hf : FaceCoordinateMatching f) {I J : Fin (m + 3)}
    {α β : ⦋k⦌ ⟶ ⦋m + 1⦌}
    (h : α ≫ SimplexCategory.δ I = β ≫ SimplexCategory.δ J) :
    f I α = f J β := by
  rcases lt_trichotomy I J with hIJ | hIJ | hIJ
  · exact faceValues_eq_of_factor_lt f hf hIJ h
  · subst J
    have hab : α = β := (cancel_mono (SimplexCategory.δ I)).mp h
    subst β
    rfl
  · exact (faceValues_eq_of_factor_lt f hf hIJ h.symm).symm

private noncomputable def recoverProperCoordinates {k m : ℕ} {A : Type*}
    (f : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A)
    (_hf : FaceCoordinateMatching f) : ProperSimplexCoordinate k m → A :=
  fun α =>
    let p := face_factor α.1 α.2
    f p.1 p.2

private lemma recover_restrictProperCoordinates {k m : ℕ} {A : Type*}
    (g : ProperSimplexCoordinate k m → A) :
    recoverProperCoordinates (restrictProperCoordinates g)
      (restrictProperCoordinates_matching g) = g := by
  funext α
  exact congrArg g (Subtype.ext (face_factor_spec α.1 α.2).symm)

private lemma restrict_recoverProperCoordinates {k m : ℕ} {A : Type*}
    (f : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → A)
    (hf : FaceCoordinateMatching f) :
    restrictProperCoordinates (recoverProperCoordinates f hf) = f := by
  funext i α
  exact faceValues_eq_of_factor f hf
    (face_factor_spec (α ≫ SimplexCategory.δ i) (face_comp_not_surjective α i)).symm

private def properFaceIndex {k m : ℕ} (i : Fin (m + 3))
    (α : (simplexPowerIndex k).obj ⦋m + 1⦌) : ProperSimplexCoordinate k m :=
  ⟨α.down ≫ SimplexCategory.δ i, face_comp_not_surjective α.down i⟩

private noncomputable def properFaceProjection {D : Type u} [Category.{v} D]
    (k m : ℕ) [HasFiniteProducts D]
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)]
    (T : D)
    [∀ r : SimplexCategoryᵒᵖ, HasProduct (fun _ : (simplexPowerIndex k).obj r.unop =>
      T)]
    [Fintype (ProperSimplexCoordinate k m)]
    [HasProduct (fun _ : ProperSimplexCoordinate k m => T)]
    (i : Fin (m + 3)) :
    (∏ᶜ fun _ : ProperSimplexCoordinate k m => T) ⟶
      ∏ᶜ fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T :=
  Limits.Pi.map' (properFaceIndex (k := k) (m := m) i) (fun _ => 𝟙 T)

private lemma properFaceIndex_comp_δ {k m : ℕ} (i j : Fin (m + 2))
    (hij : i ≤ j) (β : (simplexPowerIndex k).obj ⦋m⦌) :
    properFaceIndex (k := k) (m := m) i.castSucc
        ((simplexPowerIndex k).map (SimplexCategory.δ j) β) =
      properFaceIndex (k := k) (m := m) j.succ
        ((simplexPowerIndex k).map (SimplexCategory.δ i) β) := by
  apply Subtype.ext
  simp only [properFaceIndex]
  simp only [CosimplicialObject.uliftCoyoneda_spec, Category.assoc]
  rw [SimplexCategory.δ_comp_δ hij]

private lemma properFaceProjection_matching {D : Type u} [Category.{v} D]
    (k m : ℕ) [HasFiniteProducts D]
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)]
    (T : D)
    [∀ r : SimplexCategoryᵒᵖ, HasProduct (fun _ : (simplexPowerIndex k).obj r.unop =>
      T)]
    [Fintype (ProperSimplexCoordinate k m)]
    [HasProduct (fun _ : ProperSimplexCoordinate k m => T)]
    (i j : Fin (m + 2)) (hij : i ≤ j) :
    properFaceProjection k m T i.castSucc ≫
        (constantSimplexPower k T).map (SimplexCategory.δ j).op =
      properFaceProjection k m T j.succ ≫
        (constantSimplexPower k T).map (SimplexCategory.δ i).op := by
  apply constantSimplexPower_hom_ext k T
  intro β
  rw [Category.assoc, constantSimplexPower_face_π, Category.assoc,
    constantSimplexPower_face_π]
  simp only [properFaceProjection, Limits.Pi.map'_comp_π]
  simpa using congrArg (Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T))
    (properFaceIndex_comp_δ (k := k) (m := m) i j hij β)

private lemma faceMorphCoordinates_matching {D : Type u} [Category.{v} D]
    (k m : ℕ) [HasFiniteProducts D]
    (T X : D)
    [∀ r : SimplexCategoryᵒᵖ, HasProduct (fun _ : (simplexPowerIndex k).obj r.unop =>
      T)]
    (f : Fin (m + 3) → (X ⟶ (constantSimplexPower k T).obj (op ⦋m + 1⦌)))
    (hf : ∀ i j : Fin (m + 2), i ≤ j →
      f i.castSucc ≫ (constantSimplexPower k T).map (SimplexCategory.δ j).op =
        f j.succ ≫ (constantSimplexPower k T).map (SimplexCategory.δ i).op) :
    FaceCoordinateMatching (fun i α =>
      f i ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
        T) (coord α)) := by
  intro i j hij β
  have h := congrArg (fun g => g ≫ Limits.Pi.π
    (fun _ : (simplexPowerIndex k).obj ⦋m⦌ =>
      T) (coord β)) (hf i j hij)
  have hcoord (r : Fin (m + 2)) :
      (constantSimplexPower k T).map (SimplexCategory.δ r).op ≫
          Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m⦌ =>
            T) (coord β) =
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
          T)
          (coord (β ≫ SimplexCategory.δ r)) := by
    rw [constantSimplexPower_face_π]
    congr 1
  calc
    f i.castSucc ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
        T)
        (coord (β ≫ SimplexCategory.δ j)) =
      (f i.castSucc ≫ (constantSimplexPower k T).map (SimplexCategory.δ j).op) ≫
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m⦌ =>
          T) (coord β) := by
        rw [Category.assoc, hcoord]
    _ = (f j.succ ≫ (constantSimplexPower k T).map (SimplexCategory.δ i).op) ≫
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m⦌ =>
          T) (coord β) := h
    _ = f j.succ ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
        T)
        (coord (β ≫ SimplexCategory.δ i)) := by
        rw [Category.assoc, hcoord]

private lemma properFaceProjection_isUniversal {D : Type u} [Category.{v} D]
    [HasFiniteLimits D] (k m : ℕ) [Fintype (ProperSimplexCoordinate k m)]
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)]
    (T X : D)
    [∀ r : SimplexCategoryᵒᵖ, HasProduct (fun _ : (simplexPowerIndex k).obj r.unop =>
      T)]
    (f : Fin (m + 3) → (X ⟶ (constantSimplexPower k T).obj (op ⦋m + 1⦌)))
    (hf : ∀ i j : Fin (m + 2), i ≤ j →
      f i.castSucc ≫ (constantSimplexPower k T).map (SimplexCategory.δ j).op =
        f j.succ ≫ (constantSimplexPower k T).map (SimplexCategory.δ i).op) :
    ∃! h : X ⟶ ∏ᶜ fun _ : ProperSimplexCoordinate k m => T,
      ∀ i, h ≫ properFaceProjection k m T i = f i := by
  let c : Fin (m + 3) → (⦋k⦌ ⟶ ⦋m + 1⦌) → (X ⟶ T) := fun i α =>
    f i ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
      T) (coord α)
  have hc : FaceCoordinateMatching c := faceMorphCoordinates_matching k m T X f hf
  let g : ProperSimplexCoordinate k m → (X ⟶ T) := recoverProperCoordinates c hc
  refine ⟨Limits.Pi.lift (fun α : ProperSimplexCoordinate k m => g α), ?_, ?_⟩
  · intro i
    apply constantSimplexPower_hom_ext k T
    intro α
    change (Limits.Pi.lift (fun q : ProperSimplexCoordinate k m => g q) ≫
      properFaceProjection k m T i) ≫
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
          T) α = c i α.down
    simp only [Category.assoc, properFaceProjection, Limits.Pi.map'_comp_π]
    simpa [restrictProperCoordinates, properFaceIndex] using
      congrFun (congrFun (restrict_recoverProperCoordinates c hc) i) α.down
  · intro h hh
    apply Limits.Pi.hom_ext
    intro α
    dsimp [g, recoverProperCoordinates]
    let p := face_factor α.1 α.2
    have hcoord := congrArg (fun q => q ≫ Limits.Pi.π
      (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
        T) (coord p.2)) (hh p.1)
    simp only [Category.assoc, properFaceProjection, Limits.Pi.map'_comp_π,
      Category.comp_id] at hcoord
    have hp : properFaceIndex (k := k) (m := m) p.1 (coord p.2) = α :=
      Subtype.ext (face_factor_spec α.1 α.2).symm
    calc
      h ≫ Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) α =
          h ≫ Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T)
            (properFaceIndex (k := k) (m := m) p.1 (coord p.2)) := by rw [hp]
      _ = f p.1 ≫ Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ =>
          T) (coord p.2) := hcoord
      _ = (Limits.Pi.lift (fun q : ProperSimplexCoordinate k m => g q)) ≫
          Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) α := by
        rw [Limits.Pi.lift_comp_π]
        rfl

private noncomputable def properFaceMatchingCone {D : Type u} [Category.{v} D]
    [HasFiniteLimits D] (k m : ℕ)
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)]
    (T : D) : Cone (StructuredArrow.proj (op ⦋m + 2⦌)
      (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙
        (SimplicialObject.truncation (m + 1)).obj (constantSimplexPower k T)) := by
  letI : Fintype (ProperSimplexCoordinate k m) := Fintype.ofFinite _
  let U : SimplicialObject.Truncated D (m + 1) :=
    (SimplicialObject.truncation (m + 1)).obj (constantSimplexPower k T)
  let f : Fin (m + 3) →
      ((∏ᶜ fun _ : ProperSimplexCoordinate k m => T) ⟶
        U.obj (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1)))) :=
    fun i => properFaceProjection k m T i
  have hf : ∀ i j : Fin (m + 2), i ≤ j →
      f i.castSucc ≫ U.map
          (SimplexCategory.Truncated.δ (m + 1) j m.le_succ le_rfl).op =
        f j.succ ≫ U.map
          (SimplexCategory.Truncated.δ (m + 1) i m.le_succ le_rfl).op := by
    intro i j hij
    simpa [f, U, SimplicialObject.truncation] using
      properFaceProjection_matching k m T i j hij
  exact Cone.mk _ (Classical.choose
    ((CategoryTheory.SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff U
      (∏ᶜ fun _ : ProperSimplexCoordinate k m => T) f).2 hf))

private abbrev properFaceSlice (m : ℕ) := StructuredArrow (op ⦋m + 2⦌)
  (SimplexCategory.Truncated.inclusion (m + 1)).op

private abbrev properFaceObj {m : ℕ} (i : Fin (m + 3)) :
    StructuredArrow (op ⦋m + 2⦌) (SimplexCategory.Truncated.inclusion (m + 1)).op :=
  StructuredArrow.mk (Y := op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1)))
    (SimplexCategory.δ i).op

private lemma properFaceFamily_matching {D : Type u} [Category.{v} D] {m : ℕ}
    {U : SimplicialObject.Truncated D (m + 1)}
    (c : Cone (StructuredArrow.proj (op ⦋m + 2⦌)
      (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ U)) :
    ∀ i j : Fin (m + 2), i ≤ j →
      c.π.app (properFaceObj i.castSucc) ≫
          U.map (SimplexCategory.Truncated.δ (m + 1) j m.le_succ le_rfl).op =
        c.π.app (properFaceObj j.succ) ≫
          U.map (SimplexCategory.Truncated.δ (m + 1) i m.le_succ le_rfl).op := by
  intro i j hij
  have h₁ := c.w (StructuredArrow.homMk
    (f := properFaceObj i.castSucc)
    (f' := StructuredArrow.mk (Y := op (⟨⦋m⦌, m.le_succ⟩ : SimplexCategory.Truncated (m + 1)))
      (SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc).op)
    (SimplexCategory.Truncated.δ (m + 1) j m.le_succ le_rfl).op (by simp [properFaceObj]))
  have h₂ := c.w (StructuredArrow.homMk
    (f := properFaceObj j.succ)
    (f' := StructuredArrow.mk (Y := op (⟨⦋m⦌, m.le_succ⟩ : SimplexCategory.Truncated (m + 1)))
      (SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc).op)
    (SimplexCategory.Truncated.δ (m + 1) i m.le_succ le_rfl).op
    (by simp [properFaceObj, ← op_comp, SimplexCategory.δ_comp_δ hij]))
  exact h₁.trans h₂.symm

private lemma properFaceCone_ext {D : Type u} [Category.{v} D] {m : ℕ}
    {U : SimplicialObject.Truncated D (m + 1)} {X : D}
    {π π' : (Functor.const (StructuredArrow (op ⦋m + 2⦌)
      (SimplexCategory.Truncated.inclusion (m + 1)).op)).obj X ⟶
      StructuredArrow.proj (op ⦋m + 2⦌) (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ U}
    (h : ∀ i, π.app (properFaceObj i) = π'.app (properFaceObj i)) : π = π' := by
  let f : Fin (m + 3) → (X ⟶
      U.obj (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1)))) :=
    fun i => π.app (properFaceObj i)
  obtain ⟨_, -, huniq⟩ :=
    (CategoryTheory.SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff U X f).2
      (properFaceFamily_matching ⟨X, π⟩)
  exact (huniq π fun _ => rfl).trans (huniq π' fun i => by simpa [f] using (h i).symm).symm

private lemma properFaceMatchingCone_face_app {D : Type u} [Category.{v} D]
    [HasFiniteLimits D] (k m : ℕ)
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)]
    [Fintype (ProperSimplexCoordinate k m)] (T : D)
    (i : Fin (m + 3)) :
    (properFaceMatchingCone k m T).π.app (properFaceObj i) = properFaceProjection k m T i := by
  dsimp [properFaceMatchingCone]
  exact (Classical.choose_spec
    ((CategoryTheory.SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
    ((SimplicialObject.truncation (m + 1)).obj (constantSimplexPower k T))
    (∏ᶜ fun _ : ProperSimplexCoordinate k m => T)
    (fun i => properFaceProjection k m T i)).2 (by
      intro i j hij
      simpa [SimplicialObject.truncation] using
        properFaceProjection_matching k m T i j hij))).1 i

private noncomputable def properFaceMatchingCone_isLimit {D : Type u} [Category.{v} D]
    [HasFiniteLimits D] (k m : ℕ)
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)] (T : D) :
    IsLimit (properFaceMatchingCone k m T) := by
  letI : Fintype (ProperSimplexCoordinate k m) := Fintype.ofFinite _
  let F := (SimplicialObject.truncation (m + 1)).obj (constantSimplexPower k T)
  let P := StructuredArrow.proj (op ⦋m + 2⦌)
    (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F
  let c := properFaceMatchingCone k m T
  have hfamily (s : Cone P) :
      ∃! h : s.pt ⟶ ∏ᶜ fun _ : ProperSimplexCoordinate k m => T,
        ∀ i, h ≫ properFaceProjection k m T i = s.π.app (properFaceObj i) :=
    properFaceProjection_isUniversal k m T s.pt
      (fun i => s.π.app (properFaceObj i)) (properFaceFamily_matching s)
  refine IsLimit.mk (fun s => Classical.choose (hfamily s)) (fun s j => ?_)
    (fun s m' hm' => ?_)
  · have hfaces : ∀ i,
        ((Functor.const (StructuredArrow (op ⦋m + 2⦌)
          (SimplexCategory.Truncated.inclusion (m + 1)).op)).map
            (Classical.choose (hfamily s)) ≫ c.π).app (properFaceObj i) =
          s.π.app (properFaceObj i) := by
      intro i
      change Classical.choose (hfamily s) ≫ c.π.app (properFaceObj i) = _
      rw [properFaceMatchingCone_face_app]
      exact (Classical.choose_spec (hfamily s)).1 i
    exact congr_app (properFaceCone_ext hfaces) j
  · exact (Classical.choose_spec (hfamily s)).2 m' fun i => by
      rw [← properFaceMatchingCone_face_app]
      exact hm' _

/-- The diagram whose limit is the degree-`(m + 2)` matching object of `Hom(C[k], T)`: the
`(m + 1)`-truncation, restricted along the maps out of `⦋m + 2⦌`. -/
private noncomputable abbrev properFaceDiagram {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (k m : ℕ)
    [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)] (T : D) :
    properFaceSlice m ⥤ D :=
  StructuredArrow.proj (op ⦋m + 2⦌) (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙
    (SimplicialObject.truncation (m + 1)).obj (constantSimplexPower k T)

/-- The `β`-coordinate of the `δ i`-component of the degree-`(m + 2)` matching object.

The source is recorded as the limit of the matching diagram, so the identification of a degree of
`Hom(C[k], T)` with the product it is — available only at default transparency — is discharged once
here, instead of at every composition below, where it defeats `rw` and `simp only`. -/
private noncomputable def matchingLimitCoord {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (k m : ℕ) [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)] (T : D)
    [HasLimit (properFaceDiagram k m T)] (i : Fin (m + 3)) (β : ⦋k⦌ ⟶ ⦋m + 1⦌) :
    limit (properFaceDiagram k m T) ⟶ T :=
  limit.π (properFaceDiagram k m T) (properFaceObj i) ≫
    Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord β)

/-- The degree-`(m + 2)` matching object of `Hom(C[k], T)` is the power of `T` by the
non-surjective coordinates. -/
private noncomputable def matchingLimitIso {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (k m : ℕ) [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)] (T : D)
    [Fintype (ProperSimplexCoordinate k m)] [HasLimit (properFaceDiagram k m T)] :
    limit (properFaceDiagram k m T) ≅ ∏ᶜ fun _ : ProperSimplexCoordinate k m => T :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit (properFaceDiagram k m T))
    (properFaceMatchingCone_isLimit k m T)

/-- Under `matchingLimitIso` the coordinate at a non-surjective map `β ≫ δ i` is the `β`-coordinate
of the `δ i`-component. -/
private lemma matchingLimitIso_hom_π {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (k m : ℕ) [∀ r : SimplexCategoryᵒᵖ, Fintype ((simplexPowerIndex k).obj r.unop)] (T : D)
    [Fintype (ProperSimplexCoordinate k m)] [HasLimit (properFaceDiagram k m T)]
    (i : Fin (m + 3)) (β : ⦋k⦌ ⟶ ⦋m + 1⦌) :
    (matchingLimitIso k m T).hom ≫
        Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T)
          (properFaceIndex (k := k) (m := m) i (coord β)) =
      matchingLimitCoord k m T i β := by
  have h₁ : (matchingLimitIso k m T).hom ≫ properFaceProjection k m T i =
      limit.π (properFaceDiagram k m T) (properFaceObj i) := by
    rw [← properFaceMatchingCone_face_app]
    exact IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (properFaceDiagram k m T))
      (properFaceMatchingCone_isLimit k m T) (properFaceObj i)
  have h₂ : properFaceProjection k m T i ≫
        Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord β) =
      Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T)
        (properFaceIndex (k := k) (m := m) i (coord β)) := by
    simp only [properFaceProjection, Limits.Pi.map'_comp_π, Category.comp_id]
    rfl
  exact (congrArg ((matchingLimitIso k m T).hom ≫ ·) h₂.symm).trans
    (by rw [← Category.assoc, h₁]; rfl)

private lemma ranObjObjIsoLimit_map_π
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) [∀ F : C ⥤ H, L.HasRightKanExtension F]
    {F F' : C ⥤ H}
    [L.HasPointwiseRightKanExtension F] [L.HasPointwiseRightKanExtension F']
    (φ : F ⟶ F') (X : D) (q : StructuredArrow X L) :
    (L.ran.map φ).app X ≫ (L.ranObjObjIsoLimit F' X).hom ≫
        limit.π (StructuredArrow.proj X L ⋙ F') q =
      ((L.ranObjObjIsoLimit F X).hom ≫
        limit.π (StructuredArrow.proj X L ⋙ F) q) ≫ φ.app q.right := by
  rw [Functor.ranObjObjIsoLimit_hom_π, Functor.ranObjObjIsoLimit_hom_π,
    ← NatTrans.naturality_assoc]
  simp only [Category.assoc]
  congr 1
  exact congr_app (L.ranCounit.naturality φ) q.right

/-- The `(n + 1)`-st matching map of `Hom(C[k], T)` is, functorially in `T`,
a projection of finite powers of `T`. -/
@[stacks 0B16]
public theorem power_cosk_unit_isProjection
    {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (k n : ℕ) (hn : 0 < n) :
    letI : ∀ F : SimplicialObject.Truncated D n,
        (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F :=
      fun F =>
        (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
            (C := D)).2 (fun _ => inferInstance) n hn F;
    letI : ∀ m : SimplexCategoryᵒᵖ,
        Fintype ((uliftCoyoneda.{w}.obj (op ⦋k⦌)).obj m.unop) :=
      fun m => by
        rw [CosimplicialObject.uliftCoyoneda_spec.1 ⦋k⦌ m.unop]
        exact Fintype.ofFinite _;
    ∃ S : Finset ((uliftCoyoneda.{w}.obj (op ⦋k⦌)).obj ⦋n + 1⦌),
      ∃ e : ∀ T : D,
          (((SimplicialObject.cosk n).obj
            (((SimplicialObject.const D).obj T).power
              (uliftCoyoneda.{w}.obj (op ⦋k⦌)))).obj (op ⦋n + 1⦌)) ≅
            ∏ᶜ fun _ : ↥S => T,
        (∀ T : D,
          (((SimplicialObject.coskAdj n).unit.app
            (((SimplicialObject.const D).obj T).power
              (uliftCoyoneda.{w}.obj (op ⦋k⦌)))).app
              (op ⦋n + 1⦌)) ≫ (e T).hom =
            eqToHom (SimplicialObject.power_obj
              ((SimplicialObject.const D).obj T)
              (uliftCoyoneda.{w}.obj (op ⦋k⦌)) (op ⦋n + 1⦌)) ≫
              Limits.Pi.map' (fun s : ↥S => (s : _)) (fun _ => 𝟙 T)) ∧
        (∀ (T T' : D) (f : T ⟶ T')
          (g : (((SimplicialObject.const D).obj T).power
              (uliftCoyoneda.{w}.obj (op ⦋k⦌))) ⟶
            (((SimplicialObject.const D).obj T').power
              (uliftCoyoneda.{w}.obj (op ⦋k⦌)))),
          (∀ m : SimplexCategoryᵒᵖ,
            g.app m = Limits.Pi.map (fun _ => f)) →
          (((SimplicialObject.cosk n).map g).app (op ⦋n + 1⦌)) ≫ (e T').hom =
            (e T).hom ≫ Limits.Pi.map (fun _ : ↥S => f)) := by
  let : ∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F :=
    fun F =>
      (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := D)).2 (fun _ => inferInstance) n hn F
  let : ∀ r : SimplexCategoryᵒᵖ,
      Fintype ((uliftCoyoneda.{w}.obj (op ⦋k⦌)).obj r.unop) := fun r => by
    rw [CosimplicialObject.uliftCoyoneda_spec.1 ⦋k⦌ r.unop]
    exact Fintype.ofFinite _
  cases n with
  | zero => omega
  | succ m =>
    let : Fintype (ProperSimplexCoordinate k m) := Fintype.ofFinite _
    let A := (simplexPowerIndex k).obj ⦋m + 2⦌
    let S : Finset A := Finset.univ.filter fun a =>
      ¬ Function.Surjective a.down.toOrderHom
    let indexEquiv : ↥S ≃ ProperSimplexCoordinate k m :=
      { toFun := fun a => ⟨a.1.down, (Finset.mem_filter.mp a.2).2⟩
        invFun := fun a => ⟨coord a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
        left_inv _ := Subtype.ext rfl
        right_inv _ := Subtype.ext rfl }
    let productIso (T : D) :
        (∏ᶜ fun _ : ↥S => T) ≅ ∏ᶜ fun _ : ProperSimplexCoordinate k m => T :=
      Limits.Pi.whiskerEquiv indexEquiv (fun _ => Iso.refl T)
    let X (T : D) := ((SimplicialObject.const D).obj T).power
      (simplexPowerIndex k)
    let F (T : D) : SimplicialObject.Truncated D (m + 1) :=
      (SimplicialObject.truncation (m + 1)).obj (X T)
    let L := (SimplexCategory.Truncated.inclusion (m + 1)).op
    let ciso (T : D) :
        (((SimplicialObject.cosk (m + 1)).obj (X T)).obj (op ⦋m + 2⦌)) ≅
          ∏ᶜ fun _ : ProperSimplexCoordinate k m => T :=
      (L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)) ≪≫ matchingLimitIso k m T
    let e (T : D) :
        (((SimplicialObject.cosk (m + 1)).obj (X T)).obj (op ⦋m + 2⦌)) ≅
          ∏ᶜ fun _ : ↥S => T := ciso T ≪≫ (productIso T).symm
    have ha (a : ↥S) : ¬ Function.Surjective a.1.down.toOrderHom :=
      (Finset.mem_filter.mp a.2).2
    have hpidx (a : ↥S) : properFaceIndex.{w} (k := k) (m := m)
        (face_factor a.1.down (ha a)).1 (coord (face_factor a.1.down (ha a)).2) =
          indexEquiv a :=
      Subtype.ext (face_factor_spec a.1.down (ha a)).symm
    have hci (U : D) (a : ↥S) (i : Fin (m + 3)) (β : ⦋k⦌ ⟶ ⦋m + 1⦌)
        (h : properFaceIndex.{w} (k := k) (m := m) i (coord β) = indexEquiv a) :
        (ciso U).hom ≫ Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => U) (indexEquiv a) =
          (L.ranObjObjIsoLimit (F U) (op ⦋m + 2⦌)).hom ≫ matchingLimitCoord k m U i β := by
      rw [← h]
      change ((L.ranObjObjIsoLimit (F U) (op ⦋m + 2⦌)).hom ≫ (matchingLimitIso k m U).hom) ≫ _ = _
      rw [Category.assoc, matchingLimitIso_hom_π]
    have hcoordeq (U : D) (i : Fin (m + 3)) (β : ⦋k⦌ ⟶ ⦋m + 1⦌) :
        Limits.limit.π
            (StructuredArrow.proj (op ⦋m + 2⦌)
              (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F U) (properFaceObj i) ≫
          Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => U) (coord β) =
        matchingLimitCoord k m U i β := rfl
    have hout (U : D) (a : ↥S) :
        (productIso U).inv ≫ Limits.Pi.π (fun _ : ↥S => U) a =
          Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => U) (indexEquiv a) := by
      simp [productIso, Limits.Pi.whiskerEquiv, Limits.Pi.map'_comp_π]
    refine ⟨S, e, ?_⟩
    constructor
    · intro T
      apply Limits.Pi.hom_ext
      intro a
      let p := face_factor (a.1.down) (ha a)
      have htriangle := L.ranCounit_app_app_ranAdjunction_unit_app_app (X T)
        (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1)))
      have htriangle' :
          ((SimplicialObject.coskAdj (m + 1)).unit.app (X T)).app (op ⦋m + 1⦌) ≫
              ((L.ranCounit.app (F T)).app
                (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1)))) = 𝟙 _ := by
        simpa [SimplicialObject.coskAdj, L, F, X,
          SimplicialObject.truncation, SimplicialObject.Truncated.cosk] using htriangle
      have hunitProjection :
          ((SimplicialObject.coskAdj (m + 1)).unit.app (X T)).app (op ⦋m + 2⦌) ≫
              (L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
              Limits.limit.π
                (StructuredArrow.proj (op ⦋m + 2⦌)
                  (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T)
                (properFaceObj p.1) =
            (X T).map (SimplexCategory.δ p.1).op := by
        let η := (L.ranAdjunction D).unit.app (X T)
        have hnat :
            η.app (op ⦋m + 2⦌) ≫ (L.ran.obj (L ⋙ X T)).map
                (SimplexCategory.δ p.1).op =
              (X T).map (SimplexCategory.δ p.1).op ≫
                η.app (op ⦋m + 1⦌) :=
          (η.naturality (SimplexCategory.δ p.1).op).symm
        rw [Functor.ranObjObjIsoLimit_hom_π]
        change η.app _ ≫ (L.ran.obj (L ⋙ X T)).map (SimplexCategory.δ p.1).op ≫
            (L.ranCounit.app (L ⋙ X T)).app
              (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1))) = _
        calc
          _ = ((X T).map (SimplexCategory.δ p.1).op ≫ η.app (op ⦋m + 1⦌)) ≫
              (L.ranCounit.app (L ⋙ X T)).app
                (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1))) := by
                  rw [← Category.assoc, hnat]
          _ = (X T).map (SimplexCategory.δ p.1).op := by
            have htri : η.app (op ⦋m + 1⦌) ≫
                (L.ranCounit.app (L ⋙ X T)).app
                  (op (⟨⦋m + 1⦌, le_rfl⟩ : SimplexCategory.Truncated (m + 1))) = 𝟙 _ := by
              simpa [η, SimplicialObject.coskAdj, L, F, X,
                SimplicialObject.truncation, SimplicialObject.Truncated.cosk] using htriangle'
            rw [Category.assoc, htri]
            simp
      let ηT := (SimplicialObject.coskAdj (m + 1)).unit.app (X T)
      have hmain :
          (ηT.app (op ⦋m + 2⦌) ≫ (e T).hom) ≫
              Limits.Pi.π (fun _ : ↥S => T) a =
            (eqToHom (SimplicialObject.power_obj
                ((SimplicialObject.const D).obj T) (simplexPowerIndex k)
                (op ⦋m + 2⦌)) ≫
              Limits.Pi.map' (fun s : ↥S => (s : _)) (fun _ => 𝟙 T)) ≫
              Limits.Pi.π (fun _ : ↥S => T) a := by
        calc
          (ηT.app (op ⦋m + 2⦌) ≫ (e T).hom) ≫
              Limits.Pi.π (fun _ : ↥S => T) a =
            ηT.app
              (op ⦋m + 2⦌) ≫ (ciso T).hom ≫
                Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) (indexEquiv a) := by
                  dsimp [e]
                  simp only [Category.assoc, hout T a]
          _ = ηT.app (op ⦋m + 2⦌) ≫ (L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
              matchingLimitCoord k m T p.1 p.2 :=
            congrArg (fun q => ηT.app (op ⦋m + 2⦌) ≫ q) (hci T a p.1 p.2 (hpidx a))
          _ = (ηT.app (op ⦋m + 2⦌) ≫ (L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
              Limits.limit.π
                (StructuredArrow.proj (op ⦋m + 2⦌)
                  (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T)
                (properFaceObj p.1)) ≫
              Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord p.2) :=
            (congrArg (fun q => ηT.app (op ⦋m + 2⦌) ≫
              (L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫ q) (hcoordeq T p.1 p.2).symm).trans
                (assoc_out _ _ _ _)
          _ = (X T).map (SimplexCategory.δ p.1).op ≫
              Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T)
                (coord p.2) :=
            congrArg (fun q => q ≫ Limits.Pi.π
              (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord p.2)) hunitProjection
          _ = Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 2⦌ => T)
              ((simplexPowerIndex k).map (SimplexCategory.δ p.1) (coord p.2)) := by
            simpa [X, constantSimplexPower] using
              (constantSimplexPower_face_π (D := D) k (m + 1) T p.1 (coord p.2))
          _ = Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 2⦌ => T)
              (coord a.1.down) := by
            congr 1
            apply ULift.ext
            change p.2 ≫ SimplexCategory.δ p.1 = a.1.down
            exact (face_factor_spec a.1.down (ha a)).symm
          _ = (eqToHom (SimplicialObject.power_obj
                ((SimplicialObject.const D).obj T) (simplexPowerIndex k)
                (op ⦋m + 2⦌)) ≫
              Limits.Pi.map' (fun s : ↥S => (s : _)) (fun _ => 𝟙 T)) ≫
              Limits.Pi.π (fun _ : ↥S => T) a := by
            rw [Category.assoc, Limits.Pi.map'_comp_π]
            simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.const_obj_obj,
              eqToHom_refl, Category.comp_id, Category.id_comp]
            apply congrArg (Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 2⦌ => T))
            apply ULift.ext
            rfl
      exact hmain
    · intro T T' f g hg
      let φ : F T ⟶ F T' :=
        (SimplicialObject.truncation (m + 1)).map g
      apply Limits.Pi.hom_ext
      intro a
      let p := face_factor (a.1.down) (ha a)
      have hΦ : φ.app (properFaceObj p.1).right ≫
            Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T') (coord p.2) =
          Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord p.2) ≫ f := by
        have hφ : φ.app (properFaceObj p.1).right = g.app (op ⦋m + 1⦌) := rfl
        rw [hφ, hg (op ⦋m + 1⦌)]
        exact Limits.Pi.map_π (fun _ => f) (coord p.2)
      have hstep :
          (L.ran.map φ).app (op ⦋m + 2⦌) ≫
              (L.ranObjObjIsoLimit (F T') (op ⦋m + 2⦌)).hom ≫
                matchingLimitCoord k m T' p.1 p.2 =
            ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
              matchingLimitCoord k m T p.1 p.2) ≫ f := by
        calc
          (L.ran.map φ).app (op ⦋m + 2⦌) ≫
                (L.ranObjObjIsoLimit (F T') (op ⦋m + 2⦌)).hom ≫
                  matchingLimitCoord k m T' p.1 p.2 =
              ((L.ran.map φ).app (op ⦋m + 2⦌) ≫
                (L.ranObjObjIsoLimit (F T') (op ⦋m + 2⦌)).hom ≫
                  Limits.limit.π
                    (StructuredArrow.proj (op ⦋m + 2⦌)
                      (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T')
                    (properFaceObj p.1)) ≫
                Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T') (coord p.2) :=
            (congrArg (fun q => (L.ran.map φ).app (op ⦋m + 2⦌) ≫
              (L.ranObjObjIsoLimit (F T') (op ⦋m + 2⦌)).hom ≫ q) (hcoordeq T' p.1 p.2).symm).trans
                (assoc_out _ _ _ _)
          _ = (((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
                Limits.limit.π
                  (StructuredArrow.proj (op ⦋m + 2⦌)
                    (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T)
                  (properFaceObj p.1)) ≫ φ.app (properFaceObj p.1).right) ≫
                Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T') (coord p.2) :=
            congrArg (fun q => q ≫ Limits.Pi.π
              (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T') (coord p.2))
              (ranObjObjIsoLimit_map_π L φ (op ⦋m + 2⦌) (properFaceObj p.1))
          _ = ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
                Limits.limit.π
                  (StructuredArrow.proj (op ⦋m + 2⦌)
                    (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T)
                  (properFaceObj p.1)) ≫
                Limits.Pi.π (fun _ : (simplexPowerIndex k).obj ⦋m + 1⦌ => T) (coord p.2) ≫ f :=
            (Category.assoc _ _ _).trans
              (congrArg (fun q => ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
                Limits.limit.π
                  (StructuredArrow.proj (op ⦋m + 2⦌)
                    (SimplexCategory.Truncated.inclusion (m + 1)).op ⋙ F T)
                  (properFaceObj p.1)) ≫ q) hΦ)
          _ = ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
                matchingLimitCoord k m T p.1 p.2) ≫ f :=
            (assoc_out' _ _ _ _).trans
              (congrArg (fun q => ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫ q) ≫ f)
                (hcoordeq T p.1 p.2))
      have hcan :
          ((L.ran.map φ).app (op ⦋m + 2⦌) ≫ (ciso T').hom) ≫
              Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T') (indexEquiv a) =
            (ciso T).hom ≫
              Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) (indexEquiv a) ≫ f := by
        calc
          ((L.ran.map φ).app (op ⦋m + 2⦌) ≫ (ciso T').hom) ≫
                Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T') (indexEquiv a) =
              (L.ran.map φ).app (op ⦋m + 2⦌) ≫
                (L.ranObjObjIsoLimit (F T') (op ⦋m + 2⦌)).hom ≫
                  matchingLimitCoord k m T' p.1 p.2 :=
            (Category.assoc _ _ _).trans
              (congrArg (fun q => (L.ran.map φ).app (op ⦋m + 2⦌) ≫ q)
                (hci T' a p.1 p.2 (hpidx a)))
          _ = ((L.ranObjObjIsoLimit (F T) (op ⦋m + 2⦌)).hom ≫
                matchingLimitCoord k m T p.1 p.2) ≫ f := hstep
          _ = ((ciso T).hom ≫
                Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) (indexEquiv a)) ≫ f :=
            congrArg (fun q => q ≫ f) (hci T a p.1 p.2 (hpidx a)).symm
          _ = (ciso T).hom ≫
                Limits.Pi.π (fun _ : ProperSimplexCoordinate k m => T) (indexEquiv a) ≫ f :=
            Category.assoc _ _ _
      change
        ((L.ran.map φ).app (op ⦋m + 2⦌) ≫ (ciso T').hom ≫
          (productIso T').inv) ≫ Limits.Pi.π (fun _ : ↥S => T') a =
        (((ciso T).hom ≫ (productIso T).inv) ≫ Limits.Pi.map (fun _ => f)) ≫
          Limits.Pi.π (fun _ : ↥S => T') a
      simp only [Category.assoc, Limits.Pi.map_π, hout _ a]
      rw [← Category.assoc (productIso T).inv, hout T a]
      simpa only [Category.assoc] using hcan

end Stacks.CategoryTheory.Hypercovering
