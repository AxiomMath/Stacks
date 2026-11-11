module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Complex

/-!
# The extended Čech complex of a split covering is homotopic to zero

Let `f : U ⥤ X` be a covering of `X` over a base category `C` and let `F` be an abelian
presheaf on `X`, so that the Čech complex `Č(U → X, F)` of `Stacks.Cech.complex` has degree `n`
term `Γ(U_n, f_n⁻¹F)`. The pullback map `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)` lands in the kernel of `d⁰`,
which makes the *extended* Čech complex

`… ⟶ 0 ⟶ Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F) ⟶ Γ(U_1, f_1⁻¹F) ⟶ …`

with `Γ(X, F)` placed in degree `-1`. If `f` has a section up to a `2`-isomorphism — a
`1`-morphism `s : X ⥤ U` together with `t : f ∘ s ≅ id_X` — then that extended complex is
homotopic to zero.

## Main definitions

* `Stacks.Cech.augmentation`: the pullback map `Γ(X, F) ⟶ Γ(U_n, f_n⁻¹F)` along `f_n`.
* `Stacks.Cech.extendedComplexNat`: the extended Čech complex indexed by `ℕ`, that is the Čech
  complex augmented by `Γ(X, F)`.
* `Stacks.Cech.extendedComplex`: the extended Čech complex, indexed by `ℤ` with `Γ(X, F)` in
  degree `-1`.

## Main results

* `Stacks.Cech.nonempty_homotopy_extendedComplex_id_zero`: the identity of the extended Čech
  complex is homotopic to zero.
* `Stacks.Cech.augmentation_comp_d`: the augmentation is a cocycle, which is what makes the
  extended complex a complex.
* `Stacks.Cech.extendedComplexXNegOne`, `Stacks.Cech.extendedComplexXOfNat`,
  `Stacks.Cech.isZero_extendedComplex_X`, `Stacks.Cech.extendedComplex_d_negOne` and
  `Stacks.Cech.extendedComplex_d_ofNat` identify its terms and its differentials.

## Implementation notes

Degree `-1` is realised literally: the `ℕ`-indexed augmented complex `CochainComplex.augment` is
shifted into `ℤ` by `HomologicalComplex.extend` along `ComplexShape.embeddingUpIntGE (-1)`,
which puts zero objects in all degrees `< -1`. Its terms are therefore identified by
isomorphisms rather than by definitional equalities, which is what the identification results
above record.

"Homotopic to zero" is `Homotopy (𝟙 _) 0`. The source claims no canonical such homotopy, so the
statement asserts existence, keeping it a proposition about the complex rather than a
construction. The homotopy exhibited is pullback along the `1`-morphisms `U_n ⥤ U_{n+1}` that
send `(u_0, …, u_n, x, α_0, …, α_n)` to `(s x, u_0, …, u_n, x, t_x, α_0, …, α_n)`, and the
verticality of `t_x` is what makes the image an object of the Čech nerve. No strict
compatibility `s ⋙ f ⋙ p = p` of structure functors is assumed, because verticality of `t`
already gives the object-level consequence `p (f (s x)) = p x`, which is all the construction
uses.

All the maps occurring are of the form `CategoryTheory.Limits.limit.pre` for a functor between
Čech nerves, and the identities between them are instances of `limit.pre_pre` together with an
equality of the composite index functors on objects; `Stacks.Cech.pre_comp_pre_π` packages the
two applications of `limit.pre_π` that this needs.

Neither the base `(Sch/S)_{fppf}` nor the fibration property enters, so the base is an arbitrary
category and no `IsFiberedInGroupoids` hypothesis is imposed. The coefficient category is any
preadditive category with a zero object and the limits computing the global sections that occur,
rather than `AddCommGrpCat`; abelian presheaves are the case `A = AddCommGrpCat`.

## References

* [Stacks Project, Tag 06X6](https://stacks.math.columbia.edu/tag/06X6)
* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open Stacks.RelativeCech (Tuple)
open scoped Simplicial

namespace Stacks.Cech

universe vA vC vU vX uA uC uU uX

variable {A : Type uA} [Category.{vA} A]
  {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X]

/-- Two successive canonical maps of limits, evaluated on a component of the target cone: the
composite is the projection of the source cone at the twice-reindexed object. -/
public theorem pre_comp_pre_π {J : Type*} [Category J] (G : J ⥤ A) [HasLimit G]
    {K : Type*} [Category K] (E : K ⥤ J) [HasLimit (E ⋙ G)]
    {L : Type*} [Category L] (D : L ⥤ K) [HasLimit (D ⋙ E ⋙ G)] (l : L) :
    limit.pre G E ≫ limit.pre (E ⋙ G) D ≫ limit.π (D ⋙ E ⋙ G) l =
      limit.π G (E.obj (D.obj l)) := by
  rw [limit.pre_π, limit.pre_π]

/-- Two composites of canonical maps of limits agree on a component, up to the types of the
components, when the twice-reindexed objects agree. -/
private theorem pre_comp_pre_π_heq {J : Type*} [Category J] (G : J ⥤ A) [HasLimit G]
    {K₁ : Type*} [Category K₁] (E₁ : K₁ ⥤ J) [HasLimit (E₁ ⋙ G)]
    {K₂ : Type*} [Category K₂] (E₂ : K₂ ⥤ J) [HasLimit (E₂ ⋙ G)]
    {L : Type*} [Category L] (D₁ : L ⥤ K₁) [HasLimit (D₁ ⋙ E₁ ⋙ G)]
    (D₂ : L ⥤ K₂) [HasLimit (D₂ ⋙ E₂ ⋙ G)] (l : L)
    (h : E₁.obj (D₁.obj l) = E₂.obj (D₂.obj l)) :
    HEq (limit.pre G E₁ ≫ limit.pre (E₁ ⋙ G) D₁ ≫ limit.π (D₁ ⋙ E₁ ⋙ G) l)
      (limit.pre G E₂ ≫ limit.pre (E₂ ⋙ G) D₂ ≫ limit.π (D₂ ⋙ E₂ ⋙ G) l) := by
  rw [pre_comp_pre_π, pre_comp_pre_π]
  have key : ∀ a b : J, a = b → HEq (limit.π G a) (limit.π G b) := by
    rintro _ _ rfl
    exact HEq.rfl
  exact key _ _ h

variable (p : X ⥤ C) (f : U ⥤ X) (F : Xᵒᵖ ⥤ A)
  [HasLimitsOfShape Xᵒᵖ A] [∀ n : ℕ, HasLimitsOfShape (Tuple p f n)ᵒᵖ A]

/-- The canonical map `Γ(X, F) ⟶ Γ(U_n, f_n⁻¹F)`: pullback of global sections along the `n`-th
projection `f_n` of the Čech nerve. -/
public def augmentation (n : ℕ) : limit F ⟶ term p f F n :=
  limit.pre F (Tuple.projection p f n).op

/-- The maps `Γ(X, F) ⟶ Γ(U_n, f_n⁻¹F)` are compatible with every simplicial reindexing, since
the projections `f_n` are `1`-morphisms over `X`. -/
public theorem augmentation_comp_reindexMap {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    augmentation p f F m ≫ reindexMap p f F φ = augmentation p f F n :=
  limit.pre_pre F (Tuple.projection p f m).op (Tuple.reindex p f φ.toOrderHom).op

section ContractingMaps

/-- The `0`-th Čech nerve object attached to a section `s` of `f`: the one-element tuple `s x`
over `x`, compared to `x` by the chosen `2`-isomorphism. -/
public def sectionTuple (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) : X ⥤ Tuple p f 0 where
  obj x := ⟨x, fun _ => s.obj x, fun _ => t.app x, fun _ => ht x⟩
  map g := ⟨g, fun _ => s.map g, fun _ => t.hom.naturality g⟩
  map_id x := by
    apply tupleHom_ext
    · rfl
    · funext i
      fin_cases i
      exact s.map_id x
  map_comp {a b c} g h := by
    apply tupleHom_ext
    · rfl
    · funext i
      fin_cases i
      exact s.map_comp g h

/-- The contracting map `Γ(U_0, f_0⁻¹F) ⟶ Γ(X, F)` in degree `0`: pullback along
`Stacks.Cech.sectionTuple`. -/
private def sectionMap (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) : term p f F 0 ⟶ limit F :=
  limit.pre ((Tuple.projection p f 0).op ⋙ F) (sectionTuple p f s t ht).op

/-- The contracting map in degree `0` splits the augmentation. -/
private lemma augmentation_comp_sectionMap (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    augmentation p f F 0 ≫ sectionMap p f F s t ht = 𝟙 (limit F) := by
  refine (limit.pre_pre F (Tuple.projection p f 0).op (sectionTuple p f s t ht).op).trans ?_
  refine limit.hom_ext fun j => ?_
  exact (limit.pre_π F ((sectionTuple p f s t ht).op ⋙ (Tuple.projection p f 0).op) j).trans
    (Category.id_comp _).symm

/-- Insert the chosen section before all the existing coordinates of a Čech tuple. -/
public def prependSection (n : ℕ) (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    Tuple p f n ⥤ Tuple p f (n + 1) where
  obj a :=
    { target := a.target
      source := Fin.cases (s.obj a.target) a.source
      comparison := Fin.cases (t.app a.target) a.comparison
      comparison_lift := Fin.cases (ht a.target) a.comparison_lift }
  map g :=
    { target := g.target
      source := Fin.cases (s.map g.target) g.source
      comparison_naturality := Fin.cases (t.hom.naturality g.target) g.comparison_naturality }
  map_id a := by
    apply tupleHom_ext
    · rfl
    · funext i
      cases i using Fin.cases
      · exact s.map_id a.target
      · rfl
  map_comp g h := by
    apply tupleHom_ext
    · rfl
    · funext i
      cases i using Fin.cases
      · exact s.map_comp g.target h.target
      · rfl

/-- The contracting map `Γ(U_{n+1}, f_{n+1}⁻¹F) ⟶ Γ(U_n, f_n⁻¹F)`: pullback along
`Stacks.Cech.prependSection`. -/
private def prependSectionMap (n : ℕ) (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    term p f F (n + 1) ⟶ term p f F n :=
  limit.pre ((Tuple.projection p f (n + 1)).op ⋙ F) (prependSection p f n s t ht).op

omit [HasLimitsOfShape Xᵒᵖ A] in
/-- Reindexing along the `0`-th coface undoes prepending the section. -/
private lemma reindexMap_faceZero_comp_prepend (n : ℕ) (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    reindexMap p f F (SimplexCategory.δ (0 : Fin (n + 2))) ≫
        prependSectionMap p f F n s t ht = 𝟙 (term p f F n) := by
  refine (limit.pre_pre ((Tuple.projection p f n).op ⋙ F)
    (Tuple.reindex p f (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom).op
    (prependSection p f n s t ht).op).trans ?_
  refine limit.hom_ext fun j => ?_
  exact (limit.pre_π ((Tuple.projection p f n).op ⋙ F)
      ((prependSection p f n s t ht).op ⋙
        (Tuple.reindex p f (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom).op) j).trans
    (Category.id_comp _).symm

omit [HasLimitsOfShape Xᵒᵖ A] in
/-- Prepending the section intertwines the coface `δ_{i+1}` upstairs with the coface `δ_i`
downstairs. -/
private lemma reindexMap_faceSucc_comp_prepend (n : ℕ) (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) (i : Fin (n + 2)) :
    reindexMap p f F (SimplexCategory.δ i.succ) ≫
        prependSectionMap p f F (n + 1) s t ht =
      prependSectionMap p f F n s t ht ≫ reindexMap p f F (SimplexCategory.δ i) := by
  refine limit.hom_ext fun j => ?_
  simp only [Category.assoc]
  refine eq_of_heq (pre_comp_pre_π_heq _ _ _ _ _ j (congrArg op ?_))
  dsimp [Tuple.reindex, prependSection, SimplexCategory.δ]
  rw [Tuple.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · funext k
    cases k using Fin.cases <;> simp
  · apply Function.hfunext rfl
    intro k l hkl
    cases hkl
    cases k using Fin.cases with
    | zero =>
      generalize he : i.succ.succAbove 0 = k
      rw [Fin.succ_succAbove_zero] at he
      subst k
      rfl
    | succ k =>
      generalize he : i.succ.succAbove k.succ = l
      rw [Fin.succ_succAbove_succ] at he
      subst l
      rw [show i.succ.succAboveOrderEmb.toOrderHom k.succ =
        (i.succAbove k).succ from Fin.succ_succAbove_succ i k]
      rfl

/-- Reindexing along the first coface, after prepending the section, is the contracting map
followed by the augmentation. -/
private lemma reindexMap_faceOne_comp_prepend (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    reindexMap p f F (SimplexCategory.δ (1 : Fin 2)) ≫ prependSectionMap p f F 0 s t ht =
      sectionMap p f F s t ht ≫ augmentation p f F 0 := by
  refine limit.hom_ext fun j => ?_
  simp only [Category.assoc]
  refine eq_of_heq (pre_comp_pre_π_heq _ _ _ _ _ j (congrArg op ?_))
  dsimp [Tuple.reindex, prependSection, sectionTuple, SimplexCategory.δ]
  rw [Tuple.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · funext k
    fin_cases k
    rfl
  · apply Function.hfunext rfl
    intro k l hkl
    cases hkl
    fin_cases k
    rfl

end ContractingMaps

section Augmented

variable [Preadditive A]

/-- The map `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)` lies in the kernel of the differential `d⁰` of the Čech
complex: its two composites with the coface pullbacks `δ⁰` and `δ¹` agree, so their alternating
sum vanishes. -/
@[stacks 06X3 "Γ(X, F) → Γ(U_0, f_0⁻¹F) lies in the kernel of d⁰"]
public theorem augmentation_comp_d :
    augmentation p f F 0 ≫ (complex p f F).d 0 1 = 0 := by
  have hd : (complex p f F).d 0 1
      = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • reindexMap p f F (SimplexCategory.δ i) :=
    complex_d p f F 0
  have hsum : augmentation p f F 0 ≫
      (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • reindexMap p f F (SimplexCategory.δ i)) = 0 := by
    rw [Preadditive.comp_sum]
    simp [augmentation_comp_reindexMap, Fin.sum_univ_two]
  exact (congrArg (fun φ => augmentation p f F 0 ≫ φ) hd).trans hsum

/-- The extended Čech complex in its `ℕ`-indexed form: the Čech complex augmented by `Γ(X, F)`
in degree `0`. -/
public def extendedComplexNat : CochainComplex A ℕ :=
  (complex p f F).augment (augmentation p f F 0) (augmentation_comp_d p f F)

section Extended

variable [HasZeroObject A]

/-- The extended Čech complex `… ⟶ 0 ⟶ Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F) ⟶ Γ(U_1, f_1⁻¹F) ⟶ …`, with
`Γ(X, F)` in degree `-1`. -/
@[stacks 06X3 "the extended Čech complex"]
public def extendedComplex : CochainComplex A ℤ :=
  (extendedComplexNat p f F).extend (ComplexShape.embeddingUpIntGE (-1))

/-- Degree `-1` of the extended Čech complex is `Γ(X, F)`. -/
public def extendedComplexXNegOne : (extendedComplex p f F).X (-1) ≅ limit F :=
  (extendedComplexNat p f F).extendXIso (ComplexShape.embeddingUpIntGE (-1))
    (i := 0) (i' := -1) (by simp)

/-- Degree `n ≥ 0` of the extended Čech complex is `Γ(U_n, f_n⁻¹F)`. -/
public def extendedComplexXOfNat (n : ℕ) :
    (extendedComplex p f F).X n ≅ term p f F n :=
  (extendedComplexNat p f F).extendXIso (ComplexShape.embeddingUpIntGE (-1))
    (i := n + 1) (i' := n) (by simp)

/-- The extended Čech complex vanishes in degrees below `-1`. -/
public theorem isZero_extendedComplex_X (i : ℤ) (hi : i < -1) :
    IsZero ((extendedComplex p f F).X i) :=
  (extendedComplexNat p f F).isZero_extend_X _ i
    ((ComplexShape.notMem_range_embeddingUpIntGE_iff (-1) i).2 hi)

/-- The differential of the extended Čech complex out of degree `-1` is the pullback map
`Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)`. -/
public theorem extendedComplex_d_negOne :
    (extendedComplex p f F).d (-1) 0 =
      (extendedComplexXNegOne p f F).hom ≫ augmentation p f F 0 ≫
        (extendedComplexXOfNat p f F 0).inv :=
  (extendedComplexNat p f F).extend_d_eq (ComplexShape.embeddingUpIntGE (-1))
    (i := 0) (j := 1) (i' := -1) (j' := 0) (by simp) (by simp)

/-- In degrees `≥ 0` the differential of the extended Čech complex is the differential of the
Čech complex, the alternating sum of the coface pullbacks. -/
public theorem extendedComplex_d_ofNat (n : ℕ) :
    (extendedComplex p f F).d n (n + 1) =
      (extendedComplexXOfNat p f F n).hom ≫ (complex p f F).d n (n + 1) ≫
        (extendedComplexXOfNat p f F (n + 1)).inv :=
  (extendedComplexNat p f F).extend_d_eq (ComplexShape.embeddingUpIntGE (-1))
    (i := n + 1) (j := n + 2) (i' := n) (j' := n + 1) (by simp) (by simp; lia)

omit [HasZeroObject A] in
/-- The contraction identity in degree `0`. -/
private lemma sectionMap_comp_augmentation_add_d_comp_prepend (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    sectionMap p f F s t ht ≫ augmentation p f F 0 +
      ((complex p f F).d 0 1 ≫ prependSectionMap p f F 0 s t ht :
        term p f F 0 ⟶ term p f F 0) = 𝟙 _ := by
  rw [complex_d]
  change sectionMap p f F s t ht ≫ augmentation p f F 0 +
    (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • reindexMap p f F (SimplexCategory.δ i)) ≫
      prependSectionMap p f F 0 s t ht = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_smul]
  rw [Preadditive.add_comp, reindexMap_faceZero_comp_prepend, Preadditive.neg_comp,
    reindexMap_faceOne_comp_prepend]
  abel

omit [HasZeroObject A] [HasLimitsOfShape Xᵒᵖ A] in
/-- The contraction identity in the positive degrees. -/
private lemma prepend_comp_d_add_d_comp_prepend (n : ℕ) (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    (prependSectionMap p f F n s t ht ≫ (complex p f F).d n (n + 1) :
        term p f F (n + 1) ⟶ term p f F (n + 1)) +
      ((complex p f F).d (n + 1) (n + 2) ≫ prependSectionMap p f F (n + 1) s t ht :
        term p f F (n + 1) ⟶ term p f F (n + 1)) = 𝟙 _ := by
  rw [complex_d p f F (n + 1)]
  simp only [cosimplicial_δ]
  change (prependSectionMap p f F n s t ht ≫ (complex p f F).d n (n + 1) :
      term p f F (n + 1) ⟶ term p f F (n + 1)) +
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • reindexMap p f F (SimplexCategory.δ i)) ≫
      prependSectionMap p f F (n + 1) s t ht = _
  rw [Preadditive.sum_comp, Fin.sum_univ_succ]
  simp only [Preadditive.zsmul_comp, Fin.val_zero, pow_zero, one_zsmul,
    reindexMap_faceZero_comp_prepend, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Preadditive.neg_comp, reindexMap_faceSucc_comp_prepend, Finset.sum_neg_distrib]
  rw [complex_d]
  simp only [cosimplicial_δ]
  change (prependSectionMap p f F n s t ht ≫
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • reindexMap p f F (SimplexCategory.δ j) :
        term p f F n ⟶ term p f F (n + 1))) + _ = _
  rw [Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul]
  abel

/-- A contracting homotopy of an `ℕ`-indexed cochain complex: a degreewise splitting of the
differentials satisfying the two contraction identities exhibits the identity as homotopic to
zero.

Nothing Čech-specific enters; it is the general criterion for an `ℕ`-indexed cochain complex
to be contractible. -/
public def homotopyOfContraction (K : CochainComplex A ℕ) (h : ∀ n, K.X (n + 1) ⟶ K.X n)
    (h₀ : K.d 0 1 ≫ h 0 = 𝟙 _)
    (hs : ∀ n, h n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ h (n + 1) = 𝟙 _) :
    Homotopy (𝟙 K) 0 where
  hom i j := if e : j + 1 = i then eqToHom (congrArg K.X e.symm) ≫ h j else 0
  zero i j e := by
    change ¬ j + 1 = i at e
    exact dite_eq_right e
  comm n := by
    rw [Homotopy.dNext_cochainComplex]
    cases n with
    | zero => simpa [Homotopy.prevD_zero_cochainComplex] using h₀.symm
    | succ n =>
      rw [Homotopy.prevD_succ_cochainComplex]
      simpa [add_comm] using (hs n).symm

/-- **Stacks 06X6.** If there is a `1`-morphism `s : X ⥤ U` such that `f ∘ s` is `2`-isomorphic
to `id_X`, then the extended Čech complex is homotopic to zero: its identity is homotopic to its
zero endomorphism. -/
@[stacks 06X6]
public theorem nonempty_homotopy_extendedComplex_id_zero (s : X ⥤ U) (t : s ⋙ f ≅ 𝟭 X)
    (ht : ∀ x : X, p.IsHomLift (𝟙 (p.obj x)) (t.hom.app x)) :
    Nonempty (Homotopy (𝟙 (extendedComplex p f F)) 0) := by
  let h : ∀ n, (extendedComplexNat p f F).X (n + 1) ⟶ (extendedComplexNat p f F).X n
    | 0 => sectionMap p f F s t ht
    | n + 1 => prependSectionMap p f F n s t ht
  have hs : ∀ n, h n ≫ (extendedComplexNat p f F).d n (n + 1) +
      (extendedComplexNat p f F).d (n + 1) (n + 2) ≫ h (n + 1) = 𝟙 _
    | 0 => sectionMap_comp_augmentation_add_d_comp_prepend p f F s t ht
    | n + 1 => prepend_comp_d_add_d_comp_prepend p f F n s t ht
  have H := (homotopyOfContraction (extendedComplexNat p f F) h
    (augmentation_comp_sectionMap p f F s t ht) hs).extend
    (ComplexShape.embeddingUpIntGE (-1))
  rw [HomologicalComplex.extendMap_id, HomologicalComplex.extendMap_zero] at H
  exact ⟨H⟩

end Extended

end Augmented

end Stacks.Cech

end
