module

public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSourceShiftCommShift
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal Hom commutes with the shift of its dualized variable

Let `(C, O)` be a ringed site and `M` an object of `D(O)`.  This file equips the derived
internal Hom in its **contravariant** variable,

`RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)`,

with a `CategoryTheory.Functor.CommShift ℤ`: the natural isomorphism
`RSheafHom(L⟦-n⟧, M) ≅ RSheafHom(L, M)⟦n⟧`, coherently in `n`.  The shift on `D(O)ᵒᵖ` is the
one of `CategoryTheory.Pretriangulated.Opposite`, for which `(op L)⟦n⟧ = op (L⟦-n⟧)`.

The datum is built at the level of cochain complexes and descended along the localization.
The library already has both halves of that construction with the two coherence equations of
the chain-level datum left as hypotheses: the datum
`AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso` and its packaging
`AlgebraicGeometry.RingedSite.commShift_sheafHomComplexFlip` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSourceShiftCommShift`, and the
descent `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift`.
What this file adds is the proof of the two coherence equations — at `b = 0` and under
`b₁ + b₂` — for the source-shift identification `SheafHom(K, M)[-b] ≅ SheafHom(K[b], M)`
(`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso`), which turns both into instances.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomComplexFlipCommShift`: **the internal Hom complex into
  a fixed complex commutes with the shift of its source.**
* `AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift`: **the derived internal Hom into
  a fixed object commutes with the shift of its source.**  This is one of the data whose
  absence the section "What this file does not contain" of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated`
  records.
* `AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShiftOfQ`,
  `AlgebraicGeometry.RingedSite.derivedSheafHomModelFlipCommShift` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomFlipLifting`: the same datum at the class of a
  complex, on the cochain-level model, and the lifting datum along which it is descended, named
  so that `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated`
  can prove the exactness of the descended functor.

## Main results

* `AlgebraicGeometry.RingedSite.sourceShiftHom_zero` and
  `AlgebraicGeometry.RingedSite.sourceShiftHom_comp`: the two coherence properties of the
  source shift of the internal Hom complex, in each degree.
* `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'_zero` and
  `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'_add`: the same at the level of
  complexes.
* `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso_zero` and
  `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso_add`: the hypotheses `hzero` and `hadd`
  of `AlgebraicGeometry.RingedSite.commShift_sheafHomComplexFlip`, proved.

## Implementation notes

The signs are the ones `CochainComplex.HomComplex.Cochain.leftShift` carries, so the additivity
coherence is the congruence `(b₁ + b₂) (b₁ + b₂ - 1) / 2 = b₁ (b₁ - 1) / 2 + b₂ (b₂ - 1) / 2 +
b₁ b₂` modulo `2`, which is `AlgebraicGeometry.RingedSite.sourceShiftSign_negOnePow`; the two
sign exponents differ by `2 b₁ b₂`, hence not at all after `Int.negOnePow`.

`Stacks.CategoryTheory.OppositeShift` collects the computations of the shift of the opposite
category that the coherence proofs need, in the form in which they are needed: the `unop` of a
component rather than the component, since the two spellings
`(CategoryTheory.shiftFunctor Cᵒᵖ n).obj K` and `op ((CategoryTheory.shiftFunctor C (-n)).obj
K.unop)` are definitionally but not syntactically equal, and the equation between the `unop`s
lives in `C`, where no such mismatch arises.

The universes are the diagonal `RingedSite.{u, u, u}` with modules in `u` for the bifunctor,
as the construction of the internal Hom complex forces; the degreewise coherence statements
need no relation between them and are stated at `RingedSite.{u, v, w}` with modules in `m`.

## What this file does not contain

The `CategoryTheory.Functor.IsTriangulated` half of the gap the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated` describe
is supplied by `AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated`, not here.

Nor is `CategoryTheory.NatTrans.CommShift (derivedTensorDualNatTrans X T M) ℤ` here: that is the
compatibility of the canonical map of Stacks 08JD with the shift, which is a statement about the
composition morphism of Stacks 0A98 in its outer variable, not about the derived internal Hom
alone. Its source `AlgebraicGeometry.RingedSite.tensorDualSourceFunctor` commutes with the shift
through the datum of this file and the `commShift_right` field of the derived tensor product
datum of Stacks 06YU, and nothing in that structure relates `commShift_right` to the comparisons
from which the canonical map is built, so the square is not a consequence of the fields of
`Stacks.SheafOfModules.DerivedTensorProduct` as they stand. The dévissage of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedTensorDual`
is arranged so as not to need it.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m u v w

namespace Stacks.CategoryTheory.OppositeShift

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- The shift by `n` of the opposite category, read on an object through `unop`, is the shift
by `-n`. -/
@[simp]
lemma shiftFunctor_op_obj_unop (K : Cᵒᵖ) (n : ℤ) :
    ((shiftFunctor Cᵒᵖ n).obj K).unop = (shiftFunctor C (-n)).obj K.unop := rfl

/-- The shift by `n` of the opposite category, read on a morphism through `unop`, is the shift
by `-n`. -/
@[simp]
lemma shiftFunctor_op_map_unop {K L : Cᵒᵖ} (f : K ⟶ L) (n : ℤ) :
    ((shiftFunctor Cᵒᵖ n).map f).unop = (shiftFunctor C (-n)).map f.unop := rfl

/-- `CategoryTheory.Pretriangulated.shiftFunctorOpIso` is the identity on `unop`s. -/
@[simp]
lemma shiftFunctorOpIso_hom_app_unop (K : Cᵒᵖ) (n : ℤ) :
    ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).hom.app K).unop = 𝟙 _ := rfl

/-- `CategoryTheory.Pretriangulated.shiftFunctorOpIso` is the identity on `unop`s. -/
@[simp]
lemma shiftFunctorOpIso_inv_app_unop (K : Cᵒᵖ) (n : ℤ) :
    ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).inv.app K).unop = 𝟙 _ := rfl

/-- `CategoryTheory.Pretriangulated.shiftFunctorOpIso` at `0` is the identity on `unop`s. -/
@[simp]
lemma shiftFunctorOpIso_zero_hom_app_unop (K : Cᵒᵖ) :
    ((shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app K).unop = 𝟙 _ := rfl

/-- `CategoryTheory.Pretriangulated.shiftFunctorOpIso` at `0` is the identity on `unop`s. -/
@[simp]
lemma shiftFunctorOpIso_zero_inv_app_unop (K : Cᵒᵖ) :
    ((shiftFunctorOpIso C 0 0 (zero_add 0)).inv.app K).unop = 𝟙 _ := rfl

/-- The `unop` of the inverse of the zero-shift identification of the opposite category is the
zero-shift identification of the category. -/
lemma shiftFunctorZero_op_inv_app_unop (K : Cᵒᵖ) :
    ((shiftFunctorZero Cᵒᵖ ℤ).inv.app K).unop = (shiftFunctorZero C ℤ).hom.app K.unop := by
  simp [Pretriangulated.shiftFunctorZero_op_inv_app]

/-- The `unop` of the inverse of the additivity identification of the shift of the opposite
category is the additivity identification of the shift of the category, at the negated
degrees. -/
lemma shiftFunctorAdd_op_inv_app_unop (K : Cᵒᵖ) (a b : ℤ) :
    ((shiftFunctorAdd Cᵒᵖ a b).inv.app K).unop =
      (shiftFunctorAdd' C (-a) (-b) (-(a + b)) (by omega)).hom.app K.unop := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd,
    Pretriangulated.shiftFunctorAdd'_op_inv_app K a b (a + b) rfl (-a) (-b) (-(a + b))
      (by omega) (by omega) (by omega)]
  dsimp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op]
  simp

end Stacks.CategoryTheory.OppositeShift

namespace AlgebraicGeometry.RingedSite

/-- For integers `b₁` and `b₂`, the triangular numbers satisfy
`b₁(b₁ - 1)/2 + b₂(b₂ - 1)/2 + b₁b₂ = (b₁ + b₂)(b₁ + b₂ - 1)/2`. -/
theorem sourceShiftSign_add (b₁ b₂ : ℤ) :
    b₁ * (b₁ - 1) / 2 + b₂ * (b₂ - 1) / 2 + b₁ * b₂ = (b₁ + b₂) * ((b₁ + b₂) - 1) / 2 := by
  obtain ⟨k₁, hk₁⟩ := Int.even_mul_pred_self b₁
  obtain ⟨k₂, hk₂⟩ := Int.even_mul_pred_self b₂
  have h : (b₁ + b₂) * ((b₁ + b₂) - 1) = (k₁ + k₂ + b₁ * b₂) + (k₁ + k₂ + b₁ * b₂) := by
    have e : (b₁ + b₂) * ((b₁ + b₂) - 1) = b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + 2 * (b₁ * b₂) := by
      ring
    rw [e, hk₁, hk₂]; ring
  rw [hk₁, hk₂, h]
  omega

/-- If `n₁ = n + b₁`, `n₁₂ = n₁ + b₂` and `b₁₂ = b₁ + b₂`, then the signs
`(-1) ^ (b₁ n₁ + b₁(b₁ - 1)/2)` and `(-1) ^ (b₂ n₁₂ + b₂(b₂ - 1)/2)` multiply to
`(-1) ^ (b₁₂ n₁₂ + b₁₂(b₁₂ - 1)/2)`. -/
theorem sourceShiftSign_negOnePow (n b₁ b₂ n₁ n₁₂ b₁₂ : ℤ)
    (h₁ : n + b₁ = n₁) (h₂ : n₁ + b₂ = n₁₂) (hb : b₁ + b₂ = b₁₂) :
    (b₁ * n₁ + b₁ * (b₁ - 1) / 2).negOnePow * (b₂ * n₁₂ + b₂ * (b₂ - 1) / 2).negOnePow =
      (b₁₂ * n₁₂ + b₁₂ * (b₁₂ - 1) / 2).negOnePow := by
  subst h₁ h₂ hb
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, ← sourceShiftSign_add b₁ b₂]
  exact ⟨-(b₁ * b₂), by ring⟩

section Chain

variable (X : RingedSite.{u, v, w})
variable {K M : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Restriction to a slice carries the canonical identification of two equal degrees of a
complex to the corresponding identification of the restricted complex. -/
lemma over_XIsoOfEq_hom (U : X.C) {p q : ℤ} (h : p = q) :
    SheafOfModules.Hom.over (HomologicalComplex.XIsoOfEq K h).hom U =
      (HomologicalComplex.XIsoOfEq (restrictComplex X K U) h).hom := by
  subst h
  simp

/-- `cochainSourceShift_v` with the source index of the unshifted cochain given freely. -/
lemma cochainSourceShift_v' (U : X.C) (b n n' : ℤ) (hn' : n + b = n')
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) (p q p' : ℤ)
    (hpq : p + n' = q) (hp' : p' + n = q) :
    (cochainSourceShift X U b n n' hn' c).v p q hpq =
      (b * n' + b * (b - 1) / 2).negOnePow •
        ((restrictComplex X K U).XIsoOfEq (show p + b = p' by omega)).hom ≫ c.v p' q hp' := by
  obtain rfl : p' = p + b := by omega
  rw [cochainSourceShift_v X U b n n' hn' c p q hpq]
  simp


/-- Shifting the source of a cochain by `0` is undone by the canonical identification of `K`
with `K[0]`. -/
lemma cochainConj_cochainSourceShift_zero (U : X.C) (n : ℤ)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U
        ((CategoryTheory.shiftFunctorZero
          (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            ℤ).inv.app K) (𝟙 M)
        (cochainSourceShift X U 0 n n (add_zero n) c) = c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, cochainSourceShift_v' X U 0 n n (add_zero n) c p q p hpq (by omega)]
  rw [CochainComplex.shiftFunctorZero_inv_app_f, over_XIsoOfEq_hom]
  simp

/-- Shifting the source of a cochain by `b₁` and then by `b₂` is shifting it by `b₁ + b₂`, read
through the canonical identification of `K[b₁ + b₂]` with `K[b₁][b₂]`. -/
lemma cochainConj_cochainSourceShift_cochainSourceShift (U : X.C)
    (b₁ b₂ b₁₂ n n₁ n₁₂ : ℤ) (hb : b₁ + b₂ = b₁₂) (h₁ : n + b₁ = n₁) (h₂ : n₁ + b₂ = n₁₂)
    (c : Cochain (restrictComplex X K U) (restrictComplex X M U) n) :
    cochainConj X U
        ((CategoryTheory.shiftFunctorAdd'
          (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            b₁ b₂ b₁₂ hb).hom.app K) (𝟙 M)
        (cochainSourceShift X U b₂ n₁ n₁₂ h₂ (cochainSourceShift X U b₁ n n₁ h₁ c)) =
      cochainSourceShift X U b₁₂ n n₁₂ (by omega) c := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainConj_v, cochainSourceShift_v X U b₂ n₁ n₁₂ h₂ _ p q hpq,
    cochainSourceShift_v X U b₁ n n₁ h₁ c (p + b₂) q (by omega),
    cochainSourceShift_v' X U b₁₂ n n₁₂ (by omega) c p q (p + b₂ + b₁) hpq (by omega),
    ← sourceShiftSign_negOnePow n b₁ b₂ n₁ n₁₂ b₁₂ h₁ h₂ hb]
  rw [CochainComplex.shiftFunctorAdd'_hom_app_f', over_XIsoOfEq_hom]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.comp_id,
    Linear.units_smul_comp, Linear.comp_units_smul, mul_smul]
  rw [smul_comm]
  simp


/-- **Shifting the source by `0`.**  The degree-`n` source-shift identification at `b = 0`,
followed by the map induced by the canonical identification of `K` with `K[0]`, is the
canonical identification of the two degrees. -/
lemma sourceShiftHom_zero (n n' : ℤ) (hn' : n + 0 = n') :
    sourceShiftHom X (K := K) (M := M) 0 n n' hn' ≫
        homMapHom X ((CategoryTheory.shiftFunctorZero
          (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            ℤ).inv.app K) (𝟙 M) n' =
      ((sheafHomComplex X K M).obj.XIsoOfEq (show n = n' by omega)).hom := by
  obtain rfl : n' = n := by omega
  refine sheafHom_ext X fun U s => ?_
  apply ((sheafHomComplex X K M).sectionsEquiv U n').injective
  rw [comp_val_app_apply, sectionsEquiv_homMapHom, sectionsEquiv_sourceShiftHom,
    cochainConj_cochainSourceShift_zero]
  simp

/-- **Shifting the source by `b₁` and then by `b₂`.**  The two one-step source-shift
identifications, followed by the map induced by the canonical identification of `K[b₁ + b₂]`
with `K[b₁][b₂]`, are the source-shift identification at `b₁ + b₂`. -/
lemma sourceShiftHom_comp (b₁ b₂ b₁₂ n n₁ n₁₂ : ℤ) (hb : b₁ + b₂ = b₁₂)
    (h₁ : n + b₁ = n₁) (h₂ : n₁ + b₂ = n₁₂) :
    sourceShiftHom X (K := K) (M := M) b₁ n n₁ h₁ ≫
        sourceShiftHom X (K := K⟦b₁⟧) (M := M) b₂ n₁ n₁₂ h₂ ≫
        homMapHom X ((CategoryTheory.shiftFunctorAdd'
          (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            b₁ b₂ b₁₂ hb).hom.app K)
          (𝟙 M) n₁₂ =
      sourceShiftHom X (K := K) (M := M) b₁₂ n n₁₂ (by omega) := by
  refine sheafHom_ext X fun U s => ?_
  apply ((sheafHomComplex X (K⟦b₁₂⟧) M).sectionsEquiv U n₁₂).injective
  simp only [comp_val_app_apply, sectionsEquiv_homMapHom, CategoryTheory.Functor.comp_obj,
    sectionsEquiv_sourceShiftHom,
    cochainConj_cochainSourceShift_cochainSourceShift X U b₁ b₂ b₁₂ n n₁ n₁₂ hb h₁ h₂]


end Chain

section Diagonal

variable (X : RingedSite.{u, u, u})
variable {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The degreewise components of `sheafHomSourceShiftIso'`. -/
@[simp]
lemma sheafHomSourceShiftIso'_hom_f (b c : ℤ) (hc : b + c = 0) (n : ℤ) :
    (sheafHomSourceShiftIso' X (K := K) (M := M) b c hc).hom.f n =
      sourceShiftHom X b (n + c) n (by omega) := by
  obtain rfl : c = -b := by omega
  simp [sheafHomSourceShiftIso']

/-- Reindexing the source degree of the source-shift identification. -/
lemma XIsoOfEq_hom_comp_sourceShiftHom (b n n'' n' : ℤ) (h : n = n'') (hn' : n'' + b = n') :
    ((sheafHomComplex X K M).obj.XIsoOfEq h).hom ≫ sourceShiftHom X b n'' n' hn' =
      sourceShiftHom X (K := K) (M := M) b n n' (by omega) := by
  subst h
  simp

/-- **The source-shift identification at `b = 0`**, at the level of complexes. -/
lemma sheafHomSourceShiftIso'_zero :
    (sheafHomSourceShiftIso' X (K := K) (M := M) 0 0 (by omega)).hom ≫
        homMap X ((CategoryTheory.shiftFunctorZero _ ℤ).inv.app K) (𝟙 M) =
      (CategoryTheory.shiftFunctorZero _ ℤ).hom.app ((sheafHomComplex X K M).obj) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  rw [HomologicalComplex.comp_f, sheafHomSourceShiftIso'_hom_f, homMap_f,
    sourceShiftHom_zero, CochainComplex.shiftFunctorZero_hom_app_f]

/-- **The source-shift identification at a sum**, at the level of complexes. -/
lemma sheafHomSourceShiftIso'_add (b₁ b₂ b₁₂ c₁ c₂ c₁₂ : ℤ) (hb : b₁ + b₂ = b₁₂)
    (h₁ : b₁ + c₁ = 0) (h₂ : b₂ + c₂ = 0) (h₁₂ : b₁₂ + c₁₂ = 0) :
    (sheafHomSourceShiftIso' X (K := K) (M := M) b₁₂ c₁₂ h₁₂).hom =
      (CategoryTheory.shiftFunctorAdd' _ c₁ c₂ c₁₂ (by omega)).hom.app
            ((sheafHomComplex X K M).obj) ≫
        (CategoryTheory.shiftFunctor _ c₂).map
            (sheafHomSourceShiftIso' X (K := K) (M := M) b₁ c₁ h₁).hom ≫
        (sheafHomSourceShiftIso' X (K := K⟦b₁⟧) (M := M) b₂ c₂ h₂).hom ≫
        homMap X ((CategoryTheory.shiftFunctorAdd' _ b₁ b₂ b₁₂ hb).hom.app K) (𝟙 M) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctor_map_f', sheafHomSourceShiftIso'_hom_f, homMap_f]
  rw [sourceShiftHom_comp X b₁ b₂ b₁₂ (p + c₂ + c₁) (p + c₂) p hb (by omega) (by omega),
    XIsoOfEq_hom_comp_sourceShiftHom]

end Diagonal


section FunctorLevel

open Pretriangulated Pretriangulated.Opposite

attribute [local implicit_reducible] sheafHomComplexBifunctor

variable (X : RingedSite.{u, u, u})
  (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The inverse components of the commutation datum
`AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso`: at `op K` it is the source-shift
identification `SheafHom(K, M)[n] ≅ SheafHom(K[-n], M)`. -/
lemma sheafHomOpCommShiftIso_inv_app (n : ℤ)
    (K : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ) :
    (sheafHomOpCommShiftIso X M n).inv.app K =
      (sheafHomSourceShiftIso' X (K := K.unop) (M := M) (-n) n (by omega)).hom :=
  rfl

/-- The inverse components of `sheafHomOpCommShiftIso` at `n = 0`, with the degree of the shift
of the source written `0` rather than `-0`. -/
lemma sheafHomOpCommShiftIso_zero_inv_app
    (K : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ) :
    (sheafHomOpCommShiftIso X M 0).inv.app K =
      (sheafHomSourceShiftIso' X (K := K.unop) (M := M) 0 0 (by omega)).hom :=
  rfl

/-- The contravariant functor `SheafHom(-, M)` acts on a morphism of `K(O)ᵒᵖ` by
precomposition. -/
lemma sheafHomComplexFlip_map
    {K K' : (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ}
    (k : K ⟶ K') :
    ((sheafHomComplexBifunctor X).flip.obj M).map k = homMap X k.unop (𝟙 M) :=
  rfl

/-- The source-shift identification at `b = 0`, in the form the zero axiom of a
`CategoryTheory.Functor.CommShift` asks for. -/
lemma sheafHomSourceShiftIso'_zero'
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomSourceShiftIso' X (K := K) (M := M) 0 0 (by omega)).hom =
      (CategoryTheory.shiftFunctorZero _ ℤ).hom.app ((sheafHomComplex X K M).obj) ≫
        homMap X ((CategoryTheory.shiftFunctorZero _ ℤ).hom.app K) (𝟙 M) := by
  rw [← sheafHomSourceShiftIso'_zero X (K := K) (M := M), Category.assoc, homMap_comp,
    Iso.hom_inv_id_app, Category.comp_id, homMap_id, Category.comp_id]

/-- **The zero coherence of the commutation datum of the contravariant internal Hom complex.**
This is the hypothesis `hzero` of `AlgebraicGeometry.RingedSite.commShift_sheafHomComplexFlip`,
proved: it is `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'_zero` read on the opposite
category. -/
theorem sheafHomOpCommShiftIso_zero :
    sheafHomOpCommShiftIso X M 0 =
      Functor.CommShift.isoZero ((sheafHomComplexBifunctor X).flip.obj M) ℤ := by
  refine Iso.ext_inv (NatTrans.ext (funext fun K => ?_))
  rw [sheafHomOpCommShiftIso_zero_inv_app,
    Functor.CommShift.isoZero_inv_app, sheafHomComplexFlip_map,
    Stacks.CategoryTheory.OppositeShift.shiftFunctorZero_op_inv_app_unop]
  exact sheafHomSourceShiftIso'_zero' X M K.unop

/-- **The additivity coherence of the commutation datum of the contravariant internal Hom
complex.** This is the hypothesis `hadd` of
`AlgebraicGeometry.RingedSite.commShift_sheafHomComplexFlip`, proved: it is
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'_add` read on the opposite category, the
sign bookkeeping being `AlgebraicGeometry.RingedSite.sourceShiftSign_negOnePow`. -/
theorem sheafHomOpCommShiftIso_add (a b : ℤ) :
    sheafHomOpCommShiftIso X M (a + b) =
      Functor.CommShift.isoAdd (sheafHomOpCommShiftIso X M a) (sheafHomOpCommShiftIso X M b) := by
  refine Iso.ext_inv (NatTrans.ext (funext fun K => ?_))
  rw [sheafHomOpCommShiftIso_inv_app,
    Functor.CommShift.isoAdd_inv_app,
    sheafHomOpCommShiftIso_inv_app,
    sheafHomOpCommShiftIso_inv_app,
    sheafHomComplexFlip_map,
    Stacks.CategoryTheory.OppositeShift.shiftFunctorAdd_op_inv_app_unop,
    ← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd]
  exact sheafHomSourceShiftIso'_add X (K := K.unop) (M := M) (-a) (-b) (-(a + b)) a b (a + b)
    (by omega) (by omega) (by omega) (by omega)

/-- **The internal Hom complex into a fixed complex commutes with the shift of its source.**
The commutation isomorphism is `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso`, and its two
coherence equations are `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso_zero` and
`AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso_add`. -/
noncomputable instance sheafHomComplexFlipCommShift :
    ((sheafHomComplexBifunctor X).flip.obj M).CommShift ℤ :=
  commShift_sheafHomComplexFlip X M (sheafHomOpCommShiftIso_zero X M)
    (sheafHomOpCommShiftIso_add X M)

/-- The commutation isomorphism of `sheafHomComplexFlipCommShift` is
`AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso`. -/
lemma sheafHomComplexFlip_commShiftIso (n : ℤ) :
    ((sheafHomComplexBifunctor X).flip.obj M).commShiftIso n = sheafHomOpCommShiftIso X M n :=
  rfl

end FunctorLevel


section Derived

open Pretriangulated Pretriangulated.Opposite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The model of the derived internal Hom in its fixed variable commutes with the shift of its
source.**  This is `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomModelFlip` with its
cochain-level input supplied by `AlgebraicGeometry.RingedSite.sheafHomComplexFlipCommShift`. -/
@[instance_reducible]
noncomputable def derivedSheafHomModelFlipCommShift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomModel X).flip.obj N).CommShift ℤ :=
  commShift_derivedSheafHomModelFlip X (fun _ => inferInstance) N

attribute [local instance] derivedSheafHomBifunctorLifting in
/-- The derived internal Hom in a fixed variable lifts the model in that variable along the
localization `DerivedCategory.Q.op` of the source variable: the lifting datum of
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` evaluated at the fixed variable, which
is the one `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlipOfQ` descends along. -/
@[instance_reducible]
noncomputable def derivedSheafHomFlipLifting
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Localization.Lifting DerivedCategory.Q.op
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).op
      ((derivedSheafHomModel X).flip.obj N)
      ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N)) :=
  Localization.Lifting₂.snd DerivedCategory.Q.op DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).op
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (derivedSheafHomModel X) (derivedSheafHomBifunctor X) N

/-- **The derived internal Hom into the class of a complex commutes with the shift of its
source.**  This is `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlipOfQ` with its
cochain-level input supplied by `AlgebraicGeometry.RingedSite.sheafHomComplexFlipCommShift`. -/
@[instance_reducible]
noncomputable def derivedSheafHomFlipCommShiftOfQ
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N)).CommShift ℤ :=
  commShift_derivedSheafHomFlipOfQ X (fun _ => inferInstance) N

/-- **The derived internal Hom into a fixed object commutes with the shift of its source**:
`RSheafHom(L⟦-n⟧, M) ≅ RSheafHom(L, M)⟦n⟧`, coherently in `n`, the shift of `D(O)ᵒᵖ` being the
one of `CategoryTheory.Pretriangulated.Opposite`.

This is `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` with its cochain-level input
supplied by `AlgebraicGeometry.RingedSite.sheafHomComplexFlipCommShift`. -/
noncomputable instance derivedSheafHomFlipCommShift
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).flip.obj M).CommShift ℤ :=
  commShift_derivedSheafHomFlip X (fun _ => inferInstance) M

end Derived

end AlgebraicGeometry.RingedSite

end
