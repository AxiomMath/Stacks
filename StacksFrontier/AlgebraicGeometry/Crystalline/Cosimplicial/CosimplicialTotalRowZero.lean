module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9

/-!
# The projection of the total complex of a cosimplicial complex onto its row zero

Let `K` be a cochain complex of cosimplicial abelian groups, and `Tot(K)` the total complex of
its double complex `(a, b) ↦ K^a(⦋b⦌)` (`Crystalline.cosimplicialDoubleComplexFunctor`), the
cosimplicial direction `b` carrying the alternating coface differential.  No differential enters
the row `b = 0` from the cosimplicial direction, so projecting onto the summands with `b = 0` is a
morphism of complexes

`Tot(K) ⟶ K^*(⦋0⦌)`

onto the row zero (`Crystalline.cosimplicialTotalToRowZero`).  This file proves that it is a
quasi-isomorphism as soon as every **codiagonal** `K^*(⦋b⦌) ⟶ K^*(⦋0⦌)` (induced by the unique map
`⦋b⦌ ⟶ ⦋0⦌`), equivalently every **coprojection** `K^*(⦋0⦌) ⟶ K^*(⦋b⦌)` (induced by
`⦋0⦌ ⟶ ⦋b⦌, 0 ↦ 0`), is a quasi-isomorphism.

This is the second degeneration of the proof of [Stacks, Proposition 60.21.3, Tag 07LG] read at
the level of the *map*: there the rows `K^{*,b} = M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` are
quasi-isomorphic to the row zero along the coprojections ([Stacks, Lemma 60.21.2, Tag 07LD]).
The library's zigzag
`Crystalline.CosimplicialCompletedPair.zigzagTotal` goes through the total complex of the constant
double complex on the row zero; the projection of this file is that leg followed by the projection
of the constant double complex onto its row zero, which is a left inverse of
`Crystalline.cosimplicialRowZeroToTotal`
(`cosimplicialRowZeroToTotal_comp_cosimplicialTotalToRowZero`).

## Main definitions

* `Crystalline.cosimplicialFlipTotalToRowZero` — the projection from the total complex of the flip
  (the shape in which the Čech double complexes of the crystalline site are stated).
* `Crystalline.cosimplicialTotalToRowZero` — the projection `Tot(K) ⟶ K^*(⦋0⦌)`.
* `Crystalline.cosimplicialCodiagonal` — the morphism `K ⟶ Const(K^*(⦋0⦌))` induced by the unique
  maps `⦋b⦌ ⟶ ⦋0⦌`.
* `Crystalline.cosimplicialRowCoprojection` — the coprojection `K^*(⦋0⦌) ⟶ K^*(⦋b⦌)`.

## Main results

* `Crystalline.ιTotal_cosimplicialFlipTotalToRowZero_f` — on the summand `(0, a)` the projection
  is the identification of the row zero.
* `Crystalline.cosimplicialFlipTotalToRowZero_naturality`,
  `Crystalline.cosimplicialTotalToRowZero_naturality` — the projection is natural in `K`.
* `Crystalline.cosimplicialRowZeroToTotal_comp_cosimplicialTotalToRowZero` — for a constant `K`
  the projection is a left inverse of the inclusion of the row zero.
* **`Crystalline.quasiIso_cosimplicialTotalToRowZero`** — the projection is a quasi-isomorphism
  when every codiagonal is one; `...quasiIso_cosimplicialTotalToRowZero_of_coprojection` — the same
  when every coprojection is one.
* `Crystalline.quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_of_rows` — the hypothesis
  transfers along a morphism `K ⟶ K'` which is a quasi-isomorphism on every row.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe u

noncomputable section

namespace Crystalline

open StacksDraft.TotalComplexQuasiIso

attribute [local instance] StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn
  StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit

section Projection

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- The row `-1` of the double complex of `K` vanishes. -/
theorem isZero_cosimplicialDoubleComplex_flip_X_neg_one :
    IsZero ((cosimplicialDoubleComplexFunctor.obj K).flip.X ((0 : ℤ) - 1)) :=
  StacksDraft.TotalDegeneration.isZero_of_isZero_X
    (fun a => isZero_cosimplicialDoubleComplex_flip_X_X_of_neg K (by omega) a)

/-- **The projection of the total complex of the flip onto the row zero**: the projection
`StacksDraft.TotalComplexQuasiIso.bottomProj` of the flip onto its column `0`, followed by the
identification of the total complex of a double complex concentrated in the column `0` with that
column, and by `Crystalline.cosimplicialDoubleComplexRowIso`. -/
def cosimplicialFlipTotalToRowZero :
    (cosimplicialDoubleComplexFunctor.obj K).flip.total (ComplexShape.up ℤ) ⟶
      (cosimplicialRowComplex K 0).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex₂.total.map
      (bottomProj _ 0 (isZero_cosimplicialDoubleComplex_flip_X_neg_one K)) (ComplexShape.up ℤ) ≫
    inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K).flip.X 0) 0) ≫
    (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app _ ≫
    (cosimplicialDoubleComplexRowIso K 0).hom

/-- **On the summand `(0, a)` the projection is the identification of the row zero.** -/
theorem ιTotal_cosimplicialFlipTotalToRowZero_f (a : ℕ) :
    (cosimplicialDoubleComplexFunctor.obj K).flip.ιTotal (ComplexShape.up ℤ) 0 a a (by simp) ≫
        (cosimplicialFlipTotalToRowZero K).f a =
      (cosimplicialDoubleComplexRowIso K 0).hom.f a := by
  let W := (cosimplicialDoubleComplexFunctor.obj K).flip.X 0
  have hu : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 W).inv.f (a : ℤ) ≫
      (StacksDraft.TotalComplexQuasiIso.singleColumn W 0).ιTotal (ComplexShape.up ℤ) 0 a a
        (by simp) = (totalSingleColumnUnit W 0).f a := rfl
  have hinv : (totalSingleColumnUnit W 0).f a ≫ (inv (totalSingleColumnUnit W 0)).f a = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
  have hs : ((shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app W).f a = 𝟙 _ := by
    rw [CochainComplex.shiftFunctorZero_hom_app_f]
    rfl
  simp only [cosimplicialFlipTotalToRowZero, HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc, bottomProj_f_self]
  rw [reassoc_of% hu, reassoc_of% hinv, hs]
  exact Category.id_comp _

variable {K} in
/-- **The projection of the flip is natural in `K`.** -/
theorem cosimplicialFlipTotalToRowZero_naturality
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K') :
    HomologicalComplex₂.total.map
        (StacksDraft.TotalRowComparison.flipMap (cosimplicialDoubleComplexFunctor.map f))
        (ComplexShape.up ℤ) ≫ cosimplicialFlipTotalToRowZero K' =
      cosimplicialFlipTotalToRowZero K ≫
        HomologicalComplex.extendMap (cosimplicialRowMap f 0) ComplexShape.embeddingUpNat := by
  let φ := StacksDraft.TotalRowComparison.flipMap (cosimplicialDoubleComplexFunctor.map f)
  have h1 := bottomProj_naturality φ 0
    (isZero_cosimplicialDoubleComplex_flip_X_neg_one K)
    (isZero_cosimplicialDoubleComplex_flip_X_neg_one K')
  have h2 := totalSingleColumnUnit_naturality (φ.f 0) 0
  have h3 : (shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (-0 : ℤ)).map (φ.f 0) ≫
      (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app
        ((cosimplicialDoubleComplexFunctor.obj K').flip.X 0) =
      (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app
        ((cosimplicialDoubleComplexFunctor.obj K).flip.X 0) ≫ φ.f 0 :=
    (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.naturality (φ.f 0)
  have h4 : φ.f 0 ≫ (cosimplicialDoubleComplexRowIso K' 0).hom =
      (cosimplicialDoubleComplexRowIso K 0).hom ≫
        HomologicalComplex.extendMap (cosimplicialRowMap f 0) ComplexShape.embeddingUpNat :=
    cosimplicialDoubleComplexRowIso_naturality f 0
  have h2' : inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K).flip.X 0) 0) ≫
      (shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (-0 : ℤ)).map (φ.f 0) =
      HomologicalComplex₂.total.map ((HomologicalComplex.single
        (CochainComplex AddCommGrpCat.{u} ℤ) (ComplexShape.up ℤ) 0).map (φ.f 0))
          (ComplexShape.up ℤ) ≫
        inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K').flip.X 0) 0) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← h2, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [cosimplicialFlipTotalToRowZero, Category.assoc]
  rw [← HomologicalComplex₂.total.map_comp_assoc, ← h1, HomologicalComplex₂.total.map_comp_assoc,
    ← reassoc_of% h2', reassoc_of% h3, h4]

/-- **The projection `Tot(K) ⟶ K^*(⦋0⦌)` of the total complex onto the row zero**: the
identification of `Tot(K)` with the total complex of the flip, followed by
`Crystalline.cosimplicialFlipTotalToRowZero`. -/
def cosimplicialTotalToRowZero :
    (cosimplicialDoubleComplexFunctor.obj K).total (ComplexShape.up ℤ) ⟶
      (cosimplicialRowComplex K 0).extend ComplexShape.embeddingUpNat :=
  ((cosimplicialDoubleComplexFunctor.obj K).totalFlipIso (ComplexShape.up ℤ)).inv ≫
    cosimplicialFlipTotalToRowZero K

variable {K} in
/-- **The projection onto the row zero is natural in `K`.** -/
theorem cosimplicialTotalToRowZero_naturality
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K') :
    cosimplicialTotalMap f ≫ cosimplicialTotalToRowZero K' =
      cosimplicialTotalToRowZero K ≫
        HomologicalComplex.extendMap (cosimplicialRowMap f 0) ComplexShape.embeddingUpNat := by
  have key := StacksDraft.TotalComplexQuasiIso.totalFlipIso_naturality
    (cosimplicialDoubleComplexFunctor.map f)
  have e : cosimplicialTotalMap f ≫
      ((cosimplicialDoubleComplexFunctor.obj K').totalFlipIso (ComplexShape.up ℤ)).inv =
      ((cosimplicialDoubleComplexFunctor.obj K).totalFlipIso (ComplexShape.up ℤ)).inv ≫
        HomologicalComplex₂.total.map
          (StacksDraft.TotalRowComparison.flipMap (cosimplicialDoubleComplexFunctor.map f))
          (ComplexShape.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, key, Iso.inv_hom_id_assoc]
    rfl
  rw [cosimplicialTotalToRowZero, cosimplicialTotalToRowZero, reassoc_of% e,
    cosimplicialFlipTotalToRowZero_naturality, Category.assoc]

end Projection

section Constant

variable (R : CochainComplex AddCommGrpCat.{u} ℕ)

/-- **For a constant cosimplicial complex the projection onto the row zero is a left inverse of
the inclusion of the row zero** `Crystalline.cosimplicialRowZeroToTotal`. -/
theorem cosimplicialRowZeroToTotal_comp_cosimplicialTotalToRowZero :
    cosimplicialRowZeroToTotal R ≫
        cosimplicialTotalToRowZero (constantCosimplicialCochainComplex.obj R) =
      𝟙 (R.extend ComplexShape.embeddingUpNat) := by
  let L := constantCosimplicialCochainComplex.obj R
  ext n : 1
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    let Z := cosimplicialDoubleComplexFunctor.obj L
    have hσ : ComplexShape.σ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (n : ℤ) 0 = 1 := by
      change ((n : ℤ) * 0).negOnePow = 1
      simp
    have hkey : Z.ιTotal (ComplexShape.up ℤ) (n : ℤ) 0 n (by simp) ≫
        (Z.totalFlipIso (ComplexShape.up ℤ)).inv.f n ≫ (cosimplicialFlipTotalToRowZero L).f n =
        (cosimplicialDoubleComplexRowIso L 0).hom.f n := by
      rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv_assoc, hσ, one_smul]
      exact ιTotal_cosimplicialFlipTotalToRowZero_f L n
    have hio : (cosimplicialConstRowZeroIso R).inv.f n ≫
        (cosimplicialDoubleComplexRowIso L 0).hom.f n = 𝟙 _ :=
      congrArg (fun φ => HomologicalComplex.Hom.f φ (n : ℤ))
        (Iso.inv_hom_id (cosimplicialDoubleComplexRowIso L 0))
    rw [HomologicalComplex.id_f, ← hio]
    simp only [cosimplicialRowZeroToTotal, cosimplicialTotalToRowZero, HomologicalComplex.comp_f,
      Category.assoc, StacksDraft.TotalRowComparison.rowZeroTotalMap_f]
    exact congrArg ((cosimplicialConstRowZeroIso R).inv.f n ≫ ·) hkey
  · exact (HomologicalComplex.isZero_extend_X _ _ _
      (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)).eq_of_src _ _

/-- **For a constant cosimplicial complex the projection onto the row zero is a
quasi-isomorphism**, being a left inverse of the quasi-isomorphism
`Crystalline.cosimplicialRowZeroToTotal`. -/
instance quasiIso_cosimplicialTotalToRowZero_const :
    QuasiIso (cosimplicialTotalToRowZero (constantCosimplicialCochainComplex.obj R)) := by
  have : QuasiIso (cosimplicialRowZeroToTotal R ≫
      cosimplicialTotalToRowZero (constantCosimplicialCochainComplex.obj R)) := by
    rw [cosimplicialRowZeroToTotal_comp_cosimplicialTotalToRowZero]
    exact (inferInstance : QuasiIso (𝟙 (R.extend ComplexShape.embeddingUpNat)))
  exact quasiIso_of_comp_left (cosimplicialRowZeroToTotal R) _

end Constant

section Codiagonal

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- **The codiagonal `K ⟶ Const(K^*(⦋0⦌))`**: in the simplex `m` and the degree `a` it is the map
`K^a(m) ⟶ K^a(⦋0⦌)` induced by the unique map `m ⟶ ⦋0⦌`. -/
def cosimplicialCodiagonal :
    K ⟶ constantCosimplicialCochainComplex.obj (cosimplicialRowComplex K 0) :=
  CosimplicialDoubleComplex.constHom (K := K) (cosimplicialRowComplex K 0)
    (fun a m => (K.X a).map (SimplexCategory.const m ⦋0⦌ 0))
    (fun a _ n φ => ((K.X a).map_comp φ (SimplexCategory.const n ⦋0⦌ 0)).symm.trans
      (congrArg (K.X a).map (CosimplicialCompletedPair.hom_toZero_ext _ _)))
    (fun a a' m => (K.d a a').naturality (SimplexCategory.const m ⦋0⦌ 0))

/-- The row `b` of the codiagonal is induced by the unique map `⦋b⦌ ⟶ ⦋0⦌`. -/
theorem cosimplicialRowMap_cosimplicialCodiagonal_f (b a : ℕ) :
    (cosimplicialRowMap (cosimplicialCodiagonal K) b).f a =
      (K.X a).map (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) := rfl

/-- The row zero of the codiagonal is the identity. -/
theorem cosimplicialRowMap_cosimplicialCodiagonal_zero :
    cosimplicialRowMap (cosimplicialCodiagonal K) 0 = 𝟙 (cosimplicialRowComplex K 0) := by
  ext a : 1
  rw [cosimplicialRowMap_cosimplicialCodiagonal_f, HomologicalComplex.id_f,
    show SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ from CosimplicialCompletedPair.hom_toZero_ext _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The coprojection `K^*(⦋0⦌) ⟶ K^*(⦋b⦌)`**, induced by `⦋0⦌ ⟶ ⦋b⦌, 0 ↦ 0`. -/
def cosimplicialRowCoprojection (b : ℕ) :
    cosimplicialRowComplex K 0 ⟶ cosimplicialRowComplex K b where
  f a := (K.X a).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)
  comm' a a' _ := (K.d a a').naturality (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)

/-- The coprojection followed by the codiagonal is the identity. -/
theorem cosimplicialRowCoprojection_comp_cosimplicialRowMap_cosimplicialCodiagonal (b : ℕ) :
    cosimplicialRowCoprojection K b ≫ cosimplicialRowMap (cosimplicialCodiagonal K) b =
      𝟙 (cosimplicialRowComplex K 0) := by
  ext a : 1
  rw [HomologicalComplex.comp_f, cosimplicialRowMap_cosimplicialCodiagonal_f,
    HomologicalComplex.id_f]
  change (K.X a).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) ≫
      (K.X a).map (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp,
    show SimplexCategory.const ⦋0⦌ ⦋b⦌ 0 ≫ SimplexCategory.const ⦋b⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ from
      CosimplicialCompletedPair.hom_toZero_ext _ _, CategoryTheory.Functor.map_id]

/-- A coprojection is a quasi-isomorphism if and only if the codiagonal of the same row is. -/
theorem quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_iff (b : ℕ) :
    QuasiIso (cosimplicialRowMap (cosimplicialCodiagonal K) b) ↔
      QuasiIso (cosimplicialRowCoprojection K b) := by
  have h := cosimplicialRowCoprojection_comp_cosimplicialRowMap_cosimplicialCodiagonal K b
  constructor
  · intro _
    have : QuasiIso (cosimplicialRowCoprojection K b ≫
        cosimplicialRowMap (cosimplicialCodiagonal K) b) := by
      rw [h]; exact (inferInstance : QuasiIso (𝟙 (cosimplicialRowComplex K 0)))
    exact quasiIso_of_comp_right _ (cosimplicialRowMap (cosimplicialCodiagonal K) b)
  · intro _
    have : QuasiIso (cosimplicialRowCoprojection K b ≫
        cosimplicialRowMap (cosimplicialCodiagonal K) b) := by
      rw [h]; exact (inferInstance : QuasiIso (𝟙 (cosimplicialRowComplex K 0)))
    exact quasiIso_of_comp_left (cosimplicialRowCoprojection K b) _

/-- **The projection `Tot(K) ⟶ K^*(⦋0⦌)` is the comparison with the constant double complex on the
row zero, followed by the projection of the latter onto its row zero.** -/
theorem cosimplicialTotalToRowZero_eq :
    cosimplicialTotalToRowZero K =
      cosimplicialTotalMap (cosimplicialCodiagonal K) ≫
        cosimplicialTotalToRowZero
          (constantCosimplicialCochainComplex.obj (cosimplicialRowComplex K 0)) := by
  have h : HomologicalComplex.extendMap (cosimplicialRowMap (cosimplicialCodiagonal K) 0)
      ComplexShape.embeddingUpNat = 𝟙 _ :=
    (congrArg (fun g => HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
      (cosimplicialRowMap_cosimplicialCodiagonal_zero K)).trans
        (HomologicalComplex.extendMap_id _ _)
  rw [cosimplicialTotalToRowZero_naturality, h]
  exact (Category.comp_id _).symm

/-- **The projection of the total complex onto the row zero is a quasi-isomorphism** as soon as
every codiagonal `K^*(⦋b⦌) ⟶ K^*(⦋0⦌)` is one. -/
theorem quasiIso_cosimplicialTotalToRowZero
    (h : ∀ b : ℕ, QuasiIso (cosimplicialRowMap (cosimplicialCodiagonal K) b)) :
    QuasiIso (cosimplicialTotalToRowZero K) := by
  have := quasiIso_cosimplicialTotalMap (cosimplicialCodiagonal K)
    (quasiIso_flipMap_of_quasiIso_row (cosimplicialCodiagonal K) h)
  rw [cosimplicialTotalToRowZero_eq]
  exact quasiIso_comp _ (cosimplicialTotalToRowZero
    (constantCosimplicialCochainComplex.obj (cosimplicialRowComplex K 0)))

/-- **The projection of the total complex onto the row zero is a quasi-isomorphism** as soon as
every coprojection `K^*(⦋0⦌) ⟶ K^*(⦋b⦌)` is one: the form of the hypothesis that
[Stacks, Lemma 60.21.2, Tag 07LD] produces. -/
theorem quasiIso_cosimplicialTotalToRowZero_of_coprojection
    (h : ∀ b : ℕ, QuasiIso (cosimplicialRowCoprojection K b)) :
    QuasiIso (cosimplicialTotalToRowZero K) :=
  quasiIso_cosimplicialTotalToRowZero K fun b =>
    (quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_iff K b).2 (h b)

/-- **The projection of the total complex of the flip onto the row zero is a
quasi-isomorphism** as soon as every codiagonal is one. -/
theorem quasiIso_cosimplicialFlipTotalToRowZero
    (h : ∀ b : ℕ, QuasiIso (cosimplicialRowMap (cosimplicialCodiagonal K) b)) :
    QuasiIso (cosimplicialFlipTotalToRowZero K) := by
  have := quasiIso_cosimplicialTotalToRowZero K h
  have e : cosimplicialFlipTotalToRowZero K =
      ((cosimplicialDoubleComplexFunctor.obj K).totalFlipIso (ComplexShape.up ℤ)).hom ≫
        cosimplicialTotalToRowZero K := by
    rw [cosimplicialTotalToRowZero, Iso.hom_inv_id_assoc]
  rw [e]
  infer_instance

variable {K} in
/-- **The codiagonal is natural**: the row `b` of a morphism `f : K ⟶ K'` followed by the
codiagonal of `K'` is the codiagonal of `K` followed by the row zero of `f`. -/
theorem cosimplicialRowMap_comp_cosimplicialRowMap_cosimplicialCodiagonal
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K') (b : ℕ) :
    cosimplicialRowMap f b ≫ cosimplicialRowMap (cosimplicialCodiagonal K') b =
      cosimplicialRowMap (cosimplicialCodiagonal K) b ≫ cosimplicialRowMap f 0 := by
  ext a : 1
  simp only [HomologicalComplex.comp_f, cosimplicialRowMap_f]
  exact ((f.f a).naturality (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0)).symm

variable {K} in
/-- **The hypothesis on the codiagonals transfers along a morphism which is a quasi-isomorphism on
every row.** -/
theorem quasiIso_cosimplicialRowMap_cosimplicialCodiagonal_of_rows
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K')
    (hf : ∀ b : ℕ, QuasiIso (cosimplicialRowMap f b)) (b : ℕ)
    (h : QuasiIso (cosimplicialRowMap (cosimplicialCodiagonal K) b)) :
    QuasiIso (cosimplicialRowMap (cosimplicialCodiagonal K') b) := by
  have := hf b
  have : QuasiIso (cosimplicialRowMap f b ≫ cosimplicialRowMap (cosimplicialCodiagonal K') b) := by
    rw [cosimplicialRowMap_comp_cosimplicialRowMap_cosimplicialCodiagonal]
    exact quasiIso_comp _ _ (hφ := h) (hφ' := hf 0)
  exact quasiIso_of_comp_left (cosimplicialRowMap f b) _

end Codiagonal

end Crystalline

end
