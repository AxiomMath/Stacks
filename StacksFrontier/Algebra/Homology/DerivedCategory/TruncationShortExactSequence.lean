module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical truncation triangle comes from a short exact sequence of complexes

Let `K` be a cochain complex in an abelian category with a derived category. Truncating `K` above
degree `k` and then above degree `k - 1` gives the short exact sequence of complexes
`0 ⟶ τ_{≤k-1}K ⟶ τ_{≤k}K ⟶ Q ⟶ 0`, and this file identifies its image in the derived category
with the canonical truncation triangle `τ_{≤k-1}K ⟶ τ_{≤k}K ⟶ H^k(K)[-k] ⟶ (τ_{≤k-1}K)[1]`.

## Main results

* `CochainComplex.nonempty_truncLE_truncLE_iso`: iterated truncation from above is truncation at
  the smaller degree.
* `CochainComplex.nonempty_Q_shortComplexTruncLE_X₃_iso`: the quotient of two successive
  truncations is `H^k(K)` placed in degree `k`.
* `CochainComplex.nonempty_triangleOfSES_truncLE_iso`: the triangle of the short exact sequence
  of successive truncations is the canonical truncation triangle, morphisms included.

## References

* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The first row of the display of Stacks 0F8J.** Truncating `K` above degree `n` and then
above a degree `m ≤ n` returns the truncation of `K` above degree `m`. -/
@[stacks 0F8J "the left-hand row of the display is the preceding truncation"]
public theorem nonempty_truncLE_truncLE_iso (K : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    Nonempty ((K.truncLE n).truncLE m ≅ K.truncLE m) :=
  ⟨(truncLETruncLEIso K h).symm⟩

section Derived

variable [HasDerivedCategory.{w} C]

/-- The quotient of `τ_{≤k-1}T` inside `T` is concentrated in degrees `≥ k` in the derived
category. -/
private theorem isGE_Q_obj_shortComplexTruncLE_X₃ (T : CochainComplex C ℤ) (k : ℤ) :
    (DerivedCategory.Q.obj (T.shortComplexTruncLE (k - 1)).X₃).IsGE k := by
  let cmp := T.shortComplexTruncLEX₃ToTruncGE (k - 1) k (by omega)
  have : IsIso (DerivedCategory.Q.map cmp) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ cmp).2 inferInstance
  have : (DerivedCategory.Q.obj (T.truncGE k)).IsGE k := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map cmp)).symm k

/-- **The right-hand row of the display of Stacks 0F8J.** The quotient of the truncation of `K`
above degree `k - 1` inside the truncation of `K` above degree `k` is the cohomology object
`H^k(K)` placed in degree `k`. -/
@[stacks 0F8J "the right-hand row of the display is the shifted cohomology object"]
public theorem nonempty_Q_shortComplexTruncLE_X₃_iso (K : CochainComplex C ℤ) (k : ℤ) :
    Nonempty (DerivedCategory.Q.obj ((K.truncLE k).shortComplexTruncLE (k - 1)).X₃ ≅
      (DerivedCategory.singleFunctor C k).obj (K.homology k)) := by
  let T := K.truncLE k
  let S := T.shortComplexTruncLE (k - 1)
  have hS : S.ShortExact := T.shortComplexTruncLE_shortExact (k - 1)
  have : (DerivedCategory.Q.obj S.X₃).IsGE k := isGE_Q_obj_shortComplexTruncLE_X₃ T k
  have : (DerivedCategory.Q.obj S.X₃).IsLE k :=
    (DerivedCategory.isLE_iff (DerivedCategory.Q.obj S.X₃) k).2 fun i hik => by
      have hz₂ : IsZero (S.X₂.homology i) := T.isZero_of_isLE k i hik
      exact IsZero.of_iso (IsZero.of_epi (HomologicalComplex.homologyMap S.g i) hz₂)
        ((DerivedCategory.homologyFunctorFactors C i).app S.X₃)
  have hzero : IsZero (S.X₁.homology k) :=
    (T.truncLE (k - 1)).isZero_of_isLE (k - 1) k (by omega)
  have : Mono (HomologicalComplex.homologyMap S.g k) :=
    (hS.homology_exact₂ k).mono_g (hzero.eq_of_src _ _)
  have : IsIso (HomologicalComplex.homologyMap S.g k) := isIso_of_mono_of_epi _
  have hι : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE k) k) :=
    (quasiIsoAt_iff_isIso_homologyMap (K.ιTruncLE k) k).mp (K.quasiIsoAt_ιTruncLE k k le_rfl)
  let hK : (DerivedCategory.homologyFunctor C k).obj (DerivedCategory.Q.obj S.X₃) ≅
      K.homology k :=
    (DerivedCategory.homologyFunctorFactors C k).app S.X₃ ≪≫
      (asIso (HomologicalComplex.homologyMap S.g k)).symm ≪≫
        @asIso _ _ _ _ (HomologicalComplex.homologyMap (K.ιTruncLE k) k) hι
  obtain ⟨Y, ⟨eY⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      (DerivedCategory.Q.obj S.X₃) k
  let eYH : Y ≅ (DerivedCategory.homologyFunctor C k).obj (DerivedCategory.Q.obj S.X₃) :=
    ((DerivedCategory.homologyFunctor C k).mapIso eY ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C k).app Y).symm
  exact ⟨eY ≪≫ (DerivedCategory.singleFunctor C k).mapIso (eYH ≪≫ hK)⟩

/-- **Stacks 0F8J.** The canonical truncation triangle
`τ_{≤k-1}K ⟶ τ_{≤k}K ⟶ H^k(K)[-k] ⟶ (τ_{≤k-1}K)[1]` is the triangle of the short exact sequence
of complexes `0 ⟶ τ_{≤k-1}(τ_{≤k}K) ⟶ τ_{≤k}K ⟶ Q ⟶ 0`, morphisms included. -/
@[stacks 0F8J "the truncation triangle is the triangle of the displayed short exact sequence"]
public theorem nonempty_triangleOfSES_truncLE_iso (K : CochainComplex C ℤ) (k : ℤ) :
    Nonempty (DerivedCategory.triangleOfSES
      ((K.truncLE k).shortComplexTruncLE_shortExact (k - 1)) ≅
      (DerivedCategory.TStructure.t.triangleLEGT (k - 1)).obj
        (DerivedCategory.Q.obj (K.truncLE k))) := by
  let T := K.truncLE k
  let S := T.shortComplexTruncLE (k - 1)
  let hS := T.shortComplexTruncLE_shortExact (k - 1)
  let A := DerivedCategory.triangleOfSES hS
  let B := (DerivedCategory.TStructure.t.triangleLEGT (k - 1)).obj (DerivedCategory.Q.obj T)
  have hA : A ∈ distTriang (DerivedCategory C) := DerivedCategory.triangleOfSES_distinguished hS
  have hB : B ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.TStructure.t.triangleLEGT_distinguished (k - 1) (DerivedCategory.Q.obj T)
  have hLEA : DerivedCategory.TStructure.t.IsLE A.obj₁ (k - 1) := by
    change (DerivedCategory.Q.obj (T.truncLE (k - 1))).IsLE (k - 1)
    rw [DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  have hGEA : DerivedCategory.TStructure.t.IsGE A.obj₃ k := by
    exact isGE_Q_obj_shortComplexTruncLE_X₃ T k
  have hLEB : DerivedCategory.TStructure.t.IsLE B.obj₁ (k - 1) := by
    change DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLE (k - 1)).obj (DerivedCategory.Q.obj T)) (k - 1)
    infer_instance
  have hGEB : DerivedCategory.TStructure.t.IsGE B.obj₃ k := by
    change DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGT (k - 1)).obj (DerivedCategory.Q.obj T)) k
    infer_instance
  obtain ⟨e, -⟩ := DerivedCategory.TStructure.t.triangle_iso_exists
    hA hB (Iso.refl (DerivedCategory.Q.obj T)) (k - 1) k hLEA hGEA hLEB hGEB (by omega)
  exact ⟨e⟩

end Derived

end CochainComplex

end
