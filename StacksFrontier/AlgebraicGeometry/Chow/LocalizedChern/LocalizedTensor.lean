module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedComposite
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationTensor

/-!
# Localized classes of a derived tensor product on a modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre
at infinity `W_∞`. For `i = 1, 2` let `Z_i ⊆ X` be closed, let `Q_i ∈ D(𝒪_W)` be perfect with
defined Chern classes and let `T_i ⊆ W_∞` be closed, contain every point of `W_∞` lying over
`X ∖ Z_i`, and be such that `Q_i|_{T_i}` is zero. Then `Q = Q_1 ⊗^L Q_2` satisfies the same
hypotheses for `Z_1 ∩ Z_2` and `T_1 ∪ T_2`, and the second paragraph of the proof of
Stacks 0FBF computes its class `P'_p(Q)` of Stacks 0F9K:

  `P'_p(Q_1 ⊗^L Q_2) = ∑_{p_1 + p_2 = p} C(p, p_1) P'_{p_1}(Q_1) P'_{p_2}(Q_2)`

in `A^p(Z_1 ∩ Z_2 ⟶ X)`, provided `Q_2|_{W ∖ W_2}` is zero for `W_2 = b^{-1}(𝐏¹_{Z_2})` and `Q_2`
satisfies condition (3) of Situation 0GUJ.

The proof is the source's. Each class `P'_p` is the localization `(E ⟶ Z)_* ∘ P'_p(Q|_E) ∘ C` of
the class of Stacks 0F9H on `W_∞`. On `W_∞` the class `P'_p(Q|_{E_1 ∩ E_2})` expands as the sum
of the products `P'_{p_1}(Q_1|_{E_1}) P'_{p_2}(Q_2|_{E_2})` (Stacks 0FE5), and the localization
of a product is the product of the localizations (Stacks 0FE7).

## Main definitions

* `Stacks.Chow.modificationLocalizationAddHom` — the localization `a ↦ (E ⟶ Y)_* ∘ a ∘ C` as an
  additive map.

## Main results

* `Stacks.Chow.modificationInfinityPowerSum_derivedTensor` — the expansion on `W_∞` of
  `P'_p((Q_1 ⊗^L Q_2)|_{E_1 ∩ E_2})` (Stacks 0FE5).
* `Stacks.Chow.modificationPowerSum_derivedTensor` — the formula for `P'_p(Q_1 ⊗^L Q_2)`.

## Implementation notes

`Z_1 ∩ Z_2` is the fibre product `Z_1 ×_X Z_2`, mapping to `X` through `Z_1`, the presentation
of `Stacks.Chow.supportedIntersectionMul_modificationLocalization`; `E_1 ∩ E_2` is
`W_∞ ×_X (Z_1 ×_X Z_2)`, presented as the fibre product of `E_1 = W_∞ ×_X Z_1` and
`E_2 = W_∞ ×_X Z_2` over `W_∞` by the square of `Stacks.Chow.modificationInfinityMul`.
`T_1 ∪ T_2` is the reduced closed subscheme on the union (`Stacks.Chow.reducedUnionIdeal`).

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Linearity of the localization -/

section Linearity

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (y : Y ⟶ X) [IsClosedImmersion y]

/-- **The localization `a ↦ (E ⟶ Y)_* ∘ a ∘ C` is additive**, for `E = W_∞ ×_X Y`: on every test
scheme it caps through the cap operation of `a`. -/
def modificationLocalizationAddHom (m : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C)
        (pullback.fst (modificationProjectionAtInfinity f b) y ≫
          modificationProjectionAtInfinity f b ≫ f)
        (modificationProjectionAtInfinity f b ≫ f)
        (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m →+
      BivariantClass C (gysinSystemOfInvertible C) (y ≫ f) f y rfl m :=
  AddMonoidHom.mk' (modificationLocalization C f b hA y) fun a a' ↦ by
    refine BivariantClass.ext _ _ _ _ _ _ _ fun g _ k α ↦ ?_
    rw [BivariantClass.add_cap, modificationLocalization_cap, modificationLocalization_cap,
      modificationLocalization_cap, BivariantClass.add_cap, map_add, map_add]

/-- The additive map `modificationLocalizationAddHom` sends `a` to
`modificationLocalization C f b hA y a`. -/
theorem modificationLocalizationAddHom_apply {m : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) :
    modificationLocalizationAddHom C f b hA y m a = modificationLocalization C f b hA y a :=
  rfl

/-- The localization commutes with transport along an equality of degrees. -/
theorem modificationLocalization_bivariantClassDegreeCongr {m m' : ℤ} (h : m = m')
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) y ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) y) rfl m) :
    modificationLocalization C f b hA y (bivariantClassDegreeCongr C _ _ _ _ rfl h a) =
      bivariantClassDegreeCongr C _ _ _ _ rfl h (modificationLocalization C f b hA y a) := by
  subst h
  rfl

end Linearity

/-! ### The classes of Stacks 0F9K of `Q₁ ⊗^L Q₂` -/

section Support

variable {X S W Z₁ Z₂ T₁ T₂ : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)
  (z₁ : Z₁ ⟶ X) (z₂ : Z₂ ⟶ X) (t₁ : T₁ ⟶ modificationFibreAtInfinity f b)
  (t₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₁] [IsClosedImmersion t₂]

/-- `T₁ ∪ T₂` contains the points of `W_∞` over `X ∖ (Z₁ ∩ Z₂)`, for `Z₁ ∩ Z₂ = Z₁ ×_X Z₂` mapping
to `X` through `Z₁`. -/
theorem mem_range_reducedUnion_of_notMem_range_pullbackFst
    (hT₁ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₁ → w ∈ Set.range t₁)
    (hT₂ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₂ → w ∈ Set.range t₂) :
    ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range (pullback.fst z₁ z₂ ≫ z₁) →
      w ∈ Set.range (reducedUnionIdeal t₁ t₂).subschemeι := by
  rw [pullback.condition]
  exact mem_range_reducedUnion_of_notMem_range_inter f b z₁ z₂ t₁ t₂ hT₁ hT₂

end Support

section Tensor

variable (C : ChowSituation.{u}) {X W Z₁ Z₂ T₁ T₂ : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (z₁ : Z₁ ⟶ X) [IsClosedImmersion z₁] (z₂ : Z₂ ⟶ X) [IsClosedImmersion z₂]
  (t₁ : T₁ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₁]
  (t₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₂]
  {Q₁ Q₂ : DerivedCategory W.Modules}
  (hQp₁ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₁)
  (hQp₂ : Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) Q₂)
  (hQ₁ : HasDefinedChernClasses Q₁) (hQ₂ : HasDefinedChernClasses Q₂)
  (hT₁ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₁ → w ∈ Set.range t₁)
  (hT₂ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₂ → w ∈ Set.range t₂)
  (hzero₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t₁ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₁))
  (hzero₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t₂ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₂))

/-- **Stacks 0FE5 on `W_∞` for `P'_p(Q|_{E₁ ∩ E₂})`.** On the fibre at infinity, along the closed
cover `W_∞ = (T₁ ∪ T₂) ∪ (E₁ ∩ E₂)`, the class `P'_p((Q₁ ⊗^L Q₂)|_{E₁ ∩ E₂})` of Stacks 0F9H is
`∑_{p₁ + p₂ = p} C(p, p₁) P'_{p₁}(Q₁|_{E₁}) P'_{p₂}(Q₂|_{E₂})`, where `E_i = W_∞ ×_X Z_i` and
`E₁ ∩ E₂ = W_∞ ×_X (Z₁ ×_X Z₂)`. -/
theorem modificationInfinityPowerSum_derivedTensor (p : ℕ) :
    modificationInfinityPowerSum C f b (pullback.fst z₁ z₂ ≫ z₁)
        (reducedUnionIdeal t₁ t₂).subschemeι
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) p
        (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂) =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (modificationInfinityMul C f b z₁ z₂
            (modificationInfinityPowerSum C f b z₁ t₁ hT₁ hQ₁ q.1.1 hzero₁)
            (modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ q.1.2 hzero₂)) := by
  set π := modificationProjectionAtInfinity f b
  set ι := modificationInclusionAtInfinity f b
  set iW := pullback.fst π (pullback.fst z₁ z₂ ≫ z₁)
  have hQ := hasDefinedChernClasses_derivedTensor hQ₁ hQ₂
  have hsι : ι ≫ (modificationProjection f b ≫ f) = π ≫ f := (Category.assoc _ _ _).symm
  have hD : perfectPowerSumComponent C (iW ≫ π ≫ f) ((hQ.derivedPullback ι).derivedPullback iW) p =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ (𝟙 _) (Category.id_comp _)
          (by have := mem_antidiagonal.1 q.2; omega)
          ((TotalChowClass.res iW rfl (perfectPowerSum C (π ≫ f) (hQ₁.derivedPullback ι) q.1.1)
              q.1.1).mulId C (iW ≫ π ≫ f)
            (TotalChowClass.res iW rfl (perfectPowerSum C (π ≫ f) (hQ₂.derivedPullback ι) q.1.2)
              q.1.2)) := by
    change perfectPowerSum C (iW ≫ π ≫ f) ((hQ.derivedPullback ι).derivedPullback iW) p p = _
    rw [← res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ.derivedPullback ι) iW rfl,
      ← res_perfectPowerSum_derivedPullback C (modificationProjection f b ≫ f) hQ ι hsι,
      perfectPowerSum_derivedTensor C _ hQ₁ hQ₂ hQ p, map_sum, map_sum, TotalChowClass.sum_apply,
      ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_zsmul, map_zsmul, TotalChowClass.zsmul_apply, map_mul,
      res_perfectPowerSum_derivedPullback C _ hQ₁ ι hsι (hQ₁.derivedPullback ι),
      res_perfectPowerSum_derivedPullback C _ hQ₂ ι hsι (hQ₂.derivedPullback ι), map_mul,
      ((isHomogeneous_perfectPowerSum C (π ≫ f) (hQ₁.derivedPullback ι) q.1.1).res iW
        rfl).mul_apply _ (mem_antidiagonal.1 q.2)]
  refine IsClosedCoverExtension.eq (range_union_range_pullbackFst_eq_univ _ _
      (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂))
    (isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) _ iW _ rfl _ _ _ _) ?_
  rw [hD]
  refine IsClosedCoverExtension.sum C (π ≫ f) _ iW _ fun q _ ↦ ?_
  refine IsClosedCoverExtension.zsmul C (π ≫ f) _ iW ?_ _
  refine IsClosedCoverExtension.bivariantClassDegreeCongr C (π ≫ f) _ iW _ ?_
  have hd := fun {Z : Scheme.{u}} (z : Z ⟶ X) [IsClosedImmersion z] {Q : DerivedCategory W.Modules}
      (hQ' : HasDefinedChernClasses Q) (k : ℕ) (w : _ ⟶ pullback π z)
      [LocallyOfFiniteType w] (hw : w ≫ pullback.fst π z = iW) ↦
    res_perfectPowerSum_derivedPullback C (π ≫ f) (hQ'.derivedPullback ι) (pullback.fst π z) rfl
      ((hQ'.derivedPullback ι).derivedPullback _) k ▸
    TotalChowClass.isRestriction_res_res (perfectPowerSum C (π ≫ f) (hQ'.derivedPullback ι) k)
      (pullback.fst π z) _ iW hw k
  exact IsClosedCoverExtension.supportedIntersectionMul _
    (isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₁ (pullback.fst π z₁) _ rfl _ _
      (range_union_range_pullbackFst_eq_univ z₁ t₁ hT₁) _)
    (isClosedCoverExtension_closedCoverPowerSum C (π ≫ f) t₂ (pullback.fst π z₂) _ rfl _ _
      (range_union_range_pullbackFst_eq_univ z₂ t₂ hT₂) _)
    (hd z₁ hQ₁ q.1.1 _ ((Category.assoc _ _ _).trans (pullbackFstTestIso_inv_fst_fst π z₁ z₂)))
    (hd z₂ hQ₂ q.1.2 _ (pullbackFstTestIso_inv_snd_fst π z₂ z₁))
    (range_subschemeι_reducedUnionIdeal t₁ t₂).subset

variable (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The class `P'_p(Q)` of Stacks 0F9K is the localization of the class `P'_p(Q|_E)` of
Stacks 0F9H. -/
theorem modificationPowerSum_eq_modificationLocalization {Z T : Scheme.{u}} (z : Z ⟶ X)
    [IsClosedImmersion z] (t : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t]
    {Q : DerivedCategory W.Modules} (hQ : HasDefinedChernClasses Q) (p : ℕ)
    (hT : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z → w ∈ Set.range t)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q)) :
    modificationPowerSum C f b hA z t hQ p hT hzero =
      modificationLocalization C f b hA z (modificationInfinityPowerSum C f b z t hT hQ p hzero) :=
  (localizedModificationClass_eq_modificationLocalization C f b hA z t hT _).trans
    (by rw [modificationExtension_perfectPowerSumClass])

/-- **The class `P'_p(Q₁ ⊗^L Q₂)` of Stacks 0F9K** (the second paragraph of the proof of
Stacks 0FBF). Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and for `i = 1, 2` let
`Z_i ⊆ X` and `T_i ⊆ W_∞` be closed and `Q_i ∈ D(𝒪_W)` perfect with defined Chern classes, such
that `T_i` contains every point of `W_∞` over `X ∖ Z_i` and `Q_i|_{T_i}` is zero. Assume that
`Q₂|_{W ∖ W_2}` is zero for `W_2 = W ×_X Z₂` and that `Q₂` satisfies condition (3) of
Situation 0GUJ. Then for the data `Z₁ ∩ Z₂`, `Q₁ ⊗^L Q₂` and `T₁ ∪ T₂`

  `P'_p(Q₁ ⊗^L Q₂) = ∑_{p₁ + p₂ = p} C(p, p₁) P'_{p₁}(Q₁) P'_{p₂}(Q₂)`

in `A^p(Z₁ ∩ Z₂ ⟶ X)`, the products being those of Stacks 0FE5
(`Stacks.Chow.supportedIntersectionMul`). -/
theorem modificationPowerSum_derivedTensor
    (hres₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (W.toRingedSpace.ofRestrict (modificationComplementOpens b z₂).isOpenEmbedding)).obj Q₂))
    (hfin₂ : LocalizedChernFiniteness C (modificationProjection f b ≫ f) Q₂) (p : ℕ) :
    modificationPowerSum C f b hA (pullback.fst z₁ z₂ ≫ z₁) (reducedUnionIdeal t₁ t₂).subschemeι
        (hasDefinedChernClasses_derivedTensor hQ₁ hQ₂) p
        (mem_range_reducedUnion_of_notMem_range_pullbackFst f b z₁ z₂ t₁ t₂ hT₁ hT₂)
        (isZero_derivedPullback_reducedUnion_derivedTensor f b t₁ t₂ hQp₁ hQp₂ hzero₁ hzero₂) =
      ∑ q ∈ (antidiagonal p).attach, (p.choose q.1.1 : ℤ) •
        bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
          (supportedIntersectionMul C f z₁ z₂ (IsPullback.of_hasPullback z₁ z₂)
            (pullback.fst z₁ z₂ ≫ z₁) pullback.condition.symm
            (modificationPowerSum C f b hA z₁ t₁ hQ₁ q.1.1 hT₁ hzero₁)
            (modificationPowerSum C f b hA z₂ t₂ hQ₂ q.1.2 hT₂ hzero₂)) := by
  refine (modificationPowerSum_eq_modificationLocalization C f b hA _ _ _ p _ _).trans ?_
  refine (congrArg (modificationLocalization C f b hA (pullback.fst z₁ z₂ ≫ z₁))
    (modificationInfinityPowerSum_derivedTensor C f b z₁ z₂ t₁ t₂ hQp₁ hQp₂ hQ₁ hQ₂ hT₁ hT₂ hzero₁
      hzero₂ p)).trans ?_
  rw [← modificationLocalizationAddHom_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, modificationLocalizationAddHom_apply,
    modificationLocalization_bivariantClassDegreeCongr,
    modificationPowerSum_eq_modificationLocalization C f b hA z₁,
    modificationPowerSum_eq_modificationLocalization C f b hA z₂,
    supportedIntersectionMul_modificationLocalization C f b hA z₁ z₂ _ _
      (preservesInfinityGysinImage_modificationInfinityPowerSum C f b z₂ t₂ hT₂ hQ₂ q.1.2 hzero₂
        hQp₂ hres₂ hfin₂)]

end Tensor

end Stacks.Chow

end
