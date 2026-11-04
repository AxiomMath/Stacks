module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxSectionsGlobalInjective
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.KernelPresentation
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact
public import StacksFrontier.LinearAlgebra.TensorProduct.FiniteGridPi

/-!
# The global box-section comparison is bijective

Let `k` be a field, let `a : X ⟶ Spec k` and `b : Y ⟶ Spec k` be **proper**, and let `P` and `Q`
be quasi-coherent. Then

`Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`,  `s ⊗ t ↦ s ⊠ t`,

is **bijective**. Injectivity is
`AlgebraicGeometry.injective_globalBoxSectionMap_of_affineCovers`; this file proves surjectivity
and assembles the two.

## Where the two hypotheses on `X` and `Y` are spent

**Quasi-compactness** makes the two affine coverings *finite*. It enters twice: once so that the
restrictions to a grid of pairs detect an element of a tensor product
(`TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective`, inside injectivity), and once so
that a family of local box sections assembles into one element of
`(∏ᵢ Γ(P, U i)) ⊗_k (∏ⱼ Γ(Q, V j))` (`TensorProduct.exists_map_proj_eq`). Without it the
statement is **false**: for `X = Y = ∐_{n : ℕ} Spec k` and `P = Q = 𝒪` the comparison is the
inclusion of `(∏_ℕ k) ⊗_k (∏_ℕ k)` into `∏_{ℕ × ℕ} k`, whose image is the finite-rank matrices.

**Separatedness** makes the pairwise intersections `U i ⊓ U i'` affine, which is what lets the
*overlap* of two charts be described by a tensor product too — and that description is the whole
content of the cocycle condition: without it nothing identifies the two local preimages of a
global box section on an overlap. It is used nowhere else, and it is used only in surjectivity.

## The argument

Over each `U i ⊓ U i'` and each `V j` the comparison is bijective, so a global box section `w`
has a unique local preimage `z i j` over each pair, and the `z i j` agree on the overlaps. The
grid `(z i j)` assembles into `ζ` in `(∏ᵢ Γ(P, U i)) ⊗_k (∏ⱼ Γ(Q, V j))`, and the agreement says
exactly that `ζ` is killed by the two overlap differences tensored with the identity. Over a
field every module is flat, so
`ProjectiveDeterminant.range_mapIncl_ker_eq_ker_rTensor_inf_ker_lTensor` identifies the
intersection of those two kernels with the image of `ker d_X ⊗_k ker d_Y`; and
`AlgebraicGeometry.sectionsKerEquiv` identifies those two kernels with `Γ(X, P)` and `Γ(Y, Q)`.
The resulting element of `Γ(X, P) ⊗_k Γ(Y, Q)` restricts to `z i j` over every pair, hence has the
same restrictions as `w` to a covering of `X ×_k Y`, hence equals `w`.

## Main results

* `AlgebraicGeometry.map_restrict_eq_of_boxSectionMapInf_left` and `..._right`: **the two local
  preimages of a global box section agree on an overlap**, as soon as the overlap is affine.
* `AlgebraicGeometry.surjective_globalBoxSectionMap_of_affineCovers`: **the comparison is
  surjective.**
* `AlgebraicGeometry.bijective_globalBoxSectionMap_of_affineCovers`: **the comparison is
  bijective**, for two finite affine coverings with affine pairwise intersections.
* `AlgebraicGeometry.bijective_globalBoxSectionMap_of_isProper`: **the comparison is bijective for
  `X` and `Y` proper over `k`** — the statement of the degree-zero Künneth comparison.

## Implementation notes

`AlgebraicGeometry.boxSectionMapInf` names the comparison read over `pr₁⁻¹U ⊓ pr₂⁻¹V`, which is
the open the affine case is about; the general `AlgebraicGeometry.boxSectionMapOpens` keeps its
open as a parameter because the global statement needs it at `⊤`.

The restriction `AlgebraicGeometry.sectionsOverFieldRestrict` along `le_rfl` is the identity but
not definitionally so, and the naturality of the comparison restricts *both* factors at once; the
fixed factor is therefore restricted along `le_rfl` and
`AlgebraicGeometry.sectionsOverFieldRestrict_rfl` turns that into `LinearMap.id`, which is what
`TensorProduct.map_comp_apply` needs.

## References

* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open AlgebraicGeometry CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
  (b : Y ⟶ Spec (.of k)) (P : X.Modules) (Q : Y.Modules)

/-- Restriction along `le_rfl` is the identity. -/
theorem sectionsOverFieldRestrict_rfl {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (F : Z.Modules)
    (U : Z.Opens) : sectionsOverFieldRestrict k f F (le_refl U) = LinearMap.id :=
  LinearMap.ext fun s => Stacks.Tag01VSPullbackTensor.presheaf_map_self F _ s

/-- Two successive restrictions are one. -/
theorem sectionsOverFieldRestrict_trans {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (F : Z.Modules)
    {U V W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : ↑(sectionsOverField k f F U)) :
    sectionsOverFieldRestrict k f F h₂ (sectionsOverFieldRestrict k f F h₁ s)
      = sectionsOverFieldRestrict k f F (h₂.trans h₁) s :=
  presheaf_map_map F (homOfLE h₁) (homOfLE h₂) (homOfLE (h₂.trans h₁)) s

/-- Two sections with the same restrictions to the members of a covering are equal. -/
theorem eq_of_sectionsOverFieldRestrict_eq {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k))
    (F : Z.Modules) {ι : Type*} {W : ι → Z.Opens} (hW : ⨆ i, W i = ⊤)
    (s t : ↑(sectionsOverField k f F ⊤))
    (h : ∀ i, sectionsOverFieldRestrict k f F (le_top (a := W i)) s
      = sectionsOverFieldRestrict k f F (le_top (a := W i)) t) : s = t :=
  sub_eq_zero.mp (eq_zero_of_sectionsOverFieldRestrict_eq_zero k f F hW (s - t)
    fun i => (map_sub (sectionsOverFieldRestrict k f F (le_top (a := W i))) s t).trans
      (sub_eq_zero.mpr (h i)))

/-- **The opens `pr₁⁻¹(U i) ⊓ pr₂⁻¹(V j)` of a pair of coverings cover the fibre product.** -/
theorem iSup_preimage_inf_preimage_eq_top {I J : Type*} {U : I → X.Opens}
    (hUcov : ⨆ i, U i = ⊤) {V : J → Y.Opens} (hVcov : ⨆ j, V j = ⊤) :
    ⨆ p : I × J, (pullback.fst a b ⁻¹ᵁ U p.1 ⊓ pullback.snd a b ⁻¹ᵁ V p.2) = ⊤ := by
  refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ?_
  have h₁ : (pullback.fst a b).base z ∈ (⨆ i, U i : X.Opens) := hUcov ▸ trivial
  have h₂ : (pullback.snd a b).base z ∈ (⨆ j, V j : Y.Opens) := hVcov ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h₁
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp h₂
  exact ⟨(i, j), ⟨hi, hj⟩⟩

/-- The box-section comparison over a pair of opens, read over `pr₁⁻¹U ⊓ pr₂⁻¹V`. -/
abbrev boxSectionMapInf (U : X.Opens) (V : Y.Opens) :
    TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V) →ₗ[k]
      ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q)
        (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)) :=
  boxSectionMapOpens k a b P Q U V (pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
    inf_le_left inf_le_right

/-- Restricting the tensor of the global sections read off a pair of kernels to a pair of members
of the coverings gives the corresponding component of the tensor of the two kernels. -/
theorem map_restrict_map_sectionsKerEquiv_symm {I J : Type*} {U : I → X.Opens}
    (hUcov : ⨆ i, U i = ⊤) {V : J → Y.Opens} (hVcov : ⨆ j, V j = ⊤)
    (u : TensorProduct k (LinearMap.ker (sectionsOverlapDiff k a P U))
      (LinearMap.ker (sectionsOverlapDiff k b Q V))) (i : I) (j : J) :
    TensorProduct.map (sectionsOverFieldRestrict k a P (le_top (a := U i)))
        (sectionsOverFieldRestrict k b Q (le_top (a := V j)))
        (TensorProduct.map (sectionsKerEquiv k a P U hUcov).symm.toLinearMap
          (sectionsKerEquiv k b Q V hVcov).symm.toLinearMap u)
      = TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)
        (TensorProduct.mapIncl _ _ u) := by
  rw [TensorProduct.map_comp_apply,
    show (sectionsOverFieldRestrict k a P (le_top (a := U i))) ∘ₗ
          (sectionsKerEquiv k a P U hUcov).symm.toLinearMap
        = (LinearMap.proj i) ∘ₗ
          (LinearMap.ker (sectionsOverlapDiff k a P U)).subtype from
      LinearMap.ext fun v => sectionsKerEquiv_symm_apply_coe k a P U hUcov v i,
    show (sectionsOverFieldRestrict k b Q (le_top (a := V j))) ∘ₗ
          (sectionsKerEquiv k b Q V hVcov).symm.toLinearMap
        = (LinearMap.proj j) ∘ₗ
          (LinearMap.ker (sectionsOverlapDiff k b Q V)).subtype from
      LinearMap.ext fun v => sectionsKerEquiv_symm_apply_coe k b Q V hVcov v j,
    ← TensorProduct.map_comp_apply]

variable [P.IsQuasicoherent] [Q.IsQuasicoherent]

/-- Over a pair of affine opens the comparison read over `pr₁⁻¹U ⊓ pr₂⁻¹V` is bijective. -/
theorem bijective_boxSectionMapInf {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) : Function.Bijective (boxSectionMapInf k a b P Q U V) :=
  bijective_boxSectionMapOpens_of_isAffineOpen k a b P Q hU hV rfl inf_le_left inf_le_right

/-- Two local preimages of a global box section, over members `U₁ × V₁` and `U₂ × V₂` of coverings,
agree after restriction to a common affine pair `U₀ × V₀` below both. -/
private theorem map_restrict_eq_of_boxSectionMapInf {U₁ U₂ U₀ : X.Opens} (h₁ : U₀ ≤ U₁)
    (h₂ : U₀ ≤ U₂) (hU₀ : IsAffineOpen U₀) {V₁ V₂ V₀ : Y.Opens} (g₁ : V₀ ≤ V₁) (g₂ : V₀ ≤ V₂)
    (hV₀ : IsAffineOpen V₀)
    (w : ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) ⊤))
    (z₁ : TensorProduct k ↑(sectionsOverField k a P U₁) ↑(sectionsOverField k b Q V₁))
    (z₂ : TensorProduct k ↑(sectionsOverField k a P U₂) ↑(sectionsOverField k b Q V₂))
    (hz₁ : boxSectionMapInf k a b P Q U₁ V₁ z₁
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
    (hz₂ : boxSectionMapInf k a b P Q U₂ V₂ z₂
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w) :
    TensorProduct.map (sectionsOverFieldRestrict k a P h₁) (sectionsOverFieldRestrict k b Q g₁) z₁
      = TensorProduct.map (sectionsOverFieldRestrict k a P h₂)
        (sectionsOverFieldRestrict k b Q g₂) z₂ := by
  refine (bijective_boxSectionMapInf k a b P Q hU₀ hV₀).1 ?_
  rw [← sectionsOverFieldRestrict_boxSectionMapOpens k a b P Q h₁ g₁
      (inf_le_inf (Scheme.Hom.preimage_mono _ h₁)
        (Scheme.Hom.preimage_mono _ g₁)) inf_le_left inf_le_right inf_le_left inf_le_right z₁,
    ← sectionsOverFieldRestrict_boxSectionMapOpens k a b P Q h₂ g₂
      (inf_le_inf (Scheme.Hom.preimage_mono _ h₂)
        (Scheme.Hom.preimage_mono _ g₂)) inf_le_left inf_le_right inf_le_left inf_le_right z₂,
    hz₁, hz₂, sectionsOverFieldRestrict_trans, sectionsOverFieldRestrict_trans]

/-- **The two local preimages of a global box section agree on an overlap of the first factor**,
as soon as that overlap is affine. -/
theorem map_restrict_eq_of_boxSectionMapInf_left {U U' : X.Opens}
    (hUU' : IsAffineOpen (U ⊓ U')) {V : Y.Opens} (hV : IsAffineOpen V)
    (w : ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) ⊤))
    (z : TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V))
    (z' : TensorProduct k ↑(sectionsOverField k a P U') ↑(sectionsOverField k b Q V))
    (hz : boxSectionMapInf k a b P Q U V z
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
    (hz' : boxSectionMapInf k a b P Q U' V z'
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w) :
    TensorProduct.map (sectionsOverFieldRestrict k a P (inf_le_left : U ⊓ U' ≤ U))
        LinearMap.id z
      = TensorProduct.map (sectionsOverFieldRestrict k a P (inf_le_right : U ⊓ U' ≤ U'))
        LinearMap.id z' := by
  have h := map_restrict_eq_of_boxSectionMapInf k a b P Q inf_le_left inf_le_right hUU'
    (le_refl V) (le_refl V) hV w z z' hz hz'
  rwa [sectionsOverFieldRestrict_rfl] at h

/-- **The two local preimages of a global box section agree on an overlap of the second factor**,
as soon as that overlap is affine. -/
theorem map_restrict_eq_of_boxSectionMapInf_right {U : X.Opens} (hU : IsAffineOpen U)
    {V V' : Y.Opens} (hVV' : IsAffineOpen (V ⊓ V'))
    (w : ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) ⊤))
    (z : TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V))
    (z' : TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V'))
    (hz : boxSectionMapInf k a b P Q U V z
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
    (hz' : boxSectionMapInf k a b P Q U V' z'
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w) :
    TensorProduct.map LinearMap.id
        (sectionsOverFieldRestrict k b Q (inf_le_left : V ⊓ V' ≤ V)) z
      = TensorProduct.map LinearMap.id
        (sectionsOverFieldRestrict k b Q (inf_le_right : V ⊓ V' ≤ V')) z' := by
  have h := map_restrict_eq_of_boxSectionMapInf k a b P Q (le_refl U) (le_refl U) hU
    inf_le_left inf_le_right hVV' w z z' hz hz'
  rwa [sectionsOverFieldRestrict_rfl] at h

/-- **A grid of local preimages of a global box section is killed by the overlap difference of
the first covering**, as soon as its pairwise intersections are affine. -/
theorem rTensor_sectionsOverlapDiff_eq_zero {I J : Type*} [Finite I] [Finite J]
    {U : I → X.Opens} (hUinf : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    {V : J → Y.Opens} (hV : ∀ j, IsAffineOpen (V j))
    (w : ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) ⊤))
    (z : ∀ i j, TensorProduct k ↑(sectionsOverField k a P (U i)) ↑(sectionsOverField k b Q (V j)))
    (hz : ∀ i j, boxSectionMapInf k a b P Q (U i) (V j) (z i j)
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
    (ζ : TensorProduct k (∀ i, ↑(sectionsOverField k a P (U i)))
      (∀ j, ↑(sectionsOverField k b Q (V j))))
    (hζ : ∀ i j, TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) ζ = z i j) :
    LinearMap.rTensor (∀ j, ↑(sectionsOverField k b Q (V j)))
      (sectionsOverlapDiff k a P U) ζ = 0 := by
  refine TensorProduct.eq_zero_of_map_proj _ fun p j => ?_
  have h : ∀ (m : I) (W : X.Opens) (hW : W ≤ U m),
      TensorProduct.map ((sectionsOverFieldRestrict k a P hW).comp (LinearMap.proj m))
          (LinearMap.proj j) ζ
        = TensorProduct.map (sectionsOverFieldRestrict k a P hW) LinearMap.id (z m j) := by
    intro m W hW
    rw [← hζ m j, TensorProduct.map_comp_apply, LinearMap.id_comp]
  rw [TensorProduct.map_proj_rTensor_apply,
    show (LinearMap.proj p ∘ₗ sectionsOverlapDiff k a P U)
        = (sectionsOverFieldRestrict k a P (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).comp
            (LinearMap.proj p.1) -
          (sectionsOverFieldRestrict k a P (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)).comp
            (LinearMap.proj p.2) from LinearMap.proj_pi _ _,
    TensorProduct.map_sub_left, sub_eq_zero, h, h]
  exact map_restrict_eq_of_boxSectionMapInf_left k a b P Q (hUinf p.1 p.2) (hV j) w
    (z p.1 j) (z p.2 j) (hz p.1 j) (hz p.2 j)

/-- **A grid of local preimages of a global box section is killed by the overlap difference of
the second covering**, as soon as its pairwise intersections are affine. -/
theorem lTensor_sectionsOverlapDiff_eq_zero {I J : Type*} [Finite I] [Finite J]
    {U : I → X.Opens} (hU : ∀ i, IsAffineOpen (U i))
    {V : J → Y.Opens} (hVinf : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (w : ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) ⊤))
    (z : ∀ i j, TensorProduct k ↑(sectionsOverField k a P (U i)) ↑(sectionsOverField k b Q (V j)))
    (hz : ∀ i j, boxSectionMapInf k a b P Q (U i) (V j) (z i j)
      = sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
    (ζ : TensorProduct k (∀ i, ↑(sectionsOverField k a P (U i)))
      (∀ j, ↑(sectionsOverField k b Q (V j))))
    (hζ : ∀ i j, TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) ζ = z i j) :
    LinearMap.lTensor (∀ i, ↑(sectionsOverField k a P (U i)))
      (sectionsOverlapDiff k b Q V) ζ = 0 := by
  refine TensorProduct.eq_zero_of_map_proj _ fun i q => ?_
  have h : ∀ (m : J) (W : Y.Opens) (hW : W ≤ V m),
      TensorProduct.map (LinearMap.proj i)
          ((sectionsOverFieldRestrict k b Q hW).comp (LinearMap.proj m)) ζ
        = TensorProduct.map LinearMap.id (sectionsOverFieldRestrict k b Q hW) (z i m) := by
    intro m W hW
    rw [← hζ i m, TensorProduct.map_comp_apply, LinearMap.id_comp]
  rw [TensorProduct.map_proj_lTensor_apply,
    show (LinearMap.proj q ∘ₗ sectionsOverlapDiff k b Q V)
        = (sectionsOverFieldRestrict k b Q (inf_le_left : V q.1 ⊓ V q.2 ≤ V q.1)).comp
            (LinearMap.proj q.1) -
          (sectionsOverFieldRestrict k b Q (inf_le_right : V q.1 ⊓ V q.2 ≤ V q.2)).comp
            (LinearMap.proj q.2) from LinearMap.proj_pi _ _,
    TensorProduct.map_sub_right, sub_eq_zero, h, h]
  exact map_restrict_eq_of_boxSectionMapInf_right k a b P Q (hU i) (hVinf q.1 q.2) w
    (z i q.1) (z i q.2) (hz i q.1) (hz i q.2)

/-- **The global box-section comparison is surjective**, given two finite affine coverings whose
pairwise intersections are affine. -/
theorem surjective_globalBoxSectionMap_of_affineCovers {I J : Type*} [Finite I] [Finite J]
    {U : I → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hUcov : ⨆ i, U i = ⊤)
    (hUinf : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    {V : J → Y.Opens} (hV : ∀ j, IsAffineOpen (V j)) (hVcov : ⨆ j, V j = ⊤)
    (hVinf : ∀ j j', IsAffineOpen (V j ⊓ V j')) :
    Function.Surjective (globalBoxSectionMap k a b P Q) := by
  intro w
  choose z hz using fun (i : I) (j : J) =>
    (bijective_boxSectionMapInf k a b P Q (hU i) (hV j)).2
      (sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) le_top w)
  obtain ⟨ζ, hζ⟩ := TensorProduct.exists_map_proj_eq (R := k) z
  obtain ⟨u₀, hu₀⟩ : ζ ∈ LinearMap.range (TensorProduct.mapIncl
      (LinearMap.ker (sectionsOverlapDiff k a P U))
      (LinearMap.ker (sectionsOverlapDiff k b Q V))) := by
    rw [ProjectiveDeterminant.range_mapIncl_ker_eq_ker_rTensor_inf_ker_lTensor]
    exact ⟨rTensor_sectionsOverlapDiff_eq_zero k a b P Q hUinf hV w z hz ζ hζ,
      lTensor_sectionsOverlapDiff_eq_zero k a b P Q hU hVinf w z hz ζ hζ⟩
  refine ⟨TensorProduct.map (sectionsKerEquiv k a P U hUcov).symm.toLinearMap
    (sectionsKerEquiv k b Q V hVcov).symm.toLinearMap u₀, ?_⟩
  refine eq_of_sectionsOverFieldRestrict_eq k (boxBase k a b) (externalTensorProduct a b P Q)
    (iSup_preimage_inf_preimage_eq_top k a b hUcov hVcov) _ w fun p => ?_
  refine Eq.trans ?_ (hz p.1 p.2)
  refine (sectionsOverFieldRestrict_boxSectionMapOpens k a b P Q (le_top (a := U p.1))
    (le_top (a := V p.2))
    (le_top (a := pullback.fst a b ⁻¹ᵁ U p.1 ⊓ pullback.snd a b ⁻¹ᵁ V p.2))
    (boxTopFst k a b) (boxTopSnd k a b) inf_le_left inf_le_right _).trans ?_
  rw [map_restrict_map_sectionsKerEquiv_symm, hu₀, hζ]

/-- **The global box-section comparison is bijective**, given two finite affine coverings whose
pairwise intersections are affine. -/
theorem bijective_globalBoxSectionMap_of_affineCovers {I J : Type*} [Finite I] [Finite J]
    {U : I → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hUcov : ⨆ i, U i = ⊤)
    (hUinf : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    {V : J → Y.Opens} (hV : ∀ j, IsAffineOpen (V j)) (hVcov : ⨆ j, V j = ⊤)
    (hVinf : ∀ j j', IsAffineOpen (V j ⊓ V j')) :
    Function.Bijective (globalBoxSectionMap k a b P Q) :=
  ⟨injective_globalBoxSectionMap_of_affineCovers k a b P Q hU hUcov hV hVcov,
    surjective_globalBoxSectionMap_of_affineCovers k a b P Q hU hUcov hUinf hV hVcov hVinf⟩

/-- **The global box-section comparison is bijective for a quasi-compact separated pair.** -/
theorem bijective_globalBoxSectionMap [CompactSpace X] [CompactSpace Y] [X.IsSeparated]
    [Y.IsSeparated] : Function.Bijective (globalBoxSectionMap k a b P Q) := by
  obtain ⟨I, hI, U, hU, hUcov⟩ := exists_finite_isAffineOpen_iSup_eq_top X
  obtain ⟨J, hJ, V, hV, hVcov⟩ := exists_finite_isAffineOpen_iSup_eq_top Y
  exact bijective_globalBoxSectionMap_of_affineCovers k a b P Q hU hUcov
    (fun i i' => (hU i).inf (hU i')) hV hVcov fun j j' => (hV j).inf (hV j')

/-- **For `X` and `Y` proper over a field `k` and `P`, `Q` quasi-coherent, the canonical map**

`Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`,  `s ⊗ t ↦ s ⊠ t`,

**is bijective.** -/
theorem bijective_globalBoxSectionMap_of_isProper [IsProper a] [IsProper b] :
    Function.Bijective (globalBoxSectionMap k a b P Q) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  have sep : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsProper f], Z.IsSeparated := by
    intro Z f _
    constructor
    rw [show terminal.from Z = f ≫ terminal.from (Spec (.of k)) from Subsingleton.elim _ _]
    infer_instance
  have := sep a
  have := sep b
  exact bijective_globalBoxSectionMap k a b P Q

end AlgebraicGeometry

end
