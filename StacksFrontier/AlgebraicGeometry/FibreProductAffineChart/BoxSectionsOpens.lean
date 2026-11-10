module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.GlobalBoxChartCover
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Opens

/-!
# The comparison map of box sections over a pair of opens

Let `k` be a field, let `a : X ⟶ Spec k` and `b : Y ⟶ Spec k`, and let `P` and `Q` be modules on
`X` and on `Y`. `AlgebraicGeometry.globalBoxSectionMap` compares `Γ(X, P) ⊗_k Γ(Y, Q)` with
`Γ(X ×_k Y, P ⊠ Q)`. This file records the same comparison over a pair of opens `U` of `X` and
`V` of `Y`, read on any open `W` of `X ×_k Y` inside `pr₁⁻¹U ⊓ pr₂⁻¹V`,

`Γ(P, U) ⊗_k Γ(Q, V) ⟶ Γ(P ⊠ Q, W)`,  `s ⊗ t ↦ s ⊠ t`,

and proves it **natural** in the triple `(U, V, W)`: shrinking all three and restricting the two
sections is the same as restricting the box section. At `U = V = W = ⊤` it is
`AlgebraicGeometry.globalBoxSectionMap` itself.

## Main definitions

* `AlgebraicGeometry.boxSectionBilinOpens`: the pairing `(s, t) ↦ s ⊠ t` over a pair of opens, as
  a `k`-bilinear map.
* `AlgebraicGeometry.boxSectionMapOpens`: the induced `k`-linear map out of
  `Γ(P, U) ⊗_k Γ(Q, V)`, with `AlgebraicGeometry.boxSectionMapOpens_tmul` its value on a pure
  tensor.

## Main results

* `AlgebraicGeometry.appLE_fst_comp_sectionsScalars` and
  `AlgebraicGeometry.appLE_snd_comp_sectionsScalars`: the two projections carry the ground field
  into the structure sheaf of `X ×_k Y` by the same ring map, over an arbitrary pair of opens.
* `AlgebraicGeometry.externalTensorSection_smul_left` and `..._smul_right`: the box section of a
  pair of local sections is `k`-linear in each argument.
* `AlgebraicGeometry.globalBoxSectionMap_eq_boxSectionMapOpens`: at `⊤` the comparison is
  `AlgebraicGeometry.globalBoxSectionMap`.
* `AlgebraicGeometry.sectionsOverFieldRestrict_boxSectionMapOpens`: **the comparison is natural in
  the triple of opens.**

## Implementation notes

The `k`-action on `Γ(P, U)` is `ModuleCat.restrictScalars` along
`AlgebraicGeometry.sectionsScalars`, so `c • s` is *definitionally* the action of
`sectionsScalars k a U c` on `s`; the two `k`-linearity fields of
`AlgebraicGeometry.boxSectionBilinOpens` are therefore the `Γ`-level semilinearity lemmas of
`StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.GlobalBoxSections` applied directly, with
no rewriting. Stating them at the `k`-level instead fails, because
`Module ↑Γ(X, U) ↑(sectionsOverField k a P U)` is not found by instance search.

The three opens of the target are not required to be the `pr₁⁻¹U ⊓ pr₂⁻¹V` of the two others:
that open is what the affine case uses, but `⊤` is what the global statement uses, and
`AlgebraicGeometry.Scheme.Hom.preimage_top` is a theorem rather than a definitional equality, so
tying `W` to `U` and `V` would put a transport in the way of the global statement. `W` is
therefore a parameter, with the two inclusions as hypotheses — exactly as in
`Stacks.Tag01VSPullbackTensor.externalTensorSection`.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
  (P : X.Modules) (Q : Y.Modules)

/-- A morphism `g` into `X` carries the `k`-structure of `U` to that of `W`, for any name of the
composite structure morphism. -/
private theorem appLE_comp_sectionsScalars {Z : Scheme.{u}} (g : Z ⟶ X) (U : X.Opens)
    (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ U) {f : Z ⟶ Spec (.of k)} (hf : g ≫ a = f) :
    sectionsScalars k a U ≫ g.appLE U W hW = sectionsScalars k f W := by
  subst hf
  exact (Category.assoc _ _ _).trans
    (congrArg (fun φ => (Scheme.ΓSpecIso (.of k)).inv ≫ φ)
      (Scheme.Hom.appLE_comp_appLE g a ⊤ U W _ hW))

/-- The first projection carries the `k`-structure of `U` to that of `W`, for any name of the
composite structure morphism. -/
theorem appLE_fst_comp_sectionsScalars (U : X.Opens) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) {f : pullback a b ⟶ Spec (.of k)}
    (hf : pullback.fst a b ≫ a = f) :
    sectionsScalars k a U ≫ (pullback.fst a b).appLE U W hW₁ = sectionsScalars k f W :=
  appLE_comp_sectionsScalars k a _ U W hW₁ hf

/-- The second projection carries the `k`-structure of `V` to that of `W`, for any name of the
composite structure morphism. -/
theorem appLE_snd_comp_sectionsScalars (V : Y.Opens) (W : (pullback a b).Opens)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) {f : pullback a b ⟶ Spec (.of k)}
    (hf : pullback.snd a b ≫ b = f) :
    sectionsScalars k b V ≫ (pullback.snd a b).appLE V W hW₂ = sectionsScalars k f W :=
  appLE_comp_sectionsScalars k b _ V W hW₂ hf

/-- **The box section of a pair of local sections is `k`-linear in its first argument.** -/
theorem externalTensorSection_smul_left {U : X.Opens} {V : Y.Opens}
    (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) (c : k) (s : ↑Γ(P, U)) (t : ↑Γ(Q, V)) :
    externalTensorSection a b P Q (sectionsScalars k a U c • s) t W hW₁ hW₂
      = sectionsScalars k (boxBase k a b) W c • externalTensorSection a b P Q s t W hW₁ hW₂ := by
  rw [Stacks.Tag01VSPullbackTensor.externalTensorSection_smul_left]
  refine congrArg (fun r => r • externalTensorSection a b P Q s t W hW₁ hW₂) ?_
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
    (appLE_fst_comp_sectionsScalars k a b U W hW₁ (f := boxBase k a b) rfl) c

/-- **The box section of a pair of local sections is `k`-linear in its second argument.** -/
theorem externalTensorSection_smul_right {U : X.Opens} {V : Y.Opens}
    (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) (c : k) (s : ↑Γ(P, U)) (t : ↑Γ(Q, V)) :
    externalTensorSection a b P Q s (sectionsScalars k b V c • t) W hW₁ hW₂
      = sectionsScalars k (boxBase k a b) W c • externalTensorSection a b P Q s t W hW₁ hW₂ := by
  rw [Stacks.Tag01VSPullbackTensor.externalTensorSection_smul_right]
  refine congrArg (fun r => r • externalTensorSection a b P Q s t W hW₁ hW₂) ?_
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
    (appLE_snd_comp_sectionsScalars k a b V W hW₂ (f := boxBase k a b)
      pullback.condition.symm) c

/-- **The canonical pairing of local sections into the sections of a box product over an open.** -/
def boxSectionBilinOpens (U : X.Opens) (V : Y.Opens) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    ↑(sectionsOverField k a P U) →ₗ[k] ↑(sectionsOverField k b Q V) →ₗ[k]
      ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) W) :=
  LinearMap.mk₂ k
    (fun s t => externalTensorSection a b P Q s t W hW₁ hW₂)
    (fun s s' t => Stacks.Tag01VSPullbackTensor.externalTensorSection_add_left
      a b P Q s s' t W hW₁ hW₂)
    (fun c s t => externalTensorSection_smul_left k a b P Q W hW₁ hW₂ c s t)
    (fun s t t' => Stacks.Tag01VSPullbackTensor.externalTensorSection_add_right
      a b P Q s t t' W hW₁ hW₂)
    (fun c s t => externalTensorSection_smul_right k a b P Q W hW₁ hW₂ c s t)

/-- **The comparison map `Γ(P, U) ⊗_k Γ(Q, V) ⟶ Γ(P ⊠ Q, W)`.** -/
def boxSectionMapOpens (U : X.Opens) (V : Y.Opens) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V) →ₗ[k]
      ↑(sectionsOverField k (boxBase k a b) (externalTensorProduct a b P Q) W) :=
  TensorProduct.lift (boxSectionBilinOpens k a b P Q U V W hW₁ hW₂)

/-- The comparison map sends a pure tensor `s ⊗ t` to the box section `s ⊠ t` on `W`. -/
@[simp] theorem boxSectionMapOpens_tmul (U : X.Opens) (V : Y.Opens) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V)
    (s : ↑(sectionsOverField k a P U)) (t : ↑(sectionsOverField k b Q V)) :
    boxSectionMapOpens k a b P Q U V W hW₁ hW₂ (s ⊗ₜ[k] t)
      = externalTensorSection a b P Q s t W hW₁ hW₂ := rfl

/-- At `⊤` the comparison over a pair of opens is
`AlgebraicGeometry.globalBoxSectionMap`. -/
theorem globalBoxSectionMap_eq_boxSectionMapOpens :
    globalBoxSectionMap k a b P Q
      = boxSectionMapOpens k a b P Q ⊤ ⊤ ⊤ (boxTopFst k a b) (boxTopSnd k a b) := rfl

/-- **The comparison map is natural in the triple of opens.** Restricting the box section of a
tensor to a smaller triple is the box section of the restricted tensor. -/
theorem sectionsOverFieldRestrict_boxSectionMapOpens
    {U U' : X.Opens} (hU : U' ≤ U) {V V' : Y.Opens} (hV : V' ≤ V)
    {W W' : (pullback a b).Opens} (hW : W' ≤ W)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V)
    (hW'₁ : W' ≤ pullback.fst a b ⁻¹ᵁ U') (hW'₂ : W' ≤ pullback.snd a b ⁻¹ᵁ V')
    (z : TensorProduct k ↑(sectionsOverField k a P U) ↑(sectionsOverField k b Q V)) :
    sectionsOverFieldRestrict k (boxBase k a b) (externalTensorProduct a b P Q) hW
        (boxSectionMapOpens k a b P Q U V W hW₁ hW₂ z)
      = boxSectionMapOpens k a b P Q U' V' W' hW'₁ hW'₂
          (TensorProduct.map (sectionsOverFieldRestrict k a P hU)
            (sectionsOverFieldRestrict k b Q hV) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s t =>
    exact (Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map a b P Q s t
      hW₁ hW₂ (hW.trans hW₁) (hW.trans hW₂) (homOfLE hW)).trans <|
      (Stacks.Tag01VSPullbackTensor.externalTensorSection_restrict_left a b P Q hU s t W'
        (hW.trans hW₁) hW'₁ (hW.trans hW₂)).symm.trans
      (Stacks.Tag01VSPullbackTensor.externalTensorSection_restrict_right a b P Q hV
        (P.presheaf.map (homOfLE hU).op s) t W' hW'₁ (hW.trans hW₂) hW'₂).symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

end AlgebraicGeometry

end
