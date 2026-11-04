module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.CommonModification

/-!
# The data of Stacks 0F9K for a derived tensor product

Let `X` be a scheme over `S`, let `b : W ⟶ 𝐏¹_X` be a morphism with fibre at infinity `W_∞`, and
for `i = 1, 2` let `Z_i ⊆ X` be closed, let `Q_i ∈ D(𝒪_W)` be perfect and let `T_i ⊆ W_∞` be
closed, contain every point of `W_∞` lying over `X ∖ Z_i`, and be such that `Q_i|_{T_i}` is zero.
In the proof of Stacks 0FBF the source observes that `Q = Q_1 ⊗^L Q_2` then satisfies the same
hypotheses for `Z_1 ∩ Z_2` and `T_1 ∪ T_2`:

* `T_1 ∪ T_2` contains every point of `W_∞` lying over `X ∖ (Z_1 ∩ Z_2)`, since such a point lies
  over `X ∖ Z_1` or over `X ∖ Z_2`;
* `Q|_{T_1 ∪ T_2}` is zero, since the derived fibre of `Q` at a point of `T_1 ∪ T_2` is the
  tensor product of those of `Q_1` and `Q_2`, one of which vanishes;
* if the restrictions of `Q_i` to `b^{-1}(𝐀¹_X)` are the pullbacks of `F_i ∈ D(𝒪_X)`, then the
  restriction of `Q` is the pullback of `F_1 ⊗^L F_2`, because derived pullback commutes with
  derived tensor product.

`Q` is perfect and its Chern classes are defined when those of the `Q_i` are, by
`AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct` and
`Stacks.Chow.hasDefinedChernClasses_derivedTensor`. Hence the classes `P'_p(Q)` and `c'_p(Q)` of
Stacks 0F9K are defined for `b`, `Z_1 ∩ Z_2`, `Q` and `T_1 ∪ T_2`.

## Main results

* `Stacks.Chow.mem_range_reducedUnion_of_notMem_range_inter` — `T_1 ∪ T_2` contains every point
  of `W_∞` lying over `X ∖ (Z_1 ∩ Z_2)`.
* `Stacks.Chow.isZero_derivedPullback_reducedUnion_derivedTensor` — `Q|_{T_1 ∪ T_2}` is zero.
* `Stacks.Chow.nonempty_derivedPullback_derivedTensor_iso` — if `Lu^*Q_i ≅ Lv^*F_i` for
  `i = 1, 2`, then `Lu^*(Q_1 ⊗^L Q_2) ≅ Lv^*(F_1 ⊗^L F_2)`; in particular the restriction of `Q`
  to `b^{-1}(𝐀¹_X)` is the pullback of `F_1 ⊗^L F_2`.

## Implementation notes

`Z_1 ∩ Z_2` is the fibre product `Z_1 ×_X Z_2`, mapping to `X` through `Z_2`, as in
`Stacks.Chow.closedCoverPowerSum_derivedTensor`. `T_1 ∪ T_2` is the reduced closed subscheme of
`W_∞` on the union of the images (`Stacks.Chow.reducedUnionIdeal`); the source leaves the scheme
structure of the union implicit, and by the first assertion of Stacks 0FAU
(`Stacks.Chow.localizedModificationClass_eq`) the classes of Stacks 0F9K do not depend on it.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The data of Stacks 0F9K for `Q₁ ⊗^L Q₂` -/

section Tensor

variable {X S W Z₁ Z₂ T₁ T₂ : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)
  (z₁ : Z₁ ⟶ X) (z₂ : Z₂ ⟶ X) (t₁ : T₁ ⟶ modificationFibreAtInfinity f b)
  (t₂ : T₂ ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion t₁] [IsClosedImmersion t₂]

/-- **`T₁ ∪ T₂` contains the points of `W_∞` over `X ∖ (Z₁ ∩ Z₂)`.** If `T_i ⊆ W_∞` contains every
point of `W_∞` lying over `X ∖ Z_i` for `i = 1, 2`, then the reduced closed subscheme on
`T₁ ∪ T₂` contains every point of `W_∞` lying over `X ∖ (Z₁ ∩ Z₂)`. -/
theorem mem_range_reducedUnion_of_notMem_range_inter
    (hT₁ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₁ → w ∈ Set.range t₁)
    (hT₂ : ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range z₂ → w ∈ Set.range t₂) :
    ∀ w, modificationProjectionAtInfinity f b w ∉ Set.range (pullback.snd z₁ z₂ ≫ z₂) →
      w ∈ Set.range (reducedUnionIdeal t₁ t₂).subschemeι := by
  intro w hw
  rw [range_subschemeι_reducedUnionIdeal, Set.mem_union]
  rw [Scheme.Pullback.range_snd_comp, Set.mem_inter_iff, not_and_or] at hw
  exact hw.imp (hT₁ w) (hT₂ w)

/-- **`(Q₁ ⊗^L Q₂)|_{T₁ ∪ T₂}` is zero.** If `Q₁`, `Q₂ ∈ D(𝒪_W)` are perfect and restrict to zero
on `T₁ ⟶ W_∞ ⟶ W` and on `T₂ ⟶ W_∞ ⟶ W`, then `Q₁ ⊗^L Q₂` restricts to zero on the reduced
closed subscheme of `W_∞` on `T₁ ∪ T₂`. -/
theorem isZero_derivedPullback_reducedUnion_derivedTensor {Q₁ Q₂ : DerivedCategory W.Modules}
    (perfect₁ : RingedSpace.IsPerfect.{u, u + 1} Q₁)
    (perfect₂ : RingedSpace.IsPerfect.{u, u + 1} Q₂)
    (hzero₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t₁ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₁))
    (hzero₂ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (t₂ ≫ modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj Q₂)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      ((reducedUnionIdeal t₁ t₂).subschemeι ≫
        modificationInclusionAtInfinity f b).toLRSHom.toShHom).obj
      (((derivedTensorProductFunctor W.sheaf).obj Q₁).obj Q₂)) := by
  refine isZero_derivedPullback_derivedTensor_of_range_subset
    (t₁ ≫ modificationInclusionAtInfinity f b) (t₂ ≫ modificationInclusionAtInfinity f b)
    perfect₁ perfect₂ hzero₁ hzero₂ _ ?_
  rintro _ ⟨y, rfl⟩
  rcases (range_subschemeι_reducedUnionIdeal t₁ t₂ ▸
      Set.mem_range_self y : (reducedUnionIdeal t₁ t₂).subschemeι y ∈
        Set.range t₁ ∪ Set.range t₂) with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨x, by rw [Scheme.Hom.comp_apply, hx, Scheme.Hom.comp_apply]⟩
  · exact Or.inr ⟨x, by rw [Scheme.Hom.comp_apply, hx, Scheme.Hom.comp_apply]⟩

end Tensor

/-- **Derived pullback identifications pass to derived tensor products.** If `Lu^*Q_i ≅ Lv^*F_i`
for `i = 1, 2`, then `Lu^*(Q₁ ⊗^L Q₂) ≅ Lv^*(F₁ ⊗^L F₂)`. For `u` the inclusion of
`b^{-1}(𝐀¹_X)` into `W` and `v` its projection to `X`, this says that if the restrictions of `Q₁`
and `Q₂` to `b^{-1}(𝐀¹_X)` are the pullbacks of `F₁` and `F₂`, then the restriction of
`Q₁ ⊗^L Q₂` is the pullback of `F₁ ⊗^L F₂`. -/
theorem nonempty_derivedPullback_derivedTensor_iso {V W X : Scheme.{u}} (u : V ⟶ W) (v : V ⟶ X)
    {Q₁ Q₂ : DerivedCategory W.Modules} {F₁ F₂ : DerivedCategory X.Modules}
    (e₁ : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        u.toLRSHom.toShHom).obj Q₁ ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v.toLRSHom.toShHom).obj F₁))
    (e₂ : Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        u.toLRSHom.toShHom).obj Q₂ ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v.toLRSHom.toShHom).obj F₂)) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        u.toLRSHom.toShHom).obj (((derivedTensorProductFunctor W.sheaf).obj Q₁).obj Q₂) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj F₁).obj F₂)) := by
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  exact ⟨derivedPullbackDerivedTensorIso u Q₁ Q₂ ≪≫ derivedTensorMapIso e₁ e₂ ≪≫
    (derivedPullbackDerivedTensorIso v F₁ F₂).symm⟩

end Stacks.Chow

end
