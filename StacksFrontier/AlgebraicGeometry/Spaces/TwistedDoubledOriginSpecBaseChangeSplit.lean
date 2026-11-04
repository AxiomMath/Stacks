module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginAwayFromZero
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSpecSelfProduct

/-!
# Base change along the covering `Spec k' ⟶ Spec k` doubles a `k'`-scheme

Let `k'/k` be a degree two Galois extension with nonidentity automorphism `σ`, write
`T = Spec k'` and `S = Spec k`, and let `Y` be a scheme over `T`.  Because
`T ×_S T = T ⨿ T` (`specExtensionFiberProductSplitIso`), base change along `T ⟶ S` doubles
`Y`:

    `Y ×_S T ≅ Y ⨿ Y`,

the first summand being the graph of the structure morphism `p : Y ⟶ T` and the second the
graph of `σ ∘ p`.  Both summands project to `Y` by the identity, so the splitting is recorded
here as the single statement that

    `(Y ⨿ Y, 1 ⨿ 1, p ⨿ σp)`

is a fibre square for `p ≫ (T ⟶ S)` against `T ⟶ S`.

This is the shape in which a gluing isomorphism relative to the one-member covering
`{T ⟶ S}` is assembled: an isomorphism `Y ×_S T ≅ T ×_S Y` over `T ×_S T` amounts, under the
splitting, to a pair of isomorphisms of `Y` — one over each summand — and the cocycle condition
on the triple product likewise decomposes.

## Main results

* `AlgebraicGeometry.isPullback_coprodDesc_of_isPullback`: fibre products distribute over a
  binary coproduct.
* `AlgebraicGeometry.isPullback_baseChange_split_of_isPullback`: **a morphism whose
  self-product splits into two copies of its source doubles every scheme over that source.**
  This is the statement above with the splitting of `T ×_S T` taken as a hypothesis, so that
  it applies to any degree two Galois covering.
* `AlgebraicGeometry.TwistedDoubledOrigin.isPullback_specExtension_split`: **the self-product
  of the covering, in fibre-square form** — `T ⨿ T` is `T ×_S T`, with first projection
  `1 ⨿ 1` and second projection `1 ⨿ σ`.
* `AlgebraicGeometry.TwistedDoubledOrigin.isPullback_specExtension_baseChange_split`: **base
  change along the covering doubles a `k'`-scheme.**

## Implementation notes

The distributivity statement is
`AlgebraicGeometry.TwistedDoubledOrigin.coproductPullback_isPullback` transported along
the comparison isomorphisms of the two fibre squares being combined.

The doubling is obtained by pasting two squares vertically rather than by computing
`Y ×_S T` directly. The upper square is the base change of `1 ⨿ 1 : T ⨿ T ⟶ T` along
`p : Y ⟶ T`, which distributivity computes as `1 ⨿ 1 : Y ⨿ Y ⟶ Y` because the base change of
an identity is an identity; the lower square is the splitting of the self-product. Pasting
composes the two right-hand edges into `p ≫ (T ⟶ S)` and the two left-hand edges into
`(p ⨿ p) ≫ (1 ⨿ σ) = p ⨿ σp`.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Fibre products distribute over a binary coproduct.** If `P₀` is the fibre product of
`f₀` with `e` and `P₁` that of `f₁` with `e`, then `P₀ ⨿ P₁` is the fibre product of
`f₀ ⨿ f₁` with `e`. -/
theorem isPullback_coprodDesc_of_isPullback {T W X₀ X₁ P₀ P₁ : Scheme.{u}} (f₀ : X₀ ⟶ T)
    (f₁ : X₁ ⟶ T) (e : W ⟶ T)
    {a₀ : P₀ ⟶ X₀} {b₀ : P₀ ⟶ W} {a₁ : P₁ ⟶ X₁} {b₁ : P₁ ⟶ W}
    (h₀ : IsPullback a₀ b₀ f₀ e) (h₁ : IsPullback a₁ b₁ f₁ e) :
    IsPullback (coprod.desc (a₀ ≫ coprod.inl) (a₁ ≫ coprod.inr)) (coprod.desc b₀ b₁)
      (coprod.desc f₀ f₁) e := by
  have hdist := TwistedDoubledOrigin.coproductPullback_isPullback
    (fun b : Bool => bif b then X₀ else X₁)
    (Bool.rec (motive := fun b : Bool => (bif b then X₀ else X₁) ⟶ T) f₁ f₀) e
  refine hdist.of_iso (coprod.mapIso h₀.isoPullback.symm h₁.isoPullback.symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  · apply coprod.hom_ext <;> simp <;> rfl
  · apply coprod.hom_ext <;> simp

/-- **A covering whose self-product splits doubles every scheme over its source.** Let
`g : T ⟶ S` be a morphism whose self-product `T ×_S T` is `T ⨿ T`, with first projection the
identity on both summands and second projection `1 ⨿ s`.  Then for every `p : V ⟶ T` the
disjoint union `V ⨿ V` is the fibre product `V ×_S T`, projecting to `V` by the identity on
both summands and to `T` by `p` and by `s ∘ p`. -/
theorem isPullback_baseChange_split_of_isPullback {S T V : Scheme.{u}} {g : T ⟶ S} {s : T ⟶ T}
    (hsplit : IsPullback (coprod.desc (𝟙 T) (𝟙 T)) (coprod.desc (𝟙 T) s) g g) (p : V ⟶ T) :
    IsPullback (coprod.desc (𝟙 V) (𝟙 V)) (coprod.desc p (p ≫ s)) (p ≫ g) g := by
  have hid : IsPullback p (𝟙 V) (𝟙 T) p :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
  have hbase : IsPullback (coprod.desc (𝟙 V) (𝟙 V))
      (coprod.desc (p ≫ coprod.inl) (p ≫ coprod.inr)) p
      (coprod.desc (𝟙 T) (𝟙 T)) :=
    (isPullback_coprodDesc_of_isPullback (𝟙 T) (𝟙 T) p hid hid).flip
  have hleg : coprod.desc (p ≫ coprod.inl) (p ≫ coprod.inr) ≫ coprod.desc (𝟙 T) s =
      coprod.desc p (p ≫ s) := by
    apply coprod.hom_ext <;>
      simp only [coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
        Category.assoc, Category.comp_id]
  rw [← hleg]
  exact hbase.paste_vert hsplit

namespace TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- **The self-product of the covering `Spec k' ⟶ Spec k`, in fibre-square form.**
`Spec k' ⨿ Spec k'` is `Spec k' ×_{Spec k} Spec k'`, with first projection the identity on
both summands and second projection the identity on the first and the Galois automorphism on
the second. -/
theorem isPullback_specExtension_split (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    IsPullback (coprod.desc (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))))
      (coprod.desc (𝟙 (Spec (.of K))) (specGaloisAction k K σ))
      (specExtension k K) (specExtension k K) :=
  IsPullback.of_iso_pullback
    ⟨by
      apply coprod.hom_ext <;>
        simp only [coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.id_comp,
          specGaloisAction_comp_specExtension]⟩
    (specExtensionFiberProductSplitIso k K hdegree σ hσ).symm
    (specExtensionFiberProductSplitIso_first_factor k K hdegree σ hσ)
    (specExtensionFiberProductSplitIso_second_factor k K hdegree σ hσ)

/-- **Base change along the covering `Spec k' ⟶ Spec k` doubles a `k'`-scheme.** For a scheme
`Y` with structure morphism `p : Y ⟶ Spec k'`, the disjoint union `Y ⨿ Y` is the fibre product
`Y ×_{Spec k} Spec k'`: it projects to `Y` by the identity on both summands, and to `Spec k'`
by `p` on the first summand and by `σ ∘ p` on the second. -/
theorem isPullback_specExtension_baseChange_split (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) :
    IsPullback (coprod.desc (𝟙 Y) (𝟙 Y))
      (coprod.desc p (p ≫ specGaloisAction k K σ))
      (p ≫ specExtension k K) (specExtension k K) :=
  isPullback_baseChange_split_of_isPullback
    (isPullback_specExtension_split k K hdegree σ hσ) p

end TwistedDoubledOrigin

end AlgebraicGeometry

end
