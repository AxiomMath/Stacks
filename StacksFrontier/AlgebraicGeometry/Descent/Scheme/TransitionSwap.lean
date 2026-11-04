module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.RestrictOpen

/-!
# The gluing isomorphism of a descent datum is inverted by the swap

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to
`X/S`, so that `φ : V ×_S X ≅ X ×_S V` is an isomorphism over `X ×_S X` satisfying the cocycle
condition. Read fibrewise, `φ` is a family of isomorphisms `φ_{x₁x₂} : V_{x₁} → V_{x₂}` indexed
by the points of `X ×_S X`, and the cocycle condition says `φ_{x₂x₃} ∘ φ_{x₁x₂} = φ_{x₁x₃}`.
Together with the identity `Δ^*φ = 1` (`AlgebraicGeometry.DescentDatum.diagHom_eq_id`) this
forces `φ_{x₂x₁} = φ_{x₁x₂}⁻¹`, that is, `σ^*φ = φ⁻¹` for the swap `σ` of `X ×_S X`.

This file proves that identity and deduces that, for an open `W ⊆ V`, the *inclusion*
`φ(W ×_S X) ⊆ X ×_S W` already implies the *equality* `φ(W ×_S X) = X ×_S W`, that is,
`AlgebraicGeometry.DescentDatum.IsTransitionInvariant`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.swapTransitionHom` is `σ^*φ`, the gluing isomorphism
  conjugated by the symmetry of the product: the morphism `X ×_S V ⟶ V ×_S X` whose fibre at
  `(x₁, x₂)` is `φ_{x₂x₁}`.

## Main results

* `CategoryTheory.Over.prodLeftIsoPullback_braiding`: the symmetry of a binary product in a
  slice category is the symmetry of the corresponding fibre product.
* `AlgebraicGeometry.DescentDatum.cocycle_lift`: **the cocycle condition read fibrewise**,
  `φ_{x₂x₃} ∘ φ_{x₁x₂} = φ_{x₁x₃}`, as an identity between morphisms out of an arbitrary
  `S`-scheme equipped with a point of `V` and two points of `X`.
* `AlgebraicGeometry.DescentDatum.transition_comp_swapTransitionHom` and
  `AlgebraicGeometry.DescentDatum.swapTransitionHom_eq_inv`: **`σ^*φ = φ⁻¹`**, computed in
  `Over S`.
* `AlgebraicGeometry.DescentDatum.transitionPullbackIso_inv_eq`: the same identity on the
  literal fibre products `V ×_S X` and `X ×_S V`.
* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_of_le`: **the inclusion implies the
  equality.** An open of `V` whose product with `X` is carried *into* `X ×_S W` by `φ` is
  invariant in the sense of `AlgebraicGeometry.DescentDatum.IsTransitionInvariant`.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Over

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {X : C} (Y Z : Over X)
  [HasPullback Y.hom Z.hom] [HasPullback Z.hom Y.hom]
  [HasBinaryProduct Y Z] [HasBinaryProduct Z Y]

/-- **The symmetry of a product in a slice category is the symmetry of the fibre product.**
Conjugating `CategoryTheory.prod.braiding` by `CategoryTheory.Over.prodLeftIsoPullback` at both
ends gives `CategoryTheory.Limits.pullbackSymmetry`. -/
lemma prodLeftIsoPullback_braiding :
    (prodLeftIsoPullback Z Y).hom ≫ (pullbackSymmetry Z.hom Y.hom).hom =
      (prod.braiding Z Y).hom.left ≫ (prodLeftIsoPullback Y Z).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, prodLeftIsoPullback_hom_snd,
      Category.assoc, prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.braiding_hom,
      prod.lift_fst]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, prodLeftIsoPullback_hom_fst,
      Category.assoc, prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.braiding_hom,
      prod.lift_snd]

end CategoryTheory.Over

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-! ### The cocycle condition, read fibrewise -/

/-- **The cocycle condition, read fibrewise.** Let `Z` be a scheme over `S`
with a morphism `α` to `V` and two morphisms `β`, `γ` to `X`, naming points `x₁ = α`,
`x₂ = β` and `x₃ = γ` of `X` together with a point of `V` over `x₁`. Then applying `φ` first
over `(x₁, x₂)` and then over `(x₂, x₃)` is applying it over `(x₁, x₃)`, which fibrewise is
`φ_{x₂x₃} ∘ φ_{x₁x₂} = φ_{x₁x₃}`. -/
lemma cocycle_lift {Z : Over S} (α : Z ⟶ (Over.map f).obj D.over) (β γ : Z ⟶ Over.mk f) :
    prod.lift (prod.lift α β ≫ D.transition.hom.left ≫ prod.snd) γ ≫
        D.transition.hom.left ≫ prod.snd =
      prod.lift α γ ≫ D.transition.hom.left ≫ prod.snd := by
  have h := congrArg (fun g ↦ prod.lift (prod.lift α β) γ ≫ g ≫
    (prod.snd : _ ⟶ (Over.map f).obj D.over)) (D.cocycle () () ())
  simp only [prodMapLastTwo, prodMapFirstThird, prod.associator_hom, prod.associator_inv,
    prod.braiding_hom] at h
  simpa [prod.comp_lift, prod.comp_lift_assoc] using h

/-! ### The swap of the gluing isomorphism -/

/-- `σ^*φ`, the gluing isomorphism conjugated by the symmetry of the product: the morphism
`X ×_S V ⟶ V ×_S X` whose fibre at `(x₁, x₂)` is `φ_{x₂x₁}`. -/
def swapTransitionHom :
    Over.mk f ⨯ (Over.map f).obj D.over ⟶ (Over.map f).obj D.over ⨯ Over.mk f :=
  (prod.braiding (Over.mk f) ((Over.map f).obj D.over)).hom ≫ D.transition.hom.left ≫
    (prod.braiding (Over.mk f) ((Over.map f).obj D.over)).hom

/-- The `X`-component of `σ^*φ ∘ φ` is the second projection. -/
lemma transition_comp_swapTransitionHom_snd :
    D.transition.hom.left ≫ D.swapTransitionHom ≫ prod.snd = (prod.snd : _ ⟶ Over.mk f) := by
  simp [swapTransitionHom]

/-- The `V`-component of `σ^*φ ∘ φ` is the first projection; fibrewise,
`φ_{x₂x₁} ∘ φ_{x₁x₂} = 1`. -/
lemma transition_comp_swapTransitionHom_fst :
    D.transition.hom.left ≫ D.swapTransitionHom ≫ prod.fst =
      (prod.fst : _ ⟶ (Over.map f).obj D.over) := by
  have h := D.cocycle_lift (Z := (Over.map f).obj D.over ⨯ Over.mk f) prod.fst prod.snd
    (prod.fst ≫ structureMap f D.over)
  rw [prod.lift_fst_snd] at h
  have hl : (prod.lift prod.fst (prod.fst ≫ structureMap f D.over) :
      (Over.map f).obj D.over ⨯ Over.mk f ⟶ (Over.map f).obj D.over ⨯ Over.mk f) =
      prod.fst ≫ diagLeft f D.over := by
    simp [prod.comp_lift]
  rw [hl, Category.assoc,
    show diagLeft f D.over ≫ D.transition.hom.left ≫ prod.snd = D.diagHom from rfl,
    D.diagHom_eq_id, Category.comp_id] at h
  simpa [swapTransitionHom, prod.comp_lift_assoc] using h

/-- **`σ^*φ` is a one-sided inverse of `φ`.** -/
lemma transition_comp_swapTransitionHom :
    D.transition.hom.left ≫ D.swapTransitionHom = 𝟙 _ := by
  apply prod.hom_ext <;> simp [D.transition_comp_swapTransitionHom_fst,
    D.transition_comp_swapTransitionHom_snd]

/-- **`σ^*φ = φ⁻¹`.** The gluing isomorphism of a descent datum is inverted by conjugating it
with the symmetry of the product, computed in `Over S`. -/
theorem swapTransitionHom_eq_inv : D.swapTransitionHom = D.transition.inv.left :=
  calc D.swapTransitionHom
      = (D.transition.inv.left ≫ D.transition.hom.left) ≫ D.swapTransitionHom := by
        rw [← Over.comp_left, D.transition.inv_hom_id, Over.id_left, Category.id_comp]
    _ = D.transition.inv.left := by
        rw [Category.assoc, D.transition_comp_swapTransitionHom, Category.comp_id]

/-! ### The identity on the literal fibre products -/

/-- **`σ^*φ = φ⁻¹` on the literal fibre products.** The inverse of
`AlgebraicGeometry.DescentDatum.transitionPullbackIso` is that isomorphism conjugated by
`CategoryTheory.Limits.pullbackSymmetry`. -/
theorem transitionPullbackIso_inv_eq :
    D.transitionPullbackIso.inv =
      (pullbackSymmetry f (D.over.hom ≫ f)).hom ≫ D.transitionPullbackIso.hom ≫
        (pullbackSymmetry f (D.over.hom ≫ f)).hom := by
  have hinv : D.transitionPullbackIso.inv =
      (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).inv ≫
        D.transition.inv.left.left ≫
          (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom := by
    simp [transitionPullbackIso, DescentData.gluingPullbackIso]
  have hhom : D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := rfl
  have hsym : (pullbackSymmetry f (D.over.hom ≫ f)).hom =
      (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).inv ≫
        (prod.braiding (Over.mk f) ((Over.map f).obj D.over)).hom.left ≫
          (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom := by
    rw [← Over.prodLeftIsoPullback_braiding, Iso.inv_hom_id_assoc]
    rfl
  rw [hinv, hhom, hsym, ← D.swapTransitionHom_eq_inv, swapTransitionHom]
  simp only [Over.comp_left, Category.assoc, Iso.hom_inv_id_assoc]

/-! ### The inclusion implies the equality -/

variable (W : D.over.left.Opens)

/-- **The inclusion implies the equality.** If the gluing isomorphism carries `W ×_S X` *into*
`X ×_S W`, then it carries it *onto* `X ×_S W`, so `W` is invariant in the sense of
`AlgebraicGeometry.DescentDatum.IsTransitionInvariant`. -/
theorem isTransitionInvariant_of_le
    (hle : D.transitionPullbackIso.hom ''ᵁ (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ W) ≤
      pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ W) :
    D.IsTransitionInvariant W := by
  have hswap : ∀ y : ↥(pullback f (D.over.hom ≫ f)), pullback.fst (D.over.hom ≫ f) f
      ((pullbackSymmetry f (D.over.hom ≫ f)).hom y) = pullback.snd f (D.over.hom ≫ f) y :=
    fun y ↦ by rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
  refine le_antisymm hle fun z hz ↦ ?_
  have hz' : pullback.fst (D.over.hom ≫ f) f
      ((pullbackSymmetry f (D.over.hom ≫ f)).hom z) ∈ W := by rw [hswap]; exact hz
  have hmem : pullback.snd f (D.over.hom ≫ f)
      (D.transitionPullbackIso.hom ((pullbackSymmetry f (D.over.hom ≫ f)).hom z)) ∈ W :=
    hle ⟨_, hz', rfl⟩
  refine ⟨D.transitionPullbackIso.inv z, ?_, ?_⟩
  · show pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv z) ∈ W
    rw [D.transitionPullbackIso_inv_eq]
    simpa only [Scheme.Hom.comp_apply, hswap] using hmem
  · exact (Scheme.homeoOfIso D.transitionPullbackIso).apply_symm_apply z

end DescentDatum

end AlgebraicGeometry

end
