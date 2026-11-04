module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PicardTorsionStep

/-!
# The `ℓ`-torsion of the Picard group along a chain of elementary steps

Let `k` be an algebraically closed field and let `ℓ` be a prime different from the
characteristic of `k`. [Stacks, Tag 0C1L] factors a finite morphism which is injective on
structure sheaves and an isomorphism away from finitely many points as a chain

`X' = X_n ⟶ ⋯ ⟶ X_0 = X`

of glueings of two rational points and squishings of tangent vectors; in Lean this is
`Stacks.GlueSquishFactor.IsElementaryChain`. The proof of [Stacks, Tag 0C20] runs along such a
chain, taken for the normalization `ν : X^ν ⟶ X` of a curve.

This file records what passes along the whole chain using only the inputs of the three per-step
computations `Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_ne_connectedComponents`,
`Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_one_add_of_connectedComponents_eq` and
`Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_isSquishingTangentVector`, that is, with no
bookkeeping of the number of steps: **the `ℓ`-torsion of the Picard group surjects along the
chain**, so `dim_{F_ℓ} Pic(X^ν)[ℓ] ≤ dim_{F_ℓ} Pic(X)[ℓ]`.

Surjectivity needs none of the properness or reducedness that the per-step *equalities* need: it
uses only exactness at `Pic(X)`, surjectivity of `Pic(X) ⟶ Pic(X')`, and the `ℓ`-divisibility of
`k^*` and of `(k,+)`, all of which hold for every glueing and every squishing. Both halves of
`Stacks.EllTorsion.surjective_restrict` are therefore available at every step, and surjections
compose.

The opposite inequality — the one [Stacks, Tag 0C20] needs — does not telescope this way: it
costs one dimension at each glueing of two points on the same connected component, and bounding
the number of those requires the `h¹` bookkeeping of the source, which compares
`dim_k H¹(X_i, 𝒪_{X_i})` across the three kinds of step. This file proves only the inequality
above.

## Main results

* `Stacks.PicardTorsionStep.surjective_restrict_picardPullback_of_isElementaryStep` — the
  `ℓ`-torsion of the Picard group surjects along one elementary step.
* `Stacks.PicardTorsionStep.surjective_restrict_picardPullback_of_isElementaryChain` — and
  along a whole chain.
* `Stacks.PicardTorsionStep.rank_torsionBy_picard_le_of_isElementaryChain` —
  `dim_{F_ℓ} Pic(X')[ℓ] ≤ dim_{F_ℓ} Pic(X)[ℓ]` along a chain.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.PicardTorsionStep

/-! ### One step -/

/-- **The `ℓ`-torsion of the Picard group surjects along one elementary step.** In both cases
the sequence of [Stacks, Tag 0C1M] resp. [Stacks, Tag 0C1N] is exact at `Pic(X)` with
`Pic(X) ⟶ Pic(X')` surjective, and the left-hand term `k^*` resp. `(k,+)` is `ℓ`-divisible, so
`Stacks.EllTorsion.surjective_restrict` applies. -/
theorem surjective_restrict_picardPullback_of_isElementaryStep {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y}
    (hf : Stacks.GlueSquishFactor.IsElementaryStep f) :
    Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom f.left :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Y'.left)) := by
  have hp := (Fact.out : ℓ.Prime)
  rcases hf with ⟨a, b, hg⟩ | ⟨θ, hs⟩
  · exact Stacks.EllTorsion.surjective_restrict
      (Stacks.GluePicard.exact_picardGluingHom_schemePullbackClassHom f.left a b hg)
      (Stacks.GluePicard.surjective_schemePullbackClassHom f.left a b hg)
      (Stacks.EllTorsion.exists_zsmul_eq_additive_units k hp.pos)
  · exact Stacks.EllTorsion.surjective_restrict
      (Stacks.SquishSheafSequence.exact_picardTangentHom_schemePullbackClassHom f.left θ hs)
      (Stacks.SquishPicard.surjective_schemePullbackClassHom f.left θ hs)
      (Stacks.EllTorsion.exists_zsmul_eq_self k hℓ)

/-! ### Isomorphisms and composites -/

/-- Restriction to `ℓ`-torsion of the Picard group pullbacks is contravariantly functorial. -/
private theorem restrict_schemePullbackClassHom_comp (ℓ : ℕ) {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (Stacks.EllTorsion.restrict ℓ (Stacks.Picard.schemePullbackClassHom.{u} f)).comp
      (Stacks.EllTorsion.restrict ℓ (Stacks.Picard.schemePullbackClassHom.{u} g)) =
    Stacks.EllTorsion.restrict ℓ (Stacks.Picard.schemePullbackClassHom.{u} (f ≫ g)) :=
  AddMonoidHom.ext fun _ => Subtype.ext (Stacks.Picard.schemePullbackClass_comp f g _)

/-- Pullback along an isomorphism is surjective on `ℓ`-torsion of the Picard group: it has a
right inverse, pullback along the inverse isomorphism. -/
theorem surjective_restrict_picardPullback_of_isIso {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ : ℕ) {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) [IsIso g] :
    Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom ((Over.forget (Spec (.of k))).map g) :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Y'.left)) := by
  refine Function.Surjective.of_comp (g := Stacks.EllTorsion.restrict ℓ
    (Stacks.Picard.schemePullbackClassHom.{u} (inv ((Over.forget (Spec (.of k))).map g)))) ?_
  rw [← AddMonoidHom.coe_comp, restrict_schemePullbackClassHom_comp, IsIso.hom_inv_id]
  exact fun c => ⟨c, Subtype.ext (Stacks.Picard.schemePullbackClass_id _ _)⟩

/-- Surjectivity on `ℓ`-torsion of the Picard group composes: pullback is contravariantly
functorial. -/
theorem surjective_restrict_picardPullback_comp {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ : ℕ) {Z Y' Y : Over (Spec (.of k))} (g : Z ⟶ Y') (f : Y' ⟶ Y)
    (hg : Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom g.left :
          Stacks.Picard.ofScheme Y'.left →+ Stacks.Picard.ofScheme Z.left)))
    (hf : Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom f.left :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Y'.left))) :
    Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom (g ≫ f).left :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Z.left)) := by
  rw [Over.comp_left, ← restrict_schemePullbackClassHom_comp, AddMonoidHom.coe_comp]
  exact hg.comp hf

/-! ### The whole chain -/

/-- **The `ℓ`-torsion of the Picard group surjects along a chain of elementary steps.** The
isomorphism case is pullback along an isomorphism, which is bijective; a single step is
`Stacks.PicardTorsionStep.surjective_restrict_picardPullback_of_isElementaryStep`; and
surjections compose, pullback being contravariantly functorial. -/
theorem surjective_restrict_picardPullback_of_isElementaryChain {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y}
    (hf : Stacks.GlueSquishFactor.IsElementaryChain k f) :
    Function.Surjective
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom f.left :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Y'.left)) := by
  induction hf with
  | of_isIso g hg =>
    have := hg
    exact surjective_restrict_picardPullback_of_isIso ℓ g
  | of_step g hg => exact surjective_restrict_picardPullback_of_isElementaryStep ℓ hℓ hg
  | comp hg hfs ihg ihf => exact surjective_restrict_picardPullback_comp ℓ _ _ ihg ihf

/-- **The dimension of the `ℓ`-torsion of the Picard group does not increase along a chain of
elementary steps.** Read at the chain of [Stacks, Tag 0C1L] attached to the normalization of a
curve, this is the inequality `dim_{F_ℓ} Pic(X^ν)[ℓ] ≤ dim_{F_ℓ} Pic(X)[ℓ]`. -/
theorem rank_torsionBy_picard_le_of_isElementaryChain {k : Type u} [Field k]
    [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y}
    (hf : Stacks.GlueSquishFactor.IsElementaryChain k f) :
    letI : Module (ZMod ℓ)
        (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y.left) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ)
        (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y'.left) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y'.left) (ℓ : ℤ)) ≤
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y.left) (ℓ : ℤ)) := by
  let : Module (ZMod ℓ)
      (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y.left) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ)
      (AddSubgroup.torsionBy (Stacks.Picard.ofScheme Y'.left) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine LinearMap.rank_le_of_surjective
    (Stacks.EllTorsion.toZModLinearMap (ℓ := ℓ)
      (Stacks.EllTorsion.restrict ℓ
        (Stacks.Picard.schemePullbackClassHom f.left :
          Stacks.Picard.ofScheme Y.left →+ Stacks.Picard.ofScheme Y'.left))) ?_
  simpa only [Stacks.EllTorsion.coe_toZModLinearMap] using
    surjective_restrict_picardPullback_of_isElementaryChain ℓ hℓ hf

end Stacks.PicardTorsionStep

end
