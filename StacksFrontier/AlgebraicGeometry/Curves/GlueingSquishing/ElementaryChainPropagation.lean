module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono

/-!
# Properness and reducedness along a chain of elementary steps

The induction of [Stacks, Tag 0C20] runs along the factorization

`X' = X_n ⟶ X_{n-1} ⟶ ⋯ ⟶ X_1 ⟶ X_0 = X`

of [Stacks, Tag 0C1L], and the per-step computations
`Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_one_add_of_connectedComponents_eq` and
`Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_isSquishingTangentVector` need the
**source** of each step to be proper over `k` (cases (2) and (3)) and reduced (case (3)). Only the
two ends of the chain come with those hypotheses: `X^ν` is a normalization, hence reduced, and `X`
is the curve one started from, hence proper. This file supplies the rest, and the two properties
travel in **opposite directions**:

* **properness goes up**, from `X_i` to `X_{i+1}`: an elementary step is finite, a finite
  morphism is proper, and properness is stable under composition, so
  `X_{i+1} ⟶ X_i ⟶ Spec k` is proper as soon as `X_i ⟶ Spec k` is. No surjectivity and no
  descent are involved.
* **reducedness goes down**, from `X_{i+1}` to `X_i`: the inclusion `𝒪_{X_i} ⊂ f_*𝒪_{X_{i+1}}`
  of [Stacks, Tag 0C1L] is injective on sections over every open, and a subring of a reduced
  ring is reduced.

Both directions start at an end of the chain where the property is given, so between them every
intermediate scheme is proper and reduced.

## Implementation notes

**Why reducedness is not a descent statement.** "A finite surjection from a reduced scheme has
reduced target" is false: `Spec k ⟶ Spec k[ε]` is finite and surjective, its source is reduced
and its target is not. What makes reducedness travel here is not the surjectivity of an
elementary step but the injectivity of its structure-sheaf map — the clause
`Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f.left).hom` of
`Stacks.GlueSquishFactor.IsAlmostIso`, which the splitting lemma
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` carries to both halves of an
intermediate factorization. So `Stacks.GlueSquishFactor.IsAlmostIso.isReduced_target` is stated
at `IsAlmostIso` rather than at `IsElementaryChain`: the latter predicate has forgotten the
inclusion of structure sheaves, and reducedness genuinely does not follow from it.

**Why properness is not a descent statement either.** It could be: properness does descend
along a surjection, by `AlgebraicGeometry.UniversallyClosed.of_comp_surjective` together with
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` ([Stacks, Tag 09MQ]). But that
route would additionally need the finite type of the *target*, whereas the direction used here
needs nothing beyond the finiteness that every elementary step already has.

## Main results

* `Stacks.GlueSquishFactor.IsElementaryStep.isProper_source` and
  `Stacks.GlueSquishFactor.IsElementaryChain.isProper_source` — the source of an elementary step,
  and of a whole chain, is proper over `k` when the target is.
* `Stacks.GlueSquishFactor.isReduced_of_injective_app` — the target of a morphism injective on
  sections over every open is reduced when the source is.
* `Stacks.GlueSquishFactor.isReduced_of_mono_hom_pushforwardAlgebra` and
  `Stacks.GlueSquishFactor.IsAlmostIso.isReduced_target` — the same, at the two spellings of
  `𝒪_X ⊂ f_*𝒪_{X'}` that occur in [Stacks, Tag 0C1L].

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.GlueSquishFactor

/-! ### Properness travels from the target of a step to its source -/

/-- The source of a finite morphism over `Spec k` is proper when the target is. -/
private theorem isProper_source_of_isFinite {k : Type u} [Field k] {Y' Y : Over (Spec (.of k))}
    (f : Y' ⟶ Y) [IsFinite f.left] [IsProper (Y.left ↘ Spec (.of k))] :
    IsProper (Y'.left ↘ Spec (.of k)) := by
  have hw : f.left ≫ (Y.left ↘ Spec (.of k)) = Y'.left ↘ Spec (.of k) := by simp
  rw [← hw]
  infer_instance

/-- **The source of an elementary step is proper over `k` when its target is.** An elementary
step `f` is finite by `Stacks.GlueSquishFactor.IsElementaryStep.isFinite`, a finite morphism is
proper, and the structure morphism of the source factors as `f` followed by the structure
morphism of the target. -/
theorem IsElementaryStep.isProper_source {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryStep f)
    [IsProper (Y.left ↘ Spec (.of k))] : IsProper (Y'.left ↘ Spec (.of k)) := by
  have := hf.isFinite
  exact isProper_source_of_isFinite f

/-- **The source of a chain of elementary steps is proper over `k` when its target is.** A chain
is finite by `Stacks.GlueSquishFactor.IsElementaryChain.isFinite`; applied to the initial
segments of a chain this says that every intermediate scheme of the factorization of
[Stacks, Tag 0C1L] is proper over `k`, which is what cases (2) and (3) of the induction of
[Stacks, Tag 0C20] ask of the source of each step. -/
theorem IsElementaryChain.isProper_source {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsElementaryChain k f)
    [IsProper (Y.left ↘ Spec (.of k))] : IsProper (Y'.left ↘ Spec (.of k)) := by
  have := hf.isFinite
  exact isProper_source_of_isFinite f

/-! ### Reducedness travels from the source of a step to its target -/

/-- **A scheme receiving an injection of sections from a reduced scheme is reduced.** A scheme is
reduced when its ring of sections over every open is, and `Γ(X, U)` injects into
`Γ(X', f⁻¹U)`, which is reduced; a subring of a reduced ring has no nonzero nilpotents. -/
theorem isReduced_of_injective_app {X' X : Scheme.{u}} (f : X' ⟶ X) [IsReduced X']
    (hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom) : IsReduced X :=
  ⟨fun U => isReduced_of_injective (f.app U).hom (hinj U)⟩

/-- **The target of a morphism with `𝒪_X ⊂ f_*𝒪_{X'}` is reduced when the source is.** The
monomorphism `𝒪_X ⟶ f_*𝒪_{X'}` in the sheaves of commutative rings on `X` is injective on
sections over every open by
`Stacks.GlueSquishFactor.injective_app_of_mono_hom_pushforwardAlgebra`, which needs nothing of
`f`. -/
theorem isReduced_of_mono_hom_pushforwardAlgebra {X' X : Scheme.{u}} (f : X' ⟶ X) [IsReduced X']
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom) : IsReduced X :=
  isReduced_of_injective_app f (injective_app_of_mono_hom_pushforwardAlgebra f hmono)

/-- **The target of an almost isomorphism is reduced when the source is.** This is the clause
`Mono (pushforwardAlgebra f.left).hom` of `Stacks.GlueSquishFactor.IsAlmostIso` read as a
statement about reducedness. Along the factorization of [Stacks, Tag 0C1L] the upper halves
produced by the splitting lemmas satisfy `IsAlmostIso`, so applied to the composite
`X^ν ⟶ X_i` this gives the reducedness of `X_i` that case (3) of the induction of
[Stacks, Tag 0C20] asks of the source of each step. -/
theorem IsAlmostIso.isReduced_target {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsAlmostIso f) [IsReduced Y'.left] :
    IsReduced Y.left :=
  isReduced_of_mono_hom_pushforwardAlgebra f.left hf.2

end Stacks.GlueSquishFactor

end
