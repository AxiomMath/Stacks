module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
import StacksCore.Tactic.StacksAttribute

/-!
# Situation [Stacks, Tag 0B5D] is stable under extension of the ground field

Let `S` be a datum of Situation [Stacks, Tag 0B5D] — a field `k`, a proper scheme `X ⟶ Spec k`
of dimension one, and `H⁰(X, 𝒪_X) = k` — and let `K/k` be an extension of fields. This file
builds the datum of the same situation for `X_K = X ×_{Spec k} Spec K` over `K`.

## Main definitions

* `AlgebraicGeometry.CohenMacaulayCurveSituation.baseChange`: the base-changed situation.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.algebraicClosure`: its specialisation to
  `K = k̄`, whose base field is algebraically closed.

## Main results

* `AlgebraicGeometry.CohenMacaulayCurveSituation.baseChange_k`,
  `.baseChange_X`, `.baseChange_f`: the three components of the base-changed situation.

## Implementation notes

The three clauses of the situation are the three clauses of [Stacks, Tag 0BY9]:

* properness of `X_K ⟶ Spec K` is stability of `IsProper` under base change,
  [Stacks, Tag 01W4], which is `AlgebraicGeometry.IsProper.isStableUnderBaseChange`;
* `topologicalKrullDim X_K = topologicalKrullDim X` is
  `AlgebraicGeometry.topologicalKrullDim_baseChange`, whose own local input is part (1) of
  [Stacks, Tag 02FY];
* `H⁰(X_K, 𝒪) = K` is `AlgebraicGeometry.isIso_globalSections_baseChange`, which is flat base
  change in degree zero, part (1) of [Stacks, Tag 02KH] over an affine base.

The extension is given by an `Algebra S.k K` instance and the base change is taken at the chosen
categorical pullback, matching `AlgebraicGeometry.isIso_globalSections_pullback`.

## References

* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### [Stacks, Tag 01W4]

Both halves of the tag — the base change of a proper morphism is proper, and the base change of a
universally closed morphism is universally closed — are instances in Mathlib. -/

add_to_stacks 01W4 "the proper case" AlgebraicGeometry.IsProper.isStableUnderBaseChange

add_to_stacks 01W4 "the universally closed case"
  AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_sga "1 VIII 4.7" "necessity" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_sga "3 V 6.1" "partial" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_ega "II 5.4.9" "5.4.2(iii)" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_ega "IV 2.4.3" "(iii)" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange
add_to_ega "IV 2.6.4" "(ii)" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange

namespace CohenMacaulayCurveSituation

/-- **Situation [Stacks, Tag 0B5D] after an extension `K/k` of the ground field.** For a proper
one-dimensional `k`-scheme `X` with `H⁰(X, 𝒪_X) = k`, the base change `X_K ⟶ Spec K` is again
proper, again one-dimensional, and again has `K` for its ring of global regular functions. -/
def baseChange (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K] [Algebra S.k K] :
    CohenMacaulayCurveSituation.{u} where
  k := K
  X := pullback S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k K)))
  f := pullback.snd S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k K)))
  proper := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback _ _) inferInstance
  dimension_one :=
    (topologicalKrullDim_baseChange S.k K _ _ S.f (IsPullback.of_hasPullback _ _)).trans
      S.dimension_one
  isIso_globalSections := isIso_globalSections_pullback S.k K S.f

/-- The ground field of `S.baseChange K` is `K`. -/
@[simp] theorem baseChange_k (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K]
    [Algebra S.k K] : (S.baseChange K).k = K := rfl

/-- The scheme of `S.baseChange K` is the pullback `X ×_{Spec k} Spec K`. -/
@[simp] theorem baseChange_X (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K]
    [Algebra S.k K] : (S.baseChange K).X =
      pullback S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k K))) := rfl

/-- The structure morphism of `S.baseChange K` is the second projection
`X ×_{Spec k} Spec K ⟶ Spec K`. -/
@[simp] theorem baseChange_f (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K]
    [Algebra S.k K] : (S.baseChange K).f =
      pullback.snd S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k K))) := rfl

/-- **Situation [Stacks, Tag 0B5D] over the algebraic closure of its ground field.** The
specialisation of `baseChange` to `K = k̄`. -/
abbrev algebraicClosure (S : CohenMacaulayCurveSituation.{u}) :
    CohenMacaulayCurveSituation.{u} :=
  S.baseChange (AlgebraicClosure S.k)

/-- The ground field of `algebraicClosure` is algebraically closed. -/
instance isAlgClosed_algebraicClosure_k (S : CohenMacaulayCurveSituation.{u}) :
    IsAlgClosed S.algebraicClosure.k :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure S.k))

/-- The projection `X_{k̄} ⟶ X` of the situation over the algebraic closure. -/
abbrev algebraicClosureProj (S : CohenMacaulayCurveSituation.{u}) :
    S.algebraicClosure.X ⟶ S.X :=
  pullback.fst S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k))))

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
