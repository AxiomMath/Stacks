module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion

/-!
# The scheme-level vocabulary of Stacks 0CAY

Let `Y → T → S` be morphisms of schemes, let `t ∈ T` lie over `s ∈ S` and let
`σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a ring map. Write `Y_σ` for the base change of `Y → T` along
`Spec(𝒪_{S,s}^∧) → T` determined by `σ`. This file introduces the predicates in which Stacks
0CAY is stated: that the fibre `Y_t` of `Y → T` at `t` is a closed subscheme of such a base
change, that two such closed subschemes have isomorphic conormal algebras, and the uniform
congruence bound that would force the latter.

## Main definitions

* `Stacks.ConormalApproximation.completedStalk`: the completed local ring `𝒪_{S,s}^∧`.
* `Stacks.ConormalApproximation.HasFibreImmersion`: the fibre `Y_t` is a closed subscheme of a
  base change `Y ×_T W`, over the residue field of `t`.
* `Stacks.ConormalApproximation.HasConormalIso`: any two such closed subschemes, in two base
  changes, have isomorphic conormal algebras.
* `Stacks.ConormalApproximation.HasIsoConormalFibreImmersions`: the conclusion of Stacks 0CAY
  for one pair of maps to `Spec(𝒪_{S,s}^∧)`.
* `Stacks.ConormalApproximation.HasUniformConormalBound`: a bound `N` such that agreement of two
  maps modulo `𝔪_s^N` already forces `HasConormalIso`.

## Implementation notes

The predicates are separated from the statements using them so that the geometric input
`HasFibreImmersion` can be proved in `CompletedBaseChangeFibre` before, rather than after, the
scheme-level statement `exists_finiteType_pointed_extension_conormalAlgebra_iso` that needs it.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.ConormalApproximation

/-- The completed local ring `𝒪_{S,s}^∧` of a scheme at a point. -/
abbrev completedStalk (S : Scheme.{u}) (s : S) : Type u :=
  AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)

/-- The fibre `Y_t` of `p : Y ⟶ T` at `t` is a closed subscheme of the base change `Y ×_T W`
along `b : W ⟶ T`, sitting over a point of `W` above `t` given by the residue field of `t` and
compatibly with both projections. For `W = Spec(𝒪_{S,s}^∧)` this is the first step of the proof
of Stacks 0CAY: the residue fields of `s` and `t` agree, so the closed point of `W` lies over `t`
and the fibre of the base change over it is `Y_t`. -/
def HasFibreImmersion {T Y W : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T) : Prop :=
  ∃ (r : Spec (CommRingCat.of (T.residueField t)) ⟶ W) (j : p.fiber t ⟶ pullback p b),
    r ≫ b = T.fromSpecResidueField t ∧
    j ≫ pullback.fst p b = p.fiberι t ∧
    j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r ∧
    IsClosedImmersion j

/-- **The closed immersion of `HasFibreImmersion` exhibits the fibre as the base change of the
chosen point of `W`.** Given the three compatibilities of `HasFibreImmersion` — that `r` lies over
`t`, and that `j` commutes with both projections — the square
```
Y_t -----------→ Spec κ(t)
 |                   |
 j                   r
 ↓                   ↓
Y ×_T W --pr₂--→     W
```
is cartesian, by the pasting law: pasting it onto the defining square of `Y ×_T W` gives the
defining square of `Y_t`, because `r ≫ b = T.fromSpecResidueField t`.

This is the form in which the chart-local data of the fibre is computed, and it is also what makes
`j` a closed immersion whenever `r` is one. -/
theorem isPullback_fibre_of_immersionData {T Y W : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T)
    (r : Spec (CommRingCat.of (T.residueField t)) ⟶ W) (j : p.fiber t ⟶ pullback p b)
    (hr : r ≫ b = T.fromSpecResidueField t)
    (hfst : j ≫ pullback.fst p b = p.fiberι t)
    (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r) :
    IsPullback (p.fiberToSpecResidueField t) j r (pullback.snd p b) := by
  have hbottom : IsPullback (pullback.snd p b) (pullback.fst p b) b p :=
    (IsPullback.of_hasPullback _ _).flip
  have hpasted : IsPullback (p.fiberToSpecResidueField t) (j ≫ pullback.fst p b) (r ≫ b) p := by
    rw [hr, hfst]
    exact (IsPullback.of_hasPullback p (T.fromSpecResidueField t)).flip
  exact hpasted.of_bot hsnd.symm hbottom

/-- Any two closed immersions of the fibre `Y_t` into the base changes of `p : Y ⟶ T` along
`b : W ⟶ T` and `b' : W' ⟶ T`, compatible with the projections as in `HasFibreImmersion`, have
isomorphic conormal algebras. -/
def HasConormalIso {T Y W W' : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T) (b' : W' ⟶ T) :
    Prop :=
  ∀ (r : Spec (CommRingCat.of (T.residueField t)) ⟶ W)
    (r' : Spec (CommRingCat.of (T.residueField t)) ⟶ W')
    (j : p.fiber t ⟶ pullback p b) (j' : p.fiber t ⟶ pullback p b'),
    r ≫ b = T.fromSpecResidueField t → r' ≫ b' = T.fromSpecResidueField t →
    j ≫ pullback.fst p b = p.fiberι t → j' ≫ pullback.fst p b' = p.fiberι t →
    j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r →
    j' ≫ pullback.snd p b' = p.fiberToSpecResidueField t ≫ r' →
    ∀ (hj : IsClosedImmersion j) (hj' : IsClosedImmersion j'),
      letI : IsClosedImmersion j := hj
      letI : IsClosedImmersion j' := hj'
      Nonempty ((Stacks.Conormal.conormalAlgebra j).algebra ≅
        (Stacks.Conormal.conormalAlgebra j').algebra)

/-- The fibre `Y_t` is a closed subscheme of both base changes and the two conormal algebras are
isomorphic: the conclusion of Stacks 0CAY for one pair of maps to `Spec(𝒪_{S,s}^∧)`. -/
def HasIsoConormalFibreImmersions {T Y W W' : Scheme.{u}} (p : Y ⟶ T) (t : T)
    (b : W ⟶ T) (b' : W' ⟶ T) : Prop :=
  HasFibreImmersion p t b ∧ HasFibreImmersion p t b' ∧ HasConormalIso p t b b'

/-- A bound `N ≥ 1` such that two maps `𝒪_{T,t} → 𝒪_{S,s}^∧` agreeing modulo `𝔪_s^N` already
give isomorphic conormal algebras of `Y_t` in the two base changes. In the source this bound is
`c + 1` for an Artin-Rees constant `c` of the chart presentations of `Y`, and the implication is
the comparison of associated graded algebras of the two chart presentations, glued over a cover
of `Y` by affine opens. -/
def HasUniformConormalBound {S T Y : Scheme.{u}} (p : Y ⟶ T) (s : S) (t : T) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧
    ∀ sigma sigma' : T.presheaf.stalk t →+* completedStalk S s,
      (∀ a, sigma a - sigma' a ∈
        Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
          (maximalIdeal (S.presheaf.stalk s) ^ N)) →
      HasConormalIso p t (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
        (Spec.map (CommRingCat.ofHom sigma') ≫ T.fromSpecStalk t)

end Stacks.ConormalApproximation

end
