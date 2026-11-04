module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelTransition

/-!
# The level identification of [Stacks, Tag 07KK] at a bare level, and its naturality square

`Crystalline.completedDifferentialsLevelEquiv` of `ModuleDifferentials/CompletionLevel.lean`
identifies the two shapes of the differentials of a `p`-adically completed divided power ring
modulo `pᵏ`, and it is indexed by `k = cmp.quotientSystem.cutoff + e`: the cutoff is carried by
the comparison `cmp` of [Stacks, Tag 07KK] and is therefore a function of the ring.  A square
relating the identification for `B` to the identification for `C` along a divided power morphism
`f : B ⟶ C` has two comparisons in it, hence two such indices, and an equation between the two
composites around the square is an equation between types that are only propositionally equal.
That is why `ModuleDifferentials/CompletionLevelTransition.lean` states the square as a pair of
computations on the spanning classes rather than as one equation of maps.

This file removes the obstruction.  `Crystalline.completedDifferentialsLevelEquivAt` is the same
identification stated at a **bare** level `k` with a proof `cmp.quotientSystem.cutoff + e = k`
supplied as an argument, so that two comparisons can be read at one and the same `k`; and
`Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt` is the
naturality square as a single equation of additive maps.

Nothing new is proved about the identification itself.  Each statement about
`...completedDifferentialsLevelEquivAt` is the corresponding statement about
`...completedDifferentialsLevelEquiv` after `subst`, and the square is the two generator
computations of `ModuleDifferentials/CompletionLevelTransition.lean` fed to
`Crystalline.completedDifferentialsModPow_ext_addMonoidHom` of
`ModuleDifferentials/CompletionLevelSpan.lean`.

## Main definitions

* `Crystalline.completedDifferentialsLevelEquivAt` — the level identification
  `Ω_{B̂/A,γ̂} / pᵏ ≃+ Ω̂_{B/A,δ} / pᵏ` at a bare level `k`.
* `Crystalline.completedDifferentialsLevelLinearEquivAt` — the same as a `B̂`-linear equivalence.

## Main results

* `Crystalline.completedDifferentialsLevelEquivAt_d` — it carries the class of `d b` to the class
  of `d b`, which pins it down on the classes that
  `Crystalline.span_completedDifferentialsModPow_mk_d_of` says span.
* `Crystalline.completedDifferentialsLevelEquivAt_smul` — it is `B̂`-linear.
* `Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt` —
  **the naturality square of the level identification, as one equation of additive maps.**  For a
  divided power morphism `f : B ⟶ C` and comparisons `cmp` for `B` and `cmp'` for `C` read at a
  common level `k`, the two composites

  `Ω_{B̂/A,γ̂} / pᵏ → Ω̂_{B/A,δ} / pᵏ → Ω̂_{C/A,ε} / pᵏ`  and
  `Ω_{B̂/A,γ̂} / pᵏ → Ω_{Ĉ/A,ε̂} / pᵏ → Ω̂_{C/A,ε} / pᵏ`

  are equal.

## Implementation notes

The re-indexing is `hk ▸ _` and not a transport written by hand: the two sides of the
identification are both applications of a function of `k`, so a single `Eq.rec` on `k` crosses
both at once and the computation lemmas come back by `subst`.  The alternative — carrying a
`cast` through every statement — makes the generator computations unusable.

The level is given as a pair `(e, k)` together with `cmp.quotientSystem.cutoff + e = k` rather
than as a bare `k` past the cutoff.  The two are interchangeable, but the pair is what a consumer
has: in the application the uniform level of [Stacks, Tag 07JN] is chosen first and the `e` of
each comparison is read off from it.

## What is and is not proved

**No tag attribute is placed, and [Stacks, Tag 07LF] is not proved here.**  What is supplied is
the first of the three steps that the "What `ε` owes" note of
`SmallSite/TensorRestrictionVanishing.lean` records as outstanding: the re-indexing that turns
the pair of generator computations of `ModuleDifferentials/CompletionLevelTransition.lean` into
the naturality square.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

universe u v w

namespace Crystalline

section Reindex

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-! ### The level identification at a bare level -/

/-- **The level identification of [Stacks, Tag 07KK] at a bare level `k`.**

`Ω_{B̂/A,γ̂} / pᵏ ≃+ Ω̂_{B/A,δ} / pᵏ`

This is `Crystalline.completedDifferentialsLevelEquiv`, whose index is
`cmp.quotientSystem.cutoff + e`, re-indexed along a proof that this is the given `k`.  The point
is that two comparisons for two different rings carry two cutoffs: stated this way they can be
read at one common level, and a square relating them becomes an equation of maps between types
that are equal, not merely propositionally equal. -/
public noncomputable def completedDifferentialsLevelEquivAt
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) :
    completedDifferentialsModPow (A := A) J delta p hp k ≃+
      completionDifferentialsModPow (A := A) J delta p k :=
  hk ▸ completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e

/-- **The identification at a bare level carries `d b` to `d b`**, for a section `b` of the
uncompleted `B`.  Those classes span modulo `pᵏ` by
`Crystalline.span_completedDifferentialsModPow_mk_d_of`, so this pins the identification. -/
public theorem completedDifferentialsLevelEquivAt_d
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) (b : B) :
    completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
        (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1
          (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b))) =
      Submodule.Quotient.mk
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) _
          (dividedPowerDifferential (A := A) delta b)) := by
  subst hk
  exact completedDifferentialsLevelEquiv_d (A := A) J delta p hp cmp e b

/-- **The identification at a bare level is linear over the completion `B̂`.** -/
public theorem completedDifferentialsLevelEquivAt_smul
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k)
    (r : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (omega : completedDifferentialsModPow (A := A) J delta p hp k) :
    completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk (r • omega) =
      r • completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk omega := by
  subst hk
  exact completedDifferentialsLevelEquiv_smul (A := A) J delta p hp cmp e r omega

/-- **The identification at a bare level, as a `B̂`-linear equivalence**: the form a tensor
product over `B̂` consumes. -/
public noncomputable def completedDifferentialsLevelLinearEquivAt
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) :
    completedDifferentialsModPow (A := A) J delta p hp k ≃ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
      completionDifferentialsModPow (A := A) J delta p k :=
  (completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk).toLinearEquiv
    (completedDifferentialsLevelEquivAt_smul (A := A) J delta p hp cmp e k hk)

/-- The `B̂`-linear form of the identification at a bare level has the same underlying
function. -/
public theorem completedDifferentialsLevelLinearEquivAt_apply
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k)
    (omega : completedDifferentialsModPow (A := A) J delta p hp k) :
    completedDifferentialsLevelLinearEquivAt (A := A) J delta p hp cmp e k hk omega =
      completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk omega :=
  rfl

end Reindex

/-! ### The naturality square -/

section Square

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable (J : Ideal B) (delta : DividedPowers J) (L : Ideal C) (epsilon : DividedPowers L)
variable (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (hq : IsNilpotent (Ideal.Quotient.mk L (p : C)))
variable (f : B →ₐ[A] C)
variable (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)

include hf

/-- **One route round the naturality square at a bare level, on a spanning class.**  The level
identification for `B` followed by the transition map of the completion of the differentials
carries the class of `d (of b)` to the class of the image of `d (f b)`. -/
public theorem completionDifferentialsModPowMap_completedDifferentialsLevelEquivAt_mk_d
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) (b : B) :
    completionDifferentialsModPowMap J delta L epsilon p f hf k
        (completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
          (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1
            (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) =
      Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (dividedPowerDifferential (A := A) epsilon (f b))) := by
  subst hk
  exact completionDifferentialsModPowMap_completedDifferentialsLevelEquiv_mk_d
    J delta L epsilon p hp f hf cmp e b

/-- **The other route round the naturality square at a bare level, on a spanning class.**  The
transition map of the universal differentials of the completion followed by the level
identification for `C` carries the class of `d (of b)` to the same class. -/
public theorem completedDifferentialsLevelEquivAt_completedDifferentialsModPowMap_mk_d
    (cmp' : DifferentialsCompletionComparison (A := A) L epsilon p hq) (e' k : ℕ)
    (hk' : cmp'.quotientSystem.cutoff + e' = k) (b : B) :
    completedDifferentialsLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk'
        (completedDifferentialsModPowMap J delta L epsilon p hp hq f hf k
          (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1
            (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) =
      Submodule.Quotient.mk (AdicCompletion.of (DividedPowers.pAdicIdeal (A := C) p) _
        (dividedPowerDifferential (A := A) epsilon (f b))) := by
  subst hk'
  exact completedDifferentialsLevelEquiv_completedDifferentialsModPowMap_mk_d
    J delta L epsilon p hp hq f hf cmp' e' b

/-- **The naturality square of the level identification of [Stacks, Tag 07KK], as one equation of
additive maps.**

For a divided power morphism `f : B ⟶ C`, a comparison `cmp` for `B` read at `e` and a comparison
`cmp'` for `C` read at `e'`, both landing at the same level `k`, the square

```
Ω_{B̂/A,γ̂} / pᵏ ──── level ────▶ Ω̂_{B/A,δ} / pᵏ
      │                                │
   transition                      transition
      ▼                                ▼
Ω_{Ĉ/A,ε̂} / pᵏ ──── level ────▶ Ω̂_{C/A,ε} / pᵏ
```

commutes.  Both composites are semilinear over the completed ring map `B̂ → Ĉ` and agree on the
classes of the differentials of the sections of the uncompleted `B`, which span by
`Crystalline.span_completedDifferentialsModPow_mk_d_of`; so
`Crystalline.completedDifferentialsModPow_ext_addMonoidHom` identifies them. -/
public theorem completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp)
    (cmp' : DifferentialsCompletionComparison (A := A) L epsilon p hq) (e e' k : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) (hk' : cmp'.quotientSystem.cutoff + e' = k) :
    (completionDifferentialsModPowMap J delta L epsilon p f hf k).toAddMonoidHom.comp
        (completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk).toAddMonoidHom =
      (completedDifferentialsLevelEquivAt (A := A) L epsilon p hq cmp' e' k
            hk').toAddMonoidHom.comp
        (completedDifferentialsModPowMap J delta L epsilon p hp hq f hf k).toAddMonoidHom := by
  refine completedDifferentialsModPow_ext_addMonoidHom J delta p hp k
    (completedAlgHom p f).toRingHom (fun r w ↦ ?_) (fun r w ↦ ?_) (fun b ↦ ?_)
  · exact Eq.trans
      (congrArg (completionDifferentialsModPowMap J delta L epsilon p f hf k)
        (completedDifferentialsLevelEquivAt_smul (A := A) J delta p hp cmp e k hk r w))
      (map_smulₛₗ (completionDifferentialsModPowMap J delta L epsilon p f hf k) r
        (completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk w))
  · exact Eq.trans
      (congrArg (completedDifferentialsLevelEquivAt (A := A) L epsilon p hq cmp' e' k hk')
        (map_smulₛₗ (completedDifferentialsModPowMap J delta L epsilon p hp hq f hf k) r w))
      (completedDifferentialsLevelEquivAt_smul (A := A) L epsilon p hq cmp' e' k hk'
        ((completedAlgHom p f).toRingHom r)
        (completedDifferentialsModPowMap J delta L epsilon p hp hq f hf k w))
  · exact Eq.trans
      (completionDifferentialsModPowMap_completedDifferentialsLevelEquivAt_mk_d
        J delta L epsilon p hp f hf cmp e k hk b)
      (completedDifferentialsLevelEquivAt_completedDifferentialsModPowMap_mk_d
        J delta L epsilon p hp hq f hf cmp' e' k hk' b).symm

end Square

end Crystalline

end
