module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula

/-!
# Proper pushforward along a projective bundle is surjective on Chow groups

Let `(S, δ)` be a base situation of chapter 42, `X` locally of finite type over `S`, `ℰ` a
finite locally free `𝒪_X`-module of constant rank `n + 1` and `π : 𝐏(ℰ) ⟶ X` its projective
bundle. Then `π_* : A_k(𝐏(ℰ)) ⟶ A_k(X)` is surjective in every degree `k`: by the top-power case
of Stacks 02TW (`Stacks.Chow.projectiveBundle_projection_self`), every `α ∈ A_k(X)` is
`π_*(c₁(𝒪_P(1))^n ∩ π^*α)`.

The pushforward is the genuine one, `Stacks.Chow.properChowPushforward` with its descent through
rational equivalence supplied by Stacks 02S2
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`); nothing is
carried. The rank must be positive: the bundle of a module of rank zero is empty.

This is a step of the proof of Stacks 0FIQ ("every cycle on `X × G(l, n)` is the pushforward of
a cycle on `Y`"), and is not itself a tagged statement.

## Main results

* `Stacks.Chow.properChowPushforward_bundleProj_capPow_bundlePullback_self` — the explicit
  preimage `c₁(𝒪_P(1))^n ∩ π^*α`.
* `Stacks.Chow.properChowPushforward_bundleProj_surjective` — surjectivity.
* `Stacks.Chow.properChowPushforward_comp_surjective` — surjectivity of proper pushforward is
  stable under composition (Stacks 02R5).

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (n : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1))
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

include hE

/-- **Every class on `X` is the pushforward of an explicit class on `𝐏(ℰ)`**: for `ℰ` of rank
`n + 1` and `α ∈ A_k(X)`, `π_*(c₁(𝒪_P(1))^n ∩ π^*α) = α`, Stacks 02TW, read as a statement
about the genuine proper pushforward `π_* : A_k(𝐏(ℰ)) ⟶ A_k(X)`. -/
theorem properChowPushforward_bundleProj_capPow_bundlePullback_self (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := hE
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    properChowPushforward C (bundleProj E ≫ sX) sX (bundleProj E) rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (bundleProj E ≫ sX) sX
          (bundleProj E) rfl k)
        (capPow C (bundleProj E ≫ sX) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) n (k + n) k
          (by ring)
          (bundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl n
            (relativeDimension_bundleProj E n) k α)) = α :=
  have := hE
  projectiveBundle_projection_self E n C sX k α

/-- **Proper pushforward along a projective bundle is surjective on Chow groups.** For a finite
locally free module `ℰ` of constant rank `n + 1` on `X`, and any structure morphism `sP` of
`𝐏(ℰ)` over the base lying over that of `X`, `π_* : A_k(𝐏(ℰ)) ⟶ A_k(X)` is surjective for every
`k`. -/
theorem properChowPushforward_bundleProj_surjective (sP : bundle E ⟶ C.S)
    [LocallyOfFiniteType sP] (hsP : bundleProj E ≫ sX = sP) (k : ℤ) :
    Function.Surjective (properChowPushforward C sP sX (bundleProj E) hsP k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX (bundleProj E)
        hsP k)) := by
  subst hsP
  intro α
  exact ⟨_, properChowPushforward_bundleProj_capPow_bundlePullback_self E n hE C sX k α⟩

omit hE in
/-- **Surjectivity of proper pushforward composes**: if `f_*` and `g_*` are surjective on Chow
groups in degree `k`, so is `(f ≫ g)_*` (Stacks 02R5, `Stacks.Chow.properChowPushforward_comp`). -/
theorem properChowPushforward_comp_surjective {Y Z : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z) [IsProper g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ)
    (h₁ : Function.Surjective (properChowPushforward C sX sY f hf k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY f hf k)))
    (h₂ : Function.Surjective (properChowPushforward C sY sZ g hg k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sZ g hg k))) :
    Function.Surjective (properChowPushforward C sX sZ (f ≫ g)
      (by rw [Category.assoc, hg, hf]) k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sZ (f ≫ g)
        (by rw [Category.assoc, hg, hf]) k)) := by
  have h := h₂.comp h₁
  rwa [← AddMonoidHom.coe_comp, properChowPushforward_comp C sX sY sZ f g hf hg k] at h

end Stacks.Chow

end
