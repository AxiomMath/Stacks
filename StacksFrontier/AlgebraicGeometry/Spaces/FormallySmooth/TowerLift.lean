module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs

/-!
# Lifting a compatible family of sections along a tower of square-zero thickenings

A formally étale transformation `a : F ⟶ G` lifts a section of `G` uniquely across a single
square-zero closed immersion of affines. Along a tower `T 0 ⟶ T 1 ⟶ T 2 ⟶ ⋯` of such
immersions the unique lifts therefore assemble, by induction, into a compatible family: a
compatible family of sections of `G` over the tower, together with one lift at the initial
stage, determines lifts at every stage which are compatible with the tower.

The tower of truncations `Spec (R ⧸ 𝔪ⁿ) ↪ Spec (R ⧸ 𝔪ⁿ⁺¹)` of a local ring is the case this
is intended for, with `a` an étale atlas of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_compatible_lifts_of_formallyEtale`: the compatible family of
  lifts along the tower.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04GC](https://stacks.math.columbia.edu/tag/04GC)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A formally étale transformation lifts a compatible family of sections along a tower of
square-zero thickenings of affines.** Given a compatible family `x n` of sections of `G` over
a tower `T 0 ⟶ T 1 ⟶ ⋯` of square-zero closed immersions of affine objects, and a lift `z₀`
of `x 0` to `F`, there are lifts `z n` of `x n` which are compatible with the tower and extend
`z₀`.

At each step the lift is the unique one supplied by formal étaleness, so the family is in fact
determined by `z₀`. -/
theorem exists_compatible_lifts_of_formallyEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (ha : FormallyEtale a)
    (T : ℕ → BigFppfOver B S hS) (i : ∀ n, T n ⟶ T (n + 1))
    (hAff : ∀ n, IsAffine ((BigFppfOver.toScheme B S hS).obj (T n)))
    (hSq : ∀ n, IsSquareZeroClosedImmersion B S hS (i n))
    (x : ∀ n, G.obj (op (T n)))
    (hx : ∀ n, G.map (i n).op (x (n + 1)) = x n)
    (z₀ : F.obj (op (T 0))) (hz₀ : a.app (op (T 0)) z₀ = x 0) :
    ∃ z : ∀ n, F.obj (op (T n)),
      z 0 = z₀ ∧ (∀ n, F.map (i n).op (z (n + 1)) = z n) ∧
        (∀ n, a.app (op (T n)) (z n) = x n) := by
  classical
  -- the unique lift across the `n`-th step of any lift of `x n`
  have step : ∀ (n : ℕ) (w : {z : F.obj (op (T n)) // a.app (op (T n)) z = x n}),
      ∃ z : {z : F.obj (op (T (n + 1))) // a.app (op (T (n + 1))) z = x (n + 1)},
        F.map (i n).op z.1 = w.1 := fun n w => by
    obtain ⟨z, hz, hza⟩ := (ha (T n) (T (n + 1)) (hAff n) (hAff (n + 1)) (i n) (hSq n)
      w.1 (x (n + 1)) (by rw [w.2, ← hx n])).exists
    exact ⟨⟨z, hza⟩, hz⟩
  choose liftNext hlift using step
  let liftData : ∀ n, {z : F.obj (op (T n)) // a.app (op (T n)) z = x n} :=
    Nat.rec ⟨z₀, hz₀⟩ liftNext
  exact ⟨fun n => (liftData n).1, rfl, fun n => hlift n (liftData n), fun n => (liftData n).2⟩

end AlgebraicGeometry.Space

end
