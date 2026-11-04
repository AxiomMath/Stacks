module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.AbsoluteUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic

/-!
# The base change of the geometric Frobenius is a universal homeomorphism

Let `k` be a finite field with `q = p ^ f` elements, `X` a scheme over `k` and `K` an extension
field of `k`. The geometric Frobenius `π_X = F_X^f` of
[Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ) is a power of the absolute Frobenius, a
universal homeomorphism ([Tag 0CC8](https://stacks.math.columbia.edu/tag/0CC8)); its base change
`π̄ = π_X × id : X_K ⟶ X_K` is the base change of `π_X` along `X_K ⟶ X`, because `π_X` lies over
`Spec k`. So `π̄` is a universal homeomorphism, and by topological invariance of the étale site
([Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)) direct image along `π̄` is an exact
equivalence. This is what makes `π̄_*` exact in the comparison of the canonical Frobenius on
`Hⁱ_c(X_k̄, -)` with an operation on `Ext`, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.Frobenius.universalHomeomorphism_endPow`: powers of a universal homeomorphism.
* `Stacks.Frobenius.isPullback_geometricFrobeniusBaseChange`: `π̄` is the base change of `π_X`.
* `Stacks.Frobenius.universalHomeomorphism_geometricFrobeniusBaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Frobenius

/-- **Powers of a universal homeomorphism are universal homeomorphisms**, the composition in the
endomorphism monoid being composition of morphisms. -/
theorem universalHomeomorphism_endPow {Y : Scheme.{u}} (g : Y ⟶ Y) [UniversalHomeomorphism g]
    (n : ℕ) : UniversalHomeomorphism (End.asHom (End.of g ^ n)) := by
  induction n with
  | zero => exact universalHomeomorphism_of_isIso (𝟙 Y)
  | succ n ih =>
    rw [pow_succ]
    exact universalHomeomorphism_comp g _ inferInstance ih

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k))) (K : Type u) [Field K]
  [Algebra k K] (p : ℕ) [CharP k p] (f : ℕ) [Fact p.Prime] (hcard : Fintype.card k = p ^ f)

/-- The geometric Frobenius `π_X = F_X^f` of a scheme over a finite field is a universal
homeomorphism. -/
instance universalHomeomorphism_geometricFrobenius_left :
    UniversalHomeomorphism (geometricFrobenius X p f hcard).left :=
  universalHomeomorphism_endPow _ f

/-- **`π̄ = π_X × id` is the base change of `π_X` along `X_K ⟶ X`**: since `π_X` lies over
`Spec k`, pasting the cartesian square defining `X_K` with this square recovers that square. -/
theorem isPullback_geometricFrobeniusBaseChange :
    IsPullback (geometricFrobeniusBaseChange X K p f hcard)
      (pullback.fst X.hom (specAlgebraMap k K)) (pullback.fst X.hom (specAlgebraMap k K))
      (geometricFrobenius X p f hcard).left := by
  have hr : IsPullback (pullback.snd X.hom (specAlgebraMap k K))
      (pullback.fst X.hom (specAlgebraMap k K)) (specAlgebraMap k K) X.hom :=
    (IsPullback.of_hasPullback X.hom (specAlgebraMap k K)).flip
  refine IsPullback.of_right ?_ (geometricFrobeniusBaseChange_comp_fst X K p f hcard) hr
  rw [geometricFrobeniusBaseChange_comp_snd, Over.w (geometricFrobenius X p f hcard)]
  exact hr

/-- **The base change `π̄ = π_X × id` of the geometric Frobenius is a universal
homeomorphism.** -/
instance universalHomeomorphism_geometricFrobeniusBaseChange :
    UniversalHomeomorphism (geometricFrobeniusBaseChange X K p f hcard) :=
  Stacks.Etale.universalHomeomorphism_of_isPullback
    (isPullback_geometricFrobeniusBaseChange X K p f hcard)

end Stacks.Frobenius

end
