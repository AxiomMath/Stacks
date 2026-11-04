module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupChowFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct

/-!
# `[E] · θ = j_*(c_{r-1}(𝓕^∨) ∩ [E])` for the exceptional divisor (proof of Lemma 0FIH)

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`, with `X` of dimension
`n`, let `b : X' ⟶ X` be the blowing up of `X` in `Z`, with exceptional divisor `j : E ⟶ X'`, and
let `θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupTheta`). The proof of Lemma 0FIH uses

  `[E] · θ = j_*(j^!θ) = j_*(c_{r-1}(𝓕^∨) ∩ [E])`   in   `CH^r(X')`.

The first equality is Stacks 0FFE for the smooth divisor `E` of `X'`, in the codimension grading
(`Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass`); the second is
`j^!θ = c_{r-1}(𝓕^∨) ∩ [E]`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.regularImmersionGysin_blowupTheta`).

## Main results

* `codimensionIntersectionProduct_exceptional_blowupTheta`
  (namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`):
  `[E] · θ = j_*(c_{r-1}(𝓕^∨) ∩ [E])`, the right side read in codimension `1 + (r - 1)`.

## References

* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open AlgebraicGeometry.VectorBundleKZero

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- **`[E] · θ = j_*(c_{r-1}(𝓕^∨) ∩ [E])`** (proof of Lemma 0FIH). For `X` equidimensional of
dimension `n` and `α ∈ K_0(Vect(X))` restricting to `[𝒞_{Z/X}]` on `Z`, the product of the class
`[E] ∈ CH^1(X')` of the exceptional divisor with
`θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')` is the pushforward along `j : E ⟶ X'` of
`c_{r-1}(𝓕^∨) ∩ [E] ∈ CH_{(n-1)-(r-1)}(E)` (`excessChernCap`), read in `CH^{1+(r-1)}(X')`.

By Stacks 0FFE for the regular immersion `j` with `E` of dimension `n - 1`
(`Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass`), `[E] · θ` is
`j_*(j^!θ)`, and `j^!θ = c_{r-1}(𝓕^∨) ∩ [E]` (`regularImmersionGysin_blowupTheta`). -/
theorem codimensionIntersectionProduct_exceptional_blowupTheta {n : ℕ}
    (hX : RelativeDimension X.obj.hom n) (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (r : ℕ) :
    codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1)
        (blowupTheta i α r) =
      chowGroupToCodimension (blowupObj i).obj.hom (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
        (1 + ((r - 1 : ℕ) : ℤ))
        (properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
          (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
          (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ)) (properPushforwardDescends _ _ _ _ _ _)
          (excessChernCap i r ((n - 1 : ℕ) : ℤ))) := by
  have hw : (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom = (exceptionalObj i).obj.hom :=
    Over.w (exceptionalHom i).hom
  have hY : RelativeDimension ((exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom) (n - 1) := by
    have key : ∀ (q : (exceptionalObj i).obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q],
        q = (exceptionalObj i).obj.hom → RelativeDimension q (n - 1) := by
      rintro q _ rfl; exact relativeDimension_exceptionalObj i hX
    exact key _ hw
  rw [codimensionIntersectionProduct_closedSubschemeClass (blowupObj i).obj.hom
    (exceptionalHom i).hom.left (isRegularImmersion_of_isClosedImmersion (exceptionalHom i))
    (n - 1) hY 1 ((r - 1 : ℕ) : ℤ) (blowupTheta i α r)]
  exact chowGroupToCodimension_properChowPushforward_congr _ hw _ _ _ rfl _ _ _
    (regularImmersionGysin_blowupTheta i hX α hα r)

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
