module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupGysinFundamental
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExceptionalProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcessDegree

/-!
# The two relations of Lemma 0FIH

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`, `X` of dimension `n`
and `Z` of dimension `e`, of codimension `r = n - e ≥ 1`, and let `α ∈ K_0(Vect(X))` restrict to
the class of `𝒞_{Z/X}`. Let `b : X' ⟶ X` be the blowing up in `Z`, `j : E ⟶ X'` the exceptional
divisor, `π : E ⟶ Z`, and `θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupTheta`). Then

  `b^![Z] = [E] · θ`   in `CH^r(X')`   and   `π_*(j^!θ) = [Z]`   in `CH_e(Z)`.

Both sides of the first relation are `j_*(c_{r-1}(𝓕^∨) ∩ [E])`: the left by the blow up formula
(Tag 0FVA, `codimensionGysin_blowupHom_closedSubschemeClass`), the right by Tag 0FFE and
`j^!θ = c_{r-1}(𝓕^∨) ∩ [E]` (`codimensionIntersectionProduct_exceptional_blowupTheta`). The second
is `j^!θ = c_{r-1}(𝓕^∨) ∩ [E]` (`regularImmersionGysin_blowupTheta`) and the degree computation
`π_*(c_{r-1}(𝓕^∨) ∩ [E]) = [Z]` (`properChowPushforward_excessChernCap`).

## Main results

In namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`:

* `codimensionGysin_closedSubschemeClass_heq_blowupTheta`: `b^![Z] = [E] · θ`.
* `properChowPushforward_regularImmersionGysin_blowupTheta`: `π_*(j^!θ) = [Z]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

variable {n e r : ℕ} (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e)
  (hr : e + r = n) (hr0 : 0 < r) (α : VectorBundleKZero X.obj.left)
  (hα : VectorBundleKZero.pullback i.hom.left α =
    VectorBundleKZero.classOf _ (centreConormal i))

include hX hZ hr hr0 hα in
/-- **The first relation of Lemma 0FIH: `b^![Z] = [E] · θ`**, the two sides lying in `CH^r(X')`
and `CH^{1+(r-1)}(X')`. -/
theorem codimensionGysin_closedSubschemeClass_heq_blowupTheta :
    codimensionGysin (blowupObj i).obj.hom X.obj.hom (Over.w (blowupHom i).hom) (r : ℤ)
        (closedSubschemeClass X.obj.hom i.hom.left (r : ℤ)) ≍
      codimensionIntersectionProduct k (blowupObj i).obj.hom 1 ((r - 1 : ℕ) : ℤ)
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1)
        (blowupTheta i α r) := by
  rw [codimensionGysin_blowupHom_closedSubschemeClass i hX hZ hr hr0,
    codimensionIntersectionProduct_exceptional_blowupTheta i hX α hα r]
  have key : ∀ (c c' : ℤ), c = c' → ∀ x,
      chowGroupToCodimension (blowupObj i).obj.hom (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ)) c x ≍
        chowGroupToCodimension (blowupObj i).obj.hom (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ)) c'
          x := by
    rintro c _ rfl x
    rfl
  exact key _ _ (by omega) _

include hX hZ hr hr0 hα in
/-- **The second relation of Lemma 0FIH: `π_*(j^!θ) = [Z]`** in `CH_e(Z)`, `j^!θ` lying in
`CH_{(n-1)-(r-1)}(E)` for `j ≫ (X' ⟶ Spec k)`. -/
theorem properChowPushforward_regularImmersionGysin_blowupTheta :
    properChowPushforward (fieldChowSituation k)
        ((exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom) Z.obj.hom
        (exceptionalProj i).hom.left
        (by rw [Over.w (exceptionalHom i).hom, Over.w (exceptionalProj i).hom])
        (((n - 1 : ℕ) : ℤ) - ((r - 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (regularImmersionGysin (blowupObj i).obj.hom (exceptionalHom i).hom.left
          (isRegularImmersion_of_isClosedImmersion (exceptionalHom i)) (n - 1) ((r - 1 : ℕ) : ℤ)
          (blowupTheta i α r)) ≍
      fundamentalChowClass (fieldChowSituation k) Z.obj.hom e := by
  have h2 := properChowPushforward_excessChernCap i hX hZ (show e < n by omega)
  have hrn : r = n - e := by omega
  subst hrn
  have h3 := regularImmersionGysin_blowupTheta i hX α hα (n - e)
  refine HEq.trans ?_ (heq_of_eq h2)
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q]
      (hq : q = (exceptionalObj i).obj.hom) (m m' : ℤ) (hm : m = m')
      (x : chowGroup (fieldChowSituation k) q m)
      (x' : chowGroup (fieldChowSituation k) (exceptionalObj i).obj.hom m') (hx : x ≍ x')
      (hπ : (exceptionalProj i).hom.left ≫ Z.obj.hom = q) hd hd',
      properChowPushforward (fieldChowSituation k) q Z.obj.hom (exceptionalProj i).hom.left hπ m hd
          x ≍
        properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
          (exceptionalProj i).hom.left rfl m' hd' x' := by
    rintro q _ rfl m _ rfl x x' hx hπ hd hd'
    cases hx
    rfl
  refine key _ (Over.w (exceptionalHom i).hom) _ _ (by omega) _ _ ?_ _ _ _
  have hcap : ∀ m m' : ℤ, m = m' → excessChernCap i (n - e) m ≍ excessChernCap i (n - e) m' := by
    rintro m _ rfl
    rfl
  exact (h3.trans (hcap _ _ (by omega))).trans (chowGroupCast_heq _ _ _ _).symm

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
