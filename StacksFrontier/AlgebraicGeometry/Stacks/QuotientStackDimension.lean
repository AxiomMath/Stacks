module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering

/-!
# The dimension of a quotient stack, and the negative dimension of a classifying stack

Let `X` be of finite type over a field `k` and let `G` be a group of finite type over `k` acting
on `X`. Stacks 0AFR computes `dim [X/G] = dim(X) - dim(G)`; in particular
`dim BG = dim [Spec k/G] = -dim(G)`, so the dimension of an algebraic stack can be a negative
integer, unlike that of a scheme.

## Main results

* `AlgebraicGeometry.Stack.dimension_le_dimensionSubNat_of_chart`: one smooth, locally of finite
  type 1-morphism `T ⟶ 𝒳` from an algebraic space, surjective on points and of relative
  dimension `d` at every point, bounds `dim(𝒳)` above by `dim(T) - d`.
* `AlgebraicGeometry.Stack.dimension_quotientStack_le`: **Stacks 0AFR**, the upper bound
  `dim [X/G] ≤ dim(X) - dim(G)`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_le`: **Stacks 0AFR**, the upper bound
  `dim BG ≤ -dim(G)` for the classifying stack `BG = [Spec k/G]`.
* `AlgebraicGeometry.Stack.dimension_classifyingStack_lt_zero`: **Stacks 0AFR**, that the
  dimension of an algebraic stack can be a negative integer: `dim BG < 0` as soon as
  `dim(G) > 0`.

## Implementation notes

Only the upper bound of Stacks 0AFR is proved. `AlgebraicGeometry.Stack.dimensionAtPoint` is an
infimum over the admissible smooth charts of Stacks 0AFN, so one chart bounds it from *above*
(`AlgebraicGeometry.Stack.dimensionAtPoint_le`); the matching lower bound is the independence of
the chart, which is Stacks 0AFM and is not in the library. The negative-dimension assertion of
Stacks 0AFR runs the favourable way for an infimum and is therefore delivered in full.

Three further inputs are carried as hypotheses rather than proved.

*Algebraicity of the quotient.* `AlgebraicGeometry.Stack.dimension` is defined on
`AlgebraicGeometry.Stack.AlgebraicStacks`, whose objects have their morphisms one universe below
those of `AlgebraicGeometry.Stack.quotientStack`. So the statements quantify over an algebraic
stack `𝒬` together with an equivalence over the site between `𝒬` and the quotient stack of the
action groupoid of Stacks 0444. That the quotient *is* an algebraic stack is Stacks 04WZ and
Stacks 04TB, which the library does not have; the equivalence hypothesis is how `𝒬` is pinned
down to be `[X/G]` in their absence. It takes no part in the proofs, exactly as the local
Noetherianity hypothesis of `AlgebraicGeometry.Stack.dimensionAtPoint` takes none in its body.

*The tautological chart.* The chart of `[X/G]` the source computes with is `X ⟶ [X/G]`, which is
smooth and surjective with fibres the `G`-orbits, hence of relative dimension `dim(G)` at every
point. Its construction belongs to the theory of the quotient stack rather than to the theory of
dimension, so it is a hypothesis: a 1-morphism `f` out of `X` which is smooth, locally of finite
type, surjective on points and of relative dimension `dG` everywhere, together with the equation
`dim(G) = dG` that makes the conclusion read `dim(X) - dim(G)`.

*The dimension of the base.* That `Spec k` has dimension `0` as an algebraic space is the
hypothesis `hk0` of the two classifying-stack statements.

The finite type hypotheses of the source do not appear: everything they are used for — the
smoothness and the constant relative dimension of the tautological chart, and the finiteness of
`dim(G)` — is among the hypotheses above. The quotient `[X/G]` is formed over a general base
algebraic space `A`, the source's case being `A = Spec k`; the classifying stack is
`AlgebraicGeometry.Stack.classifyingStack`, which is over a field by construction.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack

universe u w

/-- Subtracting a fixed relative dimension from the dimension of an algebraic space is monotone
in that dimension. -/
theorem dimensionSubNat_mono (d : ℕ) {δ δ' : WithBot ℕ∞} (h : δ ≤ δ') :
    dimensionSubNat δ d ≤ dimensionSubNat δ' d := by
  induction δ' using WithBot.recBotCoe with
  | bot => rw [le_bot_iff.mp h]
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) = (⊤ : WithBot ℕ∞) from rfl, dimensionSubNat_top]
      exact le_top
    | coe n =>
      induction δ using WithBot.recBotCoe with
      | bot => rw [dimensionSubNat_bot]; exact bot_le
      | coe a =>
        induction a using ENat.recTopCoe with
        | top =>
          exact absurd (top_le_iff.mp (WithBot.coe_le_coe.mp h)) (ENat.natCast_ne_top n)
        | coe m =>
          have hL : dimensionSubNat ((m : ℕ∞) : WithBot ℕ∞) d =
            (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
          have hR : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) d =
            (((n : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
          have hmn : m ≤ n := by exact_mod_cast h
          rw [hL, hR, WithBotTop.coe_le_coe]
          omega

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- One smooth, locally of finite type chart `T ⟶ 𝒳` from an algebraic space which is surjective
on points and has relative dimension `d` at every point bounds the dimension of `𝒳` above by
`dim(T) - d`. -/
theorem dimension_le_dimensionSubNat_of_chart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property, ∃ t : Space.points B S hS T,
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : ∀ t : Space.points B S hS T,
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimension B S hS 𝒳 h𝒳 ≤ dimensionSubNat (Space.dimension B S hS T hT) d := by
  refine iSup_le fun x => ?_
  obtain ⟨t, ht⟩ := hsurj x
  exact (dimensionAtPoint_le B S hS 𝒳 h𝒳 x T hT f hsm hf t ht d (hd t)).trans
    (dimensionSubNat_mono d (le_iSup (fun s => Space.dimensionAtPoint B S hS T hT s) t))

/-! ### Stacks 0AFR: the dimension of `[X/G]` -/

/-- **Stacks 0AFR**, the upper bound. Let `G` act on `X` over the base algebraic space `A`, let
`𝒬` be an algebraic stack equivalent over the site to the quotient stack `[X/G]`, and let
`f : X ⟶ 𝒬` be the tautological chart, of relative dimension `dim(G)` at every point. Then
`dim [X/G] ≤ dim(X) - dim(G)`. -/
@[stacks 0AFR "upper bound `dim [X/G] ≤ dim X - dim G`, carrying the algebraicity of the \
quotient (Stacks 04WZ and 04TB) and the tautological chart `X ⟶ [X/G]` as hypotheses; the \
matching lower bound needs the independence of the chart, Stacks 0AFM"]
theorem dimension_quotientStack_le (A : AlgebraicSpaces B S hS) (G X : Over A.obj)
    [GrpObj G] [ModObj G X] (hG : IsAlgebraicSpace B S hS G.left)
    (hX : IsAlgebraicSpace B S hS X.left) (𝒬 : AlgebraicStacks.{u, w} B S hS)
    (_h𝒬 : Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p
      (quotientStack (Space.groupoidOfAction A G X hG hX).groupoid).p))
    (hN : IsLocallyNoetherianStack.{u, w} B S hS 𝒬)
    (f : algebraicSpaceStack.{u, w} B S hS X.left hX ⟶ 𝒬)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : ∀ x : points B S hS 𝒬.val.val 𝒬.val.property,
      ∃ t : Space.points B S hS X.left,
        pointsMap B S hS (fibredCategory B S hS X.left).val
          (fibredCategory B S hS X.left).property 𝒬.val.property f.hom.hom
          (stackPointOfSpacePoint B S hS X.left t) = x)
    (dG : ℕ) (hdG : ∀ t : Space.points B S hS X.left,
      relativeDimensionAt.{u, w} B S hS X.left hX 𝒬 f hf t = (dG : WithBot ℕ∞))
    (hGdim : Space.dimension B S hS G.left hG = (dG : WithBot ℕ∞)) :
    ∃ m : ℕ, Space.dimension B S hS G.left hG = (m : WithBot ℕ∞) ∧
      dimension B S hS 𝒬 hN ≤ dimensionSubNat (Space.dimension B S hS X.left hX) m :=
  ⟨dG, hGdim, dimension_le_dimensionSubNat_of_chart.{u, w} B S hS 𝒬 hN X.left hX f hsm hf
    hsurj dG hdG⟩

/-! ### Stacks 0AFR: the negative dimension of `BG` -/

section Classifying

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
  (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)
  (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)

/-- **Stacks 0AFR**, the upper bound for the classifying stack `BG = [Spec k/G]` of a group `G`
over a field `k`, whose tautological chart is `Spec k ⟶ BG`: `dim BG ≤ -dim(G)`. -/
@[stacks 0AFR "upper bound `dim BG ≤ -dim G` for the classifying stack, carrying the \
algebraicity of `BG` (Stacks 04WZ and 04TB), the tautological chart `Spec k ⟶ BG` and \
`dim (Spec k) = 0` as hypotheses; the matching lower bound needs Stacks 0AFM"]
theorem dimension_classifyingStack_le
    (_h𝒬 : Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p
      (classifyingStack C hk G).val.p))
    (hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬)
    (f : algebraicSpaceStack.{u, w} C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property ⟶ 𝒬)
    (hsm : AlgebraicStacks.IsSmooth C (Spec (.of k)) hk f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk f)
    (hsurj : ∀ x : points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property,
      ∃ t : Space.points C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj,
        pointsMap C (Spec (.of k)) hk
          (fibredCategory C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj).val
          (fibredCategory C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj).property 𝒬.val.property f.hom.hom
          (stackPointOfSpacePoint C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj t) = x)
    (dG : ℕ) (hdG : ∀ t : Space.points C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj,
      relativeDimensionAt.{u, w} C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj
        (Space.terminalSpace C (Spec (.of k)) hk).property 𝒬 f hf t = (dG : WithBot ℕ∞))
    (hGdim : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      (dG : WithBot ℕ∞))
    (hk0 : Space.dimension C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property = ((0 : ℕ) : WithBot ℕ∞)) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      (m : WithBot ℕ∞) ∧ dimension C (Spec (.of k)) hk 𝒬 hN ≤ ((-(m : ℤ) : ℤ) : EInt) := by
  refine ⟨dG, hGdim, le_trans (dimension_le_dimensionSubNat_of_chart.{u, w} C (Spec (.of k)) hk
    𝒬 hN (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property f hsm hf hsurj dG hdG) ?_⟩
  have hz : dimensionSubNat ((0 : ℕ) : WithBot ℕ∞) dG =
    (((0 : ℤ) - (dG : ℤ) : ℤ) : EInt) := rfl
  rw [hk0, hz, WithBotTop.coe_le_coe]
  omega

/-- **Stacks 0AFR.** The dimension of an algebraic stack can be a negative integer: the
classifying stack of a group of positive dimension over a field has negative dimension. -/
@[stacks 0AFR "the dimension of an algebraic stack can be a negative integer, carrying the \
algebraicity of `BG` (Stacks 04WZ and 04TB), the tautological chart `Spec k ⟶ BG` and \
`dim (Spec k) = 0` as hypotheses"]
theorem dimension_classifyingStack_lt_zero
    (_h𝒬 : Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p
      (classifyingStack C hk G).val.p))
    (hN : IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒬)
    (f : algebraicSpaceStack.{u, w} C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property ⟶ 𝒬)
    (hsm : AlgebraicStacks.IsSmooth C (Spec (.of k)) hk f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk f)
    (hsurj : ∀ x : points C (Spec (.of k)) hk 𝒬.val.val 𝒬.val.property,
      ∃ t : Space.points C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj,
        pointsMap C (Spec (.of k)) hk
          (fibredCategory C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj).val
          (fibredCategory C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj).property 𝒬.val.property f.hom.hom
          (stackPointOfSpacePoint C (Spec (.of k)) hk
            (Space.terminalSpace C (Spec (.of k)) hk).obj t) = x)
    (dG : ℕ) (hdG : ∀ t : Space.points C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj,
      relativeDimensionAt.{u, w} C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk).obj
        (Space.terminalSpace C (Spec (.of k)) hk).property 𝒬 f hf t = (dG : WithBot ℕ∞))
    (_hGdim : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      (dG : WithBot ℕ∞))
    (hk0 : Space.dimension C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property = ((0 : ℕ) : WithBot ℕ∞))
    (hpos : 0 < dG) :
    dimension C (Spec (.of k)) hk 𝒬 hN < 0 := by
  obtain ⟨m, hm, hle⟩ := dimension_classifyingStack_le.{u, w} C hk G 𝒬 _h𝒬 hN f hsm hf hsurj dG
    hdG _hGdim hk0
  obtain rfl : m = dG := by exact_mod_cast hm.symm.trans _hGdim
  refine lt_of_le_of_lt hle ?_
  rw [show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe]
  omega

end Classifying

end AlgebraicGeometry.Stack

end
