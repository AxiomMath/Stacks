module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchZeroSectionPushforward

/-!
# Clause (5) of Stacks 0F96 at a branch, as a carrier on an ambient scheme

`Stacks.Chow.TensorZeroScheme.rationallyEquivalent_properPushforward_zeroSection_branchSituation`
states clause (5) of [Stacks, Tag 0F96] at the branch line bundle `branchSituation Y L₁ L₂ s N`
of [Stacks, Tag 0F97](4), at the level of cycles and in the orientation [Stacks, Tag 0F98] uses:
the pushforward along the zero section of `α` is rationally equivalent to any cycle representing
`p^*(c₁(N|_D) ∩ α)`, with no sign.

A dévissage over integral closed subschemes cannot consume a rational equivalence on the total
space of the branch. The comparison principle it runs on,
`Stacks.Chow.GradedIntegralComponentRule.extendChow_congr`, asks for a cycle on the *ambient*
scheme — in the case `W ⊆ D` of [Stacks, Tag 0F98] the ambient scheme is the branch `D₁` of the
unrestricted diagram — that is rationally equivalent to zero *within* a prescribed carrier. This
file supplies that shape: along a closed immersion `j` out of the total space of the branch, the
pushforwards of the two cycles differ by a cycle rationally equivalent to zero within the image
of `j`.

The carrier cannot be read off the class identity of the clause, which has forgotten where its
witnesses are; it is produced by the immersion. Widening it to the carrier a dévissage prescribes
is `Stacks.Chow.IsRationallyEquivalentToZeroWithin.mono`, and the result then combines with the
siblings of `StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ContainedComponentComparison` by
`Stacks.Chow.isRationallyEquivalentToZeroWithin_add`.

## Main results

* `isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation`
  — **clause (5) of [Stacks, Tag 0F96] at a branch, as a carrier on an ambient scheme.**
* `isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι`
  — the same at a branch of the diagram base-changed along a closed subscheme `W ⊆ Y`, with the
  carrier the preimage of `W`, which is the carrier the dévissage prescribes.

## Implementation notes

### Why the base change needs no transport

Over a closed subscheme `W ⊆ D` the restricted section is zero, so the divisor of the
base-changed diagram is all of `W`
(`Stacks.Chow.TensorZeroScheme.zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`). It is
tempting to rewrite along that equation and present the branch as a line bundle over `W` itself.
That equation is between concrete ideal sheaves, and an `Eq.rec` at it would put a line-bundle
situation — data, not a proposition — under a `cast`, which this repository cannot reduce.

So nothing is rewritten. The base of the branch stays spelled as the zero scheme of the restricted
section throughout, and the base-changed statement below is the arbitrary-branch statement above
*instantiated* at the restricted data `W.subscheme`, `L₁|_W`, `L₂|_W`, `s|_W` — the branch
construction being parametric in them, instantiation costs nothing. A consumer that needs to see
`W` in place of that zero scheme has it as an isomorphism rather than an equation: condition (6)
of [Stacks, Tag 0F97], recorded as the field
`Stacks.Chow.TensorZeroScheme.Decomposition.intersection_isIso`, or
`AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot`, which turns the equation into an `IsIso`
without eliminating it into a type — the route
`Stacks.Chow.TensorZeroScheme.isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le` already
takes.

### How `W` enters at all

Only through the carrier. The conclusion is widened from the image of `j` to the preimage of `W`
along a morphism `g : A ⟶ Y` of the ambient scheme, and the hypothesis that makes that legitimate
is a morphism `q` witnessing that `j` lies over `W` — a commuting square, supplied by the
consumer, not an equality transported by this file.

### Why this file sits under `AffineBundle`

It is the branch analogue of
`Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_zeroSection` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionPushforwardCycle`, and is the first of
the three steps that read clause (5) into the shape the case `W ⊆ D` of [Stacks, Tag 0F98]
consumes. The declaration lives in the `Stacks.Chow.TensorZeroScheme` namespace, where
`branchSituation` lives.

### No `@[stacks]` attribute here

This is clause (5) of Tag 0F96 pushed along an immersion, not a new assertion of it: the clause is
carried by `Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow`.
Nor does anything here assert [Stacks, Tag 0F98], which is a single identity of maps and is
carried by `Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchChowIdentity`; see the
convention note in `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

/-! ### The carrier form at an arbitrary branch -/

section Carrier

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (N : Y.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
  (sD : (branchSituation Y L₁ L₂ s N).X ⟶ C.S) [LocallyOfFiniteType sD]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (branchSituation Y L₁ L₂ s N).X.sheaf.obj
    (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
    ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)]

include h₁ h₂ hN in
/-- **Clause (5) of [Stacks, Tag 0F96] at a branch of [Stacks, Tag 0F97], as a carrier on an
ambient scheme.** Let `α ∈ Z_{k+1}(D)` be a cycle on the base of the branch line bundle
`branchSituation Y L₁ L₂ s N`, let `γ` be any cycle on its total space representing the class
`p^*(c₁(N|_D) ∩ α)`, and let `j : W₁ ⟶ A` be a closed immersion of that total space into a scheme
over the base situation. Then the pushforwards along `j` of the pushforward of `α` along the zero
section and of `γ` differ by a cycle rationally equivalent to zero on `A` within the image of `j`
— with no sign, the inversion in `branchSituation` having cancelled the one of the clause.

This is `Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin` at the rational
equivalence
`Stacks.Chow.TensorZeroScheme.rationallyEquivalent_properPushforward_zeroSection_branchSituation`.
The carrier is what a dévissage over integral closed subschemes needs and what the class identity
of the clause does not retain: it is produced here by the immersion, not by the clause. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1))
    (γ : Stacks.Chow.CycleGroup C
      ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) (k + 1))
    (hγ : QuotientAddGroup.mk' (Stacks.Chow.rationalEquivalences C
        ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) (k + 1)) γ =
      Stacks.Chow.chowGroupCast C ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (Stacks.Chow.flatPullbackChowOfRelativeDimension C
          ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sD
          (branchSituation Y L₁ L₂ s N).totalSpaceToBase rfl 1
          (branchSituation Y L₁ L₂ s N).relativeDimension_totalSpaceToBase k
          (Stacks.Chow.firstChernClassCapOfInvertible C sD k
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) α)))
    {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (j : (branchSituation Y L₁ L₂ s N).totalSpace ⟶ A) [IsClosedImmersion j]
    (hj : j ≫ sA = (branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C sA (k + 1)
      (Stacks.Chow.properPushforward C
          ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sA j hj (k + 1)
          (Stacks.Chow.properPushforward C sD
            ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD)
            (branchSituation Y L₁ L₂ s N).zeroSection
            (Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp C
              (branchSituation Y L₁ L₂ s N) sD) (k + 1) α) -
        Stacks.Chow.properPushforward C
          ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sA j hj (k + 1) γ)
      (Set.range j.base) :=
  Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin C
    ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sA j hj (k + 1)
    (rationallyEquivalent_properPushforward_zeroSection_branchSituation C Y L₁ L₂ s N sD k α γ hγ)

end Carrier

/-! ### The carrier form at a branch of the base-changed diagram -/

section BaseChange

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (W : Y.IdealSheafData)
  (N : W.subscheme.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
    W.subscheme.ringCatSheaf.property N]
  (C : Stacks.Chow.ChowSituation.{u})
  (sD : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X ⟶ C.S) [LocallyOfFiniteType sD]
  [AlgebraicGeometry.SheafOfModules.IsInvertible
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X.sheaf.obj
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X.ringCatSheaf.property
    ((Scheme.Modules.pullback (zeroIdeal W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj N)]

include h₁ h₂ hN in
/-- **Clause (5) of [Stacks, Tag 0F96] at a branch of the base-changed diagram, with the carrier
the preimage of `W`.** Let `W ⊆ Y` be a closed subscheme, so that the diagram of
[Stacks, Tag 0F97] base-changes along `W ↪ Y` and the branch over `W` is the line bundle
`branchSituation W.subscheme L₁|_W L₂|_W s|_W N`; at `N = L₂|_W` this is the bundle `W₁ → W` of
the case `W ⊆ D` of [Stacks, Tag 0F98]. Let `α` be a cycle on its base, `γ` any cycle on its
total space representing `p^*(c₁(N|_{D'}) ∩ α)`, and `j` a closed immersion of that total space
into a scheme `A` carrying a morphism `g : A ⟶ Y` over which `j` lies above `W`. Then the
pushforwards along `j` of the pushforward of `α` along the zero section and of `γ` differ by a
cycle rationally equivalent to zero on `A` within the preimage of `W` along `g`.

That preimage is the carrier the dévissage of [Stacks, Tag 0F98] prescribes — at
`A = D₁.subscheme` and `g = i₁ ≫ p` it is the carrier of
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj_of_primeCycle`, and at
`A = D.subscheme` and `g = i` the carrier of
`Stacks.Chow.gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le`
— so the comparisons may be summed with
`Stacks.Chow.isRationallyEquivalentToZeroWithin_add`.

This is `isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation` at
the restricted data, widened by `Stacks.Chow.IsRationallyEquivalentToZeroWithin.mono`: the image
of `j` lies in the preimage of `W` because `q` witnesses that `j` lies over `W`, and the image of
`W ↪ Y` is the support of `W`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι
    (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1))
    (γ : Stacks.Chow.CycleGroup C
      ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD) (k + 1))
    (hγ : QuotientAddGroup.mk' (Stacks.Chow.rationalEquivalences C
        ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD) (k + 1)) γ =
      Stacks.Chow.chowGroupCast C
        ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (Stacks.Chow.flatPullbackChowOfRelativeDimension C
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD) sD
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase rfl 1
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s) N).relativeDimension_totalSpaceToBase k
          (Stacks.Chow.firstChernClassCapOfInvertible C sD k
            ((Scheme.Modules.pullback (zeroIdeal W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj N) α)))
    {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (j : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace ⟶ A) [IsClosedImmersion j]
    (hj : j ≫ sA =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD)
    (g : A ⟶ Y)
    (q : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace ⟶ W.subscheme)
    (hq : j ≫ g = q ≫ W.subschemeι) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C sA (k + 1)
      (Stacks.Chow.properPushforward C
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD)
          sA j hj (k + 1)
          (Stacks.Chow.properPushforward C sD
            ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD)
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s) N).zeroSection
            (Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp C
              (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s) N) sD) (k + 1) α) -
        Stacks.Chow.properPushforward C
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD)
          sA j hj (k + 1) γ)
      (g.base ⁻¹' (W.support : Set Y)) := by
  refine (isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation C
    W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s) N sD k α γ hγ sA j hj).mono ?_
  rintro y ⟨x, rfl⟩
  have hbase : (j ≫ g).base x = (q ≫ W.subschemeι).base x := by rw [hq]
  rw [Set.mem_preimage, show g.base (j.base x) = (j ≫ g).base x from rfl, hbase,
    ← W.range_subschemeι]
  exact ⟨q.base x, rfl⟩

end BaseChange

end Stacks.Chow.TensorZeroScheme

end
