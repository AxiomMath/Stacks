module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Connected
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorSmoothOnX
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.StalkDepthTwo

/-!
# The divisor of a member of the vanishing system is geometrically irreducible

`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair` produces, for the
Bertini step of [Stacks, Tag 0FH7], a nonzero `w ∈ V_n` whose divisor `H_w ⊆ X` is smooth over
`k`. The induction on `dim X` that step feeds has to treat `H_w` as a variety in its own right,
and for that it needs `H_w` to be *geometrically irreducible*. This file supplies that, by the
classical route: `H_w` is connected because `ℒ ^⊗ n` is ample ([Stacks, Tag 0FD9]), a connected
scheme smooth over a field is irreducible, and over a separably closed field irreducible is
already geometrically irreducible ([Stacks, Tag 020J]).

## Main results

* `Stacks.SectionsVanishingOnSubscheme.connectedSpace_divisorOnX_of_isAmple`: `H_w` is connected.
* `Stacks.SectionsVanishingOnSubscheme.irreducibleSpace_divisorOnX_of_isAmple`: `H_w` is
  irreducible once it is smooth over `k`.
* `Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple`: `H_w` is
  geometrically irreducible over `k`, for `k` separably closed.

## The hypotheses, and where each is consumed

Beyond the standing situation, the three statements carry exactly five hypotheses, and none of
them is cosmetic.

* `IsProper f`. Hypothesis of [Stacks, Tag 0FD9], and the source of `CompactSpace X` and hence of
  `CompactSpace |H_w|` through the closed immersion `H_w ↪ X`.
* `Scheme.Modules.IsAmple X (tensorPowModule X L n)` — **ampleness of `ℒ ^⊗ n` itself, not of
  `ℒ`**. [Stacks, Tag 0FD9] is applied to the module `ℒ ^⊗ n` of which `w` is a section, so it is
  that module which must be ample. For `n = d ≥ 1` this follows from ampleness of `ℒ` by
  `Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple` ([Stacks, Tag 01PT]); the
  standing situation allows an arbitrary `n : ℤ`, for which there is nothing to derive it from,
  so it is assumed.
* `2 ≤ topologicalKrullDim X` — **the dimension hypothesis, and it cannot be dropped**. What
  [Stacks, Tag 0FD9] actually asks is `depth(𝒪_{X,x}) ≥ 2` at every closed point `x`, and on a
  smooth `X` that is exactly `dim X ≥ 2`: the local rings are regular, hence Cohen–Macaulay, so
  their depth is their Krull dimension, which is `dim X` by irreducibility
  (`AlgebraicGeometry.two_le_depth_stalk_of_smooth_of_irreducible`). On a curve the depth at a
  closed point is `1` and the conclusion is false — a zero scheme on a smooth curve is a finite
  set of reduced points, which is connected only when it is a single point. `dim X ≥ 2` is
  therefore the honest shape of this hypothesis and is stated in that shape rather than as the
  depth condition.
* `IsIntegral X`. Consumed only in `AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`, to
  turn `w ≠ 0` into the regularity of `w` as a section of `ℒ ^⊗ n` ([Stacks, Tag 01WY]) which
  [Stacks, Tag 0FD9] requires; it also supplies the `IrreducibleSpace X` that the depth bound
  reads the dimension on, and the `ConnectedSpace X` of [Stacks, Tag 0FD9].
* `w ≠ 0`. The zero section has `Z(0) = X`, which is not a divisor; this is the hypothesis
  `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair` already produces
  alongside the smoothness.

Smoothness of `H_w` over `k` is a hypothesis of the last two statements rather than an instance,
because that is the form the Bertini step delivers it in.

## Implementation notes

`Stacks.Bertini.FamilyDivisors.divisor` is by definition the zero scheme of
`Stacks.Bertini.FamilyDivisors.sectionOf`, and for `familyDivisorsOnX` the scheme is `X`, the
module is `ℒ ^⊗ n` and the section of `w` is `w` itself; so `H_w` *is* the zero scheme
[Stacks, Tag 0FD9] speaks about, with no transport. The one thing that does not match on the nose
is the shape of the section: [Stacks, Tag 0FD9] takes an element of `L.sections` and evaluates it
at `⊤`, where the standing situation holds a global section directly. The global section is lifted
by `Stacks.SheafOfModules.sectionsOfTop`, but the lift is introduced through `obtain` rather than
named, so that the rewrite which brings `(sectionsOfTop _ w).eval ⊤` back to `w` is a rewrite
along a hypothesis about a local constant. Rewriting with
`Stacks.SheafOfModules.sectionsOfTop_eval_top` itself does not work here: that lemma is stated for
a sheaf of modules over `structureSheafRing X.toRingedSpace` and `tensorPowModule X L n` is
presented over `X.ringCatSheaf`, and the motive it builds is rejected at the instance argument.

Geometric irreducibility is taken through [Stacks, Tag 020J] rather than through
`AlgebraicGeometry.geometricallyIrreducible_of_geometricallyConnected_of_smooth`, which would ask
for geometric connectedness of `H_w` and so for a rational point on it. Over the separably closed
field of the Bertini step there is nothing to base change along, and `020J` says exactly that.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension, and its remaining steps — the induction on `dim X`
and the curve case of [Stacks, Tag 0BA0] — are not available; what is here is one input to that
induction. [Stacks, Tag 0FD9] is already carried in full by
`Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple`, whose statement has neither
an irreducibility clause nor a geometric one.

## References

* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)
  [FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n))]
  [FiniteDimensional k (vanishingSections k f I L n)]

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **The divisor on `X` of a nonzero member of `V_n` is connected** when `ℒ ^⊗ n` is ample and
`X` is a proper integral scheme, smooth over `k` of dimension at least two.

This is [Stacks, Tag 0FD9] at the module `ℒ ^⊗ n` and the section `w`. Its three hypotheses are
met as follows: `w` is a regular section because it is a nonzero global section of an invertible
module on an integral scheme ([Stacks, Tag 01WY]); the local rings of `X` at closed points have
depth at least two because `X` is smooth of dimension at least two; and `X` is connected because
it is integral. -/
theorem connectedSpace_divisorOnX_of_isAmple [IsProper f] [Smooth f]
    [AlgebraicGeometry.IsIntegral X]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (tensorPowModule X L n))
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (w : vanishingSections k f I L n) (hw : w ≠ 0) :
    ConnectedSpace ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme := by
  have hinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (familyDivisorsOnX k f I (L := L) n).isInvertible
  obtain ⟨s, hs⟩ : ∃ s : (tensorPowModule X L n).sections,
      s.eval (op ⊤) = (w : Stacks.Bertini.globalSections k f (tensorPowModule X L n)) :=
    ⟨Stacks.SheafOfModules.sectionsOfTop (tensorPowModule X L n) _,
      Stacks.SheafOfModules.sectionsOfTop_eval_top (tensorPowModule X L n) _⟩
  have hne : s.eval (op ⊤) ≠ 0 := by
    rw [hs]
    exact fun h => hw (Submodule.coe_eq_zero.mp h)
  have H := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple k f
    (tensorPowModule X L n) hample s
    (isRegularSection_of_eval_top_ne_zero (tensorPowModule X L n) s hne)
    (two_le_depth_stalk_of_smooth_of_irreducible k f hdim)
  rw [hs] at H
  exact H

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **The divisor on `X` of a nonzero member of `V_n` is irreducible** as soon as it is smooth
over `k`, under the hypotheses that make it connected.

A connected quasi-compact scheme smooth over a field is irreducible
(`AlgebraicGeometry.irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace`); the
quasi-compactness comes from properness of `X` over `k` through the closed immersion
`H_w ↪ X`. -/
theorem irreducibleSpace_divisorOnX_of_isAmple [IsProper f] [Smooth f]
    [AlgebraicGeometry.IsIntegral X]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (tensorPowModule X L n))
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (w : vanishingSections k f I L n) (hw : w ≠ 0)
    (hsm : Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f)) :
    IrreducibleSpace ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme := by
  have : ConnectedSpace ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme :=
    connectedSpace_divisorOnX_of_isAmple k f I n hample hdim w hw
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace
      ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι
  have := hsm
  exact irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace
    (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f)

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **The divisor on `X` of a nonzero member of `V_n` is geometrically irreducible over a
separably closed base field** as soon as it is smooth over `k`, under the hypotheses that make it
connected.

This is the input the induction on `dim X` of [Stacks, Tag 0FH7] takes from its Bertini step: it
applies the induction to `H_w` as a variety over `k`, which asks for geometric irreducibility and
not only for irreducibility. Over a separably closed field the two coincide
([Stacks, Tag 020J]), and the field of the Bertini step is algebraically closed. -/
theorem geometricallyIrreducible_divisorOnX_of_isAmple [IsSepClosed k] [IsProper f] [Smooth f]
    [AlgebraicGeometry.IsIntegral X]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (tensorPowModule X L n))
    (hdim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (w : vanishingSections k f I L n) (hw : w ≠ 0)
    (hsm : Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f)) :
    GeometricallyIrreducible
      (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) :=
  have : IrreducibleSpace ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme :=
    irreducibleSpace_divisorOnX_of_isAmple k f I n hample hdim w hw hsm
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _
    (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f)

end Stacks.SectionsVanishingOnSubscheme

end
