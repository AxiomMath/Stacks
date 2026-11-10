module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineIntegralRepresentableTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse

/-!
# Stacks 0BPV at its affineness and integrality properties

`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse` factors the argument common
to every clause of **Stacks 0BPV** into
`AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff`: a condition of Properties of
Stacks, Section 04XB holds for the restricted relative diagonal `Δ` of a morphism of thickenings
of algebraic stacks exactly when it holds for the ambient one `Δ'`, the only input per property
being the cancellation of that property against a surjective closed immersion of algebraic
spaces. This file reads that engine at the two properties for which the cancellation has just
been proved — affineness and integrality, parts (1) and (5) of **Stacks 09ZY**, in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineIntegralRepresentableTransfer` — and so
would carry the tag at its properties (b) and (f).

**Neither clause below is registered.** Both carry the three hypotheses of the library's Stacks
07VT, and one of them, `h07SQ`, is Stacks 07SQ with no bound on the index set, which is false in
this development: an index as large as the site's size cutoff can have the empty algebraic space
as its limit with no affine stage. The `@[stacks 0BPV …]` attributes these two lemmas carried were
therefore removed; the clauses need the unconditional descent of affineness along a thickening
of algebraic spaces, which is absent.

## What these two clauses assume, and what they do not

The space-level cancellation for affineness is *conditional*: parts (1) and (5) of Stacks 09ZY
rest on **Stacks 07VT**, that an algebraic space receiving a surjective universally closed
morphism from an affine scheme is affine, which this library registers conditionally at
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`. Its three
hypotheses `h09YA`, `h07SQ` and `hFinitePresentation` are carried verbatim through the square
forms into the two clauses below, where they are used for nothing else. **Both clauses are
therefore exactly as conditional as Stacks 07VT and no more**, unlike the eight clauses of this
tag carried in `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonal` and
`…Stacks.ThickeningSeparationConverse`, which assume nothing.

Inside the space-level statements only the implication *from the closed subspaces* uses the three
hypotheses; the implication to them is a cancellation along the square and is unconditional. The
engine consumes exactly the conditional implication — the cancellation of the property off the
front of `Δ ≫ k ≅ i ≫ Δ'` is the square form read at an identity right-hand inclusion, which is
its `mp` direction — so both halves of each clause below inherit the hypotheses as parameters,
and neither clause is available unconditionally.

**Stacks 07VT is awaited, not absent, and these two clauses become unconditional when it
lands.** None of the three hypotheses can be discharged against the library *as it stands*:
no declaration of this library registers Stacks 07SQ, 09YA, 084Z or 07VP, in either of the two
forms this project uses — the `@[stacks …]` attribute and the `add_to_stacks` command, the second
of which no search for the first will find — where `h07SQ` is the conclusion of Stacks 07SQ and
`hFinitePresentation` is
the third paragraph of the proof of Stacks 07VS, which runs through Stacks 07SU, 07SK, 084Z,
07SN and 07VP — the first, second and fourth of those being proved and the other two not. Each of
07VT, 09YA, 07SQ and 07SU is formalized elsewhere in the project, so the conditionality here is a
question of order, not of mathematics: once Stacks 07VT is available unconditionally, the three
parameters come off by substitution, since they are passed straight through to
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed` and used for
nothing else.

`h09YA` is worth separating from the other two, because what stands between it and a proof is
not plumbing. The proof of Stacks 09YA writes the direct-image algebra `f_* 𝒪_X` of the
*integral* morphism `f` as a directed colimit of finite algebras of finite presentation, and
that step is **Stacks 082C**, which no declaration of this library registers in either form. What
the library has
around it is the vocabulary — `AlgebraicGeometry.Space.AlgebraSheaf` with its `IsFinite`,
`IsIntegral`, `IsFiniteType` and `IsFinitePresentation`, and
`AlgebraicGeometry.Space.FiniteSubalgebra` with its diagram and cocone, in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits` — together with the one step of
082C that is pure commutative algebra,
`AlgebraicGeometry.Space.AlgebraSheaf.IsFinite.of_isFiniteType_of_injective`, and the reduction
of the finite-subalgebra colimit to the finite-type one,
`AlgebraicGeometry.Space.isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone`.
The colimit itself is not proved here. The adjacent **Stacks 086Z** is the *finite* case, not the
integral one, and even it is proved only over a carried input, as
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective` in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem`; so it cannot stand
in for 082C, and routing 09YA through it would trade `h09YA` for that carried input at every
stage of a system, which is why that route is not taken even though it is shorter than the
source's. Stacks 082C too is formalized elsewhere in the project; see the module
documentation of `StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits` for which of its
inputs this library has and which it does not.

Part (5) of Stacks 09ZY is part (1) conjoined with part (4) by **Stacks 0415**, and part (4),
`AlgebraicGeometry.Space.universallyClosed_iff_universallyClosed_of_isClosedImmersion_square`, is
unconditional; so clause (f) is granted exactly what clause (b) is granted. Clause (f) is *not*
the conjunction of clause (b) with clause (e) of this tag at the level of stacks: that splitting
happens once, at the level of morphisms of algebraic spaces, inside Stacks 09ZY part (5).

## Why clause (a), representability by schemes, is not here

Clause (a) of Stacks 0BPV has its space-level cancellation too — Stacks 09ZY part (9), the
representability companion of
`AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_of_isClosedImmersion_square` in the same
file — and it is nevertheless out of reach of this engine, for a reason about the
framework rather than about the mathematics. `AlgebraicGeometry.Stack.HasRelativeProperty`
(**Stacks 03YK**) carries `[P.IsStableUnderBaseChange]` and
`[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]` as instance arguments, so a
condition of Stacks 04XB cannot even be *stated* at a property lacking fppf locality on the
target; and representability by schemes, as a property of morphisms of algebraic spaces, has no
such statement in this library. Nor is the gap an oversight of this library: the source's own
Section 04XB assumes of `P` that it be fppf local on the target, and the list of properties it
enumerates there does not contain representability by schemes.

What clause (a) needs first is therefore one of two things: the fppf descent of representability
by schemes for morphisms of algebraic spaces, which would make it an instance of the engine like
the two clauses below; or a form of
`AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_spaceCancelFirst` whose test is at
*scheme-valued* points of the ambient product only. The second is what the source's own proof
uses implicitly, and it is available in principle, because the comparison
`AlgebraicGeometry.Stack.selfProductDiagonalMap` is a thickening: a scheme-valued point of
`𝒳' ×_{𝒴'} 𝒳'` restricts along it to a *closed subspace of a scheme*, hence to a scheme-valued
point of `𝒳 ×_𝒴 𝒳`. The library's cancellation instead tests at an algebraic-space-valued point,
through **Stacks 04XC**, and that is exactly where the locality instance enters.

## Main results

* `AlgebraicGeometry.Stack.isAffineHom_of_isThickening`: a thickening of algebraic stacks is
  affine in the sense of Stacks 04XB, because a closed immersion of algebraic spaces is affine
  (**Stacks 07U2**).
* `AlgebraicGeometry.Stack.hasRelativeProperty_integral_of_isThickening`: the same for
  integrality, a closed immersion of algebraic spaces being integral.
* `AlgebraicGeometry.Stack.isAffineHom_relativeDiagonal_iff`: **Stacks 0BPV** at its property
  (b), affineness.
* `AlgebraicGeometry.Stack.isIntegralHom_relativeDiagonal_iff`: **Stacks 0BPV** at its property
  (f), integrality.

## Implementation notes

Of the three permanence instances that a relative property of Stacks 03YK is introduced under,
`AlgebraicGeometry.Space.integralMorphismProperty` carries all three already — stability under
base change from Stacks 03ZS, locality on the target at the fppf precoverage from **Stacks
0425**, and stability under composition from Stacks 03ZR — so clause (f) needs no local instance.
`AlgebraicGeometry.Space.affineMorphismProperty` carries only stability under composition
(**Stacks 03WH**); the other two are introduced as local instances in the proof of clause (b),
from `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback` and from **Stacks 041Z**
(`AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc`) restricted along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` (**Stacks 0DFQ**). This is the idiom
`AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_iff` and
`…Stack.universallyClosed_relativeDiagonal_iff` already use for their missing locality instance,
and it keeps affineness descent off the statements: neither clause below assumes a descent
result.

Clause (b) is stated at `AlgebraicGeometry.Stack.IsAffineHom`, the written-out condition of
Stacks 04XB at `AlgebraicGeometry.Space.IsAffineHom`, which — carrying no instance argument of
its own — is the spelling the six proved clauses use. Clause (f) is stated at
`AlgebraicGeometry.Stack.HasRelativeProperty` directly, as clause (j) of this tag is: the
written-out abbreviation for Stacks 04XB-integrality,
`AlgebraicGeometry.Stack.IsIntegralHom`, lives in
`StacksFrontier.AlgebraicGeometry.Stacks.NormalizationMorphism` beside the normalization of a
groupoid in algebraic spaces, and its conjunction with representability by algebraic spaces —
which a relative diagonal has for free by part (1) of **Stacks 04XS** — is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsIntegralHom`, **Stacks 0CHU** part (1). The three
statements agree, the relative diagonal being representable by algebraic spaces.

The condition for the comparison `AlgebraicGeometry.Stack.selfProductDiagonalMap`, which the
engine asks for alongside the cancellation, is read off the first assertion of **Stacks 0BPU**
(`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`) through the two lemmas below, in
the same way as the five `…_of_isThickening` lemmas of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse`. Only the closed-immersion
clause of a thickening is used, not its surjectivity.

## References

* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0425](https://stacks.math.columbia.edu/tag/0425)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0CHU](https://stacks.math.columbia.edu/tag/0CHU)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-! ### The comparison of the two self-products -/

/-- A thickening of algebraic stacks is affine in the sense of Stacks 04XB, because a closed
immersion of algebraic spaces is affine (**Stacks 07U2**). Only the closed-immersion clause of
the thickening is used. -/
theorem isAffineHom_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) : Stack.IsAffineHom B S hS p.hom :=
  fun U y hy F hF he =>
    Space.isAffineHom_of_isClosedImmersion B S hS _ (hp.1.2 U y hy F hF he)

/-- A thickening of algebraic stacks is integral in the sense of Stacks 04XB, because a closed
immersion of algebraic spaces is integral. Only the closed-immersion clause of the thickening is
used.

This is the integrality counterpart of
`AlgebraicGeometry.Stack.hasRelativeProperty_closedImmersion_of_isThickening`, and is stated at
`AlgebraicGeometry.Stack.HasRelativeProperty` because integrality's three permanence instances
are global. -/
theorem hasRelativeProperty_integral_of_isThickening {𝒰 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {p : 𝒰 ⟶ 𝒵} (hp : IsThickening p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS) p.hom
      hp.1.1 :=
  fun U y hy F hF he =>
    Space.isIntegralHom_of_isClosedImmersion B S hS _ (hp.1.2 U y hy F hF he)

/-! ### The clauses -/

/-- **Stacks 0BPV at the affineness property.** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is affine in the sense of Stacks 04XB (**Stacks 03WF**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is.

`AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff` at
`AlgebraicGeometry.Space.affineMorphismProperty`. The cancellation of affineness against a
surjective closed immersion of algebraic spaces is **Stacks 09ZY** part (1),
`AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_of_isClosedImmersion_square`, read at an
identity right-hand inclusion. Stability of affineness under base change is
`AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback` and target-locality at the fppf
precoverage is **Stacks 041Z** restricted along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`; both are introduced locally, so
this statement assumes no descent result.

It is not registered (see the module documentation); it would be property (b), for an arbitrary
morphism of thickenings and granted the three hypotheses of Stacks 07VT. -/
theorem isAffineHom_relativeDiagonal_iff
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → Space.IsIntegralHom B S hS g →
      Space.IsQuasiCompactSpace B S hS Y₀ →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      Space.IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS B.contains_terminal I),
      Space.IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ Space.IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → Space.IsFinite B S hS g →
      Space.IsFinitePresentation B S hS g → Space.IsSurjective B S hS g →
      Space.IsAffineSpace B S hS X₀ → Space.IsAffineSpace B S hS Y₀) :
    Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom := by
  have _haffBC : (Space.affineMorphismProperty B S hS).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg => Space.isAffineHom_hom_of_isPullback sq hg }
  have _haffLoc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have _hfpqc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
      Space.isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.affineMorphismProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      (Space.isAffineHom_iff_isAffineHom_of_isClosedImmersion_square B S hS
        A.2 C.2 D.2 (i := a.hom) (j := 𝟙 D.1) (a.hom ≫ b.hom) b.hom hci hsurj
        (Space.isClosedImmersion_id B S hS D.1) (Category.comp_id _)
        h09YA h07SQ hFinitePresentation).1 hab)
    (isAffineHom_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- **Stacks 0BPV at the integrality property.** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is integral in the sense of Stacks 04XB (**Stacks 03ZP**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is.

`AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff` at
`AlgebraicGeometry.Space.integralMorphismProperty`, whose three permanence instances are global.
The cancellation of integrality against a surjective closed immersion of algebraic spaces is
**Stacks 09ZY** part (5),
`AlgebraicGeometry.Space.isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square`, read at an
identity right-hand inclusion; by **Stacks 0415** that is part (1) conjoined with part (4), and
the splitting happens there rather than here.

It is not registered (see the module documentation); it would be property (f), for an arbitrary
morphism of thickenings and granted the three hypotheses of Stacks 07VT. -/
theorem isIntegralHom_relativeDiagonal_iff
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → Space.IsIntegralHom B S hS g →
      Space.IsQuasiCompactSpace B S hS Y₀ →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      Space.IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS B.contains_terminal I),
      Space.IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ Space.IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → Space.IsFinite B S hS g →
      Space.IsFinitePresentation B S hS g → Space.IsSurjective B S hS g →
      Space.IsAffineSpace B S hS X₀ → Space.IsAffineSpace B S hS Y₀) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.integralMorphismProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      (Space.isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square B S hS
        A.2 C.2 D.2 D.2 (i := a.hom) (j := 𝟙 D.1) (a.hom ≫ b.hom) b.hom hci hsurj
        (Space.isClosedImmersion_id B S hS D.1) (Category.comp_id _)
        h09YA h07SQ hFinitePresentation).1 hab)
    (hasRelativeProperty_integral_of_isThickening B S hS
      (isThickening_selfProductDiagonalMap B S hS m))

end Diagonal

end AlgebraicGeometry.Stack

end
