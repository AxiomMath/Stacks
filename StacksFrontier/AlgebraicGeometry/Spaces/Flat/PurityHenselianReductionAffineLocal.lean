module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityAffineLocalBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.UniversalPurityFromPurity

/-!
# The strictly henselian reduction of Stacks 0CW4 with its affine local conjunct discharged

`AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`, the hypothesis carried by this
development's Stacks 0CW4, asks for a morphism of pointed algebraic spaces
`(Y₁, y₁) ⟶ (Y, y)` — intended to be `Spec 𝒪_{Y, ȳ} ⟶ Y` with its closed point — such that four
things hold of the base change along it. One of the four is that the base change be *affine
local at its chosen point*, `AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt`, and
until `AlgebraicGeometry.BigFppfOver.specStalk` there was no construction of that condition
anywhere, so the carry could not be approached at all.

This file removes that conjunct. `AlgebraicGeometry.Space.PurityReductionAtSpecStalk` is the
same reduction with the pointed base change *pinned* to the one of
`AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver` — the base change to
`Spec 𝒪_{V, v}` for a scheme chart `V` of the base and a point `v` of it above `y`, which is the
base change the source itself takes — and with the affine local conjunct dropped, because
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver` supplies it.
`AlgebraicGeometry.Space.purityStrictlyHenselianReduction_of_purityReductionAtSpecStalk` is the
implication, so every consumer of the old carry can be fed the new one.

## What this is and is not

The new condition is a **sufficient** condition for the old one, and it is not weaker as a
hypothesis: it fixes the pointed base change instead of quantifying existentially over all of
them. What it buys is that one of the four conjuncts — the only one that no declaration in this
development could produce — is gone, and the witness is a named construction rather than an
unknown.

The remaining three conjuncts are genuinely open here:

* `HasFlatImpurityAscentData` is the ascent data of Stacks 0CVA that Stacks 0CVG consumes, whose
  first conjunct is flatness of `Spec 𝒪_{V, v} ⟶ V` at the closed point;
* `IsPureAbove` of the base change is the ascent of purity along `Spec 𝒪_{V, v} ⟶ V`, which the
  source uses silently. It is **not** dischargeable from Stacks 0CVE,
  `AlgebraicGeometry.Space.isUniversallyPureAbove_iff_forall_baseChange_isPureAbove`: that
  equivalence yields purity of every pointed base change from *universal* purity of the
  situation, and universal purity is exactly what Stacks 0CW4 is trying to prove, so using it
  here would be circular;
* the étale cover of Stacks 0CVW along which the base change is universally pure, which is the
  source's appeal to More on Flatness, Stacks 05K6.

## References

* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
* [Stacks Project, Tag 0CVE](https://stacks.math.columbia.edu/tag/0CVE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The reduction of Stacks 0CW4 to a local base, at the base change to `Spec 𝒪_{V, v}`.**
For a module flat over `Y` along the fibre `f^{-1}(\{y\})` and pure above `y`, there is a
scheme chart `V` of the base with a point `v` above `y` such that the base change of the
situation to `Spec 𝒪_{V, v}` — the one of
`AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver` — admits the impurity ascent
data of Stacks 0CVA, is still pure above its closed point, and carries an étale `g` whose image
contains the fibre over that closed point and along which the module pulls back to one
universally pure above it.

This is `AlgebraicGeometry.Space.PurityStrictlyHenselianReduction` with its affine local
conjunct removed and its existential pinned; see the module docstring for what that does and
does not buy. -/
def PurityReductionAtSpecStalk (P : PrePureSituation.{u, u} B S hS) : Prop :=
  (∀ x : points B S hS P.X, pointsMap B S hS P.X P.f x = P.y →
      x ∈ flatLocus B S hS P.hX P.f P.F) →
    IsPureAbove P →
      ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
        (hv : pointsMap B S hS (yoneda.obj V) a v = P.y),
        HasFlatImpurityAscentData (P.specStalkPointedOver V a v hv) ∧
          IsPureAbove (P.specStalkPointedOver V a v hv).baseChange ∧
          ∃ e : EtaleOverSource (P.specStalkPointedOver V a v hv).baseChange,
            pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
                  (P.specStalkPointedOver V a v hv).baseChange.f ⁻¹'
                {(P.specStalkPointedOver V a v hv).baseChange.y} ⊆
              Set.range (pointsMap B S hS e.X'.1 e.g.hom) ∧
              IsUniversallyPureAbove e.situation

/-- **The affine local conjunct of the strictly henselian reduction of Stacks 0CW4 is free once
the base change is taken to `Spec 𝒪_{V, v}`.** The base change to `Spec 𝒪_{V, v}` is affine
local at its closed point by
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver`, so the three
remaining conjuncts of `AlgebraicGeometry.Space.PurityReductionAtSpecStalk` give the four of
`AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`.

Composing with `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove` this means that
Stacks 0CW4 — and through it Stacks 0CW5 — now carries three conditions on a named base change
rather than four on an unknown one. -/
theorem purityStrictlyHenselianReduction_of_purityReductionAtSpecStalk
    (P : PrePureSituation.{u, u} B S hS) (h : PurityReductionAtSpecStalk P) :
    PurityStrictlyHenselianReduction P := by
  intro hflat hpure
  obtain ⟨V, a, v, hv, hascent, hpure₁, e, hfibre, huniv⟩ := h hflat hpure
  exact ⟨P.specStalkPointedOver V a v hv, hascent,
    P.isAffineLocalAt_specStalkPointedOver V a v hv, hpure₁, e, hfibre, huniv⟩

/-- **Stacks 0CW4, carrying the reduction at `Spec 𝒪_{V, v}`.** In the situation of
Stacks 0CV6, if `ℱ` is flat over `Y` at every point of `X` lying over `y` and pure above `y`,
then `ℱ` is universally pure above `y`.

This is `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove` fed through
`AlgebraicGeometry.Space.purityStrictlyHenselianReduction_of_purityReductionAtSpecStalk`, so
the carry is the three-conjunct `AlgebraicGeometry.Space.PurityReductionAtSpecStalk` on the
named base change to `Spec 𝒪_{V, v}` rather than the four-conjunct
`AlgebraicGeometry.Space.PurityStrictlyHenselianReduction` on an unknown one. It carries no
`@[stacks 0CW4]` attribute: the tag already sits on
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove`, and registering a second
declaration for the same clause would make the audit read the tag as carried twice. -/
theorem isUniversallyPureAbove_of_isPureAbove_of_purityReductionAtSpecStalk
    (P : PrePureSituation.{u, u} B S hS) (hred : PurityReductionAtSpecStalk P)
    (hflat : ∀ x : points B S hS P.X, pointsMap B S hS P.X P.f x = P.y →
      x ∈ flatLocus B S hS P.hX P.f P.F)
    (hpure : IsPureAbove P) :
    IsUniversallyPureAbove P :=
  isUniversallyPureAbove_of_isPureAbove P
    (purityStrictlyHenselianReduction_of_purityReductionAtSpecStalk P hred) hflat hpure

end AlgebraicGeometry.Space

end
