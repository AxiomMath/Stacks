module

public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeAssertions
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeIdealSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0846, parts (1), (2) and the chartwise first half of (4), for an invertible module

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `L` be an
invertible `𝒪_X`-module and let `s` be a global section of `L`.  The general forms of parts (1),
(2) and of the chartwise first half of part (4) of Stacks 0846 in
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeAssertions.lean` carry the hypothesis `hZ` that
some closed subspace of `X` has the evaluation ideal of `s` as its defining ideal on the affine
étale charts.  For an invertible `L`, the source's hypothesis, `hZ` is a theorem:
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`
(an invertible module is finite locally free of rank one on the small étale site, Stacks 0B8Q,
hence quasi-coherent of finite presentation, which makes the ideal of Stacks 0845
quasi-coherent).  This file states the three assertions with invertibility of `L` the only
hypothesis.

Part (3) is `AlgebraicGeometry.Space.isLocallyPrincipal_zeroScheme` in
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeLocallyPrincipal.lean`, and part (4) is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection` in
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeEffectiveCartier.lean`.

## Main results

* `AlgebraicGeometry.Space.isGreatest_zeroScheme_of_isInvertible`: part (1).
* `AlgebraicGeometry.Space.exists_comp_eq_zeroScheme_iff_of_isInvertible`: part (2).
* `AlgebraicGeometry.Space.definingIdealAt_zeroScheme_eq_span_generator_of_isInvertible`: the
  chartwise reading of the first half of part (4).

## References

* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0846 (1).**  Let `L` be an invertible `𝒪_X`-module and `s` a global section of `L`.
Among the closed subspaces of `X` on which `s` vanishes — read chartwise: those whose defining
ideal contains the evaluation ideal of `s` on every affine étale chart — the zero scheme of `s`
is the greatest.

The hypotheses are the source's own and nothing else: invertibility of `L` discharges the
realization of the evaluation ideal by a closed subspace, through
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`. -/
@[stacks 0846 "part (1): maximality of the zero scheme among the closed subspaces on which the \
section vanishes, read chartwise, with no assumed inputs"]
theorem isGreatest_zeroScheme_of_isInvertible (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) :
    IsGreatest {W : ClosedSubspaces B S hS X.1 |
      ∀ U : SmallEtale B S hS X.1,
        IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1 →
        sectionEvaluationIdealAt B S hS X L s U ≤ definingIdealAt B S hS X W (op U)}
      (zeroScheme B S hS X L s) :=
  isGreatest_zeroScheme_of_exists_definingIdealAt_eq B S hS X L s
    (exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible B S hS X L s hinv)

/-- **Stacks 0846 (2).**  Let `L` be an invertible `𝒪_X`-module and `s` a global section of `L`.
A morphism `f : Y ⟶ X` of algebraic spaces factors through the zero scheme of `s` exactly when
`s` vanishes after pullback along `f` — read chartwise: on every affine étale chart `U` of `X`
the evaluation ideal of `s` is killed by pullback of regular functions along every point of `Y`
lying over `U`.

The hypotheses are the source's own and nothing else: invertibility of `L` discharges the
realization of the evaluation ideal by a closed subspace, through
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`. -/
@[stacks 0846 "part (2): a morphism factors through the zero scheme exactly when the \
pulled-back section vanishes, read chartwise, with no assumed inputs"]
theorem exists_comp_eq_zeroScheme_iff_of_isInvertible (X Y : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) (f : Y ⟶ X) :
    (∃ g : Y ⟶ (⟨(zeroScheme B S hS X L s).1.toFunctor,
        (zeroScheme B S hS X L s).2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk (zeroScheme B S hS X L s).1.ι = f) ↔
      ∀ U : SmallEtale B S hS X.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        ∀ (a : BigFppfOver B S hS) (k : a ⟶ U.1.left) (y : yoneda.obj a ⟶ Y.1),
          yoneda.map k ≫ U.1.hom = y ≫ f.hom →
            sectionEvaluationIdealAt B S hS X L s U ≤
              RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom :=
  exists_comp_eq_zeroScheme_iff_of_exists_definingIdealAt_eq B S hS X Y L s
    (exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible B S hS X L s hinv) f

/-- **Stacks 0846 (4), first half, read chartwise.**  Let `L` be an invertible `𝒪_X`-module and
`s` a global section of `L`.  On an affine étale chart `U` of `X` where `L` is free of rank one,
with generator `t` and coordinate functional `l₀`, the zero scheme of `s` is cut out by the
single regular function `l₀(s|_U)`.

Invertibility of `L` discharges the realization of the evaluation ideal by a closed subspace,
through
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`.
The chart data `t`, `l₀`, `hb` is local freeness of rank one on `U`, which for an invertible `L`
holds on a cover of `X` by Stacks 0B8Q; it is what makes the chartwise reading of the part a
statement about one regular function, and it is what the global form
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection` supplies for
itself instead of assuming. -/
@[stacks 0846 "part (4) read chartwise: the zero scheme is cut out on an affine chart by one \
regular function, with L carried as free of rank one on that chart by a generator t and a \
coordinate functional l₀; the chart U and the functional l₀ occur in the conclusion, which \
names the function as l₀ of the section over U"]
theorem definingIdealAt_zeroScheme_eq_span_generator_of_isInvertible (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1)
    (t : ToType (L.val.obj (op U)))
    (l₀ : Module.Dual
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op U))
      (L.val.obj (op U)))
    (hb : ∀ x, l₀ x • t = x) :
    definingIdealAt B S hS X (zeroScheme B S hS X L s) (op U) =
      Ideal.span {l₀ (s.eval (op U))} :=
  definingIdealAt_zeroScheme_eq_span_generator B S hS X L s
    (exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible B S hS X L s hinv)
    U hU t l₀ hb

end AlgebraicGeometry.Space

end
