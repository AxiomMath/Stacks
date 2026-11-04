module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints

/-!
# Descent of a difference of rational points along a closed immersion

Let `k` be a field, let `X` be a scheme locally of finite type over `k` and let `ι : H ⟶ X` be a
closed immersion of such schemes over `k`. If a `k`-rational point `x` of `X` factors through `H`,
say `x = x_H ≫ ι` with `x_H` a `k`-rational point of `H`, then proper pushforward along `ι`
carries the class of `x_H` in `CH_0(H)` to the class of `x` in `CH_0(X)`. Since that pushforward
is a homomorphism of abelian groups, a divisibility of a difference of two such classes in
`CH_0(H)` transports to the same divisibility in `CH_0(X)`.

This is the transport step of the induction of [Stacks, Tag 0FH7]. There the divisibility of
`[x] - [x']` by `n` is proved on a smooth hyperplane-type section `H_w ⊆ X` passing through both
points, by induction on the dimension, and must then be carried up to `X`; this file is that
carrying, and nothing else.

## Main results

* `Stacks.WeilCohomology.chowPushforwardOfIsClosedImmersion_rationalPointChowClass`: pushforward
  along `ι` of the class of `x_H` is the class of `x_H ≫ ι`.
* `Stacks.WeilCohomology.rationalPointChowClass_sub_eq_zsmul_chowPushforward`: if
  `[x_H] - [x'_H] = n c` in `CH_0(H)` then `[x] - [x'] = n ι_*c` in `CH_0(X)`.

## Implementation notes

The class of a rational point is `Stacks.WeilCohomology.rationalPointChowClass`, the established
spelling in this directory: a `k`-rational point is a section of the structure morphism, it is a
closed immersion because its target's structure morphism is separated, and its class is that of
the associated zero-cycle `Stacks.Chow.cycleAssociatedToClosedSubscheme`. The pushforward is
`Stacks.Chow.chowPushforwardOfIsClosedImmersion`, which needs no instance of [Stacks, Tag 02S2].

### The factorisation is a hypothesis, not a support condition

That `x` and `x'` lie on `H` is carried here as the two equations `x_H ≫ ι = x` and
`x'_H ≫ ι = x'` together with the two section properties of `x_H` and `x'_H`, that is as
honest sections of `H ⟶ Spec k` through the two points.

The alternative would be to carry what the Bertini step of [Stacks, Tag 0FH7] actually produces.
That step, `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair`, speaks of
*topological* points `x x' : X` that are closed, and it assumes `I.support ⊆ {x, x'}`; the
reverse inclusion `{x, x'} ⊆ I.support`, which is what makes the two points lie on `H_w` (every
member of `V_n` vanishes on `Z = |V(I)|`), gives only membership of the underlying sets. Turning
that membership into a morphism `Spec k ⟶ H_w` is a separate scheme-theoretic step — the
`k`-rational point of `X`, as a closed immersion of `Spec k`, has to be shown to factor through
the closed subscheme `H_w`, which is the statement that the ideal of `H_w` pulls back to zero
along it — and that step is not available here. So the support form is *not* what the Bertini
step produces for this purpose, and carrying it would only move the missing factorisation inside
this statement. It is left outside, named, and owed.

The hypothesis `hx : x ≫ p = 𝟙 (Spec k)` is implied by the other three, by associativity; it is
carried so that the conclusion can name `Stacks.WeilCohomology.rationalPointChowClass k p x hx`
without a proof term inlined into the statement, which is also what lets the divisibility
transport be stated and used by rewriting.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension; what is proved here is one step of its induction, and
the tag's remaining steps — the induction on `dim X` itself, the curve case and the Jacobian of
[Stacks, Tag 0BA0] — are not available.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X H : Scheme.{u}}
  (p : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType p]
  (pH : H ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType pH]
  (ι : H ⟶ X) [IsClosedImmersion ι] (hι : ι ≫ p = pH)

/-- **The class of a rational point of a closed subscheme pushes forward to the class of that
point.** Let `ι : H ⟶ X` be a closed immersion of schemes locally of finite type over a field
`k`, let `x_H` be a `k`-rational point of `H` and let `x = x_H ≫ ι` be the `k`-rational point of
`X` it determines. Then

  `ι_* [x_H] = [x]` in `CH_0(X)`.

This is `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`
— the proper pushforward of the cycle of a closed subscheme `Z ⊆ H` along `ι` is the cycle of
`Z ⊆ X` — at the closed subscheme `x_H : Spec k ⟶ H`, read on Chow classes through
`Stacks.Chow.chowPushforwardOfIsClosedImmersion_mk`. -/
theorem chowPushforwardOfIsClosedImmersion_rationalPointChowClass
    (xH : (Stacks.Chow.fieldChowSituation k).S ⟶ H)
    (hxH : xH ≫ pH = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
    (x : (Stacks.Chow.fieldChowSituation k).S ⟶ X) (hfac : xH ≫ ι = x)
    (hx : x ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k).S) :
    Stacks.Chow.chowPushforwardOfIsClosedImmersion (Stacks.Chow.fieldChowSituation k) pH p ι hι 0
        (rationalPointChowClass k pH xH hxH) =
      rationalPointChowClass k p x hx := by
  subst hfac
  let : IsClosedImmersion xH := isClosedImmersion_of_comp_eq_id pH xH hxH
  have h := Stacks.Chow.chowPushforwardOfIsClosedImmersion_mk
    (Stacks.Chow.fieldChowSituation k) pH p ι hι 0
    (Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation k) pH xH 0)
  rw [Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    at h
  exact h

/-- **Divisibility of a difference of rational points transports along a closed immersion.** Let
`ι : H ⟶ X` be a closed immersion of schemes locally of finite type over a field `k` and let
`x_H`, `x'_H` be `k`-rational points of `H` whose composites with `ι` are the `k`-rational points
`x`, `x'` of `X`. If `[x_H] - [x'_H] = n c` in `CH_0(H)` then

  `[x] - [x'] = n (ι_* c)` in `CH_0(X)`.

This is the transport step of the induction of [Stacks, Tag 0FH7]: the divisibility proved on a
smooth hyperplane-type section through both points is carried up to the ambient scheme. It is
`Stacks.WeilCohomology.chowPushforwardOfIsClosedImmersion_rationalPointChowClass` on each of the
two points together with the fact that
`Stacks.Chow.chowPushforwardOfIsClosedImmersion` is a homomorphism of abelian groups, so that it
commutes with the difference and with multiplication by `n`. -/
theorem rationalPointChowClass_sub_eq_zsmul_chowPushforward
    (xH xH' : (Stacks.Chow.fieldChowSituation k).S ⟶ H)
    (hxH : xH ≫ pH = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
    (hxH' : xH' ≫ pH = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
    (x x' : (Stacks.Chow.fieldChowSituation k).S ⟶ X)
    (hfac : xH ≫ ι = x) (hfac' : xH' ≫ ι = x')
    (hx : x ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
    (hx' : x' ≫ p = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
    (n : ℤ) (c : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) pH 0)
    (hc : rationalPointChowClass k pH xH hxH - rationalPointChowClass k pH xH' hxH' = n • c) :
    rationalPointChowClass k p x hx - rationalPointChowClass k p x' hx' =
      n • Stacks.Chow.chowPushforwardOfIsClosedImmersion (Stacks.Chow.fieldChowSituation k) pH p
        ι hι 0 c := by
  rw [← chowPushforwardOfIsClosedImmersion_rationalPointChowClass k p pH ι hι xH hxH x hfac hx,
    ← chowPushforwardOfIsClosedImmersion_rationalPointChowClass k p pH ι hι xH' hxH' x' hfac' hx',
    ← map_sub, hc, map_zsmul]

end Stacks.WeilCohomology

end
