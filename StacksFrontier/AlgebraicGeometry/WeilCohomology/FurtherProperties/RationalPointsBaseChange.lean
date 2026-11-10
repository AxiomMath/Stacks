module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitChow
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SectionCycle
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme

/-!
# The class of a rational point under a field base change

Let `K/k` be a field extension, let `X` be a scheme locally of finite type over `k` and let `x` be
a `k`-rational point of `X`, that is a section of the structure morphism. Base change along
`Spec K ⟶ Spec k` carries the class of `x` in `CH_0(X)` to the class of the induced `K`-rational
point of `X_K` in `CH_0(X_K)`, and therefore carries a difference `[x] - [x']` to the difference
of the two induced classes.

The base change is read through an arbitrary cartesian square realizing `X_K`, and the induced
point is presented by its two defining properties — that it is a section of the structure
morphism of the base change, and that it lies over `x` — rather than by a construction. Nothing
is lost: for the canonical square of `CategoryTheory.Limits.pullback` the section
`Stacks.Picard.baseChangePoint` has both properties by
`Stacks.Picard.baseChangePoint_comp_snd` and `Stacks.Picard.baseChangePoint_comp_fst`.

## Main results

* `Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass` — base change
  along a field extension carries the class of a rational point to the class of the induced
  rational point of the base change.
* `Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub` — the same
  for a difference of two rational points, which is the shape the divisibility argument for
  Stacks Tag 0FH7 consumes.

## Implementation notes

The class of a rational point is the class of the fundamental zero-cycle of the point viewed as a
closed subscheme, so the identity is Stacks 0FVI part (1) at the closed immersion `x`, modulo two
inputs.

The first is the dimension hypothesis of that part: the point has delta-dimension at most zero
over `k`. Being a section, `x ≫ p` is the identity of `Spec k`, whose delta-dimension is at most
zero because the dimension function of `Stacks.Chow.fieldChowSituation` vanishes. That is
`Stacks.WeilCohomology.schemeDeltaDimension_id_le_zero`, transported along the section identity
by `Stacks.Chow.schemeDeltaDimension_congr`; no separate computation of the relative dimension of
a closed point is needed, and in particular no Jacobson or `T1Space` hypothesis on `X`.

The second is that the base change of `x` along the projection `X_K ⟶ X` *is* the induced point:
Stacks 0FVI part (1) delivers the cycle of `pullback.snd x pr`, whereas the conclusion names the
cycle of the section `y`. The square exhibiting `y` as that base change is
`Stacks.Chow.isPullback_section`, the general statement that a section of a morphism and a section
of its base change lying over it form a cartesian square, and the fundamental cycle does not see
the resulting isomorphism of closed subschemes by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`.

No `@[stacks]` attribute is carried. The identity is Stacks 0FVI part (1) specialized to a
rational point, not a new tag, and it is one input of the divisibility step of Stacks Tag 0FH7,
which asks for much more.

## References

* Stacks Project, Tag 0FVI: https://stacks.math.columbia.edu/tag/0FVI
* Stacks Project, Tag 0FH7: https://stacks.math.columbia.edu/tag/0FH7
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- **Base change along a field extension carries the class of a rational point to the class of
the induced rational point.** Let `K/k` be a field extension, let `p : X ⟶ Spec k` be locally of
finite type, let `x` be a `k`-rational point of `X` and let `pr, q` present `Y` as the base change
`X_K` by a cartesian square. If `y` is a section of `q` lying over `x`, then the flat base-change
homomorphism `CH_0(X) ⟶ CH_0(Y)` sends the class of `x` to the class of `y`.

The hypotheses `hy` and `hxy` determine `y` uniquely, and for the canonical cartesian square they
hold of `Stacks.Picard.baseChangePoint`. -/
theorem baseChangeChowPullbackOfIsPullback_rationalPointChowClass (k K : Type u) [Field k]
    [Field K] [Algebra k K] {X Y : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType p] {pr : Y ⟶ X} {q : Y ⟶ (fieldChowSituation K).S}
    [LocallyOfFiniteType q]
    (sq : IsPullback pr q p (fieldExtensionBaseChangeSituation k K).g)
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S)
    (y : (fieldChowSituation K).S ⟶ Y) (hy : y ≫ q = 𝟙 (fieldChowSituation K).S)
    (hxy : y ≫ pr = (fieldExtensionBaseChangeSituation k K).g ≫ x) :
    baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl p sq 0
        (rationalPointChowClass k p x hx) = rationalPointChowClass K q y hy := by
  let : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id p x hx
  let : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id q y hy
  have hdim : schemeDeltaDimension (fieldChowSituation k) (x ≫ p) ≤ ((0 : ℤ) : EInt) :=
    (schemeDeltaDimension_congr (fieldChowSituation k) hx).trans_le
      (schemeDeltaDimension_id_le_zero (fieldChowSituation k) fun _ ↦ rfl)
  have hpb : IsPullback (fieldExtensionBaseChangeSituation k K).g y x pr :=
    (isPullback_section sq hx hy hxy).flip
  have hcycle : cycleAssociatedToClosedSubscheme (fieldChowSituation K) q y 0 =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) q (pullback.snd x pr) 0 :=
    cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) q y (pullback.snd x pr)
      hpb.isoPullback hpb.isoPullback_hom_snd 0
  change baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl p sq 0
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p x 0)) =
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) q 0)
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) q y 0)
  rw [baseChangeChowPullbackOfIsPullback_mk, hcycle,
    baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme
      (fieldExtensionBaseChangeSituation k K) rfl p sq x 0 hdim]

/-- **Base change along a field extension carries a difference of classes of rational points to
the difference of the classes of the induced rational points.** This is
`Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass` at each of the
two points, the base-change map being a homomorphism of abelian groups. -/
theorem baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub (k K : Type u) [Field k]
    [Field K] [Algebra k K] {X Y : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType p] {pr : Y ⟶ X} {q : Y ⟶ (fieldChowSituation K).S}
    [LocallyOfFiniteType q]
    (sq : IsPullback pr q p (fieldExtensionBaseChangeSituation k K).g)
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S)
    (x' : (fieldChowSituation k).S ⟶ X) (hx' : x' ≫ p = 𝟙 (fieldChowSituation k).S)
    (y : (fieldChowSituation K).S ⟶ Y) (hy : y ≫ q = 𝟙 (fieldChowSituation K).S)
    (hxy : y ≫ pr = (fieldExtensionBaseChangeSituation k K).g ≫ x)
    (y' : (fieldChowSituation K).S ⟶ Y) (hy' : y' ≫ q = 𝟙 (fieldChowSituation K).S)
    (hxy' : y' ≫ pr = (fieldExtensionBaseChangeSituation k K).g ≫ x') :
    baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl p sq 0
        (rationalPointChowClass k p x hx - rationalPointChowClass k p x' hx') =
      rationalPointChowClass K q y hy - rationalPointChowClass K q y' hy' := by
  rw [map_sub, baseChangeChowPullbackOfIsPullback_rationalPointChowClass k K p sq x hx y hy hxy,
    baseChangeChowPullbackOfIsPullback_rationalPointChowClass k K p sq x' hx' y' hy' hxy']

end Stacks.WeilCohomology

end
