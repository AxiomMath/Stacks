module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.HProjective

/-!
# Tag 07RM's conclusion from an already-named gap

`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Basic.lean` reduces Stacks Tag
07RM to the condition `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` on a
projectivity predicate; at Definition 01W8's `AlgebraicGeometry.IsProjective` that condition
holds and the tag is proved, as
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`. At
`Stacks.HProjective.IsHProjective`, the predicate used here, it is not proved. This file shows
that for a morphism carrying an **absolutely** ample invertible module the conclusion
follows instead from `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, which is an
already-named hypothesis — it is what
`StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean` records as the missing input
of Stacks Tag 01VS — so this route adds no new hypothesis.

## This is not Tag 07RM's hypothesis, and the difference is the point

Tag 07RM's hypothesis is quasi-projectivity: a *relatively* ample invertible module on `X` over
`S`. `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` is stated for `Stacks.Ample.IsAmple X L`,
*absolute* ampleness on `X`, so the results below are **not** Tag 07RM. They are the same
conclusion under a different ampleness hypothesis, and they are recorded because:

* they need **no quasi-compactness and no quasi-separatedness of the base**, where the tag
  assumes both, and
* they exhibit a *satisfiable* route to the conclusion that does not go through
  `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`, so neither the conclusion nor
  the reduction in `Basic.lean` is vacuous.

The source's own route from relative ampleness, through [Stacks, Tag 01VU] (1) ⟹ (3)
(`Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`), is the
one `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs` takes; it
lands in Definition 01W8's projectivity, not in H-projectivity, so it does not give the results
below.

## Main results

* `Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple`: an absolutely ample
  invertible module on a scheme locally of finite type and quasi-compact over `S` makes the
  structure morphism H-quasi-projective, from `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`.
* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isAmple`: hence
  Tag 07RM's conclusion, at `Stacks.HProjective.IsHProjective`, under that hypothesis.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.QuasiProjectiveCompactification

/-- **H-quasi-projectivity from absolute ampleness**, given
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`.

That gap delivers, for every sufficiently high tensor power of `L`, an immersion `i : X ⟶ ℙⁿ_S`
over `S`. Only one such power is used. The immersion is quasi-compact because `f` is and
`ℙⁿ_S ⟶ S` is separated —
`Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated`, the use the source of
Tag 07RM makes of [Stacks, Tag 03GI] — and that is exactly H-quasi-projectivity. -/
theorem isHQuasiProjective_of_isAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [LocallyOfFiniteType f] (hqc : QuasiCompact f)
    (hgap : Stacks.AmpleProjectiveImmersion.ImmersionTwistGap f L
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L)) :
    Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨d₀, -, hd⟩ :=
    Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple f L hL hgap
  obtain ⟨n, i, hi, hif, -⟩ := hd d₀ le_rfl
  rw [← Stacks.HProjective.over_projectiveSpaceOver] at hif
  have hic : QuasiCompact (i ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hif]; exact hqc
  exact ⟨n, i, hi,
    quasiCompact_of_comp_isSeparated i (projectiveSpaceOver n S ↘ S) inferInstance hic, hif⟩

/-- **Tag 07RM's conclusion from absolute ampleness**, given
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`: the morphism factors as an open immersion
followed by an H-projective morphism.

This is `Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` followed by
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`. The hypothesis is
absolute, not relative, ampleness; see the module documentation. -/
theorem exists_isOpenImmersion_isHProjective_of_isAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [LocallyOfFiniteType f] (hqc : QuasiCompact f)
    (hgap : Stacks.AmpleProjectiveImmersion.ImmersionTwistGap f L
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L)) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f :=
  exists_isOpenImmersion_isHProjective_of_isHQuasiProjective
    (isHQuasiProjective_of_isAmple f L hL hqc hgap)

end Stacks.QuasiProjectiveCompactification

end
