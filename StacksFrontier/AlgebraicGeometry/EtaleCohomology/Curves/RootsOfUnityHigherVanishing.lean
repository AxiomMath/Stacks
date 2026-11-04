module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
import StacksCore.Tactic.StacksAttribute

/-!
# Higher vanishing for the roots of unity on a smooth curve

Let `X` be a smooth curve over an algebraically closed field `k` and let `n` be invertible on
`X`. Then

`H^q_étale(X, μ_n) = 0` for every `q ≥ 3`.

This is the part of clause (3) of [Stacks, Tag 03RR] — and of the `q ≥ 3` clause of
[Stacks, Tag 03RQ] — that the library can reach. The argument is the source's: the Kummer
sequence `0 → μ_n → 𝐆_m → 𝐆_m → 0` is short exact on the small étale site of `X` when `n` is
invertible there, `Stacks.Kummer.kummerSequence_shortExact`, and its long exact sequence has
the segment

`H^{q-1}(X, 𝐆_m) → H^q(X, μ_n) → H^q(X, 𝐆_m)`

whose two outer groups both vanish by [Stacks, Tag 03RM] once `q - 1 ≥ 2`, that is once
`q ≥ 3`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve` — the vanishing
  above, unconditionally. It carries the `q ≥ 3` clause of the first list of
  [Stacks, Tag 03RQ].

## Implementation notes

**This file registers the `q ≥ 3` clause of the first list of [Stacks, Tag 03RQ]**, and the
statement is UNCONDITIONAL: nothing is assumed beyond the source's own hypotheses.

In particular the unrestricted [Stacks, Tag 03Q9] is not needed, and the reason is more
interesting than a missing lemma being supplied: Tag 03RM does not need Tag 03Q9 at any
strength. `R^q j_* 𝐆_m` is the sheafification of
`V ↦ H^q(Spec K ×_X V, 𝐆_m)` by [Stacks, Tag 03Q8], and at an individual étale neighbourhood
`Spec K ×_X V` is already étale over `Spec K`, hence a coproduct of spectra of finite separable
extensions by [Stacks, Tag 02GL]. The limit over neighbourhoods that the source passes to — the
step Tag 03Q9 is about — is therefore never formed, and Tag 03RG at each extension finishes it.

Tag 03RM is *not* among the hypotheses: it is consumed in its proved, unconditional form —
the fundamental exact sequence [Stacks, Tag 03RI] is proved as
`Stacks.EtaleCohomology.fundamentalSequence_shortExact`, Tag 03RG as
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_functionField`, and
[Stacks, Tag 03RJ] as
`Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf`, which
does not need [Stacks, Tag 03Q9] at all.

The tag on the statement below is the `q ≥ 3` clause of Tag 03RQ's first list alone. It is not a
covering set for either Tag 03RQ or clause (3) of Tag 03RR: degree two, which both include, is a
different input and is not covered here. The other clauses each tag reaches are registered in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.RootsOfUnity`,
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegrees`.

**Why `q ≥ 3` and not `q ≥ 2`.** The same segment in degree `2` reads
`H¹(X, 𝐆_m) --·n--> H¹(X, 𝐆_m) → H²(X, μ_n) → H²(X, 𝐆_m) = 0`, so it identifies
`H²_étale(X, μ_n)` with `Pic(X)/n·Pic(X)` rather than killing it; the vanishing in degree two
is the `n`-divisibility of `Pic(X)`, which is a different input altogether. For the affine curve
of Tag 03RR it comes from the surjection `Pic⁰(X̄) ↠ Pic(X)` and the divisibility of `Pic⁰(X̄)`,
hence from [Stacks, Tag 03RP] and the Picard scheme of [Stacks, Tag 0BA0]. Of Tag 03RP the
library has three registrations: commutativity on
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, clause (3) that `[d]` is
onto as `Stacks.Groupoids.surjective_zpow_id_left_of_flat`, and clause (4) that `A(k)` is
divisible as `Stacks.Groupoids.exists_zpow_eq_of_flat`, each of the last two over the flatness of
`[d]`; and `Stacks.Groupoids.exists_nsmul_eq_of_surjective` transports clause (4) to any additive
group that `A(k)` surjects onto, which is the shape a consumer here would use. Of Tag 0BA0 the
library has eleven registrations, covering clauses (1) to (6). What is still missing is the one
thing those cannot supply between them: an `AlgebraicGeometry.IsAbelianVariety` structure on the
degree-zero Picard scheme of the curve, so that clause (4) has an abelian variety to be applied
to. `AlgebraicGeometry.picardScheme` is `(picardFunctor …).reprX`, conditional on a
representability instance the development lacks, and carries no `CategoryTheory.GrpObj`. So
degree two is not a missing application but missing mathematics, and the vanishing in that degree
is not asserted here in any form. What degree two *does* have, on this site, is
`Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve`, the
`H² = 𝐙/n𝐙` of Tag 03RQ over the divisibility input named explicitly, and nothing else — it no
longer carries any form of [Stacks, Tag 03Q9] either.

No affineness is assumed: the vanishing holds for every smooth curve over the algebraically
closed field, which covers both the affine curve of Tag 03RR and the projective curve of Tag
03RQ.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR): clause (3), the
  vanishing for an affine smooth curve.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ): the `q ≥ 3` clause,
  for a smooth projective curve.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing for
  `𝐆_m`, which this transports across the Kummer sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The pinned instance at the coefficient universe `u + 1`

`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve` is stated with its
coefficient universe pinned to `u + 1`, behind a `local instance` that does not leave its file.
The same pin is needed here to elaborate `Sheaf.H` at that universe. -/

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The higher roots-of-unity cohomology of a smooth curve vanishes from degree three on.**
Let `X` be a smooth curve over an algebraically closed field `k` and let `n` be invertible in
the ring of global functions on `X`. Then `H^q_étale(X, μ_n) = 0` for every `q ≥ 3`.

This is the Kummer long exact sequence applied to
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve` in the two
consecutive degrees `q - 1` and `q`, both of which are at least two exactly when `q ≥ 3`.

Nothing is carried. Degree two is not covered and is not asserted here: it is the
`n`-divisibility of `Pic⁰(X)`, a separate input, and on this site it is
`Stacks.EtaleCohomology.nonempty_sheafH_rootsOfUnitySheaf_two_addEquivZMod_smoothCurve`.

This is a partial form of [Stacks, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ); the full
statement is `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`. -/
@[sga "4 IX 4.6" "special case"]
theorem subsingleton_sheafH_rootsOfUnitySheaf_smoothCurve {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
    [Smooth g] {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(X, ⊤)))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} X n) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
  exact Stacks.Cohomology.subsingleton_sheafH_X₁_of_shortExact
    (Stacks.Kummer.kummerSequence_shortExact.{u, u + 1} X hn0 hn) p (p + 1) rfl
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g (p + 1) (by lia))
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g p (by lia))

end Stacks.EtaleCohomology

end
