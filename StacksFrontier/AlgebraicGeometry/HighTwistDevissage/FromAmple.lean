module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.AffineFromNegativeTwists
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# The dévissage sequence of Stacks Tag 0EBD is no longer a hypothesis

`./AffineFromNegativeTwists.lean` proves [Stacks, Tag 0EBD] — a scheme carrying an ample
invertible module whose sufficiently negative tensor powers have no higher cohomology is affine —
on five named hypotheses, one of which is the dévissage sequence of clause (8) of
[Stacks, Tag 01Q3], written out inline as

`∀ F, F.IsQuasicoherent → F.IsFiniteType → ∃ S r d b …, S.ShortExact ∧ S.X₃ = F ∧ …`.

That is `Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists X L` applied at `n₀`, and it is
now a theorem for every scheme with an ample invertible module
(`Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`). This file discharges it, so
Tag 0EBD rests on four hypotheses instead of five and the vanishing theorem it is built from on
three instead of four.

## Main results

* `Stacks.HighTwistDevissage.isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower_of_isAmple`:
  the positive-degree cohomology of every quasi-coherent module vanishes, on the tag's own
  vanishing hypothesis, a cohomological dimension bound and the colimit reduction — the dévissage
  sequence is supplied.
* `Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower_of_isAmple`:
  **[Stacks, Tag 0EBD] on four hypotheses**: its own vanishing hypothesis, Serre's criterion
  ([Stacks, Tag 01XF]), the cohomological dimension bound ([Stacks, Tag 01XI]) and the colimit
  reduction ([Stacks, Tag 01PG]).

## Implementation notes

The ampleness hypothesis was already present in
`Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`, so Tag 0EBD loses
a hypothesis at no cost; the vanishing theorem it is built from did not assume ampleness, and
gains it here, which is why the two are given separate names rather than the second being restated.

No `@[stacks]` attribute is attached: the attribute for Tag 0EBD sits on the declarations of
`./AffineFromNegativeTwists.lean`, and what changes here is only the number of hypotheses they
carry.

## References

* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.HighTwistDevissage

attribute [local instance] _root_.HasDerivedCategory.standard

-- Seated from `OpensSheafificationInstances`, not restated: sheafification for the site of
-- opens of a scheme, and its weak equivalences.
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable (X : Scheme.{u}) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The vanishing theorem behind [Stacks, Tag 0EBD], with the dévissage sequence supplied.**
For `L` ample, the positive-degree cohomology of every quasi-coherent module vanishes as soon as
the sufficiently negative tensor powers of `L` have none, there is a cohomological dimension
bound, and the cohomology of a quasi-coherent module is the colimit of that of its finite-type
submodules.

This is `Stacks.HighTwistDevissage.isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower` with
its `hgen` discharged by
`Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`. -/
theorem isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower_of_isAmple
    (hL : Stacks.Ample.IsAmple X L) {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    (e : ℕ)
    (hdim : ∀ (F : X.Modules) (p : ℕ), e < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F))
    (hcolim : ∀ p : ℕ, 0 < p → ∀ F : X.Modules, F.IsQuasicoherent →
      ∃ (J : Type u) (_ : SmallCategory J) (pres : ColimitPresentation J F),
        (∀ j, (pres.diag.obj j).IsQuasicoherent) ∧
        (∀ j, SheafOfModules.IsFiniteType.{u, u, u} (pres.diag.obj j)) ∧
        Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone pres.cocone)))
    (F : X.Modules) (p : ℕ) (hp : 0 < p) (hF : F.IsQuasicoherent) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower X L hvan e hdim
    (Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple L hL n₀) hcolim F p hp hF

/-- **[Stacks, Tag 0EBD] on four hypotheses instead of five.** A scheme carrying an ample
invertible module whose sufficiently negative tensor powers have no higher cohomology is affine.

The hypotheses left are the tag's own vanishing hypothesis, Serre's cohomological criterion for
affineness ([Stacks, Tag 01XF]), a cohomological vanishing bound on quasi-coherent modules
([Stacks, Tag 01XI]) and the colimit presentation of the cohomology of a quasi-coherent module
([Stacks, Tag 01PG]). The fifth, the dévissage sequence of clause (8) of [Stacks, Tag 01Q3], is
discharged. -/
theorem isAffine_of_isZero_cohomology_negative_tensorPower_of_isAmple
    (hL : Stacks.Ample.IsAmple X L) {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    (serre : CompactSpace ↥X →
      (∀ (F : X.Modules) (p : ℕ), 0 < p → F.IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ p F)) → IsAffine X)
    (e : ℕ)
    (hdim : ∀ (F : X.Modules) (p : ℕ), e < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F))
    (hcolim : ∀ p : ℕ, 0 < p → ∀ F : X.Modules, F.IsQuasicoherent →
      ∃ (J : Type u) (_ : SmallCategory J) (pres : ColimitPresentation J F),
        (∀ j, (pres.diag.obj j).IsQuasicoherent) ∧
        (∀ j, SheafOfModules.IsFiniteType.{u, u, u} (pres.diag.obj j)) ∧
        Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone pres.cocone))) :
    IsAffine X :=
  isAffine_of_isZero_cohomology_negative_tensorPower X L hL hvan serre e hdim
    (Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple L hL n₀) hcolim

end Stacks.HighTwistDevissage

end
