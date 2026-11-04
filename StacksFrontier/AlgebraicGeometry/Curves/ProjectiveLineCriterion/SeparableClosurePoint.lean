module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A smooth scheme acquires a rational point over the separable closure

A nonempty smooth scheme `X` over a field `k` has a rational point after base change to a
separable closure `k^{sep}` of `k`: the base change `X_{k^{sep}}` is smooth and nonempty over the
separably closed field `k^{sep}`, so it has a closed point whose residue field is finite separable
over `k^{sep}` ([Stacks, Tag 056U]), hence equal to `k^{sep}`. The separably closed case is
`Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed`; this file adds the passage to
the separable closure. It is the step of the proof of [Stacks, Tag 0C6U] that finds a rational
point on a form of the projective line after a separable extension.

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.exists_section_pullback_separableClosure`: the base
  change of a nonempty smooth scheme to `k^{sep}` has a section.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

/-- **A nonempty smooth scheme over `k` has a rational point over a separable closure of `k`.**
The base change `X_{k^{sep}}` is smooth over the separably closed field `k^{sep}` and nonempty,
so it has a closed point with residue field `k^{sep}` (Tag 056U). -/
@[sga "6 X 7.18.2" "(a), special case"]
theorem exists_section_pullback_separableClosure (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [Nonempty X] :
    ∃ σ : Spec (.of (SeparableClosure k)) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))),
      σ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))) =
        𝟙 _ := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))) := by
    have : Subsingleton (Spec (CommRingCat.of k)) := by
      show Subsingleton (PrimeSpectrum k); infer_instance
    refine ⟨fun y => ?_⟩
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (SeparableClosure k))) := by
      show Nonempty (PrimeSpectrum (SeparableClosure k)); infer_instance
    exact ⟨x, Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨z, -⟩ := (pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).surjective x
  have : Nonempty (pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))) := ⟨z⟩
  exact Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed (SeparableClosure k) _

end AlgebraicGeometry.ProjectiveLineCriterion

end
