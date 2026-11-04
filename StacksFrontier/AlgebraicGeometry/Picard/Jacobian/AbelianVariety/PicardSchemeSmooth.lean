module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.RankOneLocusChart
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.ChartCriterion
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMapCriterion
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.HilbertInSite

/-!
# The Picard scheme of a smooth projective curve is smooth of dimension the genus

Let `X` be a smooth projective curve of genus `g` over an algebraically closed field `k`, and
let `P` be a scheme of a big fppf site representing its Picard functor. Then `P` is smooth of
relative dimension `g` over `k`, and so is its degree-zero open subgroup scheme `Pic⁰_{X/k}`.

This is the first step of the proof of [Stacks, Tag 0BA0]: the open `W` of the Hilbert scheme
`Hilb^g_{X/k}` of [Stacks, Tag 0B9X] is an open chart of `P` and its translates by `k`-points
cover `P` ([Stacks, Tag 0B9Y]); `Hilb^g_{X/k}` is smooth of relative dimension `g`
([Stacks, Tag 0B9H], via `Stacks.Hilbert.isProper_smooth_irreducible_dim_of_represents`), hence
so is `W`, hence so is `P` (`Stacks.PicardFunctor.smoothOfRelativeDimension_of_representsOpen`).

## Main results

* `Stacks.PicardFunctor.smoothOfRelativeDimension_of_representsHilbert`: `P` is smooth of
  relative dimension `g`, for any object of the site representing `Hilb^g_{X/k}`.
* `Stacks.PicardFunctor.smoothOfRelativeDimension_degreeZeroOpenSubgroupScheme_of_representsHilbert`
  : the same for `Pic⁰_{X/k}`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B9H](https://stacks.math.columbia.edu/tag/0B9H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  AlgebraicGeometry

open scoped CategoryTheory.MonObj

open CategoryTheory.CartesianMonoidalCategory

universe u

namespace Stacks.PicardFunctor

attribute [local instance] bigFppfOverCartesianMonoidal

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]
  {P : BigFppfOver B (Spec (.of k)) hk} (R : (picardFunctor B hX hk g).RepresentableBy P)

include R in
/-- **The Picard scheme of a smooth projective curve is smooth of relative dimension the
genus**, given an object `Hb` of the site representing `Hilb^g_{X/k}`. -/
theorem smoothOfRelativeDimension_of_representsHilbert {Hb : BigFppfOver B (Spec (.of k)) hk}
    (hHb : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb) (genus (B.inclusion.map g))) :
    SmoothOfRelativeDimension (genus (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P).hom := by
  set f := B.inclusion.map g
  have : IsProper f := inferInstance
  obtain ⟨F, W, i, j, hio, hopen, hjF, hjsurj, hjinj, hcov⟩ :=
    exists_rankOneChart B hX hk f R hHb
  obtain ⟨-, hsm, -, -, -⟩ := Stacks.Hilbert.isProper_smooth_irreducible_dim_of_represents f
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isCurve f) hHb
  have := hsm
  have : IsOpenImmersion ((BigFppfOver.toOver B (Spec (.of k)) hk).map i).left := hio
  have hW : SmoothOfRelativeDimension (genus f)
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj W).hom := by
    rw [← Over.w ((BigFppfOver.toOver B (Spec (.of k)) hk).map i)]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + genus f)
      (((BigFppfOver.toOver B (Spec (.of k)) hk).map i).left ≫
        ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).hom))
  refine smoothOfRelativeDimension_of_representsOpen R (genus f) F hopen j hjF hjsurj hjinj
    (fun p => ?_) hW
  obtain ⟨T, x, t, r, hxt, hF⟩ := hcov p
  exact ⟨T, x, t, r, hxt, hF (toUnit T)⟩

include R in
/-- **The Picard scheme of a smooth projective curve is smooth of relative dimension the
genus.** The Hilbert scheme `Hilb^g_{X/k}` is an object of every big fppf site containing
`Spec k`, where it represents `Hilb^g_{X/k}` (`Stacks.Hilbert.representsHilbSiteObject`). -/
theorem smoothOfRelativeDimension_picardScheme_of_representableBy :
    SmoothOfRelativeDimension (genus (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P).hom := by
  have : IsProper (B.inclusion.map g) := inferInstance
  exact smoothOfRelativeDimension_of_representsHilbert B hX k g R
    (Stacks.Hilbert.representsHilbSiteObject B hk (B.inclusion.map g) (genus (B.inclusion.map g)))

end Stacks.PicardFunctor

end
