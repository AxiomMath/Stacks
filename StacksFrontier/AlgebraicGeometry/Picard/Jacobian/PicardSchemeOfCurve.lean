module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PicardSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.HilbertInSite

/-!
# The Picard functor of a smooth projective curve is representable, given its Hilbert scheme

`AlgebraicGeometry.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed` proves
that the Picard functor of a smooth projective curve over a separably closed field is
representable, taking as arguments the statements of [Stacks, Tag 0A1H] and of description (2)
of [Stacks, Tag 0BDK], together with a scheme representing `Hilb^g_{X/k}`. The first two are
proved in this library, as
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap` and
`AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback`, and
are supplied here; what remains is the representing scheme of the Hilbert functor of degree `g`,
which is data of the statement as in [Stacks, Tag 0B9X].

## Main results

* `AlgebraicGeometry.RigidifiedPicard.isRepresentable_picardFunctor_of_representsHilbert`.
* `Stacks.PicardFunctor.isRepresentable_picardFunctor_of_isAlgClosed`: the Picard functor of a
  smooth projective curve over an algebraically closed field is representable, on every big fppf
  site containing the curve and `Spec k`; the Hilbert scheme of degree `g` is
  `Stacks.Hilbert.hilbSiteObject`.

## References

* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RigidifiedPicard

/-- **The Picard functor of a smooth projective curve over a separably closed field is
representable**, as soon as a scheme `H` of the site represents `Hilb^g_{X/k}`, `g` the genus. -/
theorem isRepresentable_picardFunctor_of_representsHilbert (B : BigFppfSite.{u}) {k : Type u}
    [Field k] [IsSepClosed k] {X : Scheme.{u}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f)
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) (genus f)) :
    (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).IsRepresentable :=
  isRepresentable_picardFunctor_of_isSepClosed
    (fun f hf E hE G hG =>
      isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf E hE G hG)
    (fun E hE i r _ h =>
      Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback E i r hE h)
    B hX hk f H hH

end AlgebraicGeometry.RigidifiedPicard

namespace Stacks.PicardFunctor

open _root_.AlgebraicGeometry

/-- **The Picard functor of a smooth projective curve over an algebraically closed field is
representable.** Let `k` be algebraically closed and `f : X ⟶ Spec k` a smooth projective curve;
on every big fppf site containing `X` and `Spec k` the Picard functor `Pic_{X/k}` is representable.
This is the statement of [Stacks, Tag 0B9Z] over an algebraically closed field (that tag is not
registered here). -/
theorem isRepresentable_picardFunctor_of_isAlgClosed (B : BigFppfSite.{u}) {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] :
    (picardFunctor B hX hk (ObjectProperty.homMk f)).IsRepresentable :=
  RigidifiedPicard.isRepresentable_picardFunctor_of_representsHilbert B hX hk f
    (Stacks.Hilbert.hilbSiteObject B hk f (genus f))
    (Stacks.Hilbert.representsHilbSiteObject B hk f (genus f))

end Stacks.PicardFunctor

end
