module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Curve
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent

/-!
# The Hilbert scheme of points of a smooth proper curve as an object of a big fppf site

Let `k` be an algebraically closed field and `X` a smooth proper curve over `k`, with structure
morphism `f : X ⟶ Spec k`. The Hilbert scheme `Hilb^d_{X/k}` (`Stacks.Hilbert.hilbOver`) is
proper over `k` (part (1) of [Stacks, Tag 0B9I]), hence quasi-compact and of finite type over
`Spec k`. A scheme quasi-compact and of finite type over a scheme of a big fppf site `B` belongs
to `B` ([Stacks, Tag 000R], (5)), so `Hilb^d_{X/k}` is an object of the big fppf site of `Spec k`
whenever `Spec k` is, and it represents the Hilbert functor of degree `d` there. This is the
representing object of the Hilbert functor on `(Sch/k)_{fppf}` used in the proof of
[Stacks, Tag 0B9X].

## Main results

* `Stacks.Hilbert.contains_hilbOver_left`: every big fppf site containing `Spec k` contains
  `Hilb^d_{X/k}`.
* `Stacks.Hilbert.hilbSiteObject`: `Hilb^d_{X/k}` as an object of the big fppf site over `Spec k`.
* `Stacks.Hilbert.representsHilbSiteObject`: it represents `Hilb^d_{X/k}`.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f]

include hk in
/-- **A big fppf site containing `Spec k` contains the Hilbert scheme of points of a smooth
proper curve over `k`**: `Hilb^d_{X/k}` is proper over `k`, so it is quasi-compact and of finite
type over `Spec k`. -/
theorem contains_hilbOver_left (d : ℕ) : B.Contains (hilbOver (Over.mk f) d).left := by
  have := (hilbOver_isProper_smooth_irreducible_dim f d).1
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (hilbOver (Over.mk f) d).hom hk

/-- **The Hilbert scheme of points `Hilb^d_{X/k}` of a smooth proper curve, as an object of the
big fppf site over `Spec k`.** Its underlying scheme over `Spec k` is `hilbOver (Over.mk f) d`. -/
def hilbSiteObject (d : ℕ) : BigFppfOver B (Spec (.of k)) hk :=
  siteObject B (Spec (.of k)) hk (contains_hilbOver_left B hk f d) (hilbOver (Over.mk f) d).hom

/-- **The site object `hilbSiteObject` represents the Hilbert functor of points of degree `d`.**
Its image in the `k`-schemes is `hilbOver (Over.mk f) d`, which represents it by
`Stacks.Hilbert.representsHilbOver`. -/
def representsHilbSiteObject (d : ℕ) :
    RepresentsHilbertFunctorOfRank (Over.mk f)
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj (hilbSiteObject B hk f d)) d :=
  representsHilbOver (Over.mk f) d

end Stacks.Hilbert

end
