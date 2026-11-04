module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationOverDvr

/-!
# Closed points of a scheme-theoretic fibre

Two ways for a point to be closed in the scheme-theoretic fibre through it.

* If the point is closed in the total space, it is closed in its fibre: the fibre embeds in the
  total space, so the singleton is the preimage of a closed set.
* If the morphism is injective on points — for instance an open immersion, or an isomorphism —
  then the fibre has at most one point, so every point of it is closed with no hypothesis on the
  point at all.

These are the two ways the closedness hypothesis of the product dimension identity used in
**Stacks 0DS9** gets discharged: along a refinement of smooth charts, where the point is closed in
the chart, and along the shrinking of a chart to an open subscheme, where it is not.

## Main results

* `AlgebraicGeometry.isClosed_singleton_asFiber_of_isClosed`
* `AlgebraicGeometry.subsingleton_fiber_of_injective`
* `AlgebraicGeometry.isClosed_singleton_asFiber_of_injective`
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **A point closed in the total space is closed in its fibre.** The singleton of the point of
the fibre is the preimage of the singleton of the point under the embedding of the fibre, which
is injective and continuous. -/
theorem isClosed_singleton_asFiber_of_isClosed {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsClosed ({q.asFiber x} : Set (q.fiber (q x))) := by
  have hpre : ({q.asFiber x} : Set (q.fiber (q x))) =
      (q.fiberι (q x)).base ⁻¹' ({x} : Set X) := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    refine ⟨?_, fun hz => Scheme.Hom.fiberι_injective q (q x)
      (hz.trans (Scheme.Hom.fiberι_asFiber q x).symm)⟩
    rintro rfl
    exact Scheme.Hom.fiberι_asFiber q x
  rw [hpre]
  exact hx.preimage (q.fiberι (q x)).base.hom.continuous

/-- **The fibre of a morphism injective on points has at most one point.** Two points of the
fibre have the same image in the total space, because both lie over the given point of the
target and the morphism is injective; the embedding of the fibre is injective, so they are
equal. -/
theorem subsingleton_fiber_of_injective {X Y : Scheme.{u}} (q : X ⟶ Y)
    (hq : Function.Injective q.base) (y : Y) : Subsingleton (q.fiber y) := by
  have key (a : q.fiber y) : q.base (q.fiberι y a) = y := by
    have h := (q.fiberHomeo y a).2
    rwa [Scheme.Hom.fiberHomeo_apply] at h
  exact ⟨fun a b => Scheme.Hom.fiberι_injective q y (hq ((key a).trans (key b).symm))⟩

/-- **Every point of the fibre of a morphism injective on points is closed in that fibre**, with
no hypothesis on the point: the fibre has at most one point, so its singleton is the whole
space.

This is the case the shrinking step of Stacks 0DS9 needs, where a chart is replaced by an open
subscheme of it and the point is only a finite type point of the chart, never a closed one. -/
theorem isClosed_singleton_asFiber_of_injective {X Y : Scheme.{u}} (q : X ⟶ Y)
    (hq : Function.Injective q.base) (x : X) :
    IsClosed ({q.asFiber x} : Set (q.fiber (q x))) := by
  have := subsingleton_fiber_of_injective q hq (q x)
  exact isClosed_discrete _

end AlgebraicGeometry

end
