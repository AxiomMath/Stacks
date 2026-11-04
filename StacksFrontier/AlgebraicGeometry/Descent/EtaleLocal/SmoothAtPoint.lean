module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpen
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry

/-!
# Smoothness at a point is étale-local on the source

Let `g : Y ⟶ X` be an étale morphism of schemes and let `f : X ⟶ S`. A point `y` of `Y` is a
point of smoothness of `g ≫ f` exactly when its image `g y` is a point of smoothness of `f`.

## Main results

* `InfinitesimalLifting.smoothAt_iff_mem_largestOpen` — smoothness at a point is membership of
  the largest open on which the morphism is smooth, the open locus of Tag 0CEY.
* `InfinitesimalLifting.smoothAt_comp_iff_of_etale` — smoothness at a point is étale-local on
  the source.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 0CEY](https://stacks.math.columbia.edu/tag/0CEY)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace InfinitesimalLifting

/-- A morphism whose restriction to an open neighbourhood of a point is smooth is smooth at that
point. -/
theorem smoothAt_of_smooth_ι_comp {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {x : X}
    (hx : x ∈ U) (hU : Smooth (U.ι ≫ f)) : SmoothAt f x := by
  refine ⟨U, hx, ?_⟩
  have heq : f.resLE ⊤ U le_top = (U.ι ≫ f) ≫ (Scheme.topIso S).inv := by
    rw [← Scheme.Hom.resLE_comp_ι f (U := (⊤ : S.Opens)) (V := U) le_top]
    simp
  rw [heq]
  infer_instance

/-- A morphism is smooth at a point exactly when the point lies in the largest open of the source
on which the morphism is smooth. -/
theorem smoothAt_iff_mem_largestOpen {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    SmoothAt f x ↔ x ∈ largestOpen (@Smooth.{u}) f := by
  refine ⟨fun hf => ?_, fun hx => ?_⟩
  · obtain ⟨U, hxU, hU⟩ := AlgebraicGeometry.smoothAt_has_smooth_open_neighborhood f x hf
    exact le_sSup (show U ∈ {V : X.Opens | Smooth (V.ι ≫ f)} from hU) hxU
  · exact smoothAt_of_smooth_ι_comp f hx (largestOpen_isGreatest_etale (@Smooth.{u}) f).1

/-- Smoothness at a point is étale-local on the source: for an étale morphism `g : Y ⟶ X` and a
morphism `f : X ⟶ S`, a point of `Y` is a point of smoothness of `g ≫ f` exactly when its
image in `X` is a point of smoothness of `f`. -/
theorem smoothAt_comp_iff_of_etale {X Y S : Scheme.{u}} (g : Y ⟶ X) [Etale g] (f : X ⟶ S)
    (y : Y) : SmoothAt (g ≫ f) y ↔ SmoothAt f (g.base y) := by
  rw [smoothAt_iff_mem_largestOpen, smoothAt_iff_mem_largestOpen,
    ← preimage_largestOpen_etale (@Smooth.{u}) g f]
  exact Iff.rfl

/-- Smoothness at a point is inherited by the composite with an étale morphism. -/
theorem smoothAt_comp_of_etale {X Y S : Scheme.{u}} (g : Y ⟶ X) [Etale g] (f : X ⟶ S) (y : Y)
    (hf : SmoothAt f (g.base y)) : SmoothAt (g ≫ f) y :=
  (smoothAt_comp_iff_of_etale g f y).2 hf

end InfinitesimalLifting

end
