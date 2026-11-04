module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# The formal disk over a field and its coordinate involution

The *formal disk* over a field `k` is the spectrum of the ring of formal power series in one
variable over `k`, regarded as a scheme over `Spec k`. Its coordinate is the power-series
variable, and the automorphism `f(X) ↦ f(-X)` of the power-series ring gives an involution of
the disk negating that coordinate. The disk is the test object that distinguishes a
set-theoretically invariant morphism out of the affine line from an invariant one, for the
involution relation of `AlgebraicGeometry.AffineLineInvolution`.

## Main definitions

* `AlgebraicGeometry.formalDisk` is the formal disk over `k`, as a scheme over `Spec k`.
* `AlgebraicGeometry.diskCoordinate` and `AlgebraicGeometry.diskNegativeCoordinate` are the
  two morphisms to the affine line given by the power-series variable and its negative.
* `AlgebraicGeometry.diskNegation` is the involution of the disk negating the coordinate.
* `AlgebraicGeometry.siteFormalDisk` and `AlgebraicGeometry.siteDiskNegation` present the
  disk and its involution in a big fppf site containing both `Spec k` and the disk.

## Main results

* `AlgebraicGeometry.formalDisk_hasEtaleLocalProperty_isReduced`: the presheaf represented by
  the formal disk in the site is reduced, the identity being a surjective étale atlas by a
  reduced scheme.

## Implementation notes

The disk is a *scheme* over `Spec k` rather than an object of a site, because the site has a
size cutoff which the power-series ring need not respect; `siteFormalDisk` takes the
containment as a hypothesis. The involution is the `Spec` of
`PowerSeries.rescale (-1 : k)`, whose compatibility with the structure morphism is checked
coefficientwise.

## References

* [Stacks Project, Tag 048Z](https://stacks.math.columbia.edu/tag/048Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open AffineLineInvolution

variable (k : Type u) [Field k]

/-- The formal disk over `k`: the spectrum of the ring of formal power series in one variable,
as a scheme over `Spec k`. -/
noncomputable abbrev formalDisk : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))))

/-- The coordinate of the formal disk, the power-series variable, read as a morphism to the
affine line. -/
noncomputable def diskCoordinate : formalDisk k ⟶ affineLine k :=
  Over.homMk
    (AffineSpace.homOfVector (formalDisk k).hom
      (fun _ : PUnit.{u + 1} =>
        (Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X))

/-- The negative of the coordinate of the formal disk, read as a morphism to the affine
line. -/
noncomputable def diskNegativeCoordinate : formalDisk k ⟶ affineLine k :=
  Over.homMk
    (AffineSpace.homOfVector (formalDisk k).hom
      (fun _ : PUnit.{u + 1} =>
        (Scheme.ΓSpecIso (.of (PowerSeries k))).inv (-PowerSeries.X)))

/-- Negation of the formal coordinate: the involution of the formal disk induced by the
power-series automorphism `f(X) ↦ f(-X)`. -/
noncomputable def diskNegation : formalDisk k ⟶ formalDisk k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.rescale (-1 : k))))
    (by
      have h : CommRingCat.ofHom (algebraMap k (PowerSeries k)) ≫
          CommRingCat.ofHom (PowerSeries.rescale (-1 : k)) =
          CommRingCat.ofHom (algebraMap k (PowerSeries k)) := by
        ext x n
        cases n with
        | zero => simp
        | succ n => simp
      change Spec.map (CommRingCat.ofHom (PowerSeries.rescale (-1 : k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k))) = _
      rw [← Spec.map_comp]
      exact congrArg Spec.map h)

/-- The formal disk as an object of a big fppf site over `Spec k` which contains it. -/
noncomputable def siteFormalDisk (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hD : B.Contains (Spec (.of (PowerSeries k)))) : BigFppfOver B (Spec (.of k)) hS :=
  Over.mk (ObjectProperty.homMk (formalDisk k).hom : B.obj hD ⟶ B.obj hS)

/-- Negation on the formal disk, as an endomorphism of its object in the site. -/
noncomputable def siteDiskNegation (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hD : B.Contains (Spec (.of (PowerSeries k)))) :
    siteFormalDisk k B hS hD ⟶ siteFormalDisk k B hS hD :=
  Over.homMk (ObjectProperty.homMk (diskNegation k).left)
    (by
      change (ObjectProperty.homMk
          ((diskNegation k).left ≫ (formalDisk k).hom) : B.obj hD ⟶ B.obj hS) =
        ObjectProperty.homMk (formalDisk k).hom
      exact congrArg (fun f : (formalDisk k).left ⟶ Spec (.of k) =>
        (ObjectProperty.homMk f : B.obj hD ⟶ B.obj hS)) (diskNegation k).w)

/-- The presheaf represented by the formal disk in the site is reduced: its identity is a
surjective étale atlas by a reduced scheme. -/
theorem formalDisk_hasEtaleLocalProperty_isReduced (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) (hD : B.Contains (Spec (.of (PowerSeries k)))) :
    Space.HasEtaleLocalProperty B (Spec (.of k)) hS
      (yoneda.obj (siteFormalDisk k B hS hD)) (fun T : Scheme.{u} ↦ IsReduced T) := by
  refine ⟨siteFormalDisk k B hS hD, 𝟙 _, ?_, ?_, ?_⟩
  · refine presheaf_id_of_iso B _ hS _ ?_ _
    intro _ _ f hf
    have : IsIso ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f) := by
      have := hf
      infer_instance
    change Surjective ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f)
    infer_instance
  · refine presheaf_id_of_iso B _ hS _ ?_ _
    intro _ _ f hf
    have : IsIso ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f) := by
      have := hf
      infer_instance
    change Etale ((BigFppfOver.toScheme B (Spec (.of k)) hS).map f)
    infer_instance
  · change IsReduced (Spec (.of (PowerSeries k)))
    exact (affine_isReduced_iff _).2 (by infer_instance)

end AlgebraicGeometry

end
