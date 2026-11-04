module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre dimension along a specialization

For a flat morphism locally of finite presentation, specializing from a point which is generic
in an irreducible component of its fibre preserves the local dimension of the fibre.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints`
  states invariance of local fibre dimension under such a specialization.

## Implementation notes

The points of the fibres corresponding to points of the source are represented by
`AlgebraicGeometry.Scheme.Hom.asFiber`. Membership in `genericPoints` expresses being the
generic point of an irreducible component. The proof locates the point in one of the pieces of
constant relative dimension supplied by
`AlgebraicGeometry.exists_open_relativeDimension_fiberwise_dense`, which is possible because
those pieces are fibrewise dense and a generic point of an irreducible component of a
Noetherian space lies in every dense open subset.

## References

* [Stacks Project, Tag 054U](https://stacks.math.columbia.edu/tag/054U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 054U.** For a flat morphism locally of finite presentation, local
dimension in the fibres is constant along a specialization whose endpoint is generic in an
irreducible component of its fibre. -/
@[stacks 054U, ega "IV 12.2.1.1" "partial"]
public theorem topologicalKrullDimAt_fiber_eq_of_specialization_of_mem_genericPoints
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    {x' x : X} (hxx : x' ⤳ x)
    (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    topologicalKrullDimAt (f.fiber (f x')) (f.asFiber x') =
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨U, hdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hopen : IsOpen ((f.fiberι (f x)) ⁻¹' (((iSup U : X.Opens) : Set X))) :=
    (iSup U).2.preimage (f.fiberι (f x)).continuous
  have hxm : x ∈ (((iSup U : X.Opens) : Set X)) := by
    have hm := scheme_genericPoints_mem_dense_open (f.fiber (f x)) hopen (hdense (f x)) hx
    simpa only [Set.mem_preimage, f.fiberι_asFiber] using hm
  obtain ⟨d, hxd⟩ : ∃ d, x ∈ U d := by
    change x ∈ (iSup U : X.Opens) at hxm
    exact Opens.mem_iSup.mp hxm
  exact (topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U d) d (hrel d) x'
      (hxx.mem_open (U d).2 hxd)).trans
    (topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U d) d (hrel d) x hxd).symm

/-! ### Nowhere density in fibres is topological

Nowhere density of a subset in a fibre is a condition on the underlying topology alone, so it is
transported by any homeomorphism of the situation. These three lemmas are stated here because the
spreading-out arguments which consume Stacks 054U need them and this is the common ancestor of
those arguments; they use nothing of the fibre dimension developed above.
-/

/-- Nowhere density in the fibre depends only on the point of the base. -/
public theorem isNowhereDense_fiberι_preimage_congr {X Y : Scheme.{u}} (f : X ⟶ Y) (y y' : Y)
    (h : y = y') (Z : Set X) (hnd : IsNowhereDense ((f.fiberι y) ⁻¹' Z)) :
    IsNowhereDense ((f.fiberι y') ⁻¹' Z) :=
  h ▸ hnd

/-- Nowhere density is invariant under a homeomorphism: interior and closure commute with the
image along it. -/
public theorem isNowhereDense_image_homeomorph_iff {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (S : Set A) : IsNowhereDense S ↔ IsNowhereDense (e '' S) := by
  rw [IsNowhereDense, IsNowhereDense]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := congrArg (fun T : Set A => e '' T) h
    rw [e.image_interior, e.image_closure] at h'
    simpa using h'
  · have h' := congrArg (fun T : Set B => e.symm '' T) h
    rw [e.symm.image_interior, e.symm.image_closure] at h'
    have himage : e.symm '' (e '' S) = S := by ext x; simp
    rw [himage] at h'
    simpa using h'

/-- Nowhere density in fibres is invariant under a homeomorphism of the whole situation: if
`a : X' ⟶ X` and `b : Y' ⟶ Y` are homeomorphisms making the square with `g : X' ⟶ Y'` and
`f : X ⟶ Y` commute on points, and `A ⊆ X'` is the preimage of `B ⊆ X` under `a`, then `A` is
nowhere dense in the fibre of `g` over `y'` exactly when `B` is nowhere dense in the fibre of `f`
over `b y'`. -/
public theorem isNowhereDense_fiberι_preimage_iff_of_isHomeomorph {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y) (ha : IsHomeomorph a)
    (hb : IsHomeomorph b) (hcomm : ∀ x', f (a x') = b (g x')) (y' : Y') (A : Set X') (B : Set X)
    (hA : ∀ x', x' ∈ A ↔ a x' ∈ B) :
    IsNowhereDense ((g.fiberι y') ⁻¹' A) ↔ IsNowhereDense ((f.fiberι (b y')) ⁻¹' B) := by
  let aH : X' ≃ₜ X := ha.homeomorph a
  have hsets : g ⁻¹' {y'} = a ⁻¹' (f ⁻¹' {b y'}) := by
    ext x'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hcomm]
    exact hb.injective.eq_iff.symm
  let e : g.fiber y' ≃ₜ f.fiber (b y') :=
    (g.fiberHomeo y').trans (aH.sets hsets) |>.trans (f.fiberHomeo (b y')).symm
  have heval (z : g.fiber y') : f.fiberι (b y') (e z) = a (g.fiberι y' z) := by
    change f.fiberι (b y') ((f.fiberHomeo (b y')).symm
      ((aH.sets hsets) ((g.fiberHomeo y') z))) = _
    rw [Scheme.Hom.fiberι_fiberHomeo_symm]
    rfl
  have himage : e '' ((g.fiberι y') ⁻¹' A) = (f.fiberι (b y')) ⁻¹' B := by
    ext z
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨z', hz', rfl⟩
      change f.fiberι (b y') (e z') ∈ B
      rw [heval]
      exact (hA _).mp hz'
    · refine ⟨e.symm z, ?_, by simp⟩
      change g.fiberι y' (e.symm z) ∈ A
      refine (hA _).mpr ?_
      rwa [← heval, e.apply_symm_apply]
  rw [← himage]
  exact isNowhereDense_image_homeomorph_iff e _

end AlgebraicGeometry
