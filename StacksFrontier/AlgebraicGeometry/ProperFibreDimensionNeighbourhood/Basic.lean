module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# A neighbourhood on which the fibres of a proper morphism keep a dimension bound

For a proper morphism `f : X ⟶ Y` and a point `y` of `Y` whose fibre has dimension at most `d`,
there is an affine open neighbourhood `V` of `y` over which *every* fibre has dimension at most
`d`, and the restricted morphism `f ∣_ V` has quasi-compact and quasi-separated source and
target.

This is the first paragraph of the Stacks Project's proof of
[Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D), and it is the whole of that tag's part (2)
except for the vanishing conclusion; see the implementation notes.

## Main results

* `exists_affineOpen_fiberDimension_le`: the neighbourhood, with the dimension bound and the four
  compactness and quasi-separatedness properties.

## Implementation notes

The openness input is `isOpen_setOf_fiberDimensionAt_le` (Tag 02FZ), which is about the *local*
dimension `topologicalKrullDimAt` of the fibre at a point of the source.  Converting between that
and the dimension of the whole fibre is `topologicalKrullDim_eq_iSup_localKrullDim` together with
`topologicalKrullDimAt_eq_localKrullDim`, and comparing the fibre over `f x` with the fibre over
`y` when `f x = y` is done with the homeomorphism built from `Scheme.Hom.fiberHomeo`, as in
`exists_topologicalKrullDim_fiber_le`.  Rewriting the *type* `f.fiber (f x)` into `f.fiber y`
directly is what that homeomorphism avoids.

Properness enters twice and in two different ways: through `LocallyOfFiniteType`, which Tag 02FZ
requires, and through `Scheme.Hom.isClosedMap`, which turns the open set where the dimension bound
holds into an open set of the *base*.  Neither can be dropped: without finite type the locus need
not be open, and without closedness its complement's image need not be closed.

**What this does not prove, and why no Stacks attribute for Tag 0E7D is attached here.**
Part (2) of Tag 0E7D asks for a neighbourhood satisfying the hypotheses *and the conclusions* of
Tag 0EX3, and the conclusion is the universal vanishing
`IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)` for every `i > d` and
every quasi-coherent `F` on `f ⁻¹ᵁ V`.  That is the substance of the tag and is not proved here;
it is the one remaining part of the tag, and the tag is therefore not attached to this
file.  Part (1) of the tag follows from part (2) and so is also outstanding.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFibreDimension

variable {X Y : Scheme.{u}}

/-- The fibre of `f` over `y` is homeomorphic to the fibre over `f x` when `f x = y`. -/
public noncomputable def fiberHomeoOfEq (f : X ⟶ Y) {x : X} {y : Y} (hx : f x = y) :
    f.fiber y ≃ₜ f.fiber (f x) :=
  (f.fiberHomeo y).trans <| (Homeomorph.setCongr (by rw [hx])).trans (f.fiberHomeo (f x)).symm

/-- A point of the source lies over `y` precisely when it is in the image of the fibre, and then
its local fibre dimension is bounded by the dimension of the fibre over `y`. -/
public theorem topologicalKrullDimAt_asFiber_le (f : X ⟶ Y) {x : X} {y : Y} (hx : f x = y)
    (d : ℕ) (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞) := by
  refine le_trans ?_ hdim
  rw [topologicalKrullDimAt_eq_of_homeomorph (fiberHomeoOfEq f hx).symm (f.asFiber x)]
  exact topologicalKrullDimAt_le_topologicalKrullDim _

/-- The dimension of a fibre is bounded by `d` as soon as every point of the source lying over
the base point has local fibre dimension at most `d`. -/
public theorem topologicalKrullDim_fiber_le_of_forall (f : X ⟶ Y) (y : Y) (d : ℕ)
    (h : ∀ x : X, f x = y →
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  have hxy : f (f.fiberι y z) = y := by
    have h' := congrArg (fun q : f.fiber y ⟶ Y ↦ q z) (f.fiber_fac y)
    simpa [Scheme.Hom.comp_apply] using h'
  have hz : (fiberHomeoOfEq f hxy) z = f.asFiber (f.fiberι y z) := by
    apply (f.fiberι (f (f.fiberι y z))).isEmbedding.injective
    rfl
  rw [topologicalKrullDimAt_eq_of_homeomorph (fiberHomeoOfEq f hxy) z, hz]
  exact h (f.fiberι y z) hxy

/-- **The fibre-dimension neighbourhood of Stacks Tag 0E7D, part (2).**  For `f` proper and `y`
a point of the base whose fibre has dimension at most `d`, there is an affine open neighbourhood
`V` of `y` over which every fibre has dimension at most `d`, and both `V` and `f ⁻¹ᵁ V` are
quasi-compact and quasi-separated.

The vanishing conclusion of part (2) is *not* included; see the module documentation. -/
public theorem exists_affineOpen_fiberDimension_le (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      ∀ y' ∈ V, topologicalKrullDim (f.fiber y') ≤ (d : WithBot ℕ∞) := by
  classical
  -- The locus in the source where the local fibre dimension is at most `d` is open.
  set Ω : Set X := {x : X |
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)} with hΩ
  have hΩopen : IsOpen Ω := isOpen_setOf_fiberDimensionAt_le f d
  -- Its complement is closed, so has closed image: `f` is proper, hence a closed map.
  have hWopen : IsOpen ((f '' Ωᶜ)ᶜ) :=
    (f.isClosedMap _ (isClosed_compl_iff.2 hΩopen)).isOpen_compl
  have hyW : y ∈ (f '' Ωᶜ)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (topologicalKrullDimAt_asFiber_le f hxy d hdim)
  -- Choose an affine open neighbourhood of `y` inside that open set.
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨(f '' Ωᶜ)ᶜ, hWopen⟩) hyW
  have : IsAffine V.toScheme := hVaff
  have : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  refine ⟨V, hyV, hVaff, ‹_›, ‹_›, inferInstance, inferInstance, fun y' hy' => ?_⟩
  refine topologicalKrullDim_fiber_le_of_forall f y' d fun x hx => ?_
  by_contra hcon
  exact hVW (hx ▸ hy') ⟨x, hcon, hx⟩

end Stacks.AlgebraicGeometry.ProperFibreDimension

end
