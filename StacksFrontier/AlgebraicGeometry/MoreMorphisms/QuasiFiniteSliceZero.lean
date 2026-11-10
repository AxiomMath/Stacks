module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# The relative dimension zero case of the slicing lemma

[Stacks, Tag 0570] is proved by induction on `d = dim_x(X_s)`, and this file supplies the base
case `d = 0` in the weakened form `AlgebraicGeometry.HasQuasiFiniteSlice` isolated in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlice`: the slice may be taken to be an
open neighbourhood of the point.

The argument is the source's. If the fibre has local dimension zero at `x` then `f` is
quasi-finite at `x` by [Stacks, Tag 0397], so `x` lies in the open locus of quasi-finiteness of
[Stacks, Tag 01TI]; `f` is also flat at `x`, so `x` lies in the open flat locus of
[Stacks, Tag 0399]. The intersection of the two is an open neighbourhood of `x` which is flat,
locally of finite presentation and locally quasi-finite over the base, and an open immersion is
an immersion.

Nothing here is tagged: this is one case of Tag 0570, not the lemma.

## Main results

* `AlgebraicGeometry.hasQuasiFiniteSlice_of_fiberDimensionAt_eq_zero` is the base case, with the
  relative dimension measured topologically.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk` identifies that
  topological measure with the Krull dimension of the local ring of the fibre, at a point closed
  in its fibre. This is [Stacks, Tag 0A21] applied to the fibre, which is locally of finite type
  over the residue field of its base point.
* `AlgebraicGeometry.hasQuasiFiniteSlice_of_isCohenMacaulayAt_of_ringKrullDim_eq_zero` is the
  base case with the hypotheses of `AlgebraicGeometry.HasQuasiFiniteSlices` together with the
  vanishing of `dim (O_{X_s, x})`.

## Implementation notes

The open neighbourhood is `AlgebraicGeometry.quasiFiniteLocus f` intersected with the flat locus
`{x | AlgebraicGeometry.IsFlatAt f x}`, which is open by
`AlgebraicGeometry.isOpen_setOf_isFlatAt`. Flatness of the restriction comes from
`AlgebraicGeometry.flat_of_subset_setOf_isFlatAt` and local quasi-finiteness from
`AlgebraicGeometry.locallyQuasiFinite_quasiFiniteLocus` composed with the open immersion of the
smaller open into the quasi-finite locus, using
`CategoryTheory.MorphismProperty.Respects @LocallyQuasiFinite @IsOpenImmersion`.

At a point closed in its fibre, the identification of the dimension of the fibre with the
dimension of its local ring is [Stacks, Tag 0A21] applied to the fibre.

## References

* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Tag 01TI](https://stacks.math.columbia.edu/tag/01TI)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The case `dim_x(X_s) = 0` of [Stacks, Tag 0570]**, in the weakened form
`AlgebraicGeometry.HasQuasiFiniteSlice`. A point at which a morphism locally of finite
presentation is flat and whose fibre has local dimension zero there has an open neighbourhood
which is flat, locally of finite presentation and locally quasi-finite over the base. -/
theorem hasQuasiFiniteSlice_of_fiberDimensionAt_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0) :
    HasQuasiFiniteSlice f x := by
  have hqf : quasiFiniteAt f x := (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mpr hdim
  let Q : X.Opens := quasiFiniteLocus f
  let F : X.Opens := ⟨{y : X | IsFlatAt f.toLRSHom.toShHom y}, isOpen_setOf_isFlatAt f⟩
  let Z : X.Opens := Q ⊓ F
  have hxZ : x ∈ Z := ⟨(mem_quasiFiniteLocus_iff f x).mpr hqf, hflat⟩
  have hqfZ : LocallyQuasiFinite (Z.ι ≫ f) := by
    rw [← X.homOfLE_ι (inf_le_left : Z ≤ Q), Category.assoc]
    infer_instance
  exact ⟨Z.toScheme, Z.ι, ⟨x, hxZ⟩, inferInstance, rfl,
    flat_of_subset_setOf_isFlatAt f Z fun y hy => hy.2, inferInstance, hqfZ⟩

/-- **[Stacks, Tag 0A21] applied to a fibre.** At a point which is closed in its fibre, the local
dimension of the fibre is the Krull dimension of the local ring of the fibre there: the fibre is
locally of finite type over the residue field of its base point. -/
theorem topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  exact topologicalKrullDimAt_eq_krullDimOfRing_stalk (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) (f.asFiber x) hclosed

/-- **The case `dim (O_{X_s, x}) = 0` of [Stacks, Tag 0570]**, in the weakened form
`AlgebraicGeometry.HasQuasiFiniteSlice` and with exactly the hypotheses of
`AlgebraicGeometry.HasQuasiFiniteSlices`: a point which is closed in its fibre, at which a
locally finitely presented morphism is Cohen–Macaulay, and whose fibre has a zero-dimensional
local ring there, admits a locally quasi-finite slice. -/
theorem hasQuasiFiniteSlice_of_isCohenMacaulayAt_of_ringKrullDim_eq_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y)) (hCM : f.IsCohenMacaulayAt hf x)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hdim : ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = 0) :
    HasQuasiFiniteSlice f x :=
  hasQuasiFiniteSlice_of_fiberDimensionAt_eq_zero f x hCM.1
    ((topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk f x hclosed).trans hdim)

end AlgebraicGeometry

end
