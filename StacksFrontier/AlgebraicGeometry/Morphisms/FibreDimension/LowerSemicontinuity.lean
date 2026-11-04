module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Semicontinuity.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne

/-!
# Lower semicontinuity of the dimension of the fibres of a flat morphism

For a flat morphism of finite presentation the dimension of the fibres is a lower semicontinuous
function on the base: if some fibre has dimension more than `b`, then so does every fibre over a
neighbourhood of that point.

The proof is the source's. A flat morphism locally of finite presentation admits open pieces
`U_d ⊆ X` of every relative dimension `d` whose union is dense in every fibre (Tag 054T). If the
fibre over `y` has dimension more than `b`, an irreducible component of that fibre of maximal
dimension has a generic point, which lies in the dense open union and hence in some `U_d`; by the
equidimensionality of the fibres of `U_d ⟶ Y` that `d` exceeds `b`. A flat morphism locally of
finite presentation is open, so the image of `U_d` is an open neighbourhood of `y`, and at every
point of it the fibre has dimension at least `d`.

## Main results

* `AlgebraicGeometry.lowerSemicontinuous_fiberDimension` is **Stacks Tag 0D4H**.

## Implementation notes

The hypothesis is finite presentation in the global sense of Tag 01TP,
`AlgebraicGeometry.FinitePresentation`; only its local part and the flatness are used, since
`AlgebraicGeometry.UniversallyOpen` and Tag 054T both follow from those.

That the local dimension of the fibre is constant on each piece `U_d` uses that a scheme of
finite type over a field whose irreducible components all have dimension `d` has local dimension
`d` at every point, which is Tag 0A21 applied to the fibres of `U_d ⟶ Y`.

## References

* [Stacks Project, Tag 0D4H](https://stacks.math.columbia.edu/tag/0D4H)
* [Stacks Project, Tag 054T](https://stacks.math.columbia.edu/tag/054T)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A dense open subset of a locally Noetherian scheme contains every generic point of an
irreducible component: the statement is local, and an affine open subscheme of a locally
Noetherian scheme is Noetherian. -/
private alias mem_of_mem_genericPoints_of_dense_scheme :=
  AlgebraicGeometry.scheme_genericPoints_mem_dense_open

/-- If a fibre has dimension more than `b`, then some piece of relative dimension exceeding `b`
has that point of the base in its image: the generic point of a component of the fibre of maximal
dimension lies in one of the pieces. -/
private theorem exists_relativeDimension_image_mem {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] (U : ℕ → X.Opens)
    (hdense : ∀ y : Y, Dense ((f.fiberι y) ⁻¹' ((iSup U : X.Opens) : Set X)))
    (hrel : ∀ d : ℕ, RelativeDimension ((U d).ι ≫ f) d) (b : WithBot ℕ∞) {y : Y}
    (hy : b < f.fiberDimension y) :
    ∃ d : ℕ, b < (d : WithBot ℕ∞) ∧ y ∈ f '' (U d : Set X) := by
  have hq : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have hdim : b < topologicalKrullDim (f.fiber y) := hy
  rw [topologicalKrullDim_eq_iSup_localKrullDim] at hdim
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 hdim
  rw [← topologicalKrullDimAt_eq_localKrullDim] at hx
  obtain ⟨Z, hZ, hxZ, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      (Y.residueField y) (f.fiber y) (f.fiberToSpecResidueField y) x
  let c : irreducibleComponents (f.fiber y) := ⟨Z, hZ⟩
  let η : f.fiber y := (genericPoints.ofComponent c).1
  have hηZ : closure ({η} : Set (f.fiber y)) = Z := genericPoints.isGenericPoint_ofComponent c
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  obtain ⟨d, hηd⟩ : ∃ d : ℕ, f.fiberι y η ∈ U d :=
    Opens.mem_iSup.mp (mem_of_mem_genericPoints_of_dense_scheme (f.fiber y)
      ((iSup U).2.preimage (f.fiberι y).continuous) (hdense y)
      (genericPoints.ofComponent c).2)
  have hηdim : topologicalKrullDimAt (f.fiber y) η = topologicalKrullDim Z := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents (Y.residueField y) (f.fiber y)
      (f.fiberToSpecResidueField y) η]
    have honly : ∀ W ∈ irreducibleComponents (f.fiber y), η ∈ W → W = Z := by
      intro W hW hηW
      have hZW : Z ⊆ W := hηZ ▸ closure_minimal (Set.singleton_subset_iff.mpr hηW)
        (isClosed_of_mem_irreducibleComponents W hW)
      exact Set.Subset.antisymm (hZ.2 hW.1 hZW) hZW
    exact le_antisymm (iSup_le fun W ↦ iSup_le fun hW ↦ by rw [honly W hW.1 hW.2])
      (le_iSup_of_le Z (le_iSup_of_le ⟨hZ, hηZ ▸ subset_closure (Set.mem_singleton η)⟩ le_rfl))
  refine ⟨d, ?_, ⟨f.fiberι y η, hηd, (f.fiberHomeo y η).2⟩⟩
  calc b < topologicalKrullDimAt (f.fiber y) x := hx
    _ = topologicalKrullDim Z := hZdim.symm
    _ = topologicalKrullDimAt (f.fiber y) η := hηdim.symm
    _ = (d : WithBot ℕ∞) := (Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f y η).symm.trans
      (topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U d) d (hrel d) _ hηd)

/-- **Stacks Project, Tag 0D4H.** The dimension-of-fibres function of a flat morphism of finite
presentation is lower semicontinuous. -/
@[stacks 0D4H]
public lemma lowerSemicontinuous_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (hf : FinitePresentation f) : LowerSemicontinuous f.fiberDimension := by
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  obtain ⟨U, hdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense f
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro b
  have hlevel : f.fiberDimension ⁻¹' Set.Ioi b =
      ⋃ d : {d : ℕ // b < (d : WithBot ℕ∞)}, f '' (U d.1 : Set X) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · intro hy
      obtain ⟨d, hd, hdy⟩ := exists_relativeDimension_image_mem f U hdense hrel b hy
      exact ⟨⟨d, hd⟩, hdy⟩
    · rintro ⟨d, x, hx, rfl⟩
      exact lt_of_lt_of_le d.2 (Scheme.Hom.le_fiberDimension_of_le_topologicalKrullDimAt_fiber f
        rfl (topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U d.1) d.1 (hrel d.1) x
          hx).ge)
  rw [hlevel]
  exact isOpen_iUnion fun d ↦ f.isOpenMap _ (U d.1).2

end AlgebraicGeometry

end
