module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme

/-!
# A closed subset of `ℓ × 𝐏(V)` is bounded by its slices over the closed points of the line

The dimension count of Tag 0B1T needs an upper bound for the dimension of a closed subset `S` of
`ℓ ×_k 𝐏(V)` in terms of the dimensions of its slices over the points of the line. The local
dimension of a fibre is upper semicontinuous, so a bound over the *closed* points of the base
holds at every point
(`AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton_target`), and the dimension of the
total space is at most the dimension of the base plus the fibre bound
(`AlgebraicGeometry.topologicalKrullDim_le_of_forall_fiber_le`). The line has dimension one, so a
bound `m` on every slice over a closed point gives `dim S ≤ m + 1`. That the bound need only be
checked over the closed points of the line is what keeps the whole count over the base field: at
a closed point of the line the slice is a subset of `𝐏(V)`, and no base change of projective space
to a residue field is needed.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_le_of_slice_le`: a closed subset
  of `ℓ × 𝐏(V)` all of whose slices over closed points of the line have dimension at most `m` has
  dimension at most `m + 1`.

## Implementation notes

The subset is turned into a scheme — the reduced closed subscheme on it, as in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme` — because the
semicontinuity and fibre-dimension tools are statements about morphisms of schemes. Its dimension
is the dimension of the subset, and the scheme-theoretic fibre over a point of the line is bounded
by the slice: the inclusion of the subscheme is inducing, so the preimage of the slice has at most
the dimension of the slice, and
`AlgebraicGeometry.topologicalKrullDim_fiber_le_of_preimage_subset` turns that into a bound on the
fibre.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

omit [IsAlgClosed k] in
/-- **A closed subset of `ℓ × 𝐏(V)` whose slice over every closed point of the line has dimension
at most `m` has dimension at most `m + 1`.** -/
public theorem topologicalKrullDim_le_of_slice_le {m : ℕ}
    {S : Set (movingAmbient k V L)} (hS : IsClosed S)
    (hL : Module.finrank k (lineSpace k V L) = 2)
    (h : ∀ lam : movingLine k V L, IsClosed ({lam} : Set (movingLine k V L)) →
      topologicalKrullDim ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}) ≤ (m : WithBot ℕ∞)) :
    topologicalKrullDim S ≤ (m : WithBot ℕ∞) + 1 := by
  set I : (movingAmbient k V L).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩ with hI
  have hrange : Set.range I.subschemeι.base = S := range_vanishingIdeal_subschemeι S hS
  set p : I.subscheme ⟶ movingLine k V L := I.subschemeι ≫ ambLine k V L with hp
  have hlftamb : LocallyOfFiniteType (ambLine k V L) := by
    have h1 : IsProper (ambLine k V L) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
        (isProper_projectiveSpaceOfModuleToSpec k V)
    infer_instance
  have hlftp : LocallyOfFiniteType p := by rw [hp]; infer_instance
  have hjac : JacobsonSpace I.subscheme :=
    LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ movingAmbientToSpec k V L)
  -- the fibre over a closed point of the line is bounded by the slice
  have hfib : ∀ lam : movingLine k V L, IsClosed ({lam} : Set (movingLine k V L)) →
      topologicalKrullDim (p.fiber lam) ≤ (m : WithBot ℕ∞) := by
    intro lam hlam
    refine topologicalKrullDim_fiber_le_of_preimage_subset p lam
      (p.base ⁻¹' {lam}) le_rfl (le_trans ?_ (h lam hlam))
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun z : ↥(p.base ⁻¹' {lam}) =>
        (⟨I.subschemeι.base z.1, hrange ▸ Set.mem_range_self z.1, z.2⟩ :
          ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}))) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact I.subschemeι.isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hdimZ : topologicalKrullDim I.subscheme ≤ 1 + (m : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_forall_fiber_le k p (movingLineToSpec k V L)
      (le_of_eq (topologicalKrullDim_movingLine k V L hL))
      (fiberDimensionAt_le_of_isClosed_singleton_target p
        fun x hx => hfib x hx)
  rw [← topologicalKrullDim_vanishingIdeal_subscheme S hS, ← hI, add_comm]
  exact hdimZ

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
