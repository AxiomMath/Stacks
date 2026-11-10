module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySlice
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Locally closed subsets of schemes of finite type over a field: dimension and slices

Tag 0B1T allows `X ⊆ 𝐏^N` to be a subvariety which is not closed, and its `T i` to be closed in
`X` only. Two facts about locally closed subsets let the dimension counts of the closed case go
through:

* **a nonempty open part of an irreducible closed subset has the dimension of the whole**, by
  Tag 0A21 applied to the reduced closed subscheme on the closed subset; in particular a locally
  closed irreducible subset has the dimension of its closure;
* **the slice bound** of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySlice`
  holds for locally closed subsets of `ℓ × 𝐏(V)`: if every slice over a closed point of the line
  has dimension at most `m`, the subset has dimension at most `m + 1`. The proof is the closed
  one run on an open subscheme of the reduced closed subscheme on the closure.

## Main results

* `topologicalKrullDim_inter_isOpen_eq`: `dim (Z ∩ O) = dim Z` for `Z` closed irreducible, `O`
  open and `Z ∩ O ≠ ∅`.
* `topologicalKrullDim_eq_closure_of_isLocallyClosed`: `dim S = dim S̄` for a locally closed
  irreducible `S`.
* `ProjectiveSpaceOfModule.topologicalKrullDim_le_of_slice_le_of_isLocallyClosed`: the slice bound
  for locally closed subsets of `ℓ × 𝐏(V)`.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The preimage of an open set `O` under an embedding with range `Z` is homeomorphic to `Z ∩ O`. -/
private theorem topologicalKrullDim_preimage_eq_inter {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) {Z : Set Y}
    (hZ : Set.range f = Z) (O : Set Y) :
    topologicalKrullDim ↥(f ⁻¹' O) = topologicalKrullDim ↥(Z ∩ O) := by
  have h : f ⁻¹' O = f ⁻¹' (Z ∩ O) := by ext x; simp [← hZ]
  rw [h]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (hf.homeomorphOfSubsetRange (hZ ▸ Set.inter_subset_left)).isHomeomorph

/-- **A nonempty open part of an irreducible closed subset of a scheme locally of finite type over
a field has the dimension of the whole closed subset.** -/
public theorem topologicalKrullDim_inter_isOpen_eq (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {Z O : Set Y} (hZ : IsClosed Z)
    (hZirr : IsIrreducible Z) (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) :
    topologicalKrullDim ↥(Z ∩ O) = topologicalKrullDim ↥Z := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds Y) with hI
  have hrange : Set.range I.subschemeι.base = Z := range_vanishingIdeal_subschemeι Z hZ
  have : IrreducibleSpace I.subscheme := irreducibleSpace_vanishingIdeal_subscheme Z hZ hZirr
  set U : Set I.subscheme := I.subschemeι.base ⁻¹' O with hU
  have hUo : IsOpen U := hO.preimage I.subschemeι.continuous
  have hUne : U.Nonempty := by
    obtain ⟨y, hyZ, hyO⟩ := hne
    rw [← hrange] at hyZ
    obtain ⟨x, rfl⟩ := hyZ
    exact ⟨x, hyO⟩
  have h0A21 := topologicalKrullDim_eq_of_isOpen k I.subscheme (I.subschemeι ≫ sY) U hUo hUne
  rw [← topologicalKrullDim_vanishingIdeal_subscheme Z hZ, ← hI, h0A21]
  exact (topologicalKrullDim_preimage_eq_inter I.subschemeι.isClosedEmbedding.isEmbedding hrange
    O).symm

/-- A locally closed subset is the intersection of its closure with an open set. -/
public theorem exists_isOpen_eq_closure_inter {Y : Type*} [TopologicalSpace Y] {S : Set Y}
    (hS : IsLocallyClosed S) : ∃ O : Set Y, IsOpen O ∧ S = closure S ∩ O := by
  obtain ⟨O, Z, hO, hZ, rfl⟩ := hS
  refine ⟨O, hO, Set.Subset.antisymm (fun x hx => ⟨subset_closure hx, hx.1⟩) ?_⟩
  rintro x ⟨hxc, hxO⟩
  exact ⟨hxO, (closure_minimal Set.inter_subset_right hZ) hxc⟩

/-- **A locally closed irreducible subset of a scheme locally of finite type over a field has the
dimension of its closure.** -/
public theorem topologicalKrullDim_eq_closure_of_isLocallyClosed (k : Type u) [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {S : Set Y}
    (hS : IsLocallyClosed S) (hSirr : IsIrreducible S) :
    topologicalKrullDim ↥S = topologicalKrullDim ↥(closure S) := by
  obtain ⟨O, hO, hSO⟩ := exists_isOpen_eq_closure_inter hS
  have hne : (closure S ∩ O).Nonempty := hSO ▸ hSirr.nonempty
  have h := topologicalKrullDim_inter_isOpen_eq k sY isClosed_closure hSirr.closure hO hne
  rw [← h, ← hSO]

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The slice bound for a locally closed subset of `ℓ × 𝐏(V)`.** A locally closed subset all
of whose slices over closed points of the line have dimension at most `m` has dimension at most
`m + 1`. -/
public theorem topologicalKrullDim_le_of_slice_le_of_isLocallyClosed {m : ℕ}
    {S : Set (movingAmbient k V L)} (hS : IsLocallyClosed S)
    (hL : Module.finrank k (lineSpace k V L) = 2)
    (h : ∀ lam : movingLine k V L, IsClosed ({lam} : Set (movingLine k V L)) →
      topologicalKrullDim ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}) ≤ (m : WithBot ℕ∞)) :
    topologicalKrullDim S ≤ (m : WithBot ℕ∞) + 1 := by
  obtain ⟨O, hO, hSO⟩ := exists_isOpen_eq_closure_inter hS
  set I : (movingAmbient k V L).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨closure S, isClosed_closure⟩ with hI
  have hrange : Set.range I.subschemeι.base = closure S :=
    range_vanishingIdeal_subschemeι (closure S) isClosed_closure
  set U : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ ⟨O, hO⟩ with hU
  set p : U.toScheme ⟶ movingLine k V L := U.ι ≫ I.subschemeι ≫ ambLine k V L with hp
  have hlftamb : LocallyOfFiniteType (ambLine k V L) := by
    have h1 : IsProper (ambLine k V L) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
        (isProper_projectiveSpaceOfModuleToSpec k V)
    infer_instance
  have hlftp : LocallyOfFiniteType p := by rw [hp]; infer_instance
  have hjac : JacobsonSpace U.toScheme :=
    LocallyOfFiniteType.jacobsonSpace (U.ι ≫ I.subschemeι ≫ movingAmbientToSpec k V L)
  -- the points of `U` are the points of `S`
  have hmemS : ∀ x : U.toScheme, I.subschemeι.base (U.ι.base x) ∈ S := by
    intro x
    rw [hSO]
    refine ⟨hrange ▸ Set.mem_range_self _, ?_⟩
    exact x.2
  -- the fibre over a closed point of the line is bounded by the slice
  have hfib : ∀ lam : movingLine k V L, IsClosed ({lam} : Set (movingLine k V L)) →
      topologicalKrullDim (p.fiber lam) ≤ (m : WithBot ℕ∞) := by
    intro lam hlam
    refine topologicalKrullDim_fiber_le_of_preimage_subset p lam
      (p.base ⁻¹' {lam}) le_rfl (le_trans ?_ (h lam hlam))
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun z : ↥(p.base ⁻¹' {lam}) =>
        (⟨I.subschemeι.base (U.ι.base z.1), hmemS z.1, z.2⟩ :
          ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}))) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact (I.subschemeι.isClosedEmbedding.isInducing.comp
      U.ι.isOpenEmbedding.isInducing).comp Topology.IsInducing.subtypeVal
  have hdimU : topologicalKrullDim U.toScheme ≤ 1 + (m : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_forall_fiber_le k p (movingLineToSpec k V L)
      (le_of_eq (topologicalKrullDim_movingLine k V L hL))
      (fiberDimensionAt_le_of_isClosed_singleton_target p fun x hx => hfib x hx)
  -- `U` is homeomorphic to `S`
  have hhom : topologicalKrullDim U.toScheme = topologicalKrullDim ↥S := by
    have := topologicalKrullDim_preimage_eq_inter
      I.subschemeι.isClosedEmbedding.isEmbedding hrange O
    rw [← hSO] at this
    exact this
  rw [← hhom, add_comm]
  exact hdimU

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
