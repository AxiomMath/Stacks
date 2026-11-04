module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibreRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySet
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySlice

/-!
# The dimension of the family `C'` is at least one more than that of `C`

The family `C'` is irreducible and dominant over the line, and its slice over a closed point of
the line is a closed subset of it which is not everything — the domination forces `C'` to have
points over other points of the line, and the line has a second point because a two-dimensional
space has two coordinate functionals with different kernels. In an irreducible Noetherian space a
proper closed subset has dimension at least one less,
so `dim C' ≥ dim C'_λ + 1`; taking for `λ` the point `0` of the line, whose slice is `C` itself,
gives `dim C' ≥ dim C + 1`.

That inequality is the one clause (3) of Tag 0B1T consumes: paired with the upper bound
`dim (C' ∩ (X × ℓ)) ≤ m + 1` and the product formulas for `dim (ℓ × 𝐏(V))` and `dim (X × ℓ)`, it
turns the fibrewise dimension criterion into the criterion for `C'` and `X × ℓ`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_slice_le_of_subset`: the
  dimension of a slice of a subset, read inside that subset, is at least the dimension of the
  slice as a subset of the ambient space.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_ne_of_movingLine`: the line has at least two
  points.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_add_one_le_movingFamilySet`:
  **`dim C + 1 ≤ dim C'`**, from the irreducibility and the dominance of `C'`.

## Implementation notes

The slice is taken twice: as a subset `S ∩ ambLine⁻¹{λ}` of the ambient product and as a subset
`Subtype.val ⁻¹' (ambLine⁻¹{λ})` of `S`. Only the inequality between their dimensions in the
direction needed is proved, by an inducing map; the two are in fact homeomorphic.

Noetherianness of `S` comes from the properness of the structure morphism of the ambient product:
proper gives both finite type, hence locally Noetherian, and quasi-compact, hence compact, and
those two give `AlgebraicGeometry.IsNoetherian`, whose underlying space is Noetherian; a subspace
of a Noetherian space is Noetherian.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- The slice of a subset, read inside that subset, has at least the dimension of the slice read
in the ambient space. -/
public theorem topologicalKrullDim_slice_le_of_subset {X : Type*} [TopologicalSpace X]
    (S W : Set X) :
    topologicalKrullDim ↥(S ∩ W) ≤
      topologicalKrullDim ↥((Subtype.val : ↥S → X) ⁻¹' W) :=
  Topology.IsInducing.topologicalKrullDim_le
    (f := fun z : ↥(S ∩ W) => (⟨⟨z.1, z.2.1⟩, z.2.2⟩ : ↥((Subtype.val : ↥S → X) ⁻¹' W)))
    (Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val
      (Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val
        Topology.IsInducing.subtypeVal))

omit [IsAlgClosed k] in
/-- The ambient product is a Noetherian space: it is proper over the ground field. -/
public theorem noetherianSpace_movingAmbient : NoetherianSpace (movingAmbient k V L) := by
  have hp : IsProper (movingAmbientToSpec k V L) := isProper_movingAmbientToSpec k V L
  have h1 : LocallyOfFiniteType (movingAmbientToSpec k V L) := by infer_instance
  have h2 : QuasiCompact (movingAmbientToSpec k V L) := by infer_instance
  have h3 : IsLocallyNoetherian (movingAmbient k V L) :=
    LocallyOfFiniteType.isLocallyNoetherian (movingAmbientToSpec k V L)
  have h4 : CompactSpace (movingAmbient k V L) :=
    QuasiCompact.compactSpace_of_compactSpace (movingAmbientToSpec k V L)
  have h5 : IsNoetherian (movingAmbient k V L) := ⟨⟩
  infer_instance

omit [IsAlgClosed k] [Nontrivial V] in
/-- **The line has at least two points.** A basis of the corank-two quotient has two coordinate
functionals, and one of them kills the first basis vector while the other does not, so they cut
out distinct points of the line. -/
public theorem exists_ne_of_movingLine (hL : Module.finrank k (lineSpace k V L) = 2)
    (lam : movingLine k V L) : ∃ lam' : movingLine k V L, lam' ≠ lam := by
  set b2 := Module.finBasisOfFinrankEq k (lineSpace k V L) hL with hb2
  have hc00 : b2.coord 0 (b2 0) = 1 := by
    simp [Module.Basis.coord_apply]
  have hc10 : b2.coord 1 (b2 0) = 0 := by
    simp [Module.Basis.coord_apply, show (1 : Fin 2) ≠ 0 from by decide]
  have hne0 : ∀ i, b2.coord i ≠ 0 := fun i hz => by
    simpa [hz] using b2.coord_apply i (b2 i)
  have hne : linearFunctionalPoint k (lineSpace k V L) (b2.coord 0) (hne0 0) ≠
      linearFunctionalPoint k (lineSpace k V L) (b2.coord 1) (hne0 1) := by
    intro heq
    have hker : b2.coord 0 (b2 0) = 0 ↔ b2.coord 1 (b2 0) = 0 := by
      rw [← linearFunctionalPoint_ι_mem k (lineSpace k V L) (b2.coord 0) (hne0 0) (b2 0),
        ← linearFunctionalPoint_ι_mem k (lineSpace k V L) (b2.coord 1) (hne0 1) (b2 0), heq]
    exact one_ne_zero (hc00 ▸ hker.mpr hc10)
  by_cases hc : linearFunctionalPoint k (lineSpace k V L) (b2.coord 0) (hne0 0) = lam
  · exact ⟨linearFunctionalPoint k (lineSpace k V L) (b2.coord 1) (hne0 1),
      fun h => hne (hc.trans h.symm)⟩
  · exact ⟨linearFunctionalPoint k (lineSpace k V L) (b2.coord 0) (hne0 0), hc⟩

/-- **`dim C + 1 ≤ dim C'`.** The slice of `C'` over the point whose fibre is `C` is a closed
subset of `C'` which is not everything, because `C'` dominates the line and the line has a second
point; in an irreducible Noetherian space such a subset drops the dimension. -/
public theorem topologicalKrullDim_add_one_le_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set (movingLine k V L)))
    (hfib : movingFibre k V L lam hlam (movingFamilySet k V L b C) = C)
    (hirr : IsIrreducible (movingFamilySet k V L b C))
    (hdom : closure ((ambLine k V L).base '' movingFamilySet k V L b C) = Set.univ)
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim ↥C + 1 ≤
      topologicalKrullDim ↥(movingFamilySet k V L b C) := by
  have hamb : NoetherianSpace (movingAmbient k V L) := noetherianSpace_movingAmbient k V L
  have hnoeth : NoetherianSpace ↥(movingFamilySet k V L b C) :=
    Topology.IsInducing.subtypeVal.noetherianSpace
  have hirrS : IrreducibleSpace ↥(movingFamilySet k V L b C) := Subtype.irreducibleSpace hirr
  have hTclosed : IsClosed ((Subtype.val : ↥(movingFamilySet k V L b C) →
      movingAmbient k V L) ⁻¹' ((ambLine k V L).base ⁻¹' {lam})) :=
    (hlam.preimage (ambLine k V L).continuous).preimage (by fun_prop)
  have hTne : (Subtype.val : ↥(movingFamilySet k V L b C) → movingAmbient k V L) ⁻¹'
      ((ambLine k V L).base ⁻¹' {lam}) ≠ Set.univ := by
    intro hTu
    obtain ⟨lam', hlam'⟩ := exists_ne_of_movingLine k V L hL lam
    have himg : (ambLine k V L).base '' movingFamilySet k V L b C ⊆
        ({lam} : Set (movingLine k V L)) := by
      rintro _ ⟨z, hzS, rfl⟩
      have hmem : (⟨z, hzS⟩ : ↥(movingFamilySet k V L b C)) ∈
          (Subtype.val : ↥(movingFamilySet k V L b C) → movingAmbient k V L) ⁻¹'
            ((ambLine k V L).base ⁻¹' {lam}) := hTu ▸ Set.mem_univ _
      exact hmem
    have huniv : (Set.univ : Set (movingLine k V L)) ⊆ ({lam} : Set _) := by
      rw [← hdom, ← hlam.closure_eq]
      exact closure_mono himg
    exact hlam' (Set.mem_singleton_iff.mp (huniv (Set.mem_univ lam')))
  have hle : topologicalKrullDim ↥C ≤
      topologicalKrullDim ↥((Subtype.val : ↥(movingFamilySet k V L b C) →
        movingAmbient k V L) ⁻¹' ((ambLine k V L).base ⁻¹' {lam})) := by
    conv_lhs => rw [← hfib]
    rw [topologicalKrullDim_movingFibre k V L lam hlam (movingFamilySet k V L b C)]
    exact topologicalKrullDim_slice_le_of_subset (movingFamilySet k V L b C)
      ((ambLine k V L).base ⁻¹' {lam})
  calc topologicalKrullDim ↥C + 1 ≤
        topologicalKrullDim ↥((Subtype.val : ↥(movingFamilySet k V L b C) →
          movingAmbient k V L) ⁻¹' ((ambLine k V L).base ⁻¹' {lam})) + 1 := by gcongr
    _ ≤ topologicalKrullDim ↥(movingFamilySet k V L b C) :=
      Topology.topologicalKrullDim_add_one_le_of_ne_univ hTclosed hTne

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
