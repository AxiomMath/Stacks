module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.NormalizationRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.CompositionData

/-!
# The normalization compactification of a finite étale cover

Let `k` be an algebraically closed field, `S` a scheme over `k` with a compactification
`j : S ⟶ S̄` (an open immersion into a scheme proper over `k`), and `π : T ⟶ S` finite étale with
`T` connected and smooth over `k`. The normalization `T̄` of `S̄` in `T` (relative normalization of
`j ∘ π`) is a compactification of `T`:

* `T ⟶ T̄` is an open immersion (Zariski's main theorem, `j ∘ π` being quasi-finite and
  separated);
* `π̄ : T̄ ⟶ S̄` is finite ([Tag 0BXS](https://stacks.math.columbia.edu/tag/0BXS): `S̄` is of
  finite type over a field), so `T̄` is proper over `k` and `dim T̄ ≤ dim S̄`;
* the square `T = T̄ ×_{S̄} S` is cartesian: `T` is closed in the irreducible open `π̄⁻¹(S)`,
  being proper over `S` (`AlgebraicGeometry.preimage_opensRange_eq_of_comp_eq`).

This is the compactification of a finite étale cover used to transport Poincaré duality along the
cover, in the proof of duality with lisse coefficients on a smooth variety (part of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.exists_isPullback_isFinite_of_compactification_of_finiteEtale`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The normalization compactification of a connected finite étale cover.** For a
compactification `j : S ⟶ S̄` of a `k`-scheme `S` and `π : T ⟶ S` finite étale with `T` connected
and smooth over `k`, there is an open immersion `j_T : T ⟶ T̄` and a finite `π̄ : T̄ ⟶ S̄` with
`T = T̄ ×_{S̄} S`, `T̄` proper over `k` and `dim T̄ ≤ dim S̄`. -/
theorem exists_isPullback_isFinite_of_compactification_of_finiteEtale (k : Type u) [Field k]
    [IsAlgClosed k] {S T : Scheme.{u}} (q : S ⟶ Spec (.of k))
    (jS : CompactificationOf (Over.mk q)) (π : T ⟶ S) [IsFinite π] [Etale π] [ConnectedSpace T]
    [Smooth (π ≫ q)] :
    ∃ (Tb : Scheme.{u}) (jT : T ⟶ Tb) (_ : IsOpenImmersion jT) (πb : Tb ⟶ jS.space),
      IsFinite πb ∧ IsPullback π jT jS.immersion πb ∧ IsProper (πb ≫ jS.toBase) ∧
        topologicalKrullDim Tb ≤ topologicalKrullDim jS.space := by
  have : IsLocallyNoetherian jS.space := LocallyOfFiniteType.isLocallyNoetherian jS.toBase
  have : IsIntegral T := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (π ≫ q)
  let g : T ⟶ jS.space := π ≫ jS.immersion
  have hgq : g ≫ jS.toBase = π ≫ q := by
    simp only [g, Category.assoc, CompactificationOf.immersion_comp_toBase', Over.mk_hom]
  have : LocallyOfFiniteType (g ≫ jS.toBase) := by rw [hgq]; infer_instance
  have : IsSeparated g := inferInstance
  obtain ⟨hto, -, -⟩ := isOpenImmersion_toNormalization_and_isIntegralHom_fromNormalization g
  have := hto
  have hfin : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType_over_field k jS.toBase (g ≫ jS.toBase) g rfl
  have : IsProper (g.fromNormalization ≫ jS.toBase) := inferInstance
  have : IrreducibleSpace g.normalization := inferInstance
  have hw : g.toNormalization ≫ g.fromNormalization = π ≫ jS.immersion :=
    g.toNormalization_fromNormalization
  have hpre := preimage_opensRange_eq_of_comp_eq k jS.toBase jS.immersion π
    (g.fromNormalization ≫ jS.toBase) g.toNormalization g.fromNormalization hw rfl
  exact ⟨g.normalization, g.toNormalization, inferInstance, g.fromNormalization, hfin,
    IsOpenImmersion.isPullback π g.toNormalization jS.immersion g.fromNormalization hw hpre,
    inferInstance, topologicalKrullDim_le_of_locallyQuasiFinite g.fromNormalization⟩

end Stacks.EtaleCohomology

end
