module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveSupportClosed
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EquidimensionalCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# An effective relative cycle is equidimensional

Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type and let `α` be a
relative `r`-cycle on `X/S`. If `α` is effective then `α` is equidimensional: its support is
contained in a closed subset of `X` whose relative dimension over `S` is at most `r`.

The bounding closed subset is `Supp(α)` itself, which is closed because `α` is effective. Its
part in the fibre over `s` is the support of the `r`-cycle `α_s`, so the assertion reduces to the
statement that the support of an `r`-cycle on a scheme locally of finite type over a field has
topological dimension at most `r`. That support is a locally finite union of closures of points
of relative dimension `r`, and relative dimension does not increase along a specialization, so
every point of it has relative dimension at most `r`; the delta-dimension of the reduced closed
subscheme it carries is therefore at most `r`, and over a field this bounds the topological
dimension.

## Main results

* `Stacks.Chow.topologicalKrullDim_tsupport_le` — the support of an `r`-cycle over a field has
  topological dimension at most `r`.
* `Stacks.Chow.isEquidimensional_of_isEffectiveFamily` — an effective relative `r`-cycle is
  equidimensional.

## Implementation notes

The source states the lemma for integers `r, e ≥ 0`; the integer `e` does not occur in the
statement and only the relative dimension `r` is retained.

## References

* [Stacks Project, Tag 0H5X](https://stacks.math.columbia.edu/tag/0H5X)
* [Stacks Project, Tag 0H5W](https://stacks.math.columbia.edu/tag/0H5W)
* [Stacks Project, Tag 0H5I](https://stacks.math.columbia.edu/tag/0H5I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The dimension of the support of a cycle -/

/-- A point of the support of a `k`-cycle has relative dimension at most `k`: it is a
specialization of a point carrying a nonzero coefficient, where the relative dimension is `k`,
and relative dimension does not increase along a specialization. -/
theorem relativeDimension_le_of_mem_tsupport (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (c : CycleGroup C p k) {y : Y}
    (hy : y ∈ tsupport (c.1 : AlgebraicCycle Y ℤ)) :
    relativeDimension C.dimensionFunction p y ≤ k := by
  have hlfs : LocallyFiniteSupport ⇑(c.1 : AlgebraicCycle Y ℤ) :=
    Function.locallyFinsupp.locallyFiniteSupport _
  rw [tsupport_eq_biUnion_closure_singleton hlfs] at hy
  obtain ⟨z, hz, hzy⟩ := Set.mem_iUnion₂.mp hy
  refine (relativeDimension_le_of_specializes C p (specializes_iff_mem_closure.mpr hzy)).trans_eq ?_
  let Z : IrreducibleCloseds Y :=
    ⟨closure ({z} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
  have hZ : IsGenericPoint z (Z : Set Y) := isGenericPoint_closure
  have hgp : Z.isIrreducible.genericPoint = z :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq hZ
  have hdd := (mem_cyclesOfDimension C p k c.1).mp c.2 Z
    (by rw [hgp]; exact Function.mem_support.mp hz)
  rwa [deltaDimension_eq_of_isGenericPoint C p Z z hZ] at hdd

/-- The support of an `r`-cycle on a scheme locally of finite type over a field has topological
dimension at most `r`: every point of that support has relative dimension at most `r`, so the
reduced closed subscheme it carries has delta-dimension at most `r`. -/
theorem topologicalKrullDim_tsupport_le (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (c : CycleGroup (fieldChowSituation k) p (r : ℤ)) :
    topologicalKrullDim ↥(tsupport (c.1 : AlgebraicCycle Y ℤ)) ≤ (r : WithBot ℕ∞) := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨tsupport (c.1 : AlgebraicCycle Y ℤ), isClosed_tsupport _⟩
  have hIrange : (Set.range I.subschemeι : Set Y) = tsupport (c.1 : AlgebraicCycle Y ℤ) := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hIrange)).isHomeomorph]
  exact topologicalKrullDim_le_of_schemeDeltaDimension_le (fieldChowSituation k)
    (fun s _ => fieldChowSituation_dimensionFunction_eq_zero k s) (I.subschemeι ≫ p) r
    (schemeDeltaDimension_le_of_forall_point (fieldChowSituation k) p I.subschemeι fun z =>
      relativeDimension_le_of_mem_tsupport (fieldChowSituation k) p (r : ℤ) c
        (by rw [← hIrange]; exact ⟨z, rfl⟩))

/-! ### Effective relative cycles -/

variable {X S : Scheme.{u}}

/-- The part of the support of a family of cycles lying in the fibre over `s` is, read on that
fibre, the support of the cycle on it. -/
private theorem preimage_inter_fiber_eq_tsupport (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) :
    (f.fiberι s) ⁻¹' (supportOfFamily f α ∩ f ⁻¹' {s}) =
      tsupport (α s : AlgebraicCycle (f.fiber s) ℤ) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
    fiberι_mem_supportOfFamily_iff f r α s y, fiberι_apply_base f s y, and_true]

/-- The part of the support of a family of `r`-cycles lying in a fibre has topological dimension
at most `r`: it is homeomorphic to the support of the `r`-cycle on that fibre. -/
private theorem topologicalKrullDim_inter_fiber_le (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) :
    topologicalKrullDim ↥(supportOfFamily f α ∩ f ⁻¹' {s}) ≤ (r : WithBot ℕ∞) := by
  have hsub : (supportOfFamily f α ∩ f ⁻¹' {s} : Set X) ⊆ Set.range (f.fiberι s) := by
    rw [f.range_fiberι s]
    exact Set.inter_subset_right
  let e : ↥(tsupport (α s : AlgebraicCycle (f.fiber s) ℤ)) ≃ₜ
      ↥(supportOfFamily f α ∩ f ⁻¹' {s}) :=
    (Homeomorph.setCongr (preimage_inter_fiber_eq_tsupport f r α s)).symm.trans
      ((f.fiberι s).isEmbedding.homeomorphOfSubsetRange hsub)
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact topologicalKrullDim_tsupport_le (S.residueField s) (f.fiberToSpecResidueField s) r (α s)

/-- **Stacks Project, Tag 0H5X.** Let `f : X ⟶ S` be a morphism of schemes with `S` locally
Noetherian and `f` locally of finite type, let `r ≥ 0` be an integer and let `α` be a relative
`r`-cycle on `X/S`. If `α` is effective then `α` is equidimensional. -/
@[stacks 0H5X]
theorem isEquidimensional_of_isEffectiveFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (r : ℕ) (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α)
    (heff : IsEffectiveFamily f r α) : IsEquidimensional f r α := by
  rw [isEquidimensional_iff_relativeDimensionLEOn_closure,
    (isClosed_supportOfFamily_of_isEffectiveFamily f r α hα heff).closure_eq]
  intro x hx
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans
    (topologicalKrullDim_inter_fiber_le f r α (f x))

end Stacks.Chow

end
