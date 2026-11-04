module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# A uniform bound on the dimensions of the fibres

The fibres of a finite-type morphism over a quasi-compact scheme have uniformly bounded
dimension. Each fibre is a scheme of finite type over a field, so its local dimension at any
point is finite; the loci where that local dimension is at most `n` are open and exhaust the
source, so by compactness finitely many of them suffice and the largest `n` occurring is a
bound for every fibre at once.

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDimAt_le` bounds the local dimension of a scheme
  locally of finite type over a field by a natural number.
* `AlgebraicGeometry.exists_topologicalKrullDim_fiber_le` gives a natural-number bound for the
  topological Krull dimensions of all scheme-theoretic fibres.

## Implementation notes

A finite-type morphism is expressed, following Mathlib, by the typeclasses
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`. Quasi-compactness
of the target is expressed by `CompactSpace`. The bound is a natural number, coerced to the
extended-valued codomain of `topologicalKrullDim`; this records in particular that every fibre
has finite dimension.

## References

* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme of finite type over a field has finite local dimension at every point. -/
theorem exists_topologicalKrullDimAt_le (Z : Scheme.{u}) (k : Type u) [Field k]
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] (z : Z) :
    ∃ n : ℕ, topologicalKrullDimAt Z z ≤ n := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let _ : Field Γ(Spec (.of k), ⊤) := IsField.toField <|
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  let φ := g.appLE ⊤ V (by simp)
  have hft : φ.hom.FiniteType :=
    g.finiteType_appLE (isAffineOpen_top _) hV (by simp)
  algebraize [φ.hom]
  have hlocal : topologicalKrullDimAt Z z ≤ ringKrullDim Γ(Z, V) := by
    refine (topologicalKrullDimAt_isLeast Z z).2 ⟨V, hzV, V.2, ?_⟩
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      hV.isoSpec.hom.homeomorph.isHomeomorph).symm
  have hdim : ringKrullDim Γ(Z, V) ≠ ⊤ :=
    ringKrullDim_ne_top_of_finiteType (κ := Γ(Spec (.of k), ⊤))
  generalize hr : ringKrullDim Γ(Z, V) = d at hlocal hdim
  cases d with
  | bot => exact ⟨0, hlocal.trans bot_le⟩
  | coe a =>
    have ha : a ≠ ⊤ := fun ha ↦ hdim (by simp [ha])
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    exact ⟨n, hlocal⟩

/-- **Stacks Project, Tag 0A3V.** The dimensions of the fibres of a finite-type morphism to a
quasi-compact scheme are bounded by a single natural number. -/
@[stacks 0A3V]
public theorem exists_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] :
    ∃ n : ℕ, ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  let U : ℕ → Set X := fun n ↦
    {x | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ n}
  have hUcover : (Set.univ : Set X) ⊆ ⋃ n, U n := by
    intro x _
    have hg : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
      locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f (Y.fromSpecResidueField (f x))) inferInstance
    obtain ⟨n, hn⟩ := exists_topologicalKrullDimAt_le
      (f.fiber (f x)) (Y.residueField (f x))
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun n ↦ isOpen_setOf_fiberDimensionAt_le f n) hUcover
  refine ⟨t.sup id, fun y ↦ ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  have hxy : f (f.fiberι y z) = y := by
    simpa [Scheme.Hom.comp_apply] using congrArg (fun q : f.fiber y ⟶ Y ↦ q z) (f.fiber_fac y)
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (f.fiberι y z)))
  let x := f.fiberι y z
  let e : f.fiber y ≃ₜ f.fiber (f x) :=
    (f.fiberHomeo y).trans <| (Homeomorph.setCongr (by rw [hxy])).trans <|
      (f.fiberHomeo (f x)).symm
  have hez : e z = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    rfl
  rw [topologicalKrullDimAt_eq_of_homeomorph e z, hez]
  exact le_trans hxi (by exact_mod_cast Finset.le_sup (f := id) hi)

end AlgebraicGeometry
