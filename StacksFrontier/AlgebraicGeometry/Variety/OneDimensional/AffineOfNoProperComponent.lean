module

public import StacksFrontier.AlgebraicGeometry.ClauseThree.GenericStalkInput
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.MultiplePointSectionDimension
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.TwistSectionDivisibility
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0A28: a one-dimensional scheme with no proper component is affine

[Stacks, Tag 0A28] says that a separated scheme `X` of finite type over a field `k` with
`dim(X) ≤ 1` no irreducible component of which is proper of dimension one is affine.

The source's proof is three sentences. Give each irreducible component of `X` the reduced induced
closed subscheme structure: it is then integral, and separated and of finite type over `k` of
dimension at most one. A component of dimension one is a curve over `k`, so [Stacks, Tag 0A27]
makes it an affine scheme or H-projective over `k`, and the second alternative is excluded by the
hypothesis, an H-projective scheme over a field being proper over it. A component of dimension
zero is affine by [Stacks, Tag 06LH]. The components are finitely many because `X` is Noetherian,
so their coproduct is an affine scheme mapping to `X` by a finite surjective morphism, and
[Stacks, Tag 01YQ] makes `X` affine.

## Main results

* `AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve` (imported): the inner claim of
  [Stacks, Tag 0A27] — on a proper curve, the complement of a closed point whose local ring is a
  discrete valuation ring is an affine open.
* `AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_completion` (imported): the
  compactification of [Stacks, Tag 0BXW], with the source's remark that it is again a curve.
* `AlgebraicGeometry.isAffine_or_isProjectiveMorphism` (imported): the dichotomy of
  [Stacks, Tag 0A27] — a curve over `k` is an affine scheme or H-projective over `k`.
* `Stacks.AffineNoProperComponent.isAffine_componentIdealSheafData`: an irreducible component of
  `X`, with its reduced structure, is affine.
* `AlgebraicGeometry.isAffine_of_topologicalKrullDim_le_one_of_forall_component_not_isProper`:
  **[Stacks, Tag 0A28]**.

## Implementation notes

**Nothing is assumed.** The two numerical inputs that the inner claim of [Stacks, Tag 0A27] needs
are proved in the two modules imported here: the dimension count is
`AlgebraicGeometry.succ_le_finrank_cohomologyOverField_multiplePoint`, clause (2) of
[Stacks, Tag 0AYT] in the shape
`dim_k H⁰(Y, i_* i^* 𝒪_Y((N+1)y)) ≥ N + 1`, read off the degree of `𝒪_Y((N+1)y)`; and the
minimality step is `AlgebraicGeometry.mem_range_invertibleSheafMap_of_notMem_nonvanishingChart`,
the source's *"otherwise it would define a section of `𝒪_X((n-1)x) ⊂ 𝒪_X(n·x)`"*.

**The reduced structure on a component is its vanishing ideal.** An irreducible component `Z` of
`X` is closed, and the closed subscheme it carries is
`(Scheme.IdealSheafData.vanishingIdeal ⟨Z, _⟩).subscheme`, whose structure sheaf is reduced by
`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` and whose space is `Z`, irreducible.
That is exactly "integral", by `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`.

**Finite type over `k` is spelled as the conjunction** of `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.QuasiCompact`, as in [Stacks, Tag 01T1]; dimension is the Krull dimension
`topologicalKrullDim` of the underlying space, valued in `WithBot ℕ∞`; H-projectivity is
`AlgebraicGeometry.IsProjectiveMorphism`, the predicate of [Stacks, Tag 01W8].

**[Stacks, Tag 09NZ] is not needed.** The compactification of [Stacks, Tag 0BXW] that the proof of
[Stacks, Tag 0A27] chooses is proved for a reduced scheme with no ample-sheaf input, as
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`, and
a curve is integral, hence reduced. What the compactification `X̄` is again a curve — the source's
own remark, not part of the conclusion of Tag 0BXW — is reproved in
`exists_isCurve_isProjectiveMorphism_completion` below.

## References

* [Stacks Project, Tag 0A28](https://stacks.math.columbia.edu/tag/0A28)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 09N9](https://stacks.math.columbia.edu/tag/09N9)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Divisors Stacks.ProjectiveSpaceSections

universe u

namespace Stacks.AffineNoProperComponent

/-! ### The inner claim and the dichotomy of Tag 0A27 -/

/-! ### The irreducible components with their reduced structure -/

/-- A dimension in `WithBot ℕ∞` which is less than one is at most zero. -/
alias dimension_le_zero_of_lt_one := AlgebraicGeometry.dim_le_zero_of_lt_one

variable {X : Scheme.{u}}

/-- The reduced induced closed subscheme structure on an irreducible component. -/
noncomputable def componentIdealSheafData (Z : irreducibleComponents X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)

/-- The underlying set of the subscheme of an irreducible component is the component. -/
theorem range_subschemeι_componentIdealSheafData (Z : irreducibleComponents X) :
    Set.range (componentIdealSheafData Z).subschemeι.base = Z.1 := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [componentIdealSheafData, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- An irreducible component with its reduced structure is integral. -/
theorem isIntegral_componentIdealSheafData (Z : irreducibleComponents X) :
    IsIntegral (componentIdealSheafData Z).subscheme :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).2
    ⟨Subtype.irreducibleSpace Z.2.1,
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _⟩

/-- The dimension of an irreducible component is at most that of the ambient scheme. -/
theorem topologicalKrullDim_componentIdealSheafData_le (Z : irreducibleComponents X) :
    topologicalKrullDim (componentIdealSheafData Z).subscheme ≤ topologicalKrullDim X :=
  (componentIdealSheafData Z).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le

/-- Each irreducible component of a separated finite type scheme of dimension at most one over a
field, with its reduced structure, is affine as soon as it is not proper when one-dimensional. -/
theorem isAffine_componentIdealSheafData (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (Z : irreducibleComponents X)
    (hprop : topologicalKrullDim (componentIdealSheafData Z).subscheme = 1 →
      ¬ IsProper ((componentIdealSheafData Z).subschemeι ≫ f)) :
    IsAffine (componentIdealSheafData Z).subscheme := by
  set C := (componentIdealSheafData Z).subscheme
  set r := (componentIdealSheafData Z).subschemeι
  have hdimC : topologicalKrullDim C ≤ 1 :=
    (topologicalKrullDim_componentIdealSheafData_le Z).trans hdim
  have _ : IsIntegral C := isIntegral_componentIdealSheafData Z
  have _ : LocallyOfFiniteType (r ≫ f) := locallyOfFiniteType_comp r f
  rcases eq_or_lt_of_le hdimC with hdim1 | hdim0
  · have hcurve : IsCurve k (r ≫ f) :=
      { toIsVariety := { }
        topologicalKrullDim_eq_one := hdim1 }
    rcases isAffine_or_isProjectiveMorphism k (r ≫ f) with h | h
    · exact h
    · exact absurd (isProper_of_isProjectiveMorphism (r ≫ f) h) (hprop hdim1)
  · have hzero : topologicalKrullDim C = 0 := by
      refine le_antisymm (dimension_le_zero_of_lt_one hdim0) ?_
      have _ : IrreducibleSpace C := Subtype.irreducibleSpace Z.2.1
      obtain ⟨x⟩ := (inferInstance : Nonempty C)
      have _ : Nonempty (IrreducibleCloseds C) :=
        ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    exact isAffine_of_finiteType_of_dimension_zero k (r ≫ f) hzero

/-! ### Tag 0A28 -/

/-- Tag 0A28, with the two inputs of the inner claim of Tag 0A27 carried. -/
theorem isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hcomponent : ∀ Z : irreducibleComponents X,
      topologicalKrullDim (componentIdealSheafData Z).subscheme = 1 →
        ¬ IsProper ((componentIdealSheafData Z).subschemeι ≫ f)) :
    IsAffine X := by
  classical
  have _ : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hfinite : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  have _ : Finite (irreducibleComponents X) := hfinite.to_subtype
  have _ : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (irreducibleComponents X)
  set e : irreducibleComponents X ≃ Fin n := Fintype.equivFin _
  set Y : Fin n → Scheme.{u} := fun i => (componentIdealSheafData (e.symm i)).subscheme
  set r : ∀ i : Fin n, Y i ⟶ X := fun i => (componentIdealSheafData (e.symm i)).subschemeι with hrr
  have _ (i : Fin n) : IsAffine (Y i) :=
    isAffine_componentIdealSheafData k f hdim (e.symm i) (hcomponent (e.symm i))
  have hcover : (⋃ i : Fin n, Set.range (r i).base) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃₀ irreducibleComponents X := by simp [sUnion_irreducibleComponents]
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨e ⟨Z, hZ⟩, ?_⟩
    change x ∈ Set.range (componentIdealSheafData (e.symm (e ⟨Z, hZ⟩))).subschemeι.base
    rw [e.symm_apply_apply, range_subschemeι_componentIdealSheafData]
    exact hxZ
  set q : (∐ Y) ⟶ X := Limits.Sigma.desc r with hq
  have _ : Surjective q :=
    Surjective.sigmaDesc_of_union_range_eq_univ (by simpa [hq, hrr] using hcover)
  exact Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective q

end Stacks.AffineNoProperComponent

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0A28].** Let `k` be a field and let `X` be a separated scheme of finite type
over `k` with `dim(X) ≤ 1`. If no irreducible component of `X`, taken with its reduced induced
closed subscheme structure, is proper over `k` of dimension one, then `X` is an affine scheme.

Each component is integral, and separated and of finite type over `k` of dimension at most one.
A one-dimensional component is therefore a curve over `k`, so [Stacks, Tag 0A27] makes it affine
or H-projective over `k`, and the latter would make it proper over `k`, which `hcomponent`
forbids; a zero-dimensional component is affine by [Stacks, Tag 06LH]. The components are
finitely many, their coproduct is affine, and the induced morphism to `X` is finite and
surjective, so [Stacks, Tag 01YQ] makes `X` affine. -/
@[stacks 0A28]
theorem isAffine_of_topologicalKrullDim_le_one_of_forall_component_not_isProper
    (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hcomponent : ∀ Z : irreducibleComponents X,
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
          (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subscheme = 1 →
        ¬ IsProper ((Scheme.IdealSheafData.vanishingIdeal
          (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds X)).subschemeι ≫ f)) :
    IsAffine X :=
  Stacks.AffineNoProperComponent.isAffine_of_topologicalKrullDim_le_one_of_forall_not_isProper
    k f hdim hcomponent

end AlgebraicGeometry

end
