module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ClosedPointEvaluation
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.StacksAttribute

/-!
# An invertible module of positive degree on a proper curve is ample

The second paragraph of the proof of [Stacks, Tag 0B5X]: on a proper curve `X` over a field `k`,
positivity of the degree of an invertible `𝓛` produces a positive tensor power of `𝓛` with a
global section whose nonvanishing locus is nonempty and affine. That is the one input the
converse direction of the tag was missing, and this file assembles it and closes the
biconditional.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `Stacks.Topology.Dimension.finite_compl_and_isClosed_singleton_of_nonempty`: **the complement
  of a nonempty open subset of an irreducible space of dimension at most one is a finite set of
  closed points.** This is the set the section of the source is made to vanish on.
* `exists_one_le_lt_finrank_cohomologyOverField_zero_tensorPower`: **`h⁰(X, 𝓛^{⊗ n})` passes
  every bound.** For every `b` there is an `n ≥ 1` with `dim_k H⁰(X, 𝓛^{⊗ n}) > b`.
* `exists_tensorPower_section_ne_zero_sectionEvaluation_eq_zero`: **a nonzero section of a high
  power vanishing at prescribed closed points**, by the pigeonhole of the source.
* `exists_tensorPower_section_isAffineOpen_nonvanishingOpen`: **the second paragraph**, a power
  of `𝓛` with a section whose nonvanishing locus is nonempty and affine.
* `hasAffinePowerOfDegreePos_of_isCurve`: the same conclusion read at the name
  `./Vanishing.lean` gives it, which discharges the hypothesis the statements there carried.
* `isAmple_of_invertibleCurveDegree_pos_of_isCurve`: **the converse direction of
  [Stacks, Tag 0B5X]**.
* `isAmple_iff_invertibleCurveDegree_pos`: **[Stacks, Tag 0B5X]**, both directions.

## The argument

*The growth.* `AlgebraicGeometry.le_finrank_cohomologyOverField_zero_tensorPower` of
`./CurveInputs.lean` is the Riemann–Roch bound `n · deg(𝓛) + χ(X, 𝒪_X) ≤ h⁰(X, 𝓛^{⊗ n})`, proved
with no hypothesis. Positivity of the degree makes `n · deg(𝓛) ≥ n`, so taking `n` past
`b + h¹(X, 𝒪_X)` makes the left-hand side exceed `b`.

*The shape of the complement.* A closed subset of an irreducible space that is not the whole
space contains no irreducible component, the sole component being the whole space. So
`Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset` makes it finite and
`Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset` makes each of
its points closed; this is where the dimension bound is used.

*The section.* The residue field at a closed point is finite over `k`, so the product of the
residue fields along a finite set `E` of closed points is a finite-dimensional `k`-vector space
whose dimension does not depend on `n`. Once `h⁰(X, 𝓛^{⊗ n})` exceeds it, the evaluation map of
`./ClosedPointEvaluation.lean` has a nonzero kernel, which is a nonzero section vanishing on `E`.

*The affineness.* Taking `E` to be the complement of a nonempty affine open `U` puts `X_s`
inside `U`, so `X_s = U ∩ X_s` is affine by [Stacks, Tag 01PV]. This is the source's "choosing
the points so that the complement is affine makes `X_s` affine as well", and it is what makes
[Stacks, Tag 0A27] unnecessary here.

*The conclusion.* `AlgebraicGeometry.isAmple_of_exists_tensorPower_section_of_isCurve` of
`./CurveAmple.lean` turns such a section into ampleness of `𝓛`, through the third paragraph of
the source and [Stacks, Tag 01PT].

## Implementation notes

**Two invertibility classes appear.** `AlgebraicGeometry.SheafOfModules.IsInvertible` is what
the degree, the tensor powers and `AlgebraicGeometry.Scheme.Modules.IsAmple` are stated for,
while [Stacks, Tag 01PV] is stated over `Stacks.SheafOfModules.IsInvertible`;
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` crosses them with no hypothesis.
Invertibility of a tensor power is not an instance in this development, so it is named with a
`haveI` wherever a statement mentions it.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingLocus nonvanishingOpen sectionsOfTop)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
-- `hasSheafifyOpensMax` leaves its second universe undetermined; instance search picks it for the
-- tensor power sheaves here and the elaborator rejects the resulting term.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

universe u

namespace Stacks.Topology.Dimension

/-- **A proper closed subset of an irreducible space contains no irreducible component.** The
only irreducible component of an irreducible space is the whole space. -/
public theorem not_irreducibleComponent_subset_of_ne_univ {T : Type u} [TopologicalSpace T]
    [IrreducibleSpace T] {Z : Set T} (hZ : Z ≠ Set.univ) :
    ∀ C ∈ irreducibleComponents T, ¬ C ⊆ Z := by
  intro C hC hsub
  exact hZ (Set.univ_subset_iff.mp
    ((hC.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ C)).trans hsub))

/-- **The complement of a nonempty open subset of an irreducible Noetherian sober `T0` space of
Krull dimension at most one is a finite set of closed points.** The complement is closed and is
not the whole space, so it contains no irreducible component, and both halves follow from the
dimension bound. -/
public theorem finite_compl_and_isClosed_singleton_of_nonempty {T : Type u} [TopologicalSpace T]
    [IrreducibleSpace T] [T0Space T] [NoetherianSpace T] [QuasiSober T]
    (hdim : topologicalKrullDim T ≤ 1) (U : Opens T) (hU : (U : Set T).Nonempty) :
    ((U : Set T)ᶜ).Finite ∧ ∀ x : T, x ∉ U → IsClosed ({x} : Set T) := by
  have hclosed : IsClosed ((U : Set T)ᶜ) := U.isOpen.isClosed_compl
  have hne : ((U : Set T)ᶜ) ≠ Set.univ := by
    obtain ⟨x, hx⟩ := hU
    exact fun h => (h.symm ▸ Set.mem_univ x : x ∈ (U : Set T)ᶜ) hx
  have hcomp := not_irreducibleComponent_subset_of_ne_univ (T := T) hne
  exact ⟨finite_of_not_irreducibleComponent_subset hdim hclosed hcomp,
    fun x hx => isClosed_singleton_of_not_irreducibleComponent_subset hdim hclosed hcomp hx⟩

end Stacks.Topology.Dimension

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`h⁰(X, 𝓛^{⊗ n})` passes every bound.** On a proper curve over a field, if the degree of an
invertible module `𝓛` is positive then for every `b` there is an `n ≥ 1` with
`b < dim_k H⁰(X, 𝓛^{⊗ n})`.

This is the opening line of the "if" direction of [Stacks, Tag 0B5X]: the Riemann–Roch bound
`AlgebraicGeometry.le_finrank_cohomologyOverField_zero_tensorPower` reads

`n · deg(𝓛) + h⁰(X, 𝒪_X) - h¹(X, 𝒪_X) ≤ dim_k H⁰(X, 𝓛^{⊗ n})`,

and `deg(𝓛) ≥ 1` makes `n · deg(𝓛) ≥ n`, so `n = b + h¹(X, 𝒪_X) + 1` suffices. **No
hypothesis.** -/
public theorem exists_one_le_lt_finrank_cohomologyOverField_zero_tensorPower [IsCurve k f]
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 0 < invertibleCurveDegree k f hdim L) (b : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ b < Module.finrank k (cohomologyOverField k f
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)) 0) := by
  set a : ℕ := Module.finrank k
    (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) with ha
  set c : ℕ := Module.finrank k
    (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) with hc
  refine ⟨b + c + 1, by omega, ?_⟩
  have hbound := le_finrank_cohomologyOverField_zero_tensorPower k f hdim L ((b + c + 1 : ℕ) : ℤ)
  have hmul : ((b + c + 1 : ℕ) : ℤ) ≤ ((b + c + 1 : ℕ) : ℤ) * invertibleCurveDegree k f hdim L := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ invertibleCurveDegree k f hdim L from hdeg)
        (Int.natCast_nonneg (b + c + 1))
  have hane : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  rw [← ha, ← hc] at hbound
  have : (b : ℤ) < (Module.finrank k (cohomologyOverField k f
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((b + c + 1 : ℕ) : ℤ)) 0) : ℤ) := by
    push_cast at hbound hmul ⊢
    linarith
  exact_mod_cast this

/-- Integer tensor powers of an invertible module are invertible. -/
private theorem isInvertible_tensorPower (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℤ) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L n) :=
  tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

/-! ### A section vanishing at prescribed closed points -/

/-- **A nonzero global section of a high power of `𝓛` vanishing at prescribed closed points.**
Let `E` be a finite set of closed points of a proper curve over `k` and let `deg(𝓛) > 0`. Then
some `𝓛^{⊗ n}` with `n ≥ 1` has a nonzero global section whose evaluation at every point of `E`
is zero.

The residue field at a closed point is finite over `k`
(`AlgebraicGeometry.finite_residueFieldOverBase`), so the product of the residue fields along
`E` is a finite-dimensional `k`-vector space whose dimension does not depend on `n`. Taking `n`
with `dim_k H⁰(X, 𝓛^{⊗ n})` past that dimension makes the evaluation map have a nonzero kernel,
which is the pigeonhole of the source. -/
public theorem exists_tensorPower_section_ne_zero_sectionEvaluation_eq_zero [IsCurve k f]
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 0 < invertibleCurveDegree k f hdim L)
    (E : Finset X) (hE : ∀ x ∈ E, IsClosed ({x} : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (restrictScalarsOverBase k f).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))),
      s ≠ 0 ∧ ∀ x ∈ E, sectionEvaluation k f
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)) x s = 0 := by
  classical
  have (x : E) : Module.Finite k (residueFieldOverBase k f x.1) :=
    finite_residueFieldOverBase k f x.1 (hE x.1 x.2)
  obtain ⟨n, hn, hgt⟩ := exists_one_le_lt_finrank_cohomologyOverField_zero_tensorPower k f hdim L
    hdeg (Module.finrank k ((x : E) → residueFieldOverBase k f x.1))
  have := isInvertible_tensorPower L (n : ℤ)
  rw [(cohomologyOverFieldZeroLinearIso k f
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ))).toLinearEquiv.finrank_eq] at hgt
  have : Module.Finite k ((restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)))) :=
    Module.finite_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le _) hgt)
  obtain ⟨s, hsmem, hs0⟩ := (LinearMap.ker (LinearMap.pi fun x : E => sectionEvaluation k f
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)) x.1)).ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt hgt)
  refine ⟨n, hn, s, hs0, fun x hx => ?_⟩
  have h0 : ∀ y : E, sectionEvaluation k f
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)) y.1 s = 0 := fun y => by
    simpa using congrFun (LinearMap.mem_ker.mp hsmem) y
  exact h0 ⟨x, hx⟩

/-! ### The second paragraph of the proof of [Stacks, Tag 0B5X] -/

/-- **Positivity of the degree gives a power of `𝓛` with a global section whose nonvanishing
locus is nonempty and affine**, which is the second paragraph of the proof of
[Stacks, Tag 0B5X].

The curve is integral, so it has a nonempty affine open `U`, and the complement of `U` is a
finite set of closed points
(`Stacks.Topology.Dimension.finite_compl_and_isClosed_singleton_of_nonempty`). A nonzero section
`s` of a high power vanishing on that complement therefore has `X_s ⊆ U`, so `X_s = U ∩ X_s` is
affine by [Stacks, Tag 01PV],
`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`; and `X_s` is nonempty
because `X` is reduced and `s` is nonzero
(`AlgebraicGeometry.nonempty_nonvanishingLocus_of_ne_zero`).

This is where the source says "choosing the points so that the complement is affine makes `X_s`
affine as well". **No hypothesis.** -/
public theorem exists_tensorPower_section_isAffineOpen_nonvanishingOpen [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 0 < invertibleCurveDegree k f hdim L) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      (∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
        IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) := by
  classical
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨hfin, hcl⟩ :=
    Stacks.Topology.Dimension.finite_compl_and_isClosed_singleton_of_nonempty hdim U ⟨x, hxU⟩
  obtain ⟨n, hn, s, hs, hzero⟩ :=
    exists_tensorPower_section_ne_zero_sectionEvaluation_eq_zero k f hdim L hdeg
      hfin.toFinset fun y hy => hcl y (by simpa using hy)
  have := isInvertible_tensorPower L (n : ℤ)
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  refine ⟨n, hn, sectionsOfTop _ s,
    nonempty_nonvanishingLocus_of_ne_zero _ s hs, ?_⟩
  have hle : nonvanishingOpen (X := X.toRingedSpace)
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ))
      (sectionsOfTop _ s) ≤ U := by
    intro y hy
    by_contra hnot
    exact notMem_nonvanishingLocus_of_sectionEvaluation_eq_zero k f _ y s
      (hzero y (by simpa using hnot)) hy
  have h := Scheme.Modules.isAffineOpen_inf_nonvanishingOpen
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ))
    (sectionsOfTop _ s) U hU
  rwa [inf_eq_right.mpr hle] at h

/-! ### [Stacks, Tag 0B5X] -/

/-- **The converse direction of [Stacks, Tag 0B5X]: an invertible module of positive degree on a
proper curve is ample.** The second paragraph of the source, above, produces a power of `𝓛` with
a global section whose nonvanishing locus is nonempty and affine, and
`AlgebraicGeometry.isAmple_of_exists_tensorPower_section_of_isCurve` of `./CurveAmple.lean`
turns that into ampleness of `𝓛` through the third paragraph and [Stacks, Tag 01PT].

**No hypothesis beyond the tag's own.** -/
public theorem isAmple_of_invertibleCurveDegree_pos_of_isCurve [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 0 < invertibleCurveDegree k f hdim L) :
    Scheme.Modules.IsAmple X L :=
  isAmple_of_exists_tensorPower_section_of_isCurve k f L
    (exists_tensorPower_section_isAffineOpen_nonvanishingOpen k f hdim L hdeg)

end AlgebraicGeometry

end
