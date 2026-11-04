module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresAffineCase
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankStalkBasis

/-!
# Stacks 0811 when the generic fibre rank is constant

With the rank of `F` at the generic point of the fibre the same at every point of the
distinguished open `U`, the two reductions of Remark 38.30.1 ([Stacks, Tag 080Y]) bring the
strict-transform problem of [Stacks, Tag 0811] to the affine case solved by
[Stacks, Tag 0810]: one `U`-admissible blowup makes the boundary an effective Cartier divisor,
and then the problem is local on the base, where [Stacks, Tag 01WS] cuts that divisor out on an
affine open by a single nonzerodivisor.

## Main results

* `AlgebraicGeometry.FlatteningSituation.isSolvable_of_constantRank`: the statement above.

## Implementation notes

The locality hypothesis of `AlgebraicGeometry.StrictTransformProblem.isSolvable_of_local` is
quantified over every strict-transform problem carrying the same property, so it is discharged
by `AlgebraicGeometry.freeOnSurjectiveOpen_of_cover` after rewriting the property of that problem
into `AlgebraicGeometry.FreeOnSurjectiveOpen` with the supplied equality of properties.

On the affine open produced by [Stacks, Tag 01WS] the inverse image of the distinguished open is
the basic open of the nonzerodivisor: the complement of the distinguished open is the support of
the exceptional divisor, which on that affine open is the zero locus of the principal ideal the
nonzerodivisor generates. The section of the open subscheme is
`AlgebraicGeometry.Scheme.Hom.appLE` of the inclusion, for which
`AlgebraicGeometry.Scheme.basicOpen_appLE` computes the basic open.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FlatteningSituation

/-- **The locality on the base of `AlgebraicGeometry.FreeOnSurjectiveOpen`, in the shape the
local-global reduction of [Stacks, Tag 080Y] consumes it.** -/
theorem freeOnSurjectiveOpen_local (D : FlatteningSituation.{u})
    (E : StrictTransformProblem.{u}) (hEP : @E.P = @D.problem.P) {ι : Type} [Finite ι]
    (W : ι → E.S.Opens) (hW : ∀ i, IsCompact (W i : Set E.S))
    (hcover : (⋃ i, (W i : Set E.S)) = Set.univ)
    (h : ∀ i, (E.restrict (W i) (hW i)).P (E.restrict (W i) (hW i)).f
      (E.restrict (W i) (hW i)).F) :
    E.P E.f E.F := by
  have hEP' : ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) (G : Y.Modules),
      E.P g G = FreeOnSurjectiveOpen g G := fun {Y T} g G ↦
    congrFun (congrFun (congrFun (congrFun hEP Y) T) g) G
  rw [hEP']
  refine freeOnSurjectiveOpen_of_cover E.f E.F W hcover fun i ↦ ?_
  rw [← hEP']
  exact h i

/-- **[Stacks, Tag 0811] when the generic fibre rank is constant.** One `U`-admissible blowup
makes the complement of the distinguished open an effective Cartier divisor, the problem is then
local on the base, and on an affine open where that divisor is cut out by a nonzerodivisor the
affine engine [Stacks, Tag 0810] closes the case. -/
theorem isSolvable_of_constantRank (D : FlatteningSituation.{u}) (r : ℕ)
    (hr : ∀ x : D.X, D.f.base x ∈ D.U → D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} →
      FreeAtPointOfRank D.F x r) :
    D.IsSolvable := by
  classical
  obtain ⟨C, hCfp, hCU, hbdry⟩ := cartierBoundaryReduction D.U D.compact_U
  refine D.problem.isSolvable_of_transform C hCfp hCU
    (D.isSolvable_transform C hCfp hCU ?_)
  set D₁ := D.transform C hCfp hCU with hD₁
  have hr₁ := D.freeAtPointOfRank_transform C hCfp hCU r hr
  refine StrictTransformProblem.isSolvable_of_local D₁.problem
    (fun E hEP ↦ D₁.freeOnSurjectiveOpen_local E (by rw [hEP])) fun y ↦ ?_
  -- Tag 01WS: on an affine open the exceptional divisor is cut out by a nonzerodivisor.
  obtain ⟨V, hyV, g, -, hgideal⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor (exceptionalIdeal C)
      inferInstance y
  have : IsAffine V.1.toScheme := V.2
  have hVle : (⊤ : V.1.toScheme.Opens) ≤ V.1.ι ⁻¹ᵁ V.1 := fun v _ ↦ v.2
  set a : Γ(V.1.toScheme, ⊤) := V.1.ι.appLE V.1 ⊤ hVle g with ha
  -- The inverse image of the distinguished open is the basic open of that nonzerodivisor.
  have hbasic : (V.1.ι ⁻¹ᵁ (blowUpToBase C ⁻¹ᵁ D.U) : V.1.toScheme.Opens) =
      V.1.toScheme.basicOpen a := by
    rw [ha, Scheme.basicOpen_appLE, top_inf_eq]
    refine TopologicalSpace.Opens.ext (Set.ext fun v ↦ ?_)
    show (blowUpToBase C).base (V.1.ι.base v) ∈ D.U ↔ V.1.ι.base v ∈ (blowUp C).basicOpen g
    have hsupp : V.1.ι.base v ∈ ((exceptionalIdeal C).support : Set (blowUp C)) ↔
        ¬ ((blowUpToBase C).base (V.1.ι.base v) ∈ D.U) := by
      rw [hbdry]
      exact Iff.rfl
    have h1 := Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := exceptionalIdeal C) (U := V) v.2
    rw [hgideal, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at h1
    have hzl : V.1.ι.base v ∈ ((exceptionalIdeal C).support : Set (blowUp C)) ↔
        V.1.ι.base v ∉ (blowUp C).basicOpen g := by
      refine h1.trans ⟨fun hz ↦ hz g (Set.mem_singleton g), fun hz t ht ↦ ?_⟩
      rw [Set.mem_singleton_iff] at ht
      exact ht ▸ hz
    exact not_iff_not.mp (hsupp.symm.trans hzl)
  have : IsAffine (D₁.restrict V.1 V.2.isCompact).S := V.2
  refine ⟨V.1, V.2.isCompact, hyV, D₁.isSolvable_restrict V.1 V.2.isCompact ?_⟩
  refine isSolvable_of_affine_of_basicOpen (D₁.restrict V.1 V.2.isCompact) a hbasic r
    fun x hx hgen ↦ ?_
  refine nonempty_basis_stalk_of_freeAtPointOfRank _ x r
    (D₁.freeAtPointOfRank_restrict V.1 V.2.isCompact r hr₁ x ?_ hgen)
  show (D₁.restrict V.1 V.2.isCompact).f.base x ∈
    (V.1.ι ⁻¹ᵁ (blowUpToBase C ⁻¹ᵁ D.U) : V.1.toScheme.Opens)
  rw [hbasic]
  exact hx

end FlatteningSituation

end AlgebraicGeometry

end
