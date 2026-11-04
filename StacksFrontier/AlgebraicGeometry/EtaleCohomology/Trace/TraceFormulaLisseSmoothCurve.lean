module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCurveTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCompactificationChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesLocallyConstantTransport
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The trace formula for a lisse complex on a smooth curve without rational points

Let `k` be a finite field, `U` a smooth curve over `k` without `k`-rational points, `Λ` a finite
ring whose cardinality is prime to that of `k`, and `K` a bounded complex of sheaves of
`Λ`-modules on `U_étale` locally constant with finite projective values. For every
compactification `j` of `U` over `k`, the trace formula

`Tr(π_U^* | RΓ_c(U_k̄, K)) = ∑_{x ∈ U(k)} Tr(π_x | K_x̄) = 0`

holds: through the smooth projective model `Ū` of `U` this is
`Stacks.EtaleCohomology.canonicalTraceFormula_of_lisse_of_isEmpty`, whose perfectness input is
[Stacks, Tag 03TV] for the projective curve `Ū` (the sheaves extended by zero lie in `D_ctf`), and
the formula does not depend on the compactification
(`Stacks.EtaleCohomology.canonicalTraceFormula_iff_of_compactifications`).

## Main results

* `Stacks.EtaleCohomology.canonicalTraceFormula_of_lisse_smoothCurve`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 3–9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} (pU : U ⟶ Spec (.of k))
  [IsCurve k pU] [Smooth pU]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  {Λ : Type} [Ring Λ] [Finite Λ] (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k))

/-- The smooth projective model of a smooth curve over a perfect field, as a compactification. -/
theorem exists_compactification_isCurve_isProjective :
    ∃ J : CompactificationOf (Over.mk pU), IsCurve k J.toBase ∧ IsProjective J.toBase := by
  obtain ⟨-, Y, q', j', hj', hjq, hcurve, hproj, -, -, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k pU
      (isRegular_of_smooth_over_field pU)
  have : IsProper q' := isProper_of_isProjectiveMorphism q' hproj
  let J : CompactificationOf (Over.mk pU) :=
    ⟨StructuredArrow.mk (Y := Over.mk q') (Over.homMk (U := Over.mk pU) j' hjq),
      ⟨inferInstanceAs (IsOpenImmersion j'), inferInstanceAs (IsProper q')⟩⟩
  exact ⟨J, hcurve, (isProjective_iff_isProjectiveMorphism_of_isAffine q').2 hproj⟩

/-- **The perfectness input through a projective curve compactification**: `RΓ_c(U_k̄, D)` is
perfect for every sheaf `D` on `U_étale` locally constant with finite projective values over a
finite ring, by [Stacks, Tag 03TV]. -/
theorem lissePerfectness_of_isCurve_of_isProjective (J : CompactificationOf (Over.mk pU))
    (hcurve : IsCurve k J.toBase) (hproj : IsProjective J.toBase) :
    LissePerfectness J kbar := by
  intro R _ _ D hD
  let B := BigEtaleSite.containing J.space
  have hY : B.Contains J.space := BigEtaleSite.contains_containing J.space
  have hU : B.Contains U := Scheme.size_lt_of_isOpenImmersion J.immersion hY
  exact isPerfect_compactSupportFrobeniusCohomology_of_isCtf_of_isProjective B R
    (X := ⟨U, hU⟩) J kbar hY hcurve hproj _
    (isCtf_singlePlus_of_isFiniteProjectiveLocallyConstant B (⟨U, hU⟩ : B.Scheme) D hD)

include hcop in
/-- **The trace formula for a bounded complex of lisse sheaves on a smooth curve without
rational points**, through any compactification: both sides vanish. This is the case of
[Stacks, Tag 03UG] to which Step 3 reduces, proved by Steps 4–9. -/
theorem canonicalTraceFormula_of_lisse_smoothCurve [IsEmpty (rationalPoints pU)]
    (J : CompactificationOf (Over.mk pU)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (a b : ℤ) [K.obj.IsStrictlyGE a] [K.obj.IsStrictlyLE b]
    (hK : ∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology
      (K.obj.X n)) :
    CanonicalTraceFormula Λ kbar p q hcard pU J K := by
  obtain ⟨J', hcurve, hproj⟩ := exists_compactification_isCurve_isProjective pU
  refine (canonicalTraceFormula_iff_of_compactifications Λ
    (fun _ E => torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E) kbar p q hcard
    pU J' J K).1 ?_
  exact canonicalTraceFormula_of_lisse_of_isEmpty J' kbar p q hcard hcop
    (lissePerfectness_of_isCurve_of_isProjective pU kbar J' hcurve hproj) K a b hK

end Stacks.EtaleCohomology

end
