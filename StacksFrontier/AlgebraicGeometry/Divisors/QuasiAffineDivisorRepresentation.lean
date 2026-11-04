module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineGlobalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# An invertible module on a quasi-affine Noetherian scheme is the sheaf of a divisor

Let `X` be a Noetherian quasi-affine scheme and let `N` be an invertible `𝒪_X`-module. Then
`N ≅ 𝒪_X(D)` for an effective Cartier divisor `D ⊆ X`.

This is the quasi-affine case of [Stacks, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM),
whose general statement represents an invertible module as a *difference* `𝒪_X(D - D')`; on a
quasi-affine scheme the second divisor can be taken empty.

## Main results

* `Stacks.Divisors.finite_schemeAssociatedPoints`: a Noetherian scheme has finitely many
  associated points.
* `Stacks.Divisors.exists_isEffectiveCartierDivisor_iso_invertibleSheaf_of_isQuasiAffine`:
  the representation `N ≅ 𝒪_X(D)`.

## What is not proved here, and why the tag is not attached

Tag 0AYM also asserts a *refinement*: given a finite `E ⊆ X` the divisors may be chosen with
`E ∩ D = ∅`. That refinement is not proved here, so the covering set of the tag's quasi-affine
clause is incomplete and no `@[stacks 0AYM]` attribute is placed on the declaration below.

The refinement is one lemma away. Transporting the nonvanishing locus along the isomorphism
produced by Tag 01X0, by `Stacks.SheafOfModules.nonvanishingLocus_sectionsMap`, and reading the
result through `Stacks.Divisors.nonvanishingLocus_canonicalSections`
(`𝒪_X(D)`'s canonical section vanishes exactly on `D`) gives
`Stacks.SheafOfModules.nonvanishingLocus N (sectionsOfTop N s) = (D.supportSet)ᶜ` directly. What
is missing is the bridge identifying the two germ spellings of "s does not vanish at x": the
scheme-level `(N.presheaf.Γgerm x).hom s ∉ Stacks.ModuleStalk.maximalSmul N x` of
`Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff` — which is the form Tag 0F20 delivers and
Tag 0AYL consumes — and the ringed-space
`Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toSheafedSpace N.val x ⊤ _ s ∉
IsLocalRing.maximalIdeal (ringStalk X.toSheafedSpace x) • ⊤` of
`Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_iff`. The two are not definitionally
equal and the repository carries no `Γgerm`/`grpGerm` comparison. Once that comparison exists,
`Disjoint E D.supportSet` follows from the membership `E ⊆ X_s` that Tag 0F20 already supplies,
and the clause can be tagged.

## References

* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 0AYL](https://stacks.math.columbia.edu/tag/0AYL)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **The associated points of a Noetherian scheme are finitely many.** -/
theorem finite_schemeAssociatedPoints (X : Scheme.{u}) [IsNoetherian X] :
    (schemeAssociatedPoints X).Finite := by
  have hc : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _
  simpa [schemeAssociatedPoints] using AlgebraicGeometry.associatedPoints_inter_finite
    (SheafOfModules.unit X.ringCatSheaf) ⊤ (by simpa using isCompact_univ)

/-- **The quasi-affine case of [Stacks, Tag 0AYM].** On a Noetherian quasi-affine scheme every
invertible `𝒪_X`-module is the invertible sheaf `𝒪_X(D)` of an effective Cartier divisor `D`,
that is, the second divisor of the general difference representation may be taken empty.

The finite-avoidance refinement of Tag 0AYM is not proved; see the module docstring. -/
theorem exists_isEffectiveCartierDivisor_iso_invertibleSheaf_of_isQuasiAffine
    (X : Scheme.{u}) [IsNoetherian X] [X.IsQuasiAffine] (N : X.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    ∃ D : X.IdealSheafData, IsEffectiveCartierDivisor D ∧ Nonempty (N ≅ invertibleSheaf' D) := by
  have hinv : Stacks.Ample.IsInvertibleModule X N := hN
  obtain ⟨s, -, hsub, -⟩ :=
    Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite
      N (finite_schemeAssociatedPoints X) ⊤ (by simp)
  have hreg : AlgebraicGeometry.IsRegularSection X.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.SheafOfModules.sectionsOfTop N s) := by
    refine (isRegularSection_iff_forall_associatedPoint_notMem_maximalSmul N
      (Stacks.SheafOfModules.sectionsOfTop N s)).2 fun x hx => ?_
    rw [Stacks.SheafOfModules.sectionsOfTop_eval_top N s]
    exact (Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff X N s x).1 (hsub hx)
  exact ⟨_, (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection
    X N _).2 hreg, ⟨(AlgebraicGeometry.existsUnique_invertibleSheafIso_zeroScheme
      X N _ hreg).exists.choose.symm⟩⟩

end Stacks.Divisors

end
