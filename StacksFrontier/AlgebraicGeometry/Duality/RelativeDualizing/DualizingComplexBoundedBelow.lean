module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing

/-!
# A dualizing complex on a quasi-compact scheme is bounded below

Over every affine open a dualizing complex on a locally Noetherian scheme is the associated sheaf
of a dualizing complex over the ring of sections, which is cohomologically bounded
(`Dualizing.IsDualizingComplex.bounded`). A finite affine cover bounds the cohomology of the
whole complex from below.

## Main results

* `Stacks.Duality.isBoundedBelow_of_isDualizingComplex`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Duality

/-- On an affine open where `K` has a dualizing model, the cohomology sheaves of `K` vanish in
all sufficiently negative degrees after restriction to that open. -/
theorem exists_isZero_restrict_homology_of_hasDualizingModelOn {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U) (h : HasDualizingModelOn K U hU) :
    ∃ a : ℤ, ∀ i < a, IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  obtain ⟨⟨a, ha⟩, -⟩ := Dualizing.IsDualizingComplex.bounded.{u, u} hω
  refine ⟨a, fun i hi => ?_⟩
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) :=
    DerivedCategory.isZero_of_isGE ω a i hi
  exact IsZero.of_iso
    (((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).map_isZero hz))
    (((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω)

end Stacks.Duality

end
