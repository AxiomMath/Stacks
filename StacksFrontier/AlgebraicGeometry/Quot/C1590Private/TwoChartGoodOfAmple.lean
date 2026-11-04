module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartDatumOfSections
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
import StacksFrontier.Algebra.Module.TwoTermComplex.Noetherian

/-!
# A good two-chart datum from an ample invertible module with two sections

Let `q : Y ⟶ T` be proper and flat with `T` affine and Noetherian, `L` an ample invertible module
on `Y`, and `σ₀`, `τ₀` global sections of a positive tensor power of `L` whose nonvanishing loci
are affine and cover `Y`. Then `Y` carries a good two-chart datum over `Γ(T, 𝒪_T)`
(`AlgebraicGeometry.C1590Private.exists_isGood_twoChartDatum`).

Serre vanishing (Stacks 0B5T,
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase`) gives `m₀` with
`H¹(Y, L^{⊗ m}) = 0` for `m ≥ m₀`. Replacing `σ₀`, `τ₀` by their `(m₀ + 1)`-st powers, which
have the same nonvanishing loci, the datum `AlgebraicGeometry.C1590Private.twoChartDatumOfSections`
of the powers has:

* surjective Čech differentials in every degree `k ≥ 1`, the obstruction being
  `H¹(Y, L^{⊗ n k}) = 0` (`AlgebraicGeometry.C1590Private.surjective_cechDiff_of_isZero_Hgroup`);
* finite section modules, which are quotients of `Γ(Y, L^{⊗ n k})`, finite over `Γ(T, 𝒪_T)`
  because `q` is proper (Stacks 02O6,
  `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`);
* projective section modules: they are kernels of the surjective Čech differentials between flat
  modules, hence flat, and finite over a Noetherian ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowerTrivialize Stacks.GradedSections Stacks.SectionProduct

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y T : Scheme.{u}} (q : Y ⟶ T)

/-- The sections of a flat scheme over an affine base over an affine open are flat over the
global functions of the base. -/
theorem flat_res_comp_appTop [IsAffine T] [Flat q] {W : Y.Opens} (hW : IsAffineOpen W) :
    ((Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp q.appTop.hom).Flat :=
  HasRingHomProperty.appLE @Flat q ‹_› ⟨⊤, isAffineOpen_top T⟩ ⟨W, hW⟩ (by simp)

/-- **A good two-chart datum from two sections of an ample module.** -/
theorem exists_isGood_twoChartDatum [IsAffine T] [IsLocallyNoetherian T] [IsProper q] [Flat q]
    (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L] (hL : Stacks.Ample.IsAmple Y L)
    {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (σ₀ τ₀ : powSections L n₀)
    (hσ : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L σ₀))
    (hτ : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L τ₀))
    (hcov : Stacks.AmpleFiniteAvoidance.nvOpen L σ₀ ⊔ Stacks.AmpleFiniteAvoidance.nvOpen L τ₀ = ⊤) :
    ∃ D : TwoChartDatum Y, D.IsGood q.appTop.hom := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨m₀, hm₀⟩ := Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
    Y T q inferInstance inferInstance inferInstance L hL
  -- pass to the `(m₀ + 1)`-st powers
  set σ := sectionPow L σ₀ m₀
  set τ := sectionPow L τ₀ m₀
  have e (ρ₀ : powSections L n₀) : Stacks.AmpleFiniteAvoidance.nvOpen L (sectionPow L ρ₀ m₀) =
      Stacks.AmpleFiniteAvoidance.nvOpen L ρ₀ := nonvanishingOpen_sectionPow L ρ₀ m₀
  have hσ' : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L σ) := e σ₀ ▸ hσ
  have hτ' : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L τ) := e τ₀ ▸ hτ
  have hcov' : Stacks.AmpleFiniteAvoidance.nvOpen L σ ⊔ Stacks.AmpleFiniteAvoidance.nvOpen L τ =
      ⊤ := by rw [e σ₀, e τ₀, hcov]
  set n := powDeg n₀ m₀
  have hn : ∀ j, m₀ ≤ powDeg n j := fun j => by
    rw [powDeg_eq]
    nlinarith [powDeg_eq n₀ m₀]
  set D := twoChartDatumOfSections hσ' hτ' hcov'
  have hsurj : ∀ k, 1 ≤ k → Function.Surjective (D.cechDiff k) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact surjective_cechDiff_of_isZero_Hgroup hσ' hτ' hcov' j (hm₀ _ (hn j) 1 one_pos)
  refine ⟨D, hsurj, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let := D.algebraU q.appTop.hom
  let := D.algebraV q.appTop.hom
  let := D.algebraUV q.appTop.hom
  -- finiteness
  set F := Stacks.TensorPowers.natTensorPow L (powDeg n j)
  have hF : F = Stacks.Ample.tensorPowModule Y L ((powDeg n j : ℕ) : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow _ L _
  have : F.IsCoherent := hF ▸
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_tensorPowModule L _
  have h0 := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology q F 0
  have hfin : Module.Finite Γ(T, ⊤) ((ModuleCat.restrictScalars q.appTop.hom).obj
      ((moduleGlobalSections Y).obj F)) :=
    Module.Finite.equiv ((ModuleCat.restrictScalars q.appTop.hom).mapIso
      (((moduleGlobalSections Y).rightDerivedZeroIsoSelf).app F)).toLinearEquiv
  have hfinS := finite_sections_of_finite hσ' hτ' hcov' q.appTop.hom j hfin
  refine ⟨hfinS, ?_⟩
  -- flatness and projectivity
  have : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian (⟨⊤, isAffineOpen_top T⟩ : T.affineOpens)
  have hUV : IsAffineOpen (D.U ⊓ D.V) := D.basicOpen_b ▸ hσ'.basicOpen D.b
  have : Module.Flat Γ(T, ⊤) Γ(Y, D.U) := flat_res_comp_appTop q hσ'
  have : Module.Flat Γ(T, ⊤) Γ(Y, D.V) := flat_res_comp_appTop q hτ'
  have : Module.Flat Γ(T, ⊤) Γ(Y, D.U ⊓ D.V) := flat_res_comp_appTop q hUV
  have : Module.Flat Γ(T, ⊤) (Γ(Y, D.U) × Γ(Y, D.V)) := Stacks.TwoTermComplex.flat_prod
  have hflat : Module.Flat Γ(T, ⊤) (D.sections q.appTop.hom (j + 1)) := by
    have := Stacks.TwoTermComplex.flat_ker_of_surjective (D.cechDiffLinear q.appTop.hom (j + 1))
      (hsurj (j + 1) (by omega))
    rwa [← TwoChartDatum.sections_eq_ker] at this
  have := hflat
  have := Module.finitePresentation_of_finite Γ(T, ⊤) (D.sections q.appTop.hom (j + 1))
  exact Module.Flat.projective_of_finitePresentation

end AlgebraicGeometry.C1590Private
