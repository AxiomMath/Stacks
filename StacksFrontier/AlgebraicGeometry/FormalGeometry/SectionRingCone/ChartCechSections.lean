module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ChartCechSections.QuotientSections

/-!
# Formal functions along the zero scheme of a section of an ample module, from the section ring

Let `L` be an ample invertible module on `X`, `A = Γ_*(X, L)` its section ring, `t₁, …, t_r ∈ A₁`
degree-one sections whose nonvanishing opens are affine and cover `X`, and `s` a global section
of `L` with image `f ∈ A₁` and zero scheme `Z(s)`. Let `I = (t₁, …, t_r) ⊆ A`.

If some power of `f` kills `H¹_I(A)` and `H²_I(A)`, then for every `m ≥ 0` the global sections of
`L^{⊗ m}` are the inverse limit of the global sections of the quotients
`L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}`:

`Γ(X, L^{⊗ m}) = lim_n Γ(X, L^{⊗ m} / Z(s)^{n+1} L^{⊗ m})`.

## Main results

* `isIdealPowerQuotientSectionsComplete_natTensorPow_of_localCohomology_torsion`: if some power
  of `f` kills `H¹_I(A)` and `H²_I(A)`, then for every `m ≥ 0` every compatible family of global
  sections of the quotients `L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}` comes from a unique global section of
  `L^{⊗ m}`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.LocalCohomology (powerQuotientShortComplex powerQuotientSESMap localCohomologyModule)

attribute [local instance] instVAddNatIntGradedLocalizedModule

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

universe u

namespace Stacks.Algebraization.SectionRingCone

/-- The Čech cocycles with coefficients in `M / f⁰ M = 0` vanish. -/
theorem kerCechDOne_powerQuotient_zero_eq_zero {R : Type u} [CommRing R] {r : ℕ}
    (fam : Fin r → R) (f : R) (M : ModuleCat.{u} R)
    (z : LinearMap.ker (Cech.cechD fam ((powerQuotientShortComplex f M 0).X₃ : Type u) 1)) :
    z = 0 := by
  have : Subsingleton ((powerQuotientShortComplex f M 0).X₃ : Type u) := by
    change Subsingleton ((M : Type u) ⧸ Stacks.LocalCohomology.powerSmulTop f M 0)
    rw [Submodule.Quotient.subsingleton_iff, Stacks.LocalCohomology.powerSmulTop,
      pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  have hloc : ∀ (t : Finset (Fin r))
      (w : Cech.cechMod fam ((powerQuotientShortComplex f M 0).X₃ : Type u) t), w = 0 := by
    intro t w
    induction w using LocalizedModule.induction_on with
    | h m u => rw [Subsingleton.elim m 0, LocalizedModule.zero_mk]
  exact Subtype.ext (DFinsupp.ext fun t ↦ hloc t.1 _)

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **Formal functions along `Z(s)` for the tensor powers of an ample module, from the section
ring.** Let `t₁, …, t_r ∈ A₁ = Γ(X, L)` have affine nonvanishing opens covering `X`, let
`I = (t₁, …, t_r) ⊆ A = Γ_*(X, L)`, and let `s ∈ Γ(X, L)` with image `f ∈ A₁`. If some power of
`f` kills `H¹_I(A)` and `H²_I(A)`, then for every `m ≥ 0` every compatible family of global
sections of the quotients `L^{⊗ m} / Z(s)^{n+1} L^{⊗ m}` comes from a unique global section of
`L^{⊗ m}`. -/
theorem isIdealPowerQuotientSectionsComplete_natTensorPow_of_localCohomology_torsion
    (hL : Stacks.Ample.IsAmple X L) [IsNoetherianRing (sectionRing L)] (s : Γ(L, ⊤))
    {r : ℕ} (fam : Fin r → powSections L 1) (hcov : ⨆ j, nvOpen L (fam j) = ⊤)
    (haff : ∀ j, IsAffineOpen (nvOpen L (fam j)))
    (hI : (Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))).FG)
    (h1 : ∃ c : ℕ, ∀ x : localCohomologyModule (sectionRing L)
      (Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))) hI
      (ModuleCat.of (sectionRing L) (sectionRing L)) 1, sectionDegreeOne L s ^ c • x = 0)
    (h2 : ∃ c : ℕ, ∀ x : localCohomologyModule (sectionRing L)
      (Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))) hI
      (ModuleCat.of (sectionRing L) (sectionRing L)) 2, sectionDegreeOne L s ^ c • x = 0)
    (m : ℕ) [(natTensorPow L m).IsQuasicoherent] :
    IsIdealPowerQuotientSectionsComplete (AlgebraicGeometry.zeroScheme X L s)
      (natTensorPow L m) := by
  intro σs hσs
  let Y : ∀ n : ℕ, LinearMap.ker (Cech.cechD (famRing L fam)
      ((powerQuotientShortComplex (sectionDegreeOne L s) (sectionRingModule (L := L)) n).X₃ :
        Type u) 1) := fun
    | 0 => 0
    | n + 1 => quotCechSection L hL fam s haff m n (σs n)
  have hY : ∀ n, Y n ∈ kerDegree (grading L) (famRing L fam)
      (powerQuotientShortComplex (sectionDegreeOne L s) (sectionRingModule (L := L)) n).X₃
      (quotientTowerPiece (sectionRingModule (L := L))
        (integerGrading (S := sectionRing L) (grading L)) (sectionDegreeOne L s) n) (m : ℤ)
    | 0 => zero_mem _
    | n + 1 => quotCechSection_mem_kerDegree L hL fam s haff m n (σs n)
  have hcompat : ∀ n, towerTransition (famRing L fam) (sectionRingModule (L := L))
      (sectionDegreeOne L s) (Nat.le_succ n) (Y (n + 1)) = Y n
    | 0 => kerCechDOne_powerQuotient_zero_eq_zero _ _ _ _
    | n + 1 => (towerTransition_quotCechSection L hL fam s haff m n (σs (n + 1))).trans
      (congrArg (quotCechSection L hL fam s haff m n) (hσs n (n + 1) (Nat.le_succ n)))
  obtain ⟨x, ⟨hxdeg, hxred⟩, huniq⟩ := existsUnique_mem_kerDegree_of_compatible
    (𝒜 := grading L) (fam := famRing L fam)
    (hc := fun j ↦ Stacks.ExternalGrading.of_mem_summand 1 (fam j))
    (M := sectionRingModule (L := L)) (𝒨 := integerGrading (S := sectionRing L) (grading L))
    (f := sectionDegreeOne L s) _ hI rfl (Stacks.ExternalGrading.of_mem_summand 1 _) one_pos
    h1 h2 (m : ℤ) Y hY hcompat
  obtain ⟨σ₀, hσ₀⟩ := exists_globalCechSection_eq L hL fam hcov m x hxdeg
  refine ⟨σ₀, fun n ↦ quotCechSection_injective L hL fam s haff m hcov n
    ((towerReduction_globalCechSection L hL fam s haff m n σ₀).symm.trans (hσ₀ ▸ hxred (n + 1))),
    fun t ht ↦ ?_⟩
  refine globalCechSection_injective L hL fam hcov m (Eq.trans ?_ hσ₀.symm)
  exact huniq _ ⟨globalCechSection_mem_kerDegree L hL fam m t, fun
    | 0 => kerCechDOne_powerQuotient_zero_eq_zero _ _ _ _
    | n + 1 => (towerReduction_globalCechSection L hL fam s haff m n t).trans
      (congrArg (quotCechSection L hL fam s haff m n) (ht n))⟩

end Stacks.Algebraization.SectionRingCone

end
