module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeFinCharts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseCechColumnsFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseCohomologyReduction

/-!
# Crystalline cohomology of a proper smooth scheme over a base with zero divided power ideal is
finite and bounded

Let `(p, (S, 0, 0), X)` be a global crystalline situation whose divided power base `S = Spec R` is
affine with zero divided power ideal (for instance `X/S₀`, `S₀` the closed fibre of a divided power
base, `...GlobalCrystallineSituation.trivialBaseSituation`), `p` nilpotent in `R`, `R` Noetherian,
and `X ⟶ S` proper and smooth.  For a crystal `N` in finite locally free modules on `CRIS(X/S)`,
every cohomology module of `RΓ(CRIS(X/S), N) ∈ D⁺(Mod_R)` is a finite `R`-module, and they vanish
in large degrees.

The proof is the one of [Stacks, Tag 07N5]: cover `X` by finitely many affine charts with smooth
lifts carrying étale coordinates (`...CechEnvelope.exists_fin_cover_smoothLift_etaleCoordinates`);
`RΓ(CRIS(X/S), N)` is computed by the Čech–de Rham double complex `B` of the smooth-lift objects
(`...CechEnvelope.cechDeRhamHomologyIso`); over the zero divided power ideal `B` is rowwise
quasi-isomorphic to the Čech–de Rham double complex `C = ∏_x N_X(U_x) ⊗ Ω^•_{U_x/R}` of `X`
(`...CechEnvelope.trivialRowsHomologyIso`); and the columns of `C` are the Čech complexes of
coherent modules on the proper `X`, with finite cohomology vanishing above the size of the cover,
while `C` vanishes in de Rham degrees above the relative dimension.

## Main results

* `...CechEnvelope.moduleFinite_and_bounded_homology_of_ideal_eq_bot` — **the finiteness and the
  boundedness**, in the form `∃ b, ∀ i > b, H^i = 0` and `∀ i, H^i` finite.
* `...CechEnvelope.moduleFinite_and_bounded_homology_trivialBaseSituation` — the same for `X/S₀`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology

universe v₂ v₃ u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

variable {T : GlobalCrystallineSituation.{u}} [IsAffine T.S.scheme]
  [IsNoetherianRing Γ(T.S.scheme, ⊤)] [IsProper (sourceToBase T)] [T.X.IsSeparated]
  [CompactSpace T.X]
  [HasDerivedCategory.{v₂} (BigModuleSheaf T)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(T.S.scheme, ⊤))]

/-- **The crystalline cohomology of a proper smooth scheme over an affine Noetherian base with
zero divided power ideal is finite and bounded.**  Let `(p, (S, 0, 0), X)` be a global
crystalline situation with `S` affine, `R = Γ(S, 𝒪_S)` Noetherian, `p` nilpotent in `R`, and
`X ⟶ S` proper and smooth (`X ⟶ S₀ = S` smooth).  For a crystal `N` in finite locally free modules
on `CRIS(X/S)`, the cohomology modules of `RΓ(CRIS(X/S), N) ∈ D⁺(Mod_R)` vanish in large degrees
and are finite `R`-modules in every degree. -/
theorem moduleFinite_and_bounded_homology_of_ideal_eq_bot
    (hp : IsNilpotent (T.p : Γ(T.S.scheme, ⊤))) (hI : (baseSectionsRing T).ideal = ⊥)
    (hsm : Smooth T.toClosedFiber)
    (N : SheafOfModules.{u} (crystallineStructureSheaf T))
    (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) :
    (∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(T.S.scheme, ⊤)) i).obj
        (DerivedCategory.Plus.ι.obj
          ((derivedBigModuleGlobalSections T).obj ((bigModuleULift T).obj N))))) ∧
      ∀ i : ℤ, Module.Finite Γ(T.S.scheme, ⊤)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(T.S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj
            ((derivedBigModuleGlobalSections T).obj ((bigModuleULift T).obj N)))) := by
  obtain ⟨k, U, hUaff, hU, hL⟩ := exists_fin_cover_smoothLift_etaleCoordinates hsm
  have : ∀ i, IsAffine (U i) := hUaff
  choose L d t ht using hL
  have hN' : N.IsQuasicoherentOnSite := hN.isQuasicoherentOnSite
  obtain ⟨D, hD⟩ := exists_isZero_trivialCechDeRhamDoubleComplex_X N U hN'
  have hfin : ∀ a j : ℕ, Module.Finite Γ(T.S.scheme, ⊤)
      (((alternatingCofaceMapComplex _).obj ((trivialCechDeRhamDoubleComplex U N hN').X a)).homology
        j) :=
    fun a j ↦ moduleFinite_homology_trivialCechDeRhamDoubleComplex_X N hU hN hN' a j
  have hcov : ⨆ i, (chartOpen U i).obj = ⊤ :=
    eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hU x)
  have hex : ∀ a j : ℕ, k < j → IsZero
      (((alternatingCofaceMapComplex _).obj ((trivialCechDeRhamDoubleComplex U N hN').X a)).homology
        j) := fun a j hj ↦
    isZero_homology_trivialColumnPresheaf N a (chartOpen U) hcov
      (isQuasicoherentOnSite_restrictSheafOfModules hN') j (by simp; omega)
  refine ⟨⟨((D + k : ℕ) : ℤ), fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    exact isZero_homology_derivedBigModuleGlobalSections_of_columns hp hU L hI t ht N hN' D k hD
      hex j (by omega)
  · by_cases hi : i < 0
    · have : Subsingleton ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} Γ(T.S.scheme, ⊤)) i).obj (DerivedCategory.Plus.ι.obj
            ((derivedBigModuleGlobalSections T).obj ((bigModuleULift T).obj N)))) :=
        ModuleCat.isZero_iff_subsingleton.1
          (isZero_homology_derivedBigModuleGlobalSections_of_neg hp hU L N hN' i hi)
      infer_instance
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      exact moduleFinite_homology_derivedBigModuleGlobalSections_of_columns hp hU L hI t ht N hN'
        D hD hfin j

section TrivialBaseSituation

variable (S : GlobalCrystallineSituation.{u})

variable [IsAffine S.S.scheme] [IsNoetherianRing Γ((trivialBaseSituation S).S.scheme, ⊤)]
  [IsProper (sourceToBase (trivialBaseSituation S))] [S.X.IsSeparated] [CompactSpace S.X]
  [HasDerivedCategory.{v₂} (BigModuleSheaf (trivialBaseSituation S))]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤))]

/-- **The crystalline cohomology of `X/S₀` is finite and bounded**, `S₀ = Spec R` the closed fibre
of an affine divided power base with zero divided power ideal: for `X ⟶ S₀` proper and smooth,
`R` Noetherian, `p` nilpotent in `R` and `N` a crystal in finite locally free modules on
`CRIS(X/S₀)`, the cohomology modules of `RΓ(CRIS(X/S₀), N) ∈ D⁺(Mod_R)` vanish in large degrees
and are finite `R`-modules. -/
theorem moduleFinite_and_bounded_homology_trivialBaseSituation
    (hp : IsNilpotent ((trivialBaseSituation S).p : Γ((trivialBaseSituation S).S.scheme, ⊤)))
    (hsm : Smooth (trivialBaseSituation S).toClosedFiber)
    (N : SheafOfModules.{u} (crystallineStructureSheaf (trivialBaseSituation S)))
    (hN : IsFiniteLocallyFreeQuasicoherentCrystal N) :
    (∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
        (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
          ((bigModuleULift (trivialBaseSituation S)).obj N))))) ∧
      ∀ i : ℤ, Module.Finite Γ((trivialBaseSituation S).S.scheme, ⊤)
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
            ((bigModuleULift (trivialBaseSituation S)).obj N)))) := by
  have : (trivialBaseSituation S).X.IsSeparated := ‹S.X.IsSeparated›
  have : CompactSpace (trivialBaseSituation S).X := ‹CompactSpace S.X›
  exact moduleFinite_and_bounded_homology_of_ideal_eq_bot hp
    (baseSectionsRing_trivialBaseSituation_ideal (S := S)) hsm N hN

end TrivialBaseSituation

end Crystalline.GlobalCrystallineSituation.CechEnvelope
