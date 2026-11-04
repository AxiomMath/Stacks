module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamColumns
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamTrivialBaseRows
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexFiniteness

/-!
# Crystalline cohomology over a base with zero divided power ideal, from the Čech–de Rham
complex of `X`

Let `(p, (S, 0, 0), X)` be a global crystalline situation over an affine base with zero divided
power ideal (for instance `X/S₀` over the closed fibre `S₀`), `R = Γ(S, 𝒪_S)`, and let
`U_i` be a finite cover of the separated scheme `X` by affine opens carrying smooth lifts with
étale coordinates.  For a quasi-coherent module `N` on `CRIS(X/S)`,

`H^j(RΓ(CRIS(X/S), N)) ≅ H^j(Tot B) ≅ H^j(Tot C)`

where `B` is the Čech–de Rham double complex of the smooth-lift cover
(`...CechEnvelope.cechDeRhamHomologyIso`) and `C` that of the trivial thickenings
`(U_x, U_x, 0)`, i.e. the Čech–de Rham double complex `∏_x N_X(U_x) ⊗ Ω^a_{U_x/R}` of `X`
(`...CechEnvelope.trivialRowsHomologyIso`).  This file draws the consequences for finiteness and
boundedness from the columns of `C`.

## Main results

* `CechEnvelope.moduleFinite_homology_derivedBigModuleGlobalSections_of_columns`
* `CechEnvelope.isZero_homology_derivedBigModuleGlobalSections_of_columns`
* `CechEnvelope.isZero_homology_derivedBigModuleGlobalSections_of_neg`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology

universe v₂ v₃ u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type} [Finite ι]
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (hU : ∀ x, ∃ i, x ∈ U i)
  (L : ∀ i, SmoothLift S (U i).ι) (hI : (baseSectionsRing S).ideal = ⊥) {d : ι → ℕ}
  (t : ∀ i, Fin (d i) → (L i).ring)
  (ht : ∀ i, (MvPolynomial.aeval (R := baseSectionsRing S) (t i)).toRingHom.Etale)
  (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
  [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **`H^j(RΓ(CRIS(X/S), N)) ≅ ULift H^j(Tot C)`**, `C` the Čech–de Rham double complex of the
trivial thickenings of the cover. -/
def homologyIsoTrivialTotal (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
        ((((Crystalline.CosimplicialDoubleComplex.functor _).obj
          (trivialCechDeRhamDoubleComplex U N hN)).total (ComplexShape.up ℤ)).homology (j : ℤ)) :=
  (cechDeRhamHomologyIso hp L hN hU j).symm ≪≫
    (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).mapIso
      (trivialRowsHomologyIso hp L hI t ht N hN (j : ℤ))

include hp hU hI ht in
/-- **Finiteness of crystalline cohomology from the columns of the Čech–de Rham complex of `X`**:
if the double complex `C` vanishes in de Rham degrees `> D` and the cohomology of each of its
columns is a finite `R`-module, `R` Noetherian, then every `H^j(RΓ(CRIS(X/S), N))` is a finite
`R`-module. -/
theorem moduleFinite_homology_derivedBigModuleGlobalSections_of_columns
    [IsNoetherianRing Γ(S.S.scheme, ⊤)] (D : ℕ)
    (hD : ∀ a, D < a → IsZero ((trivialCechDeRhamDoubleComplex U N hN).X a))
    (hfin : ∀ a j : ℕ, Module.Finite Γ(S.S.scheme, ⊤)
      (((alternatingCofaceMapComplex _).obj ((trivialCechDeRhamDoubleComplex U N hN).X a)).homology
        j))
    (j : ℕ) :
    Module.Finite Γ(S.S.scheme, ⊤)
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) := by
  have h := Crystalline.CosimplicialDoubleComplex.moduleFinite_homology_total
    (trivialCechDeRhamDoubleComplex U N hN) D hD hfin (j : ℤ)
  have hu : Module.Finite Γ(S.S.scheme, ⊤)
      ((ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
      ((((Crystalline.CosimplicialDoubleComplex.functor _).obj
        (trivialCechDeRhamDoubleComplex U N hN)).total (ComplexShape.up ℤ)).homology (j : ℤ))) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  exact Module.Finite.equiv
    (homologyIsoTrivialTotal hp hU L hI t ht N hN j).toLinearEquiv.symm

include hp hU hI ht in
/-- **Vanishing of crystalline cohomology above `D + m`** when the double complex `C` vanishes in
de Rham degrees `> D` and its columns are exact above `m`. -/
theorem isZero_homology_derivedBigModuleGlobalSections_of_columns (D m : ℕ)
    (hD : ∀ a, D < a → IsZero ((trivialCechDeRhamDoubleComplex U N hN).X a))
    (hex : ∀ a j : ℕ, m < j → IsZero
      (((alternatingCofaceMapComplex _).obj ((trivialCechDeRhamDoubleComplex U N hN).X a)).homology
        j))
    (j : ℕ) (hj : D + m < j) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
      ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) := by
  refine IsZero.of_iso ?_ (homologyIsoTrivialTotal hp hU L hI t ht N hN j)
  refine Functor.map_isZero _ ?_
  exact Crystalline.CosimplicialDoubleComplex.isZero_homology_total_of_bounded
    (trivialCechDeRhamDoubleComplex U N hN) D m hD hex (j : ℤ) (by omega)

omit [Finite ι] in
include hp hU L hN in
/-- **`H^j(RΓ(CRIS(X/S), N)) = 0` for `j < 0`**: it is the cohomology of the Čech complex
(`...CechEnvelope.cechEnvelopeHomologyIso`), which vanishes in negative degrees. -/
theorem isZero_homology_derivedBigModuleGlobalSections_of_neg (j : ℤ) (hj : j < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) j).obj
      ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) := by
  refine IsZero.of_iso ?_ (cechEnvelopeHomologyIso hp hU L N hN j).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ j).app
    ((Stacks.CechSite.FinalCover.cechIntFunctor (crystallineStructureSheaf S) (bigBaseRingHom S)
      (cechObjects hp L)).obj ((bigModuleULift S).obj N)))
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (Stacks.CechSite.FinalCover.isZero_cechIntFunctor_X _ _ _ _ j hj)

end Crystalline.GlobalCrystallineSituation.CechEnvelope
