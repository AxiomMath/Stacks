module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeArrow07QCIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeNilpotentSmooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelMilnor

/-!
# The inputs of the levels assembly from base change for `p` nilpotent

Let `X/S` be a global crystalline situation with affine base, `X ⟶ S₀` proper and smooth, and `E` a
crystal in finite locally free modules. The levels assembly
(`SmallSite.levels_isPseudoCoherentIn_and_isIso_levelProj`) asks for the base change isomorphisms
along the level transitions `S_{N₀(n+1)} ⟶ S_{N₀(n+2)}` and for the pseudo-coherence of
`RΓ(CRIS(X/S_{N₀}), E_{N₀})`. The first come from the base change theorem for `p` nilpotent and `X`
smooth (`SmallSite.isIso_baseChange_of_isNilpotent_smooth`): the closed-fibre squares of the level
transitions are pullbacks with the identity of `X` on top, `p` is nilpotent on every level, and the
restrictions of `E` are again crystals in finite locally free modules. The pseudo-coherence of the
first term is `SmallSite.isPseudoCoherentIn_levelCohomology`.

## Main results

* `SmallSite.isIso_levelTransition_transpose` — the base change isomorphisms of the tower.
* `SmallSite.levels_isPseudoCoherentIn_and_isIso_of_triangle` — the levels assembly with these
  inputs discharged, given the Milnor triangle.
* `SmallSite.exists_distTriang_levelT` — the Milnor triangle of `BigLevelMilnor` in the form of the
  assembly.
* `SmallSite.levels_isPseudoCoherentIn_and_isIso` — **(P1) and (P2)**: `RΓ(CRIS(X/S), E)` is
  pseudo-coherent and `RΓ(CRIS(X/S), E) ⊗^L_A Γ(S_{N₀}, ⊤) ≅ RΓ(CRIS(X/S_{N₀}), E_{N₀})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open DerivedCategory

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance 1100] HasDerivedCategory.standard

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {N₀ : ℕ} (h₀ : S.IsLevel N₀)

/-- **The base change isomorphisms of the tower of levels**, from base change for `p` nilpotent
(`SmallSite.isIso_baseChange_of_isNilpotent_smooth`):
for `X ⟶ S₀` proper and smooth and `E` a crystal in finite locally free modules, the transpose
`RΓ(CRIS(X/S_{N₀(n+2)}), E) ⊗^L Γ(S_{N₀(n+1)}) ⟶ RΓ(CRIS(X/S_{N₀(n+1)}), E)` of the comparison
along the level transition is an isomorphism. -/
theorem isIso_levelTransition_transpose
    (hproper : IsProper S.toClosedFiber) [Smooth S.toClosedFiber]
    {E : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hE : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal E) (n : ℕ) :
    IsIso (((derivedBaseChangeTensorAdjunction (S.levelTransition (h₀.mul n)
      (h₀.mul (n + 1)) (tower_le n.le_succ))).homEquiv
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul (n + 1)))).obj
          ((S.levelPullback (h₀.mul (n + 1))).obj ((bigModuleULift S).obj E))))
        (Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation (h₀.mul n))).obj
          ((S.levelStepPullback (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)).obj
            ((S.levelPullback (h₀.mul (n + 1))).obj ((bigModuleULift S).obj E)))))).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
          (S.levelTransition_condition _ _ _)
          ((S.levelPullback (h₀.mul (n + 1))).obj ((bigModuleULift S).obj E))))) := by
  have hsc := isSeparated_and_compactSpace_of_isProper S hproper
  have : (S.levelSituation (h₀.mul (n + 1))).X.IsSeparated := hsc.1
  have : CompactSpace (S.levelSituation (h₀.mul (n + 1))).X := hsc.2
  exact isIso_baseChange_of_isNilpotent_smooth (S := S.levelSituation (h₀.mul n))
    (S' := S.levelSituation (h₀.mul (n + 1)))
    (S.levelTransition (h₀.mul n) (h₀.mul (n + 1)) (tower_le n.le_succ)) (𝟙 S.X)
    (S.levelTransition_condition _ _ _) (isPullback_levelTransition S _ _ _)
    (isNilpotent_prime_level S _) (isNilpotent_prime_level S _) inferInstance
    ((changeBaseModulePullback (S.levelSituation (h₀.mul (n + 1))) S (S.levelProj _) (𝟙 S.X)
      (S.levelProj_condition _)).obj E) hE.changeBaseModulePullback

/-- **The levels `N₀(n+1)`, `n : ℕ`, as a sequence of levels** for `N₀ > 0`: they increase and
are unbounded. -/
def levelSequenceMul (hN₀ : 0 < N₀) : S.LevelSequence where
  seq n := N₀ * (n + 1)
  isLevel n := h₀.mul n
  monotone _ _ h := tower_le h
  unbounded k := ⟨k, by nlinarith⟩

/-- The transition `levelT` of the levels assembly is the transition of the Milnor triangle of
`BigLevelMilnor`, read in `D(Mod_A)`. -/
theorem ι_map_levelDerivedTransition (hN₀ : 0 < N₀) (N : BigModuleSheaf S) (n : ℕ) :
    Plus.ι.map (S.levelDerivedTransition (levelSequenceMul S h₀ hN₀) n N) = levelT S h₀ N n := by
  refine (Plus.ι.map_comp _ _).trans (((congrArg (_ ≫ ·) (Plus.ι.map_comp _ _))).trans ?_)
  refine Eq.trans ?_ (levelT_eq S h₀ N n).symm
  refine congrArg (_ ≫ · ≫ _) ?_
  exact StacksDraft.DerivedInverseLimit.ι_map_app_eq_derivedRestrictScalarsComp_hom_app.{u, u + 1}
    _ _ _ _ _ (Functor.mapDerivedCategoryPlusCompTransOfComp_compat _) _

/-- **The Milnor triangle of `RΓ(CRIS(X/S), N)` over the levels `S_{N₀(n+1)}`**, in the form of the
levels assembly. -/
theorem exists_distTriang_levelT (hN₀ : 0 < N₀) (N : BigModuleSheaf S) :
    letI := hasProductsOfShape_nat_derivedCategory_moduleCat Γ(S.S.scheme, ⊤)
    ∃ δ, Pretriangulated.Triangle.mk (Pi.lift (levelC S h₀ N))
      (Pi.lift fun n : ℕ ↦ Pi.π (levelX S h₀ N) n - Pi.π (levelX S h₀ N) (n + 1) ≫
        levelT S h₀ N n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) := by
  have h := S.exists_distTriang_levelDerived (levelSequenceMul S h₀ hN₀) N
  simp only [ι_map_levelDerivedTransition S h₀ hN₀ N] at h
  exact h

/-- **The levels assembly from the Milnor triangle**, in the standard models: for `A`
Noetherian and `p`-adically complete, `X ⟶ S₀` proper and smooth, `E` a crystal in finite locally
free modules and a level `N₀ > 0`, given the Milnor triangle of `RΓ(CRIS(X/S), E)` over the levels
`S_{N₀(n+1)}`, the complex `RΓ(CRIS(X/S), E)` is
pseudo-coherent and `RΓ(CRIS(X/S), E) ⊗^L_A Γ(S_{N₀}, ⊤) ⟶ RΓ(CRIS(X/S_{N₀}), E_{N₀})` is an
isomorphism. -/
theorem levels_isPseudoCoherentIn_and_isIso_of_triangle [IsNoetherianRing Γ(S.S.scheme, ⊤)]
    [IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p) Γ(S.S.scheme, ⊤)]
    (hproper : IsProper S.toClosedFiber) [Smooth S.toClosedFiber]
    {E : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hE : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal E) (hN₀ : 0 < N₀)
    [HasProduct (levelX S h₀ ((bigModuleULift S).obj E))]
    (δ : ∏ᶜ levelX S h₀ ((bigModuleULift S).obj E) ⟶ (levelK S ((bigModuleULift S).obj E))⟦(1 : ℤ)⟧)
    (hTri : Pretriangulated.Triangle.mk (Pi.lift (levelC S h₀ ((bigModuleULift S).obj E)))
      (Pi.lift fun n : ℕ ↦ Pi.π (levelX S h₀ ((bigModuleULift S).obj E)) n -
        Pi.π (levelX S h₀ ((bigModuleULift S).obj E)) (n + 1) ≫
          levelT S h₀ ((bigModuleULift S).obj E) n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn (levelK S ((bigModuleULift S).obj E)) ∧
      IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj h₀)).homEquiv _ _).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj h₀) (𝟙 S.X)
          (S.levelProj_condition h₀) ((bigModuleULift S).obj E)))) := by
  have := hproper
  exact levels_isPseudoCoherentIn_and_isIso_levelProj S h₀ ((bigModuleULift S).obj E) hN₀
    (isIso_levelTransition_transpose S h₀ hproper hE)
    (isPseudoCoherentIn_levelCohomology (h₀.mul 0) E hE) δ hTri

/-- **`RΓ(CRIS(X/S), E)` is pseudo-coherent and computes the cohomology of the first level**, in
the standard models ((P1) and (P2) of arrow 1 of [Stacks, Tag 07N5]): for an affine base with
`A = Γ(S, 𝒪)` Noetherian and `p`-adically complete, `X ⟶ S₀` proper and smooth, `E` a crystal in
finite locally free modules and a finite divided power level `N₀ > 0`, the complex
`RΓ(CRIS(X/S), E)` is pseudo-coherent over `A` and the base change map
`RΓ(CRIS(X/S), E) ⊗^L_A Γ(S_{N₀}, ⊤) ⟶ RΓ(CRIS(X/S_{N₀}), E_{N₀})` is an isomorphism. -/
theorem levels_isPseudoCoherentIn_and_isIso [IsNoetherianRing Γ(S.S.scheme, ⊤)]
    [IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p) Γ(S.S.scheme, ⊤)]
    (hproper : IsProper S.toClosedFiber) [Smooth S.toClosedFiber]
    {E : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hE : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal E) (hN₀ : 0 < N₀) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn (levelK S ((bigModuleULift S).obj E)) ∧
      IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj h₀)).homEquiv _ _).symm
        (Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj h₀) (𝟙 S.X)
          (S.levelProj_condition h₀) ((bigModuleULift S).obj E)))) := by
  let := hasProductsOfShape_nat_derivedCategory_moduleCat Γ(S.S.scheme, ⊤)
  obtain ⟨δ, hδ⟩ := exists_distTriang_levelT S h₀ hN₀ ((bigModuleULift S).obj E)
  exact levels_isPseudoCoherentIn_and_isIso_of_triangle S h₀ hproper hE hN₀ δ hδ

end Crystalline.GlobalCrystallineSituation.SmallSite
