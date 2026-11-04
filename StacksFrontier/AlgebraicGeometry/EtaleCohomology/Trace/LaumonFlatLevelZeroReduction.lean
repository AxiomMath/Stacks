module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyNoPunctualSectionsReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology

/-!
# Vanishing on the flat levels from vanishing on the bottom level

Let `F` be an ℓ-adic sheaf whose levels are flat (`0 → Fₙ → Fₙ₊₁ → F₀ → 0` is exact,
`Stacks.EtaleCohomology.LAdicSheaf.levelSES`). A cohomological functor of the levels which
vanishes on `F₀` in one degree vanishes on every `Fₙ` in that degree, by induction along these
short exact sequences: the middle term of an exact sequence with zero ends is zero. This file
records it for `Hᵠ(R f_! -)`
(`Stacks.EtaleCohomology.LAdicSheaf.isZero_lowerShriekHomology_padicTower`) and for `Hⁱ_c(X_k̄, -)`
(`Stacks.EtaleCohomology.LAdicSheaf.isZero_compactSupportSheafCohomology_padicTower`).

Applied to the flat model of the family sheaf of Laumon's degeneration argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), the vanishing input
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput` reduces to the bottom level, a sheaf
killed by `ℓ` (`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isZero_lowerShriekHomology_padicTower`.
* `Stacks.EtaleCohomology.LAdicSheaf.isZero_compactSupportSheafCohomology_padicTower`.
* `Stacks.EtaleCohomology.laumonFamilyFlatLevelVanishingInput_of_levelZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
open AlgebraicGeometry.SmallEtale CategoryTheory.Abelian

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Devissage

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] (F : LAdicSheaf B X ℓ)
  (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))

include hF in
/-- **`Hᵠ(R f_! Fₙ) = 0` for all `n` once `Hᵠ(R f_! F₀) = 0`**, for an ℓ-adic sheaf with flat
levels: `0 → Fₙ → Fₙ₊₁ → F₀ → 0` is exact. -/
theorem LAdicSheaf.isZero_lowerShriekHomology_padicTower {Y : Scheme.{u}} (f : X.1 ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (q : ℤ)
    (h0 : IsZero ((lowerShriekHomology ℤ_[ℓ] f j q).obj
      (towerObj (LAdicSheaf.padicTower B X ℓ F) 0)))
    (n : ℕ) :
    IsZero ((lowerShriekHomology ℤ_[ℓ] f j q).obj
      (towerObj (LAdicSheaf.padicTower B X ℓ F) n)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact (singleHomology_exact₂ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF n 0) q).isZero_X₂ (ih.eq_of_src _ _)
      (h0.eq_of_tgt _ _)

include hF in
/-- **`Hⁱ_c(X_k̄, Fₙ) = 0` for all `n` once `Hⁱ_c(X_k̄, F₀) = 0`**, for an ℓ-adic sheaf with flat
levels: `0 → Fₙ → Fₙ₊₁ → F₀ → 0` is exact. -/
theorem LAdicSheaf.isZero_compactSupportSheafCohomology_padicTower {k : Type u} [Field k]
    [Fintype k] (f : X.1 ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u)
    [Field kbar] [Algebra k kbar] (i : ℤ)
    (h0 : IsZero ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      (towerObj (LAdicSheaf.padicTower B X ℓ F) 0))) (n : ℕ) :
    IsZero ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      (towerObj (LAdicSheaf.padicTower B X ℓ F) n)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hS := LAdicSheaf.levelSES_shortExact B X ℓ F hF n 0
    have hex := exact_homology_compactSupportFrobeniusFunctor_map.{u, 0} ℤ_[ℓ] f j kbar
      (hS.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} ℤ_[ℓ] X.1)
        (ComplexShape.up ℤ) 0))
      (CochainComplex.plus_singleFunctor_obj _) (CochainComplex.plus_singleFunctor_obj _)
      (CochainComplex.plus_singleFunctor_obj _) i
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
    have hsub : ∀ x : (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
        (towerObj (LAdicSheaf.padicTower B X ℓ F) (n + 1)), x = 0 := fun x => by
      obtain ⟨y, hy⟩ := (hex x).1 (@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h0) _ _)
      rw [← hy, @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero ih) y 0]
      exact map_zero _
    rw [hsub a, hsub b]

end Devissage

/-- **The vanishing on the bottom flat level of Laumon's family sheaf**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput` at the level `n = 0` only, for the
bottom level `K'₀` of the flat model of the family sheaf, a sheaf killed by `ℓ`:
`R⁰pr₂! K'₀ = 0` and `H¹_c(𝔸²_k̄, K'₀) = 0`. -/
public def LaumonFamilyFlatLevelZeroVanishingInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL)))),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (laumonFamilyProjection k' B hS hL))
          jg 0).obj
        (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
          (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0)) ∧
      ∀ (kbar : Type u) [Field kbar] [Algebra k' kbar] [IsAlgClosure k' kbar]
        (jU : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫
          laumonLineStructure k' B hL))),
        IsZero ((compactSupportSheafCohomology ℤ_[ℓ]
          (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL) jU
            kbar 1).obj
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0))

/-- **The vanishing on the flat levels from the bottom level**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the levels of the flat model are flat, so
`R⁰pr₂!` and `H¹_c(𝔸²_k̄, -)` vanish on every `K'ₙ` once they vanish on `K'₀`. -/
public theorem laumonFamilyFlatLevelVanishingInput_of_levelZero
    (h : LaumonFamilyFlatLevelZeroVanishingInput.{u}) :
    LaumonFamilyFlatLevelVanishingInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg n
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  obtain ⟨h0, h1⟩ := h B ℓ k' hS hL b ψ' hψ' n₀ c hh z p₀ σ₁ hσ₁ jg
  let K := (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf
  have hK := LAdicSheaf.powExact_etaleLevel_flatModel B ℓ K
  refine ⟨?_, fun kbar _ _ _ jU => ?_⟩
  · exact LAdicSheaf.isZero_lowerShriekHomology_padicTower B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) ℓ
      (LAdicSheaf.flatModel B ℓ K) hK (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 0
      h0 n
  · exact LAdicSheaf.isZero_compactSupportSheafCohomology_padicTower B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) ℓ
      (LAdicSheaf.flatModel B ℓ K) hK
      (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL) jU
      kbar 1 (h1 kbar jU) n

end Stacks.EtaleCohomology

end
