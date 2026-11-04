module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCompactSupportRightExact

/-!
# The transitions of `n ↦ H²_c(X_k̄, Fₙ)` on a curve are onto

Let `X` be a scheme of dimension at most one over a finite field and `F = {Fₙ}` an ℓ-adic sheaf on
`X`. The transition `Fₙ₊₁ → Fₙ` is an epimorphism (it is the cokernel of `ℓⁿ⁺¹`,
`Stacks.EtaleCohomology.LAdicSheaf.etaleTransitionIsCokernel`), and `H²_c(X_k̄, -)` is right exact
on `X`, so the maps `H²_c(X_k̄, Fₙ₊₁) → H²_c(X_k̄, Fₙ)` of the inverse system whose limit is
`H²_c(X_k̄, F)` are onto. With `ℤ_ℓ`-coefficients this is read through the comparison of `H²_c`
with restriction of scalars, which is natural
(`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality`).

This is the surjectivity of the transitions used to compute `H²_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ)` of a lisse
sheaf on a curve from its finite levels ([Stacks, Tag 03VL]).

## Main results

* `compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality`: the comparison of `Hⁱ_c`
  with restriction of scalars is natural.
* `LAdicSheaf.surjective_geometricCompactlySupportedCohomologySystem_map_two`: the transitions
  `H²_c(X_k̄, Fₙ₊₁) → H²_c(X_k̄, Fₙ)` are onto.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Naturality

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The comparison of `Hⁱ_c` with restriction of scalars is natural** in the complex. -/
theorem compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality
    {K₁ K₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)} (t : K₁ ⟶ K₂) (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} ρ).map
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ') i).map
          ((compactSupportFrobeniusFunctor.{u, 0} Λ' f j kbar).map t)) ≫
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar K₂ i).hom =
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar K₁ i).hom ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.map t)) := by
  have hn := (Stacks.InverseSystem.restrictHomologyIsoOfHom.{u + 1} ρ i).inv.naturality
    (DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} Λ' f j kbar).map t))
  have hc := compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_naturality (ρ := ρ) (f := f)
    (j := j) (kbar := kbar) t
  have hH := (Functor.map_comp _ _ _).symm.trans ((congrArg
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map hc).trans
      (Functor.map_comp _ _ _))
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn)).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ hH))

end Naturality

section Transition

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar]

/-- **The transitions of `n ↦ H²_c(X_k̄, Fₙ)` are onto** on a scheme of dimension at most one: the
transition `Fₙ₊₁ → Fₙ` is an epimorphism and `H²_c(X_k̄, -)` is right exact there. -/
theorem LAdicSheaf.surjective_geometricCompactlySupportedCohomologySystem_map_two
    (F : LAdicSheaf B X ℓ) (hdim : topologicalKrullDim X.1 ≤ 1) (n : ℕ) :
    Function.Surjective ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F
      2).map (homOfLE (Nat.le_add_right n 1)).op).hom := by
  have : NeZero (ℓ ^ (n + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 2
  let C := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar
  let ρ' := PadicInt.toZModPow (p := ℓ) (n + 1 + 1)
  have hsq := LAdicSheaf.padicCoefficientComplex_map_padicTransition B X ℓ F n
  have hmap : (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F 2).map
      (homOfLE (Nat.le_add_right n 1)).op =
      H.map (C.map (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F (n + 1)).hom) ≫
        H.map (C.map ((etaleModuleRestrictScalars ρ' X.1).mapCochainComplexPlus.map
          (LAdicSheaf.levelComplexTransition B X ℓ F n))) ≫
        H.map (C.map ((etaleModuleRestrictScalarsCompPlus ρ' (levelCast ℓ n)
          (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) X.1
          (LAdicSheaf.levelComplex B X ℓ F n)).hom ≫
            (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).inv)) := by
    rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
    have h : (padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n) =
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F (n + 1)).hom ≫
          (etaleModuleRestrictScalars ρ' X.1).mapCochainComplexPlus.map
            (LAdicSheaf.levelComplexTransition B X ℓ F n) ≫
          (etaleModuleRestrictScalarsCompPlus ρ' (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
            (toZModPow_succ_comp ℓ n) X.1 (LAdicSheaf.levelComplex B X ℓ F n)).hom ≫
            (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).inv := by
      rw [(Iso.eq_comp_inv _).2 hsq]
      simp only [Category.assoc]
      rfl
    show H.map (C.map ((padicCoefficientComplex B X ℓ).map
      (LAdicSheaf.padicTransition B X ℓ F n))) = _
    rw [h]
    simp only [Functor.map_comp, Category.assoc]
  rw [hmap]
  -- the middle factor, through the comparison with restriction of scalars
  have hnat := compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality ρ' f j kbar
    (LAdicSheaf.levelComplexTransition B X ℓ F n) 2
  have hmid : Function.Surjective
      (H.map (C.map ((etaleModuleRestrictScalars ρ' X.1).mapCochainComplexPlus.map
        (LAdicSheaf.levelComplexTransition B X ℓ F n)))).hom := by
    have hT : Function.Surjective ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) 2).map
          ((compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
            (LAdicSheaf.levelComplexTransition B X ℓ F n))).hom := by
      have : Epi (LAdicSheaf.etaleTransition B X ℓ F n) :=
        epi_of_isColimit_cofork (LAdicSheaf.etaleTransitionIsCokernel B X ℓ F n)
      have h0 := surjective_compactSupportSheafCohomology_two_map_of_epi f j kbar (ℓ ^ (n + 1 + 1))
        hdim (LAdicSheaf.etaleTransition B X ℓ F n)
      let iso2 : (sheafSingleComplex (ZMod (ℓ ^ (n + 1 + 1)))).obj
          ((etaleModuleRestrictScalars (levelCast ℓ n) X.1).obj (LAdicSheaf.etaleLevel B X ℓ F n)) ≅
          (etaleModuleRestrictScalars (levelCast ℓ n) X.1).mapCochainComplexPlus.obj
            (LAdicSheaf.levelComplex B X ℓ F n) :=
        ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
          (etaleModuleRestrictScalars (levelCast ℓ n) X.1) (ComplexShape.up ℤ) 0).app
            (LAdicSheaf.etaleLevel B X ℓ F n)).symm
      have hsplit : (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
            (LAdicSheaf.levelComplexTransition B X ℓ F n) =
          (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
              ((sheafSingleComplex (ZMod (ℓ ^ (n + 1 + 1)))).map
                (LAdicSheaf.etaleTransition B X ℓ F n)) ≫
            (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
              iso2.hom := by
        rw [← Functor.map_comp]
        rfl
      rw [hsplit, Functor.map_comp]
      exact (ConcreteCategory.bijective_of_isIso
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) 2).map
          ((compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
            iso2.hom))).2.comp h0
    have hres : Function.Surjective ((ModuleCat.restrictScalars.{u + 1} ρ').map
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) 2).map
          ((compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar).map
            (LAdicSheaf.levelComplexTransition B X ℓ F n)))).hom := hT
    have hcomp := congrArg (fun g => g.hom) hnat
    intro y
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ' f j kbar
        ((etaleModuleRestrictScalars (levelCast ℓ n) X.1).mapCochainComplexPlus.obj
          (LAdicSheaf.levelComplex B X ℓ F n)) 2).hom).2 y
    obtain ⟨w, rfl⟩ := hres z
    refine ⟨(compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ' f j kbar
      (LAdicSheaf.levelComplex B X ℓ F (n + 1)) 2).hom.hom w, ?_⟩
    rw [← hz]
    exact (LinearMap.congr_fun hcomp w).symm
  exact ((ConcreteCategory.bijective_of_isIso (H.map (C.map
    ((etaleModuleRestrictScalarsCompPlus ρ' (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
      (toZModPow_succ_comp ℓ n) X.1 (LAdicSheaf.levelComplex B X ℓ F n)).hom ≫
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).inv)))).2.comp hmid).comp
    (ConcreteCategory.bijective_of_isIso (H.map (C.map
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F (n + 1)).hom))).2

end Transition

end Stacks.EtaleCohomology

end
