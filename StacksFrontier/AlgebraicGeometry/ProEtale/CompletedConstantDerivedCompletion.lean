module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantSheafMaps
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedCompletion
import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductions
import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpimorphicDifferenceLimit

/-!
# The completed constant sheaf is the derived completion of the constant sheaf

Let `X` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. On `X_proét` the completed
constant sheaf `\underline{Λ}^∧ = lim \underline{Λ/Iⁿ}` is also the derived limit
`R lim \underline{Λ/Iⁿ}`, the transition maps being surjective and `X_proét` having enough weakly
contractible objects (Stacks 0947). Since `\underline{Λ/Iⁿ}` equals
`\underline{Λ} ⊗_Λ^L \underline{Λ/Iⁿ}`, the map `\underline{Λ} → \underline{Λ}^∧` is the derived
completion of `\underline{Λ}` (Stacks 099M). Hence, in the derived category of sheaves of
`Λ`-modules on `X_proét`:

* maps `\underline{Λ}^∧[-n] → K` into a derived complete `K` are the maps `\underline{Λ}[-n] → K`;
* `\underline{Λ}[-n] ⊗_Λ^L N → \underline{Λ}^∧[-n] ⊗_Λ^L N` is an isomorphism for every sheaf `N`
  killed by `I`.

## Main results

* `AlgebraicGeometry.ProEtale.isDerivedLimitWithProjections_singleFunctor_limit_of_epi`: the limit
  of a tower of sheaves of `Λ`-modules on `X_proét` with epimorphic transition maps is its derived
  limit.
* `isDerivedLimitWithProjections_derivedReductionTower_completedConstantSheaf`:
  `\underline{Λ}^∧ = R lim (\underline{Λ} ⊗_Λ^L \underline{Λ/Iⁿ})`.
* `AlgebraicGeometry.ProEtale.bijective_comp_singleFunctor_map_completedConstantSheafMap`: maps
  from `\underline{Λ}^∧[-n]` into a derived complete object.
* `AlgebraicGeometry.ProEtale.isIso_whiskerRight_singleFunctor_map_completedConstantSheafMap`:
  `\underline{Λ}[-n] → \underline{Λ}^∧[-n]` is an isomorphism after tensoring with a sheaf killed
  by `I`; `isIso_whiskerRight_singleFunctor_map_biproductMap_completedConstantSheafMap` is the
  same for finite direct sums.

## Implementation notes

The identification with the derived completion of `\underline{Λ}` uses the general results
`Stacks.ModuleSheaf.bijective_comp_of_isDerivedLimitWithProjections_derivedReductionTower` and
`Stacks.ModuleSheaf.isIso_whiskerRight_of_isDerivedLimitWithProjections_derivedReductionTower`
of an arbitrary site. Several applications of them pass their arguments explicitly and match the
hypotheses by `convert`: elaborating them against the conclusion makes the unifier unfold the
towers, which does not terminate in reasonable time.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory NoetherianAdicCompletion

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.ModuleSheaf.derivedMonoidal

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ]
  {I : Ideal Λ}

/-- **The limit of a tower of sheaves of `Λ`-modules on `X_proét` with epimorphic transition maps
is its derived limit**, the projections being the limit projections placed in degree zero
(Stacks 0947 (3)). -/
theorem isDerivedLimitWithProjections_singleFunctor_limit_of_epi
    (G : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op)) :
    IsDerivedLimitWithProjections (G ⋙ DerivedCategory.singleFunctor _ 0)
      ((DerivedCategory.singleFunctor _ 0).obj (limit G))
      (fun n ↦ (DerivedCategory.singleFunctor _ 0).map (limit.π G ⟨n⟩)) := by
  have : HasProductsOfShape ℕ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf _ _)
  have : HasProductsOfShape ℕ
      (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ) :=
    HomologicalComplex.instHasLimitsOfShape
  let F := G ⋙ CochainComplex.singleFunctor _ 0
  have hc := isLimitMapConeSingle (limit.isLimit G)
  have : HasLimit F := ⟨⟨⟨_, hc⟩⟩⟩
  have : Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ F.obj ⟨n⟩)
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)) :=
    HomologicalComplex.epi_milnorDifference_of_epi_eval F fun i ↦
      epi_milnorDifference_sheafModuleCat X Λ (F ⋙ HomologicalComplex.eval
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) (ComplexShape.up ℤ) i)
        fun n ↦ by
        by_cases hi : i = 0
        · subst hi
          have := hG n
          show Epi (((HomologicalComplex.single _ _ 0).map
            (G.map (homOfLE (Nat.le_succ n)).op)).f 0)
          rw [HomologicalComplex.single_map_f_self]
          infer_instance
        · exact IsZero.epi (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
            (G.obj ⟨n⟩) i hi) _
  have h := (DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi_milnorDifference F).ofIso
    (DerivedCategory.Q.mapIso (hc.conePointUniqueUpToIso (limit.isLimit F))).symm
  rw [Iso.symm_inv] at h
  have heq : (fun n : ℕ ↦ (DerivedCategory.Q.mapIso
      (hc.conePointUniqueUpToIso (limit.isLimit F))).hom ≫ DerivedCategory.Q.map (limit.π F ⟨n⟩)) =
      fun n ↦ (DerivedCategory.singleFunctor _ 0).map (limit.π G ⟨n⟩) := by
    funext n
    rw [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (IsLimit.conePointUniqueUpToIso_hom_comp hc (limit.isLimit F) ⟨n⟩)
  rwa [heq] at h

/-- **The completed constant sheaf is the derived limit of the constant sheaves
`\underline{Λ/Iⁿ}`**: `\underline{Λ}^∧ = R lim \underline{Λ/Iⁿ}` in the derived category of sheaves
of `Λ`-modules on `X_proét`, the projections being the reductions. -/
theorem isDerivedLimitWithProjections_singleFunctor_completedConstantSheaf :
    IsDerivedLimitWithProjections
      (Stacks.ModuleSheaf.quotientPowerTower (Scheme.ProEt.topology X) Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        (completedConstantSheaf X Λ I (Functor.unitModule Λ)))
      (fun n ↦ (DerivedCategory.singleFunctor _ 0).map (limit.π
        (Stacks.ModuleSheaf.constantAdicQuotientTower (Scheme.ProEt.topology X) Λ I
          (Functor.unitModule Λ)) ⟨n⟩)) := by
  have h := isDerivedLimitWithProjections_singleFunctor_limit_of_epi
    (Stacks.ModuleSheaf.constantAdicQuotientTower (Scheme.ProEt.topology X) Λ I
      (Functor.unitModule Λ)) fun n ↦
    Stacks.ModuleSheaf.epi_constantAdicQuotientTower_map (Scheme.ProEt.topology X) Λ I _ _
  exact h

/-- **`\underline{Λ}^∧ = R lim (\underline{Λ} ⊗_Λ^L \underline{Λ/Iⁿ})`**: the completed constant
sheaf is the derived limit of the derived reductions of the constant sheaf `\underline{Λ}`. -/
theorem isDerivedLimitWithProjections_derivedReductionTower_completedConstantSheaf :
    IsDerivedLimitWithProjections
      (Stacks.ModuleSheaf.derivedReductionTower (Scheme.ProEt.topology X) Λ I
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
            (Functor.unitModule Λ))))
      ((DerivedCategory.singleFunctor _ 0).obj
        (completedConstantSheaf X Λ I (Functor.unitModule Λ)))
      (fun n ↦ (DerivedCategory.singleFunctor _ 0).map (limit.π
        (Stacks.ModuleSheaf.constantAdicQuotientTower (Scheme.ProEt.topology X) Λ I
          (Functor.unitModule Λ)) ⟨n⟩) ≫
        (Stacks.ModuleSheaf.derivedReductionTowerConstantSheafIso
          (Scheme.ProEt.topology X) Λ I).inv.app ⟨n⟩) := by
  let e := Stacks.ModuleSheaf.derivedReductionTowerConstantSheafIso (Scheme.ProEt.topology X) Λ I
  have he : HasEventualInverses e.inv :=
    @hasEventualInverses_of_isIso _ _ _ _ e.inv (Iso.isIso_inv e)
  -- The towers are given explicitly: inferring them from `e.inv` does not terminate in time.
  have h := IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    (F := Stacks.ModuleSheaf.quotientPowerTower (Scheme.ProEt.topology X) Λ I)
    (G := Stacks.ModuleSheaf.derivedReductionTower (Scheme.ProEt.topology X) Λ I
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
          (Functor.unitModule Λ)))) e.inv he
    isDerivedLimitWithProjections_singleFunctor_completedConstantSheaf
  convert h using 1

omit [IsNoetherianRing Λ] in
/-- The map `\underline{Λ} → \underline{Λ}^∧` placed in degree zero is compatible with the
reductions of `\underline{Λ}` and the projections of
`isDerivedLimitWithProjections_derivedReductionTower_completedConstantSheaf`. -/
theorem singleFunctor_map_completedConstantSheafMap_comp (n : ℕ) :
    (DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I) ≫
        (DerivedCategory.singleFunctor _ 0).map (limit.π
          (Stacks.ModuleSheaf.constantAdicQuotientTower (Scheme.ProEt.topology X) Λ I
            (Functor.unitModule Λ)) ⟨n⟩) ≫
          (Stacks.ModuleSheaf.derivedReductionTowerConstantSheafIso
            (Scheme.ProEt.topology X) Λ I).inv.app ⟨n⟩ =
      (Stacks.ModuleSheaf.derivedReductionMap (Scheme.ProEt.topology X) Λ I
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
            (Functor.unitModule Λ)))).app ⟨n⟩ := by
  have h : (DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I) ≫
      (DerivedCategory.singleFunctor _ 0).map (limit.π
        (Stacks.ModuleSheaf.constantAdicQuotientTower (Scheme.ProEt.topology X) Λ I
          (Functor.unitModule Λ)) ⟨n⟩) =
      (DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
          ((adicQuotientCone Λ I (ModuleCat.of Λ Λ)).app ⟨n⟩)) := by
    rw [← Functor.map_comp]
    exact congrArg _ (completedConstantSheafMap_π X I n)
  rw [reassoc_of% h]
  convert (Stacks.ModuleSheaf.derivedReductionMap_app_constantSheaf
    (Scheme.ProEt.topology X) Λ I ⟨n⟩).symm using 1

/-- **Maps from `\underline{Λ}^∧` into a derived complete object.** For every `K` in the derived
category of sheaves of `Λ`-modules on `X_proét` which is derived complete with respect to `I`,
precomposition with `\underline{Λ} → \underline{Λ}^∧` is a bijection
`Hom(\underline{Λ}^∧, K) → Hom(\underline{Λ}, K)`. -/
theorem bijective_comp_singleFunctor_zero_map_completedConstantSheafMap
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsDerivedComplete I K) :
    Function.Bijective (fun φ : (DerivedCategory.singleFunctor _ 0).obj
        (completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I) ≫ φ) := by
  -- The hypotheses are passed as proofs: unifying the conclusion with the statement does not
  -- terminate in time.
  have h := Stacks.ModuleSheaf.bijective_comp_of_isDerivedLimitWithProjections_derivedReductionTower
    (Scheme.ProEt.topology X) Λ I _ _ _
    isDerivedLimitWithProjections_derivedReductionTower_completedConstantSheaf _
    (fun n ↦ by convert singleFunctor_map_completedConstantSheafMap_comp n using 1) K hK
  exact h

/-- Precomposition with `f` is bijective on maps into `G E` if and only if precomposition with
`F f` is bijective on maps into `E`, for an adjunction `F ⊣ G`. -/
private theorem bijective_comp_map_of_adjunction {C : Type*} [Category C] {F G : C ⥤ C}
    (adj : F ⊣ G) {A B : C} (f : A ⟶ B) (E : C)
    (h : Function.Bijective (fun g : B ⟶ G.obj E ↦ f ≫ g)) :
    Function.Bijective (fun g : F.obj B ⟶ E ↦ F.map f ≫ g) := by
  have e : (fun g : F.obj B ⟶ E ↦ F.map f ≫ g) =
      (adj.homEquiv A E).symm ∘ (fun g : B ⟶ G.obj E ↦ f ≫ g) ∘ adj.homEquiv B E := by
    funext g
    apply (adj.homEquiv A E).injective
    simp [Adjunction.homEquiv_naturality_left]
  rw [e]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

/-- Precomposition with `f` and with an isomorphic arrow `f'` are bijective together. -/
private theorem bijective_comp_of_arrow_iso {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A' ≅ A) (b : B' ≅ B) (w : f' ≫ b.hom = a.hom ≫ f) (E : C)
    (h : Function.Bijective (fun g : B ⟶ E ↦ f ≫ g)) :
    Function.Bijective (fun g : B' ⟶ E ↦ f' ≫ g) := by
  have e : (fun g : B' ⟶ E ↦ f' ≫ g) =
      (fun g : A ⟶ E ↦ a.hom ≫ g) ∘ (fun g : B ⟶ E ↦ f ≫ g) ∘ (fun g : B' ⟶ E ↦ b.inv ≫ g) := by
    funext g
    simp [← reassoc_of% w]
  have ha : Function.Bijective (fun g : A ⟶ E ↦ a.hom ≫ g) :=
    ⟨fun _ _ h ↦ (cancel_epi a.hom).1 h, fun g ↦ ⟨a.inv ≫ g, by simp⟩⟩
  have hb : Function.Bijective (fun g : B' ⟶ E ↦ b.inv ≫ g) :=
    ⟨fun _ _ h ↦ (cancel_epi b.inv).1 h, fun g ↦ ⟨b.hom ≫ g, by simp⟩⟩
  rw [e]
  exact ha.comp (h.comp hb)

/-- The single functor in degree `n` is the single functor in degree zero followed by the shift
by `-n`. -/
private abbrev singleFunctorShiftIso (n : ℤ) :
    DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} Λ)) 0 ⋙ shiftFunctor _ (-n) ≅
      DerivedCategory.singleFunctor _ n :=
  (DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (neg_add_cancel n)

/-- **Maps from `\underline{Λ}^∧[-n]` into a derived complete object.** For every `K` in the
derived category of sheaves of `Λ`-modules on `X_proét` which is derived complete with respect to
`I`, precomposition with `\underline{Λ}[-n] → \underline{Λ}^∧[-n]` is a bijection
`Hom(\underline{Λ}^∧[-n], K) → Hom(\underline{Λ}[-n], K)`. -/
theorem bijective_comp_singleFunctor_map_completedConstantSheafMap (n : ℤ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsDerivedComplete I K) :
    Function.Bijective (fun φ : (DerivedCategory.singleFunctor _ n).obj
        (completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⟶ K ↦
      (DerivedCategory.singleFunctor _ n).map (completedConstantSheafMap X I) ≫ φ) := by
  let ε := singleFunctorShiftIso (X := X) (Λ := Λ) n
  have hK' : IsDerivedComplete I (K⟦n⟧) := fun a ha ↦
    isDerivedCompleteAt_map (shiftFunctor _ n) K a (hK a ha)
  have h₁ := bijective_comp_map_of_adjunction
    (shiftEquiv (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ))) n).symm.toAdjunction
    ((DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I)) K
    (bijective_comp_singleFunctor_zero_map_completedConstantSheafMap (K⟦n⟧) hK')
  exact bijective_comp_of_arrow_iso _ _ (ε.app _).symm (ε.app _).symm
    (ε.inv.naturality (completedConstantSheafMap X I)) K h₁

/-- **`\underline{Λ} → \underline{Λ}^∧` is an isomorphism after tensoring with a sheaf killed by
`I`.** For every sheaf `N` of `Λ`-modules on `X_proét` with `IN = 0`, the map
`\underline{Λ} ⊗_Λ^L N → \underline{Λ}^∧ ⊗_Λ^L N` is an isomorphism. -/
theorem isIso_whiskerRight_singleFunctor_zero_map_completedConstantSheafMap
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    IsIso ((DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I) ▷
      (DerivedCategory.singleFunctor _ 0).obj N) := by
  have hN' : ∀ x ∈ I, x • 𝟙 ((DerivedCategory.singleFunctor _ 0).obj N) = 0 := fun x hx ↦ by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hN x hx, Functor.map_zero]
  have h :=
    Stacks.ModuleSheaf.isIso_whiskerRight_of_isDerivedLimitWithProjections_derivedReductionTower
    (Scheme.ProEt.topology X) Λ I _ _ _
    isDerivedLimitWithProjections_derivedReductionTower_completedConstantSheaf _
    (fun n ↦ by convert singleFunctor_map_completedConstantSheafMap_comp n using 1) _ hN'
  exact h

/-- **`\underline{Λ}[-n] → \underline{Λ}^∧[-n]` is an isomorphism after tensoring with a sheaf
killed by `I`.** For every `n : ℤ` and every sheaf `N` of `Λ`-modules on `X_proét` with `IN = 0`,
the map `\underline{Λ}[-n] ⊗_Λ^L N → \underline{Λ}^∧[-n] ⊗_Λ^L N` is an isomorphism. -/
theorem isIso_whiskerRight_singleFunctor_map_completedConstantSheafMap (n : ℤ)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    IsIso ((DerivedCategory.singleFunctor _ n).map (completedConstantSheafMap X I) ▷
      (DerivedCategory.singleFunctor _ 0).obj N) := by
  let ε := singleFunctorShiftIso (X := X) (Λ := Λ) n
  let g := (DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I)
  let M := (DerivedCategory.singleFunctor _ 0).obj N
  obtain ⟨s, -⟩ := Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorRight
    (Scheme.ProEt.topology X) Λ M
  let := s
  have h₀ : IsIso (g ▷ M) :=
    isIso_whiskerRight_singleFunctor_zero_map_completedConstantSheafMap N hN
  have h₁ : IsIso (g⟦-n⟧' ▷ M) := by
    have : IsIso (g⟦-n⟧' ▷ M ≫ ((MonoidalCategory.tensorRight M).commShiftIso (-n)).hom.app _) := by
      show IsIso ((shiftFunctor _ (-n) ⋙ MonoidalCategory.tensorRight M).map g ≫ _)
      rw [((MonoidalCategory.tensorRight M).commShiftIso (-n)).hom.naturality g]
      show IsIso (_ ≫ (g ▷ M)⟦-n⟧')
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (((MonoidalCategory.tensorRight M).commShiftIso (-n)).hom.app _)
  have h := ε.hom.naturality (completedConstantSheafMap X I)
  rw [Functor.comp_map] at h
  have he : (DerivedCategory.singleFunctor _ n).map (completedConstantSheafMap X I) =
      ε.inv.app _ ≫ g⟦-n⟧' ≫ ε.hom.app _ := by
    rw [h, Iso.inv_hom_id_app_assoc]
  rw [he, MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight]
  infer_instance

section Biproduct

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- **`(\underline{Λ}^{⊕t})[-n] → (\underline{Λ}^∧)^{⊕t}[-n]` is an isomorphism after tensoring
with a sheaf killed by `I`.** For every `n : ℤ`, `t : ℕ` and every sheaf `N` of `Λ`-modules on
`X_proét` with `IN = 0`, the direct sum of `t` copies of `\underline{Λ} → \underline{Λ}^∧`, placed
in degree `n` and tensored with `N`, is an isomorphism. -/
theorem isIso_whiskerRight_singleFunctor_map_biproductMap_completedConstantSheafMap (n : ℤ)
    (t : ℕ) (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    IsIso ((DerivedCategory.singleFunctor _ n).map
        (biproduct.map fun _ : Fin t ↦ completedConstantSheafMap X I) ▷
      (DerivedCategory.singleFunctor _ 0).obj N) := by
  let M := (DerivedCategory.singleFunctor _ 0).obj N
  obtain ⟨s, hs⟩ := Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorRight
    (Scheme.ProEt.topology X) Λ M
  let := s
  let F := DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{max (u + 1) w} Λ)) n ⋙ MonoidalCategory.tensorRight M
  let g : ∀ _ : Fin t, _ ⟶ _ := fun _ ↦ completedConstantSheafMap X I
  have hg : ∀ j, IsIso (F.map (g j)) := fun _ ↦
    isIso_whiskerRight_singleFunctor_map_completedConstantSheafMap n N hN
  have hw : F.map (biproduct.map g) ≫ (F.mapBiproduct _).hom =
      (F.mapBiproduct _ ≪≫ biproduct.mapIso fun j ↦ @asIso _ _ _ _ (F.map (g j)) (hg j)).hom := by
    ext j
    simp only [Category.assoc, Functor.mapBiproduct_hom, Iso.trans_hom, biproduct.mapIso_hom,
      asIso_hom, biproduct.map_π, Function.comp_def, biproduct.lift_π, biproduct.lift_π_assoc,
      ← Functor.map_comp]
  have : IsIso (F.map (biproduct.map g) ≫ (F.mapBiproduct _).hom) := by
    rw [hw]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (biproduct.map g)) (F.mapBiproduct _).hom

end Biproduct

end AlgebraicGeometry.ProEtale

end
