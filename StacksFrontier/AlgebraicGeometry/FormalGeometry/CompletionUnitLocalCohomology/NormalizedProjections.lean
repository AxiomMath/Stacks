module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.InductiveSteps
public import
  StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyNormalizedLimit

/-!
# The projections of Stacks 0EEW normalized against the completion unit

Every term of the tower `RΓ_J(M/IⁿM)` of Stacks 0EEW is already derived `I`-complete, so the maps
`RΓ_J(M) ⟶ RΓ_J(M/IⁿM)` induced by `M ↠ M/IⁿM` factor uniquely through the completion unit,
giving the normalized projections `RΓ_J(M)^∧ ⟶ RΓ_J(M/IⁿM)`.

## Main definitions

* `Stacks.Algebraization.localCohomologyAdicQuotientLeg`
* `Stacks.Algebraization.completedLocalCohomologyNormalizedProjection`

## Main results

* `Stacks.Algebraization.isDerivedComplete_adicQuotientLocalCohomologySystem_obj`
* `Stacks.Algebraization.map_completionUnit_comp_completedLocalCohomologyToLimit`

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### The projections of Stacks 0EEW normalized against the completion unit -/

section NormalizedProjections

variable {A : Type u} [CommRing A]

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

/-- A power of `I` annihilates `M/IⁿM`. -/
private theorem pow_le_annihilator_adicQuotient (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    (I ^ n : Ideal A) ≤ Module.annihilator A
      (ModuleCat.of A ((M : Type u) ⧸ (I ^ n • (⊤ : Submodule A (M : Type u))))) := by
  intro c hc
  refine Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule A (M : Type u))) x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hc Submodule.mem_top)

/-- Every term of the tower of Stacks 0EEW is already derived `I`-complete: it is the local
cohomology of a module annihilated by a power of `I`. -/
theorem isDerivedComplete_adicQuotientLocalCohomologySystem_obj (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    IsDerivedComplete I ((Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩) :=
  isDerivedComplete_localCohomology_of_pow_le_annihilator I J hJ n _
    (pow_le_annihilator_adicQuotient I M n)

/-- The unit of derived `I`-adic completion is invertible at every term of the tower of
Stacks 0EEW. -/
theorem isIso_completionUnit_adicQuotientLocalCohomologySystem_obj (I J : Ideal A) (hI : I.FG)
    (hJ : J.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    IsIso ((adicCompletionUnit A I hI).app
      ((Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)) :=
  isIso_completionUnit_of_derivedComplete I hI _
    (isDerivedComplete_adicQuotientLocalCohomologySystem_obj I J hJ M n)

/-- The map `RΓ_{V(J)}(M) ⟶ RΓ_{V(J)}(M/IⁿM)` induced by the quotient map `M ↠ M/IⁿM`: the
`n`-th leg of the canonical cone from `RΓ_{V(J)}(M)` to the tower of Stacks 0EEW. -/
def localCohomologyAdicQuotientLeg (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    ((Dualizing.localCohomologyFunctor A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ⟶
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩ :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      Stacks.LocalCohomology.localCohomologyDerived A J hJ).map
    (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)

/-- The canonical legs are compatible with the transition maps of the tower: the quotient maps
`M ↠ M/IⁿM` form a cone. -/
theorem localCohomologyAdicQuotientLeg_comp_map (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    localCohomologyAdicQuotientLeg I J hJ M (n + 1) ≫
        (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).map
          (homOfLE (Nat.le_succ n)).op =
      localCohomologyAdicQuotientLeg I J hJ M n := by
  have key : ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule A (M : Type u))).mkQ ≫
        (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).map
          (homOfLE (Nat.le_succ n)).op =
      ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ := by
    unfold AlgebraicGeometry.ProEtale.adicQuotientModuleSystem
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ rfl)
  rw [localCohomologyAdicQuotientLeg, localCohomologyAdicQuotientLeg]
  change (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        Stacks.LocalCohomology.localCohomologyDerived A J hJ).map _ ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        Stacks.LocalCohomology.localCohomologyDerived A J hJ).map
          ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).map
            (homOfLE (Nat.le_succ n)).op) = _
  exact ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      Stacks.LocalCohomology.localCohomologyDerived A J hJ).map_comp _ _).symm.trans
    (congrArg (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      Stacks.LocalCohomology.localCohomologyDerived A J hJ).map key)

/-- **The projections of Stacks 0EEW, normalized against the completion unit.** The unique maps
`RΓ_{V(J)}(M)^∧ ⟶ RΓ_{V(J)}(M/IⁿM)` whose composite with the completion unit is the map induced
by `M ↠ M/IⁿM`. They exist, and are unique, because every term of the tower is already derived
`I`-complete, so the unit is invertible there. -/
def completedLocalCohomologyNormalizedProjection (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ⟶
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩ :=
  letI := isIso_completionUnit_adicQuotientLocalCohomologySystem_obj I J hI hJ M n
  (adicCompletionFunctor A I hI).map (localCohomologyAdicQuotientLeg I J hJ M n) ≫
    inv ((adicCompletionUnit A I hI).app
      ((Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩))

/-- **The normalization.** The completion unit followed by the `n`-th normalized projection is
the map `RΓ_{V(J)}(M) ⟶ RΓ_{V(J)}(M/IⁿM)` induced by `M ↠ M/IⁿM`. -/
theorem completionUnit_comp_completedLocalCohomologyNormalizedProjection
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫
        completedLocalCohomologyNormalizedProjection I J hI hJ M n =
      localCohomologyAdicQuotientLeg I J hJ M n := by
  let := isIso_completionUnit_adicQuotientLocalCohomologySystem_obj I J hI hJ M n
  rw [completedLocalCohomologyNormalizedProjection, ← Category.assoc,
    ← (adicCompletionUnit A I hI).naturality (localCohomologyAdicQuotientLeg I J hJ M n),
    Category.assoc]
  simp

/-- Maps out of `RΓ_{V(J)}(M)^∧` into a term of the tower of Stacks 0EEW are determined by their
composites with the completion unit. -/
private theorem eq_of_completionUnit_comp_eq (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕ)
    {f g : (adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ⟶
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩}
    (h : (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫ f =
        (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫ g) :
    f = g :=
  (completionUnit_comp_bijective I hI
    ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj _
    (isDerivedComplete_adicQuotientLocalCohomologySystem_obj I J hJ M n)).1 h

/-- The normalized projections form a cone on the tower of Stacks 0EEW. -/
theorem completedLocalCohomologyNormalizedProjection_comp_map (I J : Ideal A) (hI : I.FG)
    (hJ : J.FG) (M : ModuleCat.{u} A) (n : ℕ) :
    completedLocalCohomologyNormalizedProjection I J hI hJ M (n + 1) ≫
        (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).map
          (homOfLE (Nat.le_succ n)).op =
      completedLocalCohomologyNormalizedProjection I J hI hJ M n := by
  refine eq_of_completionUnit_comp_eq I J hI hJ M n ?_
  rw [← Category.assoc, completionUnit_comp_completedLocalCohomologyNormalizedProjection,
    completionUnit_comp_completedLocalCohomologyNormalizedProjection,
    localCohomologyAdicQuotientLeg_comp_map]

/-- **The normalized projections are the only cone normalized against the unit.** Any family of
maps out of `RΓ_{V(J)}(M)^∧` whose composites with the completion unit are the maps induced by
`M ↠ M/IⁿM` is the family of normalized projections: the terms of the tower are already derived
`I`-complete, so precomposition with the unit is injective on maps into them. -/
theorem eq_completedLocalCohomologyNormalizedProjection (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A)
    (q : ∀ n : ℕ, (adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ⟶
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hq : ∀ n : ℕ, (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫ q n =
        localCohomologyAdicQuotientLeg I J hJ M n) (n : ℕ) :
    q n = completedLocalCohomologyNormalizedProjection I J hI hJ M n :=
  eq_of_completionUnit_comp_eq I J hI hJ M n
    ((hq n).trans
      (completionUnit_comp_completedLocalCohomologyNormalizedProjection I J hI hJ M n).symm)

/-- **Stacks 0EEW, part (1), with the projections normalized against the completion unit**,
reduced to the same assertion for an arbitrary unit-normalized cone.

This is the step that the derived-limit property alone cannot supply. Being a derived limit is a
property of the object, and the projections of a derived limit may be altered by any automorphism
of it, so the predicate does not say which cone it holds for; what pins the cone down is the
unit, and `Stacks.Algebraization.eq_completedLocalCohomologyNormalizedProjection` then identifies
any unit-normalized cone with the normalized projections. So it suffices to exhibit *one*
derived-limit cone whose composites with the unit are the maps induced by `M ↠ M/IⁿM`. -/
theorem isDerivedLimitWithProjections_completedLocalCohomologyNormalizedProjection
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A)
    (q : ∀ n : ℕ, (adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ⟶
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hq : ∀ n : ℕ, (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫ q n =
        localCohomologyAdicQuotientLeg I J hJ M n)
    (hlim : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M)
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) q) :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M)
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)
      (completedLocalCohomologyNormalizedProjection I J hI hJ M) := by
  have heq : q = completedLocalCohomologyNormalizedProjection I J hI hJ M :=
    funext fun n ↦ eq_completedLocalCohomologyNormalizedProjection I J hI hJ M q hq n
  exact heq ▸ hlim

/-- **Stacks 0EEW, part (1), for the projections normalized against the completion unit.** For a
finite module over a Noetherian ring, `RΓ_{V(J)}(M)^∧` is a derived limit of the tower
`n ↦ RΓ_{V(J)}(M/IⁿM)` *with the normalized projections* — the cone whose composites with the
completion unit are the maps induced by `M ↠ M/IⁿM`.

`Stacks.Algebraization.isDerivedLimitWithProjections_completedLocalCohomologyNormalizedProjection`
reduces this to exhibiting *one* unit-normalized derived-limit cone, and
`Dualizing.exists_isDerivedLimitWithProjections_of_uliftAdicQuotientIso` is one: Stacks 0922
supplies a reflection onto the derived `I`-complete objects whose unit induces the reduction maps
of the tower `n ↦ K ⊗ᴸ A/Iⁿ`, the comparison with the tower of ordinary quotients is normalized,
and two reflections onto the same subcategory agree compatibly with their units, so the cone
transports to the reflection `adicCompletionFunctor`. -/
@[stacks 0EEW "part (1) for the projections normalized against the completion unit"]
theorem isDerivedLimitWithProjections_completedLocalCohomologyNormalizedProjection_of_finite
    [IsNoetherianRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M)
      ((adicCompletionFunctor A I hI).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)
      (completedLocalCohomologyNormalizedProjection I J hI hJ M) := by
  obtain ⟨Gfun, η, hGcomplete, hGbij, q, hqlim, hqnorm⟩ :=
    Dualizing.exists_isDerivedLimitWithProjections_of_uliftAdicQuotientIso A I J hJ M
      (Dualizing.fg_comap_uliftRingEquiv A hI)
      (Dualizing.uliftAdicQuotientModuleSystemIso A I M)
      (Dualizing.map_mkQ_comp_uliftAdicQuotientModuleSystemIso A I M)
  obtain ⟨ee, hee⟩ := exists_iso_of_reflections (Dualizing.derivedCompleteProperty A I)
    Gfun (adicCompletionFunctor A I hI) η (adicCompletionUnit A I hI) hGcomplete
    (fun Y ↦ ((Dualizing.derivedCompletion A I hI).obj Y).property) hGbij
    (fun Y E hE ↦ completionUnit_comp_bijective I hI Y E hE)
    ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
  have hq' : ∀ n : ℕ, (adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj ≫
        (ee.inv ≫ q n) = localCohomologyAdicQuotientLeg I J hJ M n := by
    intro n
    rw [← hee, Category.assoc, ← Category.assoc ee.hom, ee.hom_inv_id, Category.id_comp]
    exact hqnorm n
  exact isDerivedLimitWithProjections_completedLocalCohomologyNormalizedProjection I J hI hJ M
    (fun n ↦ ee.inv ≫ q n) hq' (hqlim.ofIso ee)

/-- **Stacks 0EEW, part (2), normalized against the completion unit.** The comparison map of
part (2) attached to the normalized projections, precomposed with `Hʳ` of the completion unit,
is the canonical map `Hʳ_{V(J)}(M) ⟶ lim Hʳ_{V(J)}(M/IⁿM)` induced by the quotient maps
`M ↠ M/IⁿM`.

Nothing is assumed: the comparison map is the canonical map into the limit determined by a cone
of projections, and the normalized projections are one. Part (1) of the tag is what makes *this*
comparison map an isomorphism in the relevant degrees, and it is needed in the form that names
these projections, which is not what `Dualizing.isDerivedLimit_completedLocalCohomology`
provides. -/
theorem map_completionUnit_comp_completedLocalCohomologyToLimit (I J : Ideal A) (hI : I.FG)
    (hJ : J.FG) (M : ModuleCat.{u} A) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
          ((adicCompletionUnit A I hI).app
            ((Dualizing.localCohomologyFunctor A J hJ).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) ≫
        Dualizing.completedLocalCohomologyToLimitOfProjections A I J hJ M
          (completedLocalCohomologyNormalizedProjection I J hI hJ M)
          (completedLocalCohomologyNormalizedProjection_comp_map I J hI hJ M) r =
      limit.lift _ (Dualizing.adicQuotientLocalCohomologyCone A I J hJ M
        (localCohomologyAdicQuotientLeg I J hJ M)
        (localCohomologyAdicQuotientLeg_comp_map I J hJ M) r) :=
  Dualizing.map_comp_completedLocalCohomologyToLimit_eq_limitLift A I J hJ M _
    (completedLocalCohomologyNormalizedProjection_comp_map I J hI hJ M) r _ _
    (localCohomologyAdicQuotientLeg_comp_map I J hJ M)
    (completionUnit_comp_completedLocalCohomologyNormalizedProjection I J hI hJ M)

end NormalizedProjections

end Stacks.Algebraization

end
