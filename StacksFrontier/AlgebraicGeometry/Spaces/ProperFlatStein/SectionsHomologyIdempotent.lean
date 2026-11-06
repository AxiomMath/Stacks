module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.SectionsHomologyUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType

/-!
# Degree-zero cohomology of `Rq_* 𝒪` of dimension at most one forces connectedness

Let `T` be an object of the big fppf site whose scheme is affine with Noetherian ring of
functions `K = Γ(T, 𝒪)`, a field, and let `q : Q ⟶ h_T` be a proper morphism of algebraic spaces.
If `H⁰(RΓ(T, Rq_* 𝒪_Q))` has dimension at most one over `K`, then every idempotent global function
of `Q` is `0` or `1`. Hence if `Q` is disconnected, then this dimension is at least two.

## Main results

* `ProperFlatStein.moduleFinite_representedAffineSections_modulePushforward`:
  `Γ(T, q_* 𝒪_Q)` is a finite `K`-module.
* `ProperFlatStein.isIdempotentElem_eq_zero_or_one_of_finrank_le_one`:
  every idempotent global function of `Q` is `0` or `1`.

## Implementation notes

The argument does not compute `Γ(T, q_* 𝒪_Q)`.  An idempotent `e` gives the idempotent
endomorphism `q_*(e ·)` of the quasi-coherent module `q_* 𝒪_Q`; the sections functor is faithful
on quasi-coherent modules and lands in a vector space of dimension at most one, where the only
idempotent endomorphisms are `0` and `1`.  The adjunction `q^* ⊣ q_*` then carries
`q_*(e ·) ∈ {0, 1}` to `e · ∈ {0, 1}`, read against the adjoint of `q^* 𝒪_T ≅ 𝒪_Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.ProperFlatStein

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

/-- A linear idempotent endomorphism of a finite module of rank at most one over a field is
`0` or `1`. -/
theorem linearMap_eq_zero_or_one_of_isIdempotentElem {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Module.Finite K M] (h : Module.finrank K M ≤ 1) (E : M →ₗ[K] M)
    (hE : E ∘ₗ E = E) : E = 0 ∨ E = LinearMap.id := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left
    have := Module.finrank_zero_iff.mp h0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · obtain ⟨v, hv, hspan⟩ := (finrank_eq_one_iff'.mp h1)
    obtain ⟨c, hc⟩ := hspan (E v)
    have hEv : ∀ x, ∃ a : K, x = a • v := fun x => by
      obtain ⟨a, ha⟩ := hspan x
      exact ⟨a, ha.symm⟩
    have hcc : c * c = c := by
      have h2 : E (E v) = E v := by
        simpa using congrArg (fun F : M →ₗ[K] M => F v) hE
      rw [← hc, LinearMap.map_smul, ← hc, smul_smul] at h2
      exact smul_left_injective K hv h2
    rcases (IsIdempotentElem.iff_eq_zero_or_one).mp hcc with rfl | rfl
    · left
      refine LinearMap.ext fun x => ?_
      obtain ⟨a, rfl⟩ := hEv x
      rw [LinearMap.map_smul, ← hc, zero_smul, smul_zero, LinearMap.zero_apply]
    · right
      refine LinearMap.ext fun x => ?_
      obtain ⟨a, rfl⟩ := hEv x
      rw [LinearMap.map_smul, ← hc, one_smul, LinearMap.id_apply]

section Finite

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
  {Q : AlgebraicSpaces B S hS} (q : Q ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)

/-- **`q_* 𝒪_Q` is coherent** for `q` proper over a Noetherian affine `T` (Stacks 08GK in degree
zero, for the structure sheaf). -/
theorem isCoherent_modulePushforward_structureModule (hq : IsProper B S hS q.hom) :
    IsCoherent B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      ((modulePushforward B S hS q).obj (structureModule Q)) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Q.1 Q.2)
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
  have : (modulePushforward B S hS q).IsRightAdjoint := ⟨_, ⟨modulePullbackAdjunction B S hS q⟩⟩
  have := Functor.additive_of_preserves_binary_products (modulePushforward B S hS q)
  have hZ := B.contains_terminal
  have hQN := isNoetherian_of_isProper_of_isAffine B S hS q hZ hq
  have : Fact (HasEtaleLocalProperty B S hS Q.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hQN.2.2⟩
  have hTN := isNoetherian_yoneda_of_isAffine B S hS (T := T) hZ
  have hlft : IsLocallyOfFiniteType B S hS q.hom := hq.2.1.1
  have hcoh : IsCoherent B S hS Q.1 Q.2 (structureModule Q) := isCoherent_structureSheaf B S hS _ _
  have : SheafOfModules.IsCoherentOnSite (structureModule Q) := hcoh.toIsCoherentOnSite
  have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS Q (structureModule Q)
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS (X := Q.1) Q.2
    (structureModule Q)
  have hsupp : HasProperSupport B S hS Q.2 (isAlgebraicSpace_yoneda B S hS T) q.hom hlft
      ((SheafOfModules.toSheaf _).obj (structureModule Q)) :=
    ⟨hcl, isProper_comp B S hS
      (isAlgebraicSpace_reducedClosedSubspace B S hS Q.1 Q.2 _ hcl) Q.2
      (isAlgebraicSpace_yoneda B S hS T) _ q.hom
      (isProper_ι_reducedClosedSubspace B S hS Q.1 Q.2 _ hcl) hq⟩
  have hb := derivedCategoryBBounded_derivedModulePushforward_single B S hS q hlft hTN.2.2 hTN.1
    (structureModule Q) hcoh hsupp
  have h0 : IsCoherent B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      ((DerivedCategory.homologyFunctor _ 0).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS q)).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Q.1 Q.2) 0).obj
            (structureModule Q)))) := hb.2 0
  refine isCoherent_of_iso B S hS (isAlgebraicSpace_yoneda B S hS T) ?_ h0
  exact (DerivedCategory.homologyFunctor _ 0).mapIso
      ((derivedModulePushforwardIsoTotalRightDerived B S hS q).app _).symm ≪≫
    (derivedModulePushforwardSingleHomologyZeroIso B S hS q).app (structureModule Q)

/-- **`Γ(T, q_* 𝒪_Q)` is a finite module over `Γ(T, 𝒪)`** for `q` proper over a Noetherian
affine `T`. -/
theorem moduleFinite_representedAffineSections_modulePushforward (hq : IsProper B S hS q.hom) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      ((representedAffineSections B S hS T).obj
        ((modulePushforward B S hS q).obj (structureModule Q))) := by
  have hc := isCoherent_modulePushforward_structureModule B S hS q hq
  exact moduleFinite_representedAffineSections B S hS T _ hc.toIsQuasicoherentOnSite
    (representedAffineFinalChart B S hS T)
    (isTerminalChartOfIso (B := B) (S := S) (hS := hS) T (Iso.refl _))
    (isAffineChart_representedAffineFinalChart B S hS T)
    (moduleFinite_sections_of_isCoherent B S hS _ _ _ hc
      (isAffineChart_representedAffineFinalChart B S hS T))

end Finite

section Idempotent

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
  {Q : AlgebraicSpaces B S hS} (q : Q ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)

/-- If multiplication by `e` on `𝒪_Q` is `m`, then `m` sends the section `1` over `U` to `e`. -/
private theorem globalFunctionsAt_mul_one_eq_of_globalFunctionsSmul_eq
    (e : globalFunctions' B S hS Q.1) (m : structureModule Q ⟶ structureModule Q)
    (h : globalFunctionsSmul B S hS e (structureModule Q) = m) (U) :
    globalFunctionsAt B S hS e U * 1 = m.val.app U
      (show ((structureModule Q).val.obj U : Type u) from
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Q.1 Q.2).O).obj.obj U)) := by
  subst h
  rfl

/-- Multiplication by a global function `e` on `𝒪_Q` is zero only for `e = 0`. -/
theorem eq_zero_of_globalFunctionsSmul_eq_zero (e : globalFunctions' B S hS Q.1)
    (h : globalFunctionsSmul B S hS e (structureModule Q) = 0) : e = 0 := by
  refine Subtype.ext (funext fun U => ?_)
  have h1 := globalFunctionsAt_mul_one_eq_of_globalFunctionsSmul_eq B S hS e _ h U
  rw [mul_one] at h1
  exact h1

/-- Multiplication by a global function `e` on `𝒪_Q` is the identity only for `e = 1`. -/
theorem eq_one_of_globalFunctionsSmul_eq_id (e : globalFunctions' B S hS Q.1)
    (h : globalFunctionsSmul B S hS e (structureModule Q) = 𝟙 _) : e = 1 := by
  refine Subtype.ext (funext fun U => ?_)
  have h1 := globalFunctionsAt_mul_one_eq_of_globalFunctionsSmul_eq B S hS e _ h U
  rw [mul_one] at h1
  exact h1

/-- The sections functor of an affine represented space is faithful on quasi-coherent modules: on
them it is, up to isomorphism, the inverse of the equivalence
`AlgebraicGeometry.Space.representedAffineAssoc`. -/
theorem faithful_representedAffineSections (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (E₁ E₂ : N ⟶ N)
    (h : (representedAffineSections B S hS T).map E₁ =
      (representedAffineSections B S hS T).map E₂) :
    E₁ = E₂ := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).O))
  have : (ObjectProperty.ι P ⋙ representedAffineSections B S hS T).Faithful :=
    Functor.Faithful.of_iso (representedAffineAssocInverseIso B S hS T)
  let N' : P.FullSubcategory := ⟨N, hN⟩
  have h' : (ObjectProperty.ι P ⋙ representedAffineSections B S hS T).map
      (ObjectProperty.homMk E₁ : N' ⟶ N') =
        (ObjectProperty.ι P ⋙ representedAffineSections B S hS T).map
          (ObjectProperty.homMk E₂ : N' ⟶ N') := h
  exact congrArg (fun k => k.hom)
    ((ObjectProperty.ι P ⋙ representedAffineSections B S hS T).map_injective h')

/-- **An idempotent global function is `0` or `1` when `H⁰(RΓ(T, Rq_* 𝒪_Q))` has dimension at
most one**, for `q : Q ⟶ h_T` proper over an affine `T` whose ring of functions is a Noetherian
field. -/
theorem isIdempotentElem_eq_zero_or_one_of_finrank_le_one
    (hK : IsField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hq : IsProper B S hS q.hom)
    (F : Modules.{u, u} B S hS Q.1 Q.2) (eF : F ≅ structureModule Q)
    (hrank : Module.finrank Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      ((@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
        _ _ (HasDerivedCategory.standard _) 0).obj
      ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS q).obj
          ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj F)))) ≤ 1)
    (e : globalFunctions' B S hS Q.1) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have : (modulePushforward B S hS q).IsRightAdjoint := ⟨_, ⟨modulePullbackAdjunction B S hS q⟩⟩
  have := Functor.additive_of_preserves_binary_products (modulePushforward B S hS q)
  let : Field Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := hK.toField
  have hqc : IsQuasiCompact B S hS q.hom := hq.2.1.2
  have hqs : IsQuasiSeparated B S hS q.hom := isQuasiSeparated_of_isSeparated B S hS hq.1
  have hrankM : Module.finrank Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      ((representedAffineSections B S hS T).obj
        ((modulePushforward B S hS q).obj (structureModule Q))) ≤ 1 := by
    rw [← (homologyZeroIsoRepresentedSections B S hS T q hqc hqs F eF).toLinearEquiv.finrank_eq]
    exact hrank
  have hMfin := moduleFinite_representedAffineSections_modulePushforward B S hS q hq
  have hmm : globalFunctionsSmul B S hS e (structureModule Q) ≫
      globalFunctionsSmul B S hS e (structureModule Q) =
        globalFunctionsSmul B S hS e (structureModule Q) := by
    rw [← globalFunctionsSmul_mul, he.eq]
  have hEE : (modulePushforward B S hS q).map (globalFunctionsSmul B S hS e (structureModule Q)) ≫
      (modulePushforward B S hS q).map (globalFunctionsSmul B S hS e (structureModule Q)) =
        (modulePushforward B S hS q).map (globalFunctionsSmul B S hS e (structureModule Q)) := by
    rw [← Functor.map_comp, hmm]
  have hL := linearMap_eq_zero_or_one_of_isIdempotentElem hrankM
    ((representedAffineSections B S hS T).map
      ((modulePushforward B S hS q).map (globalFunctionsSmul B S hS e (structureModule Q)))).hom
    (by rw [← ModuleCat.hom_comp, ← Functor.map_comp, hEE])
  have hNq : ((modulePushforward B S hS q).obj (structureModule Q)).IsQuasicoherentOnSite :=
    (isCoherent_modulePushforward_structureModule B S hS q hq).toIsQuasicoherentOnSite
  have hfaith := faithful_representedAffineSections B S hS T _ hNq
  have key : ∀ c : structureModule Q ⟶ structureModule Q,
      (representedAffineSections B S hS T).map
        ((modulePushforward B S hS q).map (globalFunctionsSmul B S hS e (structureModule Q))) =
      (representedAffineSections B S hS T).map ((modulePushforward B S hS q).map c) →
        globalFunctionsSmul B S hS e (structureModule Q) = c := fun c h => by
    have h' := hfaith _ _ h
    refine (Iso.cancel_iso_hom_left (modulePullbackUnitIso B S hS q) _ _).1
      (((modulePullbackAdjunction B S hS q).homEquiv _ _).injective ?_)
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, h']
  rcases hL with h0 | h1
  · exact Or.inl (eq_zero_of_globalFunctionsSmul_eq_zero B S hS e (key 0 (by
      ext1
      rw [h0, Functor.map_zero, Functor.map_zero]
      rfl)))
  · exact Or.inr (eq_one_of_globalFunctionsSmul_eq_id B S hS e (key (𝟙 _) (by
      ext1
      rw [h1, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl)))

end Idempotent

end AlgebraicGeometry.Space.ProperFlatStein
