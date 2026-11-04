module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportOpenRestrictionBijective

/-!
# The trace of the map on `H²_c` induced by a map on `X̄_k̄`, for constant coefficients

Let `X` be a geometrically connected smooth curve over `k`, `k̄` an algebraic closure, and
`ψ : R →+* Λ` a morphism of finite rings of the same order `n`, invertible in `k̄`. For `ρ` over
`Λ` and `W` over `R` on which `π₁(X_k̄)` acts trivially, and a map
`θ : res_ψ((j_! ℱ_ρ)|_{X̄_k̄}) ⟶ (j_! ℱ_W)|_{X̄_k̄}`, the trace of the image of
`x ∈ H²_c(X_k̄, ℱ_ρ)` is the image of the trace of `x` under
`M ≅ Γ(X_k̄, ℱ_ρ|) ⟶ Γ(X_k̄, ℱ_W|) ≅ W`, the middle map being `Γ(X_k̄, -)` of the restriction of
`θ` to `X_k̄` (`Stacks.EtaleCohomology.compactSupportOpenRestriction`).

## Main results

* `Stacks.EtaleCohomology.geometricSmoothModelRestrictionTrace_comp_restrictScalarsMapOfBar` — the
  trace formula on the smooth model, as an equation of additive maps.
* `AlgebraicGeometry.compactSupportTrivialTrace_comp_restrictScalarsMapOfBar` — the same for
  `Ξ_ζ : H²_c(X_k̄, ℱ_ρ) ≅ M`, one primitive root `ζ` for both rings.
* `AlgebraicGeometry.compactSupportTrivialTwistEquiv_restrictScalarsMapOfBar` — the same for the
  choice-free `Ξ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace Stacks.EtaleCohomology

section TraceComp

/-- The additive map underlying a composite of linear equivalences is the composite. -/
theorem linearEquiv_trans_toAddMonoidHom {S M N P : Type*} [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module S M] [Module S N] [Module S P] (e₁ : M ≃ₗ[S] N)
    (e₂ : N ≃ₗ[S] P) :
    (e₁.trans e₂).toLinearMap.toAddMonoidHom =
      e₂.toLinearMap.toAddMonoidHom.comp e₁.toLinearMap.toAddMonoidHom :=
  rfl

/-- The additive map underlying a linear equivalence, applied. -/
theorem linearEquiv_toAddMonoidHom_apply {S M N : Type*} [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) (x : M) :
    e.toLinearMap.toAddMonoidHom x = e x :=
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- `Stacks.EtaleCohomology.geometricSmoothModelRestrictionTrace_restrictScalarsMapOfBar` as an
equation of additive maps. -/
theorem geometricSmoothModelRestrictionTrace_comp_restrictScalarsMapOfBar [Fintype R] [Fintype Λ]
    (hcard : Fintype.card R = Fintype.card Λ) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (hnR : IsUnit ((Fintype.card R : ℕ) : kbar)) (hζR : IsPrimitiveRoot ζ (Fintype.card R))
    (F : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} R X)
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (hG : IsIso ((constantSheafΓAdj (pullback f (specAlgebraMap k kbar)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).counit.app
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)))
    (hG' : IsIso ((constantSheafΓAdj (pullback f (specAlgebraMap k kbar)).smallEtaleTopology
      (ModuleCat.{u + 1} R)).counit.app
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} R (pullback f (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G))) :
    (curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q R hnR hζR
        (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
        ((etaleModuleInverseImage.{u, 0} R (geometricSmoothModelProj f j kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)
        (geometricSmoothModelInverseImageRestrictionIso f j kbar R G) hG'
          hE').toLinearMap.toAddMonoidHom.comp
      ((galoisCompactSupportSmoothModelInverseImageEquiv f j kbar R G
          ((2 : ℕ) : ℤ)).toLinearMap.toAddMonoidHom.comp
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ)) =
    (globalSectionsRestrictScalarsAddHom ψ (pullback f (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst f (specAlgebraMap k kbar))).obj G)
        (compactSupportOpenRestriction f j kbar ψ F G θ)).comp
      ((curveExtensionByZeroRestrictionTrace (geometricSmoothModel f j kbar).q Λ hn hζ
          (geometricSmoothModel f j kbar).j (geometricSmoothModel f j kbar).finite_compl
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)
          (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F) hG
            hE).toLinearMap.toAddMonoidHom.comp
        (galoisCompactSupportSmoothModelInverseImageEquiv f j kbar Λ F
          ((2 : ℕ) : ℤ)).toLinearMap.toAddMonoidHom) :=
  AddMonoidHom.ext fun x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply, linearEquiv_toAddMonoidHom_apply, linearEquiv_toAddMonoidHom_apply,
      linearEquiv_toAddMonoidHom_apply, linearEquiv_toAddMonoidHom_apply]
    exact geometricSmoothModelRestrictionTrace_restrictScalarsMapOfBar f j kbar ψ
      hcard hn hζ hnR hζR F G θ hG hE hG' hE' x

end TraceComp

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

section Trivial

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  {R Λ : Type} [Ring R] [Ring Λ] [Fintype R] [Fintype Λ] (ψ : R →+* Λ)
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  (hnR : IsUnit ((Fintype.card R : ℕ) : kbar))

/-- **`Ξ_ζ` of the map induced by `θ`, for constant coefficients**: for `ρ` over `Λ` and `W`
over `R` on which `π₁(X_k̄)` acts trivially, `Ξ_ζ` over `R` of the image of `x` is the image of
`Ξ_ζ(x)` under `M ≅ Γ(X_k̄, ℱ_ρ|) ⟶ Γ(X_k̄, ℱ_W|) ≅ W`, the middle map being `Γ(X_k̄, -)` of the
restriction of `θ` to `X_k̄` (`Stacks.EtaleCohomology.compactSupportOpenRestriction`). -/
theorem compactSupportTrivialTrace_comp_restrictScalarsMapOfBar
    (hcard : Fintype.card R = Fintype.card Λ)
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (W : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hW : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation R _ W)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) (hζR : IsPrimitiveRoot ζ (Fintype.card R))
    (θ : letI := connectedSpace_of_isCurve B X f
      (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) R).obj W))) :
    letI := connectedSpace_of_isCurve B X f
    (compactSupportTrivialTrace B X f kbar R y j hnR W hW hζR).toLinearMap.toAddMonoidHom.comp
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ _ _ θ) =
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar R y W
        hW).toLinearMap.toAddMonoidHom.comp
        ((globalSectionsRestrictScalarsAddHom ψ _ _ _
          (compactSupportOpenRestriction f j kbar ψ _ _ θ)).comp
          ((geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ
            hρ).symm.toLinearMap.toAddMonoidHom.comp
            (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ
              hζ).toLinearMap.toAddMonoidHom)) := by
  let := connectedSpace_of_isCurve B X f
  have hev : (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ
        hρ).symm.toLinearMap.toAddMonoidHom.comp
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).toLinearMap.toAddMonoidHom =
      AddMonoidHom.id _ := AddMonoidHom.ext fun z => LinearEquiv.symm_apply_apply _ z
  unfold compactSupportTrivialTrace geometricSmoothModelTrivialTrace
  rw [linearEquiv_trans_toAddMonoidHom, linearEquiv_trans_toAddMonoidHom,
    linearEquiv_trans_toAddMonoidHom, linearEquiv_trans_toAddMonoidHom]
  rw [AddMonoidHom.comp_assoc (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ _ _ θ),
    AddMonoidHom.comp_assoc _ _
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar R y W hW).toLinearMap.toAddMonoidHom,
    geometricSmoothModelRestrictionTrace_comp_restrictScalarsMapOfBar f j kbar ψ hcard hn hζ hnR
      hζR _ _ θ
      (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar Λ y ρ hρ)
      (finite_geometricGlobalSectionsPullback B X f kbar Λ y ρ hρ)
      (isIso_constantSheafΓAdj_counit_geometricRepresentationSheafPullback B X f kbar R y W hW)
      (finite_geometricGlobalSectionsPullback B X f kbar R y W hW),
    AddMonoidHom.comp_assoc _ _
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).toLinearMap.toAddMonoidHom,
    ← AddMonoidHom.comp_assoc _
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ hρ).toLinearMap.toAddMonoidHom
      (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ
        hρ).symm.toLinearMap.toAddMonoidHom,
    hev, AddMonoidHom.id_comp]

/-- **The twisted `Ξ` of the map induced by `θ`, for constant coefficients**: no root of unity is
chosen. For `c : μ_{#R}(k̄) ⟶ μ_{#Λ}(k̄)` the identity on underlying units (e.g. `#R = #Λ`),
`Ξ` over `R` of the image of `x` is `Ξ(x) ∘ c` followed by `M ≅ Γ(X_k̄, ℱ_ρ|) ⟶ Γ(X_k̄, ℱ_W|) ≅ W`,
the middle map being `Γ(X_k̄, -)` of the restriction of `θ` to `X_k̄`. -/
theorem compactSupportTrivialTwistEquiv_restrictScalarsMapOfBar
    (hcard : Fintype.card R = Fintype.card Λ)
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hρ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation Λ _ ρ)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (W : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (hW : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      ∀ g, (finiteTypeContinuousModuleRepresentation R _ W)
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1)
    (θ : letI := connectedSpace_of_isCurve B X f
      (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ))) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) R).obj W)))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)) ((2 : ℕ) : ℤ))
    (c : Additive (_root_.rootsOfUnity (Fintype.card R) kbar) →+
      Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar))
    (hc : ∀ z, (((c z).toMul : kbarˣ) : kbar) = ((z.toMul : kbarˣ) : kbar)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportTrivialTwistEquiv B X f kbar R y j hnR W hW
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ _ _ θ x) =
      ((geometricGlobalSectionsTrivialEquivPullback B X f kbar R y W
        hW).toLinearMap.toAddMonoidHom.comp
        ((globalSectionsRestrictScalarsAddHom ψ _ _ _
          (compactSupportOpenRestriction f j kbar ψ _ _ θ)).comp
          (geometricGlobalSectionsTrivialEquivPullback B X f kbar Λ y ρ
            hρ).symm.toLinearMap.toAddMonoidHom)).comp
        ((compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ hρ x).comp c) := by
  let := connectedSpace_of_isCurve B X f
  have : NeZero (Fintype.card R) := ⟨Fintype.card_ne_zero⟩
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have hζR := (exists_isPrimitiveRoot_of_isUnit hnR).choose_spec
  have hζ : IsPrimitiveRoot (exists_isPrimitiveRoot_of_isUnit hnR).choose (Fintype.card Λ) :=
    hcard ▸ hζR
  have hcζ : c (Additive.ofMul hζR.toRootsOfUnity) = Additive.ofMul hζ.toRootsOfUnity :=
    Additive.toMul.injective <| Subtype.ext <| Units.ext <| hc _
  refine addMonoidHom_rootsOfUnity_ext hζR R (card_nsmul_eq_zero_of_module R) ?_
  rw [compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar R y j hnR W hW hζR,
    AddMonoidHom.comp_apply _ ((compactSupportTrivialTwistEquiv B X f kbar Λ y j hn ρ hρ x).comp c),
    AddMonoidHom.comp_apply _ c, hcζ,
    compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn ρ hρ hζ,
    ← linearEquiv_toAddMonoidHom_apply (compactSupportTrivialTrace B X f kbar R y j hnR W hW hζR)
      (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ _ _ θ x),
    ← AddMonoidHom.comp_apply _ (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ _ _ θ) x,
    ← linearEquiv_toAddMonoidHom_apply (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ) x,
    ← AddMonoidHom.comp_apply _
      (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).toLinearMap.toAddMonoidHom x,
    compactSupportTrivialTrace_comp_restrictScalarsMapOfBar B X f kbar ψ y j hn hnR hcard ρ hρ W hW
      hζ hζR θ,
    AddMonoidHom.comp_assoc
      (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).toLinearMap.toAddMonoidHom,
    AddMonoidHom.comp_assoc
      (compactSupportTrivialTrace B X f kbar Λ y j hn ρ hρ hζ).toLinearMap.toAddMonoidHom]

end Trivial

end AlgebraicGeometry

end
