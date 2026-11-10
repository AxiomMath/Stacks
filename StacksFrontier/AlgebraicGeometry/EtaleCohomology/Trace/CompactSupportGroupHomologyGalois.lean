module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwistNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportActionDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGroupHomologyTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwistGalois

/-!
# The Galois action on `H_c^{2-i}(X_k̄, ℱ_ρ) = H_i(π₁(X_k̄), M)(-1)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure and
`σ ∈ Aut_k(k̄) = Gal(k^{sep}/k)`. The action of `σ` on compactly supported cohomology
`H_c^q(X_k̄, ℱ_ρ)` (`Stacks.EtaleCohomology.galoisCompactSupportGroupAction`, induced by
`id_{X̄} × Spec σ`) commutes with the connecting morphisms
(`AlgebraicGeometry.compactSupportRepresentationCohomologyGalois`), so it is an endomorphism of
the homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)` of Tag 03VM.

## Main definitions

* `AlgebraicGeometry.compactSupportRepresentationHomologyGalois` — the action of `σ` on `T`.

## Main results

* `AlgebraicGeometry.compactSupportRepresentationHomologyGalois_app_comp_iso` — in degree
  `i ≤ 2` it is the action of `σ` on `H_c^{2-i}(X_k̄, ℱ_ρ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius Stacks.ContinuousCohomology

universe u v

namespace CategoryTheory

/-- Three commuting squares paste along composites of isomorphisms. -/
lemma Iso.trans_trans_hom_comm {C : Type*} [Category C] {A B D E A' B' D' E' : C} (Z : A ≅ B)
    (Z' : A' ≅ B') (Ψ : B ≅ D) (Ψ' : B' ≅ D') (K : D ≅ E) (K' : D' ≅ E') (s : A ⟶ A')
    (g : B ⟶ B') (r : D ⟶ D') (t : E ⟶ E') (hT : s ≫ Z'.hom = Z.hom ≫ g)
    (hΨ : g ≫ Ψ'.hom = Ψ.hom ≫ r) (hC : r ≫ K'.hom = K.hom ≫ t) :
    s ≫ (Z' ≪≫ Ψ' ≪≫ K').hom = (Z ≪≫ Ψ ≪≫ K).hom ≫ t := by
  simp only [Iso.trans_hom, ← Category.assoc, hT]
  simp only [Category.assoc, reassoc_of% hΨ, hC]

/-- Two commuting squares paste along composites of isomorphisms. -/
lemma Iso.trans_hom_comm {C : Type*} [Category C] {A B D A' B' D' : C} (Z : A ≅ B) (Z' : A' ≅ B')
    (Ψ : B ≅ D) (Ψ' : B' ≅ D') (s : A ⟶ A') (g : B ⟶ B') (r : D ⟶ D')
    (hT : s ≫ Z'.hom = Z.hom ≫ g) (hΨ : g ≫ Ψ'.hom = Ψ.hom ≫ r) :
    s ≫ (Z' ≪≫ Ψ').hom = (Z ≪≫ Ψ).hom ≫ r := by
  simp only [Iso.trans_hom, ← Category.assoc, hT]
  simp only [Category.assoc, hΨ]

/-- A square with horizontal isomorphisms commutes with their inverses. -/
lemma Iso.inv_comm_of_hom_comm {C : Type*} [Category C] {A B A' B' : C} (N : A ≅ B) (N' : A' ≅ B')
    (f : A ⟶ A') (φ : B ⟶ B') (h : f ≫ N'.hom = N.hom ≫ φ) : φ ≫ N'.inv = N.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory

/-- The isomorphism `A ≅ ModuleCat.of R X` in `ModuleCat R` of a linear equivalence `A ≃ₗ[R] X`
out of (the carrier of) an object `A`. -/
def LinearEquiv.toModuleIsoOfModuleCat {R : Type*} [Ring R] {A : ModuleCat.{v} R} {X : Type v}
    [AddCommGroup X] [Module R X] (e : A ≃ₗ[R] X) : A ≅ ModuleCat.of R X where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext e.apply_symm_apply)

/-- Linear equivalences `e`, `e'` intertwining `g` and `r` elementwise intertwine them in
`ModuleCat`. -/
lemma LinearEquiv.toModuleIsoOfModuleCat_hom_comm {R : Type*} [Ring R] {A A' : ModuleCat.{v} R}
    {X X' : Type v} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] (e : A ≃ₗ[R] X)
    (e' : A' ≃ₗ[R] X') (g : A ⟶ A') (r : X →ₗ[R] X') (h : ∀ x, e' (g.hom x) = r (e x)) :
    g ≫ e'.toModuleIsoOfModuleCat.hom = e.toModuleIsoOfModuleCat.hom ≫ ModuleCat.ofHom r :=
  ModuleCat.hom_ext (LinearMap.ext h)

namespace AlgebraicGeometry

section Etale

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesHomologyGalois (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The action of `σ ∈ Aut_k(k̄)` on `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)`** as an endomorphism of
homological δ-functors. -/
def compactSupportRepresentationHomologyGalois :
    compactSupportRepresentationHomology B X x Λ f j kbar ⟶
      compactSupportRepresentationHomology B X x Λ f j kbar :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.ofDeltaFunctorTwoSubMap
    (isZero_compactSupportRepresentationCohomology_three B X x Λ f j kbar)
    (compactSupportRepresentationCohomologyGalois B X x Λ f j kbar σ)
    (isZero_compactSupportRepresentationCohomology_three B X x Λ f j kbar)

/-- In degree `q` the action on `H^q(C, j_{C!}(ℱ_ρ|_{X_k̄}))` is, through the smooth model, the
action of `σ` on `H^q_c(X_k̄, ℱ_ρ)`. -/
theorem compactSupportRepresentationCohomologyGalois_app_comp_smoothModelIso (q : ℕ)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((compactSupportRepresentationCohomologyGalois B X x Λ f j kbar σ).app q).app M ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).hom.app
          ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj M) ≫
        (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
          (q : ℤ)).inv =
      ((Stacks.DerivedIndexing.rightDerivedIso
          (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q).hom.app
          ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj M) ≫
        (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
          (q : ℤ)).inv) ≫
        galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X x Λ).obj M))
          (q : ℤ) := by
  have h := galoisCompactSupportSmoothModelIso_hom_galoisAction f j kbar Λ σ
    ((representationSheaf B X x Λ).obj M) (q : ℤ)
  have h' : geometricSmoothModelGaloisAction f j kbar Λ σ ((representationSheaf B X x Λ).obj M) q ≫
      (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
        (q : ℤ)).inv =
    (galoisCompactSupportSmoothModelIso f j kbar Λ ((representationSheaf B X x Λ).obj M)
        (q : ℤ)).inv ≫
      galoisCompactSupportGroupAction Λ f j kbar σ
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X x Λ).obj M))
        (q : ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  have e3 := Iso.inv_hom_id_app (Stacks.DerivedIndexing.rightDerivedIso
    (etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb) q)
    ((compactSupportRepresentationSheaf B X x Λ f j kbar).obj M)
  refine (congrArg (· ≫ _) (compactSupportRepresentationCohomologyGalois_app_app B X x Λ f j kbar σ
    q M)).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e3)).trans
      (Category.id_comp _)))))).trans ((congrArg (_ ≫ ·) h').trans (Category.assoc _ _ _).symm)

/-- **In degree `i ≤ 2` the action of `σ` on `Tᵢ` is the action of `σ` on
`H_c^{2-i}(X_k̄, ℱ_ρ)`** (`Stacks.EtaleCohomology.galoisCompactSupportGroupAction`), through
`Tᵢ(ρ) ≅ H_c^{2-i}(X_k̄, ℱ_ρ)`. -/
theorem compactSupportRepresentationHomologyGalois_app_comp_iso (i : ℕ) (hi : i ≤ 2)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((compactSupportRepresentationHomologyGalois B X x Λ f j kbar σ).app i).app M ≫
        (compactSupportRepresentationHomologyIso B X x Λ f j kbar i hi M).hom =
      (compactSupportRepresentationHomologyIso B X x Λ f j kbar i hi M).hom ≫
        galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X x Λ).obj M))
          ((2 - i : ℕ) : ℤ) := by
  have h := compactSupportRepresentationCohomologyGalois_app_comp_smoothModelIso B X x Λ f j kbar
    σ (2 - i) M
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals refine Eq.trans ?_ (h.trans ?_)
  all_goals first
    | exact congrArg (_ ≫ ·) (Category.id_comp _)
    | exact congrArg (· ≫ _) (Category.id_comp _).symm

/-- **In degree zero the action of `σ` on `T₀` is the action of `σ` on `H²_c(X_k̄, ℱ_ρ)`**,
through `T₀(ρ) ≅ H²_c(X_k̄, ℱ_ρ)`
(`AlgebraicGeometry.compactSupportRepresentationHomologyZeroIso`). -/
theorem compactSupportRepresentationHomologyGalois_app_zero_comp_zeroIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ((compactSupportRepresentationHomologyGalois B X x Λ f j kbar σ).app 0).app M ≫
        (compactSupportRepresentationHomologyZeroIso B X x Λ f j kbar M).hom =
      (compactSupportRepresentationHomologyZeroIso B X x Λ f j kbar M).hom ≫
        galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj ((representationSheaf B X x Λ).obj M))
          ((2 : ℕ) : ℤ) :=
  compactSupportRepresentationCohomologyGalois_app_comp_smoothModelIso B X x Λ f j kbar σ 2 M

end Etale

/-- Linear equivalences `A ≃ Hom(μ_n, V)` and `A' ≃ Hom(μ_n, V')` intertwining `g` with
postcomposition by `N : V ⟶ V'` elementwise intertwine `g` with `Hom(μ_n, N)` in `ModuleCat`. -/
lemma rootsOfUnityHomFunctor_map_toModuleIsoOfModuleCat_comm {Λ : Type} [Ring Λ] {K : Type u}
    [Field K] {n : ℕ} {A A' V V' : ModuleCat.{u + 1} Λ}
    (e : A ≃ₗ[Λ] (Additive (_root_.rootsOfUnity n K) →+ V))
    (e' : A' ≃ₗ[Λ] (Additive (_root_.rootsOfUnity n K) →+ V')) (g : A ⟶ A') (N : V ⟶ V')
    (h : ∀ x, e' (g.hom x) = N.hom.toAddMonoidHom.comp (e x)) :
    g ≫ e'.toModuleIsoOfModuleCat.hom =
      e.toModuleIsoOfModuleCat.hom ≫ (rootsOfUnityHomFunctor Λ K n).map N :=
  ModuleCat.hom_ext (LinearMap.ext h)

section Group

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (σ : kbar ≃ₐ[k] kbar)

/-- **The action of `σ ∈ Aut_k(k̄)` on `M_{π₁(X_k̄)}`**: through `M_{π₁(X_k̄)} = M_N`
(`AlgebraicGeometry.geometricCoinvariantsRangeEquiv`, `N` the image of `π₁(X_k̄)`), the residual
action of `π₁(X, η̄)/N = Aut_k(k̄)`
(`AlgebraicGeometry.geometricCoinvariantsGaloisRepresentation`). -/
def geometricCoinvariantsGaloisMap
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y M) →ₗ[Λ]
      Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y M) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  ((geometricCoinvariantsRangeEquiv B X f kbar Λ y M).symm.toLinearMap.comp
    (geometricCoinvariantsGaloisRepresentation B X f kbar Λ y M σ)).comp
    (geometricCoinvariantsRangeEquiv B X f kbar Λ y M).toLinearMap

omit [Smooth f] in
/-- `σ` acts on the class of `m` by the class of `γ • m`, for `γ ∈ π₁(X, η̄)` lifting `σ`. -/
theorem geometricCoinvariantsGaloisMap_mk
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (hγ : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) = σ)
    (m : M.obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricCoinvariantsGaloisMap B X f kbar Λ y σ M (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (finiteTypeContinuousModuleRepresentation Λ _ M γ m) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  subst hγ
  exact congrArg (geometricCoinvariantsRangeEquiv B X f kbar Λ y M).symm
    (galoisCoinvariantsRepresentation_apply_mk (finiteTypeContinuousModuleRepresentation Λ _ M) _
      (geometricQuotientGaloisEquiv B X f kbar y) γ m)

/-- **The action of `σ ∈ Aut_k(k̄)` on `M ↦ M_{π₁(X_k̄)}`**, natural in `M`
(`AlgebraicGeometry.geometricCoinvariantsGaloisMap`). -/
def geometricCoinvariantsGaloisAction :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    restrictedCoinvariantsFunctor Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y) ⟶
      restrictedCoinvariantsFunctor Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  { app M := ModuleCat.ofHom (geometricCoinvariantsGaloisMap B X f kbar Λ y σ M)
    naturality M M' v := by
      obtain ⟨γ, hγ⟩ := exists_geometricQuotientGaloisEquiv_mk_eq B X f kbar y σ
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro m
      have h1 := geometricCoinvariantsGaloisMap_mk B X f kbar Λ y σ M' γ hγ
        (v.hom.hom.hom.hom.hom m)
      have h2 := geometricCoinvariantsGaloisMap_mk B X f kbar Λ y σ M γ hγ m
      exact h1.trans ((congrArg Submodule.Quotient.mk
        (finiteTypeContinuousModule_hom_comm v γ m).symm).trans
        (congrArg (fun z ↦ (finiteTypeContinuousModuleCoinvariantsMap Λ _
          ((finiteTypeContinuousModuleRes Λ (geometricFundamentalGroupMap B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar) y)).map v)) z) h2.symm)) }

/-- **Precomposition with `σ⁻¹` on `μ_n(k̄)`**, the Galois action on the twist `Hom(μ_n, -)`. -/
def rootsOfUnityHomGaloisPrecomp (n : ℕ) :
    rootsOfUnityHomFunctor Λ kbar n ⟶ rootsOfUnityHomFunctor Λ kbar n where
  app _ := ModuleCat.ofHom
    { toFun := fun g ↦ g.comp (galoisRootsOfUnity k kbar n σ⁻¹).toAdditive
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

variable [IsAlgClosure k kbar] (j : CompactificationOf (Over.mk f)) [CompactSpace X.1]
  [QuasiSeparatedSpace X.1] (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **The action of `σ` on `H₀(π₁(X_k̄), M)(-1) = Hom(μ_n, M_{π₁(X_k̄)})`**: `σ` on the
coinvariants and `σ⁻¹` on `μ_n`, i.e. `f ↦ σ ∘ f ∘ σ⁻¹`. -/
def geometricGroupHomologyTwistGaloisZero :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0 ⟶
      (geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0 :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  (Functor.whiskerRight ((restrictedHomologyZeroIso Λ (geometricFundamentalGroupMap B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y)).hom ≫
      geometricCoinvariantsGaloisAction B X f kbar Λ y σ ≫
      (restrictedHomologyZeroIso Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).inv)
      (rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)) ≫
    Functor.whiskerLeft ((geometricGroupHomology B X f kbar Λ y).functor 0)
      (rootsOfUnityHomGaloisPrecomp kbar Λ σ (Fintype.card Λ)) :
    (geometricGroupHomology B X f kbar Λ y).functor 0 ⋙
        rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ) ⟶
      (geometricGroupHomology B X f kbar Λ y).functor 0 ⋙
        rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ))

variable (hcompOp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λᵐᵒᵖ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hcompOp in
/-- **The action of `σ ∈ Aut_k(k̄)` on `H_i(π₁(X_k̄, η̄), M)(-1)`**: the unique endomorphism of the
universal homological δ-functor `M ↦ H_i(π₁(X_k̄), M)(-1)` which in degree zero is the action
`f ↦ σ ∘ f ∘ σ⁻¹` on `Hom(μ_n, M_{π₁(X_k̄)})`. In degree `i` it is the action of a lift of `σ` to
`π₁(X, η̄)` by conjugation on `π₁(X_k̄)` and on `M`, which, being an endomorphism of δ-functors
extending that of degree zero, is this one. -/
def geometricGroupHomologyTwistGalois :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGroupHomologyTwist B X f kbar Λ y hn ⟶ geometricGroupHomologyTwist B X f kbar Λ y hn :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI := isUniversal_geometricGroupHomologyTwist B X f kbar Λ y j hn hcompOp
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.lift
    (geometricGroupHomologyTwistGaloisZero B X f kbar Λ y σ hn)

include hcompOp in
/-- In degree zero, the action of `σ` on `H₀(π₁(X_k̄), M)(-1)` is
`AlgebraicGeometry.geometricGroupHomologyTwistGaloisZero`. -/
lemma geometricGroupHomologyTwistGalois_app_zero :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGroupHomologyTwistGalois B X f kbar Λ y σ j hn hcompOp).app 0 =
      geometricGroupHomologyTwistGaloisZero B X f kbar Λ y σ hn := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := isUniversal_geometricGroupHomologyTwist B X f kbar Λ y j hn hcompOp
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.lift_app_zero _

/-- **`H₀(π₁(X_k̄), M) ≅ M_N`**, `N` the image of `π₁(X_k̄)` in `π₁(X, η̄)`, as the module of
`ρ_N = AlgebraicGeometry.geometricNormalCoinvariants`. -/
def geometricGroupHomologyZeroNormalIso
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((restrictedHomologyDelta Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).functor 0).obj M ≅
      ModuleCat.of Λ (geometricNormalCoinvariants B X f kbar Λ y M).obj.obj.obj.V :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  (restrictedHomologyZeroIso Λ (geometricFundamentalGroupMap B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y)).app M ≪≫
    ((geometricCoinvariantsRangeEquiv B X f kbar Λ y M).trans
      (geometricNormalCoinvariantsEquiv B X f kbar Λ y M).symm).toModuleIso

/-- **The degree-zero identification `H²_c(X_k̄, ℱ_ρ) ≅ H₀(π₁(X_k̄), M)(-1)`, root-of-unity
free**: the composite of `T₀ ≅ H²_c`
(`AlgebraicGeometry.compactSupportRepresentationHomologyZeroIso`), the canonical
`Ψ : H²_c ≅ Hom(μ_n, M_N)` of Tag 03VK (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv`) and
`M_N ≅ H₀(π₁(X_k̄), M)`. -/
def compactSupportGroupHomologyTwistZeroIsoApp
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar).functor 0).obj M ≅
      ((geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0).obj M :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar M ≪≫
    (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn M).toModuleIsoOfModuleCat ≪≫
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).symm

omit [Smooth f] [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- Under `Hom(μ_n, M_N) ≅ H₀(π₁(X_k̄), M)(-1)`, the action `f ↦ σ ∘ f ∘ σ⁻¹` of Tag 03VK on the
left is the degree-zero action on the right. -/
theorem rootsOfUnityHomRepresentation_geometricGroupHomologyZeroNormalIso
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ModuleCat.ofHom (rootsOfUnityHomRepresentation k kbar (Fintype.card Λ) Λ
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y M) σ) ≫
      ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
        (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).inv =
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
        (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).inv ≫
      (geometricGroupHomologyTwistGaloisZero B X f kbar Λ y σ hn).app M := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let H0 := (restrictedHomologyZeroIso Λ (geometricFundamentalGroupMap B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar) y)).app M
  let R := geometricCoinvariantsRangeEquiv B X f kbar Λ y M
  let E := geometricNormalCoinvariantsEquiv B X f kbar Λ y M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  apply AddMonoidHom.ext
  intro z
  let w := g (Additive.ofMul (galoisRootsOfUnity k kbar (Fintype.card Λ) σ⁻¹ z.toMul))
  have hE := geometricNormalCoinvariantsEquiv_galoisRepresentation B X f kbar Λ y σ M w
  have hH : H0.hom.hom (H0.inv.hom (R.symm (E w))) = R.symm (E w) :=
    congrArg (fun φ ↦ φ.hom (R.symm (E w))) H0.inv_hom_id
  calc _ = H0.inv.hom (R.symm (E (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y M σ
          w))) := rfl
    _ = H0.inv.hom (R.symm (geometricCoinvariantsGaloisRepresentation B X f kbar Λ y M σ (E w))) :=
          congrArg (fun v ↦ H0.inv.hom (R.symm v)) hE
    _ = H0.inv.hom (geometricCoinvariantsGaloisMap B X f kbar Λ y σ M (R.symm (E w))) :=
          congrArg (fun v ↦ H0.inv.hom (R.symm
            (geometricCoinvariantsGaloisRepresentation B X f kbar Λ y M σ v)))
            (R.apply_symm_apply (E w)).symm
    _ = H0.inv.hom (geometricCoinvariantsGaloisMap B X f kbar Λ y σ M
          (H0.hom.hom (H0.inv.hom (R.symm (E w))))) :=
          congrArg (fun v ↦ H0.inv.hom (geometricCoinvariantsGaloisMap B X f kbar Λ y σ M v))
            hH.symm
    _ = _ := rfl

omit [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **The degree-zero identification is Galois-equivariant**: under
`H²_c(X_k̄, ℱ_ρ) ≅ H₀(π₁(X_k̄), M)(-1)`, the action of `σ` on `H²_c` (Tag 03VK, through the
canonical `Ψ`) is the action `f ↦ σ ∘ f ∘ σ⁻¹` on `Hom(μ_n, M_{π₁(X_k̄)})`. -/
theorem compactSupportGroupHomologyTwistZeroIsoApp_galois
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    haveI : Finite Λ := Finite.of_fintype Λ
    ((compactSupportRepresentationHomologyGalois B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar σ).app 0).app M ≫
          (compactSupportGroupHomologyTwistZeroIsoApp B X f kbar Λ y j hn M).hom =
      (compactSupportGroupHomologyTwistZeroIsoApp B X f kbar Λ y j hn M).hom ≫
        (geometricGroupHomologyTwistGaloisZero B X f kbar Λ y σ hn).app M := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : Finite Λ := Finite.of_fintype Λ
  have hT := compactSupportRepresentationHomologyGalois_app_zero_comp_zeroIso B X _ Λ f j kbar σ M
  have key := LinearEquiv.toModuleIsoOfModuleCat_hom_comm _ _ _ _
    (compactSupportCanonicalTwistEquiv_galois B X f kbar Λ y j hn σ M)
  exact CategoryTheory.Iso.trans_trans_hom_comm
    (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar M)
    (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar M)
    (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn M).toModuleIsoOfModuleCat
    (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn M).toModuleIsoOfModuleCat
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).symm
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).symm _ _ _ _ hT key
    (rootsOfUnityHomRepresentation_geometricGroupHomologyZeroNormalIso B X f kbar Λ y σ hn M)

omit [Smooth f] [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **`H₀(π₁(X_k̄), M) ≅ M_N` is natural in `M`.** -/
theorem geometricGroupHomologyZeroNormalIso_hom_naturality
    {M M' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : M ⟶ M') :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((restrictedHomologyDelta Λ (geometricFundamentalGroupMap B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar) y)).functor 0).map v ≫
        (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M').hom =
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M).hom ≫
        ModuleCat.ofHom (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom.hom := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  refine CategoryTheory.Iso.trans_hom_comm _ _ _ _ _ _ _
    ((restrictedHomologyZeroIso Λ (geometricFundamentalGroupMap B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y)).hom.naturality v) ?_
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro m
  rfl

omit [Smooth f] [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **The twist of `H₀(π₁(X_k̄), M) ≅ M_N` is natural in `M`**, read in the direction
`Hom(μ_n, M_N) ⟶ H₀(π₁(X_k̄), M)(-1)`. -/
theorem rootsOfUnityHomFunctor_geometricGroupHomologyZeroNormalIso_inv_naturality
    {M M' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : M ⟶ M') :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).map
        (ModuleCat.ofHom (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom.hom) ≫
        ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
          (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M')).symm.hom =
      ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
          (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).symm.hom ≫
        ((geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0).map v := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).map_comp _ _).symm.trans
    ((congrArg (rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).map
      (CategoryTheory.Iso.inv_comm_of_hom_comm _ _ _ _
        (geometricGroupHomologyZeroNormalIso_hom_naturality B X f kbar Λ y v))).trans
      ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).map_comp _ _))

omit [IsAlgClosure k kbar] [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- **The degree-zero identification `H²_c(X_k̄, ℱ_ρ) ≅ H₀(π₁(X_k̄), M)(-1)` is natural in `ρ`**,
from the naturality of `Ψ` (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv_naturality`). -/
theorem compactSupportGroupHomologyTwistZeroIsoApp_naturality
    {M M' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : M ⟶ M') :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar).functor 0).map v ≫
        (compactSupportGroupHomologyTwistZeroIsoApp B X f kbar Λ y j hn M').hom =
      (compactSupportGroupHomologyTwistZeroIsoApp B X f kbar Λ y j hn M).hom ≫
        ((geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0).map v := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  refine CategoryTheory.Iso.trans_trans_hom_comm
    (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar M)
    (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar M')
    (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn M).toModuleIsoOfModuleCat
    (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn M').toModuleIsoOfModuleCat
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M)).symm
    ((rootsOfUnityHomFunctor Λ kbar (Fintype.card Λ)).mapIso
      (geometricGroupHomologyZeroNormalIso B X f kbar Λ y M')).symm _ _ _ _
    (compactSupportRepresentationHomologyZeroIso_hom_naturality B X _ Λ f j kbar v)
    (rootsOfUnityHomFunctor_map_toModuleIsoOfModuleCat_comm _ _ _
      (geometricNormalCoinvariantsMap B X f kbar Λ y v).hom.hom.hom.hom ?_)
    (rootsOfUnityHomFunctor_geometricGroupHomologyZeroNormalIso_inv_naturality B X f kbar Λ y hn v)
  intro x
  rw [compactSupportCanonicalTwistEquiv_naturality B X f kbar Λ y j hn v x]

/-- **The degree-zero identification `T₀ ≅ H₀(π₁(X_k̄), -)(-1)`, root-of-unity free**, as functors
(`AlgebraicGeometry.compactSupportGroupHomologyTwistZeroIsoApp`). -/
def compactSupportGroupHomologyTwistZeroIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar).functor 0 ≅ (geometricGroupHomologyTwist B X f kbar Λ y hn).functor 0 :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  NatIso.ofComponents (compactSupportGroupHomologyTwistZeroIsoApp B X f kbar Λ y j hn)
    (fun v ↦ compactSupportGroupHomologyTwistZeroIsoApp_naturality B X f kbar Λ y j hn v)

variable (hcomp : letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    IsIso (geometricComparison B X Λ f kbar (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hcomp hcompOp in
/-- **`H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)`** as homological δ-functors, extending the
root-of-unity free degree-zero identification of Tag 03VK
(`AlgebraicGeometry.compactSupportGroupHomologyTwistZeroIso`). -/
def compactSupportGroupHomologyTwistIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportRepresentationHomology B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar ≅ geometricGroupHomologyTwist B X f kbar Λ y hn :=
  compactSupportGroupHomologyTwistIsoOfZero B X f kbar Λ y j hn hcomp hcompOp
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
    (compactSupportGroupHomologyTwistZeroIso B X f kbar Λ y j hn)

include hcomp hcompOp in
/-- In degree zero, `AlgebraicGeometry.compactSupportGroupHomologyTwistIso` is
`AlgebraicGeometry.compactSupportGroupHomologyTwistZeroIso`. -/
lemma compactSupportGroupHomologyTwistIso_hom_app_zero :
    (compactSupportGroupHomologyTwistIso B X f kbar Λ y j hn hcompOp hcomp).hom.app 0 =
      (compactSupportGroupHomologyTwistZeroIso B X f kbar Λ y j hn).hom := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := isUniversal_compactSupportRepresentationHomology B X f kbar Λ y j hn
    (exists_isPrimitiveRoot_of_isUnit hn).choose_spec hcomp hcompOp
  have := isUniversal_geometricGroupHomologyTwist B X f kbar Λ y j hn hcompOp
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _

include hcomp hcompOp in
/-- **`H_c^{2-i}(X_k̄, ℱ_ρ) ≅ H_i(π₁(X_k̄, η̄), M)(-1)` is Galois-equivariant**
([Stacks, Tag 03VM]): for `σ ∈ Aut_k(k̄)`, the action of `σ` on `H_c^{2-i}(X_k̄, ℱ_ρ)`
(`AlgebraicGeometry.compactSupportRepresentationHomologyGalois`) corresponds to the action of `σ`
on `H_i(π₁(X_k̄), M)(-1)` (`AlgebraicGeometry.geometricGroupHomologyTwistGalois`), in every
degree. Both are endomorphisms of universal δ-functors, so it is enough to compare them in degree
zero, where it is Tag 03VK through the canonical `Ψ`. -/
theorem compactSupportGroupHomologyTwistIso_galois :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportRepresentationHomologyGalois B X
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)
        Λ f j kbar σ ≫
          (compactSupportGroupHomologyTwistIso B X f kbar Λ y j hn hcompOp hcomp).hom =
      (compactSupportGroupHomologyTwistIso B X f kbar Λ y j hn hcompOp hcomp).hom ≫
        geometricGroupHomologyTwistGalois B X f kbar Λ y σ j hn hcompOp := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have := isUniversal_geometricGroupHomologyTwist B X f kbar Λ y j hn hcompOp
  refine Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.hom_ext_zero ?_
  rw [Stacks.CategoryHomology.HomologicalDeltaFunctor.comp_app,
    Stacks.CategoryHomology.HomologicalDeltaFunctor.comp_app,
    compactSupportGroupHomologyTwistIso_hom_app_zero, geometricGroupHomologyTwistGalois_app_zero]
  exact NatTrans.ext (funext fun M ↦
    compactSupportGroupHomologyTwistZeroIsoApp_galois B X f kbar Λ y σ j hn M)

end Group

end AlgebraicGeometry

end
