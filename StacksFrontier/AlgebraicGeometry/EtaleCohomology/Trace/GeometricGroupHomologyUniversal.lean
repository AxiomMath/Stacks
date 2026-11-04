module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportCoeffaceable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelProperIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCurveVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective

/-!
# The homology of `π₁(X_k̄)` with finite coefficients is a universal δ-functor

Let `X` be a geometrically connected smooth curve over `k` with `X_k̄ ≇ ℙ¹`, `Λ` a finite ring (not
necessarily commutative) of order invertible in `k` and `G = π₁(X_k̄, η̄)`. For every finite
`Λ`-module `N` with continuous action of `π₁(X, η̄)` the groups `H^q(G, N)` are finite:

* `q = 0`: `H⁰(G, N) = N^G ⊆ N`;
* `q = 1`: embed `N` into a permutation module `P` (the untwisted unit `m ↦ (gH ↦ g⁻¹ • m)`);
  `H¹(G, P) = H¹(X_k̄, ℱ_P)` is finite (the count for permutation modules) and `H⁰` of the cokernel
  is finite;
* `q = 2`: `H²(G, N) = H²(X_k̄, ℱ_N)`, which is `0` if `X` is affine and is `H²_c(X_k̄, ℱ_N) = N_G`
  (Tag 03VK) if `X` is projective, `X_k̄` then being its own smooth projective model;
* `q ≥ 3`: `H^q(X_k̄, ℱ_N) = 0` (Tag 0A53).

Hence one coinduced module kills all of `H^{q}(G, N^∨)` (cohomology over `Λᵐᵒᵖ`), and the homology
`H_q(G, M) = H^q(G, M^∨)^∨` is coeffaceable, hence a universal homological δ-functor: the left
derived functors of `M ↦ M_G` on finite modules.

## Main results

* `AlgebraicGeometry.finite_geometricGroupCohomology`.
* `AlgebraicGeometry.coeffaceable_geometricGroupHomology`,
  `AlgebraicGeometry.isUniversal_geometricGroupHomology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology
  Stacks.Frobenius Stacks.ContinuousCohomology

universe u

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesGroupHomology (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for continuous discrete modules at the module universe of the group. -/
local instance (priority := 3000) enoughInjectives_continuousModule_groupHomology (Λ : Type)
    [Ring Λ] (G : Type (u + 1)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} Λ G

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [IsAlgClosure k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (j : CompactificationOf (Over.mk f))
  [ConnectedSpace X.1] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1]

/-- **The homology `H_q(π₁(X_k̄), M) = H^q(π₁(X_k̄), M^∨)^∨`** of the geometric fundamental group,
on finite `Λ`-modules with continuous action of `π₁(X, η̄)`. -/
abbrev geometricGroupHomology :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
      (ModuleCat.{u + 1} Λ) :=
  restrictedHomologyDelta Λ (geometricFundamentalGroupMap B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar) y)

omit [IsAlgClosed kbar] [IsAlgClosure k kbar] [ConnectedSpace X.1] [CompactSpace X.1]
  [QuasiSeparatedSpace X.1] in
/-- `H⁰(π₁(X_k̄), N) = N^{π₁(X_k̄)}` is finite. -/
theorem finite_geometricGroupCohomology_zero [ConnectedSpace X.1]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Finite (((geometricGroupCohomology B X Λ f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y).functor 0).obj N) := by
  have : Module.Finite Λ N.obj.obj.obj.V := N.property
  have : Finite N.obj.obj.obj.V := Module.finite_of_finite Λ
  let M := (finiteTypeContinuousModuleToRes Λ (geometricFundamentalGroupMap B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar) y)).obj N
  have e := ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).rightDerivedZeroIsoSelf).app M
  have : Finite M.obj.obj.V := inferInstanceAs (Finite N.obj.obj.obj.V)
  have : Finite ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ _).obj M) :=
    Subtype.finite
  exact Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm

variable (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  (hcomp : IsIso (geometricComparison B X Λ f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar) y))

include hn hcomp j in
/-- **`H^q(π₁(X_k̄), N)` is finite** for every finite `N` and every `q`. -/
theorem finite_geometricGroupCohomology
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) (q : ℕ) :
    Finite (((geometricGroupCohomology B X Λ f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y).functor q).obj N) := by
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  let E := geometricGroupCohomology B X Λ f kbar hK y
  have hcurve : IsCurve k f := inferInstance
  have hbij : ∀ (q : ℕ) (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ _),
      Function.Bijective (((geometricComparison B X Λ f kbar hK y).app q).app N) :=
    fun q N ↦ bijective_app_of_iso Λ (asIso (geometricComparison B X Λ f kbar hK y)) q N
  -- the étale side in degree `q`, and the transfer of finiteness
  have hfin : ∀ (q : ℕ) (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ _),
      Finite (((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).rightDerived
        q).obj ((geometricRepresentationSheaf B X _ Λ f kbar).obj N)) →
      Finite ((E.functor q).obj N) :=
    fun q N h ↦
      have : Finite
          (((geometricRepresentationCohomology.{u, 0} B X _ Λ f kbar).functor q).obj N) := h
      Finite.of_injective _ (hbij q N).1
  match q with
  | 0 => exact finite_geometricGroupCohomology_zero B X f kbar Λ y N
  | n + 3 =>
    refine hfin (n + 3) N ?_
    have := ModuleCat.subsingleton_of_isZero
      (isZero_rightDerived_fieldBaseChange_of_two_lt Λ f kbar hcurve
        ((geometricRepresentationSheaf B X _ Λ f kbar).obj N) (by omega : 2 < n + 3))
    exact Finite.of_subsingleton
  | 2 =>
    refine hfin 2 N ?_
    rcases isAffine_or_isProjectiveMorphism k f with hX | hX
    · have : IsAffine (fieldBaseChange (Over.mk f) kbar) :=
        inferInstanceAs (IsAffine (pullback f (specAlgebraMap k kbar)))
      have := ModuleCat.subsingleton_of_isZero
        (isZero_rightDerived_fieldBaseChange_of_isAffine Λ f kbar hcurve
          ((geometricRepresentationSheaf B X _ Λ f kbar).obj N) (by omega : 1 < 2))
      exact Finite.of_subsingleton
    · have := isProper_of_isProjectiveMorphism f hX
      have hp : IsProper (pullback.snd f (specAlgebraMap k kbar)) := inferInstance
      let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ (geometricSmoothModel f j kbar).Vb)
      let := HasDerivedCategory.standard
        (EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar)))
      let := HasDerivedCategory.standard
        (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar))
      let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
      obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
      let G := (geometricRepresentationSheaf B X _ Λ f kbar).obj N
      let e : ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).rightDerived
          2).obj G ≅ ((compactSupportRepresentationHomology B X _ Λ f j kbar).functor 0).obj N :=
        (Stacks.DerivedIndexing.rightDerivedIso _ 2).app G ≪≫
          (geometricSmoothModelProperRightDerivedPlusIso f j kbar Λ hp G ((2 : ℕ) : ℤ)).symm ≪≫
          ((Stacks.DerivedIndexing.rightDerivedIso _ 2).app _).symm
      let e' := (compactSupportRepresentationHomologyZeroIso B X _ Λ f j kbar N).toLinearEquiv.trans
        (compactSupportGeometricCoinvariantsEquiv B X f kbar Λ y j hn hζ N)
      exact Finite.of_equiv _ (e.toLinearEquiv.trans e').toEquiv.symm
  | 1 =>
    -- embed `N` into a permutation module through the untwisted unit
    obtain ⟨H₀, hH₀n, hH₀o, htriv⟩ :=
      exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar hK).hom)) N
    let H : OpenSubgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      hK).hom)) := ⟨H₀, hH₀o⟩
    have : H.toSubgroup.Normal := hH₀n
    let Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) :=
      ⟨N.obj.obj.obj.V, N.property⟩
    let P := (finiteTypeContinuousModuleCoind Λ H).obj
      ((finiteTypeContinuousModuleTrivial Λ _).obj Q)
    let ι : N ⟶ P := finiteTypeContinuousModuleUntwistUnit Λ H N htriv
    have : Mono ι := mono_finiteTypeContinuousModuleUntwistUnit Λ H N htriv
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel ι))
        inferInstance inferInstance
    -- `H⁰` of the cokernel and `H¹(P)` are finite
    have := finite_geometricGroupCohomology_zero B X f kbar Λ y S.X₃
    obtain ⟨-, hP, -⟩ := finite_and_natCard_compactSupportRepresentationHomology_one_le B X f kbar
      Λ y j (by rwa [Nat.card_eq_fintype_card]) H Q
    have : Finite ((E.functor 1).obj P) := Finite.of_injective _ (hbij 1 P).1
    have hexact := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (E.exact_δ₂ hS 0)
    let g := ((E.functor 1).map S.f).hom.toAddMonoidHom
    have : Finite g.ker := by
      refine Finite.of_surjective (fun z : (E.functor 0).obj S.X₃ ↦
        (⟨(E.δ hS 0).hom z, ?_⟩ : g.ker)) ?_
      · show ((E.functor 1).map S.f).hom ((E.δ hS 0).hom z) = 0
        rw [← ModuleCat.comp_apply, E.δ_map_f hS 0]
        rfl
      · rintro ⟨x, hx⟩
        obtain ⟨z, hz⟩ := hexact hx
        exact ⟨z, Subtype.ext hz⟩
    have : Finite g.range := Subtype.finite
    exact finite_of_finite_ker_of_finite_range g

omit hcomp in
include hn j in
/-- **The homology `H_q(π₁(X_k̄), -)` is coeffaceable**: `H^{q+1}(π₁(X_k̄), M^∨)` (cohomology over
`Λᵐᵒᵖ`) is finite, so one coinduced module kills all of it. -/
theorem coeffaceable_geometricGroupHomology
    (hcompOp : IsIso (geometricComparison B X Λᵐᵒᵖ f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y)) :
    (geometricGroupHomology B X f kbar Λ y).Coeffaceable := by
  have hK := contains_fieldBaseChange_of_isCurve B X f kbar
  have : (geometricGroupCohomology B X Λᵐᵒᵖ f kbar hK y).ElementwiseEffaceable :=
    elementwiseEffaceable_restrictedCohomologyDelta Λᵐᵒᵖ _
      (isInducing_geometricFundamentalGroupMap B X f kbar hK y)
  have : (finiteTypeContinuousModuleDualEquivalence Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar hK).hom))).functor.Additive :=
    finiteTypeContinuousModuleDual_additive Λ _
  have hnOp : IsUnit ((Fintype.card Λᵐᵒᵖ : ℕ) : kbar) := by
    rwa [Fintype.card_congr (MulOpposite.opEquiv (α := Λ)).symm]
  exact Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffaceable_ofDeltaFunctorDual
    (geometricGroupCohomology B X Λᵐᵒᵖ f kbar hK y) (finiteTypeContinuousModuleDualEquivalence Λ _)
    fun Y n ↦ have := finite_geometricGroupCohomology B X f kbar Λᵐᵒᵖ y j hnOp hcompOp Y (n + 1)
      DeltaFunctor.ElementwiseEffaceable.exists_mono_map_eq_zero_of_finite Y n

omit hcomp in
include hn j in
/-- **`H_q(π₁(X_k̄), -)` is a universal homological δ-functor**: the left derived functors of
`M ↦ M_{π₁(X_k̄)}` on finite modules with continuous action. -/
theorem isUniversal_geometricGroupHomology
    (hcompOp : IsIso (geometricComparison B X Λᵐᵒᵖ f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar) y)) :
    (geometricGroupHomology B X f kbar Λ y).IsUniversal :=
  have := coeffaceable_geometricGroupHomology B X f kbar Λ y j hn hcompOp
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

end AlgebraicGeometry

end
