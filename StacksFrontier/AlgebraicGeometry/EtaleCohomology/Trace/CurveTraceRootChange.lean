module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RootsOfUnityHomTwist

/-!
# Changing the primitive root of unity in the trace `H²(C, ℤ/n) ≅ ℤ/n`

Let `C` be a smooth proper curve over an algebraically closed field `K` and `n` invertible in
`K`.  The identification `H²(C, ℤ/n) ≅ ℤ/n` of `Stacks.EtaleCohomology.curveConstantTrace`
passes through `ℤ/n ≅ μ_n`, `m ↦ ζ^m`, for a primitive `n`-th root of unity `ζ`, and so does
everything built on it: the module trace `H²(C, E_C) ≅ E`, its boundary version
`H²(C, j_!(E_U)) ≅ E`, the map `ψ_N` onto the coinvariants and the map `θ_ρ` of Tag 03VK.
Replacing `ζ` by `ζ' = ζ^b` multiplies each of them by `b`.  This is what makes the pairing
`(ζ, x) ↦ θ_ζ(x)` additive in `ζ`, hence a canonical, choice-free map
`H²_c(X_k̄, ℱ_ρ) ⟶ Hom(μ_n(k̄), M_π) = M_π(-1)`.

## Main results

* `Stacks.Kummer.rootsOfUnityConstantHom_of_pow_eq` — `ℤ/n ⟶ μ_n` for `ζ^b` is `b` times the
  one for `ζ`.
* `Stacks.EtaleCohomology.curveConstantTrace_of_pow_eq`,
  `Stacks.EtaleCohomology.curveConstantClass_of_pow_eq`,
  `Stacks.EtaleCohomology.curveConstantModuleTrace_of_pow_eq`,
  `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace_of_pow_eq`,
  `Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap_of_pow_eq` and
  `AlgebraicGeometry.compactSupportGeometricCoinvariantsMap_of_pow_eq` — the effect of
  `ζ ↦ ζ^b` on each map.
* `AlgebraicGeometry.compactSupportGeometricTwistMap_apply_ofMul` — the choice-free map
  `Θ : H²_c(X_k̄, ℱ_ρ) ⟶ Hom(μ_n(k̄), M_π)` (`AlgebraicGeometry.compactSupportGeometricTwistMap`)
  evaluated at any primitive `ζ` is `θ_ρ` for `ζ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Opposite Stacks.GroupCohomology Stacks.Frobenius

universe u

namespace Stacks.Kummer

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {ζ ζ' : k}
  (hζ : IsPrimitiveRoot ζ n) (hζ' : IsPrimitiveRoot ζ' n) (hn : n ≠ 0) {b : ℕ} (hb : ζ ^ b = ζ')

include hb in
/-- The image of `ζ^b` in the invertible functions on `U` is the `b`-th power of the image
of `ζ`. -/
theorem rootOn_of_pow_eq (U : X.Etale) : rootOn f hζ' hn U = rootOn f hζ hn U ^ b := by
  rw [rootOn, rootOn, ← map_pow]
  congr 1
  ext
  simp [hb]

/-- The section of `𝐆_m` of a power is the multiple of the section. -/
theorem ofUnit_pow {U : X.Etale} (x : (Γ(U.left, ⊤))ˣ) (b : ℕ) :
    ofUnit.{u, 0} (x ^ b) = b • ofUnit.{u, 0} x := by
  change ULift.up (Additive.ofMul (x ^ b)) = ULift.up (b • Additive.ofMul x)
  rw [ofMul_pow]

include hb in
/-- The map `ℤ/n ⟶ 𝐆_m(U)` for `ζ^b` is `b` times the one for `ζ`. -/
theorem rootHom_of_pow_eq (U : X.Etale) (m : ZMod n) :
    rootHom f hζ' hn U m = b • rootHom f hζ hn U m := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
  rw [rootHom_intCast, rootHom_intCast, rootOn_of_pow_eq f hζ hζ' hn hb, ofUnit_pow,
    smul_comm]

include hb in
/-- The presheaf map `ℤ/n ⟶ 𝐆_m` for `ζ^b` is `b` times the one for `ζ`. -/
theorem rootPresheafHom_of_pow_eq :
    rootPresheafHom f hζ' hn = b • rootPresheafHom f hζ hn := by
  ext U m
  exact rootHom_of_pow_eq f hζ hζ' hn hb U.unop m.down

include hb in
/-- The sheaf map `ℤ/n ⟶ 𝐆_m` for `ζ^b` is `b` times the one for `ζ`. -/
theorem rootSheafHom_of_pow_eq :
    rootSheafHom f hζ' hn = b • rootSheafHom f hζ hn := by
  ext : 1
  refine sheafify_hom_ext _ _ _ (multiplicativeSheaf.{u, 0} X).property ?_
  have h3 : (b • rootSheafHom f hζ hn).hom = b • (rootSheafHom f hζ hn).hom :=
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_nsmul
  refine (toSheafify_rootSheafHom f hζ' hn).trans ?_
  rw [rootPresheafHom_of_pow_eq f hζ hζ' hn hb, h3]
  exact congrArg (b • ·) (toSheafify_rootSheafHom f hζ hn).symm |>.trans
    (Preadditive.comp_nsmul _ _ _).symm

include hb in
/-- **`ℤ/n ⟶ μ_n` for `ζ^b` is `b` times the one for `ζ`.** -/
theorem rootsOfUnityConstantHom_of_pow_eq :
    rootsOfUnityConstantHom f hζ' hn = b • rootsOfUnityConstantHom f hζ hn := by
  rw [← cancel_mono (rootsOfUnityι.{u, 0} X n), Preadditive.nsmul_comp,
    rootsOfUnityConstantHom_comp_ι, rootsOfUnityConstantHom_comp_ι,
    rootSheafHom_of_pow_eq f hζ hζ' hn hb]

end Stacks.Kummer

namespace Stacks.EtaleCohomology

section Abelian

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {n : ℕ} (hn : IsUnit (n : K)) {ζ ζ' : K}
  (hζ : IsPrimitiveRoot ζ n) (hζ' : IsPrimitiveRoot ζ' n) {b : ℕ} (hb : ζ ^ b = ζ')

include hb in
/-- **The trace for `ζ^b` is `b` times the trace for `ζ`.** -/
theorem curveConstantTrace_of_pow_eq
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) 2) :
    curveConstantTrace q hn hζ' x = b • curveConstantTrace q hn hζ x := by
  change Stacks.Kummer.smoothProperCurveTrace q hn
      (sheafHRootsOfUnityConstantAddEquiv q hζ' (Stacks.Kummer.neZero_of_isUnit hn) 2 x) =
    b • Stacks.Kummer.smoothProperCurveTrace q hn
      (sheafHRootsOfUnityConstantAddEquiv q hζ (Stacks.Kummer.neZero_of_isUnit hn) 2 x)
  rw [sheafHRootsOfUnityConstantAddEquiv_apply, sheafHRootsOfUnityConstantAddEquiv_apply,
    Stacks.Kummer.rootsOfUnityConstantHom_of_pow_eq q hζ hζ' _ hb, sheafH_map_nsmul]
  exact map_nsmul (Stacks.Kummer.smoothProperCurveTrace q hn) b _

include hb in
/-- **The fundamental class for `ζ` is `b` times the one for `ζ^b`.** -/
theorem curveFundamentalClass_of_pow_eq :
    curveFundamentalClass q hn hζ = b • curveFundamentalClass q hn hζ' := by
  apply (curveConstantTrace q hn hζ').injective
  rw [map_nsmul, curveConstantTrace_curveFundamentalClass,
    curveConstantTrace_of_pow_eq q hn hζ hζ' hb, curveConstantTrace_curveFundamentalClass,
    nsmul_eq_mul, mul_one]

include hb in
/-- **`Θ_A` for `ζ` is `Θ_A` for `ζ^b` precomposed with multiplication by `b`.** -/
theorem curveConstantClass_of_pow_eq (A : Type) [AddCommGroup A] (φ : ZMod n →+ A) :
    curveConstantClass q hn hζ A φ = curveConstantClass q hn hζ' A (b • φ) := by
  change Sheaf.H.map _ 2 _ = Sheaf.H.map _ 2 _
  rw [curveFundamentalClass_of_pow_eq q hn hζ hζ' hb, map_nsmul, etaleConstantSheafMap_nsmul,
    sheafH_map_nsmul]

end Abelian

section Module

attribute [local instance] HasDerivedCategory.standard

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')

include hb in
/-- **`τ_E : H²(C, E_C) ≅ E` for `ζ^b` is `b` times `τ_E` for `ζ`.** -/
theorem curveConstantModuleTrace_of_pow_eq (E : ModuleCat.{u + 1} Λ) [Finite E]
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) :
    curveConstantModuleTrace q Λ hn hζ' E x = b • curveConstantModuleTrace q Λ hn hζ E x := by
  let Θ := AddEquiv.ofBijective (curveConstantClass q hn hζ (Shrink.{0} E))
    (bijective_curveConstantClass q hn hζ (shrink_card_nsmul_eq_zero Λ E))
  let Θ' := AddEquiv.ofBijective (curveConstantClass q hn hζ' (Shrink.{0} E))
    (bijective_curveConstantClass q hn hζ' (shrink_card_nsmul_eq_zero Λ E))
  change curveConstantModuleTraceAddEquiv q Λ hn hζ' E x =
    b • curveConstantModuleTraceAddEquiv q Λ hn hζ E x
  simp only [curveConstantModuleTraceAddEquiv, AddEquiv.trans_apply]
  generalize (sheafHAddEquivOfIso (underlyingConstantSheafIso C E Shrink.addEquiv.symm) 2)
    (etaleModuleCohomologyAddEquivSheafH C _ 2 x) = z
  obtain ⟨φ, rfl⟩ := Θ.surjective z
  have hΘ : Θ φ = Θ' (b • φ) := curveConstantClass_of_pow_eq q hn hζ hζ' hb _ φ
  have h1 : Θ.symm (Θ φ) = φ := Θ.symm_apply_apply φ
  have h2 : Θ'.symm (Θ φ) = b • φ := by rw [hΘ]; exact Θ'.symm_apply_apply _
  change Shrink.addEquiv (zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E) (Θ'.symm (Θ φ))) =
    b • Shrink.addEquiv (zmodEvalAddEquiv (shrink_card_nsmul_eq_zero Λ E) (Θ.symm (Θ φ)))
  rw [h1, h2, map_nsmul, map_nsmul]

section Boundary

variable {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

include hb in
/-- **`H²(C, j_!(E_U)) ≅ E` for `ζ^b` is `b` times the one for `ζ`.** -/
theorem curveExtensionByZeroConstantTrace_of_pow_eq (E : ModuleCat.{u + 1} Λ) [Finite E]
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q Λ hn hζ' jC hfin E x =
      b • curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E x := by
  rw [curveExtensionByZeroConstantTrace, curveExtensionByZeroConstantTrace,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact curveConstantModuleTrace_of_pow_eq q Λ hn hζ hζ' hb E _

end Boundary

end Module

section Psi

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')
  (jC : U.1 ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

include hb in
/-- **`ψ_N` for `ζ^b` is `b` times `ψ_N` for `ζ`.** -/
theorem curveRepresentationCoinvariantsMap_of_pow_eq
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)) :
    curveRepresentationCoinvariantsMap B U y q Λ hn hζ' jC hfin N =
      b • curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.smul_apply, curveRepresentationCoinvariantsMap_apply,
    curveRepresentationCoinvariantsMap_apply, curveExtensionByZeroConstantTrace_of_pow_eq q Λ hn hζ
      hζ' hb jC hfin]
  exact (congrArg (finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ _ N)
    (map_nsmul (ULift.moduleEquiv.{0} (R := Λ)
      (M := (ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))
        b _)).trans
    (map_nsmul (finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ _ N) b _)

end Psi

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section Theta

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  {ζ ζ' : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (hζ' : IsPrimitiveRoot ζ' (Fintype.card Λ)) {b : ℕ} (hb : ζ ^ b = ζ')

include hb in
/-- **`θ_ρ` for `ζ^b` is `b` times `θ_ρ` for `ζ`.** -/
theorem compactSupportGeometricCoinvariantsMap_of_pow_eq
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ' ρ =
      b • compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  rw [compactSupportGeometricCoinvariantsMap_eq, compactSupportGeometricCoinvariantsMap_eq,
    curveRepresentationCoinvariantsMap_of_pow_eq B
      (fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) y
      (geometricSmoothModel f j kbar).q Λ hn hζ hζ' hb (geometricSmoothModel f j kbar).j
      (geometricSmoothModel f j kbar).finite_compl, LinearMap.smul_comp]

omit hζ hζ' hb in
/-- **The choice-free map `H²_c(X_k̄, ℱ_ρ) ⟶ Hom(μ_n(k̄), M_π) = M_π(-1)`**,
`x ↦ (ζ^a ↦ a θ_ζ(x))`, formed with a chosen primitive `n`-th root of unity `ζ₀`. -/
def compactSupportGeometricTwistMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) →ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+
        Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ)) :=
  haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  (rootsOfUnityHomEvalEquiv (exists_isPrimitiveRoot_of_isUnit hn).choose_spec Λ
      (card_nsmul_eq_zero_of_module Λ)).symm.toLinearMap ∘ₗ
    compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn
      (exists_isPrimitiveRoot_of_isUnit hn).choose_spec ρ

omit hζ' hb in
/-- **The choice-free map does not depend on a root of unity**: at every primitive `n`-th root of
unity `ζ` it is `θ_ρ` for `ζ`. -/
theorem compactSupportGeometricTwistMap_apply_ofMul
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportGeometricTwistMap B X f kbar Λ y j hn ρ x (Additive.ofMul hζ.toRootsOfUnity) =
      compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ x := by
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have h₀ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  obtain ⟨b, -, hb⟩ := h₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [compactSupportGeometricCoinvariantsMap_of_pow_eq B X f kbar Λ y j hn h₀ hζ hb]
  exact rootsOfUnityHomEvalEquiv_symm_apply_of_pow_eq h₀ Λ (card_nsmul_eq_zero_of_module Λ) _ b _
    (by simp [hb])

end Theta

end AlgebraicGeometry

end
