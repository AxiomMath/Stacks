module

public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology

/-!
# `H²_c(X_k̄, ℱ_ρ)` and the geometric coinvariants: the map `θ`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k`, `Λ` a finite ring with `n = #Λ` invertible in `k̄` and `ζ ∈ k̄` a primitive `n`-th root of
unity. For a finite `Λ`-module `M` with a continuous action `ρ` of `π₁(X, η̄)` this file
constructs the map of Tag 03VK

`θ_ρ : H²_c(X_k̄, ℱ_ρ) ⟶ M_{π₁(X_k̄, η̄)}`,

the coinvariants of the geometric fundamental group, natural in `ρ`. Here `ℱ_ρ` restricted to
`U = X_k̄` is `ℱ` of the restriction of `ρ` to `π₁(U, η̄)`, the quotient `M ⟶ M_{π₁(U, η̄)}` onto
the largest quotient with trivial action gives the largest constant quotient
`ℱ_ρ|_U ⟶ (M_{π₁(U, η̄)})_U`, and `H²` of a constant sheaf on `U` is its value
(`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`), computed on the smooth projective
model `C` of `U` (`Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso`).

## Main definitions

* `Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap` — `ψ_N : H²(C, j_!ℱ_N) ⟶ N_π` on
  a connected curve with smooth projective model `C`, for a representation `N` of its
  fundamental group.
* `AlgebraicGeometry.geometricRepresentation` — the restriction of `ρ` to `π₁(X_k̄, η̄)`, as a
  representation.
* `AlgebraicGeometry.compactSupportGeometricCoinvariantsMap` — `θ_ρ`.

## Main results

* `Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap_naturality` and
  `Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap_comp`.
* `AlgebraicGeometry.compactSupportGeometricCoinvariantsMap_eq` — `θ` as a composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- **Three commutative squares of linear maps compose.** -/
theorem linearMap_comp_three_squares {R : Type*} [Ring R] {A A' B B' C C' E E' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B'] [AddCommGroup C]
    [AddCommGroup C'] [AddCommGroup E] [AddCommGroup E'] [Module R A] [Module R A'] [Module R B]
    [Module R B'] [Module R C] [Module R C'] [Module R E] [Module R E']
    {S : A →ₗ[R] B} {S' : A' →ₗ[R] B'} {h₀ : A →ₗ[R] A'} {h₁ : B →ₗ[R] B'} {P : B →ₗ[R] C}
    {P' : B' →ₗ[R] C'} {h₂ : C →ₗ[R] C'} {ψ : C →ₗ[R] E} {ψ' : C' →ₗ[R] E'} {h₃ : E →ₗ[R] E'}
    (hS : S' ∘ₗ h₀ = h₁ ∘ₗ S) (hP : P' ∘ₗ h₁ = h₂ ∘ₗ P) (hψ : ψ' ∘ₗ h₂ = h₃ ∘ₗ ψ) :
    (ψ' ∘ₗ P' ∘ₗ S') ∘ₗ h₀ = h₃ ∘ₗ ψ ∘ₗ P ∘ₗ S := by
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hS, ← LinearMap.comp_assoc S h₁ P', hP,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc _ h₂ ψ', hψ, LinearMap.comp_assoc]

/-- The category of étale sheaves of `Λ`-modules, for `Λ : Type`, has enough injectives. -/
local instance etaleModulesEnoughInjectivesZero' (Λ : Type) [Ring Λ] (Y : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- `ULift.moduleEquiv` intertwines `ModuleCat.uliftFunctor.map φ` with `φ`. -/
lemma ulift_moduleEquiv_uliftFunctor_map (Λ : Type) [Ring Λ] {E E' : ModuleCat.{u + 1} Λ}
    (φ : E ⟶ E') (w : (ModuleCat.uliftFunctor.{0, u + 1} Λ).obj E) :
    ULift.moduleEquiv.{0} (R := Λ) (ConcreteCategory.hom ((ModuleCat.uliftFunctor.{0, u + 1} Λ).map
        φ) w) =
      ConcreteCategory.hom φ (ULift.moduleEquiv.{0} (R := Λ) w) := rfl

section Psi

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (jC : U.1 ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

omit [Fintype Λ] in
/-- The universe lift of the coinvariants `N_π` of a finite `Λ`-module `N` is finite. -/
instance finite_ulift_coinvariants [Finite Λ]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)) :
    Finite ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj
      ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _ N))) := by
  have : Module.Finite Λ ((ModuleCat.isFG Λ).ι.obj
      (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)) :=
    (finiteTypeContinuousModuleCoinvariantsModule Λ _ N).property
  have : Finite ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)) :=
    Module.finite_of_finite Λ
  exact Finite.of_equiv _ Equiv.ulift.symm

/-- **`ψ_N : H²(C, j_! ℱ_N) ⟶ N_π`** for a finite `Λ`-module `N` with continuous action of
`π = π₁(U, y)`: `H²` of the largest constant quotient `ℱ_N ⟶ (N_π)_U`, followed by
`H²(C, j_!(N_π)_U) ≅ N_π`. -/
def curveRepresentationCoinvariantsMap
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)) :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((representationSheaf B U y Λ).obj N)) →ₗ[Λ]
      Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ _ N) :=
  (finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ _ N).toLinearMap ∘ₗ
    (ULift.moduleEquiv.{0} (R := Λ)
      (M := (ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _
          N))).toLinearMap ∘ₗ
    (curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin
      ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj
        ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _
            N)))).toLinearMap ∘ₗ
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        ((representationSheaf B U y Λ).map (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
            (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))).hom

/-- `curveRepresentationCoinvariantsMap` evaluated at a class `x`, as the composite of its
factors applied to `x`. -/
lemma curveRepresentationCoinvariantsMap_apply
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y))
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((representationSheaf B U y Λ).obj N))) :
    curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N x =
      finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ _ N (ULift.moduleEquiv.{0} (R := Λ)
        (M := (ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _ N))
        (curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin
        ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj
          ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
            ((representationSheaf B U y Λ).map (finiteTypeContinuousModuleCoinvariantsQuotient Λ _
                N) ≫
              (representationSheafTrivialIsoConstant B U y Λ).hom.app
                (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))).hom x))) := rfl

/-- **`ψ` is natural in the representation.** -/
theorem curveRepresentationCoinvariantsMap_naturality
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)}
    (v : N ⟶ N')
    (x : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj ((representationSheaf B U y Λ).obj N))) :
    curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N'
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((representationSheaf B U y Λ).map v))).hom
          x) =
      finiteTypeContinuousModuleCoinvariantsMap Λ _ v
        (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N x) := by
  let c : finiteTypeContinuousModuleCoinvariantsModule Λ _ N ⟶
      finiteTypeContinuousModuleCoinvariantsModule Λ _ N' :=
    ObjectProperty.homMk (ModuleCat.ofHom (finiteTypeContinuousModuleCoinvariantsMap Λ _ v))
  have hq := congrArg (representationSheaf B U y Λ).map
      (finiteTypeContinuousModuleCoinvariantsQuotient_naturality Λ _ v)
  have he := (representationSheafTrivialIsoConstant B U y Λ).hom.naturality c
  have key : (representationSheaf B U y Λ).map v ≫ (representationSheaf B U y Λ).map
      (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N') ≫
        (representationSheafTrivialIsoConstant B U y Λ).hom.app
            (finiteTypeContinuousModuleCoinvariantsModule Λ _ N') =
      ((representationSheaf B U y Λ).map (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
        (representationSheafTrivialIsoConstant B U y Λ).hom.app
            (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)) ≫
        (constantSheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          ((ModuleCat.uliftFunctor.{0, u + 1} Λ).map ((ModuleCat.isFG Λ).ι.map c)) := by
    rw [← Category.assoc, ← (representationSheaf B U y Λ).map_comp, hq, (representationSheaf B U y
        Λ).map_comp, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) he
  have hm : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((representationSheaf B U y Λ).map v)) ≫
      ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        ((representationSheaf B U y Λ).map (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N') ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
              (finiteTypeContinuousModuleCoinvariantsModule Λ _ N'))) =
      ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((representationSheaf B U y Λ).map
          (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
              (finiteTypeContinuousModuleCoinvariantsModule Λ _ N))) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((constantSheaf U.1.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).map
          ((ModuleCat.uliftFunctor.{0, u + 1} Λ).map ((ModuleCat.isFG Λ).ι.map c)))) := by
    simp only [← Functor.map_comp, key]
  have h1 := congrArg (fun φ => φ.hom x) hm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  have hτ := curveExtensionByZeroConstantTrace_naturality q Λ hn hζ jC hfin
    ((ModuleCat.uliftFunctor.{0, u + 1} Λ).map ((ModuleCat.isFG Λ).ι.map c))
    ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((representationSheaf B U y Λ).map
        (finiteTypeContinuousModuleCoinvariantsQuotient Λ _ N) ≫
          (representationSheafTrivialIsoConstant B U y Λ).hom.app
              (finiteTypeContinuousModuleCoinvariantsModule Λ _ N)))).hom x)
  rw [curveRepresentationCoinvariantsMap_apply, curveRepresentationCoinvariantsMap_apply, h1, hτ,
    ulift_moduleEquiv_uliftFunctor_map]
  exact finiteTypeContinuousModuleCoinvariantsModuleEquiv_naturality Λ _ v _

/-- **`ψ` is natural in the representation**, as an equation of linear maps. -/
theorem curveRepresentationCoinvariantsMap_comp
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)}
    (v : N ⟶ N') :
    curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N' ∘ₗ
        (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map ((representationSheaf B U y Λ).map v))).hom
              =
      finiteTypeContinuousModuleCoinvariantsMap Λ _ v ∘ₗ
        curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N :=
  LinearMap.ext (curveRepresentationCoinvariantsMap_naturality B U y q Λ hn hζ jC hfin v)

end Psi

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section Theta

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **The restriction of `ρ` to the geometric fundamental group, as a representation**: `M` with
the action of `π₁(X_k̄, η̄)` through `π₁(X_k̄, η̄) ⟶ π₁(X, η̄)`. -/
abbrev geometricRepresentation
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Representation Λ (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)
      ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
        (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
          y)).obj ρ).obj.obj.obj.V :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleRepresentation Λ _
    ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y)).obj ρ)

/-- **`ℱ_ρ|_{X_k̄} ≅ ℱ_{ρ|}`** (Tag 0DV6), with the projection `X_k̄ ⟶ X` written as
`pullback.fst f (specAlgebraMap k k̄)`. -/
def representationSheafFieldBaseChangeIso :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ ⋙
        etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar)) ≅
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
            y) ⋙
        representationSheaf B (fieldBaseChangeObj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)) y Λ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  representationSheafPullbackIso B (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)) Λ y

variable (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))
  {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))

/-- **The map `θ_ρ : H²_c(X_k̄, ℱ_ρ) ⟶ M_{π₁(X_k̄, η̄)}` of Tag 03VK.** `H²_c` is that of Remark
03UI (2) for the compactification `j`; on the smooth projective model `C` of `X_k̄` it is
`H²(C, j_{C!}(ℱ_ρ|_{X_k̄}))`, `ℱ_ρ|_{X_k̄}` is `ℱ` of the restriction of `ρ` (Tag 0DV6), and
`Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap` maps it onto the coinvariants
through the largest constant quotient. -/
def compactSupportGeometricCoinvariantsMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) →ₗ[Λ]
      Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  curveRepresentationCoinvariantsMap B
      (fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) y
      (geometricSmoothModel f j kbar).q Λ hn hζ (geometricSmoothModel f j kbar).j
      (geometricSmoothModel f j kbar).finite_compl
      ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
        (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
          y)).obj ρ) ∘ₗ
    (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
        ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((representationSheafFieldBaseChangeIso B X f kbar Λ y).hom.app ρ))).hom ∘ₗ
    (galoisCompactSupportSmoothModelIso f j kbar Λ
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)
      ((2 : ℕ) : ℤ)).hom.hom

/-- `θ_ρ` is the composite of `galoisCompactSupportSmoothModelIso`, the map induced by
`representationSheafFieldBaseChangeIso` and `curveRepresentationCoinvariantsMap`. -/
lemma compactSupportGeometricCoinvariantsMap_eq
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ =
      letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      curveRepresentationCoinvariantsMap B
        (fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) y
        (geometricSmoothModel f j kbar).q Λ hn hζ (geometricSmoothModel f j kbar).j
        (geometricSmoothModel f j kbar).finite_compl
        ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
            y)).obj ρ) ∘ₗ
      (((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
          ((representationSheafFieldBaseChangeIso B X f kbar Λ y).hom.app ρ))).hom ∘ₗ
      (galoisCompactSupportSmoothModelIso f j kbar Λ
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)
        ((2 : ℕ) : ℤ)).hom.hom := rfl

/-- **The map on geometric coinvariants induced by a morphism of representations.** -/
abbrev geometricCoinvariantsMap
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ') :
    Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ) →ₗ[Λ]
      Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ') :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleCoinvariantsMap Λ _
    ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y)).map v)

/-- **`θ` is natural in `ρ`**: for a morphism `v : ρ ⟶ ρ'` of representations, `θ_{ρ'}` composed
with `H²_c(X_k̄, ℱ_v)` is the induced map on coinvariants composed with `θ_ρ`. -/
theorem compactSupportGeometricCoinvariantsMap_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ') :
    letI := connectedSpace_of_isCurve B X f
    compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ' ∘ₗ
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map v)))).hom =
      geometricCoinvariantsMap B X f kbar Λ y v ∘ₗ
        compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hS := congrArg ModuleCat.Hom.hom
    (galoisCompactSupportSmoothModelIso_hom_naturality f j kbar Λ
      ((representationSheaf B X _ Λ).map v) ((2 : ℕ) : ℤ))
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hS
  have hP := congrArg (fun φ => ((((etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map φ)).hom))
    ((representationSheafFieldBaseChangeIso B X f kbar Λ y).hom.naturality v)
  simp only [Functor.comp_map, Functor.map_comp, ModuleCat.hom_comp] at hP
  have hψ := curveRepresentationCoinvariantsMap_comp B
    (fieldBaseChangeObj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)) y
    (geometricSmoothModel f j kbar).q Λ hn hζ (geometricSmoothModel f j kbar).j
    (geometricSmoothModel f j kbar).finite_compl
    ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
        y)).map v)
  rw [compactSupportGeometricCoinvariantsMap_eq, compactSupportGeometricCoinvariantsMap_eq]
  exact linearMap_comp_three_squares hS hP hψ

end Theta

end AlgebraicGeometry

end
