module

public import StacksFrontier.AlgebraicGeometry.TateMap.BaseChangeChartsPrescribed
public import StacksFrontier.AlgebraicGeometry.TateMap.Objects
public import StacksFrontier.AlgebraicGeometry.TateMap.DualizingRestriction
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.RingTheory.TateMap.DualizingBaseChange
public import StacksFrontier.AlgebraicGeometry.TateMap.PullbackCharts

/-!
# The pullback comparison of the relative dualizing module

For a morphism `b/a : Y'/X' → Y/X` of the category of Stacks, Section 0FKB, the canonical
isomorphism `b^* ω_{Y/X} ≅ ω_{Y'/X'}` is the one which, on compatible affine charts on which the
square is a chart base change `D`, is the base-change isomorphism `B' ⊗_B ω_{B/A} ≅ ω_{B'/A'}` of
Tag 0BVB.

## Main definitions

* `AlgebraicGeometry.TateMap.omegaChartPullbackEquiv`: on one chart quadruple, the identification
  of the sections of `b^* ω_{Y/X}` with those of `ω_{Y'/X'}` through the base change of the
  affine dualizing modules.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings
open Stacks.Discriminant Stacks.TateMap

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} (hf : IsQuasiFiniteSyntomic f)
  (hf' : IsQuasiFiniteSyntomic f') (sq : OpenBaseChangeSquare f f') [IsLocallyNoetherian X]
  [IsLocallyNoetherian X']

/-- The relative dualizing module `ω_{Y/X}` of a quasi-finite syntomic morphism `f : Y → X` with
`X` locally Noetherian is quasi-coherent. -/
instance omega_isQuasicoherent : (omega f hf).IsQuasicoherent :=
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  (omegaData f hf).isQuasicoherent

section Chart

variable (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
  (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
  (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1)

/-- **The comparison on one chart quadruple.** On affine opens `U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`,
`V' ⊆ Y'` compatible with the four maps and a chart base change `D` between their coordinate
rings, the sections of `b^* ω_{Y/X}` over `V'` are identified with those of `ω_{Y'/X'}`: the
sections of the pullback are `Γ(V') ⊗_{Γ(V)} Γ(ω, V)`, and the base change of the affine
dualizing modules carries this to `ω_{Γ(V')/Γ(U')}`. -/
def omegaChartPullbackEquiv :
    letI := isLocallyNoetherian_source f hf
    letI := isLocallyNoetherian_source f' hf'
    letI := hf.1
    letI := hf'.1
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    haveI : Flat f := AlgebraicGeometry.flat hf.2
    haveI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    ∀ (_ : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1)),
      Γ((Scheme.Modules.pullback sq.cover).obj (omega f hf), V'.1) ≃ₗ[Γ(Y', V'.1)]
        Γ(omega f' hf', V'.1) := fun D F G ↦
  letI := isLocallyNoetherian_source f hf
  letI := isLocallyNoetherian_source f' hf'
  letI := hf.1
  letI := hf'.1
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  haveI : Flat f := AlgebraicGeometry.flat hf.2
  haveI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  (pullbackSectionsTensorEquiv sq.cover (omega f hf) V V' hV'V).symm
    ≪≫ₗ ((omegaData f hf).localEquiv U V hVU F).baseChange Γ(Y, V.1) Γ(Y', V'.1) _ _
    ≪≫ₗ omegaBaseChange D F G ≪≫ₗ ((omegaData f' hf').localEquiv U' V' hV'U' G).symm

/-- **The comparison on a chart quadruple, on pulled-back sections.** The comparison carries the
pullback of a section `t` of `ω_{Y/X}` over `V` to the section of `ω_{Y'/X'}` whose affine
dualizing module image is the base change of that of `t`. -/
theorem omegaChartPullbackEquiv_pullbackSection :
    letI := isLocallyNoetherian_source f hf
    letI := isLocallyNoetherian_source f' hf'
    letI := hf.1
    letI := hf'.1
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
    haveI : Flat f := AlgebraicGeometry.flat hf.2
    haveI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    ∀ (D : ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X', U'.1) Γ(Y', V'.1)) (t : Γ(omega f hf, V.1)),
      (omegaData f' hf').localEquiv U' V' hV'U' G
          (omegaChartPullbackEquiv hf hf' sq U V U' V' hVU hU'U hV'U' hV'V D F G
            (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t)) =
        omegaBaseChange D F G (1 ⊗ₜ (omegaData f hf).localEquiv U V hVU F t) := by
  intro D F G t
  let := isLocallyNoetherian_source f hf
  let := isLocallyNoetherian_source f' hf'
  let := hf.1
  let := hf'.1
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  have : Flat f := AlgebraicGeometry.flat hf.2
  have : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  show (omegaData f' hf').localEquiv U' V' hV'U' G (((omegaData f' hf').localEquiv U' V' hV'U'
    G).symm (omegaBaseChange D F G (LinearEquiv.baseChange Γ(Y, V.1) Γ(Y', V'.1) _ _
      ((omegaData f hf).localEquiv U V hVU F)
        ((pullbackSectionsTensorEquiv sq.cover (omega f hf) V V' hV'V).symm
          (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t))))) = _
  have h1 : (pullbackSectionsTensorEquiv sq.cover (omega f hf) V V' hV'V).symm
      (Scheme.Modules.pullbackSection sq.cover (omega f hf) V.1 V'.1 hV'V t) =
      (1 : Γ(Y', V'.1)) ⊗ₜ t :=
    (LinearEquiv.symm_apply_eq _).mpr
      (pullbackSectionsTensorEquiv_one_tmul sq.cover (omega f hf) V V' hV'V t).symm
  rw [LinearEquiv.apply_symm_apply, h1, LinearEquiv.baseChange_tmul]

end Chart

end AlgebraicGeometry.TateMap
