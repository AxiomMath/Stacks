module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareComplex
public import StacksFrontier.RingTheory.DeRham.PolynomialAlgEquivQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of forms of a square over the identity, read on affine opens

Let `f : X' ⟶ X` be a morphism of schemes over a scheme `S`, with structure morphisms
`p : X ⟶ S` and `p' : X' ⟶ S`. For affine opens `U ⊆ X`, `V ⊆ S` with `U ≤ p⁻¹V` and `f⁻¹U`
affine, the canonical map `Ω^n_{X/S} ⟶ f_*Ω^n_{X'/S}` of Tag 07HX, read on sections over `U`
through the affine-open comparisons of the forms at `U` and at `f⁻¹U` with Kähler forms, is the
restriction of forms `⋀^n Ω_{A/R} ⟶ ⋀^n Ω_{A'/R}` along `A = Γ(X, U) → A' = Γ(X', f⁻¹U)`, for
`R = Γ(S, V)`.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_deRhamFormsPushforwardHom`:
  **the canonical map of forms of a square over the identity is, on affine opens, the ring-level
  restriction of forms.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham


variable {X' X S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S)
  {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hV : IsAffineOpen V)
  (e : U ≤ p ⁻¹ᵁ V) (e' : f ⁻¹ᵁ U ≤ p' ⁻¹ᵁ V) (hcomm : f ≫ p = p' ≫ 𝟙 S)

include hcomm in
/-- The ring maps `Γ(S, V) ⟶ Γ(X, U) ⟶ Γ(X', f⁻¹U)` compose to the structure map of `X'`. -/
theorem appLE_comp_app_eq_appLE :
    p.appLE V U e ≫ f.app U = p'.appLE V (f ⁻¹ᵁ U) e' := by
  obtain rfl : p' = f ≫ p := by simpa using hcomm.symm
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

include hU hU' hV hcomm in
/-- **The canonical map of forms of a square over the identity, read on affine opens, is the
restriction of Kähler forms** along `Γ(X, U) ⟶ Γ(X', f⁻¹U)`. -/
theorem formsSectionsIso_deRhamFormsPushforwardHom (n : ℕ) :
    letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U e).hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(X', f ⁻¹ᵁ U) := (p'.appLE V (f ⁻¹ᵁ U) e').hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(X', f ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (ConcreteCategory.congr_hom (appLE_comp_app_eq_appLE f p p' e e' hcomm) r).symm
    ∀ x : ⋀[Γ(X, U)]^n (Ω[Γ(X, U)⁄Γ(S, V)]),
      (formsSectionsIso p' hU' hV e' n).hom
          (((Scheme.Hom.deRhamFormsPushforwardHom f p p' (𝟙 S) hcomm).app (n : ℤ)).val.app
            (op U) ((formsSectionsIso p hU hV e n).inv x)) =
        KaehlerDifferential.mapExteriorPower Γ(S, V) Γ(X, U) Γ(X', f ⁻¹ᵁ U) n x := by
  let : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U e).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', f ⁻¹ᵁ U) := (p'.appLE V (f ⁻¹ᵁ U) e').hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(X', f ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (ConcreteCategory.congr_hom (appLE_comp_app_eq_appLE f p p' e e' hcomm) r).symm
  intro x
  have key : ringDeRhamAbSquareMap f p p' (𝟙 S) hU hU' hV hV e e' hcomm =
      ((forget₂ (ModuleCat.{u} Γ(S, V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (KaehlerDifferential.deRhamComplexMap Γ(S, V) Γ(X, U) Γ(X', f ⁻¹ᵁ U)) := by
    ext n : 1
    refine ringDeRhamAb_hom_ext p e n fun b => ?_
    rw [ringDeRhamAbSquareMap_f_smul_ιMulti_d]
    exact (KaehlerDifferential.mapExteriorPower_smul_ιMulti_D Γ(S, V) Γ(X, U)
      Γ(X', f ⁻¹ᵁ U) n b).symm
  have h2 := congrArg (fun φ : ringDeRhamAbComplex p e ⟶ ringDeRhamAbComplex p' e' =>
    (HomologicalComplex.Hom.f φ n).hom x) key
  refine (ringDeRhamAbSquareMap_f_apply f p p' (𝟙 S) hU hU' hV hV e e' hcomm n x).symm.trans
    (h2.trans ?_)
  rfl

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
