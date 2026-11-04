module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrProjMap
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesComap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesFibreProduct

/-!
# The isomorphism of relative homogeneous spectra induced by an isomorphism of algebras

Let `Φ : 𝒜₁ ⟶ 𝒜₂` be a unital homomorphism of quasi-coherent graded algebras on a scheme `Y`
which is an isomorphism in every degree, and `Proj_Y(𝒜₁) ≅ Proj_Y(𝒜₂)` the isomorphism of
relative homogeneous spectra it induces.  On points it transports a quadruple along `Φ⁻¹`; this
file reads off three consequences.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr_inv_toBase`: the inverse of
  the induced isomorphism lies over `Y`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr_comp_hom`: the isomorphism
  induced by a composite is the composite of the induced isomorphisms.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseChangeHom_comp_relativeProjCongr_hom`: the
  induced isomorphisms commute with the base-change morphisms of Tag 01O3.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- The inverse of the induced isomorphism lies over `Y`. -/
theorem relativeProjCongr_inv_toBase :
    (relativeProjCongr Φ hΦ).inv ≫ (relativeProj A₁).toBase = (relativeProj A₂).toBase := by
  rw [Iso.inv_comp_eq, relativeProjCongr_hom_comp_toBase]

/-- Two morphisms into `Proj_Y(𝒜)` agree as soon as the points they represent agree at every
quasi-compact test scheme. -/
theorem relativeProj_hom_ext {A : SheafGradedAlgebra Y} {T : Scheme.{u}}
    {k₁ k₂ : T ⟶ (relativeProj A).scheme}
    (h : ∀ (W : Scheme.{u}) (hW : CompactSpace W) (w : W ⟶ T),
      ((relativeProjRepresentableByFunctorUnconditional A).homEquiv k₁).val W hW w =
        ((relativeProjRepresentableByFunctorUnconditional A).homEquiv k₂).val W hW w) :
    k₁ = k₂ :=
  (relativeProjRepresentableByFunctorUnconditional A).homEquiv.injective
    (Scheme.QcExtension.ext (funext fun W => funext fun hW => funext fun w => h W hW w))

section Comp

variable {A₃ : SheafGradedAlgebra Y}
  (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₂) (situationAlgebra A₃))
  (hΨ : ∀ n : ℤ, IsIso (Ψ.app n)) (hΦΨ : ∀ n : ℤ, IsIso ((Φ.comp Ψ).app n))

/-- **The isomorphism induced by a composite is the composite of the induced isomorphisms.** -/
theorem relativeProjCongr_comp_hom :
    (relativeProjCongr (Φ.comp Ψ) hΦΨ).hom =
      (relativeProjCongr Φ hΦ).hom ≫ (relativeProjCongr Ψ hΨ).hom := by
  refine relativeProj_hom_ext fun W hW w => ?_
  have e1 := homEquiv_comp_relativeProjCongr_val (Φ.comp Ψ) hΦΨ (𝟙 _) W hW w
  have e2 := homEquiv_comp_relativeProjCongr_val Ψ hΨ (relativeProjCongr Φ hΦ).hom W hW w
  have e3 := homEquiv_comp_relativeProjCongr_val Φ hΦ (𝟙 _) W hW w
  rw [Category.id_comp] at e1 e3
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [e3]
  refine Eq.trans ?_ (F.algebraTransport_algebraTransport _ _ _ _ (fun n => by
    rw [SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
    have := isIso_unitalHomInverse_app Ψ hΨ n
    have := isIso_unitalHomInverse_app Φ hΦ n
    infer_instance) _).symm
  refine F.algebraTransport_congr ?_ _ _ _
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  have := hΦ n
  have := hΨ n
  simp only [unitalHomInverse_app, SheafOfModules.GradedAlgebra.UnitalHom.comp_app,
    IsIso.inv_comp]

end Comp

section BaseChange

variable {S S' : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra S} (g : S' ⟶ S)
  (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΨ : ∀ n : ℤ, IsIso (Ψ.app n))

/-- **The induced isomorphisms commute with the base-change morphisms of Tag 01O3**: base
changing and then transporting along `Ψ` is transporting along `g^*Ψ` and then base changing. -/
theorem baseChangeHom_comp_relativeProjCongr_hom :
    RelativeProjBaseChangeTwist.baseChangeHom A₁ g ≫ (relativeProjCongr Ψ hΨ).hom =
      (relativeProjCongr (A₁ := A₁.pullback g) (A₂ := A₂.pullback g) (baseAlgebraMapHom g Ψ)
          (fun n => by have := hΨ n; exact isIso_baseAlgebraMapHom_app g Ψ n)).hom ≫
        RelativeProjBaseChangeTwist.baseChangeHom A₂ g := by
  have hΨ' : ∀ n : ℤ, IsIso ((baseAlgebraMapHom g Ψ).app n) := fun n => by
    have := hΨ n; exact isIso_baseAlgebraMapHom_app g Ψ n
  refine relativeProj_hom_ext fun W hW w => ?_
  have e1 := homEquiv_comp_relativeProjCongr_val Ψ hΨ
    (RelativeProjBaseChangeTwist.baseChangeHom A₁ g) W hW w
  have e2 := homEquiv_comp_baseChangeHom_val A₁ g (𝟙 _) W hW w
  have e3 := homEquiv_comp_baseChangeHom_val A₂ g
    (relativeProjCongr _ hΨ').hom W hW w
  have e4 := homEquiv_comp_relativeProjCongr_val (A₁ := A₁.pullback g) (A₂ := A₂.pullback g)
    (baseAlgebraMapHom g Ψ) hΨ' (𝟙 _) W hW w
  rw [Category.id_comp] at e2 e4
  refine e1.trans (Eq.trans ?_ e3.symm)
  rw [e2, e4]
  refine Eq.trans (F.baseChangeUp_algebraTransport g (unitalHomInverse Ψ hΨ)
    (isIso_unitalHomInverse_app Ψ hΨ) _).symm ?_
  refine congrArg (F.baseChangeUp g (situationAlgebra A₂)) (F.algebraTransport_congr ?_ _ _ _)
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  have := hΨ n
  simp only [unitalHomInverse_app, baseAlgebraMapHom_app, Functor.map_inv]
  rfl

end BaseChange

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
