module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTangentExt
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushoutModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSupportExtFiniteSiteChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.Deformation.Artin.FiniteDimensional.AlgebraicSpacePoint
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingMorphismHomotopy

/-!
# The tangent space of `Coh_{X/Y}` at a finite type point is finite-dimensional

Let `x₀ = (Spec k, g₀, 𝒢₀)` be an object of `Coh_{X/Y}` over a field `k` of finite type over a
locally Noetherian `S`, with `Y` locally of finite presentation over `S`. The base change
`X₀ = X ×_Y Spec k` is locally of finite type over `Spec k`, hence locally Noetherian, so `𝒢₀`
is coherent; its support is proper over `Spec k`, so `Hom(𝒢₀, 𝒢₀)` and `Ext¹(𝒢₀, 𝒢₀)` are
finite-dimensional (Stacks 0D0T through the change of base site of Stacks 04SG). Together with
the finite-dimensionality of the tangent space of `Y` at the image point (Stacks 07X1) this
bounds the tangent space of `𝓕_{Coh_{X/Y}, k, x₀}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_ext_one_and_hom_basePoint`.
* `AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_tangentModuleAt_cohDef_uLift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

/-- A finite-dimensional vector space `V` over a field `k` is a module over `kᵐᵒᵖ`, with `op a`
acting as `a`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The scalar action of a field `k` on a finite-dimensional vector space `V` is central: `op a`
and `a` act in the same way. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

include hx₀ in
/-- **`X₀ = X ×_Y Spec k` is locally Noetherian.** -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_basePoint :
    HasEtaleLocalProperty B S hS (D.space x₀.T).1 (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_toScheme_eq (D.space x₀.T) (D.projection x₀.T)
    x₀.properSupport.choose (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)

include hx₀ in
/-- **`𝒢₀` is coherent.** -/
theorem isCoherent_basePoint : IsCoherent B S hS (D.space x₀.T).1 (D.space x₀.T).2 x₀.F := by
  have : Fact (HasEtaleLocalProperty B S hS (D.space x₀.T).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨D.hasEtaleLocalProperty_isLocallyNoetherian_basePoint iΛ x₀ hx₀⟩
  exact (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ x₀.F).2 x₀.finitePresentation

/-- **`Ext¹(𝒢₀, 𝒢₀)` and `Hom(𝒢₀, 𝒢₀)` are finite-dimensional over `k`.** -/
theorem finiteDimensional_ext_one_and_hom_basePoint :
    letI : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2) :=
      HasExt.standard _
    letI := D.residueLinear iΛ x₀ hx₀
    FiniteDimensional k (Abelian.Ext x₀.F x₀.F 1) ∧ FiniteDimensional k (x₀.F ⟶ x₀.F) := by
  obtain ⟨hp, hU, hprop⟩ := x₀.properSupport
  exact finiteDimensional_ext_one_and_hom_of_hasProperSupport_of_toScheme_eq (D.space x₀.T)
    (D.projection x₀.T) hp (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)
    (D.residueScalars iΛ x₀ hx₀) (fun _ => rfl) x₀.F (D.isCoherent_basePoint iΛ x₀ hx₀)
    ⟨hU, hprop⟩

/-- **Stacks 08W8, the tangent space.** The tangent module of `𝓕_{Coh_{X/Y}, k, x₀}` at the
rank-one module is finite-dimensional. -/
theorem finiteDimensional_tangentModuleAt_cohDef_uLift [IsLocallyNoetherian S]
    (hlfp : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) [Module.Finite Λ k]
    (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (hfinite : AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      AlgebraicGeometry.QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (h𝓕 : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection) h𝓕
        (FGModuleCat.of k (ULift.{u} k))) := by
  obtain ⟨h𝓖, hT, -⟩ := isFiniteDimensionalDeformationCategory_algebraicSpaceStack.{u, u}
    D.Y.1 D.Y.2 hlfp iΛ hiΛ (D.toBaseElements.obj x₀) (D.baseQ_obj_toBaseElements iΛ x₀ hx₀)
    hfinite
  have : FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (D.baseDef iΛ x₀ hx₀).projection) h𝓖
        (FGModuleCat.of k (ULift.{u} k))) :=
    finiteDimensional_tangentModuleAt_of_tangentSpaceArtinian h𝓖 hT
  let : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2) :=
    HasExt.standard _
  let := D.residueLinear iΛ x₀ hx₀
  obtain ⟨h₁, -⟩ := D.finiteDimensional_ext_one_and_hom_basePoint iΛ x₀ hx₀
  have := h₁
  have := ModuleDeformation.finiteDimensional_ext_copowerObj x₀.F x₀.F
    (FGModuleCat.of k (ULift.{u} k)) 1
  exact D.finiteDimensional_tangentModuleAt_cohDef iΛ x₀ hx₀ h𝓕 h𝓖 _

end CoherentSituation

end AlgebraicGeometry.Space

end
