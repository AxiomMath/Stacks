module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SymmetricSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineCartesianAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.RingTheory.SymmetricAlgebra.BaseChangeBijective
public import StacksFrontier.RingTheory.SymmetricAlgebra.FinitePresentation

/-!
# The symmetric algebra of a quasi-coherent module on an algebraic space, over affine charts

Let `G` be a quasi-coherent module on an algebraic space `X`, and `Sym(G)` the algebra sheaf of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.SymmetricSectionsAlgebra`, the sheafification of
`U ↦ Sym_{𝒪(U)}(G(U))`.  This file proves:

* over every affine étale chart `U` the sheafification unit `Sym_{𝒪(U)}(G(U)) ⟶ Sym(G)(U)` is an
  isomorphism;
* `Sym(G)` is a quasi-coherent algebra;
* if `G` is moreover of finite presentation, `Sym(G)` is of finite presentation.

The source of all three is that `U ↦ Sym_{𝒪(U)}(G(U))` is cartesian on the affine charts: a
morphism `V ⟶ U` of affine charts identifies `G(V)` with `𝒪(V) ⊗_{𝒪(U)} G(U)` (Descent,
Proposition 03DX (2)), and the symmetric algebra commutes with base change
(`SymmetricAlgebra.bijective_of_bijective_baseChange`).  A cartesian presheaf of modules on the
affine étale site is a sheaf there (flat descent), and sheafification on the small étale site does
not change sections over affine charts when the restriction to them is a sheaf.

## Main results

* `AlgebraicGeometry.Space.SymSections.bijective_unit_app`: the unit is bijective over affine
  charts.
* `AlgebraicGeometry.Space.SymSections.isQuasicoherent_algebra`: `Sym(G)` is quasi-coherent.
* `AlgebraicGeometry.Space.SymSections.isFinitePresentation_algebra`: `Sym(G)` is of finite
  presentation when `G` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Stacks.PresheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace SymSections

variable (G : Modules.{u, u} B S hS F hF)

/-- **The symmetric algebra presheaf is cartesian on affine charts**, in the elementwise form: an
additive map `𝒪(V) ⊗_{𝒪(U)} Sym(G(U)) ⟶ Sym(G(V))` sending `b ⊗ s` to `b · s|_V` is bijective,
for a morphism `V ⟶ U` of affine étale charts and `G` cartesian on affine charts. -/
theorem bijective_baseChange_presheaf (hG : IsCartesianOnAffineCharts G)
    {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U)
    (Ψ : letI := ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).map f.op).hom.toAlgebra
      (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op V)
        ⊗[(structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U)]
        SymmetricAlgebra ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U))
          ((val' G).obj (op U)) →+
      SymmetricAlgebra ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((val' G).obj (op V)))
    (hΨ : letI :=
        ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).map f.op).hom.toAlgebra
      ∀ (b : (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op V))
        (s : SymmetricAlgebra
          ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U))
          ((val' G).obj (op U))),
        Ψ (b ⊗ₜ s) = (PresheafOfModules.toSymAlg (val' G)).app (op V) b * (presheaf G).map f.op s) :
    Function.Bijective Ψ :=
  SymmetricAlgebra.bijective_of_bijective_baseChange _ ((val' G).restrictₛₗ f.op)
    ⟨(sectionsBaseChange G f).toAddMonoidHom, fun b m => chartBaseChange_tmul G f b m,
      hG U V hU hV f⟩ Ψ hΨ

/-- **The symmetric algebra presheaf is cartesian on affine charts.** -/
theorem isAffineCartesian (hG : IsCartesianOnAffineCharts G) :
    AffineCartesian.IsAffineCartesian (presheaf G) (PresheafOfModules.toSymAlg (val' G)) :=
  fun _ _ hU hV f => bijective_baseChange_presheaf G hG hU hV f
    (restrictionBaseChange.{u + 1, u, u, u}
      (AffineCartesian.sectionsModule (presheaf G) (PresheafOfModules.toSymAlg (val' G)))
        f.op).hom.toAddMonoidHom
    (fun b s => restrictionBaseChange_tmul.{u + 1, u, u, u}
      (AffineCartesian.sectionsModule (presheaf G) (PresheafOfModules.toSymAlg (val' G))) f.op b s)

/-- The algebra sheaf `Sym(G)` is, by definition, the sheafified algebra `AffineCartesian.algebra`
of the presheaf of algebras `U ↦ Sym_{𝒪(U)}(G(U))`. -/
theorem algebra_eq :
    algebra G = AffineCartesian.algebra (presheaf G) (PresheafOfModules.toSymAlg (val' G)) hF :=
  rfl

/-- **Over an affine étale chart the sheafification unit `Sym_{𝒪(U)}(G(U)) ⟶ Sym(G)(U)` is an
isomorphism.** -/
theorem bijective_unit_app (hG : IsCartesianOnAffineCharts G) (U : SmallEtale B S hS F)
    (hU : IsAffine (smallEtaleScheme B S hS F U)) : Function.Bijective ((unit G).app (op U)) :=
  AffineCartesian.bijective_toSheafify_app hF (isAffineCartesian G hG) U hU

/-- **`Sym(G)` is quasi-coherent** for `G` quasi-coherent. -/
theorem isQuasicoherent_algebra (hG : G.IsQuasicoherentOnSite) : (algebra G).IsQuasicoherent :=
  AffineCartesian.isQuasicoherent_algebra hF
    (isAffineCartesian G (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG))

/-- **`Sym(G)` is of finite presentation** for `G` quasi-coherent of finite presentation: over an
affine chart its structure map is that of the symmetric algebra of a finitely presented module,
followed by an isomorphism. -/
theorem isFinitePresentation_algebra (hG : G.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) : (algebra G).IsFinitePresentation := by
  intro U hU
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG
  have hb := bijective_unit_app G hcart U hU
  have hM : Module.FinitePresentation
      ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U))
      ((val' G).obj (op U)) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp U hU
  have h1 : (algebraMap ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U))
      (SymmetricAlgebra ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj (op U))
        ((val' G).obj (op U)))).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Stacks.SymAlg.finitePresentation _ _)
  have h2 : ((unit G).app (op U)).hom.FinitePresentation :=
    RingHom.FinitePresentation.of_surjective _ hb.2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hb.1]; exact Submodule.fg_bot)
  exact h2.comp h1

end SymSections

end AlgebraicGeometry.Space

end
