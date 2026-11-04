module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The direct-image functor into the quasi-coherent algebras

Let `X` be an algebraic space over a scheme `S` of a big fppf site. For an affine morphism
`f : Y ⟶ X` of algebraic spaces the direct image `f_* 𝒪_Y` is a quasi-coherent sheaf of
commutative `𝒪_X`-algebras, so the functor `f ↦ f_* 𝒪_Y` of
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` takes values in the quasi-coherent
algebras.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor`: the contravariant functor
  `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to
  `AlgebraicGeometry.Space.QuasicoherentAlgebra X`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor_comp_ι`: composed with the
  inclusion of the quasi-coherent algebras it is
  `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Functor

variable (X : AlgebraicSpaces B S hS)

/-- The contravariant functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the
quasi-coherent sheaves of commutative `𝒪_X`-algebras. -/
noncomputable def quasicoherentPushforwardAlgebraFunctor :
    (AffineOver B S hS X)ᵒᵖ ⥤ QuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift
    (AlgebraSheaf.IsQuasicoherent : ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2))
    (affinePushforwardAlgebraFunctor B S hS X)
    fun Y => by
      obtain ⟨⟨Z, hZ⟩⟩ := Y
      change (pushforwardAlgebra B S hS Z).IsQuasicoherent
      have heq : (pushforwardAlgebra B S hS Z).underlyingModule =
          (modulePushforward B S hS Z.hom).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Z.left)) :=
        congrArg
          (fun G : Modules.{u, u} B S hS Z.left.1 Z.left.2 ⥤ Modules.{u, u} B S hS X.1 X.2 =>
            G.obj (SheafOfModules.unit (structureRingSheaf B S hS Z.left)))
          (pushforwardModules_eq_modulePushforward B S hS Z.hom)
      rw [AlgebraSheaf.IsQuasicoherent, heq]
      exact isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS Z.hom
        (isQuasiCompact_of_isAffineHom' B S hS Z.hom.hom Z.left.2 X.2 hZ)
        (isQuasiSeparated_of_isAffineHom B S hS Z.hom.hom Z.left.2 X.2 hZ) _
        (_root_.SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS Z.left))

/-- Composed with the inclusion of the quasi-coherent algebras into all algebra sheaves,
`AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor` is
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor`. -/
theorem quasicoherentPushforwardAlgebraFunctor_comp_ι :
    quasicoherentPushforwardAlgebraFunctor B S hS X ⋙ quasicoherentAlgebraInclusion B S hS X =
      affinePushforwardAlgebraFunctor B S hS X :=
  rfl

end Functor

end AlgebraicGeometry.Space

end
