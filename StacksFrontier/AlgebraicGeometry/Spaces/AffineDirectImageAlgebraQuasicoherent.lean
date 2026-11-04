module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism

/-!
# The direct image of the structure sheaf along an affine morphism, as a quasi-coherent algebra

For an algebraic space `f : Y ⟶ X` affine over an algebraic space `X`, the direct image
`f_* 𝒪_Y` is a quasi-coherent sheaf of commutative `𝒪_X`-algebras, so the direct-image functor
`f ↦ f_* 𝒪_Y` corestricts to the quasi-coherent algebras.

## Main definitions

* `AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctor` is the contravariant
  direct-image functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the
  quasi-coherent sheaves of commutative `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctorObjIso` identifies its value
  on `Y` with the pushed-forward structure sheaf of `Y`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_isAffineHom`: the direct-image
  algebra `f_* 𝒪_Y` of an algebraic space affine over `X` is quasi-coherent.
* `AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctor_comp_inclusion`: composed
  with the inclusion of the quasi-coherent algebras, the functor is
  `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor`.
* `AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctor_map_right`: its action on
  a morphism over `X` is `AlgebraicGeometry.Space.pushforwardRingMap`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For an algebraic space `T` over `X` whose structure morphism is affine, the `𝒪_X`-algebra
`T.hom _* 𝒪_{T.left}` is quasi-coherent. -/
theorem isQuasicoherent_pushforwardAlgebra_of_isAffineHom {X : AlgebraicSpaces B S hS}
    (T : Over X) (hT : IsAffineHom B S hS T.hom.hom) :
    (pushforwardAlgebra B S hS T).IsQuasicoherent := by
  have e : (pushforwardAlgebra B S hS T).underlyingModule =
      (modulePushforward B S hS T.hom).obj
        (SheafOfModules.unit (structureRingSheaf B S hS T.left)) :=
    underlyingModule_pushforwardAlgebra B S hS T.hom
  rw [AlgebraSheaf.IsQuasicoherent, e]
  exact isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS T.hom hT _
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS T.left))

/-- The contravariant functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the
quasi-coherent sheaves of commutative `𝒪_X`-algebras. -/
def affinePushforwardQuasicoherentAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ⥤ QuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift
    (AlgebraSheaf.IsQuasicoherent : ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2))
    (affinePushforwardAlgebraFunctor B S hS X)
    fun Y ↦ isQuasicoherent_pushforwardAlgebra_of_isAffineHom B S hS Y.unop.obj Y.unop.property

/-- Composing `AlgebraicGeometry.Space.affinePushforwardQuasicoherentAlgebraFunctor` with the
inclusion of the quasi-coherent algebras gives the direct-image functor. -/
theorem affinePushforwardQuasicoherentAlgebraFunctor_comp_inclusion
    (X : AlgebraicSpaces B S hS) :
    affinePushforwardQuasicoherentAlgebraFunctor B S hS X ⋙
        quasicoherentAlgebraInclusion B S hS X =
      affinePushforwardAlgebraFunctor B S hS X :=
  rfl

/-- The value of the direct-image functor on an algebraic space `Y` affine over `X` is the
pushed-forward structure sheaf of `Y`. -/
def affinePushforwardQuasicoherentAlgebraFunctorObjIso (X : AlgebraicSpaces B S hS)
    (Y : AffineOver B S hS X) :
    (quasicoherentAlgebraInclusion B S hS X).obj
        ((affinePushforwardQuasicoherentAlgebraFunctor B S hS X).obj (op Y)) ≅
      pushforwardAlgebra B S hS Y.obj :=
  Iso.refl _

/-- The action of the direct-image functor on a morphism over `X` is the canonical map on
direct-image rings. -/
theorem affinePushforwardQuasicoherentAlgebraFunctor_map_right (X : AlgebraicSpaces B S hS)
    {Y Z : AffineOver B S hS X} (f : Y ⟶ Z) :
    ((affinePushforwardQuasicoherentAlgebraFunctorObjIso B S hS X Z).inv ≫
        (quasicoherentAlgebraInclusion B S hS X).map
          ((affinePushforwardQuasicoherentAlgebraFunctor B S hS X).map f.op) ≫
        (affinePushforwardQuasicoherentAlgebraFunctorObjIso B S hS X Y).hom).right =
      pushforwardRingMap B S hS f.hom :=
  rfl

end AlgebraicGeometry.Space

end
