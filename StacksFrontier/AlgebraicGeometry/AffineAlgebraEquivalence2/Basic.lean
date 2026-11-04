module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# The functor underlying the anti-equivalence of affine schemes and quasi-coherent algebras

Let `S` be a scheme. The anti-equivalence of Stacks Tag 01SA between the schemes affine over
`S` and the quasi-coherent sheaves of commutative `𝒪_S`-algebras is given by the functor
`X ↦ f_* 𝒪_X`. This file shows that this functor indeed lands in the quasi-coherent algebras,
which is what makes it a functor to the category `QuasicoherentAlgebra S`.

## Main results

* `isQuasicoherent_pushforwardAlgebra`: for an affine morphism `f : X ⟶ S` the algebra
  `f_* 𝒪_X` is quasi-coherent.
* `affineQuasicoherentPushforwardFunctor` is the resulting functor
  `(AffineOver S)ᵒᵖ ⥤ QuasicoherentAlgebra S`.

## Implementation notes

The module underlying the algebra `f_* 𝒪_X` is, by the definitions of
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` and of
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`, *equal* to the restriction of
scalars along `f.toRingCatSheafHom` of the unit module over `f_* 𝒪_X`; this is
`underlyingModule_pushforwardAlgebra`, proved by `rfl`. Quasi-coherence of the latter is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing`,
i.e. Stacks Tag 02KG for the structure sheaf.

Composing the lift with the inclusion of the full subcategory of quasi-coherent algebras
returns `affinePushforwardAlgebraFunctor` definitionally, by
`CategoryTheory.ObjectProperty.liftCompιIso`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.AffineQcohPushforward

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### Quasi-coherence of the pushed-forward structure sheaf -/

/-- The sheaf of rings underlying the algebra `f_* 𝒪_X` is the pushed-forward sheaf of rings
`f_* 𝒪_X`. -/
public theorem ringSheaf_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.RelativeSpec.AlgebraSheaf.ringSheaf (pushforwardAlgebra f) =
      pushforwardRing f.base X.ringCatSheaf :=
  rfl

/-- The structure morphism of the algebra `f_* 𝒪_X`, as a morphism of sheaves of rings, is the
morphism of sheaves of rings attached to `f`. -/
public theorem structureMap_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.RelativeSpec.AlgebraSheaf.structureMap (pushforwardAlgebra f) =
      f.toRingCatSheafHom :=
  rfl

/-- The `𝒪_S`-module underlying the algebra `f_* 𝒪_X` is the direct image of the structure
sheaf of `X`, presented as the restriction of scalars of the unit module over `f_* 𝒪_X`. -/
public theorem underlyingModule_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.RelativeSpec.AlgebraSheaf.underlyingModule (pushforwardAlgebra f) =
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
        (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)) :=
  rfl

/-- For an affine morphism `f : X ⟶ S`, the sheaf of algebras `f_* 𝒪_X` is quasi-coherent.
This is the half of Stacks Tag 02KG which makes `X ↦ f_* 𝒪_X` a functor into the category of
quasi-coherent `𝒪_S`-algebras. -/
public theorem isQuasicoherent_pushforwardAlgebra {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f) :=
  isQuasicoherent_restrictScalars_pushforwardRing f

/-- The functor `X ↦ f_* 𝒪_X` from the schemes affine over `S`, contravariantly, to the
quasi-coherent sheaves of commutative `𝒪_S`-algebras. This is the functor underlying the
anti-equivalence of Stacks Tag 01SA. -/
public noncomputable def affineQuasicoherentPushforwardFunctor (S : Scheme.{u}) :
    (AffineOver S)ᵒᵖ ⥤ QuasicoherentAlgebra S :=
  ObjectProperty.lift _ (affinePushforwardAlgebraFunctor S) fun X ↦
    letI := X.unop.property
    isQuasicoherent_pushforwardAlgebra X.unop.obj.hom

/-- Composing the functor into quasi-coherent algebras with the inclusion of the full
subcategory returns the pushforward functor into all algebra sheaves. -/
public noncomputable def affineQuasicoherentPushforwardFunctorCompι (S : Scheme.{u}) :
    affineQuasicoherentPushforwardFunctor S ⋙ (IsQuasicoherentAlgebra S).ι ≅
      affinePushforwardAlgebraFunctor S :=
  ObjectProperty.liftCompιIso _ _ _

end Stacks.AffineAlgebraEquivalence

end
