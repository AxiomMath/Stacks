module

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Quasi-coherence of the pullback of an algebra sheaf

Let `g : T ⟶ S` be a morphism of schemes and let `A` be a sheaf of commutative `𝒪_S`-algebras
whose underlying module is quasi-coherent. This file reduces quasi-coherence of the
`𝒪_T`-algebra `(algebraPullback g).obj A = g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` to each of two statements: that
its underlying `𝒪_T`-module is the pullback of the `𝒪_S`-module underlying `A`, and that the
base-change comparison of algebras is invertible at the structure morphism of the relative
spectrum of `A`.

## Main results

* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` — if
  the `𝒪_T`-module underlying `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is isomorphic to the pullback of the
  `𝒪_S`-module underlying `A`, then `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent.
* `Stacks.AffineAlgebraEquivalence.isAffineHom_pullback_hom` — the base change of an affine
  morphism, as the structure morphism of the base-changed object over `T`, is affine.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isIso_baseChangeAlgebraHom`
  — if an algebra sheaf `A` on `S` is isomorphic to `f_* 𝒪_X` for an affine `f : X ⟶ S` and the
  base-change comparison at `f` is invertible, then `(algebraPullback g).obj A` is
  quasi-coherent.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isIso` — the same for an
  arbitrary quasi-coherent `A`, with `f` taken to be the structure morphism of the relative
  spectrum of `A`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

open Stacks.RelativeSpec

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- If the `𝒪_T`-module underlying the algebra `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is isomorphic to the pullback
along `g` of the `𝒪_S`-module underlying a quasi-coherent `A`, then that algebra is
quasi-coherent. -/
public theorem isQuasicoherent_algebraPullback_of_underlyingModuleIso (A : AlgebraSheaf S)
    [A.IsQuasicoherent]
    (e : AlgebraSheaf.underlyingModule ((algebraPullback g).obj A) ≅
      (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A)) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e.symm
    (Stacks.Modules.isQuasicoherent_pullback g _ ‹A.IsQuasicoherent›)

/-- The base change along `g : T ⟶ S` of a scheme affine over `S` is affine over `T`. -/
public theorem isAffineHom_pullback_hom {X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    IsAffineHom ((Over.pullback g).obj (Over.mk f)).hom :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) ‹_›

/-- Let `A` be a sheaf of commutative `𝒪_S`-algebras which is isomorphic to `f_* 𝒪_X` for some
affine `f : X ⟶ S`. If the canonical comparison
`g⁻¹(f_* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ f'_* 𝒪_{X ×_S T}` is an isomorphism, then the pullback
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of `A` along `g` is quasi-coherent. -/
public theorem isQuasicoherent_algebraPullback_of_isIso_baseChangeAlgebraHom
    {X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] {A : AlgebraSheaf S}
    (e : pushforwardAlgebra f ≅ A) (h : IsIso (baseChangeAlgebraHom g (Over.mk f))) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  have := isAffineHom_pullback_hom g f
  AlgebraSheaf.isQuasicoherent_of_iso
    ((asIso (baseChangeAlgebraHom g (Over.mk f))).symm.trans ((algebraPullback g).mapIso e))
    (isQuasicoherent_pushforwardAlgebra ((Over.pullback g).obj (Over.mk f)).hom)

/-- If the canonical base-change comparison of algebras is an isomorphism at the structure
morphism of the relative spectrum of a quasi-coherent algebra `A` on `S`, then the pullback
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of `A` along `g` is quasi-coherent. -/
public theorem isQuasicoherent_algebraPullback_of_isIso (A : AlgebraSheaf S)
    [A.IsQuasicoherent]
    (h : IsIso (baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A)))) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  have := isAffineHom_relativeSpecToBase A
  isQuasicoherent_algebraPullback_of_isIso_baseChangeAlgebraHom g (relativeSpecToBase A)
    (pushforwardAlgebraIso A) h

end Stacks.AffineAlgebraEquivalence

end
