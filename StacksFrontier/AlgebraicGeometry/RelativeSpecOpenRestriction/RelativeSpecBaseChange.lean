module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum commutes with arbitrary base change

Let `S` be a scheme, let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras and let
`g : T ⟶ S` be an arbitrary morphism of schemes.  Then `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent
by `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_obj`, so its relative
spectrum over `T` is defined, and this file identifies it with the fibre product
`\underline{Spec}_S(A) ×_S T`.  This is Stacks Tag 01LX part (2).

## Main definitions

* `Stacks.AffineAlgebraEquivalence.relativeSpecAffineOverIso` transports the relative spectrum
  along an isomorphism of quasi-coherent algebras.
* `Stacks.AffineAlgebraEquivalence.pullbackAlgebraIso` is the isomorphism of `𝒪_T`-algebras
  between the pushed-forward structure sheaf of `\underline{Spec}_S(A) ×_S T` and `g^*A`.

## Main results

* `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`: **Stacks Tag 01LX part (2).** The
  isomorphism `\underline{Spec}_S(A) ×_S T ≅ \underline{Spec}_T(g^*A)` of schemes over `T`, with
  `Stacks.AffineAlgebraEquivalence.relativeSpecPullbackIso` for the underlying schemes.

## Implementation notes

Both schemes are affine over `T`, so both are relative spectra of their own pushed-forward
structure sheaves by Stacks Tag 01S8 (`overRelativeSpecIso`), and it suffices to identify those
two algebras.  For the fibre product that algebra is `g^*(A)` by the base-change assertion
`Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom` together with Tag 01LX part (3)
(`pushforwardAlgebraIso`); for the relative spectrum of `g^*A` it is `g^*A` itself, again by
part (3).  The transport of the relative spectrum along an isomorphism of algebras is full
faithfulness of `X ↦ f_* 𝒪_X`, exactly as in
`Stacks.AffineAlgebraEquivalence.affineOverRelativeSpecIso`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

/-! ### Transport of the relative spectrum along an isomorphism of algebras -/

/-- **An isomorphism of quasi-coherent algebras induces an isomorphism of their relative
spectra**, as schemes affine over the base.  Both relative spectra are carried to their own
algebras by the fully faithful functor `X ↦ f_* 𝒪_X`, up to the isomorphism
`pushforwardAlgebraIso` of Stacks Tag 01LX part (3). -/
public noncomputable def relativeSpecAffineOverIso {S : Scheme.{u}}
    {A A' : Stacks.RelativeSpec.AlgebraSheaf.{u} S}
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A'] (e : A ≅ A') :
    relativeSpecAffineOver A ≅ relativeSpecAffineOver A' :=
  ((fullyFaithfulAffineQuasicoherentPushforwardFunctor S).preimageIso
    (X := op (relativeSpecAffineOver A'))
    (Y := op (relativeSpecAffineOver A))
    ((IsQuasicoherentAlgebra S).ι.preimageIso
      (X := (affineQuasicoherentPushforwardFunctor S).obj (op (relativeSpecAffineOver A')))
      (Y := (affineQuasicoherentPushforwardFunctor S).obj (op (relativeSpecAffineOver A)))
      (pushforwardAlgebraIso A' ≪≫ e.symm ≪≫ (pushforwardAlgebraIso A).symm))).unop

/-- An isomorphism of quasi-coherent algebras induces an isomorphism of their relative spectra as
schemes over the base. -/
public noncomputable def relativeSpecOverIso {S : Scheme.{u}}
    {A A' : Stacks.RelativeSpec.AlgebraSheaf.{u} S}
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A'] (e : A ≅ A') :
    (Over.mk (relativeSpecToBase A) : Over S) ≅ Over.mk (relativeSpecToBase A') :=
  (IsAffineHomOver S).ι.mapIso (relativeSpecAffineOverIso e)

/-! ### The base change of a relative spectrum -/

section

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- The pushed-forward structure sheaf of the fibre product
`\underline{Spec}_S(A) ×_S T` is the base change `g^*A`: the base-change comparison is an
isomorphism by `isIso_baseChangeAlgebraHom`, and the pushed-forward structure sheaf of the
relative spectrum of `A` is `A` by Stacks Tag 01LX part (3). -/
public noncomputable def pullbackAlgebraIso :
    pushforwardAlgebra ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom ≅
      (algebraPullback g).obj A :=
  haveI : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  (@asIso _ _ _ _ _
      (isIso_baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A)))).symm ≪≫
    (algebraPullback g).mapIso (pushforwardAlgebraIso A)

/-- **Stacks Project, Tag 01LX part (2).** For a quasi-coherent sheaf of `𝒪_S`-algebras `A` and
an arbitrary morphism of schemes `g : T ⟶ S`, the fibre product
`\underline{Spec}_S(A) ×_S T` is the relative spectrum over `T` of the base change `g^*A`:
```
T ×_S \underline{Spec}_S(A) = \underline{Spec}_T(g^*A).
```
The base change `g^*A` is quasi-coherent by
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_obj`, which is what makes the
right-hand side meaningful. -/
@[stacks 01LX "part (2): Spec_S(A) ×_S T = Spec_T(g^*A) for an arbitrary morphism g : T → S",
  ega "II 1.5.6", sga "3 III 0.1.7", sga "3 VIA 2.1.2" "more general"]
public noncomputable def relativeSpecBaseChangeIso :
    (Over.pullback g).obj (Over.mk (relativeSpecToBase A)) ≅
      Over.mk (relativeSpecToBase ((algebraPullback g).obj A)) :=
  haveI : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  haveI : IsAffineHom ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom :=
    isAffineHom_overPullback_hom g (Over.mk (relativeSpecToBase A))
  haveI := isQuasicoherent_pushforwardAlgebra
    ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom
  overRelativeSpecIso ((Over.pullback g).obj (Over.mk (relativeSpecToBase A))).hom ≪≫
    relativeSpecOverIso (pullbackAlgebraIso g A)

/-- **Stacks Project, Tag 01LX part (2), on underlying schemes.** The fibre product
`\underline{Spec}_S(A) ×_S T` is isomorphic to `\underline{Spec}_T(g^*A)`; this is
`relativeSpecBaseChangeIso` read through the forgetful functor to schemes. -/
public noncomputable def relativeSpecPullbackIso :
    pullback (relativeSpecToBase A) g ≅ relativeSpec ((algebraPullback g).obj A) :=
  (Over.forget T).mapIso (relativeSpecBaseChangeIso g A)

end

end Stacks.AffineAlgebraEquivalence

end
