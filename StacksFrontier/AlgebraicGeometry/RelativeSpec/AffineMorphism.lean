module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic

/-!
# The pushed-forward structure sheaf of an affine morphism is a quasi-coherent algebra

Let `f : X ⟶ S` be an affine morphism of schemes. Over an affine open `U` of `S` the inverse
image `f ⁻¹ᵁ U` is affine, so the sections of `𝒪_X` over the inverse image of a basic open
`D(s) ⊆ U` are the localization of the sections over `f ⁻¹ᵁ U` away from the image of `s`. This
is the quasi-coherence of the `𝒪_S`-algebra `f_* 𝒪_X`, in the form
`CategoryTheory.NatTrans.Coequifibered` in which
`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData` consumes a quasi-coherent sheaf
of `𝒪_S`-algebras in order to build its relative spectrum.

## Main definitions

* `Stacks.RelativeSpec.pushforwardAlgebraSite` is the presheaf of rings `f_* 𝒪_X` read on the
  small affine Zariski site of `S`, and `Stacks.RelativeSpec.pushforwardAlgebraSiteHom` is its
  structure morphism from `𝒪_S`.

## Main results

* `Stacks.RelativeSpec.isLocalization_away_app`: for an affine morphism `f : X ⟶ S` and an
  affine open `U` of `S`, the sections of `𝒪_X` over the basic open of the image of a section
  `s` of `𝒪_S` over `U` form the localization of the sections over `f ⁻¹ᵁ U` away from that
  image.
* `Stacks.RelativeSpec.isLocalization_away_of_eq` is the same statement read on an open of `X`
  presented as that basic open, in particular on `f ⁻¹ᵁ D(s)`.
* `Stacks.RelativeSpec.coequifibered_pushforwardAlgebraSiteHom`: the structure morphism
  `𝒪_S ⟶ f_* 𝒪_X` of an affine morphism is coequifibered on the small affine Zariski site.

## Implementation notes

The localization statement is given twice because the open it concerns is presented in two
ways. `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` describes the sections over
`X.basicOpen (f.app U s)`, whereas `f_* 𝒪_X` has sections over `f ⁻¹ᵁ S.basicOpen s`; the two
opens agree by `AlgebraicGeometry.Scheme.preimage_basicOpen`, but the `Algebra` instance
carried by the localization statement mentions the open, so the identification has to be made
by substituting the open rather than by rewriting inside the statement. The second form
therefore takes the open and the restriction map as parameters, and is applied with the
equation.

The algebra structure that `coequifibered_pushforwardAlgebraSiteHom` is asked for, through
`AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway`, is the
restriction map of `f_* 𝒪_X` along an inclusion of affine opens of `S`. It is definitionally
the restriction map of `𝒪_X` along the corresponding inclusion of inverse images, because the
inverse-image functor on opens is monotone and the morphisms of a preorder are proofs.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeSpec

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]

section Localization

variable {U : S.Opens} (hU : IsAffineOpen U)

include hU

/-- For an affine morphism `f : X ⟶ S`, an affine open `U` of `S` and a section `s` of `𝒪_S`
over `U`, the sections of `𝒪_X` over the basic open of the image of `s` form the localization
of the sections over the inverse image of `U` away from that image. -/
theorem isLocalization_away_app (s : Γ(S, U)) :
    IsLocalization.Away (f.app U s) Γ(X, X.basicOpen (f.app U s)) :=
  (hU.preimage f).isLocalization_basicOpen _

/-- The localization statement of `Stacks.RelativeSpec.isLocalization_away_app`, for an open of
`X` presented as the basic open of the image of `s`. It applies to `f ⁻¹ᵁ D(s)` through
`AlgebraicGeometry.Scheme.preimage_basicOpen`. -/
theorem isLocalization_away_of_eq (s : Γ(S, U)) {W : X.Opens} (hle : W ≤ f ⁻¹ᵁ U)
    (hW : W = X.basicOpen (f.app U s)) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away (f.app U s) Γ(X, W) := by
  subst hW
  exact isLocalization_away_app f hU s

end Localization

section Site

/-- The presheaf of rings `f_* 𝒪_X`, read on the small affine Zariski site of `S`. -/
noncomputable def pushforwardAlgebraSite : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).right.obj

/-- The structure morphism `𝒪_S ⟶ f_* 𝒪_X`, read on the small affine Zariski site of `S`. -/
noncomputable def pushforwardAlgebraSiteHom :
    (Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf ⟶ pushforwardAlgebraSite f :=
  (Scheme.AffineZariskiSite.toOpensFunctor S).op.whiskerLeft
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).hom.hom

/-- **The pushed-forward structure sheaf of an affine morphism is a quasi-coherent algebra.**
For an affine morphism `f : X ⟶ S` the structure morphism `𝒪_S ⟶ f_* 𝒪_X` is coequifibered on
the small affine Zariski site of `S`: the sections of `f_* 𝒪_X` over a basic open `D(s)` of an
affine open `U` of `S` are the sections over `U`, localized away from the image of `s`. -/
@[sga "3 III 0.1.7" "For an affine morphism π"]
theorem coequifibered_pushforwardAlgebraSiteHom :
    (pushforwardAlgebraSiteHom f).Coequifibered :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U s ↦
    isLocalization_away_of_eq f U.2 s _ (Scheme.preimage_basicOpen f s)

end Site

end Stacks.RelativeSpec

end
