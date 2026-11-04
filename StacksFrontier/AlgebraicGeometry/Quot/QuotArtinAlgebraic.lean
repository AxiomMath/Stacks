module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinSizeBound
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinLimits
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentSpaces
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinEffective
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTower
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorLimitPreserving

/-!
# The Quot functor via Artin's axioms (Stacks 0CZW)

Let `S` be a Noetherian scheme all of whose local rings are G-rings, `f : X ⟶ S` a separated
morphism of finite presentation from an algebraic space, and `F` a quasi-coherent `𝒪_X`-module of
finite presentation, flat over `S`. Stacks 0CZW sketches how Artin's axioms (Stacks 07Y1) show
that `Quot_{F/X/S}` is an algebraic space locally of finite presentation over `S`, without the
algebraicity of the stack of coherent sheaves used for Stacks 09TU. The axioms are verified in

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diag_quotOverBase` (the diagonal),
* `AlgebraicGeometry.Space.isSheaf_quotOverBase` ([0]),
* `AlgebraicGeometry.Space.limitPreserving_quotOverBase` ([1]),
* `AlgebraicGeometry.Space.satisfiesRS_quotOverBase` ([2]),
* `AlgebraicGeometry.Space.hasFiniteDimensionalTangentSpaces_quotOverBase` ([3]),
* `AlgebraicGeometry.Space.isEffective_quotOverBase` ([4]),
* `AlgebraicGeometry.Space.isOpenVersality_quotOverBase` ([5]),

and assembled here through `AlgebraicGeometry.Space.isAlgebraicSpace_of_artinAxioms`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_and_isLocallyOfFinitePresentation_quotOverBase`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **`Quot_{F/X/S}` is an algebraic space locally of finite presentation over `S`.** Let `S` be
Noetherian with all local rings G-rings, `f : X ⟶ S` separated and of finite presentation, and `F`
a quasi-coherent `𝒪_X`-module of finite presentation, flat over `S`. Then every model of
`Quot_{F/X/S}` in the universe of the site is an algebraic space whose morphism to `S` is locally
of finite presentation. -/
@[stacks 0CZW "Quot_{F/X/S} is an algebraic space locally of finite presentation over S, by \
Artin's axioms (Stacks 07Y1)"]
theorem isAlgebraicSpace_and_isLocallyOfFinitePresentation_quotOverBase
    [AlgebraicGeometry.IsNoetherian S] (hG : ∀ s : S, IsGRing (S.presheaf.stalk s))
    (hsep : IsSeparated B S hS f.hom) (hFfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS X.2 f.hom F) :
    ∀ N : QuotSitePresheafModel (quotOverBase X f hf F hF),
      IsAlgebraicSpace B S hS N.presheaf ∧ IsLocallyOfFinitePresentation B S hS N.toBase := by
  have halg : IsAlgebraicSpace B S hS (quotOverBasePresheaf X f hf F hF) :=
    isAlgebraicSpace_of_artinAxioms B S hS _
      (isRepresentableByAlgebraicSpaces_diag_quotOverBase X f hf F hF)
      (exists_sizeBound_quotOverBase X f hf F hF
        (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite F))
      (isSheaf_quotOverBase X f hf F hF).2 (limitPreserving_quotOverBase X f hf F hF hFfp)
      (satisfiesRS_quotOverBase X f hf F hF).2
      (hasFiniteDimensionalTangentSpaces_quotOverBase X f hf F hF hFfp hflat)
      (isEffective_quotOverBase X f hf F hF hsep hFfp)
      (isOpenVersality_quotOverBase X f hf F hF hsep hFfp) (fun s _ => hG s)
  let M := (quotOverBase X f hf F hF).quotSitePresheafModel
  intro N
  exact QuotSitePresheafModel.isAlgebraicSpace_and_lfp_of_model M N halg
    (M.isLocallyOfFinitePresentation_toBase halg hFfp)

end AlgebraicGeometry.Space
