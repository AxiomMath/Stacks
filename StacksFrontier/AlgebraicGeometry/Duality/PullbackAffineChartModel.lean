module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AffineModelPullbackSquare

/-!
# The affine-chart model of a pullback of a quasi-coherent module

Let `f : X ⟶ Y` be an arbitrary morphism of schemes — no flatness is assumed — let `U` be an
affine open of `Y`, and let `V` be an affine open of `X` with `f(V) ⊆ U`. For a quasi-coherent
module `G` on `Y`, [Stacks, Tag 01XZ] (4) presents `G|_U` as the sheaf associated with the
`Γ(Y, U)`-module `M = Γ(U, G)`, read on `U` through `U ≅ Spec Γ(Y, U)`. The content of this file
is that the pullback `f^*G` is presented over `V` in the same way, by the extension of scalars
`Γ(X, V) ⊗_{Γ(Y, U)} M` along `f.appLE U V`, read on `V` through `V ≅ Spec Γ(X, V)`.

This is the affine comparison of [Stacks, Tag 01I9] transported to a pair of nested affine opens.
It is the underived analogue of
`AlgebraicGeometry.Scheme.Modules.restrictedDerivedPullbackModelIso`, which is the same statement
for the derived pullback of an object of the derived category and is [Stacks, Tag 08DW] part (2);
unlike that one it needs no flatness, because degreewise pullback requires no exactness.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictedPullbackModelIso` — **the affine-chart model of a
  pullback**: over an affine open `V ⊆ f⁻¹(U)` the module `f^*G` is the sheaf associated with
  `Γ(X, V) ⊗_{Γ(Y, U)} Γ(U, G)`.

## Implementation notes

The three inputs are chained as isomorphisms with `≪≫` and `CategoryTheory.Functor.mapIso`,
exactly as in `AlgebraicGeometry.Scheme.Modules.restrictedDerivedPullbackModelIso`: first
`AlgebraicGeometry.Scheme.Modules.pullbackRestrictionSquareIso` on the square
`V.ι ≫ f = f.resLE U V hVU ≫ U.ι`, which replaces `(f^*G)|_V` by `(f|_V)^*(G|_U)`; then
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde`, which names the presenting module
of `G|_U`; then `AlgebraicGeometry.Scheme.Modules.affineModelPullbackIso_unconditional`, the
comparison square itself. The middle step is stated with `Scheme.Modules.pullback hU.isoSpec.hom`
and is converted to `Scheme.Modules.restrictFunctor hU.isoSpec.hom` by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, the shape the comparison square
expects.

No rewriting is used. Goals mixing `X.Modules` with `SheafOfModules (structureSheafRing _)` are
not type-correct at the transparency `rewrite` works at, so `rw` and `calc` on such morphism
equations are unavailable; composing isomorphisms avoids the question.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentTFAE (restrictIsoSpecTilde specModule)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The presenting `Γ(Y, U)`-module of `G|_U`, read on `U` itself rather than on
`Spec Γ(Y, U)`: for quasi-coherent `G` the restriction `G|_U` is the sheaf associated with
`specModule G hU`, transported along `U ≅ Spec Γ(Y, U)`.

This is `Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde` with the transport spelled
by `Scheme.Modules.restrictFunctor` instead of `Scheme.Modules.pullback`. -/
def restrictIsoSpecTildeRestrictFunctor {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (G : Y.Modules) [G.IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor U.ι).obj G ≅
      (tilde.functor Γ(Y, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj
        (specModule G hU) :=
  restrictIsoSpecTilde G hU ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app
      ((tilde.functor Γ(Y, U)).obj (specModule G hU))).symm

/-- **The affine model of a pullback at two nested affine opens.** Let `f : X ⟶ Y` be any
morphism of schemes, `U` an affine open of `Y`, `V` an affine open of `X` with `f(V) ⊆ U`, and
`G` a quasi-coherent module on `Y`. Then the restriction of `f^*G` to `V` is the sheaf associated
with the `Γ(X, V)`-module `Γ(X, V) ⊗_{Γ(Y, U)} Γ(U, G)`, read on `V` through the canonical
isomorphism `V ≅ Spec Γ(X, V)`.

This is [Stacks, Tag 01I9] transported to the pair `(U, V)`; it is the underived form of
`AlgebraicGeometry.Scheme.Modules.restrictedDerivedPullbackModelIso`, which is
[Stacks, Tag 08DW] part (2), and carries no flatness hypothesis. -/
def restrictedPullbackModelIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (G : Y.Modules) [G.IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pullback f).obj G) ≅
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj
        ((tilde.functor Γ(X, V)).obj
          ((ModuleCat.extendScalars (f.appLE U V hVU).hom).obj (specModule G hU))) :=
  (pullbackRestrictionSquareIso f (f.resLE U V hVU) V.ι U.ι (f.resLE_comp_ι hVU).symm).app G ≪≫
    (Scheme.Modules.pullback (f.resLE U V hVU)).mapIso
      (restrictIsoSpecTildeRestrictFunctor hU G) ≪≫
    (affineModelPullbackIso_unconditional f hU hV hVU).app (specModule G hU)

end AlgebraicGeometry.Scheme.Modules

end
