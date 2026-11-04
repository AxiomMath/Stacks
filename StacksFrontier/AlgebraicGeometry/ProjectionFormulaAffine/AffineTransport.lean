module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.Basic

/-!
# The affine criterion over an arbitrary affine base

`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` detects invertibility of
a morphism of quasi-coherent modules on global sections, but only over a base which is
*literally* `Spec R`.  The locality reduction
`Stacks.ProjectionFormula.isIso_projectionFormulaMap_iff_forall_affineOpen` produces instead an
affine *open* `V` of `S`, and `(V : Scheme)` is affine without being `Spec` of anything; the two
could not be composed.

This file supplies the missing step.  For an affine scheme `Y`, Mathlib's `Scheme.isoSpec` is an
isomorphism `Y ≅ Spec Γ(Y, ⊤)`, and pushing forward along it is an equivalence of categories of
modules, so the criterion over `Spec Γ(Y, ⊤)` transports to `Y`.

## Main definitions

* `Stacks.ProjectionFormula.pushforwardCompIso`: pushing forward along an isomorphism of schemes
  and then along its inverse is the identity functor.

## Main results

* `Stacks.ProjectionFormula.isIso_of_isIso_pushforward_iso`: pushforward along an isomorphism of
  schemes reflects invertibility.
* `Stacks.ProjectionFormula.isIso_of_isIso_moduleSpecΓ_isoSpec`: **the affine criterion over an
  arbitrary affine scheme.**  A morphism of quasi-coherent modules on an affine scheme `Y` is
  invertible as soon as its transport to `Spec Γ(Y, ⊤)` is invertible on global sections.
* `Stacks.ProjectionFormula.isIso_projectionFormulaMap_of_isIso_moduleSpecΓ_isoSpec`: the same
  statement for the projection-formula map, with the quasi-coherence of its source and target
  discharged from `Basic.lean`.  This is the form the locality reduction can be composed with.

## Implementation notes

`pushforwardCompIso` is assembled from Mathlib's `Scheme.Modules.pushforwardComp`,
`Scheme.Modules.pushforwardCongr` and `Scheme.Modules.pushforwardId` rather than from an
`eqToIso`.

An isomorphism of schemes is an affine morphism by instance search, so the quasi-coherence of a
pushforward along `Scheme.isoSpec` is Stacks 02KG
(`Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom`) with no extra work.

As in `Basic.lean`, a morphism of `SheafOfModules (structureSheafRing S.toRingedSpace)` is also a
morphism of `S.Modules` and the two categories carry equal but not syntactically equal `Category`
instances, so `IsIso` has to be moved across explicitly by `isIso_schemeModules` and
`isIso_sheafOfModules`.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula

universe u

/-! ### Pushforward along an isomorphism of schemes -/

/-- **Pushing forward along an isomorphism of schemes and then along its inverse is the identity
functor.**  Assembled from `Scheme.Modules.pushforwardComp`, `Scheme.Modules.pushforwardCongr`
and `Scheme.Modules.pushforwardId`. -/
def pushforwardCompIso {Y Z : Scheme.{u}} (ε : Y ≅ Z) :
    Scheme.Modules.pushforward ε.hom ⋙ Scheme.Modules.pushforward ε.inv ≅ 𝟭 Y.Modules :=
  Scheme.Modules.pushforwardComp ε.hom ε.inv ≪≫
    Scheme.Modules.pushforwardCongr ε.hom_inv_id ≪≫ Scheme.Modules.pushforwardId Y

/-- **Pushforward along an isomorphism of schemes reflects invertibility.**  It is one half of an
equivalence of categories, by `pushforwardCompIso`. -/
lemma isIso_of_isIso_pushforward_iso {Y Z : Scheme.{u}} (ε : Y ≅ Z) {M N : Y.Modules}
    (φ : M ⟶ N) (h : IsIso ((Scheme.Modules.pushforward ε.hom).map φ)) : IsIso φ :=
  (NatIso.isIso_map_iff (pushforwardCompIso ε) φ).mp
    (Functor.map_isIso (Scheme.Modules.pushforward ε.inv) _)

/-! ### The affine criterion over an arbitrary affine scheme -/

/-- **The affine criterion over an arbitrary affine scheme.**  A morphism of quasi-coherent
modules on an affine scheme `Y` is invertible as soon as its pushforward along
`Y.isoSpec : Y ≅ Spec Γ(Y, ⊤)` is invertible on global sections.

This is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, which needs a base
which is literally `Spec` of a ring, transported along `Scheme.isoSpec`.  Without it the locality
reduction of `Basic.lean`, which produces an affine *open* of the base, cannot be composed with
the affine criterion at all. -/
theorem isIso_of_isIso_moduleSpecΓ_isoSpec {Y : Scheme.{u}} [IsAffine Y] {M N : Y.Modules}
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) (φ : M ⟶ N)
    (h : IsIso ((moduleSpecΓFunctor (R := Γ(Y, ⊤))).map
      ((Scheme.Modules.pushforward Y.isoSpec.hom).map φ))) :
    IsIso φ :=
  isIso_of_isIso_pushforward_iso Y.isoSpec φ
    (@Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ Γ(Y, ⊤) _ _
      (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom Y.isoSpec.hom M hM)
      (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom Y.isoSpec.hom N hN) _ h)

/-- **The projection-formula map over an arbitrary affine base is detected on global sections.**
For an affine morphism `h : T ⟶ S` with `S` affine and quasi-coherent `G` and `H`, the
projection-formula map is invertible as soon as its transport to `Spec Γ(S, ⊤)` is invertible on
global sections.

The quasi-coherence of the source and the target is
`isQuasicoherent_projectionFormulaMap_source` and `isQuasicoherent_projectionFormulaMap_target`
of `Basic.lean`; the transport is `isIso_of_isIso_moduleSpecΓ_isoSpec`.  This is the shape the
locality reduction `isIso_projectionFormulaMap_iff_forall_affineOpen` can be composed with, since
an affine open of `S` is affine without being `Spec` of a ring. -/
theorem isIso_projectionFormulaMap_of_isIso_moduleSpecΓ_isoSpec {T S : Scheme.{u}} [IsAffine S]
    (h : T ⟶ S) [IsAffineHom h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) (hG : G.IsQuasicoherent)
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hH : H.IsQuasicoherent)
    (hΓ : IsIso ((moduleSpecΓFunctor (R := Γ(S, ⊤))).map
      ((Scheme.Modules.pushforward S.isoSpec.hom).map (projectionFormulaMap h G H)))) :
    IsIso (projectionFormulaMap h G H) :=
  isIso_sheafOfModules
    (isIso_of_isIso_moduleSpecΓ_isoSpec
      (isQuasicoherent_projectionFormulaMap_source h G H hG hH)
      (isQuasicoherent_projectionFormulaMap_target h G H hG hH)
      (projectionFormulaMap h G H) hΓ)

end Stacks.ProjectionFormula

end
