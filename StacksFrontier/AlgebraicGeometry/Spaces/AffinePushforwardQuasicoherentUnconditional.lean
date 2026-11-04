module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardTriangle
import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The direct image along an affine morphism of algebraic spaces is quasi-coherent

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B` and let `F` be a quasi-coherent `𝒪_X`-module. The first assertion of Stacks 07U8 is that
`f_*F` is quasi-coherent.

`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` reduces that
assertion chartwise to the case of a target represented by a scheme of the site, which it carries
as the hypothesis `AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent`. This file
discharges that hypothesis, so the assertion becomes unconditional.

The reduction of the *source* is the one the proof of Stacks 073H opens with. An affine morphism
`f : X ⟶ V` with represented target is representable by Stacks 03WG, so the base change of `f`
along the identity of `V` is represented by a scheme `T'` of the site; because the morphism base
changed along is an isomorphism, that identifies `X` with the algebraic space of `T'` and `f`
with the represented morphism `T' ⟶ V`, whose underlying morphism of schemes the same reading of
Stacks 03WG shows to be affine. Quasi-coherence of the direct image along a represented morphism
with affine underlying morphism of schemes is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap`, and the
identification of `f` with a composite of an isomorphism and that represented morphism is carried
across by `AlgebraicGeometry.Space.modulePushforwardTriangleApp`.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardInvIsoModulePullback`: the direct image along the
  inverse of an isomorphism is the inverse image along the isomorphism.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isIso`: the direct image
  along the inverse of an isomorphism preserves quasi-coherence.
* `AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent`: **the hypothesis of
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`, proved.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`: **the
  quasi-coherence assertion of Stacks 07U8, with no hypothesis.**
* `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isAffineHom`: the same, in the
  packaged form `AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence` that the consumers
  of Stacks 03M9 take.

## Implementation notes

The direct image along the inverse of an isomorphism is identified with the inverse image along
the isomorphism rather than compared with it by hand: both are right adjoint to the inverse image
along the inverse — the first by the adjunction of Stacks 03LU, the second because the inverse
image along an isomorphism is an equivalence — so the identification is
`CategoryTheory.Adjunction.rightAdjointUniq`. That is what lets Stacks 03GA along an étale
morphism, which is a statement about inverse images, be read as a statement about the direct image
along the inverse of an isomorphism.

The comparison of quasi-coherence across an isomorphism is reproved here from Stacks 03GA rather
than taken from `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_iso_iff`, whose file
is the Quot development and carries far more than is needed.

The two assertions of Stacks 07U8 about the total derived direct image and about arbitrary base
change are not treated here, and the attribute carries a part string naming the one assertion
that is. They are
`AlgebraicGeometry.Space.isIso_rightDerivedFunctorPlusUnit_app_modulePushforward_isAffineHom` and
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom`. The conditional form in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageQuasicoherent.lean` keeps its own
qualified attribute.

The module universe is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePushforward` exists.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct image along the inverse of an isomorphism -/

/-- **The direct image along the inverse of an isomorphism is the inverse image along the
isomorphism.**  For an isomorphism `e : X ≅ Y` of algebraic spaces over `S` the two functors
`(e⁻¹)_*` and `e^*` from `𝒪_Y`-modules to `𝒪_X`-modules agree.

Both are right adjoint to `(e⁻¹)^*`: the first by the adjunction half of Stacks 03LU, the second
because the inverse image along an isomorphism is an equivalence with the inverse image along the
inverse isomorphism as its inverse. -/
def modulePushforwardInvIsoModulePullback {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    modulePushforward B S hS e.inv ≅ modulePullback B S hS e.hom :=
  Adjunction.rightAdjointUniq (modulePullbackAdjunction B S hS e.inv)
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence e.symm).toAdjunction

/-- **The direct image along the inverse of an isomorphism preserves quasi-coherence.**  If
`e : X ≅ Y` is an isomorphism of algebraic spaces over `S` and `F` is a quasi-coherent
`𝒪_Y`-module, then the direct image `(e⁻¹)_*F` is a quasi-coherent `𝒪_X`-module.

By `AlgebraicGeometry.Space.modulePushforwardInvIsoModulePullback` this is the inverse image
`e^*F`, and an isomorphism is étale, so Stacks 03GA along an étale morphism applies. -/
theorem isQuasicoherentOnSite_modulePushforward_of_isIso {X Y : AlgebraicSpaces B S hS}
    (e : X ≅ Y) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS e.inv).obj F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePushforwardInvIsoModulePullback B S hS e).app F).symm
    (isQuasicoherentOnSite_modulePullback_of_isEtale B S hS e.hom
      (isEtale_of_isIso B S hS e.hom.hom) F hF)

/-! ### Discharging the scheme-target hypothesis of Stacks 07U8 -/

/-- **The first assertion of Stacks 07U8 for a target represented by a scheme of the site**, with
no hypothesis.

Let `f : X ⟶ schemeSpace V` be an affine morphism of algebraic spaces whose target is the
algebraic space of a scheme `V` of the big fppf site. By Stacks 03WG, in the reading
`AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace`, the morphism
`f` is representable and each of its represented base changes is an affine morphism of schemes.
Base changing along the identity of `V` produces a scheme `T'` of the site, a morphism
`g : T' ⟶ V` whose underlying morphism of schemes is affine, and a morphism
`fst : yoneda.obj T' ⟶ X` sitting in a cartesian square whose other vertical is the identity;
hence `fst` is an isomorphism and `f` is the composite of its inverse with the represented
morphism of `g`.

Quasi-coherence is then carried along that composite: the first factor is the direct image along
the inverse of an isomorphism, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isIso`, the second is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap`, and the
two are glued by `AlgebraicGeometry.Space.modulePushforwardTriangleApp`. -/
theorem schemeTargetAffinePushforwardQuasicoherent :
    SchemeTargetAffinePushforwardQuasicoherent B S hS := by
  intro V X f hf F hF
  obtain ⟨hrel, hprop⟩ := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    X.property (schemeSpace V).property hf
  obtain ⟨T', g, fst, hsq⟩ := hrel (a := V) (𝟙 (schemeSpace V).obj)
  have hgaff : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) :=
    hprop.2 (𝟙 (schemeSpace V).obj) fst g hsq
  have hfst : IsIso fst := hsq.isIso_fst_of_isIso (IsIso.id _)
  have hemb : IsIso (ObjectProperty.homMk fst : schemeSpace T' ⟶ X) :=
    (ObjectProperty.isIso_hom_iff _).1 hfst
  have hw : fst ≫ f.hom = yoneda.map g := hsq.w.trans (Category.comp_id _)
  have hcomp : (ObjectProperty.homMk fst : schemeSpace T' ⟶ X) ≫ f = schemeSpaceMap g :=
    ObjectProperty.hom_ext _ hw
  have hk : inv (ObjectProperty.homMk fst : schemeSpace T' ⟶ X) ≫ schemeSpaceMap g = f := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso (modulePushforwardTriangleApp B S hS hk F)
    (isQuasicoherentOnSite_modulePushforward_representedSpaceMap B S hS g _
      (isQuasicoherentOnSite_modulePushforward_of_isIso B S hS
        (asIso (ObjectProperty.homMk fst : schemeSpace T' ⟶ X)) F hF))

/-! ### Stacks 07U8 -/

/-- **Stacks 07U8, the quasi-coherence of the direct image, with no hypothesis.**  Let
`f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and let `F` be a quasi-coherent
`𝒪_X`-module. Then the direct image `f_*F` is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` with its
hypothesis supplied by
`AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent`. -/
@[stacks 07U8 "quasi-coherence of the direct image"]
theorem isQuasicoherentOnSite_modulePushforward_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_isAffineHom B S hS
    (schemeTargetAffinePushforwardQuasicoherent B S hS) f hf F hF

/-- **The quasi-coherence assertion of Stacks 07U8 in packaged form.**  An affine morphism of
algebraic spaces over `S` has a direct image preserving quasi-coherence, in the sense of
`AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence`.

This is the form the consumers of Stacks 03M9 take; the content is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`, quantified over
the module. -/
theorem pushforwardPreservesQuasicoherence_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) :
    PushforwardPreservesQuasicoherence B S hS f :=
  fun F hF => isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS f hf F hF

end AlgebraicGeometry.Space

end
