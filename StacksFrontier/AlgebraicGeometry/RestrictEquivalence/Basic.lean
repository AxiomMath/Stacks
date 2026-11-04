module

public import StacksFrontier.AlgebraicGeometry.AffineQcohRestriction.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the quasi-inverse of Stacks Tag 01SB

Let `f : X ⟶ S` be an affine morphism of schemes and `A = f_* 𝒪_X`.  The quasi-inverse
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f` of Stacks Tag 01SB carries a
quasi-coherent `A`-module to a quasi-coherent `𝒪_X`-module.  This is the first of the three
hypotheses of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`,
the hypothesis called `hL` there.

## Main results

* `Stacks.AlgebraicGeometry.RestrictEquivalence.presentationOfIsoSpec`: **on an affine scheme a
  module over a quasi-coherent algebra which is quasi-coherent after restriction of scalars has
  a global presentation.**  This is the open-subscheme counterpart of
  `Stacks.AlgebraicGeometry.QcohLimits.presentationOverAffine`, which produces a presentation on
  the slice site instead.
* `Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_restrictOver`: **restriction to
  an open preserves quasi-coherence of modules over a quasi-coherent algebra**, for an arbitrary
  quasi-coherent `𝒪_S`-algebra `A`.
* `Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pullbackModules`: the
  hypothesis `hL`.

## The transport route, and why it is needed

Quasi-coherence of `(pullbackModules f).obj G` is local on `X`, and `X` is covered by the
inverse images of the affine opens of `S`, all of them affine because `f` is.  Over such an
open the restriction of `(pullbackModules f).obj G` is identified with the quasi-inverse at the
restricted morphism applied to the restriction of `G`, by
`Stacks.AlgebraicGeometry.AffineQcohRestriction.leftSquare`.  The restricted morphism is a
morphism of affine schemes, so `presentationOfIsoSpec` gives the restriction of `G` a global
presentation there, and
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules_of_presentation`
applies.

Two transports are needed to make that run, and both are forced by a mismatch of spellings
rather than by mathematics.

The first is across
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictPushforwardRing_eq`, which says that
the restriction of `A` to an open `V` and the direct image of `𝒪_U` along the restricted
morphism are **equal** sheaves of rings.  The equality is not definitional — the underlying
identity of opens needs `inf_eq_right` — so the two categories of modules, although the same
type, are not interchangeable to the elaborator.  The repair used here is the one recorded in
`StacksFrontier/AlgebraicGeometry/RelativeSpecFinish/Restriction.lean` and carried out in
`StacksFrontier/AlgebraicGeometry/AffineQcohRestriction/Basic.lean`: the retyped
restriction functor is the direct image along
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`, which **is** the transport
of the identity by `restrictCompareRing_eq_eqToHom`.  Quasi-coherence is then carried across it
by generalising the target sheaf of rings and substituting the equality, which turns the
transport into an identity functor; this is the `key` step inside
`isQuasicoherent_pushforward_restrictCompareRing`.

The second is between `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver` at the
structure sheaf and Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  These are
*not* equal: `restrictFunctor` is a direct image along the inverse of
`AlgebraicGeometry.Scheme.Hom.appIso`, while `restrictOver` uses the identity.  For the
inclusion of an open subscheme that inverse is the identity
(`AlgebraicGeometry.Scheme.Opens.ι_appIso`), so `restrictOverIso` identifies them by a single
`SheafOfModules.pushforwardCongr`.  It cannot be an equality, because `Iso.inv` is not exposed
and the comparison does not hold by `rfl`.

## Universe situation

Everything is at a single universe `u`: the schemes are `Scheme.{u}`, the sheaves of rings are
`RingCat.{u}`-valued, and the modules are `SheafOfModules.{u}`.  No universe is left free.  The
index type of the covering is `S.affineOpens`, which is in `Type u`, and the index types of the
generating families produced by `presentationOfIsoSpec` are in `Type u` as well, so the
colimit-preservation hypotheses are needed only at `Type u`.

## Transparency gotchas

Three instances that one would expect instance search to find have to be supplied by hand.

* `(SheafOfModules.restrictScalars β).PreservesZeroMorphisms` is not found, and neither is the
  `Additive` instance Mathlib has, from which it would follow: the goal elaborates the two
  `Preadditive` arguments of that class by a route along which instance search does not match
  it.  The class carries no data beyond an equation that holds by `rfl`, so it is constructed
  directly.
* `PreservesColimitsOfShape (Discrete I) (SheafOfModules.restrictScalars β)` is an instance, but
  its shape universes cannot be determined from the goal; it is named explicitly.
* `PreservesLimit (parallelPair _ 0) (SheafOfModules.restrictScalars β)` is extracted from
  `PreservesFiniteLimits` by hand for the same reason.

`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` is stated for
`AlgebraicGeometry.Scheme.Modules`, whose `Category` instance is a different instance from the
one on `SheafOfModules`, so its two quasi-coherence arguments are passed positionally rather
than found by instance search.

`Topology.IsOpenEmbedding.functor_isContinuous` is a lemma rather than an instance and is needed
to state the restriction of a sheaf at all, so it is a section-confined local instance, as in
the two files this one builds on.

## What is not done

**This file does not prove the equivalence assertion of [Stacks, Tag 01SB]**, and no Stacks tag
attribute is attached to anything here.  It supplies the hypothesis `hL`
only.  The remaining two hypotheses of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
are untouched, and they are not of the same kind: `hL` is a closure property, whereas `hunit`
and `hcounit` ask for the invertibility of a specific morphism.  Reducing those to the affine
case would need, beyond `leftSquare`, a compatibility of the unit and the counit with that
square, and then the affine statement itself — for which nothing is available: the unit and the
counit of `SheafOfModules.pullbackPushforwardAdjunction` have no component formula, the
adjunction being produced by `CategoryTheory.Adjunction.ofIsRightAdjoint`, and no form of the
equivalence of Tag 01SB over an affine base is proved anywhere.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.RestrictEquivalence

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohRestriction

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

/-! ### A global presentation on an affine scheme -/

section Presentation

variable {T : Scheme.{u}} {B : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  (β : T.ringCatSheaf ⟶ B)

/-- Restriction of scalars along a morphism of sheaves of rings on a scheme preserves zero
morphisms.  Mathlib's `Additive` instance, from which this would follow, is not matched by
instance search at this spelling, so the equation is checked directly. -/
theorem preservesZeroMorphisms_restrictScalars :
    (SheafOfModules.restrictScalars.{u} β).PreservesZeroMorphisms :=
  ⟨fun {_ _} ↦ rfl⟩

/-- **On an affine scheme a module over a quasi-coherent algebra which is quasi-coherent after
restriction of scalars has a global presentation.**  Generators come from a presentation of the
restriction of scalars, transferred by
`Stacks.AlgebraicGeometry.QcohOverAlgebra.generatingSectionsOfRestrictScalars`; the relations
come from the same construction applied to the kernel, which is quasi-coherent because
restriction of scalars preserves kernels and a kernel of a morphism of quasi-coherent modules is
quasi-coherent. -/
@[ega "II 1.4.3" "direction"]
def presentationOfIsoSpec {R : CommRingCat.{u}} (e : T ≅ Spec R)
    (hB : ((SheafOfModules.restrictScalars.{u} β).obj (SheafOfModules.unit B)).IsQuasicoherent)
    (N : SheafOfModules.{u} B)
    (hN : ((SheafOfModules.restrictScalars.{u} β).obj N).IsQuasicoherent) :
    N.Presentation := by
  have _hN := hN
  have _hz : (SheafOfModules.restrictScalars.{u} β).PreservesZeroMorphisms :=
    preservesZeroMorphisms_restrictScalars β
  have _hc : ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.restrictScalars.{u} β) := fun I ↦
    RestrictScalarsColimits.preservesColimitsOfShape_restrictScalars β (Discrete I)
  have hfree : ∀ I : Type u,
      ((SheafOfModules.restrictScalars.{u} β).obj
        (SheafOfModules.free.{u} (R := B) I)).IsQuasicoherent := fun I ↦
    QuasicoherentColimits.isQuasicoherent_of_isColimit (fun _ ↦ hB)
      (isColimitOfPreserves (SheafOfModules.restrictScalars.{u} β)
        (SheafOfModules.isColimitFreeCofan I))
  set gen := QcohOverAlgebra.generatingSectionsOfRestrictScalars β
    (AffinePushforward.nonempty_presentation_of_isoSpec e
      ((SheafOfModules.restrictScalars.{u} β).obj N)).some.generators with hgen
  have hker : ((SheafOfModules.restrictScalars.{u} β).obj (kernel gen.π)).IsQuasicoherent := by
    have hk : (kernel ((SheafOfModules.restrictScalars.{u} β).map gen.π)).IsQuasicoherent :=
      @QcohLimits.isQuasicoherent_kernel T _ _ _ (hfree gen.I) hN
    have : PreservesLimit (parallelPair gen.π 0) (SheafOfModules.restrictScalars.{u} β) :=
      ((QcohOverAlgebra.preservesFiniteLimits_restrictScalars β).preservesFiniteLimits
        WalkingParallelPair).preservesLimit
    exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
      (PreservesKernel.iso (SheafOfModules.restrictScalars.{u} β) gen.π).symm hk
  exact { generators := gen
          relations := QcohOverAlgebra.generatingSectionsOfRestrictScalars β
            (AffinePushforward.nonempty_presentation_of_isoSpec e
              ((SheafOfModules.restrictScalars.{u} β).obj (kernel gen.π))).some.generators }

end Presentation

/-! ### Restriction to an open preserves quasi-coherence over an algebra -/

section Restriction

variable {S : Scheme.{u}} (V : S.Opens)
  {A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}} (α : S.ringCatSheaf ⟶ A)

/-- The restriction to an open `V` of a morphism of sheaves of rings on `S`.  Its source is
`𝒪_V`, because the restriction of the structure sheaf of `S` to `V` is the structure sheaf of
the open subscheme `V` on the nose. -/
abbrev restrictRingHom : (V : S.Opens).toScheme.ringCatSheaf ⟶ restrictRing V A :=
  ((opensImageFunctor V).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology (V : S.Opens)) (Opens.grothendieckTopology S)).map α

/-- Restricting to `V` and then restricting scalars is restricting scalars and then restricting
to `V`.  Both are direct images along the same site functor, and the square of morphisms of
sheaves of rings commutes by construction of `restrictRingHom`. -/
theorem restrictOver_comp_restrictScalars :
    restrictOver V A ⋙ SheafOfModules.restrictScalars.{u} (restrictRingHom V α) =
      SheafOfModules.restrictScalars.{u} α ⋙ restrictOver V S.ringCatSheaf :=
  rfl

/-- Restriction to an open carries the unit module to the unit module. -/
theorem restrictOver_obj_unit :
    (restrictOver V A).obj (SheafOfModules.unit A) =
      SheafOfModules.unit (restrictRing V A) :=
  rfl

/-- **Restriction of `𝒪_S`-modules to an open subscheme, in the direct-image spelling, agrees
with Mathlib's restriction functor.**  The two differ only in the morphism of sheaves of rings
they push forward along — the identity against the inverse of
`AlgebraicGeometry.Scheme.Hom.appIso` — and for the inclusion of an open subscheme that inverse
is the identity. -/
def restrictOverIso :
    restrictOver V S.ringCatSheaf ≅ Scheme.Modules.restrictFunctor V.ι :=
  SheafOfModules.pushforwardCongr (by
    ext : 3
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

/-- Restriction to an open preserves quasi-coherence of `𝒪_S`-modules, in the direct-image
spelling.  This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor` transported along
`restrictOverIso`. -/
theorem isQuasicoherent_restrictOver_structureSheaf (M : S.Modules) (hM : M.IsQuasicoherent) :
    ((restrictOver V S.ringCatSheaf).obj M).IsQuasicoherent :=
  have := hM
  (SheafOfModules.isQuasicoherent (V : S.Opens).toScheme.ringCatSheaf).prop_of_iso
    ((restrictOverIso V).app M).symm (Scheme.Modules.isQuasicoherent_restrictFunctor V.ι M)

/-- **Restriction to an open preserves quasi-coherence of modules over a quasi-coherent
algebra.**  Let `α : 𝒪_S ⟶ A` be a sheaf of rings on `S` which is quasi-coherent as an
`𝒪_S`-module.  The restriction to an open `V` of an `A`-module which is quasi-coherent as an
`𝒪_S`-module is quasi-coherent as an `A|_V`-module.  Both hypotheses are checked downstairs, so
Stacks Tag 0H88 on `V` turns the conclusion into the corresponding statement for
`𝒪_S`-modules. -/
theorem isQuasicoherent_restrictOver
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    (G : SheafOfModules.{u} A)
    (hG : ((SheafOfModules.restrictScalars.{u} α).obj G).IsQuasicoherent) :
    ((restrictOver V A).obj G).IsQuasicoherent :=
  (QcohLimits.isQuasicoherent_restrictScalars_iff (restrictRingHom V α)
      (isQuasicoherent_restrictOver_structureSheaf V _ hA) _).mp
    (isQuasicoherent_restrictOver_structureSheaf V _ hG)

end Restriction

/-! ### The hypothesis `hL` of Stacks Tag 01SB -/

section Main

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (V : S.Opens)

/-- The restriction of `G` to an open `V`, retyped as a module over the direct image of `𝒪_U`
along the restricted morphism, is quasi-coherent.  The retyping is the direct image along
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing`, which by
`restrictCompareRing_eq_eqToHom` is the transport of the identity across
`restrictPushforwardRing_eq`; generalising the target sheaf of rings and substituting that
equality turns the transport into
`Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver`. -/
theorem isQuasicoherent_pushforward_restrictCompareRing
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (hG : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent) :
    ((SheafOfModules.pushforward.{u} (restrictCompareRing f V)).obj G).IsQuasicoherent := by
  have key : ∀ (B : Sheaf (Opens.grothendieckTopology (V : S.Opens)) RingCat.{u})
      (hB : restrictRing V (pushforwardRing f.base X.ringCatSheaf) = B),
      ((SheafOfModules.pushforward.{u} (eqToHom hB.symm)).obj G).IsQuasicoherent := by
    rintro B rfl
    exact isQuasicoherent_restrictOver V f.toRingCatSheafHom
      (isQuasicoherent_restrictScalars_pushforwardRing f) G hG
  rw [restrictCompareRing_eq_eqToHom]
  exact key _ (restrictPushforwardRing_eq f V)

/-- **The hypothesis `hL` of Stacks Tag 01SB.**  For an affine morphism `f : X ⟶ S`, the
quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` carries a quasi-coherent `f_* 𝒪_X`-module to a
quasi-coherent `𝒪_X`-module. -/
theorem isQuasicoherent_pullbackModules
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (hG : G.IsQuasicoherent) :
    ((AffineQcohEquivalence.pullbackModules f).obj G).IsQuasicoherent := by
  have hqcG : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent :=
    have := hG
    QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules f G
  refine AffinePushforward.isQuasicoherent_of_presentations _
    (fun W : S.affineOpens ↦ f ⁻¹ᵁ (W : S.Opens)) (IsOpenCover.mk ?_) fun W ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top S, Scheme.Hom.preimage_top]
  · obtain ⟨W, hW⟩ := W
    have hU : IsAffineOpen (f ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have : IsAffine (f ⁻¹ᵁ W).toScheme := hU
    have : IsAffine (W : S.Opens).toScheme := hW
    have hNres : ((SheafOfModules.restrictScalars (resPreimage f W).toRingCatSheafHom).obj
        ((SheafOfModules.pushforward.{u} (restrictCompareRing f W)).obj G)).IsQuasicoherent :=
      have := isQuasicoherent_pushforward_restrictCompareRing f W G hqcG
      QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules (resPreimage f W) _
    have h2 := AffineQcohEquivalence.isQuasicoherent_pullbackModules_of_presentation
      (resPreimage f W) _ (presentationOfIsoSpec (resPreimage f W).toRingCatSheafHom hW.isoSpec
        (isQuasicoherent_restrictScalars_pushforwardRing (resPreimage f W)) _ hNres)
    have h4 := (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ W).toScheme.ringCatSheaf).prop_of_iso
      ((restrictOverIso (f ⁻¹ᵁ W)).app _)
      ((SheafOfModules.isQuasicoherent (f ⁻¹ᵁ W).toScheme.ringCatSheaf).prop_of_iso
        ((leftSquare f W).app G) h2)
    exact (AffinePushforward.nonempty_presentation_of_isoSpec hU.isoSpec _).some

end Main

end Stacks.AlgebraicGeometry.RestrictEquivalence

end

end
