module

public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence descends along a finite-order thickening

Let `i : X ⟶ X'` be a finite-order thickening of schemes, that is, a closed immersion whose
kernel ideal sheaf is nilpotent, and let `K'` be an object of `D(𝒪_{X'})` whose derived pullback
`Li^*K'` is pseudo-coherent. Then `K'` is itself pseudo-coherent.

## Main results

* `Stacks.Thickenings.isPseudoCoherent_of_derivedPullback`: an object of `D(𝒪_{X'})` whose
  derived pullback along a finite-order thickening `i : X ⟶ X'` is pseudo-coherent is
  pseudo-coherent. No hypothesis beyond the tag's own.

## How the two halves meet

The tag's content splits exactly as the source splits it. The affine case over a surjection of
rings with nilpotent kernel is
`Stacks.Thickenings.isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent` of
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningAffine`, which rests on the
nilpotent-lifting criterion of [Stacks, Tag 0H76]. Its quasi-coherence hypothesis — the first
paragraph of the source's proof, which establishes `K' ∈ D_QCoh` — is discharged by
`Stacks.Thickenings.isQuasicoherent_homology_of_isPseudoCoherent_derivedPullback_specMap` of
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent`, which runs the
dévissage on the square-zero filtration. So nothing is granted here.

## Implementation notes

Pseudo-coherence is a local condition on the base — this is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict` — and a thickening of an
affine scheme is affine, so the statement reduces to the affine case: a surjection of rings
`R ⟶ S` with nilpotent kernel, where it is
`Stacks.Thickenings.isPseudoCoherent_of_derivedPullback_specMap` and rests on the
nilpotent-lifting criterion `StacksDraft.Perfect.isPseudoCoherent_derivedExtensionScalars_iff`
of [Stacks, Tag 0H76].

The reduction here is not the source's. The source first shows that `K'` has quasi-coherent
cohomology, by filtering the kernel ideal into square-zero steps and identifying the resulting
distinguished triangle with the projection formula of [Stacks, Tag 0B55] at each step; only then
does it work affine-locally. Because pseudo-coherence is local and is preserved by arbitrary
derived pullback ([Stacks, Tag 09U7], here
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback`), the
conclusion can instead be transported back from an affine chart directly: the chart `Spec Γ(X', U)`
of an affine open `U` of `X'` is compared with `U` along `AlgebraicGeometry.IsAffineOpen.isoSpec`,
whose two directions give the two halves of
`Stacks.Thickenings.isPseudoCoherent_of_derivedPullback_comp`, and the hypothesis is moved to the
chart along the commutative square `Spec Γ(X', U) ← Spec Γ(X, i⁻¹U)` over `i`. So nothing about
quasi-coherent cohomology, and no projection formula, is needed at the level of schemes; that
part of the argument is confined to the affine case.

The nilpotence of the kernel of `i.app U` is read off from the vanishing of a power of the kernel
ideal sheaf through `AlgebraicGeometry.Scheme.Hom.ker_apply`, which needs `i` quasi-compact, and
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow`.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, the model in which the
derived pullback and its coherences are built; the local instance carries a high priority because
the import closure also supplies the locally small model.

## References

* [Stacks Project, Tag 0DJX](https://stacks.math.columbia.edu/tag/0DJX)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Tag 0H76](https://stacks.math.columbia.edu/tag/0H76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Thickenings

/-- Equal morphisms of ringed spaces have the same derived pullback. -/
private def derivedPullbackEqIso {X Y : RingedSpace.{u, u}} {f g : X ⟶ Y} (h : f = g)
    (E : DerivedCategory (OXMod.{u, u} Y)) :
    (derivedPullback f).obj E ≅ (derivedPullback g).obj E :=
  eqToIso (congrArg (fun k : X ⟶ Y => (derivedPullback k).obj E) h)

/-- The two derived pullbacks around a commutative square of ringed spaces agree. -/
private def derivedPullbackSquareIso {V W Y Z : RingedSpace.{u, u}}
    (p : W ⟶ Y) (q : W ⟶ Z) (a : Y ⟶ V) (b : Z ⟶ V) (h : p ≫ a = q ≫ b)
    (E : DerivedCategory (OXMod.{u, u} V)) :
    (derivedPullback p).obj ((derivedPullback a).obj E) ≅
      (derivedPullback q).obj ((derivedPullback b).obj E) :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).app E ≪≫
    derivedPullbackEqIso h E ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical q b).app E).symm

/-- Pulling back along a split morphism of ringed spaces and then along a section changes
nothing. -/
private def derivedPullbackSectionIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : g ≫ f = 𝟙 Y) (E : DerivedCategory (OXMod.{u, u} Y)) :
    (derivedPullback g).obj ((derivedPullback f).obj E) ≅ E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g f).app E ≪≫
    derivedPullbackEqIso hgf E ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso Y).app E

/-- **Pseudo-coherence is reflected by derived pullback along a split morphism of ringed
spaces**, in particular along an isomorphism. -/
private theorem isPseudoCoherent_of_derivedPullback_section {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y) (E : DerivedCategory (OXMod.{u, u} Y))
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X)
      ((derivedPullback f).obj E)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := Y) E :=
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback g _
    h).of_iso (derivedPullbackSectionIso f g hgf E)

/-- **Pseudo-coherence descends along a split morphism of ringed spaces**: if `f : X ⟶ Y` has a
section `g` and the derived pullback of `E` to `X` along `f ≫ h` is pseudo-coherent, then its
derived pullback to `Y` along `h` is pseudo-coherent. -/
private theorem isPseudoCoherent_of_derivedPullback_comp {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y) (h : Y ⟶ Z)
    (E : DerivedCategory (OXMod.{u, u} Z))
    (hE : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X)
      ((derivedPullback (f ≫ h)).obj E)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := Y)
      ((derivedPullback h).obj E) :=
  isPseudoCoherent_of_derivedPullback_section f g hgf _
    (hE.of_iso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f h).app E).symm)

/-- **Pseudo-coherence descends along a finite-order thickening of schemes.** Let `i : X ⟶ X'` be
a closed immersion whose kernel ideal sheaf is nilpotent and let `K'` be an object of `D(𝒪_{X'})`
such that `K = Li^*K'` is pseudo-coherent. Then `K'` is pseudo-coherent.

Pseudo-coherence of `K'` is a local condition on `X'`, so it is enough to produce it over an
affine open `U` of `X'`. Over the chart `Spec Γ(X', U)` the thickening becomes `Spec` of the
surjection `i.app U`, whose kernel is nilpotent because a power of the kernel ideal sheaf
vanishes; the hypothesis travels to that chart because derived pullback preserves
pseudo-coherence and the two ways around the square `Spec Γ(X', U) ← Spec Γ(X, i⁻¹U)` over `i`
agree. The affine case then applies, and its conclusion comes back to `U` along
`AlgebraicGeometry.IsAffineOpen.isoSpec`, again by preservation of pseudo-coherence under derived
pullback, this time along the inverse. -/
@[stacks 0DJX "the whole statement, unconditionally: pseudo-coherence of K' in D(𝒪_{X'}) from \
pseudo-coherence of Li^*K', for a finite-order thickening i : X ⟶ X' of schemes, at the \
standard derived category", sga "6 I 2.16.2" "(i), special case"]
theorem isPseudoCoherent_of_derivedPullback {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsFiniteOrderThickening i)
    (K' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      ((derivedPullback i.toLRSHom.toShHom).obj K')) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X'.toRingedSpace) K' := by
  have : IsClosedImmersion i := hi.1
  have : IsAffineHom i := (isClosedImmersion_iff_isAffineHom.mp ‹_›).1
  refine (AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall K').2 fun m => ?_
  refine AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict K' m fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X') (U := ⊤) (Set.mem_univ x)
  refine ⟨U, hxU, ?_⟩
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hf : Function.Surjective (i.app U).hom := i.app_surjective U hU
  have hn : IsNilpotent (RingHom.ker (i.app U).hom) := by
    obtain ⟨n, hn⟩ := hi.2
    refine ⟨n + 1, ?_⟩
    have he := congrArg (fun I : X'.IdealSheafData => I.ideal ⟨U, hU⟩) hn
    simpa [Scheme.IdealSheafData.ideal_pow, Scheme.Hom.ker_apply] using he
  have hsq : Spec.map (i.app U) ≫ hU.fromSpec = hV.fromSpec ≫ i := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      IsAffineOpen.SpecMap_appLE_fromSpec i hU hV le_rfl
  have hsq' : (Spec.map (i.app U)).toLRSHom.toShHom ≫ hU.fromSpec.toLRSHom.toShHom =
      hV.fromSpec.toLRSHom.toShHom ≫ i.toLRSHom.toShHom :=
    congrArg (fun f => (Scheme.Hom.toLRSHom f).toShHom) hsq
  -- the affine model of `K'` over `U`
  have hpcV : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := (Spec Γ(X, i ⁻¹ᵁ U)).toRingedSpace)
      ((derivedPullback hV.fromSpec.toLRSHom.toShHom).obj
        ((derivedPullback i.toLRSHom.toShHom).obj K')) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback _ _ hK
  have hiso : (derivedPullback (Spec.map (i.app U)).toLRSHom.toShHom).obj
        ((derivedPullback hU.fromSpec.toLRSHom.toShHom).obj K') ≅
      (derivedPullback hV.fromSpec.toLRSHom.toShHom).obj
        ((derivedPullback i.toLRSHom.toShHom).obj K') :=
    derivedPullbackSquareIso _ _ _ _ hsq' K'
  have hpcV' := hpcV.of_iso hiso.symm
  have hAff : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := (Spec Γ(X', U)).toRingedSpace)
      ((derivedPullback hU.fromSpec.toLRSHom.toShHom).obj K') :=
    isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent (i.app U) hf hn _
      (isQuasicoherent_homology_of_isPseudoCoherent_derivedPullback_specMap (i.app U) hf hn _
        hpcV')
      hpcV'
  -- transport it back to `U`
  have hsec : hU.isoSpec.hom.toLRSHom.toShHom ≫ hU.isoSpec.inv.toLRSHom.toShHom =
      𝟙 U.toScheme.toRingedSpace :=
    congrArg (fun f => (Scheme.Hom.toLRSHom f).toShHom)
      hU.isoSpec.hom_inv_id
  have hfs : hU.isoSpec.inv.toLRSHom.toShHom ≫ U.ι.toLRSHom.toShHom =
      hU.fromSpec.toLRSHom.toShHom := rfl
  have hOpen : AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := U.toScheme.toRingedSpace) ((derivedPullback U.ι.toLRSHom.toShHom).obj K') :=
    isPseudoCoherent_of_derivedPullback_comp hU.isoSpec.inv.toLRSHom.toShHom
      hU.isoSpec.hom.toLRSHom.toShHom hsec U.ι.toLRSHom.toShHom K'
      (hAff.of_iso (derivedPullbackEqIso hfs.symm K'))
  exact ((AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall
    ((derivedPullback U.ι.toLRSHom.toShHom).obj K')).1 hOpen m).of_iso
      ((Scheme.Modules.derivedRestrictModulesIsoDerivedPullback X' U).app K').symm

end Stacks.Thickenings

end
