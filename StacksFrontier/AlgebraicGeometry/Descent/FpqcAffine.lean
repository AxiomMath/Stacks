module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local

/-!
# Affine morphisms are fpqc local on the base

A morphism of schemes is affine if and only if its base change along the members of an fpqc
covering of the target is affine.

## Main results

* `Stacks.Descent.isPullback_SpecMap_appTop_of_isPullback_of_flat`: flat base change for global
  sections, read as a cartesian square of affine schemes.
* `Stacks.Descent.isPullback_toSpecΓ_of_isPullback_of_flat`: the canonical morphisms to the
  spectra of the rings of global sections form a cartesian square, so the upper one is a base
  change of the lower one.
* `Stacks.Descent.isAffine_of_isPullback_of_flat`: over affine schemes `T ⟶ S` surjective and
  flat, a scheme over `S` whose base change to `T` is affine is itself affine.
* `Stacks.Descent.isAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact`: affine
  morphisms satisfy fpqc descent.
* `Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc`: being affine is fpqc local on the base.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- Being affine is Zariski local on the target. -/
private alias isAffineHom_isZariskiLocalAtTarget :=
  Stacks.Morphisms.isAffineHom_isZariskiLocalAtTarget

variable {Y' Y T S : Scheme.{u}} [IsAffine T] [IsAffine S]
  {p : Y' ⟶ Y} {q : Y' ⟶ T} {g : Y ⟶ S} {f : T ⟶ S}

/-- Let `f : T ⟶ S` be a flat morphism of affine schemes and let `g : Y ⟶ S` be a morphism from a
quasi-compact quasi-separated scheme, with `Y'` the base change of `Y` to `T`. Then
`Γ(Y', ⊤) = Γ(Y, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`, so applying `Spec` to the global sections of the square
gives a cartesian square again. -/
theorem isPullback_SpecMap_appTop_of_isPullback_of_flat (H : IsPullback p q g f) [Flat f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPullback (Spec.map q.appTop) (Spec.map p.appTop) (Spec.map f.appTop)
      (Spec.map g.appTop) := by
  have hpush := (isIso_pushoutSection_iff H f.preimage_top.ge g.preimage_top.ge
    (by simp : (⊤ : Y'.Opens) = _)).mp
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H) (US := ⊤) (UT := ⊤)
        (UX := ⊤) (UY := ⊤) (hUST := f.preimage_top.ge) (hUSX := g.preimage_top.ge)
        (hUY := by simp) (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ
        isQuasiSeparated_univ)
  rw [appLE_top_top, appLE_top_top, appLE_top_top, appLE_top_top] at hpush
  exact hpush.op.map Scheme.Spec

/-- In the situation of `Stacks.Descent.isPullback_SpecMap_appTop_of_isPullback_of_flat`, the
canonical morphisms to the spectra of the rings of global sections form a cartesian square: the
morphism `Y'.toSpecΓ` is the base change of `Y.toSpecΓ` along `Spec Γ(p)`. -/
theorem isPullback_toSpecΓ_of_isPullback_of_flat (H : IsPullback p q g f) [Flat f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPullback Y'.toSpecΓ p (Spec.map p.appTop) Y.toSpecΓ := by
  have houter : IsPullback (Y'.toSpecΓ ≫ Spec.map q.appTop) p (Spec.map f.appTop)
      (Y.toSpecΓ ≫ Spec.map g.appTop) := by
    rw [← Scheme.toSpecΓ_naturality q, ← Scheme.toSpecΓ_naturality g]
    exact H.flip.paste_horiz
      (IsPullback.of_horiz_isIso (CommSq.mk (Scheme.toSpecΓ_naturality f).symm))
  exact houter.of_right (Scheme.toSpecΓ_naturality p).symm
    (isPullback_SpecMap_appTop_of_isPullback_of_flat H)

/-- Let `T ⟶ S` be a surjective flat morphism of affine schemes and let `Y` be a scheme over `S`.
If the base change `Y'` of `Y` to `T` is affine, then so is `Y`. -/
theorem isAffine_of_isPullback_of_flat (H : IsPullback p q g f) [Surjective f] [Flat f]
    (h : IsAffine Y') : IsAffine Y := by
  have _ : QuasiCompact f := quasiCompact_of_compactSpace f
  have _ : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) H.flip ‹_›
  have _ : Flat p := MorphismProperty.of_isPullback (P := @Flat) H.flip ‹_›
  have _ : QuasiCompact p := MorphismProperty.of_isPullback (P := @QuasiCompact) H.flip ‹_›
  have _ : CompactSpace Y := by
    constructor
    rw [← Set.image_univ_of_surjective p.surjective]
    exact CompactSpace.isCompact_univ.image p.continuous
  have _ : QuasiSeparatedSpace Y := by
    refine ⟨fun U V hU hU' hV hV' ↦ ?_⟩
    have hUV : IsCompact (p.base ⁻¹' U ∩ p.base ⁻¹' V) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage p.continuous)
        (QuasiCompact.isCompact_preimage (f := p) U hU hU') (hV.preimage p.continuous)
        (QuasiCompact.isCompact_preimage (f := p) V hV hV')
    rw [← Set.image_preimage_eq (U ∩ V) p.surjective, Set.preimage_inter]
    exact hUV.image p.continuous
  have hsf : Flat (Spec.map f.appTop) ∧ Surjective (Spec.map f.appTop) :=
    (flat_and_surjective_SpecMap_iff f.appTop).mpr
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := f)).mp ⟨‹Flat f›, ‹_›⟩)
  have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map f.appTop) :=
    ⟨⟨hsf.2, hsf.1⟩, quasiCompact_of_compactSpace _⟩
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map p.appTop) :=
    have : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u}) (@Surjective ⊓ @Flat) := .inf
    have : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := .inf
    MorphismProperty.of_isPullback (isPullback_SpecMap_appTop_of_isPullback_of_flat H) hf
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
    (isPullback_toSpecΓ_of_isPullback_of_flat H) hp h.affine⟩

/-- Affine morphisms satisfy fpqc descent: if the base change of `g` along a surjective flat
quasi-compact morphism is affine, then so is `g`. -/
@[stacks 02L5 "the descent step"]
instance isAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_isZariskiLocalAtTarget.{u}
  have : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u}) (@Surjective ⊓ @Flat) := .inf
  have : MorphismProperty.IsStableUnderComposition (C := Scheme.{u}) (@Surjective ⊓ @Flat) :=
    have := instIsMultiplicativeSchemeSurjective.{u}.toIsStableUnderComposition
    .inf
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsAffineHom
    (@Surjective ⊓ @Flat) (fun X Y k hk ↦ ?_) ?_
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
    exact ⟨hk.2, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ k hk.1⟩
  · intro R S Z φ k hφ hfst
    obtain ⟨hs, hfl⟩ := hφ
    have _ : Surjective (Spec.map φ) := hs
    have _ : Flat (Spec.map φ) := hfl
    have _ : IsAffineHom (pullback.fst (Spec.map φ) k) := hfst
    have _ : IsAffine (pullback (Spec.map φ) k) :=
      isAffine_of_isAffineHom (pullback.fst (Spec.map φ) k)
    have _ : IsAffine Z :=
      isAffine_of_isPullback_of_flat (IsPullback.of_hasPullback (Spec.map φ) k).flip ‹_›
    exact isAffineHom_of_isAffine k

/-- Being an affine morphism of schemes is fpqc local on the base. -/
@[stacks 02L5, sga "4 IV 8.5.5"]
instance isAffineHom_isLocalAtTarget_fpqc :
    (show MorphismProperty Scheme.{u} from @IsAffineHom).IsLocalAtTarget
      Scheme.fpqcPrecoverage :=
  have := isAffineHom_isZariskiLocalAtTarget.{u}
  have := isAffineHom_isStableUnderBaseChange.{u}
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
