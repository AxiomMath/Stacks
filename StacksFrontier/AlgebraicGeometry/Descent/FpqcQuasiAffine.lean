module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability

/-!
# Quasi-affine morphisms are fpqc local on the base

A morphism of schemes is quasi-affine if and only if its base change along the members of an fpqc
covering of the target is quasi-affine. This is Tag 02L7.

## Main results

* `Stacks.Descent.isQuasiAffine_of_isPullback_of_flat` is the descent step: over affine schemes
  `T ⟶ S` surjective and flat, a scheme over `S` whose base change to `T` is quasi-affine is
  itself quasi-affine.
* `Stacks.Descent.isQuasiAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact`: quasi-affine
  morphisms satisfy fpqc descent.
* `Stacks.Descent.isQuasiAffineHom_isLocalAtTarget_fpqc` is Tag 02L7.

## Implementation notes

The Stacks proof of Tag 02L7 realises a quasi-affine morphism as a quasi-compact open immersion
into the relative spectrum of `f_*𝒪_X` and descends that. The relative spectrum is not available,
but over an *affine* base `S` the relative spectrum of `f_*𝒪_X` is the absolute `Spec Γ(X, ⊤)`, and
Zariski locality on the target (`AlgebraicGeometry.isQuasiAffineHom_isZariskiLocalAtTarget`, part of
Tag 01SM) reduces the descent step to that case. So the proof below runs on the square
```
Spec Γ(Y', ⊤) ⟶ Spec Γ(T, ⊤)
      ↓               ↓
Spec Γ(Y, ⊤)  ⟶ Spec Γ(S, ⊤)
```
obtained by applying `Spec` to the flat base-change isomorphism
`Γ(Y', ⊤) = Γ(Y, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)` of
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, which is Tag 02KH for
global sections. That square is cartesian, so `Y'.toSpecΓ` is the base change of `Y.toSpecΓ` along
a surjective flat quasi-compact morphism, and being an open immersion descends along such
morphisms by Mathlib's Tag 02L3.

The flat base-change isomorphism needs `Y` to be quasi-compact and quasi-separated; both descend
by hand from `Y'` along the surjective quasi-compact morphism `Y' ⟶ Y`, since a quasi-compact open
of `Y` has quasi-compact preimage and `Y` is the image of `Y'`.

As in `StacksFrontier/AlgebraicGeometry/Descent/FpqcLocalAtTarget.lean`, instance synthesis cannot
solve for the affine-target parameter of `AlgebraicGeometry.HasAffineProperty`, so the Zariski
locality and base-change stability of quasi-affine morphisms are supplied as explicit `have`s.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02L3](https://stacks.math.columbia.edu/tag/02L3)
* [Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- The whole space is contained in the preimage of the whole space. -/
private lemma top_le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  f.preimage_top.ge

/-- **The descent step for Tag 02L7.** Let `T ⟶ S` be a surjective flat morphism of affine
schemes and let `Y` be a scheme over `S`. If the base change `Y'` of `Y` to `T` is quasi-affine,
then so is `Y`. -/
theorem isQuasiAffine_of_isPullback_of_flat {Y' Y T S : Scheme.{u}} [IsAffine T] [IsAffine S]
    {p : Y' ⟶ Y} {q : Y' ⟶ T} {g : Y ⟶ S} {f : T ⟶ S} (H : IsPullback p q g f)
    [Surjective f] [Flat f] (h : Scheme.IsQuasiAffine Y') : Scheme.IsQuasiAffine Y := by
  have := h
  have hbc := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  obtain ⟨⟨_, _⟩, _⟩ := hbc.of_isPullback H.flip
    (⟨⟨‹_›, ‹_›⟩, quasiCompact_of_compactSpace f⟩ :
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f)
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
  -- Flat base change for global sections, Tag 02KH, in the form of a pushout of rings.
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H) (US := ⊤)
    (UT := ⊤) (UX := ⊤) (UY := ⊤) (hUST := top_le_preimage_top f)
    (hUSX := top_le_preimage_top g) (hUY := by simp)
    (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ isQuasiSeparated_univ
  have hpush := (isIso_pushoutSection_iff H (top_le_preimage_top f) (top_le_preimage_top g)
    (by simp : (⊤ : Y'.Opens) = _)).mp hiso
  rw [appLE_top_top, appLE_top_top, appLE_top_top, appLE_top_top] at hpush
  -- Applying `Spec` turns it into a cartesian square of affine schemes.
  have hsq : IsPullback (Spec.map q.appTop) (Spec.map p.appTop) (Spec.map f.appTop)
      (Spec.map g.appTop) := hpush.op.map Scheme.Spec
  -- `Spec Γ(f)` is surjective, flat and quasi-compact, hence so is its base change `Spec Γ(p)`.
  have hsf : Flat (Spec.map f.appTop) ∧ Surjective (Spec.map f.appTop) :=
    (flat_and_surjective_SpecMap_iff f.appTop).mpr
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := f)).mp ⟨‹Flat f›, ‹_›⟩)
  have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map f.appTop) :=
    ⟨⟨hsf.2, hsf.1⟩, quasiCompact_of_compactSpace _⟩
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map p.appTop) :=
    hbc.of_isPullback hsq hf
  -- The canonical morphisms to the spectra of global sections form a cartesian square.
  have hnat : (q ≫ T.toSpecΓ) = Y'.toSpecΓ ≫ Spec.map q.appTop := Scheme.toSpecΓ_naturality q
  have hnat' : (g ≫ S.toSpecΓ) = Y.toSpecΓ ≫ Spec.map g.appTop := Scheme.toSpecΓ_naturality g
  have houter : IsPullback (Y'.toSpecΓ ≫ Spec.map q.appTop) p (Spec.map f.appTop)
      (Y.toSpecΓ ≫ Spec.map g.appTop) := by
    rw [← hnat, ← hnat']
    exact H.flip.paste_horiz
      (IsPullback.of_horiz_isIso (CommSq.mk (Scheme.toSpecΓ_naturality f).symm))
  have hmain : IsPullback Y'.toSpecΓ p (Spec.map p.appTop) Y.toSpecΓ :=
    houter.of_right (Scheme.toSpecΓ_naturality p).symm hsq
  -- Being an open immersion descends, Tag 02L3.
  have : IsOpenImmersion Y.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion) hmain hp inferInstance
  exact ⟨⟩

/-- **Stacks Project, Tag 02L7.** Quasi-affine morphisms satisfy fpqc descent: if the base change
of `g` along a surjective flat quasi-compact morphism is quasi-affine, then so is `g`. -/
@[stacks 02L7 "the descent step"]
instance isQuasiAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsQuasiAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isQuasiAffineHom_isZariskiLocalAtTarget.{u}
  have := isQuasiAffineHom_isStableUnderBaseChange.{u}
  have := isStableUnderBaseChange_surjective_inf_flat.{u}
  have := isStableUnderComposition_surjective_inf_flat.{u}
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsQuasiAffineHom
    (@Surjective ⊓ @Flat) isLocalIso_inf_surjective_le_surjective_inf_flat ?_
  intro R S Y φ g hφ hfst
  obtain ⟨hs, hfl⟩ := hφ
  have _ : Surjective (Spec.map φ) := hs
  have _ : Flat (Spec.map φ) := hfl
  rw [isQuasiAffineHom_iff_isQuasiAffine] at hfst ⊢
  exact isQuasiAffine_of_isPullback_of_flat
    (IsPullback.of_hasPullback (Spec.map φ) g).flip hfst

/-- **Stacks Project, Tag 02L7.** Being a quasi-affine morphism of schemes is fpqc local on the
base. -/
@[stacks 02L7, sga "4 IV 8.5.5"]
instance isQuasiAffineHom_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsQuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isQuasiAffineHom_isZariskiLocalAtTarget.{u}
  have := isQuasiAffineHom_isStableUnderBaseChange.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsQuasiAffineHom : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
