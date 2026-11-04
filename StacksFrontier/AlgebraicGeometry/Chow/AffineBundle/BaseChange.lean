module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-!
# Base change of an affine-space bundle

A morphism `f : X ⟶ Y` is an affine-space bundle of rank `r`
(`Stacks.Chow.IsAffineSpaceBundle`) when it is Zariski-locally on `Y` the projection
`𝔸^r_U ⟶ U`. This file shows that the notion is stable under arbitrary base change, which is
what the devissage in the proof of Stacks 02TT needs: there the bundle is restricted to the
closures of points of the base and to open subschemes of those closures.

The local input is that a pullback of the projection `𝔸^r_T ⟶ T` along `h : U ⟶ T` is,
over `U`, isomorphic to the projection `𝔸^r_U ⟶ U`: Mathlib's
`AlgebraicGeometry.AffineSpace.isPullback_map` exhibits `𝔸^r_U` as such a pullback, and two
pullbacks of one cospan are isomorphic.

## Main results

* `Stacks.Chow.exists_iso_affineSpace_of_isPullback` — a pullback of the projection of affine
  space is isomorphic over the base to the projection of affine space.
* `Stacks.Chow.isAffineSpaceBundle_of_isPullback` — an affine-space bundle is stable under base
  change.
* `Stacks.Chow.isAffineSpaceBundle_morphismRestrict` — the restriction of an affine-space bundle
  to an open subscheme of its target is an affine-space bundle.
* `Stacks.Chow.isAffineSpaceBundle_comapRestrict` — the restriction of an affine-space bundle to
  the inverse image of a closed subscheme is an affine-space bundle.
* `Stacks.Chow.isAffineSpaceBundle_affineSpaceOver` — the projection of affine space is an
  affine-space bundle.
* `Stacks.Chow.quasiCompact_of_isAffineSpaceBundle` — an affine-space bundle is quasi-compact.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **A pullback of the projection of affine space is the projection of affine space.** If `g`
is the pullback of `𝔸^n_T ⟶ T` along `h : U ⟶ T`, then `g` is isomorphic over `U` to
`𝔸^n_U ⟶ U`. -/
theorem exists_iso_affineSpace_of_isPullback {n : Type u} {P U T : Scheme.{u}}
    {a : P ⟶ 𝔸(n; T)} {g : P ⟶ U} {h : U ⟶ T} (H : IsPullback a g (𝔸(n; T) ↘ T) h) :
    ∃ e : P ≅ 𝔸(n; U), e.hom ≫ (𝔸(n; U) ↘ U) = g :=
  ⟨H.isoIsPullback _ _ (AffineSpace.isPullback_map (n := n) h),
    IsPullback.isoIsPullback_hom_snd _ _ H (AffineSpace.isPullback_map (n := n) h)⟩

/-- **An affine-space bundle is stable under base change.** If `f'` is the pullback of an
affine-space bundle `f` of rank `r` along `h`, then `f'` is an affine-space bundle of rank `r`:
over the inverse image of a trivializing open `U` of `f`, the morphism `f'` is the pullback of
`f ∣_ U ≅ 𝔸^r_U ⟶ U` along `h ∣_ U`. -/
theorem isAffineSpaceBundle_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : X' ⟶ X} {h : Y' ⟶ Y} (H : IsPullback g f' f h) {r : ℕ}
    (hf : IsAffineSpaceBundle f r) : IsAffineSpaceBundle f' r := by
  intro y'
  obtain ⟨U, hyU, e, he⟩ := hf (h.base y')
  refine ⟨h ⁻¹ᵁ U, hyU, ?_⟩
  have hU := isPullback_morphismRestrict f U
  have hlift : (f' ∣_ (h ⁻¹ᵁ U) ≫ h ∣_ U) ≫ U.ι = ((f' ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) ≫ f := by
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, H.w]
  set a0 := hU.lift (f' ∣_ (h ⁻¹ᵁ U) ≫ h ∣_ U) ((f' ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) hlift with ha0
  have ha0fst : a0 ≫ f ∣_ U = f' ∣_ (h ⁻¹ᵁ U) ≫ h ∣_ U := hU.lift_fst _ _ _
  have ha0snd : a0 ≫ (f ⁻¹ᵁ U).ι = (f' ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g := hU.lift_snd _ _ _
  have hbig : IsPullback ((f' ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) (f' ∣_ (h ⁻¹ᵁ U)) f
      ((h ⁻¹ᵁ U).ι ≫ h) :=
    (isPullback_morphismRestrict f' (h ⁻¹ᵁ U)).flip.paste_horiz H
  have hbig' : IsPullback (a0 ≫ (f ⁻¹ᵁ U).ι) (f' ∣_ (h ⁻¹ᵁ U)) f (h ∣_ U ≫ U.ι) := by
    rw [ha0snd, morphismRestrict_ι]
    exact hbig
  have hsq : IsPullback a0 (f' ∣_ (h ⁻¹ᵁ U)) (f ∣_ U) (h ∣_ U) :=
    IsPullback.of_right hbig' ha0fst hU.flip
  have hiso : IsPullback e.hom (f ∣_ U) (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)
      (𝟙 U.toScheme) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have hall := hsq.paste_horiz hiso
  rw [Category.comp_id] at hall
  exact exists_iso_affineSpace_of_isPullback hall

/-- The restriction of an affine-space bundle to an open subscheme of its target is an
affine-space bundle of the same rank: the restriction square is cartesian. -/
theorem isAffineSpaceBundle_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {r : ℕ}
    (hf : IsAffineSpaceBundle f r) (V : Y.Opens) :
    IsAffineSpaceBundle (f ∣_ V) r :=
  isAffineSpaceBundle_of_isPullback (isPullback_morphismRestrict f V).flip hf

/-- The restriction of an affine-space bundle to the scheme-theoretic inverse image of a closed
subscheme of the base is an affine-space bundle of the same rank. -/
theorem isAffineSpaceBundle_comapRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {r : ℕ}
    (hf : IsAffineSpaceBundle f r) (W : Y.IdealSheafData) :
    IsAffineSpaceBundle (comapRestrict W f) r :=
  isAffineSpaceBundle_of_isPullback (isPullback_comapRestrict W f) hf

/-- The projection of affine `r`-space over a scheme is an affine-space bundle of rank `r`: over
any open `U` of the base its restriction is the pullback of the projection along `U ⟶ T`. -/
theorem isAffineSpaceBundle_affineSpaceOver (T : Scheme.{u}) (r : ℕ) :
    IsAffineSpaceBundle (𝔸(ULift.{u} (Fin r); T) ↘ T) r := fun _ ↦
  ⟨⊤, trivial, exists_iso_affineSpace_of_isPullback
    (isPullback_morphismRestrict (𝔸(ULift.{u} (Fin r); T) ↘ T) ⊤).flip⟩

/-- An affine-space bundle is quasi-compact: the projection of affine space is affine, hence
quasi-compact, and quasi-compactness is Zariski-local on the target. -/
theorem quasiCompact_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) : QuasiCompact f :=
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget (@QuasiCompact.{u}) _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  morphismProperty_of_isAffineSpaceBundle @QuasiCompact.{u} f r (fun _ ↦ inferInstance) h

end Stacks.Chow

end
