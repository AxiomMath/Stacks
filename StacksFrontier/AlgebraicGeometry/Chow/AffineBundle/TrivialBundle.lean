module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity

/-!
# Globally trivial affine-space bundles

Being *globally* the projection of affine `r`-space — an isomorphism of the source with `𝔸^r_Y`
carrying the structure morphism of the latter to the given morphism — is the condition of
`Stacks.Chow.IsAffineSpaceBundle` with "Zariski-locally on the target" dropped. It is stable
under arbitrary base change, hence transportable along an isomorphism of arrows, and flat pullback
along such a morphism is surjective as soon as it is surjective along the projections of affine
space, the two differing by an isomorphism of the source.

Naming the trivializations of the devissage of Stacks 02TT through this predicate is what makes
them usable: that devissage restricts a bundle to an open subscheme `V₀` of its target and then to
an open subscheme `V` of `V₀`, and `(f ∣_ V₀) ∣_ V` is not syntactically the restriction of `f` to
an open subscheme of `Y` — it is isomorphic to one as an arrow, which is all that is needed here.

## Main definitions

* `Stacks.Chow.IsTrivialAffineSpaceBundle` — the morphism is the projection of affine `r`-space
  over its target, up to an isomorphism of its source.

## Main results

* `Stacks.Chow.isTrivialAffineSpaceBundle_of_isPullback` — a globally trivial bundle base changes
  to one.
* `Stacks.Chow.isTrivialAffineSpaceBundle_of_arrowIso` — being a globally trivial bundle transports
  along an isomorphism of arrows.
* `Stacks.Chow.isTrivialAffineSpaceBundle_morphismRestrict_preimage` — triviality of `f` over an
  open subscheme `W` of `Y` contained in `V₀` gives triviality of `f ∣_ V₀` over the
  corresponding open subscheme of `V₀`.
* `Stacks.Chow.flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle` — surjectivity of flat
  pullback along a globally trivial bundle.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- A morphism `f : X ⟶ Y` is a **globally trivial affine-space bundle of rank `r`** if there is
an isomorphism of `X` with affine `r`-space over `Y` carrying the structure morphism of the latter
to `f`. -/
def IsTrivialAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∃ e : X ≅ 𝔸(ULift.{u} (Fin r); Y), e.hom ≫ (𝔸(ULift.{u} (Fin r); Y) ↘ Y) = f

/-- The projection of affine `r`-space over a scheme is a globally trivial affine-space bundle of
rank `r`. -/
theorem isTrivialAffineSpaceBundle_affineSpaceOver (Y : Scheme.{u}) (r : ℕ) :
    IsTrivialAffineSpaceBundle (𝔸(ULift.{u} (Fin r); Y) ↘ Y) r :=
  ⟨Iso.refl _, Category.id_comp _⟩

/-- **A trivializing open subscheme of an affine-space bundle trivializes it globally.** This is
`Stacks.Chow.IsAffineSpaceBundle` read through the present predicate: the source of `f ∣_ U` is
`f^{-1}(U)`, so the two existential statements are the same. -/
theorem exists_isTrivialAffineSpaceBundle_morphismRestrict {X Y : Scheme.{u}} {f : X ⟶ Y} {r : ℕ}
    (h : IsAffineSpaceBundle f r) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ IsTrivialAffineSpaceBundle (f ∣_ U) r :=
  h y

/-- **A globally trivial affine-space bundle base changes to a globally trivial affine-space
bundle.** In a cartesian square with `f` trivial, the base change `f'` is a base change of the
projection `𝔸^r_Y ⟶ Y`, which is the projection `𝔸^r_{Y'} ⟶ Y'` because affine space is stable
under base change. -/
theorem isTrivialAffineSpaceBundle_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback g' f' f g) (r : ℕ)
    (h : IsTrivialAffineSpaceBundle f r) : IsTrivialAffineSpaceBundle f' r := by
  obtain ⟨e, he⟩ := h
  have hiso : IsPullback e.hom f (𝔸(ULift.{u} (Fin r); Y) ↘ Y) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have hpaste : IsPullback (g' ≫ e.hom) f' (𝔸(ULift.{u} (Fin r); Y) ↘ Y) g := by
    have h2 := hsq.paste_horiz hiso
    rwa [Category.comp_id] at h2
  have hmap := AffineSpace.isPullback_map (n := ULift.{u} (Fin r)) g
  exact ⟨hpaste.isoIsPullback _ _ hmap, hpaste.isoIsPullback_hom_snd _ _ hmap⟩

/-- **Being a globally trivial affine-space bundle transports along an isomorphism of arrows.**
A square whose two horizontal legs are isomorphisms is cartesian. -/
theorem isTrivialAffineSpaceBundle_of_arrowIso {X Y X' Y' : Scheme.{u}} {g : X ⟶ Y}
    {g' : X' ⟶ Y'} (φ : Arrow.mk g ≅ Arrow.mk g') (r : ℕ)
    (h : IsTrivialAffineSpaceBundle g' r) : IsTrivialAffineSpaceBundle g r :=
  isTrivialAffineSpaceBundle_of_isPullback (f := g') (g := φ.hom.right) (g' := φ.hom.left)
    (f' := g) (IsPullback.of_horiz_isIso ⟨φ.hom.w⟩) r h

/-- **Triviality over an open subscheme passes to the bundle restricted to a larger open
subscheme.** If `W ≤ V₀` are open subschemes of `Y` and `f` is globally trivial over `W`, then
`f ∣_ V₀` is globally trivial over the open subscheme `V₀.ι^{-1}(W)` of `V₀`. -/
theorem isTrivialAffineSpaceBundle_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V₀ W : Y.Opens) (hW : W ≤ V₀) (r : ℕ) (h : IsTrivialAffineSpaceBundle (f ∣_ W) r) :
    IsTrivialAffineSpaceBundle ((f ∣_ V₀) ∣_ (V₀.ι ⁻¹ᵁ W)) r := by
  have himg : V₀.ι ''ᵁ (V₀.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  exact isTrivialAffineSpaceBundle_of_arrowIso
    (morphismRestrictRestrict f V₀ (V₀.ι ⁻¹ᵁ W) ≪≫ morphismRestrictEq f himg) r h

/-- **Surjectivity of flat pullback along a globally trivial affine-space bundle.** If flat
pullback along the projection of affine `r`-space is surjective over every base, then it is
surjective along every morphism that is such a projection up to an isomorphism of its source:
precomposing with an isomorphism does not change surjectivity, by
`Stacks.Chow.flatPullbackChow_surjective_of_isIso_comp`. -/
theorem flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle (C : ChowSituation.{u}) (r : ℕ)
    (htriv : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r
        (relativeDimension_affineSpaceOver B r) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f]
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (h : IsTrivialAffineSpaceBundle f r) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  obtain ⟨e, he⟩ := h
  have _ : IsIso e.hom := inferInstance
  exact flatPullbackChow_surjective_of_isIso_comp C (f ≫ sY)
    ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) sY e.hom (𝔸(ULift.{u} (Fin r); Y) ↘ Y) f he
    (by rw [← Category.assoc, he]) rfl rfl r (relativeDimension_affineSpaceOver Y r) hf k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (htriv Y sY k)

end Stacks.Chow

end
