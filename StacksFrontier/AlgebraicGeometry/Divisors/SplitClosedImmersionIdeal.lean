module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The reduced structure on the image of a retracted closed immersion

Let `s : X ⟶ Y` be a closed immersion which admits a retraction, that is, a morphism
`p : Y ⟶ X` with `s ≫ p = 𝟙 X`; the basic example is a section of a morphism `Y ⟶ X`, viewed as
a closed immersion when `Y ⟶ X` is separated. The closed subscheme `s(X) ⊆ Y` carries two
closed subscheme structures: the scheme-theoretic image, cut out by the kernel ideal sheaf
`AlgebraicGeometry.Scheme.Hom.ker s`, and the reduced induced structure, cut out by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`. They differ exactly by the nilpotents
of `Y`, and this file proves that: the vanishing ideal of the image is the kernel together with
the nilradical of `Y`.

The consequence this is built for: on a *reduced* scheme the two structures have the same inverse
image. So for any `ι : W ⟶ Y` with `W` reduced the scheme-theoretic preimage of the reduced
induced structure on `s(X)` agrees with that of the scheme-theoretic image, and the former
inherits every local property of the latter — local principality in particular.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.IdealSheaf.map_comap_of_isClosedImmersion`: the ideal correspondence for a closed
  immersion, `(J.comap s).map s = J ⊔ s.ker`.
* `Stacks.IdealSheaf.comap_nilradical_of_split`: for a retracted closed immersion the inverse
  image of the nilradical of the target is the nilradical of the source.
* `Stacks.IdealSheaf.vanishingIdeal_closure_range_of_split`: the reduced induced structure on the
  image of a retracted closed immersion is cut out by `s.ker ⊔ Y.nilradical`.
* `Stacks.IdealSheaf.comap_vanishingIdeal_closure_range_of_split`: over a reduced scheme the
  reduced induced structure on the image and the scheme-theoretic image have the same inverse
  image.

## Implementation notes

Only the ideal correspondence needs to look at an affine open. It is the one step where the
closed immersion hypothesis is used as more than formal nonsense: on an affine open `U` of `Y`
the preimage `s⁻¹U` is affine, the ring map `Γ(Y, U) ⟶ Γ(X, s⁻¹U)` is surjective with kernel
`s.ker.ideal U`, and `Ideal.comap_map_of_surjective` is the whole content. The two ingredients
are `AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_of_isAffineHom` and
`Stacks.IdealSheaf.ideal_comap_appLE`, so no affine cover is built.

Everything else is formal. That the inverse image of a nilradical lies in the nilradical is the
Galois connection `AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le` together with
`AlgebraicGeometry.Scheme.IdealSheafData.map_vanishingIdeal`, since the nilradical is the
vanishing ideal of the whole space; the reverse inclusion for a retracted `s` is functoriality of
`comap` along `s ≫ p = 𝟙`. The retraction is essential and not decoration: for the closed
immersion `Spec k[t]/(t²) ⟶ Spec k[t]`, whose kernel is `(t²)`, the vanishing ideal of the image
is `(t)` while the kernel together with the nilradical is `(t²)`.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.IdealSheaf

/-- The inverse image of the nilradical of the target is contained in the nilradical of the
source: a nilpotent section pulls back to a nilpotent section. -/
theorem nilradical_comap_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.nilradical.comap f ≤ X.nilradical := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.vanishingIdeal_top (X := X),
    Scheme.IdealSheafData.map_vanishingIdeal,
    ← Scheme.IdealSheafData.vanishingIdeal_top (X := Y)]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono le_top

/-- If `s : X ⟶ Y` admits a retraction `p`, the nilradical of `X` is the inverse image of the
nilradical of `Y`. -/
theorem comap_nilradical_of_split {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    (hsp : s ≫ p = 𝟙 X) : Y.nilradical.comap s = X.nilradical := by
  refine le_antisymm (nilradical_comap_le s) ?_
  calc X.nilradical = (X.nilradical.comap p).comap s := by
        rw [← Scheme.IdealSheafData.comap_comp, hsp, Scheme.IdealSheafData.comap_id]
    _ ≤ Y.nilradical.comap s :=
        Scheme.IdealSheafData.comap_mono (f := s) (nilradical_comap_le p)

/-- **The ideal correspondence for a closed immersion.** Pushing an inverse image forward again
recovers the original ideal sheaf together with the kernel of the closed immersion. -/
theorem map_comap_of_isClosedImmersion {X Y : Scheme.{u}} (s : X ⟶ Y) [IsClosedImmersion s]
    (J : Y.IdealSheafData) : (J.comap s).map s = J ⊔ s.ker := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  have hsurj : Function.Surjective ((s.app (U : Y.Opens)).hom) :=
    Scheme.Hom.app_surjective s (U : Y.Opens) U.2
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Stacks.IdealSheaf.ideal_comap_appLE J s U ⟨s ⁻¹ᵁ (U : Y.Opens), U.2.preimage s⟩ le_rfl,
    Scheme.Hom.appLE_eq_app, Ideal.comap_map_of_surjective _ hsurj,
    ← RingHom.ker_eq_comap_bot, ← Scheme.Hom.ker_apply s U]
  rfl

/-- The reduced induced structure on the image of a closed immersion is cut out by the pushforward
of the nilradical of the source. -/
theorem vanishingIdeal_closure_range {X Y : Scheme.{u}} (s : X ⟶ Y) :
    Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (Set.range s), isClosed_closure⟩ : Closeds Y) =
      X.nilradical.map s := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_top (X := X),
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext x
  simp

/-- **The reduced induced structure on the image of a retracted closed immersion.** It is cut out
by the kernel of the closed immersion together with the nilradical of the target. -/
theorem vanishingIdeal_closure_range_of_split {X Y : Scheme.{u}} (s : X ⟶ Y)
    [IsClosedImmersion s] (p : Y ⟶ X) (hsp : s ≫ p = 𝟙 X) :
    Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (Set.range s), isClosed_closure⟩ : Closeds Y) =
      Y.nilradical ⊔ s.ker := by
  rw [vanishingIdeal_closure_range s, ← comap_nilradical_of_split s p hsp,
    map_comap_of_isClosedImmersion]

/-- **Over a reduced scheme the scheme-theoretic image and the reduced induced structure on the
image of a retracted closed immersion have the same inverse image.** -/
theorem comap_vanishingIdeal_closure_range_of_split {X Y W : Scheme.{u}} (s : X ⟶ Y)
    [IsClosedImmersion s] (p : Y ⟶ X) (hsp : s ≫ p = 𝟙 X) (ι : W ⟶ Y) [IsReduced W] :
    (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (Set.range s), isClosed_closure⟩ : Closeds Y)).comap ι =
      s.ker.comap ι := by
  have hnil : Y.nilradical.comap ι = ⊥ :=
    le_bot_iff.mp (Scheme.nilradical_eq_bot (X := W) ▸ nilradical_comap_le ι)
  rw [vanishingIdeal_closure_range_of_split s p hsp, Scheme.IdealSheafData.comap_sup, hnil,
    bot_sup_eq]

end Stacks.IdealSheaf

end
