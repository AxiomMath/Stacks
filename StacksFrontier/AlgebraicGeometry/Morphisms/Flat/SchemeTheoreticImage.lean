module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change of scheme-theoretic images

The scheme-theoretic image of a quasi-compact morphism of schemes commutes with flat base
change. Writing the morphism as a scheme-theoretically dominant map onto its image followed by
a closed immersion, flatness of the base change keeps the first factor scheme-theoretically
dominant, so its kernel stays trivial and the image of the base change is cut out by the
inverse image of the original ideal sheaf.

## Main results

* `AlgebraicGeometry.ker_pullback_snd_eq_comap` identifies the ideal sheaf defining the
  scheme-theoretic image after base change with the inverse image of the original defining
  ideal sheaf.
* `AlgebraicGeometry.isPullback_image_of_flat` restates that as the square of the two closed
  embeddings being cartesian, which is the form used downstream.

## Implementation notes

The scheme-theoretic image of a morphism `g` is the closed subscheme associated to `g.ker`.
Mathlib represents the inverse image of this closed subscheme by `g.ker.comap f`; its associated
scheme is canonically isomorphic to the fibre product via `IdealSheafData.comapIso`. Thus the
equality of ideal sheaves below is the equality of closed subschemes in the source, while
avoiding an equality between noncanonical choices of pullback objects.

## References

* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 081I.** The defining ideal sheaf of the scheme-theoretic image of a
quasi-compact morphism after flat base change is the inverse image of its defining ideal
sheaf. -/
@[stacks 081I, ega "IV 2.3.2"]
public theorem ker_pullback_snd_eq_comap {X Y V : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) [Flat f] [QuasiCompact g] :
    (pullback.snd g f).ker = g.ker.comap f := by
  conv_lhs => rw [← g.toImage_imageι]
  let i := g.imageι
  let h := g.toImage
  let e := pullbackRightPullbackFstIso i f h
  let p := pullback.snd h (pullback.fst i f)
  let q := pullback.snd i f
  have : IsSchemeTheoreticallyDominant h := by
    rw [isSchemeTheoreticallyDominant_iff]
    let W : Y.affineOpens → (Scheme.Hom.image g).affineOpens := fun U =>
      ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top W
      (i.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)) fun U => ?_
    simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    apply (RingHom.injective_iff_ker_eq_bot (h.app (W U)).hom).mp
    simpa [W, h, i] using (g.toImage_app_injective U)
  have hp : IsSchemeTheoreticallyDominant p := inferInstance
  have he : e.hom ≫ pullback.snd (g.toImage ≫ g.imageι) f = p ≫ q := by
    dsimp [e, p, q, h, i]
    rw [pullbackRightPullbackFstIso_hom_snd]
  calc
    (pullback.snd (g.toImage ≫ g.imageι) f).ker = (p ≫ q).ker := by
      rw [← he, Scheme.Hom.ker_comp_of_isIso]
    _ = q.ker := by rw [Scheme.Hom.ker_comp, hp.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    _ = i.ker.comap f := by
      dsimp [q, i]
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry f g.imageι).hom
          (pullback.snd g.imageι f),
        pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    _ = g.ker.comap f := by rw [Scheme.IdealSheafData.ker_subschemeι]

/-- **Stacks Project, Tag 081I as a cartesian square.** If the right-hand vertical of a cartesian
square is flat and its bottom is quasi-compact, then the square of the closed embeddings of the
scheme-theoretic images of the two horizontal morphisms is cartesian. -/
public lemma isPullback_image_of_flat {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {q : Y' ⟶ Y}
    {a : X' ⟶ X} {b : X' ⟶ Y'} [Flat p] [QuasiCompact q]
    (h : IsPullback b a q p) (g : a.image ⟶ q.image)
    (hg : a.imageι ≫ p = g ≫ q.imageι) :
    IsPullback a.imageι g p q.imageι := by
  apply isPullback_of_isClosedImmersion _ _ _ _ hg
  simp only [Scheme.IdealSheafData.ker_subschemeι]
  rw [← h.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
  exact (ker_pullback_snd_eq_comap p q).symm

end AlgebraicGeometry
