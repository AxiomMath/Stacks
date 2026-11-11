module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The size of a pushout along a thickening and an affine morphism

Let `i : X ⟶ X'` be a thickening of schemes and `f : X ⟶ Y` an affine morphism, and let
`Q = Y ⨿_X X'` be their pushout, which exists by [Stacks Project, Tag 07RT].  The size of `Q`
in the sense of [Stacks Project, Section 000H] is bounded in terms of the sizes of `Y` and `X'`:

* `Y ⟶ Q` is a thickening, so `Q` has no more points than `Y`, and its affine opens, being
  subsets of its points, number at most `2 ^ #Y ≤ 2 ^ 2 ^ size Y`;
* the ring of sections of `Q` over an open `U` is the fibre product
  `Γ(Y, U) ×_{Γ(X, U)} Γ(X', U)`, so it injects into `Γ(Y, U) × Γ(X', U)`, which has at most
  `2 ^ size Y * 2 ^ size X'` elements.

Hence a pushout of two schemes below a strong limit cutoff is again below the cutoff, which is
what places the scheme pushouts of the construction of [Stacks Project, Tag 07VX] in a big fppf
site.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_isPushout_of_isThickening`: the explicit bound.
* `AlgebraicGeometry.Scheme.size_lt_of_isPushout_of_isThickening_of_isStrongPrelimit`: the
  pushout of two schemes of size below a strong limit cardinal has size below it.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal Stacks.Thickenings

namespace AlgebraicGeometry

variable {X X' Y Q : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {A : X' ⟶ Q} {B : Y ⟶ Q}

/-- On every open `U` of the canonical pushout of a thickening and an affine morphism, a
section is determined by its restrictions to the two preimages of `U`. -/
theorem Scheme.pushout_app_injective (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (U : (pushout i f).Opens) :
    Function.Injective fun s : Γ(pushout i f, U) =>
      ((pushout.inr i f).app U s, (pushout.inl i f).app U s) := by
  intro s t hst
  exact Types.ext_of_isPullback
    ((Stacks.Pushout.pushout_structureSheaf_isPullback' i f hi U).map
      (CategoryTheory.forget CommRingCat))
    (congrArg Prod.fst hst) (congrArg Prod.snd hst)

/-- **The size of a pushout along a thickening and an affine morphism.**  If `i : X ⟶ X'` is a
thickening, `f : X ⟶ Y` is affine and `Q` carries a pushout square, then
`size Q ≤ max (2 ^ 2 ^ size Y) (2 ^ size Y * 2 ^ size X')`. -/
theorem Scheme.size_le_of_isPushout_of_isThickening (hpo : IsPushout i f A B)
    (hi : IsThickening i) [IsAffineHom f] :
    Q.size ≤ max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Y.size)
      ((2 : Cardinal.{u}) ^ Y.size * (2 : Cardinal.{u}) ^ X'.size) := by
  have : HasPushout i f := hpo.hasPushout
  rw [Scheme.size_congr hpo.isoPushout]
  refine Scheme.size_le_of_bounds ?_ ?_ ?_
  · exact le_max_of_le_left (Y.aleph0_le_size.trans
      ((cantor _).le.trans (cantor _).le))
  · refine le_max_of_le_left ((pushout i f).mk_affineOpens_le_two_pow.trans
      (power_le_power_left two_ne_zero ?_))
    exact (mk_le_of_surjective (Stacks.Pushout.pushout_inr_isThickening' i f hi).2).trans
      Y.mk_le_two_pow_size
  · intro U
    refine le_max_of_le_right ((mk_le_of_injective
      (Scheme.pushout_app_injective i f hi U.1)).trans ?_)
    rw [mk_prod, lift_id, lift_id]
    exact mul_le_mul' (Y.mk_sections_le_two_pow_size _) (X'.mk_sections_le_two_pow_size _)

/-- **A pushout along a thickening and an affine morphism stays below a strong limit cutoff.**
If `size Y < κ` and `size X' < κ` for a strong limit cardinal `κ`, then `size Q < κ` for every
scheme `Q` carrying the pushout square of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y`. -/
theorem Scheme.size_lt_of_isPushout_of_isThickening_of_isStrongPrelimit {κ : Cardinal.{u}}
    (hsl : Cardinal.IsStrongPrelimit κ) (hpo : IsPushout i f A B) (hi : IsThickening i)
    [IsAffineHom f] (hY : Y.size < κ) (hX' : X'.size < κ) : Q.size < κ :=
  (Scheme.size_le_of_isPushout_of_isThickening hpo hi).trans_lt <| max_lt (hsl (hsl hY))
    (Cardinal.mul_lt_of_lt (Y.aleph0_le_size.trans hY.le) (hsl hY) (hsl hX'))

end AlgebraicGeometry

end
