module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale cohomology over an object of the small étale site, and torsion

Let `X` be a scheme and `W` an object of its small étale site, that is an étale morphism
`W.left ↘ X : W.left ⟶ X`. Étale cohomology over `W`, the right derived functor of the sections
functor `F ↦ F(W)` on abelian sheaves on `X_étale`, is the étale cohomology of the *scheme*
`W.left`:

> `H^n(W, F) ≅ H^n_étale(W.left, F|_{W.left})`.

Consequently [Stacks, Tag 0DDC] (1) applies over `W` as soon as the scheme `W.left` is
quasi-compact and quasi-separated — no condition on `X` itself — and the étale cohomology over
`W` of a torsion abelian sheaf on `X_étale` is a torsion abelian group. This is the form in which
the proof of [Stacks, Tag 0DDD] uses Tag 0DDC: there `W` is `V ×_Y X` for an affine object `V` of
`Y_étale`, which is quasi-compact and quasi-separated as a scheme but carries no quasi-compactness
hypothesis on `X`.

## Main results

* `Stacks.EtaleCohomology.rightDerivedSectionsOverObjectIso`: the displayed isomorphism.
* `Stacks.EtaleCohomology.exists_nsmul_eq_zero_rightDerived_sectionsOverObject`: Tag 0DDC (1)
  over an object of the small étale site.

## Implementation notes

The comparison is the localization comparison for cohomology
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardRightDerivedSectionsIso` applied to the
continuous functor of sites `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose (W.left ↘ X)`,
composition with the structure morphism of `W`. Its two hypotheses on the induced restriction
functor — exactness and preservation of injectives — are
`Stacks.EtaleCohomology.etaleRestriction_preservesColimits` and
`Stacks.EtaleCohomology.etaleRestriction_preservesInjectiveObjects`, the latter coming from the
left exactness of extension by zero. Working with `smallEtaleCompose` rather than with the slice
site `X_étale/W` is what avoids `WEqualsLocallyBijective` for the slice topology, which is not
available at the universes of the small étale site.

Sections over an object are written as the composite of `sheafToPresheaf` with evaluation, which
is the form in which the localization comparison is stated; it is the same functor as
`(CategoryTheory.sheafSections _ _).obj (Opposite.op W)`, by
`CategoryTheory.sheafSectionsNatIsoEvaluation`.

That the restriction of a torsion abelian sheaf is torsion is
`Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous`, composition with `W.left ↘ X`
being cocontinuous.

## References

* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe v u

namespace Stacks.EtaleCohomology

noncomputable section

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

variable {X : Scheme.{u}}

/-- **Étale cohomology over an object of the small étale site is the étale cohomology of its
underlying scheme.** For `W` an object of the small étale site of `X`, the `n`-th right derived
functor of `F ↦ F(W)` is the `n`-th étale cohomology of the scheme `W.left` applied to the
restriction of `F` along `W.left ↘ X`, naturally in `F`.

This is the localization comparison `pushforwardRightDerivedSectionsIso` for the continuous and
cocontinuous functor of sites given by composition with `W.left ↘ X`, evaluated at the terminal
object `𝟙 W.left` of the small étale site of `W.left`, whose image under that functor is `W`. -/
def rightDerivedSectionsOverObjectIso (W : X.Etale) (n : ℕ) :
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
          (evaluation (X.Etale)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj (op W)).rightDerived n ≅
      etaleRestriction.{u, v} (W.left ↘ X) ⋙
        (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n :=
  letI T : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  letI hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  letI e : (smallEtaleCompose (W.left ↘ X)).obj T ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl _) rfl
  Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Functor.isoWhiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        ((evaluation (X.Etale)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).mapIso e.op)) n ≪≫
    (pushforwardRightDerivedSectionsIso AddCommGrpCat.{max (u + 1) v}
        (smallEtaleCompose (W.left ↘ X)) n T).symm ≪≫
      Functor.isoWhiskerLeft (etaleRestriction.{u, v} (W.left ↘ X))
        (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
          ((sheafSectionsNatIsoEvaluation W.left.smallEtaleTopology
              AddCommGrpCat.{max (u + 1) v}).symm ≪≫
            (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology
              AddCommGrpCat.{max (u + 1) v} hT).symm) n)

/-- **[Stacks, Tag 0DDC] (1) over an object of the small étale site.** Let `W` be an object of the
small étale site of a scheme `X` whose underlying scheme `W.left` is quasi-compact and
quasi-separated, and let `F` be a torsion abelian sheaf on `X_étale`. Then every class in the
étale cohomology `H^n(W, F)` is annihilated by a positive integer.

No hypothesis is placed on `X`: the cohomology over `W` is the étale cohomology of the scheme
`W.left` by `rightDerivedSectionsOverObjectIso`, the restriction of `F` to `W.left` is again a
torsion abelian sheaf, and Tag 0DDC (1) applies to the quasi-compact and quasi-separated scheme
`W.left`. -/
@[sga "4 IX 1.2" "(ii), (v)"]
theorem exists_nsmul_eq_zero_rightDerived_sectionsOverObject (W : X.Etale)
    (hc : CompactSpace W.left) (hq : QuasiSeparatedSpace W.left)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ)
    (y : ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        (evaluation (X.Etale)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj
          (op W)).rightDerived n).obj F) :
    ∃ k : ℕ, 0 < k ∧ k • y = 0 := by
  have := hc
  have := hq
  have hres : Stacks.Torsion.torsionSheafProperty W.left.smallEtaleTopology
      ((etaleRestriction.{u, v} (W.left ↘ X)).obj F) :=
    Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous
      (smallEtaleCompose (W.left ↘ X)) F hF
  have htor := etaleCohomology_isAddTorsion.{v} W.left
    ((etaleRestriction.{u, v} (W.left ↘ X)).obj F) hres n
  let ι := (rightDerivedSectionsOverObjectIso.{v} W n).app F
  obtain ⟨k, hk0, hk⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (htor (ι.hom y))
  refine ⟨k, hk0, ?_⟩
  have h0 : ι.hom (k • y) = 0 := by rw [_root_.map_nsmul, hk]
  have h1 : ι.inv (ι.hom (k • y)) = k • y := by
    rw [← CategoryTheory.comp_apply, ι.hom_inv_id]
    rfl
  rw [← h1, h0, map_zero]

end

end Stacks.EtaleCohomology

end
