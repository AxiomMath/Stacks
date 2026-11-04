module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomologyOverAnObject
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Vanishing of a higher direct image from its cohomology over affine étale schemes

For a morphism of schemes `h : Y ⟶ X` and an abelian sheaf `G` on `Y_étale`, the higher direct
image `R^r h_* G` is the sheafification of the presheaf `V ↦ H^r(V ×_X Y, G)` on `X_étale`
(Stacks, Tag 072W). Affine étale `X`-schemes are cover dense in `X_étale`, so `R^r h_* G`
vanishes as soon as `H^r(V ×_X Y, G)` does for every affine `V` étale over `X`; and the
cohomology over the object `V ×_X Y` of `Y_étale` is the étale cohomology of the scheme
`V ×_X Y`, with coefficients in the restriction of `G`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isZero_rightDerived_pushforward_of_affineEtale` —
  `R^r h_* G = 0` from the vanishing over the base changes of affine étale `X`-schemes.
* `Stacks.EtaleCohomology.SmoothBaseChange.isZero_rightDerived_sectionsOverObject_of_subsingleton`
  — the cohomology over an object of a small étale site vanishes when the étale cohomology of
  its underlying scheme does.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  Stacks.EtaleCohomology.etaleContainsIdentities
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **A higher direct image vanishes when its cohomology over affine étale schemes does.** For
`h : Y ⟶ X`, an abelian sheaf `G` on `Y_étale` and `r : ℕ`, if for every affine `V` étale over
`X` the cohomology of `G` over the object `V ×_X Y` of `Y_étale` vanishes in degree `r`, then
`R^r h_* G = 0`. -/
theorem isZero_rightDerived_pushforward_of_affineEtale {X Y : Scheme.{u}} (h : Y ⟶ X) (r : ℕ)
    (G : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (H : ∀ Z : X.AffineEtale, IsZero (((sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1} ⋙
      (evaluation (Y.Etale)ᵒᵖ Ab.{u + 1}).obj
        (op ((smallEtaleBaseChange h).obj ((AffineEtale.Spec X).obj Z)))).rightDerived r).obj G)) :
    IsZero (((smallEtalePushforwardAb h).rightDerived r).obj G) := by
  refine
    Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_rightDerived_pushforward_of_locallyZero
      (smallEtaleBaseChange h) r G fun V ξ => ?_
  refine X.smallEtaleTopology.superset_covering ?_
    ((AffineEtale.Spec X).is_cover_of_isCoverDense X.smallEtaleTopology V)
  intro V' g hg
  obtain ⟨⟨Z, lift, map, fac⟩⟩ := hg
  let P := ((Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheaf
    (K := Y.smallEtaleTopology) Ab.{u + 1} (smallEtaleBaseChange h)).rightDerived r).obj G
  have hZ : IsZero (P.obj (op ((AffineEtale.Spec X).obj Z))) :=
    (H Z).of_iso
      (((Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheafEvaluationIso
        Ab.{u + 1} (smallEtaleBaseChange h) r ((AffineEtale.Spec X).obj Z)).app G).symm)
  have h0 : P.map map.op ξ = 0 := (AddCommGrpCat.isZero_iff_subsingleton.1 hZ).elim _ _
  show P.map g.op ξ = P.map g.op 0
  rw [map_zero, ← fac, op_comp, P.map_comp, CategoryTheory.comp_apply, h0, map_zero]

/-- **Cohomology over an object of a small étale site vanishes when the étale cohomology of its
underlying scheme does.** For an object `W` of `Y_étale`, an abelian sheaf `G` on `Y_étale` and
`r : ℕ`, if the étale cohomology `H^r` of the scheme `W` with coefficients in the restriction of
`G` vanishes, then so does the cohomology of `G` over `W` in degree `r`. -/
theorem isZero_rightDerived_sectionsOverObject_of_subsingleton {Y : Scheme.{u}} (W : Y.Etale)
    (r : ℕ) (G : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    [HasExt.{u + 1} (Sheaf W.left.smallEtaleTopology Ab.{u + 1})]
    (H : Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleRestriction.{u, 0} (W.left ↘ Y)).obj G) r)) :
    IsZero (((sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1} ⋙
      (evaluation (Y.Etale)ᵒᵖ Ab.{u + 1}).obj (op W)).rightDerived r).obj G) :=
  (((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
      W.left.smallEtaleTopology _ r).1 H)).of_iso
    ((rightDerivedSectionsOverObjectIso.{0} W r).app G)

end Stacks.EtaleCohomology.SmoothBaseChange

end
