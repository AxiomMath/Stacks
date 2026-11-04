module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSolutionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPulledBackIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts

/-!
# The thickening built from a solution of the tower problem lives on the given site

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, a solution `𝒪'` of the
problem is 05ZT data for `X₀ ⟶ Y = Spec(lim Rₙ)`
(`AlgebraicGeometry.ProperFlatFibre.towerSolutionSquareZeroExtension`), with ideal
`f^*𝒞_{Y₀/Y}`. That ideal is the pullback `(f ≫ i)^*ℐ` of the ideal sheaf `ℐ` of `Y₀ ⊂ Y` along
`X₀ ⟶ Y₀ ⟶ Y`, and `Y` is affine with `#ℐ(Y) ≤ #Γ(Y, 𝒪_Y)` below the cutoff of the big fppf
site. So the chart thickenings of `𝒪'` are bounded
(`AlgebraicGeometry.Space.SquareZeroExtension.contains_chartRealizedScheme_of_iso_modulePullback`)
and the first order thickening `X₀ ⊂ X'` over `Y` of Stacks 05ZT is an algebraic space of the
site we started with. In the proof of [Stacks Project, Tag 0D3X] this is the step "the sheaf `𝒪'`
determines a first order thickening `X₀ ⊂ X` over `Spec(lim Rₙ)`", with the size bookkeeping the
text leaves implicit.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerProblemGIso`: `f^*𝒞_{Y₀/Y} ≅ (f ≫ ρ ≫ ι)^*ℐ`, where
  `ρ : Y₀ ≅ (Y₀ ⊂ Y)` and `ι` is the inclusion of the closed subspace.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.mk_limitBaseIdeal_lt_cutoff`: `#ℐ(Y)` is below the cutoff.
* `AlgebraicGeometry.ProperFlatFibre.nonempty_towerSolutionRealization`: a solution of the tower
  problem is realized by a first order thickening `X₀ ⊂ X'` over `Y` on the given site.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- The morphism `X₀ ⟶ Y₀ ≅ (Y₀ ⊂ Y) ⟶ Y`. -/
abbrev towerIdealPullbackMap : towerSpace ξ 0 ⟶ schemeSpace c.pt :=
  towerStructureMap ξ 0 ≫ (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
    Space.subspaceInclusion B S hS (schemeSpace c.pt)
      (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)

/-- The ideal sheaf `ℐ` of `Y₀ ⊂ Y = Spec(lim Rₙ)`. -/
abbrev limitBaseIdeal :=
  (Space.definingIdealSheaf B S hS (schemeSpace c.pt)
    (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)).toSheafOfModules

/-- **`f^*𝒞_{Y₀/Y} ≅ (f ≫ ρ ≫ ι)^*ℐ`**: the conormal module is `ι^*ℐ` restricted along
`ρ : Y₀ ≅ (Y₀ ⊂ Y)`, étale restriction is pullback (Stacks 03LW), and pullbacks compose
(Stacks 03LU). -/
def towerProblemGIso :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ≅
      (Space.modulePullback B S hS (towerIdealPullbackMap ξ hsurj hsq e cR hcR c eLimit hc)).obj
        (limitBaseIdeal ξ hsurj hsq e cR hcR c eLimit hc) :=
  (Space.modulePullback B S hS (towerStructureMap ξ 0)).mapIso
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS
        (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom
        (Space.isEtale_hom_of_iso B S hS (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc))).app
          (Space.conormalModule B S hS (schemeSpace c.pt)
            (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))).symm ≪≫
    (Space.modulePullback B S hS (towerStructureMap ξ 0)).mapIso
      ((Space.modulePullbackCompIso B S hS (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom
        (Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))).app
        (limitBaseIdeal ξ hsurj hsq e cR hcR c eLimit hc)) ≪≫
    (Space.modulePullbackCompIso B S hS (towerStructureMap ξ 0)
      ((limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
        Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))).app
      (limitBaseIdeal ξ hsurj hsq e cR hcR c eLimit hc)

include hsurj hsq hcR hc in
/-- **`#ℐ(Y)` is below the cutoff**: `ℐ(Y) ⊆ Γ(Y, 𝒪_Y)`, and `Y = Spec(lim Rₙ)` is an affine
scheme of the site. -/
theorem mk_limitBaseIdeal_lt_cutoff :
    #((limitBaseIdeal ξ hsurj hsq e cR hcR c eLimit hc).val.obj
      (op (Space.selfChart B S hS c.pt))) < B.cutoff := by
  refine (Cardinal.mk_le_of_injective (f := fun x => x.1) fun a b h => Subtype.ext h).trans_lt ?_
  exact Space.mk_sections_structureRingSheaf_lt_cutoff B S hS (schemeSpace c.pt)
    (Space.selfChart B S hS c.pt)

/-- **A solution of the tower problem is realized on the given site** (Stacks 05ZT, as used in
[Stacks Project, Tag 0D3X]): there is a first order thickening `X₀ ⊂ X'` over
`Y = Spec(lim Rₙ)` of algebraic spaces of the site, with `i⁻¹𝒪_{X'} ≅ 𝒪'` compatibly with the
maps to `𝒪_{X₀}` and with the algebra structures. -/
theorem nonempty_towerSolutionRealization
    (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening) :
    Nonempty (Space.EtaleSquareZeroExtension.Realization
      (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')) := by
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := IsAffine.of_isIso eLimit.hom
  exact Space.SquareZeroExtension.nonempty_realization_of_iso_modulePullback
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P') hT
    (towerIdealPullbackMap ξ hsurj hsq e cR hcR c eLimit hc)
    (limitBaseIdeal ξ hsurj hsq e cR hcR c eLimit hc)
    (Space.isQuasicoherentOnSite_definingIdealSheaf B S hS _ _)
    (mk_limitBaseIdeal_lt_cutoff ξ hsurj hsq e cR hcR c eLimit hc)
    (towerProblemGIso ξ hsurj hsq e cR hcR c eLimit hc)

end AlgebraicGeometry.ProperFlatFibre

end
