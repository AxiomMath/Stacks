module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartGlue

/-!
# The chart comparison of the determinant is transitive

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ V' ≤ W` affine opens of `X`. The chart comparison of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermChartComparison.lean` identifies the determinant
of `L` on the chart of `V` with the restriction to `V` of the determinant of `L` on the chart of
`W`, in three successive forms: over the rings, on the spectra, and on the open subschemes. This
file proves that each of the three composes along a chain of two inclusions.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_trans`: **the comparison over the rings
  composes.** This is `TwoTermDeterminant.detBaseChangeIso_trans` at the restrictions of functions
  and at `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_trans`.

## Implementation notes

The ring homomorphism attached to `V ≤ W` is only *propositionally* the composite of the ones
attached to `V ≤ V'` and `V' ≤ W`, restriction of functions being a functor, so the statement
takes the three homomorphisms as they come and the scalar tower is
`AlgebraicGeometry.DeterminantTwoTerm.affineRestriction_hom_comp`. Flatness of each of the three
is supplied separately, by `AlgebraicGeometry.IsAffineOpen.moduleFlat_presheaf_map`: flatness of
`Γ(X, V)` over `Γ(X, W)` does not follow from the other two in the generality
`TwoTermComplex.determinantLine` needs.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule (cancelBaseChange)

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The comparison over the rings composes -/

/-- **The chart comparison of the determinant over the rings composes.** For affine opens
`V ≤ V' ≤ W` of a scheme `X` and `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`,
the comparison attached to `V ≤ W` is the comparison attached to `V' ≤ W`, base changed to
`Γ(X, V)`, followed by the comparison attached to `V ≤ V'`, read through the cancellation
`Γ(X, V) ⊗_{Γ(X, V')} (Γ(X, V') ⊗_{Γ(X, W)} det(K_W)) ≅ Γ(X, V) ⊗_{Γ(X, W)} det(K_W)`.

This is `TwoTermDeterminant.detBaseChangeIso_trans`, whose cocycle hypothesis on the
identifications of the chart complexes is
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_trans`. -/
theorem chartDetModuleIso_trans (L : PerfectTwoTermAmplitude X) {V V' W : X.affineOpens}
    (h : V ≤ V') (h' : V' ≤ W) :
    letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V'.1 : X.Opens)) :=
      (affineRestriction X h').hom.toAlgebra
    letI : Algebra Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      (affineRestriction X h).hom.toAlgebra
    letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      (affineRestriction X (h.trans h')).hom.toAlgebra
    haveI : IsScalarTower Γ(X, (W.1 : X.Opens)) Γ(X, (V'.1 : X.Opens))
        Γ(X, (V.1 : X.Opens)) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (RingHom.congr_fun (affineRestriction_hom_comp h h') r).symm
    haveI : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V'.1 : X.Opens)) :=
      V'.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h')
    haveI : Module.Flat Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      V.2.moduleFlat_presheaf_map V'.2 (AffineOpensGlue.coe_le_coe h)
    haveI : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe (h.trans h'))
    (chartDetModuleIso L h).toLinearMap ∘ₗ
        LinearMap.baseChange Γ(X, (V.1 : X.Opens)) (chartDetModuleIso L h').toLinearMap ∘ₗ
        (cancelBaseChange Γ(X, (W.1 : X.Opens)) Γ(X, (V'.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
            Γ(X, (V.1 : X.Opens))
            (((det Γ(X, (W.1 : X.Opens))).obj
              ⟨chartComplex L W⟩).of.obj : Type u)).symm.toLinearMap =
      (chartDetModuleIso L (h.trans h')).toLinearMap :=
  detBaseChangeIso_trans (affineRestriction X h').hom (affineRestriction X h).hom
    (affineRestriction X (h.trans h')).hom (affineRestriction_hom_comp h h')
    (V'.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h'))
    (V.2.moduleFlat_presheaf_map V'.2 (AffineOpensGlue.coe_le_coe h))
    (V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe (h.trans h')))
    (chartComplex L W) (chartComplex L V') (chartComplex L V)
    (sourceComplexRestrictionIso V'.2 W.2 (AffineOpensGlue.coe_le_coe h') L)
    (sourceComplexRestrictionIso V.2 V'.2 (AffineOpensGlue.coe_le_coe h) L)
    (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe (h.trans h')) L)
    (sourceComplexRestrictionIso_trans V.2 V'.2 W.2 (AffineOpensGlue.coe_le_coe h)
      (AffineOpensGlue.coe_le_coe h') L)

/-! ### The structural comparisons along a chain of two inclusions -/

/-- **The two routes down the spectra agree.** For affine opens `V ≤ V' ≤ W` of `X`, pulling a
module on `Spec Γ(X, W)` back along `Spec ρ_{V',W}` and then along `Spec ρ_{V,V'}` is pulling it
back along `Spec ρ_{V,W}`: the composition isomorphism of
`AlgebraicGeometry.Scheme.Modules.pullback` at the factorisation
`AlgebraicGeometry.DeterminantTwoTerm.specMap_chartRestriction_comp`. -/
def chartSpecPullbackCompIso {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W)
    (M : (Spec Γ(X, (W.1 : X.Opens))).Modules) :
    (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).obj
        ((Scheme.Modules.pullback (Spec.map (affineRestriction X h'))).obj M) ≅
      (Scheme.Modules.pullback (Spec.map (affineRestriction X (h.trans h')))).obj M :=
  (Scheme.Modules.pullbackComp (Spec.map (affineRestriction X h))
      (Spec.map (affineRestriction X h'))).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (specMap_chartRestriction_comp (AffineOpensGlue.coe_le_coe h)
        (AffineOpensGlue.coe_le_coe h'))).app M

/-- **The chart comparison of the determinant on the open subschemes, in pullback form.** For
affine opens `V ≤ W` of `X`, the pullback along the inclusion `V ⟶ W` of the determinant of `L`
on `W` is the determinant of `L` on `V`.

The determinant on an affine open is the pullback along
`AlgebraicGeometry.IsAffineOpen.isoSpec` of the determinant on its spectrum, so this is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso` read through the two
factorisations of the pullback along `V ⟶ W ⟶ Spec Γ(X, W)` and along
`V ⟶ Spec Γ(X, V) ⟶ Spec Γ(X, W)`, which agree by
`AlgebraicGeometry.DeterminantTwoTerm.isoSpec_hom_specMap_chartRestriction`. -/
def chartDetPullbackIso (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    (Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe h))).obj (chartDet L W) ≅
      chartDet L V :=
  (Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h)) W.2.isoSpec.hom).app
      (chartDetSpec L W) ≪≫
    (Scheme.Modules.pullbackCongr (isoSpec_hom_specMap_chartRestriction h).symm).app
      (chartDetSpec L W) ≪≫
    ((Scheme.Modules.pullbackComp V.2.isoSpec.hom (Spec.map (affineRestriction X h))).app
      (chartDetSpec L W)).symm ≪≫
    (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h)

end AlgebraicGeometry.DeterminantTwoTerm

end
