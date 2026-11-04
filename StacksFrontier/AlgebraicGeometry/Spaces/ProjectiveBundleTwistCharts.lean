module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.RelativeProjLocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist

/-!
# The twist `𝒪_P(1)` over the étale charts of the base and over the fibres

Let `X` be an algebraic space with its étale presentation `X = U/R`, let `ℰ` be a finite locally
free `𝒪_X`-module and `π : P = 𝐏(ℰ) ⟶ X` its projective bundle with the twist `𝒪_P(1)`
(`AlgebraicGeometry.Space.projectiveBundleTwist`).

Every étale scheme chart `V` of `X` with a morphism `m : V ⟶ U` to the presenting chart carries
the chart bundle `P_V = 𝐏(ℰ|_V)` and the morphism `P_V ⟶ P_U ⟶ P`, which exhibits `P_V` as
`P ×_X V`.  This file proves that **the restriction of `𝒪_P(1)` to `P_V` is the twist
`𝒪_{P_V}(1)` of the chart bundle**: the restriction to `P_U` is `𝒪_{P_U}(1)` by construction
(`AlgebraicGeometry.Space.projectiveBundleTwistChartReadingIso`), and the twists of the chart
bundles are compatible with the morphisms of chart bundles by Stacks 01O3.  Every étale chart of
`X` is covered by charts admitting a morphism to `U`, namely its fibre products with `U`.

Pulling back further along any morphism of schemes `g : Y ⟶ V`, the base change
`𝐏(g^*ℰ|_V) = P_V ×_V Y` receives the restriction of `𝒪_P(1)` as its own twist.  At the
spectrum of the residue field `κ(x)` of a point `x` of `V` and for `ℰ` of rank `n + 1`, the
fibre `P_x = 𝐏(ℰ|_V ⊗ κ(x))` is the projective space `ℙⁿ_{κ(x)}`, and `𝒪_P(1)` restricts on it to
the twist of `𝐏(ℰ|_V ⊗ κ(x))`.

Over a chart, the chart bundle is also the presentation `Stacks.Chow.bundle (ℰ|_V)` of the
projective bundle for which the projective bundle formula of Stacks 02TW is stated, and the
restriction of `𝒪_P(1)` is its twist `Stacks.Chow.bundleTwist (ℰ|_V)`: the twist of the chart
bundle is by definition the inverse image of that one along the comparison of the two
presentations.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleChartOfHom`: the morphism `P_V ⟶ P` over a chart
  `V` with a morphism to the presenting chart.
* `AlgebraicGeometry.Space.projectiveBundleTwistChartOfHomReadingIso`: **the restriction of
  `𝒪_P(1)` to `P_V` is `𝒪_{P_V}(1)`.**
* `AlgebraicGeometry.Space.projectiveBundleTwistBaseChangeIso`: the restriction of `𝒪_P(1)` to
  `P_V ×_V Y = 𝐏(g^*ℰ|_V)` is the twist of `𝐏(g^*ℰ|_V)`.
* `AlgebraicGeometry.Space.chartBundleChowBundleIso` and
  `AlgebraicGeometry.Space.projectiveBundleTwistChowIso`: the chart bundle is the projective
  bundle `Stacks.Chow.bundle (ℰ|_V)` of the projective bundle formula (Stacks 02TW), and the
  restriction of `𝒪_P(1)` to it is `Stacks.Chow.bundleTwist (ℰ|_V)`.

## Main results

* `AlgebraicGeometry.Space.isPullback_projectiveBundleChartOfHom`: `P_V = P ×_X V`.
* `AlgebraicGeometry.Space.projectiveBundleChartOfHom_eq`: the morphism `P_V ⟶ P` does not
  depend on the morphism `V ⟶ U`.
* `AlgebraicGeometry.Space.isPullback_chartBundleBaseChange`:
  `𝐏(g^*ℰ|_V) = P_V ×_V Y`.
* `AlgebraicGeometry.Space.exists_iso_projectiveSpaceOver_residueField`: over the residue field
  of a point of `V`, `𝐏(ℰ|_V ⊗ κ(x)) ≅ ℙⁿ_{κ(x)}` when `ℰ` has rank `n + 1`.

## Implementation notes

The morphism `P_V ⟶ P` is formed for the charts `V` admitting a morphism to the presenting chart
`U`, through the atlas `P_U ⟶ P` of the presentation over which `P` is glued; by
`AlgebraicGeometry.Space.projectiveBundleChartOfHom_eq` it does not depend on the morphism.  For
an arbitrary chart `V` the chart `V ×_X U` is of this kind and covers `V`.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-! ### The charts over the presenting chart -/

/-- **The morphism `P_V ⟶ P` over an étale chart `V` of `X` with a morphism `m : V ⟶ U` to the
presenting chart**: the morphism of chart bundles `P_V ⟶ P_U` over `m` followed by the atlas
`P_U ⟶ P`. -/
abbrev projectiveBundleChartOfHom {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) :
    representedAlgebraicSpace B S hS ((projectiveBundleChartFamily E hfree).site V) ⟶
      projectiveBundle E hfree :=
  representedSpaceMap B S hS ((projectiveBundleChartFamily E hfree).siteMap m) ≫
    projectiveBundleAtlas E hfree

/-- **`P_V = P ×_X V`**: over a chart `V` with a morphism `m : V ⟶ U` to the presenting chart,
the square formed by `P_V ⟶ P`, the projection `P_V ⟶ V`, the projection `π` and the chart
`V ⟶ X` is cartesian.  It is the cartesian square of the chart bundles over `m` pasted with the
cartesian square `P_U = P ×_X U` of `AlgebraicGeometry.Space.isPullback_projectiveBundleProj`. -/
theorem isPullback_projectiveBundleChartOfHom {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    IsPullback (projectiveBundleChartOfHom E hfree m).hom
      (yoneda.map ((projectiveBundleChartFamily E hfree).siteToChart V))
      (projectiveBundleProj E hfree).hom V.obj.hom := by
  have h₁ := ((projectiveBundleChartFamily E hfree).isPullback_siteMap m).map yoneda
  have h₂ := isPullback_projectiveBundleProj E hfree
  have h := h₁.paste_horiz h₂
  rwa [yoneda_map_toOver_map_comp_hom m] at h

/-- **The morphism `P_V ⟶ P` does not depend on the morphism `V ⟶ U`**: two morphisms
`a, b : V ⟶ U` of charts factor through the relation chart `R = U ×_X U`
(`AlgebraicGeometry.Space.chartRelationLift`), and the atlas `P_U ⟶ P` identifies the two
morphisms `P_R ⇉ P_U`. -/
theorem projectiveBundleChartOfHom_eq {V : SmallEtale B S hS X.1} (a b : V ⟶ bundleBaseChart X) :
    projectiveBundleChartOfHom E hfree a = projectiveBundleChartOfHom E hfree b := by
  have hsq := isPullback_projectiveBundlePresentation X
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : V ⟶ bundleRelationChart X,
      l ≫ presentationRelationTargetHom (projectiveBundlePresentation X) = a ∧
        l ≫ presentationRelationSourceHom (projectiveBundlePresentation X) = b :=
    ⟨chartRelationLift _ _ hsq a b, chartRelationLift_comp_fst _ _ hsq a b,
      chartRelationLift_comp_snd _ _ hsq a b⟩
  rw [← hl₁, ← hl₂, projectiveBundleChartOfHom, projectiveBundleChartOfHom,
    CartesianChartFamily.siteMap_comp, CartesianChartFamily.siteMap_comp,
    ← representedSpaceMap_comp, ← representedSpaceMap_comp, Category.assoc, Category.assoc]
  exact congrArg (fun k => representedSpaceMap B S hS ((projectiveBundleChartFamily E hfree).siteMap
      l) ≫ k)
    (presentationAtlas_comm (projectiveBundleChartPresentation E hfree))

/-- **The restriction of `𝒪_P(1)` to the chart bundle `P_V` is the twist `𝒪_{P_V}(1)`**, for an
étale chart `V` of `X` with a morphism `m : V ⟶ U` to the presenting chart: the reading of the
inverse image of `𝒪_P(1)` along `P_V ⟶ P` on the scheme `P_V`.  It is the pullback along the
morphism of chart bundles `P_V ⟶ P_U` of the identification on `P_U`
(`AlgebraicGeometry.Space.projectiveBundleTwistChartReadingIso`), followed by the comparison of
the twists of the chart bundles over `m` (Stacks 01O3). -/
def projectiveBundleTwistChartOfHomReadingIso {V : SmallEtale B S hS X.1}
    (m : V ⟶ bundleBaseChart X) :
    schemeReading (projectiveBundleTwist E hfree).obj (projectiveBundleChartOfHom E hfree m) ≅
      chartBundleTwist E V :=
  (schemeReadingPullbackIso (projectiveBundleTwist E hfree).obj
      (projectiveBundleTwist E hfree).property
      ((projectiveBundleChartFamily E hfree).siteMap m) rfl).symm ≪≫
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) ((projectiveBundleChartFamily E hfree).siteMap m).left)).mapIso
      (projectiveBundleTwistChartReadingIso E hfree) ≪≫
    chartBundleTwistIso E m

/-! ### Base change of a chart bundle, and the fibres -/

/-- The base change `𝐏(g^*ℰ|_V) ⟶ P_V` of the chart bundle along a morphism of schemes
`g : Y ⟶ V`. -/
abbrev chartBundleBaseChange (V : SmallEtale B S hS X.1) {Y : Scheme.{u}}
    (g : Y ⟶ chartScheme V) :
    Stacks.RelativeProj.projectiveBundle Y
        ((Scheme.Modules.pullback g).obj (chartBundleModule E V)) ⟶ chartBundle E V :=
  Stacks.RelativeProj.projectiveBundleBaseChange g (chartBundleModule E V)
    ((Scheme.Modules.pullback g).obj (chartBundleModule E V)) (Iso.refl _)

/-- **`𝐏(g^*ℰ|_V) = P_V ×_V Y`** (Stacks 01O3). -/
theorem isPullback_chartBundleBaseChange (V : SmallEtale B S hS X.1) {Y : Scheme.{u}}
    (g : Y ⟶ chartScheme V) :
    IsPullback (chartBundleBaseChange E V g)
      (Stacks.RelativeProj.projectiveBundleToBase Y
        ((Scheme.Modules.pullback g).obj (chartBundleModule E V)))
      (chartBundleToChart E V) g :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange g (chartBundleModule E V)
    ((Scheme.Modules.pullback g).obj (chartBundleModule E V)) (Iso.refl _)

/-- **The restriction of `𝒪_P(1)` to `𝐏(g^*ℰ|_V) = P_V ×_V Y` is the twist of `𝐏(g^*ℰ|_V)`**,
for an étale chart `V` of `X` with a morphism `m : V ⟶ U` to the presenting chart and a morphism
of schemes `g : Y ⟶ V`: the pullback along `𝐏(g^*ℰ|_V) ⟶ P_V` of
`AlgebraicGeometry.Space.projectiveBundleTwistChartOfHomReadingIso`, followed by the base change
of the twist (Stacks 01O3). -/
def projectiveBundleTwistBaseChangeIso {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X)
    {Y : Scheme.{u}} (g : Y ⟶ chartScheme V) :
    (Scheme.Modules.pullback (chartBundleBaseChange E V g)).obj
        (schemeReading (projectiveBundleTwist E hfree).obj (projectiveBundleChartOfHom E hfree m)) ≅
      Stacks.RelativeProj.tautologicalDatumTwist
        ((Scheme.Modules.pullback g).obj (chartBundleModule E V)) :=
  (Scheme.Modules.pullback (chartBundleBaseChange E V g)).mapIso
      (projectiveBundleTwistChartOfHomReadingIso E hfree m) ≪≫
    Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso g (chartBundleModule E V)
      ((Scheme.Modules.pullback g).obj (chartBundleModule E V)) (Iso.refl _)

/-- **The fibre of a chart bundle over a point is `ℙⁿ`**: for `ℰ` of rank `n + 1` and a point `x`
of an étale chart `V` of `X`, the base change `𝐏(ℰ|_V ⊗ κ(x)) = P_V ×_V Spec κ(x)` of
`AlgebraicGeometry.Space.chartBundleBaseChange` along `Spec κ(x) ⟶ V` is `ℙⁿ_{κ(x)}` over
`Spec κ(x)`.  On it `𝒪_P(1)` restricts to the twist of `𝐏(ℰ|_V ⊗ κ(x))`, by
`AlgebraicGeometry.Space.projectiveBundleTwistBaseChangeIso`. -/
theorem exists_iso_projectiveSpaceOver_residueField (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E (n + 1))
    (V : SmallEtale B S hS X.1) (x : chartScheme V) :
    ∃ e : Stacks.RelativeProj.projectiveBundle (Spec ((chartScheme V).residueField x))
        ((Scheme.Modules.pullback ((chartScheme V).fromSpecResidueField x)).obj
          (chartBundleModule E V)) ≅
        projectiveSpaceOver n (Spec ((chartScheme V).residueField x)),
      e.hom ≫ (projectiveSpaceOver n (Spec ((chartScheme V).residueField x)) ↘
          Spec ((chartScheme V).residueField x)) =
        Stacks.RelativeProj.projectiveBundleToBase (Spec ((chartScheme V).residueField x))
          ((Scheme.Modules.pullback ((chartScheme V).fromSpecResidueField x)).obj
            (chartBundleModule E V)) := by
  have := isFiniteLocallyFreeOfRank_chartBundleModule E n hr V
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    ((chartScheme V).fromSpecResidueField x) (chartBundleModule E V) (n + 1)
  obtain ⟨y⟩ : Nonempty (Spec ((chartScheme V).residueField x)) := inferInstance
  exact Stacks.RelativeProj.exists_iso_projectiveSpaceOver_of_forall_eq_top _ n y
    fun W hyW => eq_top_iff.2 fun z _ => (Subsingleton.elim z y) ▸ hyW

/-! ### Comparison with the presentation of Stacks 02TW -/

section Chow

variable (V : SmallEtale B S hS X.1)

/-- **The chart bundle `P_V` is the projective bundle `Stacks.Chow.bundle (ℰ|_V)`** over which
the projective bundle formula of Stacks 02TW is stated: the comparison
`Stacks.RelativeProj.bundlePresentationIso` of the two presentations of `𝐏(ℰ|_V)`. -/
def chartBundleChowBundleIso :
    letI := isFiniteLocallyFree_chartBundleModule E hfree V
    Stacks.Chow.bundle (chartBundleModule E V) ≅ chartBundle E V :=
  Stacks.RelativeProj.bundlePresentationIso (chartBundleModule E V)

/-- The comparison lies over the chart. -/
theorem chartBundleChowBundleIso_hom_comp_chartBundleToChart :
    letI := isFiniteLocallyFree_chartBundleModule E hfree V
    (chartBundleChowBundleIso E hfree V).hom ≫ chartBundleToChart E V =
      Stacks.Chow.bundleProj (chartBundleModule E V) :=
  Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase (chartBundleModule E V)

/-- **The twist of the chart bundle is the twist `Stacks.Chow.bundleTwist (ℰ|_V)` of
Stacks 02TW**, through `AlgebraicGeometry.Space.chartBundleChowBundleIso`: the twist of
`Stacks.RelativeProj.projectiveBundle` is by definition the inverse image of that of the other
presentation along the comparison. -/
def chartBundleTwistChowIso :
    letI := isFiniteLocallyFree_chartBundleModule E hfree V
    (Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).hom).obj
        (chartBundleTwist E V) ≅ Stacks.Chow.bundleTwist (chartBundleModule E V) :=
  letI := isFiniteLocallyFree_chartBundleModule E hfree V
  (Scheme.Modules.pullbackComp (chartBundleChowBundleIso E hfree V).hom
      (chartBundleChowBundleIso E hfree V).inv).app _ ≪≫
    (Scheme.Modules.pullbackCongr (chartBundleChowBundleIso E hfree V).hom_inv_id).app _ ≪≫
    (Scheme.Modules.pullbackId (X := Stacks.Chow.bundle (chartBundleModule E V))).app _

/-- **The restriction of `𝒪_P(1)` to a chart bundle, read on the presentation of Stacks 02TW, is
`Stacks.Chow.bundleTwist (ℰ|_V)`**, for an étale chart `V` of `X` with a morphism `m : V ⟶ U` to
the presenting chart. -/
def projectiveBundleTwistChowIso (m : V ⟶ bundleBaseChart X) :
    letI := isFiniteLocallyFree_chartBundleModule E hfree V
    (Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).hom).obj
        (schemeReading (projectiveBundleTwist E hfree).obj (projectiveBundleChartOfHom E hfree m)) ≅
      Stacks.Chow.bundleTwist (chartBundleModule E V) :=
  letI := isFiniteLocallyFree_chartBundleModule E hfree V
  (Scheme.Modules.pullback (chartBundleChowBundleIso E hfree V).hom).mapIso
      (projectiveBundleTwistChartOfHomReadingIso E hfree m) ≪≫
    chartBundleTwistChowIso E hfree V

end Chow

end AlgebraicGeometry.Space

end
