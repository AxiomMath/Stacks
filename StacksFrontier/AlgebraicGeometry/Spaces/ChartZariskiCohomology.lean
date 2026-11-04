module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison

/-!
# Étale and Zariski cohomology of a quasi-coherent module over a chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `A` be an
étale chart of `X` with underlying scheme `T`, and let `𝓜` be a quasi-coherent `𝒪_X`-module.
Reading a Zariski open `W` of `T` as the étale chart of `X` it cuts out is a continuous functor
`u : T_Zar ⟶ X_étale`, `AlgebraicGeometry.Space.chartComparisonFunctor`, and restriction along
it carries `𝓜` to a module on the Zariski site of `T`, the *chart restriction* of `𝓜`.  This file
shows that the cohomology of `𝓜` over `A` is the Zariski cohomology of the chart restriction:

`H^n(A, 𝓜) = H^n(T, u_* 𝓜)`,

in the form of the vanishing of the left-hand side in a positive degree as soon as the right-hand
side vanishes.

The argument is the Leray collapse along `u`, as in the proof of Descent, Proposition 35.9.3
([Stacks, Tag 03DW]).  The higher direct images `R^q u_* 𝓜` vanish for `q > 0`, since the
affine opens of `T` cover every open, an affine open of `T` is an affine étale chart of `X`, and
the higher cohomology of a quasi-coherent module on an affine étale chart vanishes
(`AlgebraicGeometry.Space.isZero_sheafCohomology_succ_of_isAffineChart`).  Then cohomology over
`⊤` on the Zariski site of `T` agrees with cohomology over `u ⊤ ≅ A` on the étale site of `X`,
by `Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_chartZariskiPushforward`: the higher direct images
  along `u` of a quasi-coherent module vanish.
* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isZero_hgroup`: **the cohomology of
  a quasi-coherent module over a chart vanishes in a positive degree as soon as the Zariski
  cohomology of its chart restriction does.**

## Implementation notes

The comparison is made between abelian sheaves, where restriction along `u` preserves injective
objects (`Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous`: the
Zariski site has fibre products and equalizers and `u` preserves them), and is then read on
modules at both ends: on the Zariski site by the comparison of Stacks 01F1 for a small site,
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsIsoCohomologyPresheaf`, and on the étale
site by `Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`, the form of
Stacks 03FD available on a site whose objects live one universe above its morphisms.

The `Ext` groups of abelian sheaves on the étale site of `X` are taken at the universe `u` of the
morphisms of the site in the collapse, which is where
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections` identifies them with
right derived sections, and at the universe `u + 1` of its objects where the vanishing on affine
charts is stated; `Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv` passes between the
two.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1)

/-! ### Homological instances on the étale site at the morphism universe -/

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] enoughInjectives_sheaf_smallEtale SmallEtale.instHasSheafify
  SmallEtale.instWEqualsLocallyBijective

/-- The `Ext` groups of abelian sheaves on the small étale site of an algebraic space, at the
universe of the morphisms of the site: the site is essentially small there, so its abelian sheaves
form a Grothendieck abelian category. -/
local instance (priority := 5000) hasExt_sheaf_smallEtale_morphismUniverse :
    HasExt.{u} (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  have : IsGrothendieckAbelian.{u} (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  inferInstance

/-- The `Ext` groups of abelian sheaves on the small étale site of an algebraic space, at the
universe of the objects of the site. -/
local instance (priority := 5000) hasExt_sheaf_smallEtale_objectUniverse :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Enough injective abelian sheaves, at the projection spelling of the topology, which instance
search does not unfold to the reduced one. -/
local instance enoughInjectives_sheaf_smallEtaleRingedSite_chart :
    EnoughInjectives (Sheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}) :=
  enoughInjectives_sheaf_smallEtale B S hS X.1

/-- `Ext` of abelian sheaves at the universe of the objects of the site, at the projection
spelling of the topology. -/
local instance hasExt_sheaf_smallEtaleRingedSite_chart :
    HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The `𝒪_X`-modules at the universe of the structure rings have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_chart :
    EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) :=
  enoughInjectives_modules B S hS X.1 X.2

/-- The `Ext` groups of `𝒪_X`-modules at the universe of the objects of the site. -/
local instance hasExt_modules_chart :
    HasExt.{u + 1} (Modules.{u, u} B S hS X.1 X.2) :=
  HasExt.standard _

/-! ### The chart restriction of abelian sheaves -/

/-- Restriction of abelian sheaves along the comparison functor of a chart: an abelian sheaf on
the small étale site of `X` read on the Zariski site of the chart's scheme. -/
abbrev chartZariskiPushforward :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (chartScheme A)) AddCommGrpCat.{u} :=
  (chartComparisonFunctor B S hS X A).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology (chartScheme A)) (SmallEtale.topology B S hS X.1)

/-- An affine open of the chart's scheme cuts out an affine étale chart of `X`: the scheme of
that chart is the open subscheme itself. -/
theorem isAffineChart_openChartOfComparison {W : (chartScheme A).Opens}
    (hW : IsAffineOpen W) : IsAffineChart B S hS X.1 (openChartOfComparison B S hS X A W) :=
  hW

/-- **The Ext universe of the cohomology of an abelian sheaf does not matter for its
vanishing.** -/
theorem isZero_sheafH'_iff_univ {C : Type*} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})] (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ)
    (V : C) : IsZero (Sheaf.H'.{u} F n V) ↔ IsZero (Sheaf.H'.{u + 1} F n V) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  exact Equiv.subsingleton_congr
    (Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{u, u + 1}).toEquiv

/-- **The higher direct images along the comparison functor of a chart of a quasi-coherent
module vanish.**  Every Zariski open of the chart's scheme is covered by affine opens, which cut
out affine étale charts of `X`, and the higher cohomology of a quasi-coherent module on an affine
étale chart vanishes. -/
theorem isZero_rightDerived_chartZariskiPushforward (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    IsZero (((chartZariskiPushforward B S hS X A).rightDerived q).obj
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M)) := by
  refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (chartComparisonFunctor B S hS X A) q _ (fun V => ?_)
  refine ⟨fun W (_ : W ⟶ V) => IsAffineOpen W, ?_, fun W g hW => ?_⟩
  · intro x hx
    obtain ⟨W, hW, hxW, hWV⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (chartScheme A)) hx
    exact ⟨W, homOfLE hWV, ⟨W, 𝟙 W, homOfLE hWV, hW, Category.id_comp _⟩, hxW⟩
  · refine IsZero.of_iso ?_
      (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
        (SmallEtale.topology B S hS X.1) _ q _).symm
    exact (isZero_sheafH'_iff_univ (J := SmallEtale.topology B S hS X.1) _ _ _).2
      (isZero_sheafCohomology_succ_of_isAffineChart B S hS X.1 X.2 M hM _
        (isAffineChart_openChartOfComparison B S hS X A hW) q hq)

/-- **The abelian cohomology over the chart cut out by a Zariski open vanishes with the Zariski
cohomology over that open.**  Let `A` be an étale chart of `X`, `W` an open of the chart's scheme
`T` and `𝓜` a quasi-coherent `𝒪_X`-module.  If `H^q(W, u_*𝓜) = 0` on the Zariski site of `T`,
for some `q > 0`, then the cohomology of the underlying abelian sheaf of `𝓜` over the étale chart
`u W` of `X` vanishes in degree `q`.

The higher direct images along `u` vanish
(`AlgebraicGeometry.Space.isZero_rightDerived_chartZariskiPushforward`), so cohomology over `W`
on the Zariski site agrees with cohomology over `u W` on the étale site, by
`Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso`; the Zariski end is read on
modules by the comparison of Stacks 01F1 for a small site. -/
theorem isZero_sheafH'_openChartOfComparison_of_isZero_hgroup
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : (chartScheme A).Opens) (q : ℕ) (_hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme A).ringCatSheaf W q
      ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M))) :
    IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M) q
        (openChartOfComparison B S hS X A W)) := by
  let F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} := (SheafOfModules.toSheaf
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M
  have := Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (Opens.grothendieckTopology (chartScheme A)) (SmallEtale.topology B S hS X.1)
    (chartComparisonFunctor B S hS X A)
  have hF : ∀ q', 1 ≤ q' → q' ≤ q →
      IsZero (((chartZariskiPushforward B S hS X A).rightDerived q').obj F) :=
    fun q' hq' _ => isZero_rightDerived_chartZariskiPushforward B S hS X A M hM q' hq'
  have h₁ : IsZero (Sheaf.H'.{u} ((chartZariskiPushforward B S hS X A).obj F) q W) :=
    h.of_iso (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsIsoCohomologyPresheaf
      (Opens.grothendieckTopology (chartScheme A)) (chartScheme A).ringCatSheaf W q
      ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M)).symm
  have h₂ : IsZero (Sheaf.H'.{u} F q (openChartOfComparison B S hS X A W)) := by
    refine IsZero.of_iso ?_
      (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
        (SmallEtale.topology B S hS X.1) F q _)
    refine IsZero.of_iso ?_ (Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso
      (Opens.grothendieckTopology (chartScheme A)) (SmallEtale.topology B S hS X.1)
      (chartComparisonFunctor B S hS X A) F W q hF).symm
    exact h₁.of_iso (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (Opens.grothendieckTopology (chartScheme A)) _ q W).symm
  exact (isZero_sheafH'_iff_univ (J := SmallEtale.topology B S hS X.1) F q _).1 h₂

/-- Vanishing of the cohomology of the underlying abelian sheaf of a module over an object, read
on modules. -/
private theorem isZero_rightDerived_evaluation_of_isZero_sheafH'
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M) q
        V)) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (op V)).rightDerived q).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact ModuleCat.isZero_iff_subsingleton.2
    (Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation
      (smallEtaleRingedSite B S hS X.1 X.2).J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) M V n h)

/-- **The cohomology of a quasi-coherent module over the chart cut out by a Zariski open vanishes
as soon as the Zariski cohomology of its chart restriction over that open does.**  This is
`AlgebraicGeometry.Space.isZero_sheafH'_openChartOfComparison_of_isZero_hgroup` read on modules,
by `Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`. -/
theorem isZero_rightDerived_evaluation_openChartOfComparison_of_isZero_hgroup
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (W : (chartScheme A).Opens) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme A).ringCatSheaf W q
      ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M))) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (op (openChartOfComparison B S hS X A W))).rightDerived q).obj M) := by
  exact isZero_rightDerived_evaluation_of_isZero_sheafH' B S hS X M _ q hq
    (isZero_sheafH'_openChartOfComparison_of_isZero_hgroup B S hS X A M hM W q hq h)

/-- **The cohomology of a quasi-coherent module over a chart vanishes as soon as the Zariski
cohomology of its chart restriction does.**  Let `A` be an étale chart of `X` and `𝓜` a
quasi-coherent `𝒪_X`-module.  If `H^q(T, u_*𝓜) = 0` on the Zariski site of the chart's scheme
`T`, for some `q > 0`, then `H^q(A, 𝓜) = 0`.

This is `AlgebraicGeometry.Space.isZero_sheafH'_openChartOfComparison_of_isZero_hgroup` at the
open `⊤`, whose chart is `A` itself by `AlgebraicGeometry.Space.openChartOfComparisonTopIso`,
read on modules. -/
theorem isZero_rightDerived_evaluation_of_isZero_hgroup (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme A).ringCatSheaf ⊤ q
      ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).obj M))) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (op A)).rightDerived q).obj M) := by
  have h₃ := (isZero_sheafH'_openChartOfComparison_of_isZero_hgroup B S hS X A M hM ⊤ q hq
    h).of_iso ((Sheaf.cohomologyPresheaf.{u + 1} ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj M)
        q).mapIso (openChartOfComparisonTopIso B S hS X A).op)
  exact isZero_rightDerived_evaluation_of_isZero_sheafH' B S hS X M A q hq h₃

end AlgebraicGeometry.Space

end
