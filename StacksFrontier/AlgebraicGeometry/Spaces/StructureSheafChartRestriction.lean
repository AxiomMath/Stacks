module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent

/-!
# The structure sheaf of an algebraic space under inverse image and chart restriction

The structure sheaf `𝒪_X` of an algebraic space is the free `𝒪_X`-module of rank one on its
small étale site, and this file proves that the two constructions which move `𝒪_X`-modules
around carry it to the corresponding structure sheaf:

* the inverse image of Stacks 03LU along a morphism `h : X' ⟶ X` of algebraic spaces carries
  `𝒪_X` to `𝒪_{X'}`;
* the restriction of Stacks 03G6 to the scheme of an étale chart `V` of `X` carries `𝒪_X` to the
  structure sheaf of that scheme.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackUnitIso`: the inverse image of the structure sheaf
  along a morphism of algebraic spaces is the structure sheaf.
* `AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`: the restriction of the structure sheaf
  of an algebraic space to the scheme of an étale chart is the structure sheaf of that scheme,
  that is, the free module of rank one over `(chartScheme V).ringCatSheaf`.

## Implementation notes

The first is `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` at the morphism of
small étale ringed topoi of Stacks 03G8, which is the morphism
`AlgebraicGeometry.Space.modulePullback` is defined from.

The second goes through the three steps `AlgebraicGeometry.Space.restrictToChartScheme` is built
from, each of which carries the free module of rank one to the free module of rank one: the
universe of the sections is raised by an amount already present
(`SheafOfModules.uliftForPresentationSelfIso`, applicable because the module universe of the
structure sheaf of an algebraic space is the universe of the schemes), the change of scalars
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` is an isomorphism — it is
`AlgebraicGeometry.Scheme.restrictFunctorΓ` whiskered with the forgetful functor to `RingCat`,
so `PresheafOfModules.pushforwardUnitIso` applies and the invertibility is found by instance
search rather than proved — and the structure presheaf of a scheme is its own sheafification
(`Stacks.SheafOfModules.FreeSheafification.unitIso`).

The two sheafification instances for the Zariski site of the chart are restated from its
essential smallness exactly as in `AlgebraicGeometry.Space.restrictToChartScheme`; both classes
are propositions, so which term is used is immaterial.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The inverse image of the structure sheaf is the structure sheaf.**  For a morphism
`h : X' ⟶ X` of algebraic spaces, the inverse image of Stacks 03LU carries `𝒪_X` to `𝒪_{X'}`. -/
def modulePullbackUnitIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (h : X' ⟶ X) :
    (modulePullback B S hS h).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)) :=
  (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
    (smallEtaleRingedToposModulesHom B S hS h)).symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The restriction of the structure sheaf to an étale chart's scheme is the structure sheaf of
that scheme.** -/
def restrictToChartSchemeUnitIso (hF : IsAlgebraicSpace B S hS F) (V : SmallEtale B S hS F) :
    restrictToChartScheme B S hS F hF
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) V ≅
      SheafOfModules.unit (chartScheme V).ringCatSheaf := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  haveI : IsIso (chartSchemeRestrictionRingHom B S hS F V) :=
    inferInstanceAs (IsIso (Functor.whiskerRight
      (Scheme.restrictFunctorΓ (X := chartScheme V)).inv
      (forget₂ CommRingCat.{u} RingCat.{u})))
  have e : (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u}
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).val ≅
      PresheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj :=
    (SheafOfModules.forget _).mapIso
      (SheafOfModules.uliftForPresentationSelfIso.{u + 1, u, u, u} _)
  exact (PresheafOfModules.sheafification (𝟙 (chartScheme V).ringCatSheaf.obj)).mapIso
      ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F V)).mapIso e ≪≫
        PresheafOfModules.pushforwardUnitIso
          (chartSchemeRestrictionRingHom B S hS F V)) ≪≫
    Stacks.SheafOfModules.FreeSheafification.unitIso (chartScheme V).ringCatSheaf

end AlgebraicGeometry.Space

end
