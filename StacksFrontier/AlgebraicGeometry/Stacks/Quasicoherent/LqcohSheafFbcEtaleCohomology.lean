module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf

/-!
# fppf and étale cohomology agree on `LQCoh^fbc(𝒪_𝒳)` (Stacks 075R)

Stacks 075R for an algebraic stack `𝒳` at module universe `u` and `ℱ` in the corrected
`LQCoh^fbc(𝒪_𝒳)` (`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`, flat base change read on
sheaves, Stacks 0762): hypotheses (a) and (b) of the source are exactly membership. Every module
in `LQCoh^fbc(𝒪_𝒳)` is cartesian along flat morphisms of affines
(`AlgebraicGeometry.Stack.isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules`, Stacks 0779),
and each statement holds for such modules.

## Main results

* `isZero_rightDerived_etaleComparisonPushforward_of_lqcohSheafFbc`: (1), `Rε_*ℱ = ε_*ℱ`;
* `shortExact_map_etaleComparisonPushforward_of_lqcohSheafFbc`: `ε_*` is exact on short exact
  sequences whose first term is in `LQCoh^fbc(𝒪_𝒳)`;
* `rightDerivedEvaluationIsoOfLqcohSheafFbc`, `rightDerivedCoyonedaUnitIsoOfLqcohSheafFbc`: (2),
  over every object `x` and globally;
* `nonempty_rightDerived_stackModuleDirectImage_iso_of_lqcohSheafFbc`: (3).

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LqcohSheafFbc

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The abelian structure of `Mod(𝒪_𝒳)`. -/
abbrev abelianFppfModules : Abelian (fppfModules B S hS 𝒳) := SheafOfModules.instAbelian _

/-- The abelian structure of `Mod(𝒳_étale, 𝒪_𝒳)`. -/
abbrev abelianEtaleSiteModules :
    Abelian (SheafOfModules.{u} (etaleSiteRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)) :=
  SheafOfModules.instAbelian _

/-- The abelian structure of `Mod(𝒵_τ, 𝒪_𝒵)`, on `StackModules`. -/
abbrev abelianStackModules (τ : SiteKind) (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    Abelian (StackModules B S hS τ 𝒵) :=
  SheafOfModules.instAbelian _

attribute [local instance high] abelianFppfModules abelianEtaleSiteModules abelianStackModules

/-- **Stacks 075R (1)** on an algebraic stack, at module universe `u`: for `ℱ` in
`LQCoh^fbc(𝒪_𝒳)` and the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale`, `Rε_*ℱ = ε_*ℱ`, that is
`R^iε_*ℱ = 0` for `i > 0`. -/
theorem isZero_rightDerived_etaleComparisonPushforward_of_lqcohSheafFbc
    (F : fppfModules B S hS 𝒳) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F)
    (i : ℕ) (hi : 0 < i) :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    letI := enoughInjectives_etaleSiteModules B S hS 𝒳
    IsZero (((etaleComparisonPushforward B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids).rightDerived i).obj F) :=
  isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳 F
    (isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules B E h S hS 𝒳 F hF) i hi

/-- `ε_*` carries a short exact sequence of `Mod(𝒪_𝒳)` whose first term lies in
`LQCoh^fbc(𝒪_𝒳)` to a short exact sequence of `Mod(𝒳_étale, 𝒪_𝒳)`: the case `i = 1` of
**Stacks 075R (1)**. -/
theorem shortExact_map_etaleComparisonPushforward_of_lqcohSheafFbc
    {T : ShortComplex (fppfModules B S hS 𝒳)} (hT : T.ShortExact)
    (h₁ : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 T.X₁) :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    letI := enoughInjectives_etaleSiteModules B S hS 𝒳
    (T.map (etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)).ShortExact :=
  shortExact_map_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳 hT
    (isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules B E h S hS 𝒳 T.X₁ h₁)

/-- **Stacks 075R (2) over an object**, on an algebraic stack at module universe `u`:
`H^n_fppf(x, ℱ) ≅ H^n_ét(x, ℱ)` for `ℱ` in `LQCoh^fbc(𝒪_𝒳)`, every object `x` and every `n`. -/
def rightDerivedEvaluationIsoOfLqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) (x : 𝒳.val.val.obj) (n : ℕ) :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    letI := enoughInjectives_etaleSiteModules B S hS 𝒳
    ((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)
        (op x)).rightDerived n).obj F ≅
      ((SheafOfModules.evaluation (etaleSiteRingSheaf B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids) (op x)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj F) :=
  rightDerivedEvaluationIsoOfIsCartesianAlongFlatAffines B S hS 𝒳 F
    (isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules B E h S hS 𝒳 F hF) x n

/-- **Stacks 075R (2) globally**, on an algebraic stack at module universe `u`:
`H^n_fppf(𝒳, ℱ) ≅ H^n_ét(𝒳, ℱ)`, as right derived functors of `Hom(𝒪_𝒳, -)`, for `ℱ` in
`LQCoh^fbc(𝒪_𝒳)`. -/
def rightDerivedCoyonedaUnitIsoOfLqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) (n : ℕ) :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    letI := enoughInjectives_etaleSiteModules B S hS 𝒳
    ((preadditiveCoyoneda.obj (op (SheafOfModules.unit (fppfSiteRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)))).rightDerived n).obj F ≅
      ((preadditiveCoyoneda.obj (op (SheafOfModules.unit (etaleSiteRingSheaf B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)))).rightDerived n).obj
        ((etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj F) :=
  rightDerivedCoyonedaUnitIsoOfIsCartesianAlongFlatAffines B S hS 𝒳 F
    (isCartesianAlongFlatAffines_of_lqcohSheafFbcFppfModules B E h S hS 𝒳 F hF) n

/-- **Stacks 075R (3)** on algebraic stacks, at module universe `u`: for a `1`-morphism
`f : 𝒳 ⟶ 𝒴` and `ℱ` in `LQCoh^fbc(𝒪_𝒳)`, the higher direct image `R^if_*ℱ` on the fppf sites is
the fppf sheafification `ε^*` of the higher direct image on the étale sites of `ε_*ℱ`. -/
theorem nonempty_rightDerived_stackModuleDirectImage_iso_of_lqcohSheafFbc
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (F : StackModules B S hS .fppf 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) (i : ℕ) :
    letI := enoughInjectives_moduleRingSheaf B S hS 𝒳 .fppf
    letI := enoughInjectives_moduleRingSheaf B S hS 𝒳 .etale
    Nonempty (((stackModuleDirectImage B S hS f .fppf).rightDerived i).obj F ≅
      (stackModulesEtaleComparisonPullback B S hS 𝒴).obj
        (((stackModuleDirectImage B S hS f .etale).rightDerived i).obj
          ((stackModulesEtaleComparison B S hS 𝒳).obj F))) :=
  nonempty_rightDerived_stackModuleDirectImage_iso_of_isZero B S hS f F
    (isZero_rightDerived_etaleComparisonPushforward_of_lqcohSheafFbc B S hS E h 𝒳 F hF) i

end LqcohSheafFbc

end AlgebraicGeometry.Stack
