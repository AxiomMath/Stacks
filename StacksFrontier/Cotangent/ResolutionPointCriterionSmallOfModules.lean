module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmall
import StacksCore.Tactic.StacksAttribute

/-!
# Left derived lower shriek of modules at the restricted polynomial site

Let `A → B` be a ring map and let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are
polynomial algebras on at most `κ` variables. For every sheaf of `B`-modules `ℱ` on the small model
of the site restricted to such polynomial algebras, the sections at the point of `L_nπ_!(ℱ)` are
the degree `n` homology of the Moore complex of the simplicial `B`-module `ℱ(P_•, ε)`, naturally
in `ℱ`; that is, `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`.

## Main definitions

* `CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso`: for a resolution `P_•` of `B`
  over `A` by polynomial algebras on at most `κ` variables, the natural isomorphism between the
  sections at the point of `L_nπ_!(ℱ)` and the degree `n` homology of the Moore complex of
  `ℱ(P_•, ε)`.
* `CommAlgCat.standardResolutionModuleLeftDerivedLowerShriekNatIso`: the same for the standard
  resolution of `B` over `A`.

## References

* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

section Bounded

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial algebras on at
most `κ` variables. For every sheaf of `B`-modules `ℱ` on the small model of the restricted site
`C_{B/A}`, the sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the Moore
complex of the simplicial `B`-module `ℱ(P_•, ε)`, naturally in `ℱ`; here `π` is the point
morphism of the small model. -/
@[stacks 08PS "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` functorially in `ℱ` in \
  `Mod(B̲)`, read at the small model of the footnote-restricted site, for the same reason as \
  recorded for the abelian half in \
  `StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean`"]
def smallResolutionModuleLeftDerivedLowerShriekNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (n : ℕ) :
    (modulePointLowerShriek (smallBoundedPolynomialSite A B κ)
          (B : Type u)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections.{u, u + 1, u} (ModuleCat.{u} (B : Type u)) ≅
      sheafToPresheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
          (ModuleCat.{u} (B : Type u)) ⋙
        moduleCosimplicialMooreComplex (smallResolutionCosimplicialObject ε κ hPκ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} (B : Type u))
            (ComplexShape.down ℕ) n :=
  moduleLeftDerivedPointLowerShriekNatIso _ _ _
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε) n

end Bounded

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- For every sheaf of `B`-modules `ℱ` on the small model of the site `C_{B/A}` restricted to
polynomial algebras on at most `CommAlgCat.standardResolutionVarCardinal A B` variables, the
sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the Moore complex of the
simplicial `B`-module `ℱ(P_•, ε)` for `P_•` the standard resolution of `B` over `A`, naturally
in `ℱ`. -/
@[stacks 08PT "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` functorially in `ℱ` in \
  `Mod(B̲)`, for the standard resolution, read at the small model of the footnote-restricted \
  site, for the reason recorded at Tag 08PS in this file"]
def standardResolutionModuleLeftDerivedLowerShriekNatIso (n : ℕ) :
    (modulePointLowerShriek
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
          (B : Type u)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections.{u, u + 1, u} (ModuleCat.{u} (B : Type u)) ≅
      sheafToPresheaf (GrothendieckTopology.trivial
            (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)))
          (ModuleCat.{u} (B : Type u)) ⋙
        moduleCosimplicialMooreComplex
            (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
              (standardResolutionVarCardinal A B)
              (standardResolution_isPolynomialAlgebraBelow A B)) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} (B : Type u))
            (ComplexShape.down ℕ) n :=
  smallResolutionModuleLeftDerivedLowerShriekNatIso (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration n

end CommAlgCat

end
