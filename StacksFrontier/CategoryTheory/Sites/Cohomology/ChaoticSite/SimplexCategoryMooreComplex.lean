module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# `L_nπ_!` over `Δ` is Moore homology

Let `Δ = SimplexCategory` carry the chaotic topology, so that a presheaf on `Δ` is a simplicial
object and `π_!` is the colimit over `Δᵒᵖ` (Stacks 08PF). This file records the instance of
Stacks 08Q9 at `C = Δ` with the cosimplicial object `U_• = 𝟭 Δ`:

`L_nπ_!(ℱ) = H_n(ℱ)`, the `n`th homology of the alternating-face-map complex of `ℱ`.

Both inputs are in the library. `Stacks.ChaoticSite.leftDerivedColimitNatIso` is Stacks 08Q9 for an
arbitrary cosimplicial point resolution of an arbitrary small category, and
`Stacks.ChaoticSite.isPointResolution_id_simplexCategory` says that `𝟭 Δ` is one — the simplicial
set `Mor_Δ(⦋•⦌, W)` being the standard simplex on `W`, which is contractible (Stacks 08QD). What
this file adds is the observation that at `U_• = 𝟭` the construction collapses: evaluation on the
cosimplicial object is the identity functor, so the Moore complex of `ℱ(U_•)` is the
alternating-face-map complex of `ℱ` itself, and the right-hand side of Stacks 08Q9 becomes a
statement about `ℱ` with no cosimplicial object in it.

## Main definitions

* `Stacks.ChaoticSite.simplexCategoryLeftDerivedColimitNatIso`: **Stacks 08Q9 at `Δ`**, abelian
  coefficients, degreewise and natural in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.simplexCategoryModuleLeftDerivedColimitNatIso`: the same at
  module coefficients.
* `Stacks.ChaoticSite.AbelianValued.simplexCategoryMooreCochainNatIsoDerivedColimit`: the
  derived-category form, `Q(Moore ℱ) ≅ Lπ_!(ℱ[0])` in `D(Ab)`, natural in `ℱ`.

## Main results

* `Stacks.ChaoticSite.cosimplicialMooreComplex_id`,
  `Stacks.ChaoticSite.AbelianValued.mooreCochainComplex_id` and
  `Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex_id`: evaluation on `𝟭 Δ` is the
  identity, so each Moore-complex functor of the cosimplicial object is the plain
  alternating-face-map complex. All three are `rfl`.
* `Stacks.ChaoticSite.categoryHomology_simplexCategory`: the same statement written with
  `Stacks.CategoryHomology.categoryHomology`, which is the spelling the fibrewise machinery of
  Stacks 08PI and 08PJ consumes.

## Implementation notes

The three `rfl`s are what make this cheap. `cosimplicialMooreComplex U` is
`(whiskeringLeft _ _ _).obj U.op ⋙ alternatingFaceMapComplex _`; at `U = 𝟭 Δ` the whiskering
functor is the identity, because `(𝟭 Δ).op` is definitionally `𝟭 Δᵒᵖ` — `Functor.op` of the
identity has the same `obj` and `map` fields — and `𝟭 ⋙ F` is definitionally `F`. Mathlib has no
`Functor.op_id`, but none is needed: nothing has to be rewritten, only stated at the collapsed
type and accepted by `rfl`.

**Universes.** The `CosimplicialResolution` chain is single-universe: it asks for `C : Type u`
with `[SmallCategory C]` and coefficients in `AddCommGrpCat.{u}`, and at module coefficients for
a ring `B : Type u` as well. `SimplexCategory` is a `Type` with `Type`-valued homs, so `u = 0`
throughout here, and the module statement is at `ModuleCat.{0} B` for `B : Type`. Lifting the
chain to coefficients in a larger universe is not done here; a
consumer needing it should expect to transport along `AsSmall.{u} SimplexCategory` rather than to
reuse these statements.

**What this is and is not.** This is the *absolute* statement, for the point morphism
`Δ ⟶ ⋆`: `Lπ_!` here is the total left derived functor of the colimit over `Δᵒᵖ`. It is not the
relative statement for a projection `Δ × C ⟶ C`, which is what the cotangent-complex application
needs; passing between them is the fibrewise comparison of Stacks 08PI and 08PJ and is not done
here.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF), `π_!` on a chaotic site
  as the colimit.
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD), the contractibility of
  the standard simplices, which is what makes `𝟭 Δ` a point resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

/-- At `U_• = 𝟭 Δ` the Moore complex of the evaluation on `U_•` is the alternating-face-map
complex itself: evaluation on `𝟭` is the identity functor. -/
theorem cosimplicialMooreComplex_id :
    cosimplicialMooreComplex (𝟭 SimplexCategory) =
      alternatingFaceMapComplex AddCommGrpCat.{0} := rfl

/-- **Stacks 08Q9 at `C = Δ`.** For a simplicial abelian group `ℱ`, the homology `L_nπ_!` of `Δ`
with coefficients `ℱ` is the `n`th homology of the alternating-face-map complex of `ℱ`, naturally
in `ℱ`. -/
@[stacks 08Q9 "at C = Δ with U_• = 𝟭: L_n of the colimit over Δᵒᵖ is the homology of the \
alternating-face-map complex of the simplicial abelian group itself, there being no cosimplicial \
object left in the statement. Abelian coefficients in the universe of Δ, which is 0"]
def simplexCategoryLeftDerivedColimitNatIso (n : ℕ) :
    (colim : (SimplexCategoryᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0}).leftDerived n ≅
      alternatingFaceMapComplex AddCommGrpCat.{0} ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.down ℕ) n :=
  leftDerivedColimitNatIso (𝟭 SimplexCategory) isPointResolution_id_simplexCategory n

/-- **Stacks 08Q9 at `C = Δ`, in the `categoryHomology` spelling.** The homology of `Δ` with
coefficients in a simplicial abelian group is the Moore homology of that simplicial abelian
group. This is the form the fibrewise machinery of Stacks 08PI and 08PJ consumes. -/
@[stacks 08Q9 "at C = Δ, written with `Stacks.CategoryHomology.categoryHomology`"]
def categoryHomology_simplexCategory (F : SimplexCategoryᵒᵖ ⥤ AddCommGrpCat.{0}) (n : ℕ) :
    categoryHomology F n ≅
      ((alternatingFaceMapComplex AddCommGrpCat.{0}).obj F).homology n :=
  (simplexCategoryLeftDerivedColimitNatIso n).app F

namespace AbelianValued

/-- At `U_• = 𝟭 Δ` the extended Moore cochain complex of the evaluation on `U_•` is the extended
alternating-face-map complex of `ℱ` itself. -/
theorem mooreCochainComplex_id :
    mooreCochainComplex (𝟭 SimplexCategory) =
      alternatingFaceMapComplex AddCommGrpCat.{0} ⋙
        (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{0} := rfl

/-- **Stacks 08Q9 at `C = Δ`, in the derived category.** The extended alternating-face-map complex
of a simplicial abelian group is derived lower shriek of that simplicial abelian group placed in
degree zero, as an isomorphism of functors into `D(Ab)`. -/
@[stacks 08Q9 "at C = Δ, derived-category form, natural in the coefficient presheaf"]
def simplexCategoryMooreCochainNatIsoDerivedColimit :
    (alternatingFaceMapComplex AddCommGrpCat.{0} ⋙
        (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{0}) ⋙
        DerivedCategory.Q ≅
      HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ AddCommGrpCat.{0}) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit SimplexCategory AddCommGrpCat.{0} :=
  mooreCochainNatIsoDerivedColimit (𝟭 SimplexCategory) isPointResolution_id_simplexCategory

end AbelianValued

namespace ModuleValued

variable {B : Type} [Ring B]

/-- At `U_• = 𝟭 Δ` the Moore complex of the evaluation on `U_•` is the alternating-face-map
complex itself, at module coefficients. -/
theorem moduleCosimplicialMooreComplex_id :
    moduleCosimplicialMooreComplex (B := B) (𝟭 SimplexCategory) =
      alternatingFaceMapComplex (ModuleCat.{0} B) := rfl

/-- **Stacks 08Q9 at `C = Δ`, module coefficients.** For a simplicial `B`-module `ℱ`, the homology
`L_nπ_!` of `Δ` with coefficients `ℱ` is the `n`th homology of the alternating-face-map complex of
`ℱ`, naturally in `ℱ`, as `B`-modules. -/
@[stacks 08Q9 "at C = Δ with U_• = 𝟭, module coefficients: L_n of the colimit over Δᵒᵖ is the \
homology of the alternating-face-map complex of the simplicial B-module itself. The ring and the \
module sections lie in the universe of Δ, which is 0"]
def simplexCategoryModuleLeftDerivedColimitNatIso (n : ℕ) :
    (colim : (SimplexCategoryᵒᵖ ⥤ ModuleCat.{0} B) ⥤ ModuleCat.{0} B).leftDerived n ≅
      alternatingFaceMapComplex (ModuleCat.{0} B) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{0} B) (ComplexShape.down ℕ) n :=
  moduleLeftDerivedColimitNatIso (𝟭 SimplexCategory) isPointResolution_id_simplexCategory n

end ModuleValued

end Stacks.ChaoticSite

end
