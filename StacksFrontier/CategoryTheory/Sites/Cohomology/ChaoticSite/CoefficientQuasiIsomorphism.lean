module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Homology of a category under a coefficient map it inverts

Let `C` be a small category carrying the chaotic topology, so that `L_nπ_!(ℱ)` is the degree `n`
left derived functor of the colimit over `Cᵒᵖ` applied to the abelian presheaf `ℱ`
(`Stacks.ChaoticSite.lowerShriek_pointSections_colimitIso`), and let `U_•` be a cosimplicial
object of `C` which is a point resolution, so that `L_nπ_!(ℱ) = H_n(ℱ(U_•))`
(`Stacks.ChaoticSite.leftDerivedColimitNatIso`).

Let `a : 𝒪 ⟶ 𝒪'` be a morphism of abelian presheaves such that `L_nπ_!(a)` is invertible. This
file proves that for every object `W` of `C`, `L_nπ_!` also inverts the induced morphism
`j_{W!}𝒪_W ⟶ j_{W!}𝒪'_W` of extensions by zero.

Here `j_{W!}ℱ_W` is the abelian presheaf `V ↦ ⊕_{V ⟶ W} ℱ(V)`, the copower of `ℱ` by the
representable presheaf of `W`; for the chaotic topology this is extension by zero from the slice
`C/W` of the restriction of `ℱ`. Evaluated on `U_•` it is the product of the simplicial set
`Mor_C(U_•, W)` with the simplicial abelian group `ℱ(U_•)`, and `Mor_C(U_•, W)` is homotopy
equivalent to a singleton by the point resolution hypothesis, so the two projections onto
`𝒪(U_•)` and `𝒪'(U_•)` are inverted by homology.

## Main definitions

* `Stacks.ChaoticSite.extensionByZeroPresheaf` and
  `Stacks.ChaoticSite.extensionByZeroPresheafMap`: the abelian presheaf `j_{W!}ℱ_W` on a chaotic
  site, as the copower of `ℱ` by the presheaf represented by `W`, and its functoriality.

## Main results

* `Stacks.ChaoticSite.isIso_leftDerivedPointLowerShriek_map_iff`: `L_nπ_!` along the point
  morphism of the chaotic site inverts a morphism of abelian sheaves exactly when the left derived
  functor of the colimit inverts the underlying morphism of presheaves.
* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerProj`: the projection
  `j_{W!}ℱ_W ⟶ ℱ` is inverted by `L_nπ_!`.
* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero`: if `L_nπ_!(a)` is
  invertible then so is `L_nπ_!(j_{W!}a)`.

## Implementation notes

The homotopy invariance of the product of a simplicial set with a simplicial object is
`CategoryTheory.SimplicialObject.isIso_homologyMap_copowerMap`; the evaluation of `j_{W!}ℱ_W` on
`U_•` is such a product by `CategoryTheory.Functor.comp_copower` and
`CategoryTheory.Functor.whiskerLeft_copowerMap`, both of which hold by `rfl`.

Everything is stated for the left derived functors of the colimit over `Cᵒᵖ`, and
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff` is the criterion used.
`isIso_leftDerivedColimit_map_extensionByZero` assumes `L_nπ_!(a)` invertible only in the degree
in which the conclusion is drawn, unlike
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerMap`, which assumes it in every
degree.

Scope: `isIso_leftDerivedColimit_map_extensionByZero` treats the generators `j_{W!}𝒪_W`, with
`Lπ_!` read as the left derived functor of the colimit over `Cᵒᵖ`. It does not identify
`j_{W!}𝒪_W ⊗^L_𝒪 𝒪'` with `j_{W!}𝒪'_W`, nor reduce an arbitrary object `K` of `D(𝒪)` to bounded
above complexes of direct sums of these generators: it is about `Lπ_!` alone and mentions no
tensor product.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe u

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The extension by zero of an abelian presheaf from a slice of a chaotic site**, `j_{W!}ℱ_W`:
the abelian presheaf `V ↦ ⊕_{V ⟶ W} ℱ(V)`, the copower of `ℱ` by the presheaf represented by
`W`. For the chaotic topology, where every presheaf is a sheaf, this is the extension by zero of
the restriction of `ℱ` to `C/W`. -/
abbrev extensionByZeroPresheaf (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (W : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ℱ.copower (yoneda.obj W)

/-- **The extension by zero of a morphism of abelian presheaves**, `j_{W!}a_W`: on the summand
of `(j_{W!}ℱ_W)(V)` indexed by `g : V ⟶ W` it is `a` on the sections over `V`, landing in the
summand indexed by the same `g`. -/
abbrev extensionByZeroPresheafMap {ℱ 𝒢 : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : ℱ ⟶ 𝒢) (W : C) :
    extensionByZeroPresheaf ℱ W ⟶ extensionByZeroPresheaf 𝒢 W :=
  Functor.copowerMap a (𝟙 (yoneda.obj W))

/-- **A criterion for the lower shriek of the point morphism to invert a map.** On a small
chaotic site with a point resolution `U_•`, the degree `n` left derived functor of `π_!`
inverts a morphism of abelian sheaves exactly when the left derived functor of the colimit
over `Cᵒᵖ` inverts the underlying morphism of presheaves. -/
lemma isIso_leftDerivedPointLowerShriek_map_iff (hU : IsPointResolution U)
    {ℱ 𝒢 : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}} (a : ℱ ⟶ 𝒢) (n : ℕ) :
    IsIso (((abelianPointLowerShriek C).leftDerived n).map a) ↔
      IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
        ((sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).map a)) := by
  refine Iff.trans ?_ ((NatIso.isIso_map_iff (leftDerivedPointLowerShriekNatIso C U hU n) a).trans
    (isIso_leftDerivedColimit_map_iff U hU
      ((sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).map a) n).symm)
  refine ⟨fun _ ↦ inferInstanceAs (IsIso ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).map
    (((abelianPointLowerShriek C).leftDerived n).map a))), fun h ↦ ?_⟩
  have : IsIso ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).map
    (((abelianPointLowerShriek C).leftDerived n).map a)) := h
  exact isIso_of_reflects_iso _ (pointSections.{u, u + 1, u} AddCommGrpCat.{u})

/-- **`L_nπ_!(j_{W!}ℱ_W) = L_nπ_!(ℱ)` on a chaotic site with a point resolution**, the comparison
being the projection of the copower. Evaluated on `U_•`, `j_{W!}ℱ_W` is the product of the
simplicial set `Mor_C(U_•, W)` with the simplicial abelian group `ℱ(U_•)`, and `Mor_C(U_•, W)` is
homotopy equivalent to a singleton, so the projection is a homotopy equivalence of simplicial
abelian groups. -/
theorem isIso_leftDerivedColimit_map_copowerProj (hU : IsPointResolution U)
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (W : C) (n : ℕ) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
      (ℱ.copowerProj (yoneda.obj W))) := by
  rw [isIso_leftDerivedColimit_map_iff U hU _ n]
  exact SimplicialObject.isIso_homologyMap_copowerProj (U.op ⋙ ℱ) n
    (U.op ⋙ yoneda.obj W) (hU W)

/-- Let `C` be a small category with the chaotic topology,
let `U_•` be a cosimplicial object of `C` which is a point resolution, and let `a : 𝒪 ⟶ 𝒪'` be a
morphism of abelian presheaves such that `L_nπ_!(a)` is invertible. Then for every object `W` of
`C` the induced morphism `j_{W!}𝒪_W ⟶ j_{W!}𝒪'_W` of extensions by zero is also inverted by
`L_nπ_!`.

Evaluated on `U_•` the two extensions by zero are the products of the simplicial set
`Mor_C(U_•, W)` with the simplicial abelian groups `𝒪(U_•)` and `𝒪'(U_•)`, and `Mor_C(U_•, W)` is
homotopy equivalent to a singleton; so the projections to `𝒪(U_•)` and `𝒪'(U_•)` are inverted by
the homology of the Moore complex, which reduces the claim to the hypothesis on `a`. -/
@[stacks 08RX "the generators `j_{U!}O_U`; see the scope paragraph in the module docstring"]
theorem isIso_leftDerivedColimit_map_extensionByZero (hU : IsPointResolution U)
    {P P' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : P ⟶ P') (W : C) (n : ℕ)
    (ha : IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map a)) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
      (extensionByZeroPresheafMap a W)) := by
  rw [isIso_leftDerivedColimit_map_iff U hU _ n] at ha ⊢
  exact SimplicialObject.isIso_homologyMap_copowerMap (Functor.whiskerLeft U.op a) n ha
    (U.op ⋙ yoneda.obj W) (hU W)

end Stacks.ChaoticSite

end
