module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.LocallyQuasiCompactTerminalOpen

/-!
# Sections of the comparison inverse image

Let `X` be an object of the locally quasi-compact Zariski site, let `F` be a sheaf of sets on the
space `X`, and let `h : W ⟶ X` be an object of the localized Zariski site `LC_Zar/X`. The
sections of the comparison inverse image `π_X^{-1}F` over that object are the global sections of
the inverse image of `F` along the underlying continuous map of `h`:

`(π_X^{-1}F)(h : W ⟶ X) = Γ(W, h^{-1}F)`.

This is the displayed formula of Stacks 09X3, for the Zariski topology.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImageSectionsIso`: the
  displayed isomorphism, for coefficients of types in any universe containing the universe of
  the spaces.

## Implementation notes

The formula is derived from two clauses of Stacks 0DCU:

* the commutative square of clause (5), `zariskiComparisonSquareIso`, applied to the morphism
  `h : W ⟶ X` of the site itself, identifies the restriction of `π_X^{-1}F` to `LC_Zar/W` with
  `π_W^{-1}(h^{-1}F)`;
* the unit clause (3) on sheaves of sets, `comparisonAdjunction_unit_isIso`, evaluated at the
  top open subset of `W`, identifies the global sections of `π_W^{-1}G` on `LC_Zar/W` with
  `Γ(W, G)`.

Composing the two gives the formula, once sections over the terminal object are matched up: the
object `h : W ⟶ X` of `LC_Zar/X` is the image under `Over.map h` of the terminal object of
`LC_Zar/W`, which is `opensToSlice ⊤` by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_top_isTerminal`, and the
comparison direct image is restriction along `opensToSlice`, so sections of `π_{W,*}H` over `⊤`
*are* sections of `H` over that terminal object.

The inverse image `h^{-1}F` on the right-hand side is the sheaf pullback along `Opens.map h`,
i.e. the usual inverse image of sheaves on topological spaces.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X : S.category} (W : Over X)

/-- The object `h : W ⟶ X` of the localized Zariski site is the image under `Over.map h` of the
terminal object `opensToSlice ⊤` of the localized Zariski site of `W`. -/
def overMapOpensToSliceTopIso :
    (Over.map W.hom).obj ((S.opensToSlice W.left).1.obj ⊤) ≅ W :=
  (Over.map W.hom).mapIso
      ((opensToSlice_top_isTerminal S W.left).uniqueUpToIso Over.mkIdTerminal) ≪≫
    Over.isoMk (Iso.refl _) (by simp)

/-- The inverse image of sheaves of sets along the underlying continuous map of a morphism of
the site: this is the `h^{-1}` of the formula of Stacks 09X3, the usual inverse image of sheaves
on topological spaces. -/
abbrev spaceInverseImage {X' Y' : S.category} (h : X' ⟶ Y') :
    Sheaf (Opens.grothendieckTopology Y'.obj) (Type (max u t)) ⥤
      Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t)) :=
  (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map h)).sheafPullback
    (Type (max u t)) (Opens.grothendieckTopology Y'.obj)
    (Opens.grothendieckTopology X'.obj)

/-- **The displayed formula of Stacks 09X3, for the Zariski topology.** The sections of the
comparison inverse image `π_X^{-1}F` over an object `h : W ⟶ X` of the localized Zariski site
are the global sections of the inverse image `h^{-1}F` of `F` along the underlying continuous
map of `h`:

`(π_X^{-1}F)(h : W ⟶ X) = Γ(W, h^{-1}F)`.

The coefficients are types in any universe containing the universe of the spaces. -/
def comparisonInverseImageSectionsIso
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :
    ((comparisonInverseImage.{u, w, t} S X).obj F).obj.obj (op W) ≅
      ((spaceInverseImage.{u, w, t} S W.hom).obj F).obj.obj (op ⊤) := by
  have hunit : IsIso (comparisonAdjunction.{u, w, t} S W.left).unit :=
    comparisonAdjunction_unit_isIso.{u, w, t} S W.left
  let eSquare := (zariskiComparisonSquareIso.{u, w, t} S W.hom).app F
  refine ((comparisonInverseImage.{u, w, t} S X).obj F).obj.mapIso
      (overMapOpensToSliceTopIso S W).op ≪≫ ?_
  refine ((sheafToPresheaf _ _).mapIso eSquare).symm.app
      (op ((S.opensToSlice W.left).1.obj ⊤)) ≪≫ ?_
  exact (((sheafToPresheaf _ _).mapIso
    (asIso ((comparisonAdjunction.{u, w, t} S W.left).unit.app
      ((spaceInverseImage.{u, w, t} S W.hom).obj F)))).app (op ⊤)).symm

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
