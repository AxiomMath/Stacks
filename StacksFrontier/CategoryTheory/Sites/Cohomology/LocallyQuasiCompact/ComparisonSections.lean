module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.LocallyQuasiCompactTerminalOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDirectImage

/-!
# Sections of the Zariski comparison inverse image

Let `S` be a locally quasi-compact Zariski situation, let `Y` be an object of its site and let
`π_Y : Sh(LC_Zar/Y) → Sh(Y_Zar)` be the comparison morphism of topoi of
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonAdjunction`. For a sheaf of sets
`H` on the small Zariski site of `Y`, the sections of `π_Y^{-1}H`

* over an open `U ⊆ Y`, viewed in the slice site, are the sections of `H` over `U`;
* over an arbitrary object `q : V ⟶ Y` of the slice site, are the global sections of the
  inverse image `q^{-1}H` on the small Zariski site of `V`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonSectionsIso`: sections of
  `π_Y^{-1}H` over the image of an open subset of `Y` are the sections of `H` over that open.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonGlobalSectionsIso`: the case of
  the top open subset, transported to the terminal object `𝟙 Y` of the slice site.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonSectionsOverIso`: sections of
  `π_Y^{-1}H` over an object `q : V ⟶ Y` are the global sections of `q^{-1}H` on `V`.

## Implementation notes

Each isomorphism is built by composing isomorphisms with `≪≫`, not by rewriting through the
coercion at `Sheaf.obj.obj (op _)`, which is defeq but not type-correct at `implicit`
transparency.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- Sections of `π_X^{-1}G` over the open subset `U ⊆ X`, viewed as an object of the slice site,
are the sections of `G` over `U`. -/
def comparisonSectionsIso (X : S.category)
    (G : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u v)))
    (U : Opens X.obj) :
    G.obj.obj (op U) ≅
      ((S.comparisonInverseImage.{u, w, v} X).obj G).obj.obj
        (op ((S.opensToSlice X).1.obj U)) := by
  haveI := comparisonAdjunction_unit_isIso.{u, w, v} S X
  haveI : IsIso ((S.comparisonAdjunction.{u, w, v} X).unit.app G) := inferInstance
  exact ((sheafToPresheaf _ _).mapIso
    (asIso ((S.comparisonAdjunction.{u, w, v} X).unit.app G))).app (op U)

/-- Sections of `π_X^{-1}G` over the terminal object `𝟙 X` of the slice site are the global
sections of `G`. -/
def comparisonGlobalSectionsIso (X : S.category)
    (G : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u v))) :
    G.obj.obj (op ⊤) ≅
      ((S.comparisonInverseImage.{u, w, v} X).obj G).obj.obj (op (Over.mk (𝟙 X))) :=
  comparisonSectionsIso.{u, w, v} S X G ⊤ ≪≫
    ((S.comparisonInverseImage.{u, w, v} X).obj G).obj.mapIso
      ((opensToSlice_top_isTerminal S X).uniqueUpToIso Over.mkIdTerminal).symm.op

/-- The sections of `π_Y^{-1}H` over an object `q : V ⟶ Y` of the localized Zariski site are the
global sections of the inverse image `q^{-1}H` on the small Zariski site of `V`. -/
def comparisonSectionsOverIso {V Y : S.category} (q : V ⟶ Y)
    (H : Sheaf (Opens.grothendieckTopology Y.obj) (Type (max u v))) :
    ((((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map q)).sheafPullback
            (Type (max u v))
            (Opens.grothendieckTopology
              ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
            (Opens.grothendieckTopology
              ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj V))).obj
          H).obj.obj (op ⊤)) ≅
      ((S.comparisonInverseImage.{u, w, v} Y).obj H).obj.obj (op (Over.mk q)) :=
  comparisonGlobalSectionsIso.{u, w, v} S V _ ≪≫
    ((sheafToPresheaf _ _).mapIso ((zariskiComparisonSquareIso.{u, w, v} S q).app H)).app
      (op (Over.mk (𝟙 V))) ≪≫
    ((S.comparisonInverseImage.{u, w, v} Y).obj H).obj.mapIso
      (eqToIso (congrArg Over.mk (Category.id_comp q))).op

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
