module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Vanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution

/-!
# The complex of a fibrewise point resolution computes the homology of the fibres

In the situation of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic`, for an abelian
presheaf `G` on the total category and an object `V` of the base, the homology of `G(A_{•,V})` is
the homology `H_n(C_V, G|_{C_V})` of the fibre category `C_V` with coefficients in the restriction
of `G` (Stacks 08PF), by Stacks 08Q9 applied to the point resolution `A_{•,V}` of `C_V`.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointMooreComplexHomologyEvalIso`: the value
  at `V` of the homology of the complex of presheaves `V ↦ G(A_{•,V})` is the homology of
  `G(A_{•,V})`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.categoryHomologyFiberIso`: that homology is
  the homology of the fibre over `V` with coefficients in `G`.

## Implementation notes

The fibre `C_V` has objects in `Type uC` and morphisms in `Type vC`, while the homology of a
category is defined for a small category (Stacks 08PF, at Mathlib's projective resolutions of
abelian presheaves on a small category). It is therefore taken on `AsSmall (C_V)`, the
equivalent small category with the same objects and universe-lifted morphisms, in the universe of
the sections; a point resolution of `C_V` is one of `AsSmall (C_V)`, the lift of a homotopy
equivalence of simplicial sets being a homotopy equivalence.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}

/-- The value at `V` of the homology of the complex of presheaves `V ↦ G(A_{•,V})` is the homology
of the Moore complex of `G(A_{•,V})`. -/
def pointMooreComplexHomologyEvalIso (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
    (V : s.base.C) (n : ℕ) :
    (((pointMooreComplex s A).obj G).homology n).obj (op V) ≅
      ((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
        ((A.obj V).op ⋙ G)).homology n :=
  (ShortComplex.mapHomologyIso (((pointMooreComplex s A).obj G).sc n)
      ((evaluation s.base.Cᵒᵖ AddCommGrpCat.{max w uD vD uC vC}).obj (op V))).symm ≪≫
    eqToIso (show ((((pointMooreComplex s A).obj G).sc n).map
        ((evaluation s.base.Cᵒᵖ AddCommGrpCat.{max w uD vD uC vC}).obj (op V))).homology =
        ((alternatingFaceMapComplex AddCommGrpCat.{max w uD vD uC vC}).obj
          ((A.obj V).op ⋙ G)).homology n by
      have hmap := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
        ((evaluation s.base.Cᵒᵖ AddCommGrpCat.{max w uD vD uC vC}).obj (op V)))
        ((pointEvaluation s A).obj G)
      change ((((alternatingFaceMapComplex _ ⋙ ((evaluation s.base.Cᵒᵖ
        AddCommGrpCat.{max w uD vD uC vC}).obj (op V)).mapHomologicalComplex _).obj
          ((pointEvaluation s A).obj G)).sc n).homology) = _
      rw [hmap]
      rfl)

variable (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
      SimplicialObject.homotopyEquivalences (Type vC) f)

/-- The cosimplicial object `A_{•,V}` of the small model of the fibre over `V`. -/
abbrev smallFibreResolution (V : s.base.C) :
    CosimplicialObject (AsSmall.{max w uD vD uC vC} (s.p.Fiber V)) :=
  Functor.Fiber.inducedFunctor (Functor.congr_obj hA V) ⋙ AsSmall.up

include hres in
/-- `A_{•,V}` is a point resolution of the small model of the fibre over `V`. -/
lemma isPointResolution_smallFibreResolution (V : s.base.C) :
    Stacks.ChaoticSite.IsPointResolution (smallFibreResolution s hA V) := by
  intro W
  obtain ⟨f₀, hf₀⟩ := hres V (AsSmall.down.obj W)
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1} ⋙
      uliftFunctor.{max w uD vD uC vC} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{max w uD vD uC vC + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  let e' : (smallFibreResolution s hA V).op ⋙ yoneda.obj W ≅
      ((Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙
          yoneda.obj (AsSmall.down.obj W)) ⋙
        uliftFunctor.{max w uD vD uC vC} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact ⟨e'.hom ≫ Functor.whiskerRight f₀ uliftFunctor ≫ e.hom,
    CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor hf₀)⟩

/-- The restriction of a presheaf on the total category to the small model of the fibre over
`V`. -/
abbrev smallFiberRestriction (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C) :
    (AsSmall.{max w uD vD uC vC} (s.p.Fiber V))ᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC} :=
  AsSmall.down.op ⋙ (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G

include hres in
/-- **The complex of presheaves `V ↦ G(A_{•,V})` computes the homology of the fibres**: its
homology at `V` in degree `n` is `H_n(C_V, G|_{C_V})`, by Stacks 08Q9 for the point resolution
`A_{•,V}` of the fibre `C_V`. -/
def categoryHomologyFiberIso (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C)
    (n : ℕ) :
    (((pointMooreComplex s A).obj G).homology n).obj (op V) ≅
      CategoryHomology.categoryHomology.{max w uD vD uC vC, max w uD vD uC vC}
        (smallFiberRestriction s G V) n :=
  pointMooreComplexHomologyEvalIso s G V n ≪≫
    ((Stacks.ChaoticSite.leftDerivedColimitNatIso (smallFibreResolution s hA V)
      (isPointResolution_smallFibreResolution s hA hres V) n).app
        (smallFiberRestriction s G V)).symm

end Stacks.Sites.FibredCategory.FibredCategorySituation
