module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableReplacementAsANerve
import StacksCore.Tactic.StacksAttribute

/-!
# Acyclicity of the simplicial replacement of a representable

Let `C` be a small category with the chaotic topology and let `U` be an object of `C`. The
extension by zero `j_!ℤ` of the constant integer sheaf from the slice site over `U`
(`Stacks.CategoryHomology.integerExtensionByZero`) is the sheaf whose simplicial replacement
computes the homology of `C` with representable coefficients. This file proves that that
replacement is acyclic: its homology vanishes in every positive degree.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map`: a functor carries a
  homotopy equivalence of simplicial objects to a homotopy equivalence.
* `Stacks.CategoryHomology.representableReplacementComplex_homology_isZero`: the simplicial
  replacement complex of `j_!ℤ` has vanishing homology in every positive degree.

## Implementation notes

Vanishing is expressed as `CategoryTheory.Limits.IsZero` of the homology object rather than as
an `ExactAt`.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject

universe v₁ v₂ u₁ u₂

/-- A functor carries a homotopy equivalence of simplicial objects to a homotopy equivalence. -/
theorem homotopyEquivalences_whiskering_map {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] (F : A ⥤ B) {X Y : SimplicialObject A} {f : X ⟶ Y}
    (hf : homotopyEquivalences A f) :
    homotopyEquivalences B (((whiskering A B).obj F).map f) := by
  let W := (whiskering A B).obj F
  obtain ⟨g, hfg, hgf⟩ := hf
  refine ⟨W.map g, ?_, ?_⟩
  · simpa only [W.map_comp, W.map_id] using
      Relation.EqvGen.map (fun a : X ⟶ X ↦ W.map a)
        (fun _ _ (h : Nonempty (Homotopy ..)) ↦ ⟨h.some.whiskerRight F⟩) hfg
  · simpa only [W.map_comp, W.map_id] using
      Relation.EqvGen.map (fun a : Y ⟶ Y ↦ W.map a)
        (fun _ _ (h : Nonempty (Homotopy ..)) ↦ ⟨h.some.whiskerRight F⟩) hgf

end CategoryTheory.SimplicialObject

namespace Stacks.CategoryHomology

universe u

variable {C : Type u} [SmallCategory C]

/-- The simplicial replacement complex of the extension by zero of the
constant integer sheaf from the slice site over `U` has vanishing homology in every positive
degree. -/
@[stacks 08PG "representable_acyclic"]
theorem representableReplacementComplex_homology_isZero (U : C) (n : ℕ) (hn : 0 < n) :
    IsZero
      ((simplicialReplacementComplex
        ((sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).obj
          (integerExtensionByZero U))).homology n) := by
  let P := (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}
  obtain ⟨f, hf⟩ := nerveOver_homotopyEquivalent_point U
  let W := (SimplicialObject.whiskering (Type u) AddCommGrpCat).obj AddCommGrpCat.free
  let A := AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}
  have hhom := (quasiIsoAt_iff_isIso_homologyMap _ n).mp
      ((homotopyEquivalences_le_quasiIso AddCommGrpCat (ComplexShape.down ℕ) _
        (AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map
          (SimplicialObject.homotopyEquivalences_whiskering_map AddCommGrpCat.free hf))).quasiIsoAt
        n)
  let X := AddCommGrpCat.free.obj PUnit.{u + 1}
  let e : A.obj (W.obj P) ≅ ChainComplex.alternatingConst.obj X :=
    A.mapIso (Functor.constComp SimplexCategoryᵒᵖ PUnit.{u + 1} AddCommGrpCat.free) ≪≫
      AlgebraicTopology.alternatingFaceMapComplexConst.app X
  have hzPoint : IsZero ((A.obj (W.obj P)).homology n) :=
    (ChainComplex.alternatingConst_exactAt X n hn.ne').isZero_homology.of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).mapIso e)
  exact (hzPoint.of_iso (asIso (HomologicalComplex.homologyMap (A.map (W.map f)) n))).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).mapIso
      (representableReplacementComplexIsoFreeNerve U))

end Stacks.CategoryHomology
