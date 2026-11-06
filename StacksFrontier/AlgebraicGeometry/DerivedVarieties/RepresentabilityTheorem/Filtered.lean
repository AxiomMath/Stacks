module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute

/-!
# Arrows along a triangulated functor form a filtered category

Let `ι : C ⥤ D` be a triangulated functor between pretriangulated categories. For every object
`X` of `D` the category of arrows `ι.obj E ⟶ X`, with `E` ranging over `C`, is filtered. The
case of interest is the inclusion of a full triangulated subcategory, where this says that
every object of `D` is approximated by a filtered system of objects of `C`.

## Main results

* `CategoryTheory.isFiltered_costructuredArrow`: the category of arrows to a fixed object along
  a triangulated functor is filtered.

## Implementation notes

The category of arrows in the source is Mathlib's `CategoryTheory.CostructuredArrow ι X`. The
underlying argument uses only the axioms of a pretriangulated category — in particular not the
octahedral axiom — so the hypotheses are stated for pretriangulated categories. It also uses
only that `ι` commutes with shifts and preserves distinguished triangles: neither fullness nor
faithfulness is needed. The statement is therefore given for an arbitrary triangulated functor,
with the inclusion of a full triangulated subcategory as a special case.

## References

* [Stacks Project, Tag 0FYF](https://stacks.math.columbia.edu/tag/0FYF)
-/

@[expose] public section

open CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory

universe v v' u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (ι : C ⥤ D) [ι.CommShift ℤ] [ι.IsTriangulated]

/-- **Stacks Project, Tag 0FYF.** The category of arrows to a fixed object along a triangulated
functor is filtered. -/
@[stacks 0FYF]
lemma isFiltered_costructuredArrow (X : D) :
    IsFiltered (CostructuredArrow ι X) where
  nonempty := ⟨CostructuredArrow.mk (0 : ι.obj (0 : C) ⟶ X)⟩
  cocone_objs A B := by
    let Z : CostructuredArrow ι X := CostructuredArrow.mk
      (ι.map biprod.fst ≫ A.hom + ι.map biprod.snd ≫ B.hom)
    refine ⟨Z, CostructuredArrow.homMk biprod.inl ?_,
      CostructuredArrow.homMk biprod.inr ?_, trivial⟩
    all_goals
      dsimp [Z]
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        ← ι.map_comp, ← ι.map_comp]
      simp
  cocone_maps {A B} f g := by
    obtain ⟨Z, q, r, hT⟩ :=
      Pretriangulated.distinguished_cocone_triangle (f.left - g.left)
    let T := Pretriangulated.Triangle.mk (f.left - g.left) q r
    obtain ⟨c, hc, _⟩ := Pretriangulated.complete_distinguished_triangle_morphism
      (ι.mapTriangle.obj T) (Pretriangulated.Triangle.mk
        (0 : (0 : D) ⟶ X) (𝟙 X) (0 : X ⟶ _))
      (ι.map_distinguished T hT) (Pretriangulated.contractible_distinguished₁ X)
      0 B.hom (by
        show ι.map (f.left - g.left) ≫ B.hom = _
        rw [ι.map_sub, Preadditive.sub_comp, CostructuredArrow.w f,
          CostructuredArrow.w g, sub_self, zero_comp])
    refine ⟨CostructuredArrow.mk c, CostructuredArrow.homMk q ?_,
      CostructuredArrow.hom_ext _ _ ?_⟩
    · show ι.map q ≫ c = B.hom
      simpa using (show ι.map q ≫ c = B.hom ≫ 𝟙 X from hc)
    · dsimp
      simpa only [Preadditive.sub_comp, sub_eq_zero] using
        (show (f.left - g.left) ≫ q = 0 from
          Pretriangulated.comp_distTriang_mor_zero₁₂ T hT)

end CategoryTheory
