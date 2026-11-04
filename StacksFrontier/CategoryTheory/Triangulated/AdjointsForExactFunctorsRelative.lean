module

public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors

/-!
# A relative form of Stacks 09J1

Let `F ⊣ G` be an adjunction between pretriangulated categories with `F` fully faithful and `G`
triangulated, and let `P` be a triangulated subcategory of the target of `F`, closed under
isomorphisms and containing the image of `F`, on which the kernel of `G` is zero. Then the counit
of the adjunction is invertible at every object of `P`.

This module extends `StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors`.

## Main results

* `isIso_counit_app_of_fullyFaithful_of_ker_eq_zero`: the counit of `F ⊣ G` is invertible at
  every object of `P`.

## References

* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public section


end

section

@[expose] public section


open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Limits

universe v v' u u'

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v'} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']

variable (F : D ⥤ D') (G : D' ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]

omit [IsTriangulated D] [IsTriangulated D'] [F.CommShift ℤ] in
/-- **The relative form of Stacks 09J1.** Let `F ⊣ G` with `F` fully faithful and `G` exact, and
let `P` be a triangulated subcategory of the target of `F`, closed under isomorphisms and
containing the image of `F`, on which the kernel of `G` is zero. Then the counit is invertible at
every object of `P`, so `P` is the essential image of `F`. -/
theorem isIso_counit_app_of_fullyFaithful_of_ker_eq_zero
    [G.IsTriangulated] [F.Full] [F.Faithful] (adj : F ⊣ G) (P : ObjectProperty D')
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] (hF : ∀ X : D, P (F.obj X))
    (hker : ∀ X : D', P X → IsZero (G.obj X) → IsZero X) (X : D') (hX : P X) :
    IsIso (adj.counit.app X) := by
  have hunit : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful adj
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle (adj.counit.app X)
  have hGT := Functor.IsTriangulated.map_distinguished
    (F := G) (Pretriangulated.Triangle.mk (adj.counit.app X) g h) hT
  have hGiso : IsIso (G.map (adj.counit.app X)) :=
    IsIso.of_isIso_comp_left (adj.unit.app (G.obj X)) (G.map (adj.counit.app X))
  have hGZ : IsZero (G.obj Z) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (G.mapTriangle.obj (Pretriangulated.Triangle.mk (adj.counit.app X) g h)) hGT hGiso
  have hPZ : P Z := P.ext_of_isTriangulatedClosed₃ _ hT (hF _) hX
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (Pretriangulated.Triangle.mk (adj.counit.app X) g h) hT).mp (hker Z hPZ hGZ)

end

end
