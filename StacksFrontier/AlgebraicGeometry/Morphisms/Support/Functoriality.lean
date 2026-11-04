module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# The support of a sheaf of modules and exactness

The support of a sheaf of modules on a topological space is read off its stalks, so it responds
to exactness of a complex of sheaves of modules through the induced maps on stalks: a zero sheaf
has empty support, and the support of the middle term of a short complex which is exact in the
middle is covered by the supports of the two outer terms.

## Main results

* `SheafOfModules.supp_eq_empty_of_isZero`: a zero sheaf of modules has empty support.
* `SheafOfModules.supp_subset_union_of_exact`: for a short complex which is exact at its middle
  term, the support of that term is contained in the union of the supports of the outer two.
* `SheafOfModules.supp_subset_of_retract`: the support of a retract is contained in the support
  of the sheaf it retracts off; in particular the support of a direct summand is contained in
  the support of the sum.

## Implementation notes

Both proofs go through `AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor`, the functor
taking a sheaf of modules to the stalk at a point of its underlying sheaf of abelian groups; the
support is the set of points at which that abelian group is nontrivial. An exact short complex
is transported to stalks by
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, which detects exactness of
sheaves of modules pointwise, so neither statement needs a hypothesis on the sheaf of rings
beyond its being a sheaf of rings on a topological space.

Invariance of the support under an isomorphism is
`SheafOfModules.supp_eq_of_iso`, in `StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs`.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u

namespace SheafOfModules

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}

/-- A point lies in the support of a sheaf of modules exactly when the stalk functor to abelian
groups takes it to a nontrivial group there. -/
lemma mem_supp_iff_nontrivial_stalkAddCommGroupFunctor_obj (F : SheafOfModules.{u} R) (x : T) :
    x ∈ supp F ↔
      Nontrivial
        ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj F) :=
  mem_supp_iff_nontrivial_stalk F x

/-- **A zero sheaf of modules has empty support.** Its stalks are zero, hence have no nonzero
element. -/
lemma supp_eq_empty_of_isZero {F : SheafOfModules.{u} R} (hF : IsZero F) : supp F = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_supp_iff_nontrivial_stalkAddCommGroupFunctor_obj]
  exact not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).map_isZero hF))

/-- **Two out of three for supports.** If a short complex of sheaves of modules is exact at its
middle term, then the support of that term is contained in the union of the supports of the
outer two. A germ of the middle term at a point outside both outer supports is the image of a
germ of the first term, which is zero because the second map kills it. -/
lemma supp_subset_union_of_exact (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.Exact) :
    supp S.X₂ ⊆ supp S.X₁ ∪ supp S.X₃ := by
  intro x hx
  by_contra hxu
  have key (X : SheafOfModules.{u} R) (hX : x ∉ supp X)
      (a : (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj X) : a = 0 := by
    rw [mem_supp_iff_nontrivial_stalkAddCommGroupFunctor_obj] at hX
    have := not_nontrivial_iff_subsingleton.1 hX
    exact Subsingleton.elim a 0
  have h₁ := key S.X₁ fun h => hxu (.inl h)
  have h₃ := key S.X₃ fun h => hxu (.inr h)
  have hfun := (ShortComplex.ab_exact_iff_function_exact _).mp
    ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact R S).mp hS x)
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne
    (0 : (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj S.X₂)).mp
      ((mem_supp_iff_nontrivial_stalkAddCommGroupFunctor_obj S.X₂ x).mp hx)
  obtain ⟨b, hb⟩ := (hfun a).mp (h₃ _)
  refine ha ?_
  rw [← hb, h₁ b]
  exact map_zero _

/-- **The support of a retract is contained in the support of the sheaf it retracts off.** If
`i : F ⟶ G` has a retraction `r`, then the stalk functor at a point carries that retraction to
a retraction of abelian groups, and the identity of a retract of a zero object factors through
that object, hence vanishes. So a point outside the support of `G` is outside the support of
`F`.

Applied to `biprod.inl` and `biprod.fst` this says that the support of a direct summand is
contained in the support of the sum, which is the half of the saturation of a support condition
that does not mention the ambient category. -/
lemma supp_subset_of_retract {F G : SheafOfModules.{u} R} (i : F ⟶ G) (r : G ⟶ F)
    (hir : i ≫ r = 𝟙 F) : supp F ⊆ supp G := by
  intro x hx
  rw [mem_supp_iff_nontrivial_stalkAddCommGroupFunctor_obj] at hx ⊢
  by_contra hG
  have := not_nontrivial_iff_subsingleton.1 hG
  have hGz : IsZero ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj G) :=
    AddCommGrpCat.isZero_of_subsingleton _
  have hret : (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).map i ≫
      (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).map r =
      𝟙 ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj F) := by
    rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  have hFz : IsZero ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj F) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← hret, hGz.eq_zero_of_tgt
      ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).map i), zero_comp]
  exact (not_nontrivial_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero hFz)) hx

end SheafOfModules
