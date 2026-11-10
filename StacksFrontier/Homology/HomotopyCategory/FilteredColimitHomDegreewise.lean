module

public import StacksFrontier.Homology.HomotopyCategory.FilteredColimitHom
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!
# The four hypotheses of the ring-level colimit computation, from a degreewise colimit

`StacksFrontier/Homology/HomotopyCategory/FilteredColimitHom.lean` proves the ring-level heart of
Stacks 09RE — `Stacks.FilteredColimitHom.exists_descends_derived` and
`Stacks.FilteredColimitHom.exists_le_eq_of_eq_derived` — from four hypotheses about a directed
system `N` of complexes of `R`-modules with transition maps `t`, a complex `P` and maps `ι` to it:

* `htrans`, that the transition maps compose;
* `hcompat`, that the maps to `P` are compatible with them;
* `hsurj`, that every element of `P.X n` comes from some `(N i).X n`;
* `hzero`, that an element of `(N i).X n` dying in `P.X n` dies at a later stage.

The last two are the crux: they are assertions about the *modules* in a single degree, and they are
the only place where "`P` is the colimit of the `N i`" is used.  Those theorems take them as
hypotheses and are therefore universe-polymorphic in the index; nothing here changes that.

**This file derives all four from a diagram of complexes with a degreewise colimit cocone.**  That
is the shape in which a limit of algebraic spaces delivers them, and it is also the shape in which
the index universe matters.

## The universe restriction, and where it is imposed

The two crux clauses are proved below *only for an index type in the universe of the modules*,
`J : Type u` for `ModuleCat.{u} R`.  The restriction is imposed exactly here and nowhere else: it
is what makes `CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
`CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists` applicable, i.e. what makes the
forgetful functor of `ModuleCat.{u} R` preserve the filtered colimit, i.e. what makes a filtered
colimit of modules describable by its elements at all.  Over a larger index there is no such
description and the two clauses do not follow from the categorical colimit.

This is faithful to the source and not a weakening.  Situation 09RD takes a directed system of
schemes, and Situation 09RH a directed system of algebraic spaces, indexed by a set that lives in
the universe of the schemes; the scheme-level Stacks 09RE is proved in this library at exactly that
restriction (`AlgebraicGeometry.DescentSituation.isHomColimit`, whose index is `I : Type u`), and
over an index set one universe up the statement is **false**:
`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/Counterexample.lean` exhibits a situation
of type 09RD indexed by a preorder in `Type (u+1)` and an `E₀ = K₀ = 𝒪_{S₀}` which is perfect,
pseudo-coherent, of finite Tor dimension and with quasi-coherent cohomology, for which the
conclusion fails.  So an index-universe restriction is not optional for any route to 09RE or 09RI,
and the clause it has to sit on is the colimit assertion about the modules.

## Main results

* `Stacks.FilteredColimitHom.map_comp_map`: `htrans` — the transition maps of the diagram compose.
* `Stacks.FilteredColimitHom.map_comp_ι`: `hcompat` — the cocone is compatible with them.
* `Stacks.FilteredColimitHom.exists_stage_of_isColimit_eval`: `hsurj`.
* `Stacks.FilteredColimitHom.exists_le_map_eq_zero_of_isColimit_eval`: `hzero`.

## References

* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 36.29.1 (Tag 09RD)](https://stacks.math.columbia.edu/tag/09RD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FilteredColimitHom

section Degreewise

variable {R : Type u} [Ring R] {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ) {c : Cocone F}

omit [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- **The transition maps of a diagram of complexes compose.**  This is the hypothesis `htrans` of
`Stacks.FilteredColimitHom.exists_descends_derived` for the system `i ↦ F.obj i` with transition
maps `F.map (homOfLE h)`.  The proof `h.trans h'` on the right is interchangeable with any other
proof of `i ≤ k`, a morphism of a preorder carrying no information beyond its existence. -/
theorem map_comp_map {i j k : J} (h : i ≤ j) (h' : j ≤ k) :
    F.map (homOfLE h) ≫ F.map (homOfLE h') = F.map (homOfLE (h.trans h')) := by
  rw [← F.map_comp]
  congr 1

omit [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- **The cocone of a diagram of complexes is compatible with its transition maps.**  This is the
hypothesis `hcompat` of `Stacks.FilteredColimitHom.exists_descends_derived`. -/
theorem map_comp_ι {i j : J} (h : i ≤ j) : F.map (homOfLE h) ≫ c.ι.app j = c.ι.app i :=
  c.w (homOfLE h)

/-- **Joint surjectivity in each degree**: if the cocone `c` is a colimit in every degree, every
element of a degree of its vertex comes from that degree of some stage.  This is the hypothesis
`hsurj` of `Stacks.FilteredColimitHom.exists_descends_derived`.

The index lies in the universe of the modules; see "The universe restriction" in this file's
module documentation for why the clause is proved only there. -/
theorem exists_stage_of_isColimit_eval
    (hc : ∀ n : ℤ, IsColimit
      ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapCocone c))
    (n : ℤ) (x : c.pt.X n) :
    ∃ (i : J) (y : (F.obj i).X n), (c.ι.app i).f n y = x :=
  Concrete.isColimit_exists_rep _ (hc n) x

/-- **Eventual vanishing in each degree**: if the cocone `c` is a colimit in every degree, an
element of a degree of a stage whose image in the vertex is zero is already carried to zero by a
transition map.  This is the hypothesis `hzero` of
`Stacks.FilteredColimitHom.exists_descends_derived`.

The index lies in the universe of the modules; see "The universe restriction" in this file's
module documentation for why the clause is proved only there. -/
theorem exists_le_map_eq_zero_of_isColimit_eval
    (hc : ∀ n : ℤ, IsColimit
      ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapCocone c))
    (n : ℤ) (i : J) (y : (F.obj i).X n) (h : (c.ι.app i).f n y = 0) :
    ∃ (j : J) (hij : i ≤ j), (F.map (homOfLE hij)).f n y = 0 := by
  have h0 : (c.ι.app i).f n y = (c.ι.app i).f n (0 : (F.obj i).X n) := by
    rw [h, map_zero]
  obtain ⟨k, g, g', hk⟩ := (Concrete.isColimit_rep_eq_iff_exists
    (F ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n) (hc n)
    y (0 : (F.obj i).X n)).1 h0
  refine ⟨k, leOfHom g, ?_⟩
  have hg : F.map (homOfLE (leOfHom g)) = F.map g := by
    congr 1
  rw [hg]
  exact hk.trans (map_zero _)

end Degreewise

end Stacks.FilteredColimitHom

end
