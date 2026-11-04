module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageCyclicCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SepClosedFieldConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFilteredColimit

/-!
# Cohomology with constant coefficients comes from finitely generated subgroups

An abelian group is the filtered colimit of its finitely generated subgroups
(`Stacks.EtaleCohomology.isColimitFGAddSubgroupCocone`). The constant sheaf functor is a left
adjoint, and étale cohomology of a quasi-compact and quasi-separated scheme
commutes with filtered colimits of abelian sheaves ([Stacks, Tag 03Q5]), so every class in
`H^p(Y, A)` comes from `H^p(Y, S)` for a finitely generated subgroup `S` of `A`. For a torsion
group `A`, such an `S` is finite.

This is the reduction "since `M` is `n`-torsion, it is the union of finite subgroups" in the proof
of [Stacks, Tag 0EYT].

## Main results

* `Stacks.EtaleCohomology.exists_fg_sheafH_map_eq` — a class in `H^p(Y, A)` comes from a finitely
  generated subgroup of `A`.
* `Stacks.EtaleCohomology.finite_of_fg_of_isTorsion` — a finitely generated subgroup of a torsion
  abelian group is finite.

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

variable {A : AddCommGrpCat.{u + 1}}

/-- A finitely generated subgroup of a torsion abelian group is finite. -/
theorem finite_of_fg_of_isTorsion (hA : IsAddTorsion A) (S : AddSubgroup A)
    (hS : S.FG) : Finite S := by
  have : AddGroup.FG S := (AddGroup.fg_iff_addSubgroup_fg S).2 hS
  have : Module.Finite ℤ S := Module.Finite.iff_addGroup_fg.2 this
  exact Module.finite_of_fg_torsion S (fun x => by
    obtain ⟨n, hn, hx⟩ := (hA x.1).exists_nsmul_eq_zero
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    exact Subtype.ext (by simpa using hx))

/-- **A class with constant coefficients comes from a finitely generated subgroup.** Let `Y` be a
quasi-compact and quasi-separated scheme and `A` an abelian group. Every class in `H^p(Y, A)`, with
coefficients in the constant sheaf, is the image of a class in `H^p(Y, S)` for a finitely
generated subgroup `S` of `A`, under the map induced by the inclusion `S ⊆ A`. -/
theorem exists_fg_sheafH_map_eq {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (A : AddCommGrpCat.{u + 1}) (p : ℕ)
    (ζ : Sheaf.H.{u + 1} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) p) :
    ∃ (S : AddSubgroup A) (_ : S.FG)
      (ζ' : Sheaf.H.{u + 1}
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of S)) p),
      Sheaf.H.map ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom S.subtype)) p ζ' = ζ := by
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 Y)) := MorphismProperty.Over.mkIdTerminal _ _
  have : PreservesColimitsOfShape (FGAddSubgroup A)
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    (constantSheafAdj _ _ hT).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := preservesColimitsOfShape_functorH_smallEtale Y p (FGAddSubgroup A)
  have hc := isColimitOfPreserves
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ smallEtaleFunctorH Y p)
    (isColimitFGAddSubgroupCocone A)
  obtain ⟨S, ζ', h⟩ := Concrete.isColimit_exists_rep _ hc ζ
  exact ⟨S.1, S.2, ζ', h⟩

end Stacks.EtaleCohomology

end
