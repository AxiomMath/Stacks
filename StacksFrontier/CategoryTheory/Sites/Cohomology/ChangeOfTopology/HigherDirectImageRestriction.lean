module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyViaSectionComplex
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Restriction and the higher direct images of a change of topology

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology
morphism. For a morphism `u : V ⟶ X` of the site, restriction along `u` carries abelian sheaves
on the site localized at `X` to abelian sheaves on the site localized at `V`, and the square of
topoi of Stacks 0EZ2 says that it commutes with `ε_*` on the nose:

`ε_{X,*} ⋙ (-)|_V = (-)|_V ⋙ ε_{V,*}`.

This file derives the same identity for the higher direct images,

`(R^i ε_{X,*} ℱ)|_V ≅ R^i ε_{V,*} (ℱ|_V)`,

and reads off its consequence for the vanishing condition `(V_n)` of the situation: to obtain
`R^i ε_{X,*} ℱ = 0` for every object `X` and every `ℱ` in `𝒜_X` it suffices that the global
sections of `R^i ε_{X,*} ℱ` vanish, again for every `X` and every `ℱ` in `𝒜_X`.

## Main definitions

* `Stacks.ComparingTopologies.restrictionRightDerivedIso`: the isomorphism
  `(R^i ε_{X,*} ℱ)|_V ≅ R^i ε_{V,*} (ℱ|_V)`.

## Main results

* `Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology`: an exact functor has no
  higher right derived functors.
* `Stacks.ComparingTopologies.abelianComparisonPushforward_comp_overMapPullback`: the square of
  topoi of Stacks 0EZ2 for restriction along a morphism, as a strict identity of functors.
* `Stacks.ComparingTopologies.isZero_rightDerived_of_isZero_globalSections`: the vanishing of a
  higher change-of-topology direct image, from the vanishing of global sections alone.

## References

* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EZ9](https://stacks.math.columbia.edu/tag/0EZ9)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

/-- An exact additive functor `G` has no higher right derived functors: `(R^n G)(M) = 0` for
`n > 0`. -/
theorem isZero_rightDerived_obj_of_preservesHomology {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasInjectiveResolutions A] (G : A ⥤ B) [G.Additive]
    [G.PreservesHomology] (M : A) (n : ℕ) (hn : 0 < n) :
    IsZero ((G.rightDerived n).obj M) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h0 : IsZero (G.obj ((injectiveResolution M).cocomplex.homology (m + 1))) :=
    G.map_isZero (RightDerivedCoEdge.isZero_homology_succ (injectiveResolution M) m)
  exact (h0.of_iso (ShortComplex.mapHomologyIso
      ((injectiveResolution M).cocomplex.sc (m + 1)) G)).of_iso
    ((injectiveResolution M).isoRightDerivedObj G (m + 1))

end Stacks.Cohomology

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- The square of topoi of Stacks 0EZ2 for restriction along a morphism of the site:
change-of-topology direct image followed by restriction along `u : V ⟶ X` is restriction along
`u` followed by change-of-topology direct image, as one and the same functor. -/
theorem abelianComparisonPushforward_comp_overMapPullback (S : CohomologyComparison C)
    {V X : C} (u : V ⟶ X) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} u =
      S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} u ⋙
        abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine V :=
  rfl

/-- Restriction commutes with the higher change-of-topology direct images: for `u : V ⟶ X` a
morphism of the site and `ℱ` an abelian sheaf on the finer site localized at `X`,

`(R^i ε_{X,*} ℱ)|_V ≅ R^i ε_{V,*} (ℱ|_V)`. -/
def restrictionRightDerivedIso (S : CohomologyComparison C) {V X : C} (u : V ⟶ X)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (i : ℕ) :
    (S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} u).obj
        (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).rightDerived i).obj F) ≅
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine V).rightDerived i).obj
        ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} u).obj F) :=
  let Lf := S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} u
  let Lc := S.coarseCoverage.toGrothendieck.overMapPullback Ab.{max u v} u
  let TX := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let TV := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine V
  let I := injectiveResolution F
  let I' : InjectiveResolution (Lf.obj F) :=
    Stacks.RightDerivedComp.mapOfAcyclic Lf I
      (fun n hn ↦ Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology Lf F n hn)
  Lc.mapIso (I.isoRightDerivedObj TX i) ≪≫
    (ShortComplex.mapHomologyIso
      (((TX.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc i) Lc).symm ≪≫
    (I'.isoRightDerivedObj TV i).symm

/-- If, for every object `V` of the site and every abelian sheaf `𝒢` of `𝒜_V` on the
finer localized site over `V`, the global sections of `R^i ε_{V,*} 𝒢` vanish, then `R^i ε_{X,*} ℱ`
vanishes outright, for every `X` and every `ℱ` of `𝒜_X`. -/
theorem isZero_rightDerived_of_isZero_globalSections (S : CohomologyComparison C) (i : ℕ)
    (h : ∀ (V : C) (G : Sheaf (S.fineCoverage.toGrothendieck.over V) Ab.{max u v}),
      S.fineWeakSerre V G →
        IsZero ((globalSectionsOver S.coarseCoverage.toGrothendieck V).obj
          (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
            S.coarse_le_fine V).rightDerived i).obj G)))
    (X : C) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    IsZero (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerived i).obj F) := by
  refine Stacks.Cohomology.Locality.isZero_of_forall_isZero_sections _ _ fun U ↦ ?_
  induction U with
  | op U =>
    have hmk : (Over.mk (𝟙 U.left ≫ U.hom) : Over X) ≅ U :=
      Over.isoMk (Iso.refl U.left) (by simp)
    have hres := h U.left
      ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} U.hom).obj F)
      (CohomologyComparison.fineWeakSerre_overMapPullback S U.hom F hF)
    refine (hres.of_iso ?_).of_iso
      ((((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerived i).obj F).obj.mapIso (Iso.op hmk))
    exact ((sheafSections (S.coarseCoverage.toGrothendieck.over U.left) Ab.{max u v}).obj
        (op (Over.mk (𝟙 U.left)))).mapIso (restrictionRightDerivedIso S U.hom F i)

end Stacks.ComparingTopologies

end
