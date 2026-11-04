module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkFrameworkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Torsion of an abelian sheaf on the small étale site is detected on stalks

An abelian sheaf on the small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology` of a
scheme `X` whose stalks at all geometric points are torsion groups is a torsion abelian sheaf.

This is the stalk criterion
`AlgebraicGeometry.SmallEtale.torsionSheafProperty_of_forall_etaleStalk`, proved there for the
size-bounded small étale site of a big étale site, transported to the small étale site of `X`.
The two sites have the same sheaves (`AlgebraicGeometry.SmallEtale.sheafEquiv`), torsion of a sheaf
on the larger site may be checked after restriction to the dense subsite
(`Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward`), and the stalks at a geometric
point agree across that identification
(`AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso`).

## Main results

* `AlgebraicGeometry.torsionSheafProperty_of_forall_smallEtaleStalkAb` — the stalk criterion for
  torsion on the small étale site.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Torsion Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Torsion of an abelian sheaf on the small étale site is detected on stalks.** An abelian
sheaf on the small étale site of `X` whose stalks at all geometric points are torsion groups is a
torsion abelian sheaf.

This is `AlgebraicGeometry.SmallEtale.torsionSheafProperty_of_forall_etaleStalk` for the
restriction of the sheaf to the size-bounded small étale site of a big étale site containing `X`,
the two stalks agreeing by `AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso` (through the
counit of `AlgebraicGeometry.SmallEtale.sheafEquiv`), and torsion being
checked on that dense subsite by `Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward`. -/
theorem torsionSheafProperty_of_forall_smallEtaleStalkAb
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (t : GeometricPoint X) (g : ↑((smallEtaleStalkAb t.hom).obj F)),
      ∃ n : ℕ, 0 < n ∧ n • g = 0) :
    torsionSheafProperty X.smallEtaleTopology F := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  refine torsionSheafProperty_of_pushforward (SmallEtale.topology B X hX) X.smallEtaleTopology
    (SmallEtale.toEtaleSite B X hX) F ?_
  refine SmallEtale.torsionSheafProperty_of_forall_etaleStalk.{u, 0} B X hX _ fun t g => ?_
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let e : (smallEtaleStalkAb t.hom).obj F ≅
      etaleStalk B X hX t ((sheafToPresheaf _ _).obj (E.inverse.obj F)) :=
    (smallEtaleStalkAb t.hom).mapIso (E.counitIso.app F).symm ≪≫
      smallEtaleStalkAb_sheafEquiv_obj_iso B ⟨X, hX⟩ t (E.inverse.obj F)
  exact exists_nsmul_eq_zero_of_iso e (hF t) g

end AlgebraicGeometry

end
