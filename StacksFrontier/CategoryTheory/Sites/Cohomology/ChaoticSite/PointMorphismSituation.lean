module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The projection of a chaotic site to its ringed point, as a morphism of fibred categories

Let `C` be a category with its chaotic topology and `B` a ring on the one-object site `*`, the
data of `Stacks.ChaoticSite.RingedPointSituation`. The projection `π : (Sh(C), B) ⟶ (Sh(*), B)`
is produced by Stacks 08P8 from a *fibred category* over the ringed point. The forgetful
comparisons of Stacks 08PC, and with them the clause of Stacks 08PF that lower shriek on modules
agrees with lower shriek on abelian sheaves, are instead stated for a *1-morphism of fibred
categories*, the standing data of Stacks 08PA. This file presents `π` in that form: the unique
functor `C ⥤ *` is a 1-morphism from `C ⥤ *` to `* ⥤ *` over the ringed point, both structure
functors being the unique functor to the one-object category.

With that presentation the two inherited topologies are the chaotic ones, abelian groups can be
sheafified for both, and the abelian half of Stacks 08PC — the lower-shriek functor and its
adjunction — becomes available at the ringed point.

## Main definitions

* `Stacks.ChaoticSite.RingedPointSituation.pointMorphismSituation`: the ringed-point projection
  as the standing data of Stacks 08PA.
* `Stacks.ChaoticSite.RingedPointSituation.pointAbelianLowerShriek` and
  `pointAbelianInverseImage`: `π_!^{Ab}` and `π^{-1}` on abelian sheaves, in that presentation.

## Main results

* `Stacks.ChaoticSite.star_isFibredOneMorphism`: the unique functor to the one-object category
  is a 1-morphism of fibred categories over that category.
* `Stacks.ChaoticSite.RingedPointSituation.pointMorphismSituation_sourceTopology` and
  `pointMorphismSituation_totalTopology`: both inherited topologies are chaotic.

## Implementation notes

The target of the 1-morphism is the one-object category with the *unique functor to itself* as
its structure functor, not the identity functor: the two are equal, but taking the unique functor
makes `Stacks.ChaoticSite.pointFunctor_isFibered` apply on the nose and makes the inherited
topology on the target literally the inherited topology of a `RingedPointSituation`, so that
`Stacks.ChaoticSite.RingedPointSituation.topology_eq_trivial` computes it with no rewriting.

What this file does **not** contain is the clause of Stacks 08PF it is the setup for. That clause
compares lower shriek on sheaves of *modules* with lower shriek on abelian sheaves, and its
statement needs the module half of Stacks 08PC — a lower-shriek left adjoint for
`Stacks.Sites.FibredCategory.MorphismSituation.moduleInverseImage` — which is absent from this
tree, for the reason recorded in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ModuleInverseImage.lean`: the
inverse image of sheaves of modules along the induced morphism of topoi has not been identified
with restriction of sheaves of modules along the 1-morphism. Nothing here is tagged 08PF for
that reason.

The sheafification hypothesis of Stacks 08PC is discharged from the chaotic topology, where every
presheaf is a sheaf. Exactness of `π^{-1}` additionally asks that the maps inverted by
sheafification be the locally bijective ones, which on the chaotic topology is
`Stacks.SheafOfModules.botWEqualsLocallyBijective`; that lemma lives in a module this one does
not import, and exactness is one rewrite along the two topology computations below away from it.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ChaoticSite

universe w v u

/-- The unique functor to the one-object category is a 1-morphism of fibred categories over that
category: its image of any morphism is an identity, hence strongly cartesian. -/
theorem star_isFibredOneMorphism (C : Type u) [Category.{v} C] :
    (Functor.star C : C ⥤ Discrete PUnit.{u + 1}).IsFibredOneMorphism
      (Functor.star (Discrete PUnit.{u + 1}) : Discrete PUnit.{u + 1} ⥤ Discrete PUnit.{u + 1})
      (Functor.star C : C ⥤ Discrete PUnit.{u + 1}) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have : (Functor.star C : C ⥤ Discrete PUnit.{u + 1}).IsHomLift f φ := h.toIsHomLift
    have : (Functor.star (Discrete PUnit.{u + 1}) :
        Discrete PUnit.{u + 1} ⥤ Discrete PUnit.{u + 1}).IsHomLift f
          ((Functor.star C : C ⥤ Discrete PUnit.{u + 1}).map φ) :=
      CategoryTheory.Functor.isHomLift_map_of_comp_eq
        (p := (Functor.star C : C ⥤ Discrete PUnit.{u + 1}))
        (q := (Functor.star (Discrete PUnit.{u + 1}) :
          Discrete PUnit.{u + 1} ⥤ Discrete PUnit.{u + 1}))
        (G := (Functor.star C : C ⥤ Discrete PUnit.{u + 1})) rfl f φ
    have : IsIso ((Functor.star C : C ⥤ Discrete PUnit.{u + 1}).map φ) := by
      change IsIso (𝟙 _)
      infer_instance
    exact Functor.IsStronglyCartesian.of_isIso _ f _

namespace RingedPointSituation

variable (s : RingedPointSituation.{w, v, u})

/-- The one-object category with the same ring on it, as a situation in its own right. Its
inherited topology is the one the target of the 1-morphism below carries. -/
def toPointSituation : RingedPointSituation.{max w v, u, u} where
  C := Discrete PUnit.{u + 1}
  B := s.B

/-- The projection of the chaotic site to its ringed point, presented as the standing data of
Stacks 08PA: a 1-morphism of fibred categories over the ringed point, from `C` to the one-object
category. -/
def pointMorphismSituation :
    Stacks.Sites.FibredCategory.MorphismSituation.{u, u, u, u, u, v, max w u v} where
  base :=
    { C := Discrete PUnit.{u + 1}
      J := GrothendieckTopology.trivial (Discrete PUnit.{u + 1})
      O := s.pointRingSheaf }
  total := Discrete PUnit.{u + 1}
  source := s.C
  p := Functor.star (Discrete PUnit.{u + 1})
  p' := Functor.star s.C
  u := Functor.star s.C
  isFibredOneMorphism := star_isFibredOneMorphism s.C

/-- The topology the source of the 1-morphism inherits is the chaotic topology on `C`; it is the
topology of the given ringed-point situation. -/
theorem pointMorphismSituation_sourceTopology :
    (pointMorphismSituation s).sourceTopology = GrothendieckTopology.trivial s.C :=
  s.topology_eq_trivial

/-- The topology the target of the 1-morphism inherits is the chaotic topology on the one-object
category. -/
theorem pointMorphismSituation_totalTopology :
    (pointMorphismSituation s).totalTopology =
      GrothendieckTopology.trivial (Discrete PUnit.{u + 1}) :=
  s.toPointSituation.topology_eq_trivial

/-- Abelian presheaves on the source of `pointMorphismSituation s` can be sheafified. -/
instance hasSheafifySource :
    HasSheafify (pointMorphismSituation s).sourceTopology AddCommGrpCat.{max w u v} := by
  rw [pointMorphismSituation_sourceTopology, GrothendieckTopology.trivial_eq_bot]
  exact instHasSheafifyBotGrothendieckTopology _

/-- Abelian presheaves on the target of `pointMorphismSituation s` can be sheafified. -/
instance hasSheafifyTotal :
    HasSheafify (pointMorphismSituation s).totalTopology AddCommGrpCat.{max w u v} := by
  rw [pointMorphismSituation_totalTopology, GrothendieckTopology.trivial_eq_bot]
  exact instHasSheafifyBotGrothendieckTopology _

/-- `π^{-1}` on abelian sheaves: restriction along the unique functor `C ⥤ *`. -/
abbrev pointAbelianInverseImage :=
  (pointMorphismSituation s).abelianInverseImage.{u, u, u, u, u, v, w}

/-- `π_!^{Ab}`, the lower-shriek functor on abelian sheaves for the ringed-point projection. -/
abbrev pointAbelianLowerShriek :=
  (pointMorphismSituation s).abelianLowerShriek.{u, u, u, u, u, v, w}

/-- The adjunction `π_!^{Ab} ⊣ π^{-1}` of Stacks 08PC at the ringed point. -/
abbrev pointAbelianLowerShriekAdjunction :=
  (pointMorphismSituation s).abelianLowerShriekAdjunction.{u, u, u, u, u, v, w}

end RingedPointSituation

end Stacks.ChaoticSite

end
