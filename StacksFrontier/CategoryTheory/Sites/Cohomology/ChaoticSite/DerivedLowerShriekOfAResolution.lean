module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.CategoryTheory.Abelian.LeftDerivedTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAnEvaluation

/-!
# Derived lower shriek computed by a cosimplicial resolution

Let `C` be a small category with the chaotic topology and let `π : Sh(C) ⟶ Sh(*)` be the point
morphism, so that `π_!` is the inverse image along the point, the left adjoint of restriction.
Let `U_•` be a cosimplicial object of `C` such that every simplicial set `Mor_C(U_•, W)` is
homotopy equivalent to a singleton. Then

`L_nπ_!(ℱ) = H_n(ℱ(U_•))`,

the homology of the Moore complex of the simplicial abelian group `ℱ(U_•)`, naturally in the
abelian sheaf `ℱ`.

The criterion of Tag 08Q9 (`Stacks.ChaoticSite.leftDerivedColimitNatIso`) is the same statement
for the left derived functors of `colim` over the index category of *presheaves*; Tag 08PF says
that `π_!` is that colimit, undierived. This file supplies the passage between the two derived
functors: `π_!` followed by the sections at the point is the colimit of the underlying presheaf,
and a left derived functor is transported along an isomorphism of the functor and along an
equivalence of its source or of its target.

## Main definitions

* `Stacks.ChaoticSite.colimitLowerShriek`: the colimit over `Cᵒᵖ`, read as a sheaf on the point,
  at an arbitrary coefficient category.
* `Stacks.ChaoticSite.abelianPointLowerShriek`: `π_!` on abelian sheaves for the chaotic topology
  on a small category, with coefficients in the same universe as the site.

## Main results

* `Stacks.ChaoticSite.colimitLowerShriekAdjunction` and
  `Stacks.ChaoticSite.lowerShriekColimitIso`: **Tag 08PF** at an arbitrary coefficient category —
  the colimit presentation is left adjoint to restriction along the point functor, hence is
  canonically the established inverse image.
* `Stacks.ChaoticSite.lowerShriek_pointSections_colimitIso`: the sections at the point of `π_!ℱ`
  are the colimit of the underlying presheaf of `ℱ`, naturally in `ℱ`.
* `Stacks.ChaoticSite.trivialSheafEnoughProjectives`: abelian sheaves for the chaotic topology
  have enough projectives.
* `Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso`: **the conclusion of Tag 08Q9 for
  `Lπ_!`** — `L_nπ_!(ℱ)`, read at the point, is the degree `n` homology of the Moore complex of
  `ℱ(U_•)`, naturally in `ℱ`.

## Implementation notes

The colimit presentation of lower shriek already in the library,
`Stacks.ChaoticSite.abelianLowerShriekColimitIso`, is stated with coefficients in
`AddCommGrpCat.{max w (u + 1) v}` for a site with objects in `Type u` and morphisms in
`Type v`, a universe which can never be the site's own `u`; the criterion of Tag 08Q9 is stated
for a small site with coefficients in `AddCommGrpCat.{u}`, so the two cannot be composed as they
stand. The declarations of the first section below are therefore the same construction at an
arbitrary coefficient category — the ingredients,
`Stacks.ChaoticSite.presheafColimitStarAdjunction` and the sheafification of the chaotic
topology, are already stated there — assembled exactly as
`Stacks.ChaoticSite.evaluationLowerShriekAdjunction` assembles the evaluation presentation.

`Abelian` and `EnoughProjectives` for sheaves on a chaotic site are not proved again: every
presheaf is a sheaf, so `sheafToPresheaf` is an equivalence
(`Stacks.ChaoticSite.sheafToPresheafTrivial_isEquivalence`), and both properties transport along
it, the second by `CategoryTheory.Equivalence.enoughProjectives`.

The three transports of `CategoryTheory.Functor.leftDerived` are those of
`StacksFrontier/CategoryTheory/Abelian/LeftDerivedTransport.lean`: along an isomorphism of the
functor, along an equivalence of the target (here the sections at the point) and along an
equivalence of the source (here the inclusion of sheaves into presheaves).

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe v₂ u₂ v u

/-! ### The colimit presentation of lower shriek at an arbitrary coefficient category -/

section Colimit

variable (A : Type u₂) [Category.{v₂} A] (C : Type u) [Category.{v} C]
  [HasColimitsOfShape Cᵒᵖ A]

/-- The colimit over `Cᵒᵖ` of the underlying presheaf, read as a sheaf on the point. For the
chaotic topology this is lower shriek along the point morphism. -/
def colimitLowerShriek :
    Sheaf (GrothendieckTopology.trivial C) A ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A :=
  sheafToPresheaf (GrothendieckTopology.trivial C) A ⋙ colim ⋙
    Functor.const (Discrete PUnit.{u + 1})ᵒᵖ ⋙
      presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A

/-- **Tag 08PF.** The colimit over `Cᵒᵖ` is left adjoint to restriction along the point functor:
it is a lower shriek. -/
def colimitLowerShriekAdjunction :
    colimitLowerShriek A C ⊣
      (Functor.star C).sheafPushforwardContinuous A (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  ((presheafColimitStarAdjunction A C).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Restriction along the point functor has a left adjoint as soon as the coefficient category
has colimits of shape `Cᵒᵖ`. -/
instance (priority := 1100) colimitLowerShriek_isRightAdjoint :
    ((Functor.star C).sheafPushforwardContinuous A (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint :=
  (colimitLowerShriekAdjunction A C).isRightAdjoint

/-- **Tag 08PF.** The established inverse image along the point, the left adjoint of
restriction, is canonically the colimit over `Cᵒᵖ`. -/
def lowerShriekColimitIso :
    (Functor.star C).sheafPullback A (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ≅
      colimitLowerShriek A C :=
  Adjunction.leftAdjointUniq
    ((Functor.star C).sheafAdjunctionContinuous A (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (colimitLowerShriekAdjunction A C)

/-- The sections at the point of the colimit presentation are the colimit. -/
def colimitLowerShriek_pointSectionsIso :
    colimitLowerShriek A C ⋙ pointSections.{v₂, u₂, u} A ≅
      sheafToPresheaf (GrothendieckTopology.trivial C) A ⋙ colim :=
  Functor.isoWhiskerLeft (sheafToPresheaf (GrothendieckTopology.trivial C) A ⋙ colim)
      (constPresheafToSheafPointSectionsIso.{v₂, u₂, u} A) ≪≫
    Functor.rightUnitor _

/-- **Tag 08PF.** The sections at the point of `π_!ℱ` are the colimit over `Cᵒᵖ` of the
underlying presheaf of `ℱ`, naturally in `ℱ`. -/
def lowerShriek_pointSections_colimitIso :
    (Functor.star C).sheafPullback A (GrothendieckTopology.trivial C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ⋙
        pointSections.{v₂, u₂, u} A ≅
      sheafToPresheaf (GrothendieckTopology.trivial C) A ⋙ colim :=
  Functor.isoWhiskerRight (lowerShriekColimitIso A C) (pointSections.{v₂, u₂, u} A) ≪≫
    colimitLowerShriek_pointSectionsIso A C

end Colimit

/-! ### Derived lower shriek on a small chaotic site -/

section Derived

variable (C : Type u) [SmallCategory C]

/-- Abelian sheaves for the chaotic topology have enough projectives: they are the abelian
presheaves, which do. -/
instance trivialSheafEnoughProjectives :
    EnoughProjectives (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}) :=
  Equivalence.enoughProjectives
    (sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}).asEquivalence.symm

/-- `π_!` on abelian sheaves for the chaotic topology on a small category, with coefficients in
the universe of the site. -/
abbrev abelianPointLowerShriek :
    Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u} ⥤
      Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u} :=
  (Functor.star C).sheafPullback AddCommGrpCat.{u} (GrothendieckTopology.trivial C)
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))

/-- The colimit presentation of lower shriek is additive, being a composite of additive
functors. -/
instance colimitLowerShriek_additive :
    (colimitLowerShriek AddCommGrpCat.{u} C).Additive :=
  inferInstanceAs ((sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u} ⋙ colim ⋙
    Functor.const (Discrete PUnit.{u + 1})ᵒᵖ ⋙
      presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        AddCommGrpCat.{u}).Additive)

/-- `π_!` is additive: it is the colimit presentation up to isomorphism. -/
instance abelianPointLowerShriek_additive : (abelianPointLowerShriek C).Additive :=
  Functor.additive_of_iso (lowerShriekColimitIso AddCommGrpCat.{u} C).symm

/-- **The conclusion of the criterion of Tag 08Q9 for `Lπ_!`.** Let `U_•` be a cosimplicial
object of a small category `C` such that every simplicial set `Mor_C(U_•, W)` is homotopy
equivalent to a singleton. Then for every abelian sheaf `ℱ` on the chaotic site `C`, the
sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the Moore complex of the
simplicial abelian group `ℱ(U_•)`, naturally in `ℱ`.

This is `Stacks.ChaoticSite.leftDerivedColimitNatIso` — the criterion, stated for the colimit
over the index category of presheaves — transported to `π_!`: the sections at the point of `π_!`
are that colimit by Tag 08PF, and a left derived functor is carried along an isomorphism of the
functor and along the equivalences between sheaves for the chaotic topology and presheaves and
between sheaves on the point and abelian groups. -/
def leftDerivedPointLowerShriekNatIso (U : CosimplicialObject C) (hU : IsPointResolution U)
    (n : ℕ) :
    (abelianPointLowerShriek C).leftDerived n ⋙ pointSections.{u, u + 1, u} AddCommGrpCat.{u} ≅
      sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u} ⋙
        cosimplicialMooreComplex U ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  (Functor.leftDerivedCompIso (abelianPointLowerShriek C)
        (pointSections.{u, u + 1, u} AddCommGrpCat.{u}) n).symm ≪≫
    Functor.leftDerivedIsoOfNatIso
      (lowerShriek_pointSections_colimitIso AddCommGrpCat.{u} C) n ≪≫
    Functor.compLeftDerivedIso
      (sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}) colim n ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u})
      (leftDerivedColimitNatIso U hU n)

end Derived

end Stacks.ChaoticSite

end
