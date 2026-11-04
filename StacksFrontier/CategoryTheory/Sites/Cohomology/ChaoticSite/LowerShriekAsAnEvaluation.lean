module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek to a point on a chaotic site with an initial object

Let `C` be a category whose opposite has a terminal object `T`, equivalently a category with an
initial object, and give `C` the chaotic topology. For the unique functor `p : C ⥤ *` the inverse
image `π^{-1}` of the induced morphism of topoi is restriction along `p`, that is, the constant
presheaf; its left adjoint `π_!` is the colimit over `Cᵒᵖ`, and a colimit over an index category
with a terminal object is the value there. So on such a site

* `π_!` is *evaluation at `T`*, transported to the point, and
* `π_!` therefore preserves finite limits as well as all colimits, i.e. it is exact.

Neither statement needs colimits in the coefficient category to exist, so this file assumes none;
that is the one way in which it is not a corollary of the colimit formula of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/LowerShriekAsAColimit.lean`.

## Main definitions

* `Stacks.ChaoticSite.pointSections`: the sections at the point, an equivalence from sheaves on
  the one-object chaotic site to the coefficient category.
* `Stacks.ChaoticSite.evaluationLowerShriek`: evaluation at `T`, read as a functor to sheaves on
  the point.
* `CategoryTheory.evaluationObjConstAdjunction`: evaluation at a terminal object of the index
  category is left adjoint to the constant functor.

## Main results

* `Stacks.ChaoticSite.evaluationLowerShriekAdjunction`: evaluation at `T` is left adjoint to
  restriction along the point functor, so it *is* a lower shriek.
* `Stacks.ChaoticSite.lowerShriekEvaluationIso`: the established inverse image
  `Functor.sheafPullback` along the point is canonically evaluation at `T`.
* `Stacks.ChaoticSite.lowerShriek_pointSections_evaluationIso`: the sections at the point of
  `π_!F` are the sections of `F` at `T`, naturally in `F`.
* `Stacks.ChaoticSite.lowerShriek_preservesFiniteLimits` and
  `Stacks.ChaoticSite.lowerShriek_preservesColimitsOfShape`: `π_!` is exact.

## Implementation notes

The topology on `C` is left as a parameter `J` rather than fixed to be the chaotic one: the only
thing used of it is that the point functor is continuous for it, and the two spellings of the
chaotic topology that occur in practice — `GrothendieckTopology.trivial` and the topology
inherited from the chaotic point of Stacks 08P8 — are equal but not syntactically identical. A
statement about `J` applies to both. The topology on the one-object category *is* fixed to be
`GrothendieckTopology.trivial`, because that is the one the point morphism of Stacks 08PF is
formed over.

The adjunction is assembled exactly as the colimit formula's is, with evaluation at `T` in place
of `colim`: the presheaf-level adjunction composes `evaluationObjConstAdjunction` with the
equivalence `Stacks.ChaoticSite.pointConstAdjunction`, and `Adjunction.restrictFullyFaithful`
restricts it along `sheafToPresheaf`, both comparison isomorphisms being `Iso.refl`.

Exactness of `π_!` is read off after composing with `pointSections`, which is an equivalence and
so reflects finite limits; that composite is `sheafToPresheaf` followed by evaluation, and both
of those preserve limits. Preservation of colimits is formal, `π_!` being a left adjoint.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₂ u₂ v u

/-- Evaluation at a terminal object of the index category is left adjoint to the constant
functor: a cocone on a diagram indexed by a category with a terminal object is the same thing as
a map out of its value there. -/
@[sga "3 IV 4.3.17", sga "4 Vbis 1.2.11" "special case"]
def evaluationObjConstAdjunction {J : Type u} [Category.{v} J] (A : Type u₂) [Category.{v₂} A]
    {t : J} (ht : IsTerminal t) :
    (evaluation J A).obj t ⊣ Functor.const J where
  unit :=
    { app := fun F =>
        { app := fun j => F.map (ht.from j)
          naturality := by
            intro j k f
            dsimp
            rw [Category.comp_id, ← F.map_comp]
            exact congrArg F.map (ht.hom_ext _ _) } }
  counit := { app := fun _ => 𝟙 _ }
  left_triangle_components F := by
    dsimp
    rw [ht.hom_ext (ht.from t) (𝟙 t), F.map_id, Category.comp_id]
  right_triangle_components X := by ext j; simp

end CategoryTheory

namespace Stacks.ChaoticSite

universe v₂ u₂ v u

section Trivial

variable (D : Type u) [Category.{v} D] (A : Type u₂) [Category.{v₂} A]

/-- For the chaotic topology, the inclusion of sheaves into presheaves is an equivalence: every
presheaf is a sheaf. -/
@[sga "3 IV 4.4.2" "more general", sga "4 IV 6.8.6" "more general"]
instance sheafToPresheafTrivial_isEquivalence :
    (sheafToPresheaf (GrothendieckTopology.trivial D) A).IsEquivalence := by
  rw [GrothendieckTopology.trivial_eq_bot, ← sheafBotEquivalence_functor]
  infer_instance

/-- For the chaotic topology, the unit of sheafification is an isomorphism at every presheaf. -/
instance isIso_toSheafify_trivial (P : Dᵒᵖ ⥤ A) :
    IsIso (toSheafify (GrothendieckTopology.trivial D) P) := by
  refine isIso_toSheafify _ ?_
  rw [GrothendieckTopology.trivial_eq_bot]
  exact Presheaf.isSheaf_bot P

/-- For the chaotic topology, the unit of the sheafification adjunction is an isomorphism. -/
instance isIso_sheafificationAdjunction_unit_trivial :
    IsIso (sheafificationAdjunction (GrothendieckTopology.trivial D) A).unit :=
  NatIso.isIso_of_isIso_app _

/-- For the chaotic topology, sheafification followed by the inclusion of sheaves into presheaves
is the identity. -/
def trivialSheafificationUnitIso :
    𝟭 (Dᵒᵖ ⥤ A) ≅ presheafToSheaf (GrothendieckTopology.trivial D) A ⋙
      sheafToPresheaf (GrothendieckTopology.trivial D) A :=
  asIso (sheafificationAdjunction (GrothendieckTopology.trivial D) A).unit

end Trivial

section Point

variable (A : Type u₂) [Category.{v₂} A] (C : Type u) [Category.{v} C]

/-- The unique object of the opposite of the one-object category. -/
abbrev pointObj : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨⟨⟩⟩

/-- The sections at the point of a sheaf on the one-object chaotic site. This is an equivalence
onto the coefficient category. -/
abbrev pointSections :
    Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A ⥤ A :=
  sheafToPresheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A ⋙
    (evaluation (Discrete PUnit.{u + 1})ᵒᵖ A).obj pointObj.{u}

/-- Evaluation at the unique object of the opposite of the one-object category is an equivalence
from presheaves on it to the coefficient category. -/
instance evaluationPoint_isEquivalence :
    ((evaluation (Discrete PUnit.{u + 1})ᵒᵖ A).obj pointObj.{u}).IsEquivalence :=
  inferInstanceAs (pointConstEquiv.{u} A).inverse.IsEquivalence

/-- The constant presheaf on the one-object site, sheafified, is inverse to taking sections at
the point. -/
def constPresheafToSheafPointSectionsIso :
    (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ ⋙
        presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A) ⋙
      pointSections.{v₂, u₂, u} A ≅ 𝟭 A :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Functor.const (Discrete PUnit.{u + 1})ᵒᵖ)
        (trivialSheafificationUnitIso (Discrete PUnit.{u + 1}) A).symm)
      ((evaluation (Discrete PUnit.{u + 1})ᵒᵖ A).obj pointObj.{u}) ≪≫
    Functor.constCompEvaluationObj A pointObj.{u}

variable {C} {T : Cᵒᵖ}

/-- Restriction along the point functor is right adjoint to evaluation at a terminal object of
`Cᵒᵖ`, read as a presheaf on the point. -/
@[sga "4 Vbis 1.2.11" "special case"]
def presheafEvaluationStarAdjunction (hT : IsTerminal T) :
    ((evaluation Cᵒᵖ A).obj T ⋙ Functor.const (Discrete PUnit.{u + 1})ᵒᵖ) ⊣
      (Functor.whiskeringLeft Cᵒᵖ ((Discrete PUnit.{u + 1})ᵒᵖ) A).obj (Functor.star C).op :=
  Adjunction.ofNatIsoRight
    ((evaluationObjConstAdjunction A hT).comp (pointConstAdjunction.{u} A))
    (starWhiskerIso A C)

variable (T) (J : GrothendieckTopology C)
  [(Functor.star C).IsContinuous J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))]

/-- Evaluation at an object `T` of `Cᵒᵖ`, read as a functor to sheaves on the point. For `T`
terminal this is lower shriek along the point morphism. -/
def evaluationLowerShriek :
    Sheaf J A ⥤ Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A :=
  sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T ⋙
    Functor.const (Discrete PUnit.{u + 1})ᵒᵖ ⋙
      presheafToSheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) A

variable {T}

/-- Evaluation at a terminal object of `Cᵒᵖ` is left adjoint to restriction along the point
functor: it is a lower shriek. -/
def evaluationLowerShriekAdjunction (hT : IsTerminal T) :
    evaluationLowerShriek A T J ⊣
      (Functor.star C).sheafPushforwardContinuous A J
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
  ((presheafEvaluationStarAdjunction A hT).comp
      (sheafificationAdjunction (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
        A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Restriction along the point functor has a left adjoint as soon as `Cᵒᵖ` has a terminal
object; no colimits in the coefficient category are needed. -/
theorem pointRestriction_isRightAdjoint (hT : IsTerminal T) :
    ((Functor.star C).sheafPushforwardContinuous A J
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint :=
  (evaluationLowerShriekAdjunction A J hT).isRightAdjoint

variable [((Functor.star C).sheafPushforwardContinuous A J
  (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).IsRightAdjoint]

/-- The established inverse image along the point, the left adjoint of restriction, is
canonically evaluation at a terminal object of `Cᵒᵖ`. -/
def lowerShriekEvaluationIso (hT : IsTerminal T) :
    (Functor.star C).sheafPullback A J
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ≅
      evaluationLowerShriek A T J :=
  Adjunction.leftAdjointUniq
    ((Functor.star C).sheafAdjunctionContinuous A J
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (evaluationLowerShriekAdjunction A J hT)

/-- The sections at the point of the evaluation presentation are the sections at `T`. -/
def evaluationLowerShriek_pointSectionsIso :
    evaluationLowerShriek A T J ⋙ pointSections.{v₂, u₂, u} A ≅
      sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T)
      (constPresheafToSheafPointSectionsIso.{v₂, u₂, u} A) ≪≫
    Functor.rightUnitor _

/-- The sections at the point of `π_!F` are the sections of `F` at the terminal object `T` of
`Cᵒᵖ`, naturally in `F`. For the site of Stacks 08PR and `T` the identity augmentation this is
the formula `π_!F = F(B → B)` of Stacks 08QG. -/
def lowerShriek_pointSections_evaluationIso (hT : IsTerminal T) :
    (Functor.star C).sheafPullback A J
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ⋙
        pointSections.{v₂, u₂, u} A ≅
      sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T :=
  Functor.isoWhiskerRight (lowerShriekEvaluationIso A J hT) (pointSections.{v₂, u₂, u} A) ≪≫
    evaluationLowerShriek_pointSectionsIso A J

/-- Lower shriek along the point morphism preserves finite limits, as soon as `Cᵒᵖ` has a
terminal object. -/
theorem lowerShriek_preservesFiniteLimits [HasFiniteLimits A] (hT : IsTerminal T) :
    PreservesFiniteLimits
      ((Functor.star C).sheafPullback A J
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) := by
  have : PreservesFiniteLimits
      ((Functor.star C).sheafPullback A J
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) ⋙
        pointSections.{v₂, u₂, u} A) :=
    preservesFiniteLimits_of_natIso (lowerShriek_pointSections_evaluationIso A J hT).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (pointSections.{v₂, u₂, u} A)

/-- Lower shriek along the point morphism preserves all colimits, being a left adjoint. Together
with `Stacks.ChaoticSite.lowerShriek_preservesFiniteLimits` this is exactness of `π_!`. -/
instance lowerShriek_preservesColimitsOfShape {K : Type*} [Category* K] :
    PreservesColimitsOfShape K
      ((Functor.star C).sheafPullback A J
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))) :=
  ((Functor.star C).sheafAdjunctionContinuous A J
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape

end Point

end Stacks.ChaoticSite

end
