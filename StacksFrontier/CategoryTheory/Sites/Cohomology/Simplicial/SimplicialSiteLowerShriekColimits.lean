module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteLowerShriek

/-!
# `Lπ_!` on the simplicial site commutes with colimits

Let `C` be a site and `π : Δ × C ⥤ C` the projection from the simplicial site of Stacks 09D0.
This file records the first step of the proof of Stacks 09D2: derived lower shriek
`Lπ_! : D(Ab(Δ × C)) ⥤ D(Ab(C))` commutes with colimits, and consequently a morphism of
colimit-preserving functors which `Lπ_!` inverts at every object of a diagram is inverted by
`Lπ_!` at its colimit. The source's "since `Lπ_!` commutes with colimits, it suffices to prove
this for bounded above complexes" is exactly this assertion and the reduction it licenses.

## Main results

* `Stacks.SimplicialModules.preservesColimitsOfSize_derivedAbelianLowerShriek`: `Lπ_!`
  preserves every colimit, being a left adjoint.
* `Stacks.SimplicialModules.isIso_derivedAbelianLowerShriek_map_app_colimit`: the reduction to
  the objects of a diagram.

## These are proof steps, and carry no tag

Stacks 09D2 is a single lemma: its "steps" are steps of its proof, not numbered parts of its
statement, so neither declaration below is tagged.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.FibredCategory

namespace Stacks.SimplicialModules

universe w u w₁ w₂ u₁ v₁

attribute [local instance] HasDerivedCategory.standard

variable (B : AlgebraicGeometry.RingedSite.{u, u, w})
  [((simplicialSituation B).abelianLowerShriekOnHomotopy ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (simplicialSituation B).topology AddCommGrpCat.{max w u}) (ComplexShape.up ℤ))]

/-- **Step 1 of the proof of Stacks 09D2: `Lπ_!` commutes with colimits.** Derived lower shriek
along the projection `π : Δ × C ⥤ C`, on the unbounded derived category of abelian sheaves on
`Δ × C`, preserves every colimit that exists — it is a left adjoint, derived restriction along
`π` being its right adjoint (Stacks 07AC,
`Stacks.Sites.FibredCategory.FibredCategorySituation.derivedAbelianLowerShriekAdjunction`).
Being a step of the proof and not a part of the statement, it carries no tag. -/
theorem preservesColimitsOfSize_derivedAbelianLowerShriek
    (h : (simplicialSituation B).AbelianLowerShriekAcyclic) :
    PreservesColimitsOfSize.{w₁, w₂} (simplicialSituation B).derivedAbelianLowerShriek :=
  ((simplicialSituation B).derivedAbelianLowerShriekAdjunction h).leftAdjoint_preservesColimits

/-- **Step 1 of the proof of Stacks 09D2: the reduction that commuting with colimits licenses.**
Let `α : Φ ⟶ Ψ` be a morphism of functors into the derived category of abelian sheaves on
`Δ × C`, both of which commute with colimits of shape `J`, and let `K : J ⥤ E` be a diagram
with a colimit. If `Lπ_!` inverts `α` at every object of `K`, then it inverts `α` at the colimit
of `K`. Being a step of the proof and not a part of the statement, it carries no tag. -/
theorem isIso_derivedAbelianLowerShriek_map_app_colimit
    (h : (simplicialSituation B).AbelianLowerShriekAcyclic)
    {E : Type u₁} [Category.{v₁} E] {J : Type w₂} [Category.{w₁} J]
    {Φ Ψ : E ⥤ DerivedCategory (Sheaf (simplicialSituation B).topology AddCommGrpCat.{max w u})}
    (α : Φ ⟶ Ψ) (K : J ⥤ E) [HasColimit K]
    [PreservesColimitsOfShape J Φ] [PreservesColimitsOfShape J Ψ]
    (hα : ∀ j, IsIso ((simplicialSituation B).derivedAbelianLowerShriek.map
      (α.app (K.obj j)))) :
    IsIso ((simplicialSituation B).derivedAbelianLowerShriek.map (α.app (colimit K))) := by
  have : PreservesColimitsOfShape J (simplicialSituation B).derivedAbelianLowerShriek :=
    (preservesColimitsOfSize_derivedAbelianLowerShriek B h).preservesColimitsOfShape
  exact NatTrans.isIso_app_colimit
    (Functor.whiskerRight α (simplicialSituation B).derivedAbelianLowerShriek) K hα

end Stacks.SimplicialModules

end
