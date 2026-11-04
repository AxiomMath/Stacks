module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# ExtensionByZeroUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (A : Type u') [Category.{v'} A]

variable [HasLimitsOfSize.{u, u} A]
  {LM : Sheaf U.obj.left.1.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A}
  {LB : Sheaf (topology B U.obj.left.1 U.obj.left.property) A ⥤ Sheaf (topology B X hX) A}
  (adjM : LM ⊣ (@Scheme.Etale.smallEtaleCompose U.obj.left.1 X (B.inclusion.map U.obj.hom)
        U.property).sheafPushforwardContinuous A
        U.obj.left.1.smallEtaleTopology X.smallEtaleTopology)
  (adjB : LB ⊣ (smallEtalePostcompose B X hX U).sheafPushforwardContinuous A
        (topology B U.obj.left.1 U.obj.left.property) (topology B X hX))

/-- **Extension by zero commutes with the equivalence of the two models of the small étale
site.** For `U` in the small étale site of Tag 021B of `X`, with structure morphism `j`, let
`LM` be a left adjoint of restriction along `j` on Mathlib's small étale site and `LB` one on the
site of Tag 021B — extension by zero `j_!` in the two models. Then transporting a sheaf from the
site of Tag 021B to Mathlib's site and extending by zero there is the same as extending by zero
on the site of Tag 021B and then transporting. Both composites are left adjoint to the same
functor, by `AlgebraicGeometry.SmallEtale.toEtaleSiteRestrictionIso`. -/
public def sheafEquivExtensionByZeroIsoUnconditional :
    (sheafEquiv B U.obj.left.1 U.obj.left.property A).functor ⋙ LM ≅
      LB ⋙ (sheafEquiv B X hX A).functor :=
  Adjunction.leftAdjointUniq
    (((sheafEquiv B U.obj.left.1 U.obj.left.property A).toAdjunction.comp adjM).ofNatIsoRight
      (toEtaleSiteRestrictionIso B X hX U A))
    (adjB.comp (sheafEquiv B X hX A).toAdjunction)

end AlgebraicGeometry.SmallEtale

end
