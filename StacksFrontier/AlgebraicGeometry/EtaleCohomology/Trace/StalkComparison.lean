module

public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Comparing the two small étale sites at a geometric point

The library carries two small étale sites: the bounded one `SmallEtale B S hS` indexed by a big
étale site, and Mathlib's `S.Etale`. They are compared by `SmallEtale.toEtaleSite`, which is a
dense subsite inclusion. This file shows that the inclusion is representably flat and compares
the stalks of the two sites at a geometric point.

## Main results

* `AlgebraicGeometry.representablyFlat_toEtaleSite`: the inclusion of the bounded small étale site
  into Mathlib's is representably flat.
* `AlgebraicGeometry.toEtaleSiteFiberIso`: the fibre of Mathlib's point at a geometric point,
  restricted along the inclusion, is the bounded site's fibre.
* `AlgebraicGeometry.sheafEquivCompSheafFiberIso`: the stalk functor of Mathlib's point, read
  through the identification of the two sheaf categories, is the bounded site's own stalk functor.
* `AlgebraicGeometry.finite_sheafFiber_sheafEquiv`: finiteness of a stalk transports across that
  identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of a big étale site sends the identity of a contained scheme to the identity. -/
public theorem inclusion_map_id_of_contains : B.inclusion.map (𝟙 (B.obj S hS)) = 𝟙 S :=
  B.inclusion.map_id _

/-- The inclusion into Mathlib's small étale site sends the final object of the bounded site to a
terminal object. -/
public def isTerminalToEtaleSiteFinal :
    IsTerminal ((SmallEtale.toEtaleSite B S hS).obj (SmallEtale.final B S hS)) :=
  IsTerminal.ofUniqueHom
    (fun Y ↦ MorphismProperty.Over.homMk Y.hom
      ((congrArg (Y.hom ≫ ·) (inclusion_map_id_of_contains B S hS)).trans (Category.comp_id _))
      (by trivial))
    fun Y f ↦ MorphismProperty.Over.Hom.ext <| (Category.comp_id f.left).symm.trans
      ((congrArg (f.left ≫ ·) (inclusion_map_id_of_contains B S hS)).symm.trans
        (MorphismProperty.Over.w f))

/-- The inclusion into Mathlib's small étale site preserves the terminal object. -/
public theorem preservesTerminal_toEtaleSite :
    PreservesLimit (Functor.empty.{0} (SmallEtale B S hS)) (SmallEtale.toEtaleSite B S hS) :=
  preservesTerminal_of_iso _
    ((SmallEtale.toEtaleSite B S hS).mapIso
        (terminalIsTerminal.uniqueUpToIso (SmallEtale.finalIsTerminal B S hS)) ≪≫
      (isTerminalToEtaleSiteFinal B S hS).uniqueUpToIso terminalIsTerminal)

/-- The inclusion into Mathlib's small étale site preserves pullbacks. -/
public theorem preservesPullbacks_toEtaleSite :
    PreservesLimitsOfShape WalkingCospan (SmallEtale.toEtaleSite B S hS) :=
  have : PreservesLimitsOfShape WalkingCospan
      (SmallEtale.toEtaleSite B S hS ⋙
        Scheme.Etale.forget S ⋙ CategoryTheory.Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (SmallEtale.toScheme B S hS))
  preservesLimitsOfShape_of_reflects_of_preserves (SmallEtale.toEtaleSite B S hS)
    (Scheme.Etale.forget S ⋙ CategoryTheory.Over.forget S)

/-- The inclusion into Mathlib's small étale site preserves finite limits. -/
public theorem preservesFiniteLimits_toEtaleSite :
    PreservesFiniteLimits (SmallEtale.toEtaleSite B S hS) :=
  have := preservesTerminal_toEtaleSite B S hS
  have := preservesPullbacks_toEtaleSite B S hS
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (SmallEtale.toEtaleSite B S hS)
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (SmallEtale.toEtaleSite B S hS)

/-- The inclusion of the bounded small étale site into Mathlib's is representably flat. -/
public theorem representablyFlat_toEtaleSite :
    RepresentablyFlat (SmallEtale.toEtaleSite B S hS) :=
  have := preservesFiniteLimits_toEtaleSite B S hS
  flat_of_preservesFiniteLimits _

variable (s : GeometricPoint S)

/-- The fibre of Mathlib's point at a geometric point, restricted along the inclusion, is the
bounded site's own fibre. -/
public def toEtaleSiteFiberIso :
    SmallEtale.toEtaleSite B S hS ⋙ (Scheme.pointSmallEtale s.hom).fiber ≅
      geometricPointFiber B S hS s :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun f := ⟨f.left, Over.w f⟩
      invFun p := Over.homMk p.1 p.2
      left_inv _ := Over.OverMorphism.ext rfl
      right_inv _ := rfl })
    (by intro U V g; ext f; apply Subtype.ext; rfl)

/-! ### The stalk functors of the two sites agree -/

section Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] (s : GeometricPoint X.obj)

/-- The stalk functor of Mathlib's point of the small étale site at a geometric point, read
through the identification of the two sheaf categories, is the bounded site's own module-valued
stalk functor at that point. -/
public def sheafEquivCompSheafFiberIso :
    (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor ⋙
        (Scheme.pointSmallEtale s.hom).sheafFiber ≅
      etaleModuleStalkFunctor B X Λ s :=
  sheafFiberIsoOfAdjOfFiberIso (geometricSitePoint B X s)
    (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B X.obj X.property)
    (toEtaleSiteFiberIso B X.obj X.property s)
    (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).toAdjunction

/-- Finiteness of the stalk transports across the identification of the two small étale sites. -/
public theorem finite_sheafFiber_sheafEquiv
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F)) :
    Module.Finite Λ (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{w} Λ)).obj
      ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F)) :=
  Module.Finite.equiv ((sheafEquivCompSheafFiberIso B X Λ s).app F).symm.toLinearEquiv

end Modules

end AlgebraicGeometry

end
