module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.GeometricStalkGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.GeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse

/-!
# The stalks at the geometric points over the points of a scheme detect the zero sheaf of modules

For a sheaf `G` of `Λ`-modules on Mathlib's small étale site of a scheme `X`, if the stalk of `G`
at the geometric point `AlgebraicGeometry.GeometricPoint.ofPoint X x` over every point `x` of `X`
vanishes, then `G` vanishes: those geometric points cover `X`, so their stalk functors form a
conservative family ([Stacks, Tag 03PU]).

## Main results

* `Stacks.EtaleCohomology.etaleModuleStalkIsoUliftSheafFiber` — the stalk functor of the point
  `pointSmallEtale` agrees with that of its universe lift, on sheaves of modules.
* `Stacks.EtaleCohomology.isZero_of_forall_isZero_etaleModuleStalk_ofPoint` — a sheaf of
  `Λ`-modules whose stalks at the geometric points over all points of `X` vanish is zero.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZeroObject

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ]

/-- The stalk functor of the point `pointSmallEtale` of a geometric point and that of its universe
lift agree on sheaves of `Λ`-modules: both are global sections of the inverse image
([Stacks, Tag 04JN]). -/
def etaleModuleStalkIsoUliftSheafFiber {X : Scheme.{u}} (s : GeometricPoint X) :
    (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) ≅
      ((Scheme.pointSmallEtale s.hom).ulift.{max (u + 1) r}).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) :=
  etaleModuleStalkIsoInverseImageGlobalSections.{u, r} Λ s ≪≫
    etaleModuleInverseImageGlobalSectionsIsoSheafFiber.{u, r} Λ s.residueField s.hom

/-- **The stalks at the geometric points over the points of a scheme detect the zero sheaf.** -/
theorem isZero_of_forall_isZero_etaleModuleStalk_ofPoint {X : Scheme.{u}}
    (G : EtaleModules.{u, r} Λ X)
    (h : ∀ x : X, IsZero (((Scheme.pointSmallEtale (GeometricPoint.ofPoint X x).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj G)) :
    IsZero G := by
  have hP : (ObjectProperty.ofObj (fun x : X ↦ (Scheme.pointSmallEtale
      (GeometricPoint.ofPoint X x).hom).ulift.{max (u + 1) r})).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift _ (Set.eq_univ_of_forall fun x ↦
      Set.mem_iUnion.2 ⟨x, default, GeometricPoint.ofPoint_liesOver X x⟩)
  let : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r,
      max (u + 1) r, max (u + 1) r} Λ
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})
      (forget AddCommGrpCat.{max (u + 1) r})
  have hiso : IsIso (0 : G ⟶ 0) := by
    refine ((hP.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)).isIso_iff _).2 ?_
    rintro ⟨_, ⟨x⟩⟩
    exact isIso_of_source_target_iso_zero _
      ((h x).of_iso ((etaleModuleStalkIsoUliftSheafFiber Λ _).app G).symm).isoZero
      ((Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

end Stacks.EtaleCohomology

end
