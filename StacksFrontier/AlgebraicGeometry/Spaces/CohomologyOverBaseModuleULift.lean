module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# Cohomology over the base ring and the universe lift of the module sections

`AlgebraicGeometry.Space.cohomologyOverBase` is the cohomology over `A` of an `𝒪_X`-module on the
small étale ringed site of an algebraic space over `Spec A`, at the module universe
`max (u + 1) w`; `AlgebraicGeometry.Space.cohomologyOverBaseRingUniverse` is the same construction
at the universe `u` of the structure rings, where the direct images of modules live and where
the finiteness theorem of Stacks 08AS is proved.  This file identifies the two along the universe
lift `Stacks.SheafOfModules.moduleULift` of the module sections:

`Hⁱ(X, F↑) ≃ Hⁱ(X, F)` as `A`-modules.

The lift is exact and preserves injective objects
(`Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift`, the small étale site being
essentially small at `u` by Stacks 03ED), and it commutes with global sections, so the right
derived functors of global sections commute with it
(`CategoryTheory.Functor.rightDerivedIsoOfSquare`).

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsModuleULiftIso`: on any site, the global sections
  of the universe lift of a sheaf of modules are the universe lift of its global sections.
* `AlgebraicGeometry.Space.cohomologyOverBaseModuleULiftLinearEquiv`: **the comparison**
  `Hⁱ(X, F↑) ≃ Hⁱ(X, F)` of `A`-modules.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_moduleULift_modules`: the universe lift of
  the `𝒪_X`-modules on an algebraic space preserves injective objects.
* `AlgebraicGeometry.Space.preservesFiniteLimits_moduleULift_modules` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_moduleULift_modules`: and it is exact.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u w t z u₁ v₁ r

namespace Stacks.Cohomology.SiteModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- The global sections of the universe lift of a sheaf of modules, as a linear equivalence with
the universe lift of its global sections: a compatible family of lifted sections is the lift of
the compatible family of the underlying sections. -/
def sectionsModuleULiftLinearEquiv (M : _root_.SheafOfModules.{z} R) :
    ((Stacks.SheafOfModules.moduleULift.{t, z} R).obj M).sections ≃ₗ[RingCat.sectionsSubring R.obj]
      ULift.{t} M.sections where
  toFun s := ULift.up ⟨fun X => (s.1 X).down, fun f => congrArg ULift.down (s.2 f)⟩
  invFun s := ⟨fun X => ULift.up (s.down.1 X), fun f => congrArg ULift.up (s.down.2 f)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Global sections commute with the universe lift of the module sections**, on any site. -/
def globalSectionsModuleULiftIso :
    Stacks.SheafOfModules.moduleULift.{t, z} R ⋙ globalSectionsFunctor.{u₁, v₁, r, max z t} R ≅
      globalSectionsFunctor.{u₁, v₁, r, z} R ⋙
        ModuleCat.uliftFunctor.{t} (RingCat.sectionsSubring R.obj) :=
  NatIso.ofComponents (fun M => (sectionsModuleULiftLinearEquiv.{t} R M).toModuleIso)
    (fun _ => rfl)

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **The universe lift of the `𝒪_X`-modules on an algebraic space preserves injective
objects.**  The small étale site is essentially small at the universe of the schemes
(Stacks 03ED), so this is `Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift`. -/
theorem preservesInjectiveObjects_moduleULift_modules :
    (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).PreservesInjectiveObjects := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B (Spec (.of A)) hA X))
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have := site_hasSheafify_addCommGrp.{u + 1, u, max (u + 1) w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, max (u + 1) w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := moduleSheavesGrothendieck.{u + 1, u, u, max (u + 1) w}
    (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  exact Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift.{max (u + 1) w, u}

/-- The universe lift of the module sections of the `𝒪_X`-modules on an algebraic space is
exact. -/
theorem preservesFiniteLimits_moduleULift_modules :
    PreservesFiniteLimits (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) := by
  let R := ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O
  let G := _root_.SheafOfModules.forget.{max (u + 1) w} R ⋙ PresheafOfModules.toPresheaf R.obj
  have hG : PreservesFiniteLimits (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u} R ⋙ G) := by
    change PreservesFiniteLimits
      ((_root_.SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringRight _ AddCommGrpCat.{u} AddCommGrpCat.{max (u + 1) w}).obj
          AddCommGrpCat.uliftFunctor.{max (u + 1) w, u})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- The universe lift of the module sections of the `𝒪_X`-modules on an algebraic space
preserves finite colimits. -/
theorem preservesFiniteColimits_moduleULift_modules :
    PreservesFiniteColimits (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) := by
  have := site_hasSheafify_addCommGrp.{u + 1, u, max (u + 1) w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, max (u + 1) w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  exact Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{max (u + 1) w, u} _

/-- **Cohomology over the base ring commutes with the universe lift of the module sections**:
for an `𝒪_X`-module `F` with sections in the universe of the structure rings,
`Hⁱ(X, F↑) ≃ Hⁱ(X, F)` as `A`-modules, the left side being
`AlgebraicGeometry.Space.cohomologyOverBase` of the lift and the right side
`AlgebraicGeometry.Space.cohomologyOverBaseRingUniverse`. -/
def cohomologyOverBaseModuleULiftLinearEquiv (M : Modules.{u, u} B (Spec (.of A)) hA X hX)
    (i : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
    cohomologyOverBase.{u, w} A B hA X hX
        ((Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
          (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).obj M) i ≃ₗ[A]
      cohomologyOverBaseRingUniverse A B hA X hX M i :=
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  have := preservesInjectiveObjects_moduleULift_modules.{u, w} A B hA X hX
  have := preservesFiniteLimits_moduleULift_modules.{u, w} A B hA X hX
  have := preservesFiniteColimits_moduleULift_modules.{u, w} A B hA X hX
  have : (ModuleCat.uliftFunctor.{max (u + 1) w} (GlobalSectionRing
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let N := ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M
  let e := ((Functor.rightDerivedIsoOfSquare
      (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
        (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
      (globalSectionsFunctor.{u + 1, u, u, max (u + 1) w}
        (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
      (ModuleCat.uliftFunctor.{max (u + 1) w} _)
      (globalSectionsModuleULiftIso.{max (u + 1) w, u} _).symm i).app M).symm
  let d : (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
      ((ModuleCat.uliftFunctor.{max (u + 1) w} _).obj N) ≃ₗ[A]
      (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj N :=
    { toFun := fun x => (show ULift.{max (u + 1) w} N from x).down
      invFun := fun x => (ULift.up x : ULift.{max (u + 1) w} N)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).mapIso e).toLinearEquiv.trans d

end AlgebraicGeometry.Space

end
