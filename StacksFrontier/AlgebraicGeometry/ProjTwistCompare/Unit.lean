module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The unit of the graded twisting algebra, and its compatibility with the comparison maps

The degree-zero twist `𝒪_{Proj 𝒮}(0)` is the sheaf associated to the ring with its grading
extended to `ℤ` by zero, so a section of the structure sheaf is a section of it: a homogeneous
fraction `a / s` of equal degrees has numerator homogeneous of the right degree for the
degree-zero twist. That inclusion is the unit of the graded algebra `⨁_n 𝒪(n)`, and the
comparison maps `θ` of `StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist` respect it.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompare.unitSection`: a section of the structure sheaf read
  as a section of the degree-zero twist.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap`: the unit
  `𝒪_{Proj 𝒮} ⟶ 𝒪_{Proj 𝒮}(0)`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistUnit`: the unit of `ℬ`'s twisting
  algebra restricted to `U(ψ)`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.pushforwardTwistUnit`: that unit pushed forward
  along `mapHom`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_twistUnitMap`: the unit law,
  in adjoint form: `θ` composed after the unit of `𝒜`'s twisting algebra is the unit of `ℬ`'s,
  carried across `mapHom` on the structure sheaves.

## Implementation notes

The unit is built with `PresheafOfModules.homMk`, as `θ` is: the module structures involved are
not found by instance search if the `app` is written as a `ModuleCat.ofHom` of a structure
literal.

The unit law is stated in the adjoint form, as a morphism into the pushforward of a
restriction, where both sides are concrete families of homogeneous fractions, rather than as an
equality of morphisms out of `𝒪_{U(ψ)}` written with `SheafOfModules.pullbackObjUnitToUnit`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

section one

variable {S : Type u} {ρ : Type w} [CommRing S] [SetLike ρ S] [AddSubgroupClass ρ S]
  (𝒮 : ℕ → ρ) [GradedRing 𝒮]

/-- A section of the structure sheaf, read as a section of the degree-zero twist: its value at
each point is a homogeneous fraction of equal degrees, whose numerator is homogeneous of the
degree the degree-zero twist asks for. -/
public def unitSection (U : (AlgebraicGeometry.Proj 𝒮).Opens)
    (r : Γ(AlgebraicGeometry.Proj 𝒮, U)) : (twistingSheaf 𝒮 0).val.obj (.op U) := by
  refine ⟨fun x => (r.1 x).val, fun x => ?_⟩
  obtain ⟨V, hxV, iV, k, num, den, hden, hw⟩ := r.2 x
  refine ⟨V, hxV, iV, k, num.1, den.1, ?_, den.2, hden, ?_⟩
  · simp [num.2]
  · intro y
    have hwy : r.1 (iV y) = HomogeneousLocalization.mk ⟨k, num, den, hden y⟩ := hw y
    change (r.1 (iV y)).val = LocalizedModule.mk num.1 ⟨den.1, hden y⟩
    rw [hwy]
    rfl

/-- The defining formula for `unitSection`. -/
public theorem unitSection_val (U : (AlgebraicGeometry.Proj 𝒮).Opens)
    (r : Γ(AlgebraicGeometry.Proj 𝒮, U)) (x : ↥U) :
    (unitSection 𝒮 U r).1 x = (r.1 x).val := rfl

/-- The unit of the graded twisting algebra on the underlying presheaves of abelian groups. -/
public def unitPresheafMap :
    (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf).val.presheaf ⟶
      (twistingSheaf 𝒮 0).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := unitSection 𝒮 U.unop
      map_zero' := Subtype.ext (funext fun _ => HomogeneousLocalization.val_zero)
      map_add' := fun _ _ => Subtype.ext (funext fun _ =>
        HomogeneousLocalization.val_add _ _) }
  naturality := by
    intro U V f
    ext a
    exact Subtype.ext (funext fun _ => rfl)

/-- **The unit of the graded twisting algebra**: the structure sheaf included into its own
degree-zero twist. -/
public def twistUnitMap :
    SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf ⟶ twistingSheaf 𝒮 0 :=
  ⟨PresheafOfModules.homMk (unitPresheafMap 𝒮) (fun _ _ _ =>
    Subtype.ext (funext fun _ => HomogeneousLocalization.val_mul _ _))⟩

/-- The defining formula for the unit, read off the morphism. -/
public theorem twistUnitMap_app_val (U : (Opens ↑(AlgebraicGeometry.Proj 𝒮))ᵒᵖ)
    (r : (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf).val.obj U) (x : ↑U.unop) :
    (((twistUnitMap 𝒮).val.app U).hom' r).1 x = (r.1 x).val := rfl

end one


section two

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The unit of `ℬ`'s twisting algebra restricted to `U(ψ)`, on presheaves of abelian groups. -/
public def restrictUnitPresheafMap (ψ : 𝒜 →+*ᵍ ℬ) :
    (SheafOfModules.unit (mapDomain 𝒜 ℬ ψ).toScheme.ringCatSheaf).val.presheaf ⟶
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj
        (twistingSheaf ℬ 0)).val.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun := unitSection ℬ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V.unop)
      map_zero' := Subtype.ext (funext fun _ => HomogeneousLocalization.val_zero)
      map_add' := fun _ _ => Subtype.ext (funext fun _ =>
        HomogeneousLocalization.val_add _ _) }
  naturality := by
    intro V W f
    ext t
    exact Subtype.ext (funext fun _ => rfl)

/-- The unit of `ℬ`'s graded twisting algebra, restricted to `U(ψ)`. -/
public def restrictTwistUnit (ψ : 𝒜 →+*ᵍ ℬ) :
    SheafOfModules.unit (mapDomain 𝒜 ℬ ψ).toScheme.ringCatSheaf ⟶
      (Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ 0) :=
  ⟨PresheafOfModules.homMk (restrictUnitPresheafMap 𝒜 ℬ ψ) (fun V r m => by
    refine Subtype.ext (funext fun z => ?_)
    have hL : ((ConcreteCategory.hom ((restrictUnitPresheafMap 𝒜 ℬ ψ).app V)) (r • m)).1 z =
        (r.1 z).val * (m.1 z).val := HomogeneousLocalization.val_mul _ _
    have hR : (r • (ConcreteCategory.hom ((restrictUnitPresheafMap 𝒜 ℬ ψ).app V)) m).1 z =
        ((((mapDomain 𝒜 ℬ ψ).ι.appIso V.unop).inv.hom' r).1 z).val * (m.1 z).val := rfl
    rw [hL, hR]
    exact congrArg (fun t => (t.1 z).val * (m.1 z).val)
      (ι_appIso_inv_apply 𝒜 ℬ ψ V.unop r).symm)⟩

/-- The unit of `ℬ`'s twisting algebra on `U(ψ)`, pushed forward along `mapHom`. -/
public def pushforwardTwistUnit (ψ : 𝒜 →+*ᵍ ℬ) :
    SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ 0)) :=
  SheafOfModules.unitToPushforwardObjUnit (mapHom 𝒜 ℬ ψ).toRingCatSheafHom ≫
    (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map (restrictTwistUnit 𝒜 ℬ ψ)

/-- The comparison map on the degree-zero twist carries the unit of `𝒜`'s graded twisting
algebra to the unit of `ℬ`'s, over `mapHom`. -/
public theorem twistPushforwardMap_twistUnitMap (ψ : 𝒜 →+*ᵍ ℬ) :
    twistUnitMap 𝒜 ≫ twistPushforwardMap 𝒜 ℬ ψ 0 = pushforwardTwistUnit 𝒜 ℬ ψ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  refine Subtype.ext (funext fun z => ?_)
  exact twistFibreMap_val_app 𝒜 ℬ ψ U.unop r z

end two

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
