module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.ProperSpecializationOfFibreRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.ConstantExtRestrictionBijectiveOnExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.StrictlyHenselianFibreRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Specialization maps of `Rf_* ℤ/ℓ` for a smooth proper family of curves, `ℓ` invertible

Let `f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most
one, and `ℓ` a prime invertible on `S`. For every geometric point `s` of `S` and every geometric
point `t` of `Spec 𝒪^{sh}_{S,s}`, the specialization map
`(Rf_* ℤ/ℓ)_s ⟶ (Rf_* ℤ/ℓ)_{t'}` is an isomorphism.

By `AlgebraicGeometry.isIso_specializationMap_of_isProper_of_isIso_restriction` it suffices that
pullback of derived sections along the fibre `h : X_t ⟶ Y` of `Y = X ×_S Spec 𝒪^{sh}_{S,s}` over
`t` be invertible on `ℤ/ℓ`. That is bijectivity of restriction `Hᵠ(Y, ℤ/ℓ) → Hᵠ(X_t, ℤ/ℓ)` in
every degree (in the namespace `Stacks.EtaleCohomology`:
`isIso_smallEtaleDerivedGlobalSectionsRestriction_single_of_isBijectiveOnExt` and
`bijective_constantExtRestriction_iff_isBijectiveOnExt`), which follows
from the same statement for the closed geometric fibre, a consequence of proper base change
(`AlgebraicGeometry.hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange`),
by `Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_strictlyHenselian`.

## Main results

* `AlgebraicGeometry.isIso_specializationMap_constantSheaf_of_smooth_of_isProper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The dimension of a base change to a field is bounded by the fibre dimensions.** If every
fibre of a morphism `f : X ⟶ S` locally of finite type has dimension at most `d`, then so does
the base change of `f` along any morphism `Spec k ⟶ S` from the spectrum of a field: it is the
fibre of the base change over the unique point of `Spec k`, whose dimension is that of a fibre of
`f` by Tag 05F8. -/
theorem topologicalKrullDim_pullback_le_of_forall_fiber_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {k : Type u} [Field k] (y : Spec (.of k) ⟶ S) (d : WithBot ℕ∞)
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) :
    topologicalKrullDim (pullback f y : Scheme.{u}) ≤ d := by
  let fη : pullback f y ⟶ Spec (.of k) := pullback.snd f y
  let o : Spec (.of k) := IsLocalRing.closedPoint k
  have hpre : ⇑fη ⁻¹' {o} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  have h₁ : topologicalKrullDim (pullback f y : Scheme.{u}) =
      topologicalKrullDim (⇑fη ⁻¹' {o}) := by
    rw [hpre]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm
  rw [h₁, ← IsHomeomorph.topologicalKrullDim_eq _ (fη.fiberHomeo o).isHomeomorph]
  change fη.fiberDimension o ≤ d
  rw [congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback (IsPullback.of_hasPullback f y)) o]
  exact hdim _

/-- **The fibres of a base change have the dimensions of fibres of the original morphism**, here:
if every fibre of `f` has dimension at most `d`, so does every fibre of `pullback.snd f g`. -/
theorem topologicalKrullDim_fiber_pullbackSnd_le {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [LocallyOfFiniteType f] (d : WithBot ℕ∞)
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) (r : T) :
    topologicalKrullDim ((pullback.snd f g).fiber r) ≤ d := by
  change topologicalKrullDim
    (Limits.pullback (pullback.snd f g) (T.fromSpecResidueField r) : Scheme.{u}) ≤ d
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso f g (T.fromSpecResidueField r)).inv.homeomorph.isHomeomorph]
  exact topologicalKrullDim_pullback_le_of_forall_fiber_le f _ d hdim

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The constant abelian sheaf `ℤ/ℓ` on `X_étale`, the underlying abelian sheaf of the constant
sheaf of `ℤ/ℓ`-modules. -/
@[sga "7 XXII 2.0"]
abbrev constantZModAb (X : Scheme.{u}) (ℓ : ℕ) : Sheaf (smallEtaleTopology X) Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    ((forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))

/-- The constant abelian sheaf `ℤ/ℓ` is the underlying abelian sheaf of the constant sheaf of
`ℤ/ℓ`-modules. -/
def constantZModAbIso (X : Scheme.{u}) (ℓ : ℕ) :
    (etaleModuleUnderlyingAbelian X (ZMod ℓ)).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) X.smallEtaleTopology) ≅
      constantZModAb X ℓ :=
  (etaleModuleForgetConstantSheafIso.{u, 0} (ZMod ℓ) X).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- The restriction of `ℤ/ℓ` along `g` is `ℤ/ℓ`. -/
def smallEtalePullbackAbConstantZModAbIso {X Y : Scheme.{u}} (g : Y ⟶ X) (ℓ : ℕ) :
    (smallEtalePullbackAb g).obj (constantZModAb X ℓ) ≅ constantZModAb Y ℓ :=
  (smallEtalePullbackAbIsoInverseImage g).app _ ≪≫
    (etaleAbelianInverseImageConstantIso.{u, 0} g).app _

/-- The constant sheaf `ℤ/ℓ` is torsion. -/
theorem torsionSheafProperty_constantZModAb (X : Scheme.{u}) (ℓ : ℕ) [NeZero ℓ] :
    Stacks.Torsion.torsionSheafProperty (smallEtaleTopology X) (constantZModAb X ℓ) := by
  refine (Stacks.Torsion.torsionSheafProperty _).prop_of_iso (constantZModAbIso X ℓ) fun U x => ?_
  refine ⟨⊤, (smallEtaleTopology X).top_mem U, fun V g _ => ⟨ℓ, Nat.pos_of_neZero ℓ, ?_⟩⟩
  change ℓ • ((Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ)
    X.smallEtaleTopology).obj.map g.op x) = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

/-- **Pullback of derived sections of `ℤ/ℓ` along `g` is invertible iff restriction
`Hᵠ(Y, ℤ/ℓ) → Hᵠ(W, ℤ/ℓ)` is bijective in every degree.** -/
theorem isIso_restriction_single_constantZModAb_iff {W Y : Scheme.{u}} (g : W ⟶ Y) (ℓ : ℕ) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction g).app
        ((DerivedCategory.singleFunctor _ 0).obj (constantZModAb Y ℓ))) ↔
      ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ) g q) := by
  rw [← NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.singleFunctor _ 0).mapIso (constantZModAbIso Y ℓ))]
  exact ⟨fun hiso q => (bijective_constantExtRestriction_iff_isBijectiveOnExt (ZMod ℓ) g q).2
      (isBijectiveOnExt_of_isIso_smallEtaleDerivedGlobalSectionsRestriction_single g _ hiso q),
    fun hb => isIso_smallEtaleDerivedGlobalSectionsRestriction_single_of_isBijectiveOnExt g _
      fun n => (bijective_constantExtRestriction_iff_isBijectiveOnExt (ZMod ℓ) g n).1 (hb n)⟩

/-- **The specialization maps of `Rf_* ℤ/ℓ` are isomorphisms** for `f` proper and smooth with
geometrically connected fibres of dimension at most one and `ℓ` a prime invertible on `S`. -/
theorem isIso_specializationMap_constantSheaf_of_smooth_of_isProper [IsProper f] [Smooth f]
    [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (constantZModAb X ℓ)))) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := etaleLocalRing_strictHenselian B S hS s
  have hsq := IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s)
  have : IsProper (strictHenselizationBaseChangeToStrictHenselization B hS f s) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have : Smooth (strictHenselizationBaseChangeToStrictHenselization B hS f s) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have : GeometricallyConnected
      (strictHenselizationBaseChangeToStrictHenselization B hS f s) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have hℓR : IsUnit (ℓ : ↥(etaleLocalRing B S hS s)) := by
    simpa only [map_natCast] using hℓ.map ((strictHenselizationToBase B S hS s).appTop ≫
      (Scheme.ΓSpecIso (.of ↥(etaleLocalRing B S hS s))).hom).hom
  -- restriction to the closed geometric fibre is bijective, by proper base change
  have hi : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ)
      (geometricFibreToStrictHenselizationBaseChange B hS f s) q) :=
    (isIso_restriction_single_constantZModAb_iff _ ℓ).1
      (hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange B
        (fun _ _ g _ => cohomologyCommutesWithBaseChange_of_isProper g) hS f s _ 0 inferInstance
        (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ _
          (torsionSheafProperty_constantZModAb (strictHenselizationBaseChange B hS f s) ℓ)))
  -- hence so is restriction to the fibre over `t`
  have hh : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ)
      (cospecializationFibreToBaseChange B hS f s t) q) :=
    Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_strictlyHenselian
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (topologicalKrullDim_fiber_pullbackSnd_le f _ _ hdim _)
      hℓR (geometricPointToStrictHenselization B S hS s) t.hom
      (isPullback_geometricFibreToStrictHenselizationBaseChange B hS f s)
      (IsPullback.of_hasPullback
        (strictHenselizationBaseChangeToStrictHenselization B hS f s) t.hom) hi
  refine isIso_specializationMap_of_isProper_of_isIso_restriction B hS f s t _ 0 inferInstance
    (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ _
      (torsionSheafProperty_constantZModAb X ℓ)) ?_
  exact (NatTrans.isIso_app_iff_of_iso _
    (((smallEtalePullbackAb
      (strictHenselizationBaseChangeToSource B hS f s)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (smallEtalePullbackAbConstantZModAbIso
          (strictHenselizationBaseChangeToSource B hS f s) ℓ))).2
    ((isIso_restriction_single_constantZModAb_iff _ ℓ).2 hh)

end AlgebraicGeometry

end
