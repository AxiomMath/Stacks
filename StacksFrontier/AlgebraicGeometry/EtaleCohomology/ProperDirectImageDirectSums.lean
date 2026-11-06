module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimensionDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.UnboundedCoefficientUniverse
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageForget
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageUnboundedLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Proper direct images and direct sums, for torsion coefficients in any universe

Let `f : X ⟶ Y` be a proper morphism of schemes and let `Λ` be a torsion ring in an arbitrary
universe. Then the unbounded derived direct image `Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes
with direct sums. For `Λ = ℤ/nℤ` this is [Stacks, Tag 0F0D], and the argument is the source's. It
is enough to treat a quasi-compact `Y`. There the fibres of `f` have bounded dimension, so
`R^q f_*` vanishes on torsion sheaves above a uniform degree ([Stacks, Tag 095U]). A derived
functor of finite cohomological dimension whose higher derived functors commute with direct sums
commutes with direct sums ([Stacks, Tag 0F11]).

## Main results

* `preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`:
  for `f` quasi-compact and quasi-separated, `R^q f_*` on sheaves of `Λ`-modules commutes with
  direct sums, `Λ` a ring in any universe ([Stacks, Tag 09Z1] for a constant system).
* `preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper_of_compactSpace`:
  the case of a quasi-compact base.
* `preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper`:
  **[Stacks, Tag 0F0D]**, over an arbitrary base.

## Implementation notes

The higher direct images of sheaves of `Λ`-modules are those of the underlying abelian sheaves,
because the underlying abelian sheaf of an injective sheaf of modules is `f_*`-acyclic
(`Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj`); on
abelian sheaves with coefficients in `AddCommGrpCat.{max (u + 1) r}` they commute with direct sums
by `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`,
and forgetting the module structure preserves and reflects direct sums. The base has this for a
ring `Λ : Type` only.

*Reduction to a quasi-compact base.* Represent the summands by K-injective complexes. Their
degreewise direct sum represents the direct sum, and `Rf_*` commutes with this direct sum exactly
when the unit `f_* ⟶ Rf_*` is invertible at it. Being invertible is étale local on `Y`
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover`). Over an
affine open `V` of `Y`, restriction carries the direct sum to the direct sum of the restrictions,
which are K-injective, and there both `(f_V)_*` and `R(f_V)_*` commute with direct sums.

Direct sums are indexed by `Type (max (u + 1) r)`, the morphism universe of the sheaf categories
and the universe relative to which they are Grothendieck abelian.

## References

* [Stacks Project, Tag 0F0D](https://stacks.math.columbia.edu/tag/0F0D)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-! ### Higher direct images and direct sums -/

section HigherDirectImage

attribute [local instance] hasSheafCompose_forget₂_etaleModuleCoefficientUniverse
  preservesSheafification_forget₂_etaleModuleCoefficientUniverse

/-- Forgetting the module structure preserves direct sums of sheaves of `Λ`-modules. -/
lemma preservesColimitsOfShape_discrete_etaleModuleForgetUniv (Z : Scheme.{u})
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleForgetAb.{u, r} Λ Z) := by
  let : PreservesColimits (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, max (u + 1) r, max (u + 1) r} Λ
  exact preservesColimitsOfShape_sheafCompose _ _ (Discrete I)

/-- **Higher direct images of sheaves of `Λ`-modules and of their underlying abelian sheaves
agree**: `R^q f_* ⋙ forget ≅ forget ⋙ R^q f_*`, for `Λ` in any universe. -/
def rightDerivedEtaleModuleDirectImageForgetUnivIso {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (etaleModuleDirectImage.{u, r} Λ f).rightDerived q ⋙ etaleModuleForgetAb.{u, r} Λ Y ≅
      etaleModuleForgetAb.{u, r} Λ X ⋙ (etaleAbelianDirectImage.{u, r} f).rightDerived q :=
  have : (etaleModuleForgetAb.{u, r} Λ Y).PreservesHomology := Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (etaleModuleDirectImage.{u, r} Λ f)
      (etaleModuleForgetAb.{u, r} Λ Y)
      (etaleModuleForgetAb.{u, r} Λ X ⋙ etaleAbelianDirectImage.{u, r} f) (Iso.refl _) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (fun I _ => rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj Λ f I) q

/-- **Higher direct images of sheaves of `Λ`-modules commute with direct sums** along a
quasi-compact and quasi-separated morphism, for a ring `Λ` in any universe. -/
theorem preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) ((etaleModuleDirectImage.{u, r} Λ f).rightDerived q) := by
  have := preservesColimitsOfShape_discrete_etaleModuleForgetUniv Λ X I
  have := preservesColimitsOfShape_discrete_etaleModuleForgetUniv Λ Y I
  have : HasColimitsOfSize.{max (u + 1) r, max (u + 1) r} (EtaleModules.{u, r} Λ Y) :=
    IsGrothendieckAbelian.hasColimits _
  have : ReflectsColimitsOfShape (Discrete I) (etaleModuleForgetAb.{u, r} Λ Y) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleAbelianDirectImage.{u, r} f).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{r} f q I
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleModuleDirectImage.{u, r} Λ f).rightDerived q ⋙ etaleModuleForgetAb.{u, r} Λ Y) :=
    preservesColimitsOfShape_of_natIso (rightDerivedEtaleModuleDirectImageForgetUnivIso Λ f q).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (etaleModuleForgetAb.{u, r} Λ Y)

end HigherDirectImage

/-! ### The unbounded proper direct image and direct sums -/

/-- **Proper direct images commute with direct sums over a quasi-compact base, for a torsion
coefficient ring.** Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` quasi-compact and let
`Λ` be a torsion ring in any universe. Then the unbounded derived direct image
`Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums. -/
theorem preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper_of_compactSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f) := by
  obtain ⟨m, hm, hmΛ⟩ := hΛ
  have hqc := quasiCompact_of_isProper f
  have := quasiSeparated_of_isProper f
  obtain ⟨d, hd⟩ := @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le X Y f
    (IsProper.toLocallyOfFiniteType (f := f)) hqc ‹CompactSpace Y›
  exact preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage Λ f
    ⟨2 * d + 1, fun q hq F => isZero_rightDerived_etaleModuleDirectImage_of_isProper_univ Λ f d hd
      F (isTorsionEtaleModule_of_nsmul_eq_zero_univ Λ m hm hmΛ F) q (by omega)⟩
    (fun q I => preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ Λ f q I)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
    (Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit
      (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)) I


/-! ### Comparing two functors on direct sums -/

section Comparison

variable {C D : Type*} [Category* C] [Category* D] {G H : C ⥤ D} (β : G ⟶ H)
  {J : Type*} (K : J → C) [HasCoproduct K] [HasCoproduct fun j ↦ G.obj (K j)]
  [HasCoproduct fun j ↦ H.obj (K j)]

omit [HasCoproduct K] in
/-- The direct sum of isomorphisms `β.app (K j)` is an isomorphism. -/
lemma isIso_sigmaMap_app [∀ j, IsIso (β.app (K j))] :
    IsIso (Limits.Sigma.map fun j ↦ β.app (K j)) :=
  ⟨⟨Limits.Sigma.map fun j ↦ inv (β.app (K j)), by ext; simp, by ext; simp⟩⟩

/-- The two comparison maps of a direct sum along a transformation `β : G ⟶ H` are compatible
with `β`. -/
lemma sigmaComparison_comp_app (β : G ⟶ H) :
    sigmaComparison G K ≫ β.app (∐ K) =
      Limits.Sigma.map (fun j ↦ β.app (K j)) ≫ sigmaComparison H K := by
  ext j
  simp [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison]

/-- A transformation between two functors preserving a direct sum is invertible at the direct
sum when it is invertible at each summand. -/
lemma isIso_app_sigma_of_preservesColimit [PreservesColimit (Discrete.functor K) G]
    [PreservesColimit (Discrete.functor K) H] [∀ j, IsIso (β.app (K j))] :
    IsIso (β.app (∐ K)) := by
  have := isIso_sigmaMap_app β K
  have : IsIso (sigmaComparison G K ≫ β.app (∐ K)) := by
    rw [sigmaComparison_comp_app]; infer_instance
  exact IsIso.of_isIso_comp_left (sigmaComparison G K) _

/-- If `β : G ⟶ H` is invertible at each summand and at the direct sum, and `G` preserves the
direct sum, then so does `H`. -/
lemma preservesColimit_of_isIso_app_sigma [PreservesColimit (Discrete.functor K) G]
    [∀ j, IsIso (β.app (K j))] [IsIso (β.app (∐ K))] :
    PreservesColimit (Discrete.functor K) H := by
  have := isIso_sigmaMap_app β K
  have : IsIso (sigmaComparison H K) :=
    IsIso.of_isIso_fac_left (sigmaComparison_comp_app (K := K) β).symm
  exact PreservesCoproduct.of_iso_comparison H K

end Comparison

/-! ### Proper direct images and direct sums over an arbitrary base -/

section Local

attribute [local instance] HasDerivedCategory.standard

/-- Sheaves of `Λ`-modules on a small étale site have direct sums indexed by the universe relative
to which they are Grothendieck abelian. -/
local instance (Z : Scheme.{u}) (I : Type (max (u + 1) r)) :
    HasColimitsOfShape (Discrete I) (EtaleModules.{u, r} Λ Z) :=
  haveI := IsGrothendieckAbelian.hasColimits (EtaleModules.{u, r} Λ Z)
  inferInstance

/-- Complexes of sheaves of `Λ`-modules on a small étale site have direct sums, computed
degreewise. -/
local instance (Z : Scheme.{u}) (I : Type (max (u + 1) r)) :
    HasColimitsOfShape (Discrete I) (CochainComplex (EtaleModules.{u, r} Λ Z) ℤ) :=
  inferInstance

/-- Direct image along a quasi-compact and quasi-separated morphism preserves direct sums of
sheaves of `Λ`-modules. -/
lemma preservesColimitsOfShape_discrete_etaleModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleDirectImage.{u, r} Λ f) :=
  have := preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ Λ f 0 I
  preservesColimitsOfShape_of_natIso (etaleModuleDirectImage.{u, r} Λ f).rightDerivedZeroIsoSelf

/-- The unit of the unbounded derived direct image along a proper morphism, `Λ` torsion, is
invertible at a direct sum of K-injective complexes. -/
lemma isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_sigma_of_isProper {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {I : Type (max (u + 1) r)}
    (L : I → CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hL : ∀ k, (L k).IsKInjective) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app (∐ L)) := by
  let 𝒰 := Y.affineCover
  refine isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover Λ f (fun i ↦ 𝒰.f i)
    (coversTop_smallEtaleObj_of_jointlySurjective _ fun y ↦ ⟨𝒰.idx y, 𝒰.covers y⟩)
    (fun i ↦ pullback.fst (𝒰.f i) f) (fun i ↦ pullback.snd (𝒰.f i) f)
    (fun i ↦ IsPullback.of_hasPullback _ _) _ fun i ↦ ?_
  have := AlgebraicGeometry.Scheme.Etale.etale_of_isPullback_snd
    (IsPullback.of_hasPullback (𝒰.f i) f)
  have : CompactSpace (𝒰.X i) := inferInstanceAs (CompactSpace (Spec _))
  let fi := pullback.fst (𝒰.f i) f
  have : IsProper fi := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (𝒰.f i) f).flip inferInstance
  have := quasiCompact_of_isProper fi
  have := quasiSeparated_of_isProper fi
  let XU := pullback (𝒰.f i) f
  let R := (etaleModuleRestriction.{u, r} Λ (pullback.snd (𝒰.f i) f)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let M : I → CochainComplex (EtaleModules.{u, r} Λ XU) ℤ := fun k ↦ R.obj (L k)
  let β := etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fi
  rw [NatTrans.isIso_app_iff_of_iso β (PreservesCoproduct.iso R L)]
  have : ∀ k, IsIso (β.app (M k)) := fun k ↦
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ fi (M k)
      (isKInjective_etaleModuleRestriction Λ (pullback.snd (𝒰.f i) f) (L k))
  have := preservesColimitsOfShape_discrete_etaleModuleDirectImage Λ fi I
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (EtaleModules.{u, r} Λ XU) I
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (EtaleModules.{u, r} Λ (𝒰.X i)) I
  have :=
    preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper_of_compactSpace
      Λ fi hΛ I
  exact isIso_app_sigma_of_preservesColimit β M

/-- Let `f : X ⟶ Y` be a proper morphism of schemes and let `Λ` be a torsion ring, in any
universe; for instance `Λ = ℤ/nℤ` with `n ≥ 1`. Then the unbounded derived direct image
`Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums. -/
@[stacks 0F0D "for a torsion ring Λ in any universe, which contains Λ = ℤ/nℤ, n ≥ 1"]
theorem preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f) := by
  have := quasiCompact_of_isProper f
  have := quasiSeparated_of_isProper f
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (EtaleModules.{u, r} Λ X) I
  have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
    (EtaleModules.{u, r} Λ Y) I
  have := preservesColimitsOfShape_discrete_etaleModuleDirectImage Λ f I
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f
  let β := etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f
  have hKinj : ∀ L : I → CochainComplex (EtaleModules.{u, r} Λ X) ℤ, (∀ k, (L k).IsKInjective) →
      PreservesColimit (Discrete.functor L) (DerivedCategory.Q ⋙ RF) := fun L hL ↦
    have : ∀ k, IsIso (β.app (L k)) := fun k ↦
      isIso_etaleModuleDerivedDirectImageUnboundedUnit_app Λ f (L k) (hL k)
    have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_sigma_of_isProper Λ f hΛ L hL
    preservesColimit_of_isIso_app_sigma β L
  refine ⟨fun {K} ↦ ?_⟩
  choose L s hL hs using fun k : I ↦
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (EtaleModules.{u, r} Λ X) (DerivedCategory.Q.objPreimage (K.obj ⟨k⟩))
  have := hKinj L hL
  have hQ : IsColimit ((DerivedCategory.Q (C := EtaleModules.{u, r} Λ X)).mapCocone
      (colimit.cocone (Discrete.functor L))) :=
    isColimitOfPreserves DerivedCategory.Q (colimit.isColimit _)
  have : PreservesColimit (Discrete.functor L ⋙ DerivedCategory.Q) RF :=
    preservesColimit_of_preserves_colimit_cocone hQ
      (isColimitOfPreserves (DerivedCategory.Q ⋙ RF) (colimit.isColimit _))
  let e : Discrete.functor L ⋙ DerivedCategory.Q ≅ K :=
    Discrete.natIso fun ⟨k⟩ ↦ by
      have : IsIso (DerivedCategory.Q.map (s k)) := by
        rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hs k
      exact (asIso (DerivedCategory.Q.map (s k))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso _
  exact preservesColimit_of_iso_diagram RF e

end Local

end Stacks.EtaleCohomology

end
