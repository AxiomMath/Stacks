module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RightDerivedConstantUnitBaseChange
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ZModFiniteTypeDescent
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The higher direct images of `ℤ/ℓ` along a smooth proper curve are locally constant

Let `S` be a Noetherian scheme on which the prime `ℓ` is invertible and `f : X ⟶ S` proper and
smooth with fibres of dimension at most one. Then every `Rᵠ f_* ℤ/ℓ` is a locally constant sheaf of
finite type of `ℤ/ℓ`-modules on `S_étale`
(`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit`).

This is case (a) of the proof of [Stacks, Tag 0GKV]: the stalks are finite (proper base change and
finiteness, Tags 0DDF, 03SC) and the specialization maps are bijective (Tag 0GKD), so the sheaf of
sets underlying `Rᵠ f_* ℤ/ℓ` is finite locally constant (Tag 0GJ7)
(`Stacks.EtaleCohomology.isFiniteLocallyConstant_rightDerived_constantSheaf_of_isUnit`). The base
records only the constructibility which follows
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isUnit`); here the
finite local constancy is kept and read on sheaves of `ℤ/ℓ`-modules
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget₂_zmod`).

It is the input on the compactification `X̄ ⟶ S` of an elementary fibration for the local
constancy of `R¹ f_! ℤ/ℓ` in the fibration step of Poincaré duality, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statement on `Hᵠ(Rf_*(f⁻¹ ℤ/ℓ))` uses the standard model `HasDerivedCategory.standard` of the
derived category, as do its consumers.

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `isFiniteLocallyConstant_rightDerived_constantSheaf_of_isUnit`.
* `isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit`.
* `isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f]
  (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) [IsNoetherian S]
  (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)

include hdim in
/-- **[Stacks, Tag 0GKV], case (a): `Rᵠ f_* ℤ/ℓ` is finite locally constant** as an abelian sheaf,
for `f` proper and smooth with fibres of dimension at most one over a Noetherian base on which `ℓ`
is invertible: its stalks are finite ([Stacks, Tags 0DDF, 03SC]) and its specialization maps
bijective ([Stacks, Tag 0GKD]), so its underlying sheaf of sets is finite locally constant
([Stacks, Tag 0GJ7]). -/
theorem isFiniteLocallyConstant_rightDerived_constantSheaf_of_isUnit
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))) := by
  let S₀ : Set Scheme.{u} := {X, S}
  let B := BigEtaleSite.ofSet S₀
  have hX : B.Contains X := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hS : B.Contains S := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, 0} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, 0} B
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))
  have : Finite A := inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let K := ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj C
  have hScomp : ∀ V : S.Opens, IsCompact (V : Set S) →
      (irreducibleComponents V).Finite := fun V _ =>
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology C := by
    have := isFiniteLocallyConstant_constantSheaf_smallEtale X A
    infer_instance
  have hset := isFiniteLocallyConstant_of_finite_etaleStalk_of_bijective_specializationMap B S
    hS hScomp (forgetSheafTransport B S hS K)
    (fun s => finite_etaleStalk_transport B S hS K s
      (finite_smallEtaleStalkAb_rightDerived_constantSheaf_of_isProper f hdim s A q))
    (fun s σ => by
      rw [geometricSpecialization_eq_ofPoint B S hS σ]
      exact bijective_specializationMapOnStalks_transport B S hS K s σ.point
        (isIso_smallEtaleSpecializationStalkAb_app_rightDerived_of_smooth_of_isProper B S
          hS s σ.point hX f C hlc
          (fun x a => constantSheaf_zmod_stalk_torsion ℓ (isUnit_natCast_of_hom f hℓ) x a) q))
  let e := SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}
  have := Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget _ (e.inverse.obj K) hset
  have h := (SmallEtale.isFiniteLocallyConstant_abelian_sheafEquiv_functor_iff B S hS
    (e.inverse.obj K)).2 inferInstance
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ (e.counitIso.app K) (hF := h)

include hdim in
/-- **`Rᵠ f_* ℤ/ℓ` is locally constant of finite type as a sheaf of `ℤ/ℓ`-modules**, for `f` proper
and smooth with fibres of dimension at most one over a Noetherian base on which `ℓ` is invertible:
its underlying abelian sheaf is finite locally constant
(`Stacks.EtaleCohomology.isFiniteLocallyConstant_rightDerived_constantSheaf_of_isUnit`). -/
@[sga "4 XVI 2.1" "special case", sga "4 XVI 2.2" "special case", sga "7 I 0.1.5" "special case"]
theorem isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      (rightDerivedConstantUnit f q (ZMod ℓ)) := by
  have h := isFiniteLocallyConstant_rightDerived_constantSheaf_of_isUnit f hdim ℓ q hℓ
  have : ∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u + 1} :=
    fun U => (Stacks.ModuleSheaf.hasSheafify_addCommGrpCat.{u + 1} (S.smallEtaleTopology.over U)).1
  have : ∀ U : S.Etale, (S.smallEtaleTopology.over U).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) := fun U =>
    Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} (ZMod ℓ) _
  have : ∀ U : S.Etale, (S.smallEtaleTopology.over U).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) := fun U =>
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} (ZMod ℓ) _
  have : S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} (ZMod ℓ) _
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget₂_zmod
    ℓ _ _ (Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      (rightDerivedConstantUnitForgetIso f q (ZMod ℓ)).symm (hF := h))

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

include hdim in
/-- **`Hᵠ(Rf_*(f⁻¹ ℤ/ℓ))` is locally constant of finite type for every `q ∈ ℤ`**, for `f` proper
and smooth with fibres of dimension at most one over a Noetherian base on which `ℓ` is invertible:
`f⁻¹ ℤ/ℓ` is the constant sheaf, its cohomology vanishes in negative degrees, and in degree `n ≥ 0`
it is `Rⁿ f_* ℤ/ℓ`
(`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit`). -/
@[sga "4 XIV 1.11" "more general",
  sga "4 XVI 2.1" "special case",
  sga "4 XVI 2.2" "special case",
  sga "7 I 0.1.5" "special case"]
theorem isFiniteTypeLocallyConstant_homology_derivedDirectImage_inverseImage_unitSheaf
    (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (p : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ p).obj
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))) := by
  let P : ObjectProperty (EtaleModules.{u, 0} (ZMod ℓ) S) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      S.smallEtaleTopology (ZMod ℓ)
  show P _
  let e := (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) f).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  refine P.prop_of_iso ((DerivedCategory.Plus.homologyFunctor _ p).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) f).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e.symm))) ?_
  rcases lt_or_ge p 0 with hp | hp
  · exact P.prop_of_isZero
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) f).isZero_rightDerivedPlus_of_neg _ p hp)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact P.prop_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} (ZMod ℓ) f) n).app
        (unitSheaf (X := X) ℓ))
      (isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit f hdim ℓ n hℓ)

end Stacks.EtaleCohomology

end
