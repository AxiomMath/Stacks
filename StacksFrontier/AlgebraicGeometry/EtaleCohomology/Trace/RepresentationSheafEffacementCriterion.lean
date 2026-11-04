module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceable

/-!
# Elementwise effaceability of `H^i(X_K, ℱ_ρ)` from finite étale covers

Let `X` be a connected scheme over a field `k` with a geometric point `x`, `Λ` a finite ring and
`K/k` a field extension. The δ-functor `(M, ρ) ↦ H^i(X_K, ℱ_ρ)`
(`AlgebraicGeometry.geometricRepresentationCohomology`) is effaced, one class at a time, by finite
étale covers of `X`: for a finite étale surjective `π : Y ⟶ X` the sheaf `π_* π^* ℱ_ρ` is again
finite type locally constant (Tags 093R and 095B), hence by Tag 0DV5 it is `ℱ_N` for a finite
`Λ`-module `N` with continuous action, and the unit `ℱ_ρ ⟶ π_* π^* ℱ_ρ` — a monomorphism, `π`
being surjective — is `ℱ_u` for a monomorphism `u : M ⟶ N`. So a class killed by the unit of
some such cover is killed by a monomorphism of representations. This is the coinduced-module
step of the proof of Tag 03VM: `N` is the module coinduced from the open subgroup attached to `Y`.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_directImage_inverseImage` — `π_* π^* G` is
  finite type locally constant for `π` finite étale.
* `Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app` — the unit `G ⟶ π_* π^* G` is a
  monomorphism for `π` surjective.
* `AlgebraicGeometry.representationSheafIsoFiniteTypeLocallyConstant` — `ℱ_ρ` is the inverse of
  Tag 0DV5 on Mathlib's small étale site, for `Λ : Type`.
* `AlgebraicGeometry.exists_mono_geometricRepresentationCohomology_map_eq_zero_of_unit` — a class
  killed by the unit of a finite étale surjective cover is killed by a monomorphism, one class at
  a time.
* `AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit`
  — the effaceability criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at the module
universe `u + 1`: the general instance is indexed by `max (u + 1) r`, and instance search cannot
solve `max (u + 1) ?r = u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at the
module universe `u + 1`, ahead of the abelian-sheaf instance whose sheafification hypothesis cannot
be solved at this universe by instance search. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section FiniteEtaleCover

/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site, at the
module universe `u + 1`. -/
local instance hasWeakSheafify_over_moduleCat_ofScheme (Λ : Type) [Ring Λ] (Z : Scheme.{u})
    (W : Z.Etale) : HasWeakSheafify (Z.smallEtaleTopology.over W) (ModuleCat.{u + 1} Λ) :=
  letI := Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} Λ
    Z.smallEtaleTopology W
  inferInstance

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (π : Y ⟶ X)

/-- **`π_* π^* G` is finite type locally constant** for a finite étale `π` and a finite type
locally constant sheaf `G` of `Λ`-modules: inverse image preserves the condition (Tag 093R) and
direct image along a finite étale morphism does too (Tag 095B). -/
theorem isFiniteTypeLocallyConstant_directImage_inverseImage [IsFinite π] [Etale π]
    (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology G) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology
      ((etaleModuleDirectImage.{u, 0} Λ π).obj ((etaleModuleInverseImage.{u, 0} Λ π).obj G)) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0} π Λ _
    (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_sheafPullback _ _ Λ (smallEtaleBaseChange π)
      (coverPreserving_smallEtaleBaseChange π) G hG)

/-- **The unit `G ⟶ π_* π^* G` is a monomorphism for a surjective `π`**, for sheaves of modules
over any ring: its underlying abelian map is the abelian unit, a monomorphism
(`mono_etaleAbelianUnit_of_surjective`), followed by an isomorphism. -/
theorem mono_etaleModuleInverseImageAdj_unit_app [Surjective π] (G : EtaleModules.{u, 0} Λ X) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app G) := by
  have : Mono ((etaleModuleUnderlyingAbelian X Λ).map
      ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app G)) := by
    rw [etaleModuleUnderlyingAbelianInverseImageIsoOfRing_unit Λ π G]
    have : Mono (((smallEtaleBaseChange π).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).map
        ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).hom.app G)) :=
      inferInstanceAs (Mono (((smallEtaleBaseChange π).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).mapIso
        ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).app G)).hom)
    exact @mono_comp _ _ _ _ _ _ (mono_etaleAbelianUnit_of_surjective π _) _ this
  exact (etaleModuleUnderlyingAbelian X Λ).mono_of_mono_map this

end FiniteEtaleCover

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology Stacks.GroupCohomology

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at the module
universe `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse' (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at the
module universe `u + 1`, ahead of the abelian-sheaf instance whose sheafification hypothesis cannot
be solved at this universe by instance search. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse' (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Raising the module universe from `u + 1` to `u + 1` is isomorphic to the identity, on sheaves
of `Λ`-modules on Mathlib's small étale site. -/
def sheafComposeUliftFunctorIso (Λ : Type) [Ring Λ] (Z : Scheme.{u}) :
    sheafCompose Z.smallEtaleTopology (ModuleCat.uliftFunctor.{0, u + 1} Λ) ≅
      𝟭 (EtaleModules.{u, 0} Λ Z) :=
  NatIso.ofComponents (fun G => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun V => ULift.moduleEquiv.toModuleIso) (fun _ => rfl)))
    (fun _ => by ext; rfl)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ]

/-- **`ℱ_ρ` is the inverse of Tag 0DV5 on Mathlib's small étale site**, for a finite ring
`Λ : Type`: at this universe the lift of coefficients in `AlgebraicGeometry.representationSheaf`
is isomorphic to the identity. -/
def representationSheafIsoFiniteTypeLocallyConstant :
    representationSheaf.{u, 0} B X x Λ ≅
      (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).inverse ⋙
        ObjectProperty.ι _ :=
  representationSheafIsoEtaleSite.{u, 0} B X x Λ ≪≫
    Functor.isoWhiskerLeft
        (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).inverse
      (Functor.isoWhiskerLeft (ObjectProperty.ι _) (sheafComposeUliftFunctorIso Λ X.1) ≪≫
        Functor.rightUnitor _)

/-- `AlgebraicGeometry.representationSheaf` is fully faithful, for a finite ring `Λ : Type`. -/
def representationSheafFullyFaithful : (representationSheaf.{u, 0} B X x Λ).FullyFaithful :=
  ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).fullyFaithfulInverse.comp
    (ObjectProperty.fullyFaithfulι _)).ofIso
    (representationSheafIsoFiniteTypeLocallyConstant B X x Λ).symm

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- **A class killed by the unit of a finite étale cover is killed by a monomorphism of
representations.** If `ξ ∈ H^{n+1}(X_K, ℱ_ρ)` dies under the restriction to `X_K` of the unit
`ℱ_ρ ⟶ π_* π^* ℱ_ρ` of a finite étale surjective `π : Y ⟶ X`, then it dies under `H^{n+1}(ℱ_u)`
for a monomorphism `u : M ⟶ N` of finite `Λ`-modules with continuous action: `π_* π^* ℱ_ρ` is
finite type locally constant (Tags 093R and 095B), hence `ℱ_N` by Tag 0DV5, and the unit, a
monomorphism since `π` is surjective, is `ℱ_u` because `ρ ↦ ℱ_ρ` is fully faithful. -/
theorem exists_mono_geometricRepresentationCohomology_map_eq_zero_of_unit
    {M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)} {n : ℕ}
    (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M))
    {Y : Scheme.{u}} (π : Y ⟶ X.1) [IsFinite π] [Etale π] [Surjective π]
    (hξ : ((etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).map
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
            ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
              ((representationSheaf B X x Λ).obj M))) ξ = 0) :
    ∃ (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (u : M ⟶ N), Mono u ∧
        ((geometricRepresentationCohomology B X x Λ f K).functor (n + 1)).map u ξ = 0 := by
  let E := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ
  let β := representationSheafIsoFiniteTypeLocallyConstant B X x Λ
  let FM := (representationSheaf B X x Λ).obj M
  let H := (etaleModuleDirectImage.{u, 0} Λ π).obj ((etaleModuleInverseImage.{u, 0} Λ π).obj FM)
  have hFM : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology FM :=
    ObjectProperty.prop_of_iso
      (P := fun G : EtaleModules.{u, 0} Λ X.1 ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology G)
      (β.app M).symm (E.inverse.obj M).property
  let H' : ObjectProperty.FullSubcategory (fun G : EtaleModules.{u, 0} Λ X.1 ↦
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology G) :=
    ⟨H, isFiniteTypeLocallyConstant_directImage_inverseImage Λ π FM hFM⟩
  let N := E.functor.obj H'
  let θ : (representationSheaf B X x Λ).obj N ≅ H :=
    β.app N ≪≫ (ObjectProperty.ι _).mapIso (E.unitIso.app H').symm
  let hFF := representationSheafFullyFaithful B X x Λ
  let u : M ⟶ N := hFF.preimage ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app FM ≫ θ.inv)
  have hu : (representationSheaf B X x Λ).map u =
      (etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app FM ≫ θ.inv := hFF.map_preimage _
  refine ⟨N, u, ?_, ?_⟩
  · have := mono_etaleModuleInverseImageAdj_unit_app Λ π FM
    have := hFF.faithful
    refine (representationSheaf B X x Λ).mono_of_mono_map ?_
    rw [hu]
    infer_instance
  · change ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((representationSheaf B X x Λ).map u)) ξ = 0
    rw [hu, Functor.map_comp, Functor.map_comp]
    exact (congrArg (ConcreteCategory.hom (((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map θ.inv)))
        hξ).trans (map_zero _)

/-- **Elementwise effaceability of `(M, ρ) ↦ H^i(X_K, ℱ_ρ)` from finite étale covers.** Suppose
that every class of `H^{n+1}(X_K, ℱ_ρ)` dies under the restriction to `X_K` of the unit
`ℱ_ρ ⟶ π_* π^* ℱ_ρ` of some finite étale surjective `π : Y ⟶ X`. Then the δ-functor
`AlgebraicGeometry.geometricRepresentationCohomology` is elementwise effaceable.

The sheaf `π_* π^* ℱ_ρ` is finite type locally constant (Tags 093R and 095B), so by Tag 0DV5 it is
`ℱ_N` for a finite `Λ`-module `N` with continuous action, and the unit is `ℱ_u` for a morphism
`u : M ⟶ N`, a monomorphism because the unit is one (`π` is surjective) and `ρ ↦ ℱ_ρ` is
faithful. -/
theorem elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit
    (h : ∀ (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (n : ℕ) (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M)),
      ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π),
        ((etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).map
          ((etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
            ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
              ((representationSheaf B X x Λ).obj M))) ξ = 0) :
    (geometricRepresentationCohomology B X x Λ f K).ElementwiseEffaceable where
  exists_mono {M} {n} ξ := by
    obtain ⟨Y, π, _, _, _, hξ⟩ := h M n ξ
    exact exists_mono_geometricRepresentationCohomology_map_eq_zero_of_unit B X x Λ f K ξ π hξ

end AlgebraicGeometry

end
