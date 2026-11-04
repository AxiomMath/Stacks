module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCurveVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology

/-!
# `RΓ^Gal(X_k̄, F)` of a curve is concentrated in degrees `[0, 2]`

For a curve `X` over `k`, a separable algebraic closure `k̄` and a sheaf `F` of modules over a
finite ring on `X_ét`, the Galois-equivariant derived global sections `RΓ^Gal(X_k̄, F)`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSections`) have no cohomology outside `[0, 2]`
(`Stacks.EtaleCohomology.isZero_homology_galoisDerivedGlobalSections_single`). Forgetting the
Galois action is exact and faithful and carries `RΓ^Gal(X_k̄, -)` to `RΓ(X_k̄, -|_{X_k̄})`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso`), whose cohomology vanishes above
degree `2` (Tag 0A53, `Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_two_lt`).

This is the vanishing of `H^q(Γ^Gal(ℋom^•(I, K)))` outside `[0, 2]` in the derived Poincaré duality
of Tag 03VM, read through `RΓ^Gal(X, ℋom(F, μ_n))`.

## References

* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the coefficient
universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisVanishing (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned at the module universe `u + 1`. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisVanishing (Λ : Type)
    [Ring Λ] (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

/-- The underlying module of a discrete Galois module is a left exact functor (pinned). -/
local instance (priority := 3000) preservesFiniteLimits_galoisModulesUnderlying_galoisVanishing
    (Λ : Type) [Ring Λ] {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteLimits
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
    (K ≃ₐ[k] K)

/-- The underlying module of a discrete Galois module is a right exact functor (pinned). -/
local instance (priority := 3000) preservesFiniteColimits_galoisModulesUnderlying_galoisVanishing
    (Λ : Type) [Ring Λ] {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteColimits
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
    (K ≃ₐ[k] K)

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] [Algebra.IsSeparable k kbar]
  [QuasiCompact (Over.mk f).hom] [QuasiSeparated (Over.mk f).hom]

/-- **`H^q(X_k̄, F) = 0` for `q > 2`, with its Galois action**: the right derived functors of
`Γ^Gal(X_k̄, -)` on a curve vanish above degree `2`. -/
theorem isZero_rightDerivedPlus_galoisGlobalSections_of_two_lt (F : EtaleModules.{u, 0} Λ X)
    (q : ℤ) (hq : 2 < q) :
    IsZero (((galoisGlobalSections Λ (Over.mk f) kbar).rightDerivedPlus q).obj F) := by
  have hU : IsZero ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
      (kbar ≃ₐ[k] kbar)).obj
        (((galoisGlobalSections Λ (Over.mk f) kbar).rightDerivedPlus q).obj F)) := by
    refine IsZero.of_iso ?_ ((((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlusHomologyNatIso q).app _).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (((galoisDerivedGlobalSectionsForgetIso Λ (Over.mk f) kbar).app _) ≪≫
          (etaleModuleGlobalSections.{u, 0} Λ
            (fieldBaseChange (Over.mk f) kbar)).rightDerivedFunctorPlus.mapIso
            (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f)
              kbar)).singleFunctorCompMapDerivedCategoryPlusIso).app F)))
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg (by omega)⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl _).2
      (isZero_rightDerived_fieldBaseChange_of_two_lt Λ f kbar inferInstance _ (by omega))
  rw [IsZero.iff_id_eq_zero]
  apply (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
    (kbar ≃ₐ[k] kbar)).map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact hU.eq_of_src _ _

/-- **`RΓ^Gal(X_k̄, F)` is concentrated in degrees `[0, 2]`** for a sheaf `F` of modules over a
finite ring on a curve `X`. -/
theorem isZero_homology_galoisDerivedGlobalSections_single (F : EtaleModules.{u, 0} Λ X) (q : ℤ)
    (hq : q < 0 ∨ 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Plus.ι.obj
      ((galoisDerivedGlobalSections Λ (Over.mk f) kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  rcases hq with hq | hq
  · exact (galoisGlobalSections Λ (Over.mk f) kbar).isZero_rightDerivedPlus_of_neg F q hq
  · exact isZero_rightDerivedPlus_galoisGlobalSections_of_two_lt Λ f kbar F q hq

/-- **`Hᵠ(X_k̄, -)` with its Galois action, forgetting the action, is
`Hᵠ(X_k̄, -|_{X_k̄})`**,
naturally: the comparison `Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso` read on
cohomology of complexes concentrated in degree `0`. -/
def galoisRightDerivedPlusForgetIso (q : ℤ) :
    (galoisGlobalSections Λ (Over.mk f) kbar).rightDerivedPlus q ⋙
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)) ≅
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)) ⋙
        (etaleModuleGlobalSections.{u, 0} Λ
          (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (galoisGlobalSections Λ (Over.mk f) kbar).rightDerivedFunctorPlus)
      ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlusHomologyNatIso q).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk f) kbar))
      (DerivedCategory.Plus.homologyFunctor _ q) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk f) kbar)).singleFunctorCompMapDerivedCategoryPlusIso
      (etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk f) kbar)).rightDerivedFunctorPlus)
      (DerivedCategory.Plus.homologyFunctor _ q)

end Stacks.EtaleCohomology

end
