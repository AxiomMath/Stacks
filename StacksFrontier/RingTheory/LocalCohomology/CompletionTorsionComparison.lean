module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local cohomology of `I`-power torsion modules over a ring and over its completion

Let `R` be a Noetherian ring of finite dimension, `I ⊆ R` an ideal, `A = R^∧` the `I`-adic
completion, `T ⊆ Spec(R)` stable under specialization with `T ⊆ V(I)`, and `T_A ⊆ Spec(A)` its
preimage. For an `A`-module `N` killed by a power of `IA`, local cohomology with support in
`T_A`, read as an `R`-module, is local cohomology with support in `T` of `N` read as an
`R`-module:

`H^i_{T_A}(N) ≅ H^i_T(N)`,

naturally in `N`. The comparison is the composite

`H^i_{T_A}(N) ≅ H^i_{T_A}(A ⊗_R N) ≅ A ⊗_R H^i_T(N) ≅ H^i_T(N)`.

The middle isomorphism is flat base change of local cohomology with general support
([Stacks, Tag 0EF5], `Stacks.LocalCohomology.derivedSectionsWithSupportInBaseChangeIso`) read on
modules placed in degree zero; the two outer ones say that `I`-power torsion modules do not see the
difference between `R` and `A`: the counit `A ⊗_R N ⟶ N` is bijective for an `IA`-power torsion
`A`-module, and the unit `P ⟶ A ⊗_R P` is bijective for an `I`-power torsion `R`-module, because
`A` is flat over `R` and `R/I = A/IA`
(`IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective`). The module `H^i_T(N)` is
`I`-power torsion because it is supported in `T ⊆ V(I)`.

## Main definitions

* `Stacks.LocalCohomology.extendScalarsLocalCohomologyIso` — `H^i_{T_A}(A ⊗_R M) ≅ A ⊗_R H^i_T(M)`,
  naturally in the `R`-module `M`, for any flat map of Noetherian rings of finite dimension.
* `Stacks.LocalCohomology.completionTorsionLocalCohomologyNatIso` — the natural isomorphism
  `H^i_{T_A}(N) ≅ H^i_T(N)` of `R`-modules on a diagram of `IA`-power torsion `A`-modules.

## References

* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### Flat base change on modules -/

section BaseChange

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
  [IsNoetherianRing A] (f : R →+* A) (hf : f.Flat) (T : Set (PrimeSpectrum R))
  (hT : StableUnderSpecialization T) (hR : ringKrullDim R < ⊤) (hA : ringKrullDim A < ⊤)

/-- **Flat base change of local cohomology on modules.** For a flat map `f : R → A` of Noetherian
rings of finite dimension and `T ⊆ Spec(R)` stable under specialization, with preimage
`T_A ⊆ Spec(A)`, there is an isomorphism `H^i_{T_A}(A ⊗_R M) ≅ A ⊗_R H^i_T(M)`, natural in the
`R`-module `M`. It is [Stacks, Tag 0EF5] applied to `M` placed in degree zero, together with the
exactness of `A ⊗_R -`. -/
def extendScalarsLocalCohomologyIso (i : ℤ) :
    ModuleCat.extendScalars.{u, u, u} f ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} A ((PrimeSpectrum.comap f) ⁻¹' T) i ≅
      localCohomologyWithSupportInModuleFunctor.{u, u} R T i ⋙
        ModuleCat.extendScalars.{u, u, u} f :=
  letI := preservesFiniteLimits_extendScalars_of_flat.{u, u, u} f hf
  let E := ModuleCat.extendScalars.{u, u, u} f
  let D := (derivedExtensionScalarsGeneral.{u, u, u} f).functor
  let e₀ : E ⋙ DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ≅
      DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ D :=
    (E.mapDerivedCategorySingleFunctor 0).symm ≪≫
      Functor.isoWhiskerLeft _ (derivedExtensionScalarsIsoMapDerivedCategory.{u, u, u} f).symm
  let e₁ := (derivedSectionsWithSupportInBaseChangeIso.{u, u, u} f hf T hT hR hA).1
  Functor.isoWhiskerRight e₀ (derivedSectionsWithSupportIn.{u, u} A
      ((PrimeSpectrum.comap f) ⁻¹' T) ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0)
      (Functor.isoWhiskerRight e₁.symm (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
      derivedSectionsWithSupportIn.{u, u} R T)
      (derivedExtensionScalarsHomologyNatIso.{u, u, u} f i)

end BaseChange

/-! ### The comparison for `I`-power torsion modules -/

section Completion

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

/-- The unit `P ⟶ A ⊗_R P` of extension of scalars to the completion is bijective on an `I`-power
torsion `R`-module. -/
@[sga "2 IV 4.6" "more general"]
theorem bijective_extendRestrictScalarsAdj_unit_adicCompletion (P : ModuleCat.{u} R)
    (hP : IsIPowerTorsion R P I) :
    Function.Bijective
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap R (AdicCompletion I R))).unit.app P) := by
  have h := (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, u, u} R
    (AdicCompletion I R) I inferInstance).2
    (AdicCompletion.quotientMap_bijective I (Ideal.fg_of_isNoetherianRing I)) P hP
  exact IPowerTorsion.one_tmul_bijective h

variable (hR : ringKrullDim R < ⊤) (hA : ringKrullDim (AdicCompletion I R) < ⊤)
  (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T)
  (hTI : T ⊆ PrimeSpectrum.zeroLocus (I : Set R))

/-- **Local cohomology of `I`-power torsion modules over a ring and over its completion.** Let `R`
be a Noetherian ring of finite dimension, `A` its `I`-adic completion (assumed of finite
dimension), `T ⊆ V(I)` stable under specialization and `T_A` its preimage in `Spec(A)`. For a
diagram `D` of `A`-modules each killed by a power of `IA`, local cohomology with support in `T_A`
read over `R` is naturally isomorphic to local cohomology with support in `T` of the modules read
over `R`. -/
def completionTorsionLocalCohomologyNatIso {J : Type*} [Category J]
    (D : J ⥤ ModuleCat.{u} (AdicCompletion I R))
    (hD : ∀ j, ∃ k : ℕ, (I.map (algebraMap R (AdicCompletion I R))) ^ k •
      (⊤ : Submodule (AdicCompletion I R) (D.obj j)) = ⊥) (i : ℤ) :
    D ⋙ localCohomologyWithSupportInModuleFunctor.{u, u} (AdicCompletion I R)
        ((PrimeSpectrum.comap (algebraMap R (AdicCompletion I R))) ⁻¹' T) i ⋙
        ModuleCat.restrictScalars.{u} (algebraMap R (AdicCompletion I R)) ≅
      D ⋙ ModuleCat.restrictScalars.{u} (algebraMap R (AdicCompletion I R)) ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} R T i := by
  let φ := algebraMap R (AdicCompletion I R)
  have hflat : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ
  let res := ModuleCat.restrictScalars.{u} φ
  let LA := localCohomologyWithSupportInModuleFunctor.{u, u} (AdicCompletion I R)
    ((PrimeSpectrum.comap φ) ⁻¹' T) i
  let LR := localCohomologyWithSupportInModuleFunctor.{u, u} R T i
  let α := extendScalarsLocalCohomologyIso φ hflat T hT hR hA i
  -- The counit is invertible on the terms of the diagram.
  have hcounit (j : J) : IsIso (adj.counit.app (D.obj j)) := by
    obtain ⟨k, hk⟩ := hD j
    have htor : IsIPowerTorsion (AdicCompletion I R) (D.obj j) (I.map φ) := fun m =>
      ⟨k + 1, Nat.succ_pos k, fun a ha => by
        have hmem : a • m ∈ (I.map φ) ^ k • (⊤ : Submodule (AdicCompletion I R) (D.obj j)) :=
          Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ k) ha) Submodule.mem_top
        rw [hk] at hmem
        exact hmem⟩
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (IPowerTorsion.extendRestrictScalarsAdj_counit_app_bijective.{u, u, u} I inferInstance
        (AdicCompletion.quotientMap_bijective I (Ideal.fg_of_isNoetherianRing I)) (D.obj j) htor)
  -- The unit is invertible on local cohomology with support in `T ⊆ V(I)`.
  have hunit (M : ModuleCat.{u} R) : IsIso (adj.unit.app (LR.obj M)) := by
    have htor : IsIPowerTorsion R (LR.obj M) I :=
      isIPowerTorsion_of_support_subset (Ideal.fg_of_isNoetherianRing I)
        ((support_localCohomologyWithSupportIn_subset.{u, u} T _ i).trans hTI)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_extendRestrictScalarsAdj_unit_adicCompletion I (LR.obj M) htor)
  let N₁ : D ⋙ LA ⋙ res ≅ D ⋙ res ⋙ ModuleCat.extendScalars.{u, u, u} φ ⋙ LA ⋙ res :=
    NatIso.ofComponents (fun j => haveI := hcounit j
        (res.mapIso (LA.mapIso (asIso (adj.counit.app (D.obj j))))).symm)
      (fun {j j'} g => by
        have := hcounit j
        have := hcounit j'
        have h1 := adj.counit.naturality (D.map g)
        simp only [Functor.comp_map, Functor.id_map] at h1
        simp only [Functor.comp_map, Iso.symm_hom, Functor.mapIso_inv, asIso_inv]
        rw [← res.map_comp, ← res.map_comp, ← LA.map_comp, ← LA.map_comp]
        congr 2
        rw [IsIso.eq_inv_comp, ← Category.assoc, ← h1, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id])
  let N₂ : D ⋙ res ⋙ ModuleCat.extendScalars.{u, u, u} φ ⋙ LA ⋙ res ≅
      D ⋙ res ⋙ LR ⋙ ModuleCat.extendScalars.{u, u, u} φ ⋙ res :=
    NatIso.ofComponents (fun j => res.mapIso (α.app (res.obj (D.obj j))))
      (fun {j j'} g => by
        have h2 := α.hom.naturality (res.map (D.map g))
        simp only [Functor.comp_map] at h2
        simp only [Functor.comp_map, Functor.mapIso_hom, Iso.app_hom]
        rw [← res.map_comp, ← res.map_comp, h2])
  let N₃ : D ⋙ res ⋙ LR ⋙ ModuleCat.extendScalars.{u, u, u} φ ⋙ res ≅ D ⋙ res ⋙ LR :=
    NatIso.ofComponents (fun j => haveI := hunit (res.obj (D.obj j))
        (asIso (adj.unit.app (LR.obj (res.obj (D.obj j))))).symm)
      (fun {j j'} g => by
        have := hunit (res.obj (D.obj j))
        have := hunit (res.obj (D.obj j'))
        have h3 := adj.unit.naturality (LR.map (res.map (D.map g)))
        simp only [Functor.comp_map, Functor.id_map] at h3
        simp only [Functor.comp_map, Iso.symm_hom, asIso_inv]
        rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
        exact h3.symm)
  exact N₁ ≪≫ N₂ ≪≫ N₃

end Completion

end Stacks.LocalCohomology

end
