module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Flat descent of local cohomology with torsion support

Let `A → B` be a flat map of Noetherian rings, `T ⊆ Spec A` a specialization-stable subset and
`T' ⊆ Spec B` its preimage. Suppose `T ⊆ V(J)` for an ideal `J` of `A` such that
`A/J → B/JB` is bijective. Then local cohomology with support in `T` is unchanged by base change
to `B`:

`Hⁱ_T(K) ≅ Hⁱ_{T'}(K ⊗ᴸ_A B)` as `A`-modules, naturally in `K ∈ D(A)`,

and in particular `Hⁱ_T(N) ≅ Hⁱ_{T'}(N ⊗_A B)` naturally in the `A`-module `N`. This is the
argument of the proof of [Stacks, Tag 0EFR]: by flat base change ([Stacks, Tag 0EF5])
`Hⁱ_T(K) ⊗_A B = Hⁱ_{T'}(K ⊗ᴸ_A B)`, and `Hⁱ_T(K)` is `J`-power torsion, so it does not change
under `- ⊗_A B` ([Stacks, Tag 05EC]). The typical case is `B` the `J`-adic completion of `A`, or
the `I`-adic completion for an ideal `I` with `T ⊆ V(I)`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyFlatBaseChangeIso` — flat base change on cohomology,
  `Hⁱ_T(K) ⊗_A B ≅ Hⁱ_{T'}(K ⊗ᴸ_A B)`, natural in `K ∈ D(A)`.
* `Stacks.LocalCohomology.localCohomologyTorsionDescentIso` — the descent isomorphism
  `Hⁱ_T(K) ≅ Hⁱ_{T'}(K ⊗ᴸ_A B)` of `A`-modules, natural in `K ∈ D(A)`.
* `Stacks.LocalCohomology.localCohomologyModuleTorsionDescentIso` — the same for modules,
  `Hⁱ_T(N) ≅ Hⁱ_{T'}(B ⊗_A N)`, natural in `N`.

## Main results

* `Stacks.LocalCohomology.bijective_extendRestrictScalarsAdj_unit_app` — for a flat `B` with
  `A/J ≅ B/JB`, the unit `X → B ⊗_A X` is bijective on every `J`-power torsion module.

## Implementation notes

The descent isomorphism is the composite of the unit `X → B ⊗_A X` at `X = Hⁱ_T(K)` with the
restriction of scalars of the flat base change isomorphism; it is not asserted here to agree with
the map induced on `Hⁱ_T` by `K → K ⊗ᴸ_A B`. The statements are on cohomology modules, and on
derived objects only through their cohomology.

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Stacks Project, Tag 05EC.** For a flat `A`-algebra `B` such that `A/J → B/JB` is bijective,
the unit `X → B ⊗_A X` of extension of scalars is bijective on every `J`-power torsion module. -/
theorem bijective_extendRestrictScalarsAdj_unit_app (J : Ideal A) (hflat : Module.Flat A B)
    (hq : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (X : ModuleCat.{u} A) (hX : IsIPowerTorsion A X J) :
    Function.Bijective
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)).unit.app X) := by
  have hunit :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, u, u} A B J hflat).2 hq X hX
  have h := (IPowerTorsion.tensorModuleCatEquiv.{u, u, u} (S := B) X).bijective.comp
    (IPowerTorsion.one_tmul_bijective hunit)
  have heq (m : X) :
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)).unit.app X m =
        IPowerTorsion.tensorModuleCatEquiv.{u, u, u} (S := B) X ((1 : B) ⊗ₜ[A] m) := by
    rw [IPowerTorsion.tensorModuleCatEquiv_tmul]
    rfl
  exact funext heq ▸ h

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Flat base change of local cohomology, on cohomology** ([Stacks, Tag 0EF5]). For a flat map
`A → B` of Noetherian rings, `Hⁱ_T(K) ⊗_A B ≅ Hⁱ_{T'}(K ⊗ᴸ_A B)` naturally in `K ∈ D(A)`, where
`T'` is the preimage of `T`. -/
def localCohomologyFlatBaseChangeIso (hflat : Module.Flat A B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (i : ℤ) :
    derivedSectionsWithSupportIn.{u, u} A T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A B) ≅
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor ⋙
        derivedSectionsWithSupportIn.{u, u} B ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' T) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} B) i :=
  have hf : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr hflat
  letI := preservesFiniteLimits_extendScalars_of_flat.{u, u, u} (algebraMap A B) hf
  have : ∀ K, IsIso ((derivedSectionsWithSupportInBaseChangeMap.{u, u, u}
      (algebraMap A B) T).app K) :=
    fun K => isIso_derivedSectionsWithSupportInBaseChangeMap.{u, u, u} (algebraMap A B) T hT K
  have : IsIso (derivedSectionsWithSupportInBaseChangeMap.{u, u, u} (algebraMap A B) T) :=
    NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerLeft (derivedSectionsWithSupportIn.{u, u} A T)
      (derivedExtensionScalarsHomologyNatIso.{u, u, u} (algebraMap A B) i).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (derivedSectionsWithSupportInBaseChangeMap.{u, u, u} (algebraMap A B) T))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i)

omit [IsNoetherianRing B] in
/-- If `T ⊆ V(J)`, every local cohomology module with support in `T` is `J`-power torsion. -/
theorem isIPowerTorsion_localCohomologyWithSupportIn {T : Set (PrimeSpectrum A)} (J : Ideal A)
    (hTJ : T ⊆ PrimeSpectrum.zeroLocus (J : Set A)) (K : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ) : IsIPowerTorsion A (localCohomologyWithSupportIn.{u, u} A T K i) J :=
  isIPowerTorsion_of_support_subset (Ideal.fg_of_isNoetherianRing J)
    ((support_localCohomologyWithSupportIn_subset.{u, u} T K i).trans hTJ)

/-- **Local cohomology with torsion support descends along a flat map that is an isomorphism
modulo the torsion ideal** (the argument of [Stacks, Tag 0EFR]). Let `A → B` be a flat map of
Noetherian rings, `T ⊆ Spec A` specialization-stable, `T'` its preimage, and `J` an ideal with
`T ⊆ V(J)` and `A/J ≅ B/JB`. Then `Hⁱ_T(K) ≅ Hⁱ_{T'}(K ⊗ᴸ_A B)` as `A`-modules, naturally in
`K ∈ D(A)`: the unit `Hⁱ_T(K) → Hⁱ_T(K) ⊗_A B` is bijective because `Hⁱ_T(K)` is `J`-power torsion
([Stacks, Tag 05EC]), followed by flat base change ([Stacks, Tag 0EF5]). -/
def localCohomologyTorsionDescentIso (hflat : Module.Flat A B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (J : Ideal A)
    (hTJ : T ⊆ PrimeSpectrum.zeroLocus (J : Set A))
    (hq : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (i : ℤ) :
    derivedSectionsWithSupportIn.{u, u} A T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ≅
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor ⋙
        derivedSectionsWithSupportIn.{u, u} B ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' T) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
            ModuleCat.restrictScalars.{u} (algebraMap A B) :=
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)
  let F := derivedSectionsWithSupportIn.{u, u} A T ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  have : ∀ K, IsIso ((Functor.whiskerLeft F adj.unit).app K) := fun K =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_extendRestrictScalarsAdj_unit_app J hflat hq _
        (isIPowerTorsion_localCohomologyWithSupportIn J hTJ K i))
  have : IsIso (Functor.whiskerLeft F adj.unit) := NatIso.isIso_of_isIso_app _
  (Functor.rightUnitor F).symm ≪≫ asIso (Functor.whiskerLeft F adj.unit) ≪≫
    Functor.isoWhiskerRight (localCohomologyFlatBaseChangeIso hflat T hT i)
      (ModuleCat.restrictScalars.{u} (algebraMap A B))

/-- **The module form of the descent.** Under the hypotheses of
`localCohomologyTorsionDescentIso`, `Hⁱ_T(N) ≅ Hⁱ_{T'}(B ⊗_A N)` as `A`-modules, naturally in the
`A`-module `N`: for flat `B`, derived extension of scalars of a module in degree zero is its
extension of scalars in degree zero. -/
def localCohomologyModuleTorsionDescentIso (hflat : Module.Flat A B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (J : Ideal A)
    (hTJ : T ⊆ PrimeSpectrum.zeroLocus (J : Set A))
    (hq : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (i : ℤ) :
    localCohomologyWithSupportInModuleFunctor.{u, u} A T i ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A B) ⋙
        localCohomologyWithSupportInModuleFunctor.{u, u} B
          ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' T) i ⋙
          ModuleCat.restrictScalars.{u} (algebraMap A B) :=
  have hf : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr hflat
  letI := preservesFiniteLimits_extendScalars_of_flat.{u, u, u} (algebraMap A B) hf
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)).isLeftAdjoint
  letI : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  let eS : DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor ≅
      E ⋙ DerivedCategory.singleFunctor (ModuleCat.{u} B) 0 :=
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
        (derivedExtensionScalarsIsoMapDerivedCategory.{u, u, u} (algebraMap A B)) ≪≫
      E.mapDerivedCategorySingleFunctor 0
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (localCohomologyTorsionDescentIso hflat T hT J hTJ hq i) ≪≫
    Functor.isoWhiskerRight eS
      (derivedSectionsWithSupportIn.{u, u} B ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' T) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
          ModuleCat.restrictScalars.{u} (algebraMap A B))

end Stacks.LocalCohomology

end
