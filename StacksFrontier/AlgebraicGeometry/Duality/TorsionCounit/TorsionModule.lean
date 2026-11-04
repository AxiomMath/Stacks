module

public import StacksFrontier.AlgebraicGeometry.Duality.TorsionCounit.KInjectiveCriterion
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Algebra.Module.Matlis

/-!
# Derived torsion of a module that is already torsion

Let `I` be a finitely generated ideal of a Noetherian ring `A` and let `M` be an `I`-power-torsion
`A`-module. Then the counit `RΓ_I(M) ⟶ M` of the adjunction of Stacks Tag 0A6L is an isomorphism
in `D(A)`.

This is the first paragraph of the proof of Stacks Tag 0955, and it is where the Noetherian
hypothesis is used: by Stacks Tag 08XW the `I`-power-torsion submodule of an injective module is
again injective, so `M` embeds into an injective `A`-module which is itself `I`-power torsion, and
iterating gives an injective resolution of `M` by `I`-power-torsion modules. Such a resolution is
bounded below with injective terms, hence K-injective, and its termwise torsion subcomplex is
itself, so the criterion
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isIPowerTorsion_kInjective`
applies.

The two steps are isolated, since both are statements about the abelian category of
`I`-power-torsion modules rather than about complexes:

* that category has enough injectives — this needs only finite generation of `I`, and follows
  formally from the adjunction `ι ⊣ Γ_I` of Stacks Tag 09T5, because a right adjoint of an exact
  functor preserves injectives;
* over a Noetherian ring its injective objects are injective as `A`-modules — here the Matlis
  input enters, in the form of the injective envelope supported in a closed subset of the
  spectrum, and the injective object is recovered as a retract of such an envelope.

## Main results

* `Dualizing.TorsionCounit.enoughInjectives_powerTorsionModule` — the `I`-power-torsion modules
  have enough injectives.
* `Dualizing.TorsionCounit.injective_obj_of_injective_powerTorsionModule` — over a Noetherian
  ring, an injective `I`-power-torsion module is an injective `A`-module.
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_Q_mapHomologicalComplex` —
  **the counit `RΓ_I ⟶ id` is invertible at every object of `D(A)` represented by a
  bounded-below complex of `I`-power-torsion modules.**
* `Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_singleFunctor` — the counit
  `RΓ_I(M) ⟶ M` is an isomorphism for an `I`-power-torsion module `M` over a Noetherian ring.

## Implementation notes

No `@[stacks]` attribute appears here. The statement proved is the module case of part (1) of Tag
0955, not part (1), whose assertion is about every object of `D_{I^∞-torsion}(A)`; and the
covering set of Tag 0955 is its three enumerated assertions, none of which is proved.

## References

* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 08XW](https://stacks.math.columbia.edu/tag/08XW)
* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing.TorsionCounit

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- The inclusion of the `I`-power-torsion modules, spelled with the bare torsion predicate so
that it matches the target of `Dualizing.powerTorsionFunctor`, preserves monomorphisms. -/
private lemma preservesMonomorphisms_ι (hI' : I.FG) :
    Functor.PreservesMonomorphisms
      (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I)) :=
  inferInstanceAs (Functor.PreservesMonomorphisms
    (powerTorsionModuleProperty.{u, max u v} A I hI').ι)

/-- **The `I`-power-torsion modules have enough injectives.** Every `I`-power-torsion module
embeds into one which is an injective object of the category of `I`-power-torsion modules, namely
the torsion submodule of an injective envelope. This is formal: `Γ_I` is right adjoint to the
exact inclusion, so it carries injective `A`-modules to injective torsion modules. -/
theorem enoughInjectives_powerTorsionModule :
    EnoughInjectives (PowerTorsionModule.{u, max u v} A I hI) := by
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let : Functor.PreservesMonomorphisms
      (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I)) :=
    preservesMonomorphisms_ι.{u, v} A I hI
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨pres⟩ := EnoughInjectives.presentation (C := ModuleCat.{max u v} A)
    ((powerTorsionModuleProperty.{u, max u v} A I hI).ι.obj X)
  let adj := powerTorsionAdjunction.{u, v} A I
  let g := (adj.homEquiv X pres.J) pres.f
  have hfac : (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦
      IsIPowerTorsion A M I)).map g ≫ adj.counit.app pres.J = pres.f := by
    rw [← adj.homEquiv_counit X pres.J g]
    exact (adj.homEquiv X pres.J).symm_apply_apply pres.f
  have hmono : Mono g := by
    refine Functor.mono_of_mono_map
      (ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦ IsIPowerTorsion A M I)) ?_
    have : Mono ((ObjectProperty.ι (fun M : ModuleCat.{max u v} A ↦
        IsIPowerTorsion A M I)).map g ≫ adj.counit.app pres.J) := by
      rw [hfac]; exact pres.mono
    exact mono_of_mono _ (adj.counit.app pres.J)
  exact ⟨{ J := (powerTorsionFunctor.{u, v} A I).obj pres.J
           injective := Injective.injective_of_adjoint adj pres.J
           f := g
           mono := hmono }⟩

/-- **Over a Noetherian ring an injective `I`-power-torsion module is an injective `A`-module.**
The torsion module embeds into an injective `A`-module which is itself `I`-power torsion, and
being injective in the torsion category it is a retract of that envelope. -/
theorem injective_obj_of_injective_powerTorsionModule [IsNoetherianRing A]
    (Z : PowerTorsionModule.{u, max u v} A I hI) (hZ : Injective Z) :
    Injective ((powerTorsionModuleProperty.{u, max u v} A I hI).ι.obj Z) := by
  set T := PrimeSpectrum.zeroLocus (I : Set A) with hT
  have hTstab : StableUnderSpecialization T :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  have hZsupp : Stacks.LocalCohomology.supportModuleProperty.{u, max u v} A T Z.obj :=
    (isIPowerTorsion_iff_support_subset A Z.obj I hI).mp Z.property
  obtain ⟨J, hJsupp, i, hi, hJinj⟩ :=
    Stacks.LocalCohomology.exists_injective_supported_envelope.{u, v} T hTstab ⟨Z.obj, hZsupp⟩
  have hJtor : IsIPowerTorsion A J I :=
    (isIPowerTorsion_iff_support_subset A J I hI).mpr hJsupp
  -- read the envelope as a monomorphism of torsion modules
  let Jt : PowerTorsionModule.{u, max u v} A I hI := ⟨J, hJtor⟩
  let F := (powerTorsionModuleProperty.{u, max u v} A I hI).ι
  let i' : Z ⟶ Jt := ⟨i⟩
  have hFi : F.map i' = i := rfl
  have : Mono i' := Functor.mono_of_mono_map F (f := i') hi
  -- injectivity of `Z` splits it
  let r : Jt ⟶ Z := Injective.factorThru (𝟙 Z) i'
  have hr : i' ≫ r = 𝟙 Z := Injective.comp_factorThru (𝟙 Z) i'
  have hret : i ≫ F.map r = 𝟙 (F.obj Z) := by
    rw [← hFi, ← F.map_comp, hr, F.map_id]
  exact (⟨i, F.map r, hret⟩ : Retract (F.obj Z) (ModuleCat.of A J)).injective

/-- **Stacks 0955, part (1), on the bounded-below complexes of torsion modules.** Let `A` be a
Noetherian ring and `I ⊆ A` a finitely generated ideal. For every bounded-below complex `L` of
`I`-power-torsion `A`-modules, the counit `RΓ_I ⟶ id` is invertible at the object of `D(A)`
represented by `L`.

The proof is the first paragraph of the proof of Stacks Tag 0955: `L` has an injective resolution
in the abelian category of `I`-power-torsion modules, bounded below in the same degree, and its
terms are injective `A`-modules by the Matlis input, so it is a K-injective complex with
`I`-power-torsion terms. On such a complex the degreewise torsion inclusion is the identity. -/
theorem isIso_derivedPowerTorsionCounit_app_Q_mapHomologicalComplex [IsNoetherianRing A]
    (a : ℤ) (L : CochainComplex (PowerTorsionModule.{u, max u v} A I hI) ℤ)
    (hL : CochainComplex.IsGE L a) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app
      (DerivedCategory.Q.obj
        (((powerTorsionModuleProperty.{u, max u v} A I hI).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L))) := by
  let F := (powerTorsionModuleProperty.{u, max u v} A I hI).ι
  let : EnoughInjectives (PowerTorsionModule.{u, max u v} A I hI) :=
    enoughInjectives_powerTorsionModule.{u, v} A I hI
  obtain ⟨R, -, hGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a L
  set J : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex with hJ
  -- the terms of `J` are `I`-power torsion by construction
  have hterm : ∀ n : ℤ, IsIPowerTorsion A (J.X n) I := fun n ↦ (R.cocomplex.X n).property
  -- and they are injective `A`-modules, so `J` is K-injective
  have hinj : ∀ n : ℤ, Injective (J.X n) := fun n ↦
    injective_obj_of_injective_powerTorsionModule.{u, v} A I hI (R.cocomplex.X n) (R.injective n)
  have hJGE : CochainComplex.IsStrictlyGE J a :=
    (CochainComplex.isStrictlyGE_iff J a).mpr fun i hi =>
      F.map_isZero ((CochainComplex.isStrictlyGE_iff R.cocomplex a).mp hGE i hi)
  have hK : CochainComplex.IsKInjective J := CochainComplex.isKInjective_of_injective J a
  -- `J` represents the same object of `D(A)` as `L` does
  have : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  let e : DerivedCategory.Q.obj J ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    (asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι))).symm
  exact isIso_derivedPowerTorsionCounit_app_of_isIPowerTorsion_kInjective.{u, v} A I hI J hK
    hterm e

/-- **Stacks 0955, part (1), for a module.** Let `A` be a Noetherian ring, `I ⊆ A` a finitely
generated ideal and `M` an `I`-power-torsion `A`-module. Then the counit `RΓ_I(M) ⟶ M` is an
isomorphism in `D(A)`. -/
theorem isIso_derivedPowerTorsionCounit_app_singleFunctor [IsNoetherianRing A]
    (M : ModuleCat.{max u v} A) (hM : IsIPowerTorsion A M I) :
    IsIso ((derivedPowerTorsionCounit.{u, v} A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) := by
  let F := (powerTorsionModuleProperty.{u, max u v} A I hI).ι
  let Mt : PowerTorsionModule.{u, max u v} A I hI := ⟨M, hM⟩
  let L : CochainComplex (PowerTorsionModule.{u, max u v} A I hI) ℤ :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj Mt
  have hbase := isIso_derivedPowerTorsionCounit_app_Q_mapHomologicalComplex.{u, v} A I hI 0 L
    inferInstance
  let e₂ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅
      (HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) 0).obj M :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app Mt
  exact isIso_derivedPowerTorsionCounit_app_of_iso.{u, v} A I hI
    (DerivedCategory.Q.mapIso e₂ ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).app M).symm) hbase

end Dualizing.TorsionCounit

end
