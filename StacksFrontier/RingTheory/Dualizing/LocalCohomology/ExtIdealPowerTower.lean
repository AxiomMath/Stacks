module

public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
public import StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero
public import StacksFrontier.RingTheory.LocalCohomology.UniformVanishingSpread

/-!
# The Ext modules of the ideal-power filtration as a direct system of finite modules

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `M` a finite `A`-module and `ω` a dualizing
complex. The uniformity paragraph in the proof of [Stacks, Tag 0EFX] runs on the modules

`E(n, j) = Ext^j_A(IⁿM, ω) = H^j(RHom_A(IⁿM, ω))`

and uses two of their properties: they are **finite** `A`-modules, and they form a **direct
system** in `n`, the transition `E(m, j) → E(k, j)` for `m ≤ k` being precomposition with the
inclusion `IᵏM ⊆ IᵐM`. This module assembles that system — `Dualizing.extIdealPowerTower` — out
of `Stacks.LocalCohomology.idealPowerTower` and `Dualizing.dualizingDerivedHomFunctor`, records
the finiteness from [Stacks, Tag 0A7C], and proves the one comparison the paragraph needs at a
prime `𝔮`: the vanishing of the localization at `𝔮` of a transition map of this system is the
same thing as the vanishing of the precomposition map on `Hom_{D(A_𝔮)}(−, ω_𝔮⟦j⟧)`, which is
the side on which local duality is available.

## Main definitions

* `Dualizing.extIdealPowerTower` — the direct system `n ↦ H^j(RHom_A(IⁿM, ω))`.

## Main results

* `Stacks.LocalCohomology.finite_idealPowerTower_obj` — `IⁿM` is a finite module.
* `Dualizing.finite_extIdealPowerTower_obj` — each term of the system is a finite `A`-module,
  by [Stacks, Tag 0A7C].
* `Dualizing.isNormalizedDualizingComplex_localizedModuleFunctor_shift_dualizingDimension` —
  the localization of `ω` at `𝔮`, shifted by `-δ(𝔮)`, is a normalized dualizing complex for
  `A_𝔮`.
* `Dualizing.localizedModuleFunctor_map_eq_zero_iff` — the two localization functors detect the
  same vanishing.
* `Dualizing.localized_extIdealPowerTower_map_eq_zero_iff` — the localization at `𝔮` of a
  transition map of the Ext system vanishes exactly when precomposition with the localized
  inclusion `(IᵏM)_𝔮 ⊆ (IᵐM)_𝔮` kills every morphism `single((IᵐM)_𝔮) ⟶ ω_𝔮⟦j⟧`.

## Implementation notes

The comparison at `𝔮` composes three identifications:

* `Dualizing.extIntoOmegaAtLinearEquiv` with its naturality, over `A_𝔮`, turning the
  precomposition maps on `Hom_{D(A_𝔮)}(single(−), ω_𝔮⟦j⟧)` into the maps on
  `H^j(RHom_{A_𝔮}(−, ω_𝔮))`;
* `Dualizing.localizedDerivedHomHomologyIso` with its naturality, identifying the localization
  at `𝔮` of `H^j(RHom_A(−, ω))` with `H^j(RHom_{A_𝔮}(−_𝔮, ω_𝔮))` compatibly with every map of
  finite modules;
* `Stacks.LocalCohomology.isLocalizedModule_map_eq_zero_iff`, which reads the vanishing of a
  localized map off any model of the localization and so compares the two localization functors
  the previous two items are stated in — `ModuleCat.localizedModuleFunctor`, whose carrier is a
  `Shrink`, and `CochainComplex.DerivedTensor.localizedModuleFunctor`, whose carrier is the
  literal `LocalizedModule`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **A term of the ideal-power tower is a finite module.** `IⁿM` is a submodule of the finite
module `M`, which is Noetherian over the Noetherian ring `A`, so it is finitely generated. -/
theorem finite_idealPowerTower_obj {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (n : ℕᵒᵖ) :
    Module.Finite A ((idealPowerTower.{u, u} I M).obj n) := by
  have : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  change Module.Finite A ↥(I ^ n.unop • (⊤ : Submodule A M))
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

/-- **The vanishing of a localized map in the `ModuleCat` localization functor**, read
elementwise. -/
theorem localizedModuleFunctor_map_eq_zero_iff_forall {A : Type u} [CommRing A]
    (S : Submonoid A) {X Y : ModuleCat.{u} A} (ψ : X ⟶ Y) :
    (ModuleCat.localizedModuleFunctor.{u} S).map ψ = 0 ↔
      ∀ x : X, ∃ r ∈ S, r • ψ.hom x = 0 := by
  have key : ∀ z : (X.localizedModule S),
      ((ModuleCat.localizedModuleFunctor.{u} S).map ψ).hom z =
        IsLocalizedModule.map S (X.localizedModuleMkLinearMap S)
          (Y.localizedModuleMkLinearMap S) ψ.hom z := fun _ => rfl
  rw [← isLocalizedModule_map_eq_zero_iff S (X.localizedModuleMkLinearMap S)
    (Y.localizedModuleMkLinearMap S) ψ.hom]
  refine ⟨fun h => LinearMap.ext fun z => ?_,
    fun h => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
  · rw [← key z, h]
    rfl
  · rw [key z, h]
    rfl

/-- **The vanishing of a localized map in the `LocalizedModule`-carrier localization functor**,
read elementwise. -/
theorem derivedTensorLocalizedModuleFunctor_map_eq_zero_iff_forall {A : Type u} [CommRing A]
    (S : Submonoid A) {X Y : ModuleCat.{u} A} (ψ : X ⟶ Y) :
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map ψ = 0 ↔
      ∀ x : X, ∃ r ∈ S, r • ψ.hom x = 0 := by
  have key : ∀ z : LocalizedModule S X,
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map ψ).hom z =
        IsLocalizedModule.map S (LocalizedModule.mkLinearMap S X)
          (LocalizedModule.mkLinearMap S Y) ψ.hom z := fun _ => rfl
  rw [← isLocalizedModule_map_eq_zero_iff S (LocalizedModule.mkLinearMap S X)
    (LocalizedModule.mkLinearMap S Y) ψ.hom]
  refine ⟨fun h => LinearMap.ext fun z => ?_,
    fun h => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
  · rw [← key z, h]
    rfl
  · rw [key z, h]
    rfl

end Stacks.LocalCohomology

namespace Dualizing

/-- **The two localization functors detect the same vanishing.** A map of `A`-modules dies after
localization at `S` in the `Shrink`-carrier model exactly when it dies in the
`LocalizedModule`-carrier model: by
`Stacks.LocalCohomology.isLocalizedModule_map_eq_zero_iff` both are the elementwise condition
that every value of the map be annihilated by an element of `S`. -/
theorem localizedModuleFunctor_map_eq_zero_iff {A : Type u} [CommRing A]
    (S : Submonoid A) {X Y : ModuleCat.{u} A} (ψ : X ⟶ Y) :
    (ModuleCat.localizedModuleFunctor.{u} S).map ψ = 0 ↔
      (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map ψ = 0 :=
  (Stacks.LocalCohomology.localizedModuleFunctor_map_eq_zero_iff_forall S ψ).trans
    (Stacks.LocalCohomology.derivedTensorLocalizedModuleFunctor_map_eq_zero_iff_forall S ψ).symm

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- **The Ext modules of the ideal-power filtration as a direct system.** The functor
`n ↦ H^j(RHom_A(IⁿM, ω))` on `ℕ`, whose transition map from `m` to `k ≥ m` is precomposition
with the inclusion `IᵏM ⊆ IᵐM`. These are the modules `E(n, j)` of the proof of
[Stacks, Tag 0EFX]. -/
def extIdealPowerTower (I : Ideal A) (M : ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (j : ℤ) : ℕ ⥤ ModuleCat.{u} A :=
  (Stacks.LocalCohomology.idealPowerTower.{u, u} I M).rightOp ⋙
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
      dualizingDerivedHomFunctor.{u, u} A ω ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) j

omit [IsNoetherianRing A] in
/-- The transition map of `Dualizing.extIdealPowerTower`, written out. -/
theorem extIdealPowerTower_map (I : Ideal A) (M : ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (j : ℤ) {m k : ℕ} (h : m ≤ k) :
    (extIdealPowerTower A I M ω j).map (homOfLE h) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((dualizingDerivedHomFunctor.{u, u} A ω).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
            ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).map
              (homOfLE h).op)).op) :=
  rfl

/-- **Each term of the Ext system is a finite module**, by [Stacks, Tag 0A7C]: `IⁿM` is finite
and `RHom_A(−, ω)` into a dualizing complex preserves finiteness of cohomology. -/
theorem finite_extIdealPowerTower_obj (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) (j : ℤ) (n : ℕ) :
    Module.Finite A ((extIdealPowerTower A I M ω j).obj n) := by
  have := Stacks.LocalCohomology.finite_idealPowerTower_obj I M (op n)
  exact dualizingDerivedHom_finiteCohomology.{u, u} A ω hω
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).obj (op n)))
    (fun i => finite_homology_single _ i) j

/-- **The localization of a dualizing complex at a prime, shifted by minus the value of the
dimension function, is a normalized dualizing complex**, in the spelling
`Dualizing.localizedDerivedHomHomologyIso` produces its target in. This is
`Dualizing.dualizingDimension_spec` carried across
`Dualizing.pseudoCoherenceLocalizationDerivedObjIso`, which compares the derived extension of
scalars with the localized-module functor. -/
theorem isNormalizedDualizingComplex_localizedModuleFunctor_shift_dualizingDimension
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω)
    (q : PrimeSpectrum A) :
    letI : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
      IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
    IsNormalizedDualizingComplex.{u, u}
      (((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).mapDerivedCategory.obj ω)⟦
        -dualizingDimension.{u, u} ω q⟧) := by
  let : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  exact (isNormalizedDualizingComplex_congr.{u, u}
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (Localization q.asIdeal.primeCompl)))
      (-dualizingDimension.{u, u} ω q)).mapIso
      (pseudoCoherenceLocalizationDerivedObjIso.{u, u} q.asIdeal ω))).mp
    (dualizingDimension_spec.{u, u} ω hω q)

/-- **Precomposition on `Hom_{D(B)}(single(−), ω⟦j⟧)` read on cohomology.** The map induced on
`H^j(RHom_B(−, ω))` by a map `f : X ⟶ Y` of `B`-modules vanishes exactly when precomposition
with `single(f)` kills every morphism `single(Y) ⟶ ω⟦j⟧`. This is
`Dualizing.extIntoOmegaAtLinearEquiv` with its naturality, read as an equivalence of
vanishings. -/
theorem homologyMap_dualizingDerivedHom_eq_zero_iff (B : Type u) [CommRing B]
    (ω : DerivedCategory (ModuleCat.{u} B)) (j : ℤ) {X Y : ModuleCat.{u} B} (f : X ⟶ Y) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
        ((dualizingDerivedHomFunctor.{u, u} B ω).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map f).op) = 0 ↔
      ∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj Y ⟶
          (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) j).obj ω,
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map f ≫ u = 0 := by
  refine ⟨fun hz u => ?_, fun hz => ?_⟩
  · refine (extIntoOmegaAtLinearEquiv.{u, u} B ω j X).injective ?_
    rw [extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j f u, map_zero]
    exact congrArg (fun w => ModuleCat.Hom.hom w
      (extIntoOmegaAtLinearEquiv.{u, u} B ω j Y u)) hz
  · refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    obtain ⟨u, rfl⟩ := (extIntoOmegaAtLinearEquiv.{u, u} B ω j Y).surjective y
    rw [← extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j f u, hz, map_zero]
    rfl

/-- **The localization at `T` of the map induced on `H^j(RHom_A(−, ω))` vanishes exactly when the
corresponding map over `T⁻¹A` does.** This is
`Dualizing.localizedDerivedHomHomologyIso_naturality` read as an equivalence of vanishings: the
comparison is an isomorphism, so the two maps vanish together, and `ModuleCat.restrictScalars`
is faithful, so reading the localized side over `A` loses nothing.

The two localization functors appearing on the left — `ModuleCat.localizedModuleFunctor`, whose
carrier is a `Shrink`, and the `LocalizedModule`-carrier functor the comparison is stated in —
are interchanged by `Dualizing.localizedModuleFunctor_map_eq_zero_iff`. -/
theorem localized_homologyMap_dualizingDerivedHom_eq_zero_iff (T : Submonoid A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hωge : ∃ b : ℤ, ω.IsGE b) (j : ℤ)
    {X Y : ModuleCat.{u} A} [Module.Finite A X] [Module.Finite A Y] (f : X ⟶ Y) :
    (ModuleCat.localizedModuleFunctor.{u} T).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
          ((dualizingDerivedHomFunctor.{u, u} A ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op)) = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) j).map
        ((dualizingDerivedHomFunctor.{u, u} (Localization T)
            ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj ω)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
            ((ModuleCat.localizedModuleFunctor.{u} T).map f)).op) = 0 := by
  rw [localizedModuleFunctor_map_eq_zero_iff]
  have hnat := localizedDerivedHomHomologyIso_naturality.{u} T ω hωge j f
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · refine (Functor.map_eq_zero_iff
      (ModuleCat.restrictScalars (algebraMap A (Localization T)))).1 ?_
    refine (cancel_epi (localizedDerivedHomHomologyIso.{u} T ω hωge j Y).hom).1 ?_
    rw [← hnat, hz, Limits.zero_comp, Limits.comp_zero]
  · refine (cancel_mono (localizedDerivedHomHomologyIso.{u} T ω hωge j X).hom).1 ?_
    rw [hnat, hz]
    simp

/-- **The localized transition maps of the Ext system.** For a prime `𝔮` of `A`, the
localization at `𝔮` of the transition map

`E(m, j) = H^j(RHom_A(IᵐM, ω)) ⟶ H^j(RHom_A(IᵏM, ω)) = E(k, j)`

vanishes exactly when precomposition with the localized inclusion `(IᵏM)_𝔮 ⊆ (IᵐM)_𝔮` kills
every morphism `single((IᵐM)_𝔮) ⟶ ω_𝔮⟦j⟧` in `D(A_𝔮)`. -/
theorem localized_extIdealPowerTower_map_eq_zero_iff
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hωge : ∃ b : ℤ, ω.IsGE b) (j : ℤ)
    (q : PrimeSpectrum A) {m k : ℕ} (h : m ≤ k) :
    (extIdealPowerTower A I M ω j ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map (homOfLE h) = 0 ↔
      ∀ u : (DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization q.asIdeal.primeCompl)) 0).obj
            ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).obj
              ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).obj (op m))) ⟶
          (shiftFunctor (DerivedCategory (ModuleCat.{u} (Localization q.asIdeal.primeCompl)))
            j).obj ((ModuleCat.localizedModuleFunctor.{u}
              q.asIdeal.primeCompl).mapDerivedCategory.obj ω),
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization q.asIdeal.primeCompl)) 0).map
            ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map
              ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).map (homOfLE h).op)) ≫ u
          = 0 := by
  have := Stacks.LocalCohomology.finite_idealPowerTower_obj I M (op m)
  have := Stacks.LocalCohomology.finite_idealPowerTower_obj I M (op k)
  rw [Functor.comp_map, extIdealPowerTower_map]
  exact (localized_homologyMap_dualizingDerivedHom_eq_zero_iff A q.asIdeal.primeCompl ω hωge j
      ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).map (homOfLE h).op)).trans
    (homologyMap_dualizingDerivedHom_eq_zero_iff (Localization q.asIdeal.primeCompl)
      ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).mapDerivedCategory.obj ω) j
      ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map
        ((Stacks.LocalCohomology.idealPowerTower.{u, u} I M).map (homOfLE h).op)))

end Dualizing

end
