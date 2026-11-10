module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.ExtIdealPowerTower
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtStableImage

/-!
# The stable-image transport of local duality at a prime, read on the global Ext modules

`Dualizing.LocalDuality.ker_le_ker_localCohomologyModuleFunctor_iff_range_le_range` is the
stable-image transport over a Noetherian **local** ring with a normalized dualizing complex. Here
it is read at an arbitrary prime `𝔮` of a Noetherian ring `A` with a dualizing complex `ω`, with
the Ext side transferred from `A_𝔮` to the localization at `𝔮` of the **finite** `A`-modules
`H^j(RHom_A(−, ω))`. The normalized dualizing complex of `A_𝔮` is `ω_𝔮⟦-δ(𝔮)⟧`, so the Ext
degree paired with `H^i_𝔮` is `-δ(𝔮) - i`.

## Main results

* `Stacks.Algebraization.forall_exists_eq_iff_of_comm` — a containment of images transfers across
  two commuting squares whose vertical maps are surjective, surjective and injective.
* `Stacks.Algebraization.localized_ker_le_ker_localCohomology_iff_exists_localized_ext` — the
  transport at a prime: the containment of kernels on local cohomology over `A_𝔮` is the
  containment of images of the localizations at `𝔮` of the global Ext modules.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **A containment of images transfers across two commuting squares.** If `eX` is injective and
`eY`, `eZ` are surjective, and the two squares `eX ∘ a = a' ∘ eY` and `eX ∘ c = c' ∘ eZ` commute,
then every value of `a` is a value of `c` exactly when every value of `a'` is a value of `c'`.
-/
theorem forall_exists_eq_iff_of_comm {X Y Z X' Y' Z' : Type*}
    (a : Y → X) (c : Z → X) (a' : Y' → X') (c' : Z' → X')
    (eX : X → X') (eY : Y → Y') (eZ : Z → Z')
    (hX : Function.Injective eX) (hY : Function.Surjective eY) (hZ : Function.Surjective eZ)
    (ha : ∀ y, eX (a y) = a' (eY y)) (hc : ∀ z, eX (c z) = c' (eZ z)) :
    (∀ y, ∃ z, a y = c z) ↔ ∀ y', ∃ z', a' y' = c' z' := by
  constructor
  · intro h y'
    obtain ⟨y, rfl⟩ := hY y'
    obtain ⟨z, hz⟩ := h y
    exact ⟨eZ z, ((ha y).symm.trans (congrArg eX hz)).trans (hc z)⟩
  · intro h y
    obtain ⟨z', hz'⟩ := h (eY y)
    obtain ⟨z, rfl⟩ := hZ z'
    exact ⟨z, hX (((ha y).trans hz').trans (hc z).symm)⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The localization of an injective map of modules is injective. -/
theorem injective_localizedModuleFunctor_map (S : Submonoid A) {X Y : ModuleCat.{u} A}
    (γ : X ⟶ Y) (hγ : Function.Injective γ.hom) :
    Function.Injective ((ModuleCat.localizedModuleFunctor.{u} S).map γ).hom :=
  IsLocalizedModule.map_injective S (X.localizedModuleMkLinearMap S)
    (Y.localizedModuleMkLinearMap S) γ.hom hγ

/-- The short complex `X_S → Y_S → Y_S / im(γ_S)` formed by the localization of `γ` at `S` and
the quotient by its image. -/
def localizedShortComplex (S : Submonoid A) {X Y : ModuleCat.{u} A} (γ : X ⟶ Y) :
    ShortComplex (ModuleCat.{u} (Localization S)) :=
  ShortComplex.mk ((ModuleCat.localizedModuleFunctor.{u} S).map γ)
    (ModuleCat.ofHom (Submodule.mkQ
      (LinearMap.range ((ModuleCat.localizedModuleFunctor.{u} S).map γ).hom)))
    (ModuleCat.hom_ext (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩))

omit [IsNoetherianRing A] in
/-- The sequence of `Stacks.Algebraization.localizedShortComplex` is short exact when the
localized map is injective. -/
theorem localizedShortComplex_shortExact (S : Submonoid A) {X Y : ModuleCat.{u} A} (γ : X ⟶ Y)
    (hγ : Function.Injective ((ModuleCat.localizedModuleFunctor.{u} S).map γ).hom) :
    (localizedShortComplex.{u} S γ).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  mono_f := (ModuleCat.mono_iff_injective _).2 hγ
  epi_g := (ModuleCat.epi_iff_surjective _).2
    (Submodule.mkQ_surjective _)

/-- **The stable-image transport of local duality at an arbitrary prime.** Let `A` be a Noetherian
ring with a dualizing complex `ω`, let `𝔮` be a prime, let `γ : X ⟶ Y` be a map of finite
`A`-modules whose localization at `𝔮` is injective, and let `α : X ⟶ N` be any map into a finite
`A`-module. Then

`ker H^i_{𝔮A_𝔮}(γ_𝔮) ⊆ ker H^i_{𝔮A_𝔮}(α_𝔮)`

holds exactly when every value of the localization at `𝔮` of the map induced by `α` on
`H^{-δ(𝔮)-i}(RHom_A(−, ω))` is a value of the one induced by `γ`. -/
theorem localized_ker_le_ker_localCohomology_iff_exists_localized_ext
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (q : PrimeSpectrum A) (i : ℤ)
    {X Y N : ModuleCat.{u} A} [Module.Finite A X] [Module.Finite A Y] [Module.Finite A N]
    (γ : X ⟶ Y) (hγ : Function.Injective ((ModuleCat.localizedModuleFunctor.{u}
      q.asIdeal.primeCompl).map γ).hom) (α : X ⟶ N) :
    letI : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
      IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
    (LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor
            (Localization q.asIdeal.primeCompl) i).map
          ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map γ)).hom ≤
        LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor
            (Localization q.asIdeal.primeCompl) i).map
          ((ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl).map α)).hom) ↔
      ∀ y, ∃ z, ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
            q.asIdeal.primeCompl).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
              (-Dualizing.dualizingDimension.{u, u} ω q - i)).map
            ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).map
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map α).op))).hom y =
        ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
            q.asIdeal.primeCompl).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
              (-Dualizing.dualizingDimension.{u, u} ω q - i)).map
            ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).map
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map γ).op))).hom z := by
  let : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  classical
  set Bq := Localization q.asIdeal.primeCompl with hBq
  set Lq := ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl with hLq
  set d := Dualizing.dualizingDimension.{u, u} ω q with hd
  set j := -d - i with hj
  have hfinloc : ∀ Z : ModuleCat.{u} A, Module.Finite A Z → Module.Finite Bq (Lq.obj Z) := by
    intro Z hZ
    change Module.Finite Bq (Z.localizedModule q.asIdeal.primeCompl)
    exact Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl
      (Z.localizedModuleMkLinearMap q.asIdeal.primeCompl)
  have := hfinloc X inferInstance
  have := hfinloc Y inferInstance
  have := hfinloc N inferInstance
  set S := localizedShortComplex.{u} q.asIdeal.primeCompl γ with hS
  have hSe := localizedShortComplex_shortExact.{u} q.asIdeal.primeCompl γ hγ
  have : Module.Finite Bq S.X₃ := by
    change Module.Finite Bq (Lq.obj Y ⧸ LinearMap.range (Lq.map γ).hom)
    exact Module.Finite.quotient Bq _
  have hωnorm :=
    Dualizing.isNormalizedDualizingComplex_localizedModuleFunctor_shift_dualizingDimension A ω hω q
  have hshift := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} Bq)) (-d) (-i) j
    (by rw [hj]; ring)).app (Lq.mapDerivedCategory.obj ω)
  have hmain := Dualizing.LocalDuality.ker_le_ker_localCohomologyModuleFunctor_iff_range_le_range
    Bq ((Lq.mapDerivedCategory.obj ω)⟦-d⟧) hωnorm i (Lq.mapDerivedCategory.obj ω) j hshift
    hSe (N := Lq.obj N) (Lq.map α)
  refine hmain.trans ?_
  obtain ⟨⟨b, hb⟩, -⟩ := hω.bounded
  have hωge : ∃ c : ℤ, ω.IsGE c := ⟨b, hb⟩
  have hnatα := Dualizing.localizedDerivedHomHomologyIso_naturality.{u}
    q.asIdeal.primeCompl ω hωge j α
  have hnatγ := Dualizing.localizedDerivedHomHomologyIso_naturality.{u}
    q.asIdeal.primeCompl ω hωge j γ
  refine Iff.trans ?_ (forall_exists_eq_iff_of_comm
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} q.asIdeal.primeCompl).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map α).op))).hom
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} q.asIdeal.primeCompl).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map γ).op))).hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Bq) j).map
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} Bq
            (Lq.mapDerivedCategory.obj ω)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Bq) 0).map (Lq.map α)).op)).hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Bq) j).map
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} Bq
            (Lq.mapDerivedCategory.obj ω)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Bq) 0).map (Lq.map γ)).op)).hom
      (Dualizing.localizedDerivedHomHomologyIso.{u} q.asIdeal.primeCompl ω hωge j X).hom.hom
      (Dualizing.localizedDerivedHomHomologyIso.{u} q.asIdeal.primeCompl ω hωge j N).hom.hom
      (Dualizing.localizedDerivedHomHomologyIso.{u} q.asIdeal.primeCompl ω hωge j Y).hom.hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      (fun y => ConcreteCategory.congr_hom hnatα y)
      (fun z => ConcreteCategory.congr_hom hnatγ z)).symm
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (LinearMap.mem_range_self _ y)
    exact ⟨z, hz.symm⟩
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨z, hz⟩ := h y
    exact ⟨z, hz.symm⟩

end Stacks.Algebraization

end
