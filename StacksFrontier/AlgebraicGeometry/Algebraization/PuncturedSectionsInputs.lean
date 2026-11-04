module

public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport

import all StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible

/-!
# The global sections of an invertible module on a punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and let `U` be its punctured spectrum. The global
sections `Γ(U, ℱ)` of a module on `U` are an `A`-module through
`Stacks.Algebraization.puncturedScalars`, and this file collects what is known about that module
when `ℱ` is invertible: it is the module of global sections on `Spec A` of the direct image of
`ℱ`, hence finite of depth at least two over `A` as soon as `depth(A) ≥ 2`; every nonzerodivisor
of `A` acts regularly on it; and for a coherent triple `(ℱ, ℱ₀, α)` the kernel of the canonical
map on global sections

`Γ(U, ℱ) ⟶ Γ(U₀, ℱ₀|_{U₀})`

is exactly `f Γ(U, ℱ)`.

## Main definitions

* `Stacks.Algebraization.puncturedSectionsPushforwardEquiv`: the global sections on the punctured
  spectrum are the global sections on `Spec A` of the direct image, as `A`-modules.

## Main results

* `Stacks.Algebraization.finite_puncturedSections_of_isInvertible` and
  `Stacks.Algebraization.two_le_depth_puncturedSections_of_isInvertible`: for an invertible module
  on the punctured spectrum of a Noetherian local ring of depth at least two, the global sections
  are a finite `A`-module of depth at least two.
* `Stacks.Algebraization.isSMulRegular_puncturedSections`: a nonzerodivisor of `A` acts regularly
  on those global sections.
* `Stacks.Algebraization.ker_globalSectionsMap`: the kernel of the canonical map on global
  sections of an invertible coherent triple over a Noetherian local ring of depth at least three
  is `f Γ(U, ℱ)`.

## Implementation notes

The two `A`-modules of the first item have the same underlying abelian group, the open immersion
pulling `⊤` back to `⊤`; what the comparison says is that the two actions of `A` agree, and both
are the action of the global functions on `U` read through
`Stacks.Algebraization.puncturedScalars`. So the comparison is the identity map and its content is
one `rfl`. Finiteness and the depth bound are then transported from the direct image, which is
coherent and recovered from its own restriction by
`Stacks.Algebraization.isIso_unit_pushforward_puncturedSpectrum`.

Regularity of `f` is `f`-torsion-freeness of the module at the open `⊤`. The structure sheaf of
the punctured spectrum is `f`-torsion-free for every nonzerodivisor by
`Stacks.Algebraization.isFTorsionFree_unitModule`, hence so is every invertible module by
`Stacks.Algebraization.isFTorsionFree_of_isInvertible`; and
`Stacks.Algebraization.scalarOnOpen_top` says that at `⊤` the scalar used there is the one the
module structure on global sections acts by.

The kernel computation is the only piece with content. The inclusion `f Γ(U, ℱ) ⊆ ker` holds
because the target is a module over `A/fA`: the action of `A` there factors through
`Stacks.Algebraization.puncturedClosedFibreScalars`, which kills `f`. For the reverse inclusion
the prepared extension `ℱ' = ι_*ℱ` of
`Stacks.Algebraization.exists_preparedExtension_pushforward` is used. Restriction of global
sections to the punctured spectrum, followed by the extension's identification, is an `A`-linear
bijection `Γ(Spec A, ℱ') ≃ Γ(U, ℱ)`, and under it the canonical map on global sections becomes
the closed-fibre map of the extension precomposed with restriction along the closed immersion.
Both the closed-fibre map and restriction from the closed fibre to the punctured closed fibre are
injective — the first by
`Stacks.Algebraization.injective_closedFibreMap_of_pushforward`, the second by Hartogs extension
on `A/fA` — so the kernel in question is the kernel of restriction along the closed immersion.

That last kernel is computed without identifying the restriction map. Composed with
`Stacks.Algebraization.closedFibreSectionsEquivQuotSMulTop` it is a surjection of
`Γ(Spec A, ℱ')` onto `Γ(Spec A, ℱ')/f` which kills `f`, so it factors through an endomorphism of
`Γ(Spec A, ℱ')/f`; that endomorphism is a surjective endomorphism of a finite module over a
Noetherian ring, hence injective, and the kernel is therefore no larger than `f Γ(Spec A, ℱ')`.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open scoped Pointwise

universe u

namespace Stacks.Algebraization

/-! ### Global sections on the punctured spectrum and on the spectrum -/

/-- **The global sections on the punctured spectrum are the global sections on `Spec A` of the
direct image**, as `A`-modules. The two underlying abelian groups are the same, the open
immersion pulling `⊤` back to `⊤`; the content is that the two actions of `A` agree, both being
the action of the global functions on the punctured spectrum. -/
public noncomputable def puncturedSectionsPushforwardEquiv (A : Type u) [CommRing A]
    [IsLocalRing A] (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules) :
    letI := puncturedSectionsModule A F
    Γ(F, ⊤) ≃ₗ[A]
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F) : Type u) :=
  letI := puncturedSectionsModule A F
  AddEquiv.toLinearEquiv
    (M := Γ(F, ⊤))
    (M₂ := ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F) : Type u))
    (by rfl) (fun _ _ => rfl)

/-! ### Finiteness and depth for an invertible module -/

/-- **The global sections of an invertible module on the punctured spectrum of a Noetherian local
ring of depth at least two form a finite `A`-module.** They are the global sections of the direct
image, which is coherent. -/
public theorem finite_puncturedSections_of_isInvertible (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 F]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    letI := puncturedSectionsModule A F
    Module.Finite A Γ(F, ⊤) := by
  let := puncturedSectionsModule A F
  have : Module.Finite A
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F)) :=
    finite_globalSections_of_isCoherent _
      (isCoherent_isReflexive_pushforward_puncturedSpectrum A F hdepth).1
  exact Module.Finite.equiv (puncturedSectionsPushforwardEquiv A F).symm

/-- **The global sections of an invertible module on the punctured spectrum of a Noetherian local
ring of depth at least two have depth at least two over `A`.** They are the global sections of the
direct image, which is recovered from its own restriction, so
`Stacks.Algebraization.two_le_depth_globalSections_of_isIso_unit` applies. -/
public theorem two_le_depth_puncturedSections_of_isInvertible (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 F]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    letI := puncturedSectionsModule A F
    2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) Γ(F, ⊤) := by
  let := puncturedSectionsModule A F
  have hcoh : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F) :=
    (isCoherent_isReflexive_pushforward_puncturedSpectrum A F hdepth).1
  have : ((Scheme.Modules.pushforward
      (Stacks.Divisors.puncturedSpectrum A).ι).obj F).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A)
    (puncturedSectionsPushforwardEquiv A F)]
  exact two_le_depth_globalSections_of_isIso_unit A
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F)
    (isIso_unit_pushforward_puncturedSpectrum A F hdepth)

/-! ### Regularity of a nonzerodivisor -/

/-- **A nonzerodivisor of `A` acts regularly on the global sections of an invertible module on the
punctured spectrum.** The structure sheaf of the punctured spectrum is `f`-torsion-free for every
nonzerodivisor `f`, hence so is every invertible module; the assertion is that
`f`-torsion-freeness at the open `⊤`. -/
public theorem isSMulRegular_puncturedSections (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} (hf : IsSMulRegular A f)
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 F] :
    letI := puncturedSectionsModule A F
    IsSMulRegular Γ(F, ⊤) f := by
  let := puncturedSectionsModule A F
  have : Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme F :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ F).2 ‹_›
  have htf : IsFTorsionFree A f F :=
    isFTorsionFree_of_isInvertible A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) F
      (isFTorsionFree_unitModule A hf)
  exact htf ⊤

/-! ### The kernel of the canonical map on global sections -/

/-- The image of `f` in the functions on the punctured closed fibre vanishes: it factors through
the functions on the closed fibre, which is the spectrum of `A/fA`. -/
private theorem puncturedClosedFibreScalars_self (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) : puncturedClosedFibreScalars A f f = 0 := by
  have h2 : (closedImmersion A f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) = 0 := by
    rw [← closedFibreScalars_eq A f f,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f), map_zero]
  show (puncturedClosedFibre A f).ι.appTop
      ((closedImmersion A f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) = 0
  rw [h2, map_zero]

/-- If `f` kills every value of a linear map `g`, then `f • ⊤` lies in the kernel of `g`. -/
private theorem smul_top_le_ker_of_smul_eq_zero {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (f : A) (g : M →ₗ[A] N) (h : ∀ y, f • g y = 0) :
    f • (⊤ : Submodule A M) ≤ LinearMap.ker g := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  simpa using h y

/-- **Stacks Project, Tag 0F28 (the kernel of the canonical map).** For an invertible coherent
triple over a Noetherian local ring of depth at least three, the kernel of the canonical map on
global sections is `f Γ(U, ℱ)`.

One inclusion is that the target is a module over `A/fA`. The other is the injectivity of the
induced map `Γ(U, ℱ)/f ⟶ Γ(U₀, ℱ₀|_{U₀})`, obtained from the prepared extension given by the
direct image of the punctured-spectrum member: its closed-fibre map is injective, restriction to
the punctured closed fibre is bijective, and restriction along the closed immersion has kernel
exactly `f` times the global sections of the extension. -/
public theorem ker_globalSectionsMap (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 T.F]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (closedFibre A f).presheaf
      (closedFibre A f).ringCatSheaf.2 T.F₀]
    (hdepth : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    LinearMap.ker (globalSectionsMap A f T) = f • (⊤ : Submodule A Γ(T.F, ⊤)) := by
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  let := isLocalRing_quotient_span (A := A) (f := f) hf
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  obtain ⟨P, hP⟩ := exists_preparedExtension_pushforward A f hf hreg T hdepth
  have : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  have : P.F'.IsQuasicoherent := isQuasicoherent_of_isCoherent P.F'
  have : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F') :=
    finite_globalSections_of_isCoherent P.F' P.coherent
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.app P.F') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.Divisors.puncturedSpectrum A).ι).unit.isIso_app_iff_of_iso
        (eqToIso hP)).mpr (isIso_unit_pushforward_puncturedSpectrum A T.F hd2)
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (puncturedClosedFibre A f).ι).unit.app T.F₀) :=
    isIso_unit_puncturedClosedFibre A f hf hreg T.F₀ hdepth
  -- restriction to the punctured spectrum, read through the extension's identification
  have hαinv : ∀ z : Γ((Scheme.Modules.pullback
      (Stacks.Divisors.puncturedSpectrum A).ι).obj P.F', ⊤),
      P.alpha'.inv.app ⊤ (P.alpha'.hom.app ⊤ z) = z := fun z =>
    (ConcreteCategory.congr_hom
      (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) P.alpha'.hom_inv_id) z).trans
        (CategoryTheory.id_apply z)
  let := puncturedSectionsModule A
    ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj P.F')
  let Φ₁ : ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u) →ₗ[A]
      Γ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj P.F', ⊤) :=
    { toFun := pullbackGlobalSections (Stacks.Divisors.puncturedSpectrum A).ι P.F'
      map_add' := map_add _
      map_smul' := fun a x =>
        AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul
          (Stacks.Divisors.puncturedSpectrum A).ι P.F'
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) x }
  let Φ₂ : Γ((Scheme.Modules.pullback (Stacks.Divisors.puncturedSpectrum A).ι).obj P.F', ⊤) →ₗ[A]
      Γ(T.F, ⊤) :=
    { toFun := P.alpha'.hom.app ⊤
      map_add' := map_add _
      map_smul' := fun a x =>
        Scheme.Modules.Hom.app_smul P.alpha'.hom (puncturedScalars A a) x }
  let Φlin := Φ₂ ∘ₗ Φ₁
  have hΦbij : Function.Bijective Φlin := by
    constructor
    · intro a b hab
      refine (bijective_pullbackGlobalSections_of_isIso_unit
        (Stacks.Divisors.puncturedSpectrum A).ι P.F').injective ?_
      exact ((hαinv _).symm.trans (congrArg (P.alpha'.inv.app ⊤) hab)).trans (hαinv _)
    · intro y
      obtain ⟨s, hs⟩ := (bijective_pullbackGlobalSections_of_isIso_unit
        (Stacks.Divisors.puncturedSpectrum A).ι P.F').surjective (P.alpha'.inv.app ⊤ y)
      refine ⟨s, ?_⟩
      show P.alpha'.hom.app ⊤
        (pullbackGlobalSections (Stacks.Divisors.puncturedSpectrum A).ι P.F' s) = y
      rw [hs]
      exact AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app P.alpha' y
  let Φ := LinearEquiv.ofBijective Φlin hΦbij
  -- restriction along the closed immersion, as a map of `A`-modules
  let ρ : ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u) →ₗ[A]
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj
          ((Scheme.Modules.pullback (closedImmersion A f)).obj P.F')) : Type u) :=
    { toFun := pullbackGlobalSections (closedImmersion A f) P.F'
      map_add' := map_add _
      map_smul' := fun a s =>
        (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul
            (closedImmersion A f) P.F' ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) s).trans
          (congrArg (fun r => r • pullbackGlobalSections (closedImmersion A f) P.F' s)
            (closedFibreScalars_eq A f a).symm) }
  have hρsurj : Function.Surjective ρ :=
    surjective_pullbackGlobalSections_specMap (CommRingCat.of A)
      (CommRingCat.of (A ⧸ Ideal.span {f}))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      Ideal.Quotient.mk_surjective P.F'
  -- the kernel of that restriction is `f` times the global sections
  let E := closedFibreSectionsEquivQuotSMulTop A f P.F'
  have hfkill : ∀ y : QuotSMulTop f
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u), f • y = 0 := fun y =>
    Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator _ f) y
  have hle : f • (⊤ : Submodule A
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u)) ≤
      LinearMap.ker (E.toLinearMap ∘ₗ ρ) :=
    smul_top_le_ker_of_smul_eq_zero f _ fun y => hfkill _
  have hkerEq : LinearMap.ker (E.toLinearMap ∘ₗ ρ) = LinearMap.ker ρ := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
  have hkerρ : LinearMap.ker ρ =
      f • (⊤ : Submodule A
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u)) := by
    refine le_antisymm ?_ (hkerEq ▸ hle)
    have hbar := IsNoetherian.injective_of_surjective_endomorphism
      (Submodule.liftQ _ (E.toLinearMap ∘ₗ ρ) hle)
      (fun y => by
        obtain ⟨z, hz⟩ := E.surjective.comp hρsurj y
        exact ⟨Submodule.Quotient.mk z, hz⟩)
    intro x hx
    refine (Submodule.Quotient.mk_eq_zero _).mp (hbar ?_)
    rw [map_zero]
    show E (ρ x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  -- the comparison of the two routes on global sections
  have hkey : ∀ s : ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u),
      globalSectionsMap A f T (Φ s) =
        pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀
          (P.alpha₀'.app ⊤ (pullbackGlobalSections (closedImmersion A f) P.F' s)) := fun s =>
    (globalSectionsMap_apply A f T _).trans (preparedExtension_globalSections_comm A f T P s)
  have hρ₀inj : Function.Injective
      (pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀) :=
    (bijective_pullbackGlobalSections_of_isIso_unit (puncturedClosedFibre A f).ι T.F₀).injective
  have hcfm : Function.Injective P.closedFibreMap :=
    injective_closedFibreMap_of_pushforward A f hf T P hP hd2
  have hcfm' : ∀ z, P.closedFibreMap.hom z = 0 → z = 0 := fun z hz =>
    hcfm (hz.trans (map_zero P.closedFibreMap.hom).symm)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨s, rfl⟩ := Φ.surjective x
    have h1 : pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀
        (P.alpha₀'.app ⊤ (pullbackGlobalSections (closedImmersion A f) P.F' s)) = 0 :=
      (hkey s).symm.trans (LinearMap.mem_ker.mp hx)
    have h2 : ρ s = 0 := hcfm' _ (hρ₀inj (h1.trans (map_zero _).symm))
    have h3 : s ∈ f • (⊤ : Submodule A
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj P.F' : Type u)) := by
      rw [← hkerρ]
      exact LinearMap.mem_ker.mpr h2
    have h4 := Submodule.mem_map_of_mem (f := Φ.toLinearMap) h3
    rwa [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range] at h4
  · refine smul_top_le_ker_of_smul_eq_zero f _ fun y => ?_
    show puncturedClosedFibreScalars A f f • globalSectionsMap A f T y = 0
    rw [puncturedClosedFibreScalars_self, zero_smul]

end Stacks.Algebraization

end
