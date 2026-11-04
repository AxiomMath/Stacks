module

public import StacksFrontier.AlgebraicGeometry.Fibres.AssociatedPrimesCover
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAtAdicLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAtCollapse
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSectionsFiniteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness

/-!
# The whole of Stacks 0DXR

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is complete with respect
to an ideal `I`, put `X = Spec(A)`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let `ℱ` be a coherent module
on `U` whose every associated point `x ∈ U` satisfies `dim(closure {x}) > cd(A, I) + 1`, the
closure being taken in `X`. Stacks 0DXR asserts that the canonical map

`colim_V H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ / Iⁿ ℱ)`,

the colimit being over the opens `V ⊆ U` containing `U ∩ Y`, is an isomorphism of finite
`A`-modules. This file proves that.

## The route

The source proves it by applying Stacks 0DXQ with `s = 1`, getting the finiteness as well. The
hypothesis half of that application is
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSectionsFiniteness`; its
comparison clause at `i = 0` is
`Stacks.Algebraization.surjective_comparisonAt_ofZeroLocusInter`, proved by the four-term diagram
chase of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsAdicLimit`. What this file adds
is the passage from those to the displayed map:

* Stacks 0BK0 (1) presents `ℱ` as `M̃|_U` for a finite `A`-module `M`;
* the associated points of `M̃|_U` are the associated primes of `M` other than `𝔪`, by
  `Stacks.Algebraization.mem_associatedPoints_complementTilde_iff`, so the source's dimension
  hypothesis becomes `Stacks.Algebraization.AssociatedPrimesClosureDimensionBound`;
* Stacks 0DXP then supplies the ideal `J₀`, hence the surjectivity of the canonical map
  `H¹_{J₀}(M) ⟶ lim_n H¹_{J₀}(M/IⁿM)`, hence the surjectivity of the comparison at the
  neighbourhood `V₀ = X ∖ V(J₀)`;
* the displayed map is injective with no hypothesis beyond Noetherian and coherent, so it is an
  isomorphism, and the colimit is a quotient of `H⁰(V₀, ℱ)`.

## Main results

* `Stacks.Algebraization.mem_associatedPoints_complementTilde_iff` — the associated points of
  `M̃|_U` are the associated primes of `M`.
* `Stacks.Algebraization.surjective_comparisonAt_of_dimensionBound` — the comparison at one
  neighbourhood is onto, under the source's own hypotheses.
* `Stacks.Algebraization.isIso_comparisonMap_of_dimensionBound` — the displayed map is an
  isomorphism of abelian groups.

## References

* [Stacks Project, Tag 0DXR](https://stacks.math.columbia.edu/tag/0DXR)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The associated points of `M̃|_U` -/

/-- **The associated points of `M̃|_U` are the associated primes of `M`.** For `U = Spec(A) ∖ V(𝔟)`
and a point `x` of `U`, the prime of `x` is an associated prime of `M` exactly when `x` is an
associated point of the restriction of `M̃` to `U`: restriction along an open immersion does not
change the stalk, and the stalk of `M̃` at a prime is the localization of `M` there. -/
public theorem mem_associatedPoints_complementTilde_iff (A : Type u) [CommRing A]
    [IsNoetherianRing A] (b : Ideal A) (M : ModuleCat.{u} A)
    (x : (complementZeroLocus A b : Scheme)) :
    x ∈ Stacks.Divisors.associatedPoints
        (((tilde.functor (CommRingCat.of A)).obj M).restrict (complementZeroLocus A b).ι) ↔
      x.1.asIdeal ∈ associatedPrimes A M :=
  ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
        (complementZeroLocus A b).ι ((tilde.functor (CommRingCat.of A)).obj M) x).trans
      (isAssociatedPoint_tilde_iff A M x.1)).trans
    Stacks.Divisors.isAssociatedPrimeStacks_iff_mem_associatedPrimes

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : ModuleCat.{u} A) [Module.Finite A M]

omit [Module.Finite A M] in
/-- **The dimension hypothesis of Stacks 0DXR, read on a finite module.** The source's hypothesis
is a bound at the associated points of `ℱ = M̃|_U`; by
`Stacks.Algebraization.mem_associatedPoints_complementTilde_iff` those are the associated primes
of `M` other than the maximal ideal, so the hypothesis is
`Stacks.Algebraization.AssociatedPrimesClosureDimensionBound`. -/
public theorem associatedPrimesClosureDimensionBound_of_dimensionBound
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints
        (((tilde.functor (CommRingCat.of A)).obj M).restrict
          (complementZeroLocus A (maximalIdeal A)).ι) →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    AssociatedPrimesClosureDimensionBound (M := M) I := by
  intro p hass hpne
  have hmem : p ∈ complementZeroLocus A (maximalIdeal A) :=
    (mem_complementZeroLocus_iff_not_le (maximalIdeal A) p).2 fun hle =>
      hpne (PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) hle))
  exact hdim ⟨p, hmem⟩
    ((mem_associatedPoints_complementTilde_iff A (maximalIdeal A) M ⟨p, hmem⟩).2 hass)

variable (Fm : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)
  (e : Fm ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
    (complementZeroLocus A (maximalIdeal A)).ι)

include e in
/-- **The comparison at one neighbourhood of the formal locus is onto, under the hypotheses of
Stacks 0DXR.** Stacks 0DXP supplies the ideal `J₀`; the canonical map
`H¹_{J₀}(M) ⟶ lim_n H¹_{J₀}(M/IⁿM)` is then onto by
`Stacks.Algebraization.surjective_localCohomologyAdicQuotientToLimit`, and the comparison at the
neighbourhood `X ∖ V(J₀)` is onto by
`Stacks.Algebraization.surjective_comparisonAt_ofZeroLocusInter`. -/
public theorem surjective_comparisonAt_of_dimensionBound
    (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A)) (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints Fm →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    ∃ V : OpensNearVanishing A I (maximalIdeal A),
      Function.Surjective (ConcreteCategory.hom (comparisonAt A I (maximalIdeal A) Fm V)) := by
  have := hcomplete
  have : IsAdicComplete I (M : Type u) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I (M : Type u)
  have hdimM : AssociatedPrimesClosureDimensionBound (M := (M : Type u)) I :=
    associatedPrimesClosureDimensionBound_of_dimensionBound A I M fun x hx =>
      hdim x ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr
        e x).2 hx)
  obtain ⟨J₀, H⟩ := exists_isLocalAlgebraizationIdeal_of_associatedPrimesClosureDimensionBound
    (M := (M : Type u)) I hcomplete omega hdualizing hdimM
  refine ⟨OpensNearVanishing.ofZeroLocusInter I J₀ H.zeroLocus_inter, ?_⟩
  exact surjective_comparisonAt_ofZeroLocusInter A I J₀ H.zeroLocus_inter M Fm e
    J₀.fg_of_isNoetherianRing
    (localizationTriangleData.{u} A J₀ J₀.fg_of_isNoetherianRing)
    (surjective_localCohomologyAdicQuotientToLimit H J₀ le_rfl H.zeroLocus_inter 1 le_rfl)

include e in
/-- **The displayed map of Stacks 0DXR is an isomorphism of abelian groups.** It is injective with
no hypothesis beyond `A` Noetherian and `ℱ` coherent, and surjective because the comparison at one
neighbourhood is. -/
public theorem isIso_comparisonMap_of_dimensionBound [Fm.IsCoherent]
    (hcomplete : IsAdicComplete I A)
    (omega : DerivedCategory (ModuleCat.{u} A)) (hdualizing : Dualizing.IsDualizingComplex omega)
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints Fm →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    IsIso (comparisonMap A I (maximalIdeal A) Fm) := by
  obtain ⟨V, hsurj⟩ := surjective_comparisonAt_of_dimensionBound A I M Fm e hcomplete omega
    hdualizing hdim
  exact isIso_comparisonMap_of_surjective_comparisonAt' A I (maximalIdeal A) Fm hsurj

/-! ### The two `A`-module structures on the sections of `M̃` over an open -/

variable {A I}

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- **The `A`-action of `Stacks.Algebraization.opensScalars` on the sections of `M̃|_U` is the
evident one.** The scalars of `A` on an open `W` of `U = Spec(A) ∖ V(𝔟)` are the restriction of
the global scalars, which at every prime of the image of `W` is `r / 1`, and a locally fractional
section is multiplied by it componentwise. -/
public theorem smul_opensScalars_restrict_tilde (b : Ideal A) (N : ModuleCat.{u} A)
    (W : (complementZeroLocus A b : Scheme).Opens) (r : A)
    (x : moduleSections N ((complementZeroLocus A b).ι ''ᵁ W)) :
    ConcreteCategory.hom ((((tilde.functor (CommRingCat.of A)).obj N).restrict
        (complementZeroLocus A b).ι).smul (opensScalars A b W r)) x = r • x := by
  have happ : (((complementZeroLocus A b).ι.appIso W).inv (opensScalars A b W r)) =
      opensScalars A b W r := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hstep : ConcreteCategory.hom ((((tilde.functor (CommRingCat.of A)).obj N).restrict
        (complementZeroLocus A b).ι).smul (opensScalars A b W r)) x =
      ConcreteCategory.hom (((tilde.functor (CommRingCat.of A)).obj N).smul
        (((complementZeroLocus A b).ι.appIso W).inv (opensScalars A b W r))) x := rfl
  rw [hstep, happ]
  refine Subtype.ext (funext fun y => ?_)
  exact algebraMap_smul (StructureSheaf.Localizations A y.1) r (x.1 y)

variable (A I)

/-! ### The sections on the neighbourhood cut out by `J` are a finite `A`-module -/

/-- **The sections of `ℱ` on the neighbourhood cut out by `J` are the global sections of `M̃` on
`Spec(A) ∖ V(J)`, `A`-linearly.** The map goes from the second to the first: the identification
of the opens, then the identification of `M̃|_U` with `ℱ`. -/
public def complementGlobalSectionsToSectionsAt (J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (M : ModuleCat.{u} A)
    (Fm : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)
    (e : Fm ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι) :
    complementGlobalSections A J (complementTilde A J M) →ₗ[A]
      sectionsAtModule (F := Fm) (OpensNearVanishing.ofZeroLocusInter I J hV) where
  toFun y := ConcreteCategory.hom
    (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)
    ((moduleSectionsCongr M
      (ι_image_openSet_ofZeroLocusInter_eq_ι_image_top A I J hV)).symm
        ((complementGlobalSectionsEquiv J M).symm y))
  map_add' y z := by
    simp only [map_add]
    exact map_add _ _ _
  map_smul' r y := by
    have h1 : (moduleSectionsCongr M
          (ι_image_openSet_ofZeroLocusInter_eq_ι_image_top A I J hV)).symm
          ((complementGlobalSectionsEquiv J M).symm (r • y)) =
        r • (moduleSectionsCongr M
          (ι_image_openSet_ofZeroLocusInter_eq_ι_image_top A I J hV)).symm
          ((complementGlobalSectionsEquiv J M).symm y) := by
      rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
    rw [h1, ← smul_opensScalars_restrict_tilde (maximalIdeal A) M
      (OpensNearVanishing.ofZeroLocusInter I J hV).openSet r]
    exact (ConcreteCategory.congr_hom
      (app_comp_smul e.inv
        (opensScalars A (maximalIdeal A)
          (OpensNearVanishing.ofZeroLocusInter I J hV).openSet r)) _).symm

/-- The comparison of the previous definition is onto: each of its three factors is a
bijection. -/
public theorem surjective_complementGlobalSectionsToSectionsAt (J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (M : ModuleCat.{u} A)
    (Fm : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)
    (e : Fm ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι) :
    Function.Surjective (complementGlobalSectionsToSectionsAt A I J hV M Fm e) := by
  have hiso : IsIso (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet) :=
    ((Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj
      (op (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)).mapIso e.symm).isIso_hom
  have hbij := ConcreteCategory.bijective_of_isIso
    (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)
  intro w
  obtain ⟨v, hv⟩ := hbij.2 w
  refine ⟨(complementGlobalSectionsEquiv J M)
    ((moduleSectionsCongr M (ι_image_openSet_ofZeroLocusInter_eq_ι_image_top A I J hV)) v), ?_⟩
  refine Eq.trans (congrArg (ConcreteCategory.hom
    (e.inv.app (OpensNearVanishing.ofZeroLocusInter I J hV).openSet)) ?_) hv
  rw [LinearEquiv.symm_apply_apply]
  exact LinearEquiv.symm_apply_apply _ v

/-- **The sections of `ℱ` on the neighbourhood cut out by `J` are a finite `A`-module** as soon as
the global sections of `M̃` on `Spec(A) ∖ V(J)` are. -/
public theorem finite_sectionsAtModule_ofZeroLocusInter (J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (M : ModuleCat.{u} A)
    (Fm : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules)
    (e : Fm ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict
      (complementZeroLocus A (maximalIdeal A)).ι)
    [Module.Finite A (complementGlobalSections A J (complementTilde A J M))] :
    Module.Finite A (sectionsAtModule (F := Fm) (OpensNearVanishing.ofZeroLocusInter I J hV)) :=
  Module.Finite.of_surjective (complementGlobalSectionsToSectionsAt A I J hV M Fm e)
    (surjective_complementGlobalSectionsToSectionsAt A I J hV M Fm e)

/-! ### Stacks 0DXR -/

/-- **Stacks 0DXR.** Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is
complete with respect to an ideal `I`. Put `X = Spec(A)`, `Y = V(I)` and `U = X ∖ {𝔪}`, and let
`ℱ` be a coherent module on `U` such that every associated point `x ∈ U` of `ℱ` satisfies
`dim(closure {x}) > cd(A, I) + 1`, the closure being taken in `X`. Then the canonical map

`colim_V H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ / Iⁿ ℱ)`,

the colimit being over the opens `V ⊆ U` containing `U ∩ Y`, is an isomorphism of finite
`A`-modules.

The two sides are the `A`-modules `Stacks.Algebraization.sectionsNearVanishingColimit` and
`Stacks.Algebraization.formalSectionsLimit`; the map is
`Stacks.Algebraization.comparisonModuleMap`, whose underlying map of abelian groups is
`Stacks.Algebraization.comparisonMap` by
`Stacks.Algebraization.forget₂_comparisonModuleMap`. The source's dimension hypothesis is stated
with `dim(closure {x}) = dim(A/𝔭)`, exactly as the source states it.

The proof is the source's: apply Stacks 0DXQ with `s = 1`, getting the finiteness too. Stacks
0BK0 (1) presents `ℱ` as `M̃|_U` for a finite `A`-module `M`; the associated points of `M̃|_U` are
the associated primes of `M`, so the dimension hypothesis becomes the hypothesis of Stacks 0DXP,
which supplies an ideal `J₀`, and of the finiteness clause of Stacks 0DXQ, which supplies an
ideal `J₁`. At `J = J₀ ∩ J₁` both apply: the canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is onto
by Stacks 0DXP together with the pinned form of Stacks 0DXJ, so the four-term diagram chase makes
the comparison at the neighbourhood `X ∖ V(J)` onto; the displayed map is injective with no
hypothesis beyond Noetherian and coherent, hence an isomorphism; and the colimit is a quotient of
`H⁰(X ∖ V(J), ℱ)`, which is finite. -/
@[stacks 0DXR "the whole statement: the displayed map colim_V H⁰(V, ℱ) ⟶ lim_n H⁰(U, ℱ/Iⁿℱ) is \
an isomorphism of A-modules, and both of its two sides are finite A-modules"]
public theorem isIso_comparisonModuleMap_and_finite_maximalIdeal
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (F : (complementZeroLocus A (maximalIdeal A) : Scheme).Modules) [F.IsCoherent]
    (hdim : ∀ x : (complementZeroLocus A (maximalIdeal A) : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal))) :
    IsIso (comparisonModuleMap A I (maximalIdeal A) F) ∧
      Module.Finite A (sectionsNearVanishingColimit A I (maximalIdeal A) F) ∧
        Module.Finite A (formalSectionsLimit A I (maximalIdeal A) F) := by
  obtain ⟨K, hK⟩ := hdualizing
  obtain ⟨M, hMfin, ⟨e⟩⟩ := exists_finiteModule_iso_restrict_tilde A (maximalIdeal A) F
  have := hMfin
  have := hcomplete
  have : IsAdicComplete I (M : Type u) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I (M : Type u)
  have hdimM : AssociatedPrimesClosureDimensionBound (M := (M : Type u)) I :=
    associatedPrimesClosureDimensionBound_of_dimensionBound A I M fun x hx =>
      hdim x ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr
        e x).2 hx)
  obtain ⟨J₀, H⟩ := exists_isLocalAlgebraizationIdeal_of_associatedPrimesClosureDimensionBound
    (M := (M : Type u)) I hcomplete K hK hdimM
  obtain ⟨J₁, hJ₁, hfin⟩ :=
    finite_complementGlobalSections_of_associatedPrimesClosureDimensionBound
      (M := (M : Type u)) I hcomplete K hK hdimM
  -- the two ideals are combined by intersection
  have hVJ : PrimeSpectrum.zeroLocus ((J₀ ⊓ J₁ : Ideal A) : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) = {closedPoint A} := by
    rw [PrimeSpectrum.zeroLocus_inf, Set.union_inter_distrib_right, H.zeroLocus_inter, hJ₁,
      Set.union_self]
  have := hfin (J₀ ⊓ J₁) inf_le_right hVJ
  have hsurj := surjective_comparisonAt_ofZeroLocusInter A I (J₀ ⊓ J₁) hVJ M F e
    (J₀ ⊓ J₁).fg_of_isNoetherianRing
    (localizationTriangleData.{u} A (J₀ ⊓ J₁) (J₀ ⊓ J₁).fg_of_isNoetherianRing)
    (surjective_localCohomologyAdicQuotientToLimit H (J₀ ⊓ J₁) inf_le_left hVJ 1 le_rfl)
  have : Module.Finite A (sectionsAtModule (F := F)
      (OpensNearVanishing.ofZeroLocusInter I (J₀ ⊓ J₁) hVJ)) :=
    finite_sectionsAtModule_ofZeroLocusInter A I (J₀ ⊓ J₁) hVJ M F e
  exact ⟨(isIso_comparisonModuleMap_iff A I (maximalIdeal A) F).2
      (isIso_comparisonMap_of_surjective_comparisonAt' A I (maximalIdeal A) F hsurj),
    finite_sectionsNearVanishingColimit_of_surjective_comparisonAt hsurj,
    finite_formalSectionsLimit_of_surjective_comparisonAt hsurj⟩

end Stacks.Algebraization

end
