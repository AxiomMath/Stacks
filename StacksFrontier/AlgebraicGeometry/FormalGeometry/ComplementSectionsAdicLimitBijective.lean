module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsAdicLimit

/-!
# The degree-zero comparison of Stacks 0DXQ is an isomorphism

Let `(A, 𝔪)` be a Noetherian local ring which is `I`-adically complete, `M` a finite
`A`-module, and `J` an ideal with `V(J) ∩ V(I) = {𝔪}` and `J ⊆ J₀` for the ideal `J₀`
of Stacks 0DXP. This file proves that the canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is injective, and hence — together with the surjectivity of
`Stacks.Algebraization.surjective_complementSectionsToLimit` — bijective. This is the comparison
clause of Stacks 0DXQ read on the affine complement at `i = 0`; the theorem asserts it for
`i < s`, so the degree-zero case is the one that holds as soon as `1 ≤ s`.

## The diagram chase

The four-term sequence of Stacks 0BK0 gives, for every `A`-module `N`, an exact sequence

`0 ⟶ H⁰_J(N) ⟶ N ⟶ Γ(Spec A ∖ V(J), Ñ) ⟶ H¹_J(N) ⟶ 0`,

natural in `N`. Applying it to `N = M` and to the tower `N = M/IⁿM`, and taking the inverse limit
of the latter, gives a map of four-term sequences

```
H⁰_J(M)              ⟶  M            ⟶  Γ(Spec A ∖ V(J), M̃)              ⟶  H¹_J(M)
↓                        ↓                ↓                                  ↓
lim_n H⁰_J(M/IⁿM)    ⟶  lim_n M/IⁿM  ⟶  lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~) ⟶  lim_n H¹_J(M/IⁿM)
```

to which the mono half of the sharp four lemma,
`Stacks.LimitComparison.SharpFourLemma.injective_middle`, applies: the comparison in the second
spot from the right is injective once the left one is onto, the second from the left is injective
and the right one is injective, the top row is exact at `M` and at `Γ`, and the bottom row is
exact at `lim_n M/IⁿM`. The four inputs are:

* the left comparison `H⁰_J(M) ⟶ lim_n H⁰_J(M/IⁿM)` is onto, because it is an isomorphism:
  `Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit` applies in every degree
  `≤ s`, by Stacks 0DXP in the form of the `Stacks.Algebraization` lemma
  `isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal`;
* the second comparison `M ⟶ lim_n M/IⁿM` is injective, because a finite module over a Noetherian
  `I`-adically complete ring is `I`-adically complete, so Mathlib's `AdicCompletion.of` is
  bijective;
* the right comparison `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is injective, by the same route at degree
  `1`, which is where `1 ≤ s` is used;
* the bottom row is exact at `lim_n M/IⁿM` by Stacks 070B, applied to the four-term exact sequence
  of towers `0 ⟶ H⁰_J(M/IⁿM) ⟶ M/IⁿM ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~)` whose first term is the
  Mittag-Leffler tower `n ↦ H⁰_J(M/IⁿM)` itself, Mittag-Leffler by
  `Stacks.LocalCohomology.isMittagLeffler_forget_adicQuotientLocalCohomologySystem`. Exactness of
  that sequence at `H⁰_J(M/IⁿM)` is the injectivity of `H⁰_J(N) ⟶ N`.

## Main results

* `Stacks.LimitComparison.SharpFourLemma.injective_middle` — the mono half of the sharp four
  lemma, elementwise for linear maps.
* `Stacks.Algebraization.injective_adicQuotientModuleToLimit` — injectivity of
  `M ⟶ lim_n M/IⁿM` for an `I`-adically complete module.
* `Stacks.Algebraization.exact_lim_adicLocalCohomologyZero_restriction` — the bottom row of the
  ladder is exact at `lim_n M/IⁿM`.
* `Stacks.Algebraization.injective_complementSectionsToLimit` — injectivity of the degree-zero
  comparison.
* `Stacks.Algebraization.bijective_complementSectionsToLimit_of_comparisons` — the injectivity
  packaged with `Stacks.Algebraization.surjective_complementSectionsToLimit`.
* `Stacks.Algebraization.bijective_localCohomologyAdicQuotientToLimit` — bijectivity of
  `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)` under the hypotheses of Stacks 0DXP.
* `Stacks.Algebraization.bijective_complementSectionsToLimit` — the degree-zero comparison is
  bijective.

## Implementation notes

The mono half of the sharp four lemma is stated in the same elementwise style as its epi half,
`Stacks.LimitComparison.surjective_middle`, so the two are usable side by side.

The ladder is five columns wide at the level of the four-term sequence but only four are needed:
the chase never uses the map `H⁰_J(M) ⟶ lim_n H⁰_J(M/IⁿM)` beyond its surjectivity, and the
exactness of the top row at `M` enters only through `r ∘ i = 0`.

## References

* [Stacks Project, Tag 070B](https://stacks.math.columbia.edu/tag/070B)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LimitComparison.SharpFourLemma

/-! ### The mono half of the sharp four lemma -/

variable {R : Type*} [CommRing R]
  {H : Type*} [AddCommGroup H] [Module R H]
  {Mm : Type*} [AddCommGroup Mm] [Module R Mm]
  {G : Type*} [AddCommGroup G] [Module R G]
  {D : Type*} [AddCommGroup D] [Module R D]
  {Hl : Type*} [AddCommGroup Hl] [Module R Hl]
  {Lb : Type*} [AddCommGroup Lb] [Module R Lb]
  {Lc : Type*} [AddCommGroup Lc] [Module R Lc]
  {Ld : Type*} [AddCommGroup Ld] [Module R Ld]
  (i : H →ₗ[R] Mm) (r : Mm →ₗ[R] G) (δ : G →ₗ[R] D)
  (il : Hl →ₗ[R] Lb) (rl : Lb →ₗ[R] Lc) (δl : Lc →ₗ[R] Ld)
  (cA : H →ₗ[R] Hl) (cB : Mm →ₗ[R] Lb) (cC : G →ₗ[R] Lc) (cD : D →ₗ[R] Ld)

/-- **The comparison in the third spot of a four-column ladder is injective.** Given a
commutative ladder of `R`-linear maps

```
H  --i--> Mm --r--> G  --δ--> D
|cA       |cB       |cC       |cD
Hl --il-> Lb --rl-> Lc --δl-> Ld
```

whose top row is exact at `Mm` and at `G` and whose bottom row is exact at `Lb`, with `cA`
surjective, `cB` injective and `cD` injective, the comparison `cC` is injective.

This is the mono half of the sharp four lemma, the companion of
`Stacks.LimitComparison.surjective_middle`. The chase: if `cC x = 0` then `cD (δ x) = δl 0 = 0`,
so `δ x = 0` because `cD` is injective, so `x = r y` by exactness of the top row at `G`; then
`rl (cB y) = cC (r y) = 0`, so `cB y = il z` by exactness of the bottom row at `Lb`, and
`z = cA w` because `cA` is onto; the left square rewrites `il (cA w)` as `cB (i w)`, so
`y = i w` because `cB` is injective, and `x = r (i w) = 0` by exactness of the top row at
`Mm`. -/
public theorem injective_middle
    (hsqA : ∀ x, cB (i x) = il (cA x)) (hsqB : ∀ x, cC (r x) = rl (cB x))
    (hsqC : ∀ x, cD (δ x) = δl (cC x))
    (htopMm : Function.Exact i r) (htopG : Function.Exact r δ)
    (hbot : Function.Exact il rl)
    (hcA : Function.Surjective cA) (hcB : Function.Injective cB)
    (hcD : Function.Injective cD) :
    Function.Injective cC := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hδx : δ x = 0 := hcD (by rw [hsqC x, hx, map_zero, map_zero])
  obtain ⟨y, rfl⟩ := (htopG x).1 hδx
  obtain ⟨z, hz⟩ := (hbot (cB y)).1 ((hsqB y).symm.trans hx)
  obtain ⟨w, rfl⟩ := hcA z
  have hy : i w = y := hcB ((hsqA w).trans hz)
  rw [← hy]
  exact htopMm.apply_apply_eq_zero w

end Stacks.LimitComparison.SharpFourLemma

namespace Stacks.Algebraization

open Stacks.LocalCohomology

section Ladder

variable (A : Type u) [CommRing A] (I J : Ideal A) (hJ : J.FG)
  (D : LocalizationTriangleData.{u, u} A J hJ) (M : ModuleCat.{u} A)

/-! ### The comparison `M ⟶ lim_n M/IⁿM` is injective -/

/-- The `n`-th component of Mathlib's `AdicCompletion.of` is the `n`-th leg of the cone of
quotient maps `M ⟶ M/IⁿM`, read through the limit comparison. -/
public theorem adicCompletion_of_val_eq (x : M) (n : ℕ) :
    (AdicCompletion.of I M x).val n =
      ConcreteCategory.hom (limit.π (adicQuotientModuleSystem A I M) (op n))
        (ConcreteCategory.hom (adicQuotientModuleToLimit A I M) x) := by
  rw [← ConcreteCategory.comp_apply, adicQuotientModuleToLimit_π]
  rfl

/-- **The canonical map `M ⟶ lim_n M/IⁿM` is injective for an `I`-adically complete module.**
Its components are the components of Mathlib's `AdicCompletion.of`, which completeness makes
bijective. -/
public theorem injective_adicQuotientModuleToLimit [IsAdicComplete I M] :
    Function.Injective (ConcreteCategory.hom (adicQuotientModuleToLimit A I M)) := by
  intro x y h
  refine (AdicCompletion.of_bijective I M).1 (AdicCompletion.ext fun n => ?_)
  rw [adicCompletion_of_val_eq A I M x n, adicCompletion_of_val_eq A I M y n, h]

/-! ### The square on the far left of the ladder -/

/-- **The square on the far left of the chase**: reducing the image in `M` of a degree-zero local
cohomology class modulo `Iⁿ` is the image in `M/IⁿM` of its reduction. This is the naturality of
the map `H⁰_J(-) ⟶ (-)` of the four-term sequence along the quotient maps `M ⟶ M/IⁿM`. -/
public theorem localCohomologyZeroToModule_comp_adicQuotientModuleToLimit :
    localCohomologyZeroToModule A J hJ M ≫ adicQuotientModuleToLimit A I M =
      localCohomologyAdicQuotientToLimit A I J hJ M 0 ≫
        limMap (adicLocalCohomologyZeroNat A I J hJ M) := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  simp only [Category.assoc, adicQuotientModuleToLimit_π, limMap_π,
    adicLocalCohomologyZeroNat_app]
  refine ((localCohomologyZeroNat A J hJ).naturality
    (Dualizing.adicQuotientProjection A I M n)).symm.trans ?_
  exact (congrArg (fun φ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((localCohomologyDerived A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ⟶
        (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (op n) =>
      φ ≫ localCohomologyZeroToModule A J hJ ((adicQuotientModuleSystem A I M).obj (op n)))
    (localCohomologyAdicQuotientToLimit_π A I J hJ M 0 n).symm).trans (Category.assoc _ _ _)

/-- The square on the far left of the chase, read on an element: this is
`Stacks.Algebraization.localCohomologyZeroToModule_comp_adicQuotientModuleToLimit` with both
composites applied to a degree-zero local cohomology class. -/
public theorem adicQuotientModuleToLimit_localCohomologyZeroToModule
    (x : localCohomologyModule A J hJ M 0) :
    ConcreteCategory.hom (adicQuotientModuleToLimit A I M)
        (ConcreteCategory.hom (localCohomologyZeroToModule A J hJ M) x) =
      ConcreteCategory.hom (limMap (adicLocalCohomologyZeroNat A I J hJ M))
        (ConcreteCategory.hom (localCohomologyAdicQuotientToLimit A I J hJ M 0) x) :=
  congrArg (fun φ : localCohomologyModule A J hJ M 0 ⟶
      limit (adicQuotientModuleSystem A I M) => ConcreteCategory.hom φ x)
    (localCohomologyZeroToModule_comp_adicQuotientModuleToLimit A I J hJ M)

/-! ### The bottom row is exact at `lim_n M/IⁿM` -/

/-- The map `H⁰_J(M/IⁿM) ⟶ M/IⁿM` of the four-term sequence is injective at every index of the
tower: it is the canonical map `H⁰_J(N) ⟶ N` of Stacks 0DWR. -/
public theorem injective_adicLocalCohomologyZeroNat_app (n : ℕᵒᵖ) :
    Function.Injective
      (ConcreteCategory.hom ((adicLocalCohomologyZeroNat A I J hJ M).app n)) := by
  rw [adicLocalCohomologyZeroNat_app]
  exact localCohomologyZeroToModule_injective A J hJ _

variable [IsLocalRing A] [IsNoetherianRing A]

/-- **The limit of the four-term sequences is exact at `lim_n M/IⁿM`**, by Stacks 070B applied to
the exact sequence of towers

`H⁰_J(M/IⁿM) --0--> H⁰_J(M/IⁿM) ⟶ M/IⁿM ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~)`,

whose first term is the tower `n ↦ H⁰_J(M/IⁿM)`, Mittag-Leffler when `V(J) ∩ V(I) = {𝔪}`. The
sequence is exact at the second spot because `H⁰_J(N) ⟶ N` is injective. -/
public theorem exact_lim_adicLocalCohomologyZero_restriction [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    Function.Exact
      (ConcreteCategory.hom (limMap (adicLocalCohomologyZeroNat A I J hJ M)))
      (ConcreteCategory.hom (limMap (adicComplementRestrictionNat A I J hJ D M))) := by
  refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (ModuleCat.exact_lim_map_of_isMittagLeffler
      (0 : (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0) ⟶
          Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
      (adicLocalCohomologyZeroNat A I J hJ M)
      (adicComplementRestrictionNat A I J hJ D M)
      zero_comp
      (adicLocalCohomologyZeroNat_comp_restriction A I J hJ D M)
      (ShortComplex.exact_of_exact_evaluation _ fun n => ?_)
      (ShortComplex.exact_of_exact_evaluation _
        (exact_evaluation_adicLocalCohomologyZeroNat A I J hJ D M))
      (isMittagLeffler_forget_adicQuotientLocalCohomologySystem A I J M hV 0))
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx0 : ConcreteCategory.hom ((adicLocalCohomologyZeroNat A I J hJ M).app n) x =
      ConcreteCategory.hom ((adicLocalCohomologyZeroNat A I J hJ M).app n) 0 := by
    rw [map_zero]
    exact hx
  refine ⟨0, ?_⟩
  rw [injective_adicLocalCohomologyZeroNat_app A I J hJ M n hx0, map_zero]

/-! ### Injectivity of the degree-zero comparison -/

include D in
/-- **The comparison clause of Stacks 0DXQ at `i = 0`, read on the affine complement
`Spec A ∖ V(J)`: the injectivity.** The canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is injective, provided the canonical map `H⁰_J(M) ⟶ lim_n H⁰_J(M/IⁿM)` is surjective and the
canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is injective. Both are supplied by Stacks 0DXP
together with the pinned form of Stacks 0DXJ, in
`Stacks.Algebraization.bijective_localCohomologyAdicQuotientToLimit`.

This is the diagram chase of `Stacks.LimitComparison.SharpFourLemma.injective_middle`, applied to
the map from the four-term sequence of `M` to the inverse limit of the four-term sequences of the
`M/IⁿM`. -/
public theorem injective_complementSectionsToLimit [Module.Finite A M] [IsAdicComplete I M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hcA : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 0)))
    (hcD : Function.Injective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1))) :
    Function.Injective (ConcreteCategory.hom (complementSectionsToLimit A I J M)) :=
  Stacks.LimitComparison.SharpFourLemma.injective_middle _ _ _ _ _ _ _ _ _ _
    (adicQuotientModuleToLimit_localCohomologyZeroToModule A I J hJ M)
    (complementSectionsToLimit_restrictionToComplement A I J hJ D M)
    (localCohomologyAdicQuotientToLimit_localizationBoundary A I J hJ D M)
    (exact_localCohomologyZeroToModule_restrictionToComplement D M
      (complementTilde A J M) (Iso.refl _))
    (exact_restrictionToComplement_localizationBoundary D M
      (complementTilde A J M) (Iso.refl _))
    (exact_lim_adicLocalCohomologyZero_restriction A I J hJ D M hV)
    hcA (injective_adicQuotientModuleToLimit A I M) hcD

include D in
/-- **The comparison clause of Stacks 0DXQ at `i = 0`, read on the affine complement
`Spec A ∖ V(J)`: the bijectivity.** The canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is bijective, provided the canonical map `H⁰_J(M) ⟶ lim_n H⁰_J(M/IⁿM)` is surjective and the
canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is bijective. -/
public theorem bijective_complementSectionsToLimit_of_comparisons [Module.Finite A M]
    [IsAdicComplete I M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hcA : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 0)))
    (hcD : Function.Bijective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1))) :
    Function.Bijective (ConcreteCategory.hom (complementSectionsToLimit A I J M)) :=
  ⟨injective_complementSectionsToLimit A I J hJ D M hV hcA hcD.1,
    surjective_complementSectionsToLimit A I J hJ D M hV hcD.2⟩

end Ladder

/-! ### Discharging the two comparisons from Stacks 0DXP -/

section Discharge

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- **The canonical map `Hʳ_J(M) ⟶ lim_n Hʳ_J(M/IⁿM)` is bijective** under the hypotheses of
Stacks 0DXP, in every degree `r ≤ s`. This is
`Stacks.Algebraization.isIso_localCohomologyAdicQuotientToLimit` fed with Stacks 0DXP in the form
of
`Stacks.Algebraization.isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal`,
the same route as `Stacks.Algebraization.surjective_localCohomologyAdicQuotientToLimit`. -/
public theorem bijective_localCohomologyAdicQuotientToLimit
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (r : ℤ) (hr : r ≤ s) :
    Function.Bijective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J J.fg_of_isNoetherianRing
        (ModuleCat.of A M) r)) := by
  have := isIso_localCohomologyAdicQuotientToLimit A I J (ModuleCat.of A M) hV r
    (isIso_homology_completedLocalCohomologyUnit_of_isLocalAlgebraizationIdeal H J hJ hV r hr)
  exact ConcreteCategory.bijective_of_isIso _

/-- **The comparison clause of Stacks 0DXQ at `i = 0`, read on the affine complement
`Spec A ∖ V(J)`, with every comparison discharged.** For `(A, 𝔪)` Noetherian local and
`I`-adically complete, `M` a finite `A`-module, `J₀` an ideal with the property of Stacks 0DXP
for a bound `1 ≤ s`, and `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`, the canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is bijective.

The completeness of `M` is not assumed: a finite module over a Noetherian `I`-adically complete
ring is `I`-adically complete, by
`AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing`. The two comparisons the chase
needs are the degree-`0` and degree-`1` instances of
`Stacks.Algebraization.bijective_localCohomologyAdicQuotientToLimit`, which is where `1 ≤ s`
enters: the theorem of Stacks 0DXQ asserts the isomorphism in degrees `i < s`, and `i = 0`
is covered exactly when `0 < s`. -/
public theorem bijective_complementSectionsToLimit
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} [IsAdicComplete I A] {hI : I ≠ ⊤} {s : ℤ} {J₀ : Ideal A}
    (H : IsLocalAlgebraizationIdeal (M := M) I hI s J₀)
    (J : Ideal A) (hJJ₀ : J ≤ J₀) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hs : 1 ≤ s) :
    Function.Bijective (ConcreteCategory.hom
      (complementSectionsToLimit A I J (ModuleCat.of A M))) :=
  have : IsAdicComplete I M :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I M
  bijective_complementSectionsToLimit_of_comparisons A I J hJ D (ModuleCat.of A M) hV
    (bijective_localCohomologyAdicQuotientToLimit H J hJJ₀ hV 0
      (le_trans zero_le_one hs)).2
    (bijective_localCohomologyAdicQuotientToLimit H J hJJ₀ hV 1 hs)

end Discharge

end Stacks.Algebraization

end
