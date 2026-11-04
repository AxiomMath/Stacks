module

public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Assembly
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic

/-!
# `g ^* 𝒪(1)` is free of rank one on every chart of a pinned morphism to `ℙⁿ_ℤ`

The twist half of [Stacks, Tag 01NE] — `Stacks.AmpleImmersionReduction.TwistPullback`, the first
of the four named inputs of [Stacks, Tag 01VS] — asks for an isomorphism
`M ≅ p ^* 𝒪(1)` for a morphism `p : X ⟶ ℙⁿ_S` pinned on each chart `X_{sᵢ}` by a generating
family `s` of global sections of an invertible `M`. This file does the `𝒪(1)` side of that
comparison: it produces, from the pinning alone, a trivialization of `g ^* 𝒪(1)` over each chart.

## What the pinning is used for

Nothing in `StacksFrontier/AlgebraicGeometry/TwistInvertibleOverBase/Basic.lean` — which made
both sides of the comparison invertible, and so reduced the obligation from an isomorphism to a
single epimorphism — uses the pinning hypothesis. This file is where it is consumed, and it is
consumed twice over:

* the pinned restriction `(X_{sᵢ}).ι ≫ g` is the morphism of the ratio family `sₖ/sᵢ`, whose
  `i`-th member is `1`, so by `Stacks.SectionsToProjectiveSpace.preimage_basicOpen` and
  `AlgebraicGeometry.Scheme.basicOpen_one` the preimage of the standard chart `D₊(Tᵢ)` is all of
  `X_{sᵢ}`. That is `Stacks.TwistPullbackChart.range_subset_chart`, and it is what lets `g`
  restricted to the chart be *factored* through `D₊(Tᵢ)`.
* the factorization is then fed to
  `Stacks.AlgebraicGeometry.ProjTwistMono.restrictPullbackIsoUnit`, which carries a
  trivialization of a module on a target open back along an arbitrary morphism.

## The trivialization of `𝒪(1)` on `D₊(Tᵢ)`

`Stacks.AlgebraicGeometry.ProjTwistMono.pullbackTwistIsoUnit` trivializes `𝒪(n)` on `D₊(p q)`
for `p` homogeneous of degree `e + 1` and `q` of degree `e`, for **every** integer `n`, with no
divisibility condition — the trivializing section being `(p/q)ⁿ`. Its own file applies it only
to the degree-one ratio locus of a graded homomorphism.
`Stacks.TwistPullbackChart.degreeOnePullbackTwistIsoUnit` is the case `q = 1`, `e = 0`, which is
the standard-open statement: on `D₊(p)` for `p` of degree one, every `𝒪(n)` is the unit module.
`Stacks.TwistPullbackChart.twistIsoUnitOnChart` is that at `𝒜 = ℤ[T₀, …, Tₙ]`, `p = Tᵢ`, `n = 1`.

## Main definitions

* `Stacks.TwistPullbackChart.degreeOnePullbackTwistIsoUnit`: `𝒪(n)` pulls back to the unit module
  on the standard open of a degree-one homogeneous element, for every `n : ℤ`.
* `Stacks.TwistPullbackChart.twistIsoUnitOnChart`: the same at `D₊(Tᵢ) ⊆ ℙⁿ_ℤ` and the
  hyperplane sheaf `Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse`.
* `Stacks.TwistPullbackChart.chartFactor`: the pinned restriction of `g` to a chart, factored
  through `D₊(Tᵢ)`.
* `Stacks.TwistPullbackChart.pullbackTwistRestrictIsoUnit` and
  `pullbackTwistRestrictIsoUnitChart`: **`g ^* 𝒪(1)` restricted to the chart is the unit
  module**, the second stated at the statement's own chart `X_{sᵢ}` and ratio family.

## Main results

* `Stacks.TwistPullbackChart.range_subset_chart`: a spanning family one of whose members is `1`
  has its morphism to `ℙⁿ_ℤ` landing set-theoretically inside the matching standard chart.
* `Stacks.TwistPullbackChart.range_comp_subset_chart`,
  `Stacks.TwistPullbackChart.chartFactor_fac`: the factorization and its defining identity.

## What is not done, exactly

The companion half — a trivialization of `M` itself over `X_{sᵢ}` in the `restrictFunctor`
spelling — is **not** here, and neither is the comparison of the two. The mathematics left is one
proposition, and it is the transition-cocycle comparison:

> for `i j`, the two trivializations of `g ^* 𝒪(1)` over `X_{sᵢ} ∩ X_{sⱼ}` coming from
> `pullbackTwistRestrictIsoUnitChart` at `i` and at `j` differ by the unit
> `Stacks.ProjectiveFromSections.ratio s i j`.

That is the only input `Stacks.AmpleImmersionReduction.TwistPullback` still needs, because
everything else is available: `M`'s own transitions are `ratio` by
`Stacks.ProjectiveFromSections.ratio_cocycle`, a compatible family of morphisms of
`Scheme.Modules` over an open cover glues by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, and an
epimorphism between the two invertible modules is already enough by
`Stacks.TwistInvertibleOverBase.nonempty_iso_of_epi_pullback_twistingSheaf`. The pullback of the
degree-zero fraction `Tⱼ/Tᵢ` along the chart morphism, which is the value that proposition has to
be computed from, is itself available:
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop` together with
`projAwayHom_apply_mk` evaluates it at `sⱼ/sᵢ`.

**No Stacks tag attribute is attached, and none is owed.** Tag 01NE is a representability
statement and nothing below is one of its assertions; Tag 01MN is the definition of the twisting
sheaf, and the trivialization of `𝒪(n)` on a standard open already carries Tag 01MS at
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit` and Tag 01MU at
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_isIso_on_whereInvertible`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections
open Stacks.SectionsToProjectiveSpace

universe u w

namespace Stacks.TwistPullbackChart

/-! ### The twist on the standard open of a degree-one element -/

section Degree

variable {C : Type u} {ρ : Type w} [CommRing C] [SetLike ρ C] [AddSubgroupClass ρ C]
  (𝒞 : ℕ → ρ) [GradedRing 𝒞]

/-- **`𝒪(n)` pulls back to the unit module on the standard open of a degree-one element**, for
every `n : ℤ` and with no divisibility condition.

This is the case `q = 1`, `e = 0` of
`Stacks.AlgebraicGeometry.ProjTwistMono.pullbackTwistIsoUnit`, whose trivializing section is
`(p/q)ⁿ` and so is `pⁿ` here. The transport is along `mul_one p`, the only difference between
`D₊(p · 1)` and `D₊(p)`. -/
noncomputable def degreeOnePullbackTwistIsoUnit {p : C} (hp : p ∈ 𝒞 1) (n : ℤ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.basicOpen 𝒞 p).ι).obj
        (twistingSheaf 𝒞 n) ≅
      SheafOfModules.unit (AlgebraicGeometry.Proj.basicOpen 𝒞 p).toScheme.ringCatSheaf :=
  mul_one p ▸ Stacks.AlgebraicGeometry.ProjTwistMono.pullbackTwistIsoUnit 𝒞
    (p := p) (q := 1) (e := 0) (by simpa using hp) SetLike.GradedOne.one_mem n

end Degree

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`𝒪(1)` on `ℙⁿ_ℤ` is the unit module on the standard chart `D₊(Tᵢ)`.** The variables are
homogeneous of degree one (`Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one`), so this is
the previous definition at `𝒜 = ℤ[T₀, …, Tₙ]`. -/
noncomputable def twistIsoUnitOnChart (n : ℕ) (i : Fin (n + 1)) :
    (Scheme.Modules.pullback
        (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).ι).obj
        (twistingSheafAtUniverse.{u} n) ≅
      SheafOfModules.unit
        (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
          (MvPolynomial.X i)).toScheme.ringCatSheaf :=
  degreeOnePullbackTwistIsoUnit (coordGrading.{u} n) (X_mem_coordGrading_one i) 1

/-! ### Factoring a pinned morphism through the standard chart -/

section Factor

variable {X : Scheme.{u}} {n : ℕ}

/-- **A spanning family one of whose members is `1` has its morphism to `ℙⁿ_ℤ` landing inside the
matching standard chart.** The preimage of `D₊(Tᵢ)` is the nonvanishing locus of `tᵢ`
(`Stacks.SectionsToProjectiveSpace.preimage_basicOpen`), which is everything when `tᵢ = 1`. -/
theorem range_subset_chart {W : Scheme.{u}} (t : Fin (n + 1) → Γ(W, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1)) (hti : t i = 1) :
    Set.range (toProjectiveSpaceAtUniverse t ht).base ⊆
      Set.range (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)).ι.base := by
  have hpre := preimage_basicOpen t ht i
  rw [hti, Scheme.basicOpen_one] at hpre
  rintro - ⟨x, rfl⟩
  have hx : (toProjectiveSpaceAtUniverse t ht).base x ∈
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
    have hmem : x ∈ toProjectiveSpaceAtUniverse t ht ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
      rw [hpre]; trivial
    exact hmem
  exact (Scheme.Opens.range_ι (U := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
    (MvPolynomial.X i))).ge hx

/-- The pinned restriction of `g` to a chart lands inside the standard chart `D₊(Tᵢ)`. -/
theorem range_comp_subset_chart (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (V : X.Opens)
    (t : Fin (n + 1) → Γ(V.toScheme, ⊤)) (ht : Ideal.span (Set.range t) = ⊤)
    (i : Fin (n + 1)) (hti : t i = 1)
    (hpin : V.ι ≫ g = toProjectiveSpaceAtUniverse t ht) :
    Set.range (V.ι ≫ g) ⊆
      Set.range (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)).ι := by
  rw [hpin]
  exact range_subset_chart t ht i hti

/-- **The pinned restriction of `g` to a chart, factored through `D₊(Tᵢ)`.** -/
noncomputable def chartFactor (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (V : X.Opens)
    (t : Fin (n + 1) → Γ(V.toScheme, ⊤)) (ht : Ideal.span (Set.range t) = ⊤)
    (i : Fin (n + 1)) (hti : t i = 1)
    (hpin : V.ι ≫ g = toProjectiveSpaceAtUniverse t ht) :
    V.toScheme ⟶ (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
      (MvPolynomial.X i)).toScheme :=
  IsOpenImmersion.lift (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
    (MvPolynomial.X i)).ι (V.ι ≫ g) (range_comp_subset_chart g V t ht i hti hpin)

/-- The factorization is a factorization. -/
theorem chartFactor_fac (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (V : X.Opens)
    (t : Fin (n + 1) → Γ(V.toScheme, ⊤)) (ht : Ideal.span (Set.range t) = ⊤)
    (i : Fin (n + 1)) (hti : t i = 1)
    (hpin : V.ι ≫ g = toProjectiveSpaceAtUniverse t ht) :
    chartFactor g V t ht i hti hpin ≫ (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
      (MvPolynomial.X i)).ι = V.ι ≫ g :=
  IsOpenImmersion.lift_fac _ _ _

/-- **`g ^* 𝒪(1)` restricted to a chart that `g` sends into `D₊(Tᵢ)` is the unit module.**

This is the `𝒪(1)` half of the twist comparison of [Stacks, Tag 01NE]: the chart factorization
carries the trivialization of `𝒪(1)` on `D₊(Tᵢ)` back along `g`, by
`Stacks.AlgebraicGeometry.ProjTwistMono.restrictPullbackIsoUnit`. No hypothesis on `g` beyond
the pinning is used — no ampleness, no finite type, no immersion. -/
noncomputable def pullbackTwistRestrictIsoUnit (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (V : X.Opens) (t : Fin (n + 1) → Γ(V.toScheme, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1)) (hti : t i = 1)
    (hpin : V.ι ≫ g = toProjectiveSpaceAtUniverse t ht) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjTwistMono.restrictPullbackIsoUnit g V
    (twistingSheafAtUniverse.{u} n)
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (chartFactor g V t ht i hti hpin) (chartFactor_fac g V t ht i hti hpin)
    (twistIsoUnitOnChart n i)

end Factor

/-! ### The charts `X_{sᵢ}` of a pinned morphism -/

/-- **`g ^* 𝒪(1)` is the unit module on each chart `X_{sᵢ}` of a pinned morphism.**

The chart is `Stacks.ProjectiveFromSections.nvCover s i`, the family is the ratio family
`Stacks.ProjectiveFromSections.chartRatio s i`, and the hypothesis `tᵢ = 1` is
`Stacks.ProjectiveFromSections.chartRatio_self`. The pinning hypothesis is verbatim the last
clause of `Stacks.AmpleImmersionReduction.TwistPullback` after
`Stacks.AmpleProjectiveImmersion.liftOver_snd`, so this applies to the morphism that
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` produces. -/
noncomputable def pullbackTwistRestrictIsoUnitChart {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    (Scheme.Modules.restrictFunctor (nvCover s i).ι).obj
        ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)) ≅
      SheafOfModules.unit (nvCover s i).toScheme.ringCatSheaf :=
  pullbackTwistRestrictIsoUnit g (nvCover s i) (chartRatio s i) (span_range_chartRatio s i) i
    (chartRatio_self s i) hpin

end Stacks.TwistPullbackChart

end
