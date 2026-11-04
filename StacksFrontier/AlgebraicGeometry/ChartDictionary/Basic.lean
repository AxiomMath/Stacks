module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
public import StacksFrontier.AlgebraicGeometry.ChartImmersionAssembly.Basic

/-!
# The chart dictionary: `Tₖ/Tᵢ` goes to the `k`-th coordinate ratio

Step 4 of the proof of [Stacks, Tag 01VS] compares coordinates on the `i`-th chart. This file
computes what the restricted morphism

`X_{sᵢ} ⟶ D₊(Tᵢ) ⊓ pr⁻¹(V)`

does to the chart coordinate `Tₖ/Tᵢ`: **it sends `Tₖ/Tᵢ` to the coordinate ratio `sₖ/sᵢ`** of
`Stacks.ProjectiveFromSections.ratio`, and sends a section of `𝒪_S(V)` to its image under the
structure map of the chart. Surjectivity of the chart's ring map is then a generation statement
about the ratios, which gives the chart-local condition consumed by
`Stacks.ChartImmersionAssembly.isImmersion_of_isImmersion_chartOverRestrict` and
`Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart`.

## The route

`Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse` identifies the restriction of
the pinned morphism to `D₊(Tᵢ)` with Mathlib's
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, and
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop` computes that morphism on
sections as `Stacks.ProjGlobalSectionsAppTop.projAwayHom`, whose value on a fraction `p / tᵏ` is
`Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk`. Composing the three gives the dictionary at
the integral model, `Stacks.ChartDictionary.appLE_chartCoord`. Specialising to the chart family
`Stacks.ProjectiveFromSections.chartRatio`, whose `i`-th member is `1`
(`Stacks.ProjectiveFromSections.chartRatio_self`), makes the nonvanishing locus the whole chart and
clears the denominator: `Stacks.ChartDictionary.appLE_chartCoord_top`. Transporting along the
pinning hypothesis and the two projections of `ℙⁿ_S` gives
`Stacks.ChartDictionary.appLE_chartCoordOver` and
`Stacks.ChartDictionary.appLE_chartCoordChart`.

`AlgebraicGeometry.Scheme.Hom.appLE` is used throughout rather than
`AlgebraicGeometry.Scheme.Hom.appTop` of a restriction: it carries the two opens in its type and
no `AlgebraicGeometry.Scheme.Opens.topIso` transport, and
`Stacks.ProjGlobalSectionsAppTop.topIso_inv_resLE_appTop` converts to the `appTop` form where it is
needed.

## That the chart is affine

The chart-local condition is a condition on a ring map only because `D₊(Tᵢ) ⊓ pr⁻¹(V)` is affine
for affine `V`, and that is proved here too, as
`Stacks.ChartDictionary.isAffineOpen_chartOpenOver`. The reason is a base change: the `i`-th chart
of `ℙⁿ_S` over `S` is the base change of `D₊(Tᵢ) ⟶ Spec ℤ` along `S ⟶ Spec ℤ`, hence an affine
morphism, so the preimage of an affine open of `S` in it is affine.

## Main definitions

* `Stacks.ChartDictionary.awayCoord`: the chart coordinate `Tₖ/Tᵢ` as a degree-zero fraction in
  `(ℤ[T₀, …, Tₙ]_{Tᵢ})₀`.
* `Stacks.ChartDictionary.chartCoord`, `chartCoordOver`, `chartCoordChart`: that coordinate as a
  section of the structure sheaf over `D₊(Tᵢ)` of `ℙⁿ_ℤ`, over the `i`-th chart of `ℙⁿ_S`, and over
  that chart cut down by `pr⁻¹(V)`.

## Main results

* `Stacks.ChartDictionary.appLE_chartCoord`, `appLE_chartCoord_top`: **the dictionary at the
  integral model.**
* `Stacks.ChartDictionary.appLE_chartCoordOver`, `appLE_chartCoordChart`: **the dictionary** —
  the ring map of the chart sends `Tₖ/Tᵢ` to `Stacks.ProjectiveFromSections.ratio s i k`.
* `Stacks.ChartDictionary.appLE_baseSection`: the other half — on `𝒪_S(V)` the ring map is the
  structure map `f.appLE V (X_{sᵢ})` of the chart over the base.
* `Stacks.ChartDictionary.isAffineHom_standardChart_over`,
  `Stacks.ChartDictionary.isAffineOpen_chartOpenOver`: **`D₊(Tᵢ) ⊓ pr⁻¹(V)` is affine.**
* `Stacks.ChartDictionary.surjective_appLE_chartOpenOver`: **the chart's ring map is surjective**
  as soon as the ratios together with the base sections generate the sections of `X_{sᵢ}`.
* `Stacks.ChartDictionary.isClosedImmersion_resLE_chartOpenOver`,
  `Stacks.ChartDictionary.exists_isImmersion_standardChart`: the chart-local closed immersion and
  the chartwise immersion condition that step 4 consumes.
* `Stacks.ChartDictionary.isImmersion_of_closure`: **the chart route of [Stacks, Tag 01VS] through
  step 4**, leaving only the generation hypothesis.

## What is not done

**No Stacks attribute is claimed.** Nothing here is a tagged statement: the results it unlocks
carry their own tags elsewhere.

The generation hypothesis of `Stacks.ChartDictionary.isImmersion_of_closure` is not discharged
here. It is stated as membership in `Subring.closure` of the base sections together with **all**
the ratios, so a generating subset of them suffices, and
`Stacks.ChartDictionary.mem_closure_of_adjoin_eq_top` turns an `Algebra.adjoin` statement into it.
Supplying it from [Stacks, Tag 01T2] and [Stacks, Tag 01PW], and re-indexing the equalised family
of `Stacks.ChartDegreeEqualisation.exists_family_ratio_eq`, is
`Stacks.ChartImmersionFinish.chartImmersion`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomogeneousLocalization
open Stacks.ProjectiveFromSections Stacks.ProjGlobalSectionsAppTop
open Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.ChartDictionary

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/-! ### The chart coordinate -/

/-- **The chart coordinate `Tₖ/Tᵢ`**, as a degree-zero fraction in `(ℤ[T₀, …, Tₙ]_{Tᵢ})₀`: the
numerator is the variable `Tₖ`, homogeneous of degree one, and the denominator is the first power
of `Tᵢ`. -/
def awayCoord (n : ℕ) (i k : Fin (n + 1)) :
    Away (coordGrading.{u} n) (MvPolynomial.X i) :=
  Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_coordGrading_one k)

/-- **The chart coordinate `Tₖ/Tᵢ` as a section of `𝒪` over `D₊(Tᵢ)` of `ℙⁿ_ℤ`**, through
Mathlib's identification `AlgebraicGeometry.Proj.basicOpenIsoAway` of the degree-zero localization
with the sections over the standard open. -/
def chartCoord (n : ℕ) (i k : Fin (n + 1)) :
    Γ(projectiveSpaceAtUniverse.{u} n,
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :=
  (Proj.basicOpenIsoAway (coordGrading.{u} n) (MvPolynomial.X i)
    (X_mem_coordGrading_one i) Nat.one_pos).hom (awayCoord.{u} n i k)

/-! ### The dictionary at the integral model -/

variable {Y : Scheme.{u}}

/-- The nonvanishing locus of the `i`-th section lies in the preimage of `D₊(Tᵢ)` — with equality,
by `Stacks.SectionsToProjectiveSpace.preimage_basicOpen`. This is the inclusion of opens the chart
morphism is `AlgebraicGeometry.Scheme.Hom.appLE` along. -/
theorem preimage_le (s : Fin (n + 1) → Γ(Y, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (i : Fin (n + 1)) :
    Y.basicOpen (sectionsHom s (MvPolynomial.X i)) ≤
      toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :=
  (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom s)
    (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one i)).ge

/-- **The chart morphism on sections is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`**, read
through `AlgebraicGeometry.Proj.basicOpenIsoAway`. This is
`Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse` composed with
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`, with the
`AlgebraicGeometry.Scheme.Opens.topIso` on the source cancelled. -/
theorem basicOpenIsoAway_hom_appLE (s : Fin (n + 1) → Γ(Y, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (i : Fin (n + 1)) :
    (Proj.basicOpenIsoAway (coordGrading.{u} n) (MvPolynomial.X i)
        (X_mem_coordGrading_one i) Nat.one_pos).hom ≫
      (toProjectiveSpaceAtUniverse s hs).appLE
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) (preimage_le s hs i) =
      CommRingCat.ofHom (projAwayHom (coordGrading.{u} n) (sectionsHom s)) := by
  have h1 : (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).topIso.inv ≫
      (Proj.toBasicOpenOfGlobalSections (coordGrading.{u} n) (sectionsHom s) rfl Nat.one_pos
        (X_mem_coordGrading_one i)).appTop =
      (toProjectiveSpaceAtUniverse s hs).appLE
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) (preimage_le s hs i) ≫
      (Y.basicOpen (sectionsHom s (MvPolynomial.X i))).topIso.inv :=
    (congrArg (fun q : (Y.basicOpen (sectionsHom s (MvPolynomial.X i))).toScheme ⟶
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).toScheme =>
      (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)).topIso.inv ≫ q.appTop)
      (resLE_toProjectiveSpaceAtUniverse s hs i)).symm.trans
        (topIso_inv_resLE_appTop (toProjectiveSpaceAtUniverse s hs) (preimage_le s hs i))
  have h2 := toBasicOpenOfGlobalSections_appTop (coordGrading.{u} n) (sectionsHom s)
    Nat.one_pos (X_mem_coordGrading_one i)
  refine (cancel_mono (Y.basicOpen (sectionsHom s (MvPolynomial.X i))).topIso.inv).mp ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Proj.basicOpenIsoAway (coordGrading.{u} n) (MvPolynomial.X i)
      (X_mem_coordGrading_one i) Nat.one_pos).hom ≫ z) h1.symm).trans h2)

/-- **The dictionary at the integral model**: the morphism `X ⟶ ℙⁿ_ℤ` of a family `s` of global
sections spanning the unit ideal sends the chart coordinate `Tₖ/Tᵢ` to `sₖ · sᵢ⁻¹` over the
nonvanishing locus of `sᵢ`. -/
theorem appLE_chartCoord (s : Fin (n + 1) → Γ(Y, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (i k : Fin (n + 1)) :
    ((toProjectiveSpaceAtUniverse s hs).appLE
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) (preimage_le s hs i)).hom
      (chartCoord.{u} n i k) =
      resTop (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) (s k) *
        resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i)) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (basicOpenIsoAway_hom_appLE s hs i) (awayCoord.{u} n i k)
  simp only [CommRingCat.hom_ofHom] at h
  refine h.trans (Eq.trans (projAwayHom_apply_mk (coordGrading.{u} n) (sectionsHom s)
    (X_mem_coordGrading_one i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_coordGrading_one k)) ?_)
  rw [sectionsHom_X s k, pow_one]

/-- Restriction of a global section to `⊤` is the section. -/
theorem resTop_top (a : Γ(Y, ⊤)) : resTop (⊤ : Y.Opens) a = a := by
  simp [resTop]

/-- **The dictionary at the integral model, on the whole of `Y`**, when the `i`-th section is
the unit. -/
theorem appLE_chartCoord_top (s : Fin (n + 1) → Γ(Y, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    {i : Fin (n + 1)} (hi : s i = 1) (k : Fin (n + 1))
    (e : (⊤ : Y.Opens) ≤ toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :
    ((toProjectiveSpaceAtUniverse s hs).appLE
      (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ e).hom
      (chartCoord.{u} n i k) = s k := by
  have hB : Y.basicOpen (sectionsHom s (MvPolynomial.X i)) = ⊤ := by
    rw [sectionsHom_X, hi, Scheme.basicOpen_one]
  have hstep := Scheme.Hom.appLE_map (toProjectiveSpaceAtUniverse s hs)
    (U := Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) (preimage_le s hs i)
    (homOfLE hB.ge).op
  have happ := CategoryTheory.ConcreteCategory.congr_hom hstep (chartCoord.{u} n i k)
  simp only [CommRingCat.hom_comp] at happ
  have hres : ∀ a : Γ(Y, ⊤), (Y.presheaf.map (homOfLE hB.ge).op).hom
      (resTop (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) a) = a := fun a => by
    rw [resTop_resTop hB.ge a, resTop_top]
  have hden : (Y.presheaf.map (homOfLE hB.ge).op).hom
      (resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i))) = 1 := by
    have hv : resTop (Y.basicOpen (sectionsHom s (MvPolynomial.X i)))
          (sectionsHom s (MvPolynomial.X i)) *
        resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i)) = 1 :=
      (isUnit_resTop_basicOpen _).unit.mul_inv
    have h1 := congrArg (Y.presheaf.map (homOfLE hB.ge).op).hom hv
    rw [map_mul, map_one, hres] at h1
    exact (one_mul _).symm.trans (congrArg (· * _) ((sectionsHom_X s i).trans hi).symm |>.trans h1)
  have hfinal : (Y.presheaf.map (homOfLE hB.ge).op).hom
      (resTop (Y.basicOpen (sectionsHom s (MvPolynomial.X i))) (s k) *
        resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i))) = s k := by
    rw [map_mul, hres, hden, mul_one]
  exact happ.symm.trans ((congrArg (fun z => (Y.presheaf.map (homOfLE hB.ge).op).hom z)
    (appLE_chartCoord s hs i k)).trans hfinal)

/-! ### The dictionary over a base scheme -/

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **The chart coordinate `Tₖ/Tᵢ` as a section over the `i`-th standard chart of `ℙⁿ_S`**, pulled
back along the projection to the integral model. -/
def chartCoordOver (n : ℕ) (S : Scheme.{u}) (i k : Fin (n + 1)) :
    Γ(projectiveSpaceOver n S, projectiveSpaceOver.standardChart n S i) :=
  ((projectiveSpaceOver.toIntegralAtUniverse n S).appLE
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (projectiveSpaceOver.standardChart n S i) le_rfl).hom (chartCoord.{u} n i k)

/-- The inclusion of an open subscheme, on sections over that open, is
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem ι_appLE_top (U : X.Opens) (e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ e = U.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- Two equal morphisms have the same effect on sections. -/
theorem appLE_congr {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') (W : Z.Opens) (T : Y.Opens)
    (e : T ≤ g ⁻¹ᵁ W) (e' : T ≤ g' ⁻¹ᵁ W) : g.appLE W T e = g'.appLE W T e' := by
  subst h; rfl

/-- **The dictionary.** For a morphism `p : X ⟶ ℙⁿ_S` pinned on the `i`-th chart by the ratio
family of a family `s` of global sections of an invertible `L`, the ring map of the `i`-th standard
chart sends the chart coordinate `Tₖ/Tᵢ` to the coordinate ratio `sₖ/sᵢ`. -/
theorem appLE_chartCoordOver (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (e : nvCover s i ≤ p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i) (k : Fin (n + 1)) :
    (p.appLE (projectiveSpaceOver.standardChart n S i) (nvCover s i) e).hom
      (chartCoordOver.{u} n S i k) = ratio s i k := by
  have etop : (⊤ : (nvCover s i).toScheme.Opens) ≤ (nvCover s i).ι ⁻¹ᵁ nvCover s i := by
    intro x _; exact x.2
  have epq : nvCover s i ≤ (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := e
  have etop' : (⊤ : (nvCover s i).toScheme.Opens) ≤
      ((nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
    intro x _; exact epq x.2
  have hpre : toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i) ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) = ⊤ := by
    rw [preimage_basicOpen, chartRatio_self, Scheme.basicOpen_one]
  have h1 := Scheme.Hom.appLE_comp_appLE p (projectiveSpaceOver.toIntegralAtUniverse n S)
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (projectiveSpaceOver.standardChart n S i) (nvCover s i) le_rfl e
  have h2 := Scheme.Hom.appLE_comp_appLE (nvCover s i).ι
    (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) (nvCover s i) ⊤ epq etop
  have h3 : ((nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S).appLE
      (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ etop' =
      (toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)).appLE
        (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ hpre.ge :=
    appLE_congr hchart _ _ etop' hpre.ge
  have key : ((nvCover s i).topIso.inv).hom
      ((p.appLE (projectiveSpaceOver.standardChart n S i) (nvCover s i) e).hom
        (chartCoordOver.{u} n S i k)) = chartRatio s i k := by
    have ha := CategoryTheory.ConcreteCategory.congr_hom h1 (chartCoord.{u} n i k)
    have hb := CategoryTheory.ConcreteCategory.congr_hom h2 (chartCoord.{u} n i k)
    have hc := CategoryTheory.ConcreteCategory.congr_hom h3 (chartCoord.{u} n i k)
    have hd := appLE_chartCoord_top (chartRatio s i) (span_range_chartRatio s i)
      (chartRatio_self s i) k hpre.ge
    have hι : ((nvCover s i).topIso.inv).hom = ((nvCover s i).ι.appLE
        (nvCover s i) ⊤ etop).hom :=
      congrArg CommRingCat.Hom.hom (ι_appLE_top (nvCover s i) etop).symm
    rw [hι]
    exact (congrArg (fun z => ((nvCover s i).ι.appLE (nvCover s i) ⊤ etop).hom z) ha).trans
      (hb.trans (hc.trans hd))
  exact (ConcreteCategory.bijective_of_isIso (nvCover s i).topIso.inv).1 key

/-! ### The chart cut down over an open of the base -/

/-- The chart cut down over an open of the base lies in the chart. -/
theorem chartOpenOver_le_standardChart (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) (V : S.Opens) :
    Stacks.ChartImmersionAssembly.chartOpenOver n S i V ≤
      projectiveSpaceOver.standardChart n S i := inf_le_left

/-- The chart cut down over an open `V` of the base lies over `V`. -/
theorem chartOpenOver_le_preimage (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) (V : S.Opens) :
    Stacks.ChartImmersionAssembly.chartOpenOver n S i V ≤
      pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) ⁻¹ᵁ V := inf_le_right

/-- **The chart coordinate `Tₖ/Tᵢ` as a section over `D₊(Tᵢ) ⊓ pr⁻¹(V)`**, by restriction from
the whole chart. -/
def chartCoordChart (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) (V : S.Opens) (k : Fin (n + 1)) :
    Γ(projectiveSpaceOver n S, Stacks.ChartImmersionAssembly.chartOpenOver n S i V) :=
  ((projectiveSpaceOver n S).presheaf.map
    (homOfLE (chartOpenOver_le_standardChart n S i V)).op).hom (chartCoordOver.{u} n S i k)

/-- **The dictionary on the chart cut down over the base**: the `k`-th chart coordinate goes to
the `k`-th ratio. -/
theorem appLE_chartCoordChart (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : S.Opens)
    (e : nvCover s i ≤ p ⁻¹ᵁ Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
    (k : Fin (n + 1)) :
    (p.appLE (Stacks.ChartImmersionAssembly.chartOpenOver n S i V) (nvCover s i) e).hom
      (chartCoordChart.{u} n S i V k) = ratio s i k := by
  have h := Scheme.Hom.map_appLE p e (homOfLE (chartOpenOver_le_standardChart n S i V)).op
  exact (CategoryTheory.ConcreteCategory.congr_hom h (chartCoordOver.{u} n S i k)).trans
    (appLE_chartCoordOver s p i hchart _ k)

/-- **The dictionary on the base**: the ring map is the structure map of the chart over `Vᵢ`. -/
theorem appLE_baseSection (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}} {f : X ⟶ S}
    (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (i : Fin (n + 1)) (V : S.Opens) (hle : nvCover s i ≤ f ⁻¹ᵁ V)
    (e : nvCover s i ≤ p ⁻¹ᵁ Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
    (r : Γ(S, V)) :
    (p.appLE (Stacks.ChartImmersionAssembly.chartOpenOver n S i V) (nvCover s i) e).hom
      (((pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))).appLE V
          (Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
          (chartOpenOver_le_preimage n S i V)).hom r) =
      (f.appLE V (nvCover s i) hle).hom r := by
  have h := Scheme.Hom.appLE_comp_appLE p
    (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
    V (Stacks.ChartImmersionAssembly.chartOpenOver n S i V) (nvCover s i)
    (chartOpenOver_le_preimage n S i V) e
  exact (CategoryTheory.ConcreteCategory.congr_hom h r).trans
    (CategoryTheory.ConcreteCategory.congr_hom (appLE_congr hpf V (nvCover s i) _ hle) r)

/-- **The ring map of the chart is surjective** as soon as the ratios together with the base
sections generate the sections of the chart. -/
theorem surjective_appLE_chartOpenOver (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}} {f : X ⟶ S}
    (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : S.Opens) (hle : nvCover s i ≤ f ⁻¹ᵁ V)
    (e : nvCover s i ≤ p ⁻¹ᵁ Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
    (hgen : ∀ y : Γ(X, nvCover s i), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE V (nvCover s i) hle).hom r) ∪ Set.range (ratio s i))) :
    Function.Surjective
      (p.appLE (Stacks.ChartImmersionAssembly.chartOpenOver n S i V) (nvCover s i) e).hom := by
  have hsub : Subring.closure
      (Set.range (fun r => (f.appLE V (nvCover s i) hle).hom r) ∪ Set.range (ratio s i)) ≤
      (p.appLE (Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
        (nvCover s i) e).hom.range := by
    refine Subring.closure_le.mpr ?_
    rintro z (⟨r, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨_, appLE_baseSection s p hpf i V hle e r⟩
    · exact ⟨_, appLE_chartCoordChart s p i hchart V e k⟩
  exact fun y => hsub (hgen y)

/-! ### The chart over an affine open of the base is affine -/

/-- **The `i`-th standard chart of `ℙⁿ_S` is affine over `S`.** The chart is the base change of
the affine `D₊(Tᵢ) ⟶ Spec ℤ` along `S ⟶ Spec ℤ`, and affine morphisms are stable under base
change. -/
instance isAffineHom_standardChart_over (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) :
    IsAffineHom ((projectiveSpaceOver.standardChart n S i).ι ≫
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
  have sqA := isPullback_morphismRestrict (projectiveSpaceOver.toIntegralAtUniverse n S)
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
  have sqB : IsPullback (projectiveSpaceOver.toIntegralAtUniverse n S)
      (pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) (terminal.from S) :=
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
  have hD : IsAffine ((Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :
      (projectiveSpaceAtUniverse.{u} n).Opens)).toScheme :=
    Proj.isAffineOpen_basicOpen (coordGrading.{u} n) (MvPolynomial.X i)
      (X_mem_coordGrading_one i) Nat.one_pos
  have hterm : (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :
        (projectiveSpaceAtUniverse.{u} n).Opens).ι ≫
      terminal.from (projectiveSpaceAtUniverse.{u} n) =
      terminal.from (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :
        (projectiveSpaceAtUniverse.{u} n).Opens).toScheme :=
    terminal.hom_ext _ _
  have hg : IsAffineHom ((Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :
      (projectiveSpaceAtUniverse.{u} n).Opens).ι ≫
      terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
    hterm ▸ inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (sqA.paste_vert sqB) hg

/-- **`D₊(Tᵢ) ⊓ pr⁻¹(V)` is an affine open of `ℙⁿ_S` for an affine open `V` of `S`.** -/
theorem isAffineOpen_chartOpenOver (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) {V : S.Opens}
    (hV : IsAffineOpen V) :
    IsAffineOpen (Stacks.ChartImmersionAssembly.chartOpenOver n S i V) := by
  have hpre := hV.preimage ((projectiveSpaceOver.standardChart n S i).ι ≫
    pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
  have himg := hpre.image_of_isOpenImmersion (projectiveSpaceOver.standardChart n S i).ι
  have heq : (projectiveSpaceOver.standardChart n S i).ι ''ᵁ
      (((projectiveSpaceOver.standardChart n S i).ι ≫
        pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n))) ⁻¹ᵁ V) =
      Stacks.ChartImmersionAssembly.chartOpenOver n S i V := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    rfl
  exact heq ▸ himg

/-! ### The chart-local closed immersion -/

/-- Surjectivity on sections transports from `AlgebraicGeometry.Scheme.Hom.appLE` to
`AlgebraicGeometry.Scheme.Hom.appTop` of the restricted morphism. -/
theorem surjective_appTop_resLE_of_surjective {Y Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens}
    {T : Y.Opens} (e : T ≤ g ⁻¹ᵁ W) (h : Function.Surjective (g.appLE W T e).hom) :
    Function.Surjective ((g.resLE W T e).appTop).hom := by
  intro y
  obtain ⟨x, hx⟩ := h ((T.topIso.hom).hom y)
  refine ⟨(W.topIso.inv).hom x, ?_⟩
  have hkey := CategoryTheory.ConcreteCategory.congr_hom (topIso_inv_resLE_appTop g e) x
  have hy : (T.topIso.inv).hom ((T.topIso.hom).hom y) = y :=
    CategoryTheory.ConcreteCategory.congr_hom T.topIso.hom_inv_id y
  exact hkey.trans ((congrArg (T.topIso.inv).hom hx).trans hy)

/-- **`X_{sᵢ}` lies in the preimage of `D₊(Tᵢ) ⊓ pr⁻¹(Vᵢ)`.** -/
theorem nvCover_le_preimage_chartOpenOver (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (V : S.Opens) (hle : nvCover s i ≤ f ⁻¹ᵁ V) :
    nvCover s i ≤ p ⁻¹ᵁ Stacks.ChartImmersionAssembly.chartOpenOver n S i V := by
  rw [Stacks.ChartImmersionAssembly.chartOpenOver, Scheme.Hom.preimage_inf]
  refine le_inf
    (Stacks.ChartImmersionAssembly.nvCover_le_preimage_chartOpen s p i hchart) ?_
  rwa [← Scheme.Hom.comp_preimage, hpf]

/-- **The chart-local morphism `X_{sᵢ} ⟶ D₊(Tᵢ) ⊓ pr⁻¹(Vᵢ)` is a closed immersion** as soon as the
ratios `s_k/sᵢ` together with the sections of `𝒪_S(Vᵢ)` generate `𝒪_X(X_{sᵢ})`. Both schemes are
affine — the source by hypothesis, the target by
`Stacks.ChartDictionary.isAffineOpen_chartOpenOver` — and the ring map is surjective by the
dictionary. -/
theorem isClosedImmersion_resLE_chartOpenOver (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    {V : S.Opens} (hV : IsAffineOpen V) (hle : nvCover s i ≤ f ⁻¹ᵁ V)
    (haff : IsAffineOpen (nvCover s i))
    (hgen : ∀ y : Γ(X, nvCover s i), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE V (nvCover s i) hle).hom r) ∪ Set.range (ratio s i))) :
    IsClosedImmersion (p.resLE (Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
      (nvCover s i) (nvCover_le_preimage_chartOpenOver s p hpf i hchart V hle)) := by
  have h1 : IsAffine (nvCover s i).toScheme := haff
  have h2 : IsAffine (Stacks.ChartImmersionAssembly.chartOpenOver n S i V).toScheme :=
    isAffineOpen_chartOpenOver n S i hV
  exact IsClosedImmersion.of_surjective_of_isAffine _
    (surjective_appTop_resLE_of_surjective p _
      (surjective_appLE_chartOpenOver s p hpf i hchart V hle _ hgen))

/-- **The chartwise immersion condition of step 4 of [Stacks, Tag 01VS], from the generation
hypothesis.** -/
theorem exists_isImmersion_standardChart (s : Fin (n + 1) → Γ(L, ⊤)) {S : Scheme.{u}}
    {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (i : Fin (n + 1))
    (hchart : (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    {V : S.Opens} (hV : IsAffineOpen V) (hle : nvCover s i ≤ f ⁻¹ᵁ V)
    (haff : IsAffineOpen (nvCover s i))
    (hgen : ∀ y : Γ(X, nvCover s i), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE V (nvCover s i) hle).hom r) ∪ Set.range (ratio s i))) :
    ∃ g : (nvCover s i).toScheme ⟶ (projectiveSpaceOver.standardChart n S i).toScheme,
      IsImmersion g ∧
        g ≫ (projectiveSpaceOver.standardChart n S i).ι = (nvCover s i).ι ≫ p := by
  have := isClosedImmersion_resLE_chartOpenOver s p hpf i hchart hV hle haff hgen
  exact Stacks.AmpleImmersionReduction.exists_isImmersion_standardChart_of_isClosedImmersion_le
    s p i (Stacks.ChartImmersionAssembly.chartOpenOver n S i V)
    (chartOpenOver_le_standardChart n S i V) _ (Scheme.Hom.resLE_comp_ι _ _)

/-- **The generation hypothesis from an `Algebra.adjoin` statement.** If a subset `T` of the
ratios generates `𝒪_X(X_{sᵢ})` as an algebra over `𝒪_S(Vᵢ)`, then every section lies in the
subring generated by the base sections together with all the ratios. -/
theorem mem_closure_of_adjoin_eq_top {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {T U : Set A} (hTU : T ⊆ U) (h : Algebra.adjoin R T = ⊤) (x : A) :
    x ∈ Subring.closure (Set.range (algebraMap R A) ∪ U) := by
  have hx : x ∈ Algebra.adjoin R T := h ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Subring.subset_closure (Or.inr (hTU hy))
  | algebraMap r => exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

/-- **The chart route of [Stacks, Tag 01VS] through step 4, with only the generation hypothesis
left.** A morphism to `ℙⁿ_S` pinned on the charts of a generating family whose charts are affine
and map into affine opens of `S` is an immersion, as soon as on each chart the ratios together with
the base sections generate the sections. -/
theorem isImmersion_of_closure (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
    {S : Scheme.{u}} {f : X ⟶ S} (p : X ⟶ projectiveSpaceOver n S)
    (hpf : p ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (hchart : ∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (haff : ∀ i, IsAffineOpen (nvCover s i))
    (V : Fin (n + 1) → S.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hle : ∀ i, nvCover s i ≤ f ⁻¹ᵁ V i)
    (hgen : ∀ i, ∀ y : Γ(X, nvCover s i), y ∈ Subring.closure
      (Set.range (fun r => (f.appLE (V i) (nvCover s i) (hle i)).hom r) ∪
        Set.range (ratio s i))) :
    IsImmersion p :=
  Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart s hs p hchart
    fun i => exists_isImmersion_standardChart s p hpf i (hchart i) (hV i) (hle i) (haff i)
      (hgen i)

end Stacks.ChartDictionary

end
