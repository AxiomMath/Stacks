module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic

/-!
# The standard charts of the morphism to projective space, and step 4 of Stacks Tag 01VS

Step 4 of the proof of [Stacks, Tag 01VS] has two halves. The first is a comparison of
coordinates: for the morphism `p : X ⟶ ℙⁿ_S` attached by [Stacks, Tag 01NE] to a generating family
`s₀, …, sₙ` of global sections of an invertible `𝒪_X`-module, the preimage of the `i`-th standard
chart of `ℙⁿ_S` is exactly the nonvanishing open `X_{sᵢ}`. The second is an assembly: given that, a
morphism which is an immersion into each standard chart is an immersion.

Both halves are proved here, unconditionally in ampleness and in the finite type hypothesis.
Together they localise `Stacks.AmpleImmersionReduction.ChartImmersion` — one of the four named
inputs of `StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/Basic.lean` — to
`Stacks.AmpleImmersionReduction.ChartwiseImmersion`, which says only that the restriction of `p` to
each chart `X_{sᵢ}` is an immersion into the `i`-th chart of `ℙⁿ_S`. The two are *equivalent*; what
the localisation buys is that the surviving condition is local on the target, hence — the charts
being affine for the family step 1 produces — a statement about a ring map, which is the form step
2 of the source answers it in. No claim is made that it is a smaller statement.

## The comparison of coordinates

The morphism is pinned on every chart: on `X_{s_k}` it is the morphism attached to the ratio family
`sⱼ / s_k`, which is what
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` produces. The
preimage of `D₊(Tᵢ)` under *that* morphism is the basic open of its `i`-th member
(`Stacks.SectionsToProjectiveSpace.preimage_basicOpen`), namely `X.basicOpen (sᵢ / s_k)`, and that
basic open is `X_{sᵢ} ⊓ X_{s_k}` by
`Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen`. So

`p ⁻¹ᵁ (i-th chart) ⊓ X_{s_k} = X_{sᵢ} ⊓ X_{s_k}` for every `k`,

and the `X_{s_k}` cover `X`, which gives the identification. **Every chart is used to identify one
chart**: the inclusion `X_{sᵢ} ≤ p ⁻¹ᵁ (i-th chart)` needs only `k = i` and `sᵢ / sᵢ = 1`, but the
reverse inclusion needs the pinning at every `k`.

## The assembly

`AlgebraicGeometry.IsImmersion` is Zariski local on the target, and the standard charts cover
`ℙⁿ_S` because the variables span the irrelevant ideal of `ℤ[T₀, …, Tₙ]` — every homogeneous
polynomial of positive degree lies in the ideal they generate, since
`MvPolynomial.homogeneousSubmodule` in degree one is their span. An immersion into the `i`-th chart
followed by the open immersion of that chart is an immersion, so locality concludes. This is the
source's appeal to [Stacks, Tag 02V0].

The chartwise condition asks for an *immersion*, not a closed immersion: step 2 of the source
produces a closed immersion into the affine open `Vᵢ ×_ℤ D₊(Tᵢ)` of the `i`-th chart, whose image
need not be closed in the whole chart. Asking for a closed immersion there would be a condition the
source's own argument does not supply.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOver.standardChart`: the `i`-th standard chart of `ℙⁿ_S`, the
  preimage of `D₊(Tᵢ)` along the projection to the integral model.
* `Stacks.AmpleImmersionReduction.ChartwiseImmersion`: the input that replaces
  `Stacks.AmpleImmersionReduction.ChartImmersion`.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.iSup_standardChart`: the standard charts cover `ℙⁿ_S`.
* `Stacks.AmpleImmersionReduction.preimage_standardChart`: **the comparison of coordinates**,
  `p ⁻¹ᵁ (i-th chart) = X_{sᵢ}`.
* `Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart`: **step 4** — a pinned
  morphism all of whose chart restrictions are immersions is an immersion.
* `Stacks.AmpleImmersionReduction.isImmersion_standardChart_of_isImmersion`: its converse, so that
  step 4 is an equivalence and no claim of a smaller statement is made.
* `Stacks.AmpleImmersionReduction.exists_isImmersion_standardChart_of_isClosedImmersion_le`: the
  chartwise condition from a closed immersion into an open part of the chart, which is the shape
  step 2 of the source delivers.
* `Stacks.AmpleImmersionReduction.chartImmersion_of_chartwiseImmersion`:
  `ChartwiseImmersion f L → ChartImmersion f L`, hence through
  `Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist` a reduction of
  `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` in which `ChartImmersion` is replaced by
  `ChartwiseImmersion`.

## Implementation notes

The chart restriction is presented as a *factorisation* — a morphism `X_{sᵢ} ⟶ (i-th chart)`
composing with the chart's inclusion to `(X_{sᵢ}).ι ≫ p` — rather than as
`AlgebraicGeometry.Scheme.Hom.resLE`. The two agree, the inclusion of an open being a
monomorphism, but the factorisation form carries no inequality of opens in its type and so needs no
transport along `Stacks.AmpleImmersionReduction.preimage_standardChart`.

The two `CategoryTheory.MorphismProperty` instances built inside the assembly are the ones instance
search does not find for `AlgebraicGeometry.IsImmersion` against
`AlgebraicGeometry.IsOpenImmersion`; only the `⊤`-flavoured
`CategoryTheory.MorphismProperty.HasOfPostcompProperty` is registered in Mathlib.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 02V0](https://stacks.math.columbia.edu/tag/02V0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionsToProjectiveSpace

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The `i`-th standard chart of `ℙⁿ_S`**: the preimage of the standard open `D₊(Tᵢ)` of the
integral model along the projection `ℙⁿ_S ⟶ ℙⁿ_ℤ`. These are the opens over which the source of
[Stacks, Tag 01VS] compares coordinates in step 4. -/
def standardChart (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) :
    (projectiveSpaceOver n S).Opens :=
  toIntegralAtUniverse n S ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)

/-- **The variables span the irrelevant ideal of `ℤ[T₀, …, Tₙ]`.** A homogeneous polynomial of
positive degree has every member of its support of positive total degree, hence divisible by some
variable. -/
theorem irrelevant_coordGrading_le_span_X (n : ℕ) :
    (HomogeneousIdeal.irrelevant (coordGrading.{u} n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → coordRing.{u} n)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd q hq
  have hqh : (q : coordRing.{u} n).IsHomogeneous d :=
    (MvPolynomial.mem_homogeneousSubmodule d q).mp hq
  have himg : (Set.range (MvPolynomial.X : Fin (n + 1) → coordRing.{u} n)) =
      MvPolynomial.X '' (Set.univ : Set (Fin (n + 1))) := (Set.image_univ).symm
  rw [Submodule.mem_toAddSubmonoid, himg, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hsum := hqh (MvPolynomial.mem_support_iff.mp hm)
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra! hcon
    rw [show m = 0 from Finsupp.ext hcon] at hsum
    simp only [map_zero] at hsum
    omega
  exact ⟨j, Set.mem_univ j, hj⟩

/-- **The standard charts cover `ℙⁿ_S`.** The standard opens `D₊(Tᵢ)` cover the integral model by
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`, and the charts are their preimages. -/
theorem iSup_standardChart (n : ℕ) (S : Scheme.{u}) :
    ⨆ i, standardChart n S i = ⊤ := by
  have hint : ⨆ i : Fin (n + 1),
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (irrelevant_coordGrading_le_span_X n)
  refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hint.ge (show (toIntegralAtUniverse n S).base x ∈ (⊤ : (projectiveSpaceAtUniverse.{u} n).Opens)
      from trivial))
  exact ⟨i, hi⟩

end AlgebraicGeometry.projectiveSpaceOver

namespace Stacks.AmpleImmersionReduction

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

/-! ### The comparison of coordinates -/

/-- **The preimage of the `i`-th standard chart of `ℙⁿ_S` is `X_{sᵢ}`**, for the morphism of
[Stacks, Tag 01NE] attached to a generating family `s` of global sections of an invertible
`𝒪_X`-module. This is the first half of step 4 of the proof of [Stacks, Tag 01VS], and it is
unconditional: no ampleness and no finite type hypothesis occurs.

The hypothesis `hchart` is the pinning that
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` supplies, and
every one of its instances is used: on `X_{s_k}` the morphism is the one of the ratio family, whose
preimage of `D₊(Tᵢ)` is `X.basicOpen (sᵢ / s_k) = X_{sᵢ} ⊓ X_{s_k}`. -/
theorem preimage_standardChart {S : Scheme.{u}} (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    (i : Fin (n + 1)) :
    p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i = nvCover s i := by
  have key : ∀ k, p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i ⊓ nvCover s k =
      nvCover s i ⊓ nvCover s k := by
    intro k
    have h1 : (nvCover s k).ι ⁻¹ᵁ (p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i) =
        (nvCover s k).toScheme.basicOpen (chartRatio s k i) := by
      have hc : (nvCover s k).ι ⁻¹ᵁ (p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i) =
          ((nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ
            Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := rfl
      rw [hc, hchart k]
      exact Stacks.SectionsToProjectiveSpace.preimage_basicOpen (chartRatio s k)
        (span_range_chartRatio s k) i
    have h2 := congrArg (fun W => (nvCover s k).ι ''ᵁ W) h1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      chartRatio, Scheme.Opens.ι_image_basicOpen_topIso_inv, inf_comm] at h2
    rw [h2]
    exact (Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen (s k) (s i)
      le_rfl (ratio s k i) (ratio_smul s k i).symm).symm
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  obtain ⟨k, hk⟩ := exists_mem_nvCover_of_generatesStalks s hs x
  have h := SetLike.ext_iff.mp (key k) x
  exact ⟨fun hx => (h.mp ⟨hx, hk⟩).1, fun hx => (h.mpr ⟨hx, hk⟩).1⟩

/-! ### Step 4 of the proof of Stacks Tag 01VS -/

/-- **Step 4 of the proof of [Stacks, Tag 01VS].** A morphism to `ℙⁿ_S` pinned on the charts of a
generating family, which on each chart `X_{sᵢ}` is an immersion into the `i`-th standard chart of
`ℙⁿ_S`, is an immersion.

This is unconditional: it uses neither ampleness nor the finite type hypothesis, only the pinning.
The charts cover `ℙⁿ_S` and being an immersion is Zariski local on the target, so it suffices that
each `X_{sᵢ} ⟶ ℙⁿ_S` is an immersion, which it is — an immersion into an open subscheme followed by
that subscheme's inclusion. The preimage identification is what makes `X_{sᵢ}` the source of the
restriction of `p` over the `i`-th chart rather than merely a subscheme of it.

**The chartwise hypothesis is an immersion and not a closed immersion**, because the source's step
2 produces a closed immersion into the *affine open over `Vᵢ`* of the `i`-th chart and not into the
whole chart: the image of `X_{sᵢ}` is closed in `Vᵢ ×_ℤ D₊(Tᵢ)` and need not be closed in
`S ×_ℤ D₊(Tᵢ)` when `Vᵢ ≠ S`. A closed immersion into the chart is of course a special case, by
Mathlib's instance `AlgebraicGeometry.IsImmersion` of `AlgebraicGeometry.IsClosedImmersion`. -/
theorem isImmersion_of_isImmersion_standardChart {S : Scheme.{u}}
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    (hcl : ∀ i, ∃ g : (nvCover s i).toScheme ⟶
        (projectiveSpaceOver.standardChart n S i).toScheme,
      IsImmersion g ∧
        g ≫ (projectiveSpaceOver.standardChart n S i).ι = (nvCover s i).ι ≫ p) :
    IsImmersion p := by
  have hrr : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hop : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun q i _ hqi => MorphismProperty.HasOfPostcompProperty.of_postcomp
      (W := @IsImmersion) (W' := (⊤ : MorphismProperty Scheme)) q i trivial hqi⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) p
  intro x
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs x
  have hpre : p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i = nvCover s i :=
    preimage_standardChart s hs p hchart i
  refine ⟨projectiveSpaceOver.standardChart n S i, ?_, ?_⟩
  · exact show x ∈ p ⁻¹ᵁ projectiveSpaceOver.standardChart n S i from hpre ▸ hi
  · rw [hpre]
    obtain ⟨g, hg, hgfac⟩ := hcl i
    rw [← hgfac]
    infer_instance

/-- **The converse of `Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart`**,
so that step 4 of the proof of [Stacks, Tag 01VS] is an *equivalence*: the global immersion
condition on a pinned morphism and the chartwise one say the same thing.

The chartwise morphism is `AlgebraicGeometry.Scheme.Hom.resLE`, whose source is `X_{sᵢ}` precisely
by `Stacks.AmpleImmersionReduction.preimage_standardChart`. Recorded so that no claim is made that
the chartwise condition is weaker than the global one: what step 4 buys is that the condition
becomes *local*, hence a question about a ring map, not that it becomes a smaller statement. -/
theorem isImmersion_standardChart_of_isImmersion {S : Scheme.{u}}
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (p : X ⟶ projectiveSpaceOver n S)
    (hchart : ∀ k, (nvCover s k).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s k) (span_range_chartRatio s k))
    [IsImmersion p] (i : Fin (n + 1)) :
    ∃ g : (nvCover s i).toScheme ⟶ (projectiveSpaceOver.standardChart n S i).toScheme,
      IsImmersion g ∧
        g ≫ (projectiveSpaceOver.standardChart n S i).ι = (nvCover s i).ι ≫ p :=
  ⟨p.resLE (projectiveSpaceOver.standardChart n S i) (nvCover s i)
      (preimage_standardChart s hs p hchart i).ge,
    inferInstance, Scheme.Hom.resLE_comp_ι _ _⟩

/-- **The chartwise condition from a closed immersion into an open part of the chart.** This is the
shape step 2 of the proof of [Stacks, Tag 01VS] delivers it in: the chart `X_{sᵢ}` maps into the
affine open `Vᵢ ×_ℤ D₊(Tᵢ)` of the `i`-th chart of `ℙⁿ_S`, where `Vᵢ` is the affine open of `S`
that `Stacks.AmpleChartsOverBase.exists_generating_family_over_of_isAmple` produces, and the ring
map is surjective there, not on the whole chart.

So the hypothesis of
`Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart` need only be met by a
closed immersion into *some* open subscheme of the chart, which is what this supplies. -/
theorem exists_isImmersion_standardChart_of_isClosedImmersion_le {S : Scheme.{u}}
    (s : Fin (n + 1) → Γ(L, ⊤)) (p : X ⟶ projectiveSpaceOver n S) (i : Fin (n + 1))
    (V : (projectiveSpaceOver n S).Opens)
    (hV : V ≤ projectiveSpaceOver.standardChart n S i)
    (g : (nvCover s i).toScheme ⟶ V.toScheme) [IsClosedImmersion g]
    (hfac : g ≫ V.ι = (nvCover s i).ι ≫ p) :
    ∃ g' : (nvCover s i).toScheme ⟶ (projectiveSpaceOver.standardChart n S i).toScheme,
      IsImmersion g' ∧
        g' ≫ (projectiveSpaceOver.standardChart n S i).ι = (nvCover s i).ι ≫ p :=
  ⟨g ≫ (projectiveSpaceOver n S).homOfLE hV, inferInstance, by
    rw [Category.assoc, Scheme.homOfLE_ι, hfac]⟩

/-! ### The input that replaces `ChartImmersion` -/

variable {S : Scheme.{u}}

/-- **Steps 2 and 4 of the proof of [Stacks, Tag 01VS], with step 4 performed.** For an ample `L`
on a scheme locally of finite type over `S`, some positive power of `L` carries a generating family
of global sections whose pinned morphism to projective space over `S` restricts on each chart
`X_{sᵢ}` to an immersion into the `i`-th standard chart of `ℙⁿ_S`.

This is `Stacks.AmpleImmersionReduction.ChartImmersion` with the global immersion condition traded
for the chartwise one, and `Stacks.AmpleImmersionReduction.chartImmersion_of_chartwiseImmersion` is
the trade. What it buys is that the condition is *local on the target*: the family of
`Stacks.AmpleChartsOverBase.exists_generating_family_over_of_isAmple` has every `X_{sᵢ}` affine and
contained in `f⁻¹(Vᵢ)` for an affine open `Vᵢ` of `S`, so the `i`-th chart may be cut down to its
affine open `Vᵢ ×_ℤ D₊(Tᵢ)` and the condition becomes surjectivity of a ring map — which is what
the source's step 2 provides, from [Stacks, Tag 01T2] and [Stacks, Tag 01PW].

**It is not [Stacks, Tag 01VS]**: it says nothing about `𝒪(1)` and nothing about any degree beyond
the single one it produces. -/
def ChartwiseImmersion (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  Stacks.Ample.IsAmple X L → LocallyOfFiniteType f →
    ∃ (N : ℤ) (m : ℕ) (s : Fin (m + 1) → Γ(tensorPowModule X L N, ⊤)),
      1 ≤ N ∧ GeneratesStalks s ∧
        ∀ p : X ⟶ projectiveSpaceOver m S,
          p ≫ pullback.fst (terminal.from S)
              (terminal.from (projectiveSpaceAtUniverse.{u} m)) = f →
            (∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse m S =
              toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) →
            ∀ i, ∃ g : (nvCover s i).toScheme ⟶
                (projectiveSpaceOver.standardChart m S i).toScheme,
              IsImmersion g ∧
                g ≫ (projectiveSpaceOver.standardChart m S i).ι = (nvCover s i).ι ≫ p

/-- **`Stacks.AmpleImmersionReduction.ChartImmersion` from
`Stacks.AmpleImmersionReduction.ChartwiseImmersion`**: step 4 of the proof of [Stacks, Tag 01VS]
performed, so that what the source's steps 2 and 4 still owe is chartwise and therefore affine.

Through `Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist` this replaces
`ChartImmersion` by `ChartwiseImmersion` in the four named inputs of
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`. -/
theorem chartImmersion_of_chartwiseImmersion (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (h : ChartwiseImmersion f L) :
    ChartImmersion f L := by
  intro hL hft
  obtain ⟨N, m, s, hN, hgen, hcl⟩ := h hL hft
  exact ⟨N, m, s, hN, hgen, fun p hpf hpchart =>
    isImmersion_of_isImmersion_standardChart s hgen p hpchart (hcl p hpf hpchart)⟩

end Stacks.AmpleImmersionReduction

end
