module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Quotient
public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Graded
public import StacksFrontier.RingTheory.GradedAlgebra.NoetherianModel

/-!
# The comparison map on twists at a graded quotient, Tag 01N0 part (3)

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring, let `I` be a homogeneous ideal, let `X = Proj 𝒮` and
let `Y = Proj (𝒮 ⧸ I) = V₊(I)` with `r : Y ⟶ X` the closed immersion
`AlgebraicGeometry.Proj.map (Stacks.HomogeneousIdeal.quotientMk I)` of Tag 01N0 part (2). Tag
01N0 part (3) is about the comparison maps

`θ : r^* 𝒪_X(n) ⟶ 𝒪_Y(n)`.

The source says they are surjective but *not* isomorphisms in general, even for a surjective
`ψ`; its counterexample is `A = k[x, y]` with `deg x = 1`, `deg y = 2` and `I = (x)`, where
`𝒪_Y(1) = 0` while `r^* 𝒪_X(1) ≠ 0`. Surjectivity is already
`Stacks.AlgebraicGeometry.ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective`. This
file proves the complementary positive statement, in the one place where the counterexample is
excluded and where the chain consuming this tag needs it: **when `𝒮` is Noetherian and generated
in degree one over `𝒮 0`, `θ` is injective on the canonical twisted sections**, so the two
descriptions of a homogeneous element dying on `Y` — its section of `𝒪_X(n)` pulling back to
zero, and its class having zero section on `Y` — agree.

That is exactly the identification the saturation files were missing. The docstring of
`StacksFrontier/AlgebraicGeometry/ProjSaturation/Quotient.lean` records
`degreeSection_quotientGradingMk_eq_zero_iff` — the section of the class of `a` on `V₊(I)`
vanishes iff `a` is in the saturation of `I` — and says it does **not** compute
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme 𝒮 (Proj.map (quotientMk I) _)`,
which asks instead for the vanishing of the *pulled-back* sections of `𝒪_X(n)`. The comparison
below closes that gap, and with it the converse half of Tag 0BXK: for a saturated homogeneous
ideal `I`, the ideal of equations of `V₊(I)` is `I` itself.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_degree_mul_mem_of_forall_exists_pow_mul_mem`:
  the Noetherian uniformization step, relative to an ideal — if every degree-one element carries
  `x` into `I` after raising it to some power, then one whole homogeneous component `𝒮 N`
  carries `x` into `I`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.le_idealOfClosedSubscheme_map_quotientMk`: `I` is
  contained in the ideal of equations of `V₊(I)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_idealOfClosedSubscheme_map_quotientMk_iff`:
  **the computation** — a homogeneous element is an equation for `V₊(I)` exactly when it lies in
  the saturation of `I`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.pullbackGlobalSections_degreeSection_eq_zero_iff_degreeSection_quotientGradingMk_eq_zero`:
  **the comparison of Tag 01N0 part (3) on canonical sections** — the pullback along `r` of the
  section of `𝒪_X(n)` attached to `a ∈ 𝒮 n` vanishes exactly when the section of `𝒪_Y(n)`
  attached to the class of `a` vanishes. This is the assertion that `θ` is injective where the
  source's counterexample says it need not be, under degree-one generation.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_map_eq_of_ker_eq_of_saturated`:
  for a surjective `ψ`, a saturated kernel is the ideal of equations of `Proj ℬ ⊆ Proj 𝒮`. At the
  quotient by a homogeneous ideal this is
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_projMap_quotientMk_eq`.

## Implementation notes

Both directions go through the chart comparison rather than through sheaves of modules on `Y`.
Membership in the ideal of equations is tested on the standard opens of the degree-one elements,
which cover `Proj 𝒮`, by the lemmas of the namespace `AlgebraicGeometry.ProjectiveSpectrum`,
`Proj.mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker` in one direction and
`Proj.chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme` in the other; on the chart `D₊(f)`
the kernel of `r` is computed by
`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff` followed by
`Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff`, which turn the
vanishing of the chart function `a / f ^ n` into `∃ k, f ^ k * a ∈ Ker (quotientMk I) = I`.

So the chartwise content is "for every degree-one `f` some power of `f` carries `a` into `I`",
and the two sides of the comparison differ only in how that is made uniform in `f`. The
quotient-side description produced by `ProjSaturation/Quotient.lean` is "one whole `𝒮 N` carries
`a` into `I`", and passing between the two is the only place Noetherianness is used:
`exists_degree_mul_mem_of_forall_exists_pow_mul_mem` puts the colon ideal `(I : a)` in place of
the annihilator used by `ProjSaturation/Basic.lean`, notes that the irrelevant ideal lies in its
radical because each degree-one element does, and applies
`Ideal.exists_pow_le_of_le_radical_of_fg` together with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_irrelevant_pow_of_mem`, which places `𝒮 N` inside
the `N`-th power of the irrelevant ideal when `𝒮` is generated in degree one.

Degree-one generation is used twice more and for a different reason each time: it provides the
cover by the `D₊(f)` with `f ∈ 𝒮 1`, and it makes every `𝒪(k)` invertible, which is what the
chart description of the zero scheme of a twisted section needs.

The grading is taken `AddSubgroupClass`-valued in the same universe as the ring, as in
`ProjQuotientChartIdeal/Graded.lean`: the chart comparison for `Proj.map` of a homomorphism of
graded rings is stated with the two rings and the two grading types in one universe.

## What is not done

`θ` is not shown to be an isomorphism of sheaves of modules. What is proved is its injectivity on
the canonical twisted sections of homogeneous elements, which is the form Tags 0BXK and 0801 use
and the form the saturation files were missing; promoting it to a sheaf-level isomorphism would
need the sections of a pullback of sheaves of modules, which
`StacksFrontier/AlgebraicGeometry/ProjTwistEpi/Basic.lean` records as unavailable in this library.
Nor is the source's counterexample formalized: nothing here says that degree-one generation
cannot be dropped.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
open AlgebraicGeometry
open Stacks.HomogeneousIdeal

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ)
  [GradedRing 𝒮]

/-! ### The Noetherian uniformization step, relative to an ideal -/

/-- **If every degree-one element carries `x` into `I` after raising it to a power, then one
whole homogeneous component carries `x` into `I`.** This is the relative form of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_annihilating_degree_of_degreeSection_eq_zero`,
with the annihilator of `x` replaced by the colon ideal `(I : x)`: the degree-one elements
generate the irrelevant ideal, so that ideal lies in the radical of `(I : x)`, a finitely
generated ideal inside a radical has a power inside the ideal, and in a ring generated in degree
one the component `𝒮 N` lies in the `N`-th power of the irrelevant ideal. -/
theorem exists_degree_mul_mem_of_forall_exists_pow_mul_mem [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (I : Ideal S) (x : S)
    (h : ∀ f : S, f ∈ 𝒮 1 → ∃ k : ℕ, f ^ k * x ∈ I) :
    ∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * x ∈ I := by
  set K := I.colon ({x} : Set S) with hK
  have hmem : ∀ y : S, y ∈ K ↔ y * x ∈ I := by
    intro y
    rw [hK, Submodule.mem_colon_singleton, smul_eq_mul]
  have hrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ K.radical := by
    rw [← span_degreeOne_eq_irrelevant 𝒮 hgen, Ideal.span_le]
    intro f hf
    obtain ⟨k, hk⟩ := h f hf
    rw [SetLike.mem_coe, Ideal.mem_radical_iff]
    exact ⟨k, (hmem _).mpr hk⟩
  obtain ⟨N, hN⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing _)
  exact ⟨N, fun y hy => (hmem y).mp (hN (mem_irrelevant_pow_of_mem 𝒮 hgen N hy))⟩

/-- The chart function of `b / f ^ n` dies on `Proj ℬ` iff some power of `f` carries `b` into
`Ker ψ`. -/
private theorem awayToSection_mk_mem_ker_iff {B τ : Type u} [CommRing B] [SetLike τ B]
    [AddSubgroupClass τ B] (ℬ : ℕ → τ) [GradedRing ℬ] (ψ : 𝒮 →+*ᵍ ℬ)
    (hq : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    {f : S} (hf : f ∈ 𝒮 1) {n : ℕ} {b : S}
    (hb : b ∈ 𝒮 (n • 1)) :
    (AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (HomogeneousLocalization.Away.mk 𝒮 hf n b hb) ∈
        RingHom.ker ((Proj.map ψ hq).app (Proj.basicOpen 𝒮 f)).hom ↔
      ∃ k : ℕ, f ^ k * b ∈ RingHom.ker (ψ : S →+* B) := by
  rw [Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff ψ hq hf Nat.one_pos,
    Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff]

/-! ### The ideal of equations of a closed subscheme `Proj ℬ ⊆ Proj 𝒮` -/

section Surjective

variable {B τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ℕ → τ)
  [GradedRing ℬ] (ψ : 𝒮 →+*ᵍ ℬ)
  (hq : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
  [IsClosedImmersion (Proj.map ψ hq)]

/-- **A homogeneous element of the kernel is an equation for `Proj ℬ`.** On the chart `D₊(f)` of
a degree-one element the chart function of the element is the image of a fraction whose numerator
already lies in `Ker ψ`, so it dies on `Proj ℬ`; the degree-one charts cover `Proj 𝒮`, so the
chartwise criterion applies. -/
theorem mem_idealOfClosedSubscheme_map_of_mem_ker
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n)
    (hb : (b : S) ∈ RingHom.ker (ψ : S →+* B)) :
    (b : S) ∈ idealOfClosedSubscheme 𝒮 (Proj.map ψ hq) := by
  have hb1 : (b : S) ∈ 𝒮 (n • 1) := by simp
  refine mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker 𝒮 Nat.one_pos
    (fun g : 𝒮 1 => (g : S)) (fun g => g.2)
    (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen)
    (Proj.map ψ hq) (m := n) ⟨(b : S), hb1⟩ fun g => ?_
  refine (awayToSection_mk_mem_ker_iff 𝒮 ℬ ψ hq g.2 hb1).mpr ?_
  exact ⟨0, by rwa [pow_zero, one_mul]⟩

/-- **The kernel of `ψ` consists of equations for `Proj ℬ`.** The kernel of a homomorphism of
graded rings is homogeneous, and each homogeneous component of one of its elements is an
equation. -/
theorem ker_le_idealOfClosedSubscheme_map
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) :
    RingHom.ker (ψ : S →+* B) ≤ idealOfClosedSubscheme 𝒮 (Proj.map ψ hq) := by
  classical
  intro x hx
  rw [← DirectSum.sum_support_decompose 𝒮 x]
  refine Submodule.sum_mem _ fun n _ => ?_
  exact mem_idealOfClosedSubscheme_map_of_mem_ker 𝒮 ℬ ψ hq hgen
    (DirectSum.decompose 𝒮 x n) (Stacks.GradedModel.isHomogeneous_ker 𝒮 ℬ ψ n hx)

/-- **The ideal of equations of `Proj ℬ ⊆ Proj 𝒮`, on homogeneous elements: it is the saturation
of `Ker ψ`.** A homogeneous element `b` is an equation for `Proj ℬ` exactly when one whole
homogeneous component `𝒮 N` multiplies `b` into `Ker ψ`.

The forward direction reads the vanishing of the chart function of `b` on each degree-one chart
`D₊(f)` as `∃ k, f ^ k b ∈ Ker ψ` and makes that uniform in `f` by
`exists_degree_mul_mem_of_forall_exists_pow_mul_mem`. The backward direction is the saturation of
the ideal of equations of *any* closed subscheme,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.saturated_idealOfClosedSubscheme`, applied to the
multipliers, which lie in `Ker ψ` and hence in the ideal of equations. -/
theorem mem_idealOfClosedSubscheme_map_iff [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n) :
    (b : S) ∈ idealOfClosedSubscheme 𝒮 (Proj.map ψ hq) ↔
      ∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * (b : S) ∈ RingHom.ker (ψ : S →+* B) := by
  have inst : ∀ k : ℤ, SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 k) :=
    algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen
  have hb1 : (b : S) ∈ 𝒮 (n • 1) := by simp
  constructor
  · intro hb
    refine exists_degree_mul_mem_of_forall_exists_pow_mul_mem 𝒮 hgen
      (RingHom.ker (ψ : S →+* B)) (b : S) fun f hf => ?_
    have hker := chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme 𝒮 hf Nat.one_pos
      (Proj.map ψ hq) n ⟨(b : S), hb1⟩ hb
    exact (awayToSection_mk_mem_ker_iff 𝒮 ℬ ψ hq hf hb1).mp hker
  · rintro ⟨N, hN⟩
    exact saturated_idealOfClosedSubscheme 𝒮 hgen (Proj.map ψ hq) (b : S)
      ⟨N, fun y hy => ker_le_idealOfClosedSubscheme_map 𝒮 ℬ ψ hq hgen (hN y hy)⟩

/-! ### Tag 01N0 part (3) on the canonical sections -/

/-- **The comparison of Tag 01N0 part (3) on canonical twisted sections, for a surjective
homomorphism of graded rings out of a Noetherian ring generated in degree one.** Write
`X = Proj 𝒮`, `Y = Proj ℬ` and `r = r_ψ : Y ⟶ X` for the closed immersion of part (2). For
`a ∈ 𝒮 n`, the pullback along `r` of the canonical section of `𝒪_X(n)` attached to `a` vanishes
exactly when the canonical section of `𝒪_Y(n)` attached to `ψ a` vanishes.

The source's part (3) says the comparison maps `θ : r^* 𝒪_X(n) ⟶ 𝒪_Y(n)` of Tag 01MY are
surjective but in general not injective, even for a surjective `ψ`; its counterexample is
`𝒮 = k[x, y]` with `deg x = 1`, `deg y = 2` and `Ker ψ = (x)`. The statement here is that `θ`
*is* injective on the canonical sections once `𝒮` is generated in degree one — the hypothesis the
counterexample violates. Tag 01N0 part (3) itself is carried by
`Stacks.AlgebraicGeometry.ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective`
(surjectivity of `θ`) and
`Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample`
`.surjective_and_not_isIso_projMapData_twistMap`
(an example where `θ₁` is not an isomorphism), so no `@[stacks]` attribute is attached here.

Both sides are the saturation of `Ker ψ`: the left by `mem_idealOfClosedSubscheme_map_iff` and
the right by `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_iff` on `ℬ`, which
inherits Noetherianness and degree-one generation from `𝒮` along `ψ`. -/
theorem pullbackGlobalSections_degreeSection_eq_zero_iff_degreeSection_map_eq_zero
    [IsNoetherianRing S] (hψ : Function.Surjective ψ)
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) {n : ℕ} (b : 𝒮 n) :
    pullbackGlobalSections (Proj.map ψ hq) (twistingSheaf 𝒮 (n : ℤ))
          (degreeSection 𝒮 n b) = 0 ↔
      degreeSection ℬ n ⟨ψ (b : S), ψ.map_mem b.2⟩ = 0 := by
  have : IsNoetherianRing B := isNoetherianRing_of_surjective S B (ψ : S →+* B) hψ
  have hgenB : Algebra.adjoin (ℬ 0) (ℬ 1 : Set B) = ⊤ :=
    ψ.adjoin_degreeOne_eq_top_of_surjective hψ hgen
  have hdec : (DirectSum.decompose 𝒮 (b : S) n : 𝒮 n) = b :=
    Subtype.ext (DirectSum.decompose_of_mem_same 𝒮 b.2)
  have h1 : pullbackGlobalSections (Proj.map ψ hq) (twistingSheaf 𝒮 (n : ℤ))
        (degreeSection 𝒮 n b) = 0 ↔
      (b : S) ∈ idealOfClosedSubscheme 𝒮 (Proj.map ψ hq) := by
    refine ⟨fun h => mem_idealOfClosedSubscheme 𝒮 _ n b h, fun h => ?_⟩
    have h2 := (mem_idealOfClosedSubscheme_iff 𝒮 (Proj.map ψ hq) (b : S)).mp h n
    rwa [hdec] at h2
  rw [h1, mem_idealOfClosedSubscheme_map_iff 𝒮 ℬ ψ hq hgen b,
    degreeSection_eq_zero_iff ℬ hgenB ⟨ψ (b : S), ψ.map_mem b.2⟩]
  refine (exists_congr fun N => ⟨fun h y hy => ?_, fun h z hz => ?_⟩).symm
  · simpa [RingHom.mem_ker, map_mul] using h (ψ y) (ψ.map_mem hy)
  · obtain ⟨y, hy, rfl⟩ := ψ.exists_mem_of_surjective hψ hz
    simpa [RingHom.mem_ker, map_mul] using h y hy

/-! ### The converse half of Tag 0BXK -/

/-- **A saturated ideal is the ideal of equations of the closed subscheme it cuts out.** For a
surjective `ψ` out of a Noetherian graded ring generated in degree one, if an ideal `J` is the
kernel of `ψ` and is saturated, then `J` is exactly the homogeneous ideal of equations of
`Proj ℬ ⊆ Proj 𝒮`. This is the converse half of Tag 0BXK, and the form a consumer uses: it
arrives with `J` computed for other reasons and a proof that `J` is saturated.

The ideal of equations is homogeneous, so the containment `I(Proj ℬ) ≤ J` follows degreewise from
`mem_idealOfClosedSubscheme_map_iff` and saturation; the other containment is
`ker_le_idealOfClosedSubscheme_map`. -/
theorem idealOfClosedSubscheme_map_eq_of_ker_eq_of_saturated [IsNoetherianRing S]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (J : Ideal S)
    (hJ : RingHom.ker (ψ : S →+* B) = J)
    (hsat : ∀ x : S, (∃ N : ℕ, ∀ y : S, y ∈ 𝒮 N → y * x ∈ J) → x ∈ J) :
    idealOfClosedSubscheme 𝒮 (Proj.map ψ hq) = J := by
  classical
  subst hJ
  refine le_antisymm (fun x hx => ?_) (ker_le_idealOfClosedSubscheme_map 𝒮 ℬ ψ hq hgen)
  rw [← DirectSum.sum_support_decompose 𝒮 x]
  exact Submodule.sum_mem _ fun m _ => hsat _ ((mem_idealOfClosedSubscheme_map_iff 𝒮 ℬ ψ hq hgen
    (DirectSum.decompose 𝒮 x m)).mp (idealOfClosedSubscheme_isHomogeneous 𝒮 (Proj.map ψ hq) m hx))

end Surjective

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
