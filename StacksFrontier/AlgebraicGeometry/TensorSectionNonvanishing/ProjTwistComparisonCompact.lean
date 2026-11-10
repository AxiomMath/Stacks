module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenCover
public import StacksFrontier.AlgebraicGeometry.ProjQuasiCoherentRecovery.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.GlobalSections
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistChartBijective
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistIntegerLocalComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0AG5: a quasi-coherent sheaf on a quasi-compact `Proj` is recovered from its twisted
global sections

Let `S` be a graded ring with `X = Proj S` **quasi-compact**, let `ℱ` be a quasi-coherent
`𝒪_X`-module and let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the graded `S`-module of twisted global
sections of Section 01MM, with the graded module structure of Tag 03GK.
[Stacks, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5) asserts two things: that the
comparison `M̃ ⟶ ℱ` of Tag 0B5I is an isomorphism, and that if `X` is moreover covered by the
standard opens `D₊(f)` of the elements `f` of degree one then the induced maps
`M_n → Γ(X, ℱ(n))` are the identity maps.  **This file proves both**, with no hypothesis beyond
the source's own.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_integerComparison`: **Tag 0AG5's
  first assertion**, for `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` with its canonical graded module structure,
  and `isIso_integerComparison_of_compactSpace`, the same for an arbitrary graded module
  structure on `M`.
* `Stacks.AlgebraicGeometry.ProjTwistComparisonCompact`
  `.twistSheafMap_integerComparison_degreeNToTwistedGlobalSections`: **Tag 0AG5's second
  assertion**, that under the degree-one covering hypothesis the induced maps
  `M_n → Γ(X, ℱ(n))` are the identity maps, and
  `twistSheafMap_integerComparison_degreeNToTwistedGlobalSections_of_module`, the same for an
  arbitrary graded module structure on `M`.
* `Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_comparison_of_compactSpace`: the
  same conclusion for the **natural**-graded module `⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM, which
  is the form the chart bijectivity is proved in.  Tag 03GM asserts this for `ℙᵐ_R`; the
  statement here is at an arbitrary quasi-compact `Proj S`.
* `Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.bijective_chartHom_of_compactSpace`: the
  local half, that the chart comparison `Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)` is bijective for every
  homogeneous `f` of positive degree.

## The route

The source replaces the members of a finite cover of `X` by standard opens by suitable powers,
so that the defining elements acquire one common degree.  That cover is
`AlgebraicGeometry.Proj.commonDegreeCover`, which quasi-compactness supplies directly, and the
bijectivity of the chart comparison against a cover by standard opens of elements *of the same
degree as the chart's own element* is
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover`.

The two degrees still have to be matched.  For `f` of degree `e` and a cover of common degree
`d`, the element `f ^ d` has degree `d e`, the cover elements raised to the `e`-th power have
degree `e d`, and `D₊(f ^ d) = D₊(f)`, `D₊(c ^ e) = D₊(c)`.  So the cover statement applies at
`f ^ d`, and `bijective_chartHom_of_pow` transports its conclusion back to `f`: the two chart
comparisons live over opens that are *equal*, so the restriction maps between them are mutually
inverse and `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom_restrict` identifies the
two maps up to those bijections.

`Stacks.AlgebraicGeometry.ProjTwistChartBijective.isIso_comparison_of_degreeOneCover` is the
same conclusion under the stronger hypothesis of a cover by the standard opens of *degree-one*
elements, where the degree matching is needed only on the cover; that is Tag 03GM's hypothesis,
not Tag 0AG5's.

Tag 0AG5's module is the **integer**-graded `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` of Tag 0B5I, while the chart
bijectivity is proved for the natural-graded `⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM.  These are
different types with different gradings and different scalar actions, but a degree-zero fraction
`x / f ^ n` only ever meets the components of degree `n d` with `n ≥ 0`, so the two numerator
families agree on what a fraction sees; that is `numerSection_eq`, and it is what carries the
source's omitted injectivity and surjectivity arguments across.  The vanishing of a power of `f`
times a homogeneous element transfers for the same reason: on a homogeneous element both scalar
actions are the global sections of the same multiplication morphism of twists
(`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.gsmul_eq`).

## The route of the second assertion

The source omits this proof.  The induced map is Equation 0AG3, `M_n → Γ(X, M̃(n))`, followed by
the global sections of the `n`-th twist of the comparison, and the identification
`M_n = Γ(X, ℱ(n))` is the inclusion of the degree-`n` summand.  Both sides are sections over
`X`, so the identity is checked on the cover by the standard opens `D₊(g)` of the degree-one
elements, which is exactly the hypothesis.

On such a `D₊(g)` the element `g ^ n` trivializes `𝒪_X(n)` — for a *negative* `n` as well, the
trivializing section of Tag 01MS being the fraction `g ^ n⁺ / g ^ n⁻` — so multiplication by it
is a bijection `Γ(D₊(g), ℰ) → Γ(D₊(g), ℰ(n))` for every sheaf of modules `ℰ`
(`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`), and the whole clause
becomes a statement about *untwisted* sections.  On the `M̃` side the section coming from `m` is
`g ^ n` times the fraction `g ^ n⁻ · m / g ^ n⁺`, which is proved pointwise against Equation
01MQ (`mulTrivSection_degreeZeroFraction`); the chart comparison of Tag 0B5I carries that
fraction to the section whose product with `g ^ n⁺` is the restriction of the degree-`n⁺`
component of `g ^ n⁻ · m`; and that component is `g ^ n⁻` acting on `s` because `m` is the
element of `M_n` that `s` names.  Dividing back by `g ^ n⁻` is
`twistSheafScalarMap_mulTrivSection_int`, the trivializing-section law of
`ProjTwistScalarTriviality` at an integer exponent, which is what the negative twists need.

## References

* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01MM](https://stacks.math.columbia.edu/tag/01MM)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0AG3](https://stacks.math.columbia.edu/tag/0AG3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistSectionModule (moduleGrading
  associatedTwistSectionSheaf)
open Stacks.AlgebraicGeometry.ProjTwistLocalComparison (chartHom chartHom_restrict comparison
  isIso_comparison_of_bijective_chartHom)
open Stacks.AlgebraicGeometry.ProjTwistChartBijective (bijective_chartHom_of_cover)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistComparisonCompact

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **Restriction between two opens that are equal is bijective on sections.**  The two
restriction maps along the two inclusions are mutually inverse, because the two composites are
the restriction along an identity. -/
private theorem bijective_res_of_le_of_le (G : SheafOfModules.{u} (projRingSheaf 𝒮))
    {U V : Opens (ProjectiveSpectrum.top 𝒮)} (h : V ≤ U) (h' : U ≤ V) :
    Function.Bijective fun z : G.val.obj (op U) => G.val.map (homOfLE h).op z := by
  have hidU : ∀ z : G.val.obj (op U), G.val.map (homOfLE (le_refl U)).op z = z := by
    intro z
    have hz := CategoryTheory.congr_fun (G.val.map_id (op U)) z
    simpa using hz
  have hidV : ∀ z : G.val.obj (op V), G.val.map (homOfLE (le_refl V)).op z = z := by
    intro z
    have hz := CategoryTheory.congr_fun (G.val.map_id (op V)) z
    simpa using hz
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z => G.val.map (homOfLE h').op z, fun z => ?_, fun z => ?_⟩
  · exact (CategoryTheory.congr_fun
      (G.val.map_comp (homOfLE h).op (homOfLE h').op) z).symm.trans (hidU z)
  · exact (CategoryTheory.congr_fun
      (G.val.map_comp (homOfLE h').op (homOfLE h).op) z).symm.trans (hidV z)

/-- **A map compatible with restriction along equal opens is bijective if its twin is.** -/
private theorem bijective_of_res_comp_eq (G G' : SheafOfModules.{u} (projRingSheaf 𝒮))
    {U V : Opens (ProjectiveSpectrum.top 𝒮)} (h : V ≤ U) (h' : U ≤ V)
    {φ : G.val.obj (op V) → G'.val.obj (op V)} {ψ : G.val.obj (op U) → G'.val.obj (op U)}
    (hψ : Function.Bijective ψ)
    (hcomp : ∀ z, φ (G.val.map (homOfLE h).op z) = G'.val.map (homOfLE h).op (ψ z)) :
    Function.Bijective φ := by
  refine (Function.Bijective.of_comp_iff φ (bijective_res_of_le_of_le 𝒮 G h h')).mp ?_
  rw [show φ ∘ _ = _ from funext hcomp]
  exact (bijective_res_of_le_of_le 𝒮 G' h h').comp hψ

/-- **Bijectivity of the chart comparison passes from a power of the element to the element.**
`D₊(f ^ k) = D₊(f)` for `k ≥ 1`, so the two chart comparisons have equal source and target up
to the restriction maps along that equality, which are bijections. -/
private theorem bijective_chartHom_of_pow {f : S} {e k D : ℕ} (hf : f ∈ 𝒮 e) (he : 0 < e)
    (hk : 0 < k) (hfk : f ^ k ∈ 𝒮 D) (hD : 0 < D)
    (h : Function.Bijective (chartHom 𝒮 F hfk hD).hom) :
    Function.Bijective (chartHom 𝒮 F hf he).hom := by
  have heq : ProjectiveSpectrum.basicOpen 𝒮 (f ^ k) = ProjectiveSpectrum.basicOpen 𝒮 f :=
    ProjectiveSpectrum.basicOpen_pow 𝒮 f k hk
  exact bijective_of_res_comp_eq 𝒮 (associatedTwistSectionSheaf 𝒮 F) F heq.ge heq.le h
    (chartHom_restrict 𝒮 F hfk hD hf he heq.ge)

/-- **A quasi-compact `Proj S` has a finite cover by standard opens of elements of one degree
`d * e`**, namely the `e`-th powers of a common-degree-`d` cover, and `f ^ d` has that degree
too. -/
private theorem exists_pow_cover [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)] {f : S} {e : ℕ}
    (hf : f ∈ 𝒮 e) (he : 0 < e) :
    ∃ (d : ℕ) (_ : 0 < d) (ι : Type u) (_ : Fintype ι) (g : ι → S),
      f ^ d ∈ 𝒮 (d * e) ∧ (∀ i, g i ∈ 𝒮 (d * e)) ∧
        (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) = ⊤ := by
  obtain ⟨d, hd, s, hsmem, hscov⟩ :=
    _root_.AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover 𝒮 ⊤
      (isCompact_univ.of_isClosed_subset isClosed_univ (by simp))
  refine ⟨d, hd, {x : S // x ∈ s}, inferInstance, fun i => (i : S) ^ e, ?_, fun i => ?_, ?_⟩
  · simpa using SetLike.pow_mem_graded d hf
  · simpa [mul_comm] using SetLike.pow_mem_graded e (hsmem (i : S) i.2)
  · refine le_antisymm le_top (hscov.le.trans ?_)
    refine iSup₂_le fun g hg => ?_
    refine le_trans inf_le_left ?_
    refine le_trans (le_of_eq ?_)
      (le_iSup (fun i : {x : S // x ∈ s} =>
        ProjectiveSpectrum.basicOpen 𝒮 ((i : S) ^ e)) ⟨g, hg⟩)
    exact (ProjectiveSpectrum.basicOpen_pow 𝒮 g e he).symm

/-- **The local half of Tag 0AG5.**  On a quasi-compact `Proj S` the chart comparison
`Γ(D₊(f), M̃) → Γ(D₊(f), ℱ)` of a quasi-coherent `ℱ` is bijective for every homogeneous `f` of
positive degree.

Quasi-compactness gives a finite cover by standard opens of one common positive degree `d`
(`AlgebraicGeometry.Proj.commonDegreeCover`).  Raising `f` to the `d`-th power and the cover
elements to the `e`-th power puts all of them in degree `d e` without changing any of the
standard opens, which is what
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover` asks for. -/
public theorem bijective_chartHom_of_compactSpace
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {f : S} {e : ℕ} (hf : f ∈ 𝒮 e) (he : 0 < e) :
    Function.Bijective (chartHom 𝒮 F hf he).hom := by
  obtain ⟨d, hd, ι, _, g, hfd, hc, hsup⟩ := exists_pow_cover 𝒮 hf he
  exact bijective_chartHom_of_pow 𝒮 F hf he hd hfd (Nat.mul_pos hd he)
    (bijective_chartHom_of_cover 𝒮 F hqc hfd (Nat.mul_pos hd he) hc hsup)

/-- **The comparison `M̃ ⟶ ℱ` is an isomorphism on a quasi-compact `Proj S`, for the
natural-graded module `M = ⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM.**

The proof is the source's: quasi-compactness gives a finite cover by standard opens whose
defining elements can be taken of one common degree, on each standard open the comparison is
bijective, and an isomorphism of sheaves is local on the base.

No `stacks` attribute.  This is not Tag 0AG5, whose module is the *integer*-graded
`⨁_{n ∈ ℤ} Γ(X, ℱ(n))` of Tag 0B5I — that is `isIso_integerComparison` below.  Nor is it Tag
03GM, which states this for `ℙᵐ_R`; the statement here drops projective space for an arbitrary
quasi-compact `Proj S`, and Tag 03GM's attachment stays on
`Stacks.AlgebraicGeometry.ProjTwistComparisonIso.gradedModule_and_isIso_comparison`, which also
carries the tag's graded-module assertion. -/
public theorem isIso_comparison_of_compactSpace
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    IsIso (comparison 𝒮 F) :=
  isIso_comparison_of_bijective_chartHom 𝒮 F fun hg he =>
    bijective_chartHom_of_compactSpace 𝒮 F hqc hg he

/-! ### Tag 0AG5 for the integer-graded module of Tag 0B5I -/

section Integer

open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  isBasis_positiveBasicOpen)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (bijective_mulTrivSection)

variable {f : S} {d : ℕ}

/-- **The two numerator maps agree on a homogeneous element.**  The natural-graded module of Tag
03GM and the integer-graded module of Tag 0B5I have the same degree-`n d` component, and on it
both numerator maps are "restrict and divide by `f ^ n`". -/
private theorem numerSection_eq (hf : f ∈ 𝒮 d) (n : ℕ)
    (s : ProjTwistSectionModule.twistSections 𝒮 F (n * d)) :
    ProjTwistIntegerComparison.numerSection 𝒮 F hf n
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))
        (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s) =
      ProjTwistLocalComparison.numerSection 𝒮 F hf n
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))
        (DirectSum.of (ProjTwistSectionModule.twistSections 𝒮 F) (n * d) s) :=
  congrArg (fun y => ProjTwistLocalComparison.divTriv 𝒮 F hf n
      (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))
      ((twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op y))
    ((ProjTwistIntegerComparison.degreeComponent_of 𝒮 F ((n * d : ℕ) : ℤ) s).trans
      (ProjTwistLocalComparison.degreeComponent_of 𝒮 F (n * d) s).symm)

/-- **The chart comparison of Tag 0B5I is bijective against a cover by standard opens of
elements of the same degree.**  This is
`Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover` read at the
integer-graded module: the two numerator families agree by `numerSection_eq`, so the source's
omitted injectivity and surjectivity arguments serve both. -/
private theorem bijective_integerChartLift_of_cover (D : TwistedGlobalSectionsModule 𝒮 F)
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {ι : Type u} [Finite ι] {g : ι → S}
    (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : ∀ i, g i ∈ 𝒮 d)
    (hsup : (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) =
      (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    letI := D.moduleInst
    letI := D.gradedSMul
    Function.Bijective (ProjTwistIntegerComparison.chartLift 𝒮 F
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hf) := by
  let := D.moduleInst
  let := D.gradedSMul
  have hcov : ∀ y : ProjectiveSpectrum.top 𝒮,
      ∃ i, y ∈ ProjectiveSpectrum.basicOpen 𝒮 (g i) := by
    intro y
    have hy : y ∈ (⨆ i, ProjectiveSpectrum.basicOpen 𝒮 (g i)) := by rw [hsup]; trivial
    exact Opens.mem_iSup.mp hy
  refine Stacks.SheafOfModules.bijective_degreeZeroLocalizationLiftOfDegree_of_degree
    𝒮 (twistedGlobalSectionsGrading 𝒮 F) hf _ _ (fun y => ?_) (fun n x hx h0 => ?_)
  · obtain ⟨n, x', hx', hval⟩ :=
      ProjTwistChartBijective.exists_numerSection_eq 𝒮 F hqc hf hd hg hsup y
    obtain ⟨s, rfl⟩ := hx'
    exact ⟨n, DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) s,
      (DirectSum.mem_rangeGrading ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m)
        ((n * d : ℕ) : ℤ) _).mpr ⟨s, rfl⟩,
      (numerSection_eq 𝒮 F hf n s).trans hval⟩
  · obtain ⟨s, rfl⟩ := (DirectSum.mem_rangeGrading ℤ
      (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((n * d : ℕ) : ℤ) x).mp hx
    have h0' : ProjTwistLocalComparison.numerSection 𝒮 F hf n
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 f))
        (DirectSum.of (ProjTwistSectionModule.twistSections 𝒮 F) (n * d) s) = 0 :=
      (numerSection_eq 𝒮 F hf n s).symm.trans h0
    obtain ⟨k, hk⟩ := ProjTwistChartBijective.exists_pow_smul_eq_zero_of_numerSection_eq_zero
      𝒮 F hqc hf hd hg hcov n
      (DirectSum.of (ProjTwistSectionModule.twistSections 𝒮 F) (n * d) s)
      ⟨s, rfl⟩ h0'
    refine ⟨k, ?_⟩
    have hpow : f ^ k ∈ 𝒮 (k * d) := by
      simpa [mul_comm] using SetLike.pow_mem_graded (A := 𝒮) k hf
    have hsec : ProjTwistSectionModule.gsmul 𝒮 F hpow (n * d) (k * d + n * d) rfl s = 0 := by
      have h1 := (ProjTwistLocalComparison.smul_of' 𝒮 F hpow
        (rfl : k * d + n * d = k * d + n * d) s).symm.trans hk
      have h2 := congrArg (ProjTwistLocalComparison.degreeComponent 𝒮 F (k * d + n * d)) h1
      simpa using h2
    refine (D.smul_homogeneous (k * d) ((n * d : ℕ) : ℤ) ⟨f ^ k, hpow⟩ s).trans ?_
    have hkz : ((k * d : ℕ) : ℤ) + ((n * d : ℕ) : ℤ) = ((k * d + n * d : ℕ) : ℤ) := by
      push_cast
      ring
    -- `homogeneousScalarTwistedSections` and `gsmul` are the global sections of the two
    -- spellings of multiplication by `f ^ k` on the twists, and those are identified by
    -- `ProjTwistLocalComparison.gsmul_eq` rather than by unfolding.
    have h4 : homogeneousScalarTwistedSections 𝒮 F (k * d) ((n * d : ℕ) : ℤ)
        ⟨f ^ k, hpow⟩ s = 0 :=
      (ProjTwistLocalComparison.gsmul_eq 𝒮 F hpow rfl hkz s).symm.trans hsec
    rw [h4]
    exact map_zero _

/-- **Bijectivity of the chart comparison of Tag 0B5I passes from a power of the element to the
element**, the opens `D₊(f ^ k)` and `D₊(f)` being equal. -/
private theorem bijective_integerChartHom_of_pow (D : TwistedGlobalSectionsModule 𝒮 F)
    {e k j : ℕ} (hf : f ∈ 𝒮 e) (he : 0 < e) (hk : 0 < k) (hfk : f ^ k ∈ 𝒮 j) (hj : 0 < j)
    (h : letI := D.moduleInst
      letI := D.gradedSMul
      Function.Bijective (ProjTwistIntegerComparison.chartHom 𝒮 F
        (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hfk hj).hom) :
    letI := D.moduleInst
    letI := D.gradedSMul
    Function.Bijective (ProjTwistIntegerComparison.chartHom 𝒮 F
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hf he).hom := by
  let := D.moduleInst
  let := D.gradedSMul
  have heq : ProjectiveSpectrum.basicOpen 𝒮 (f ^ k) = ProjectiveSpectrum.basicOpen 𝒮 f :=
    ProjectiveSpectrum.basicOpen_pow 𝒮 f k hk
  exact bijective_of_res_comp_eq 𝒮
    (associatedModuleSheaf 𝒮 (twistedGlobalSectionsGrading 𝒮 F)) F heq.ge heq.le h
    (ProjTwistIntegerComparison.chartHom_restrict 𝒮 F
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hfk hj hf he heq.ge)

/-- **The local half of Tag 0AG5 for the integer-graded module of Tag 0B5I.** -/
private theorem bijective_integerChartHom_of_compactSpace
    (D : TwistedGlobalSectionsModule 𝒮 F)
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    {e : ℕ} (hf : f ∈ 𝒮 e) (he : 0 < e) :
    letI := D.moduleInst
    letI := D.gradedSMul
    Function.Bijective (ProjTwistIntegerComparison.chartHom 𝒮 F
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hf he).hom := by
  obtain ⟨dd, hdd, ι, _, t, hfd, hc, hsup⟩ := exists_pow_cover 𝒮 hf he
  refine bijective_integerChartHom_of_pow 𝒮 F D hf he hdd hfd (Nat.mul_pos hdd he) ?_
  let := D.moduleInst
  let := D.gradedSMul
  refine (Equiv.bijective_comp
    (associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
      hfd (Nat.mul_pos hdd he)).toEquiv
    (ProjTwistIntegerComparison.chartLift 𝒮 F
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D) hfd)).mpr
    (bijective_integerChartLift_of_cover 𝒮 F D hqc hfd (Nat.mul_pos hdd he) hc hsup)

/-- **[Stacks, Tag 0AG5].** Let `S` be a graded ring such that `X = Proj S` is quasi-compact, let
`ℱ` be a quasi-coherent `𝒪_X`-module, and let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the graded
`S`-module of Section 01MM, with the graded module structure `D` of Tag 03GK.  Then the
comparison map `M̃ ⟶ ℱ` of Tag 0B5I is an isomorphism.

The proof is the source's.  Quasi-compactness gives a finite cover of `X` by standard opens
whose defining elements can be taken of one common degree
(`AlgebraicGeometry.Proj.commonDegreeCover`); against such a cover the chart comparison on
`D₊(f)` is bijective for every positive-degree homogeneous `f`; and a morphism of sheaves of
modules bijective on the members of a basis is an isomorphism.  The chart bijectivity is the
source's omitted injectivity and surjectivity argument, which
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistChartBijective.lean` proves
for the natural-graded module of Tag 03GM and which `numerSection_eq` transports to the
integer-graded module of Tag 0B5I. -/
@[ega "II 8.14.8" "special case"]
public theorem isIso_integerComparison_of_compactSpace
    (D : TwistedGlobalSectionsModule 𝒮 F)
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    IsIso (ProjTwistIntegerComparison.integerComparison 𝒮 F D) := by
  refine ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis
    (twistedGlobalSectionsAssociatedSheaf 𝒮 F D) F (positiveBasicOpen 𝒮)
    (isBasis_positiveBasicOpen 𝒮) _ fun p => ?_
  rw [ProjTwistIntegerComparison.integerComparison_app]
  exact bijective_integerChartHom_of_compactSpace 𝒮 F D hqc p.2.choose_spec.2
    p.2.choose_spec.1

/-- **[Stacks, Tag 0AG5].** Let `S` be a graded ring such that `X = Proj S` is quasi-compact and
let `ℱ` be a quasi-coherent `𝒪_X`-module.  Set `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, the graded
`S`-module of Section 01MM with its canonical graded module structure
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule` of Tag 03GK.  Then
the comparison map `M̃ ⟶ ℱ` of Tag 0B5I is an isomorphism.

This is `isIso_integerComparison_of_compactSpace` at the canonical graded module structure, so
nothing is quantified over beyond the graded ring and the sheaf: the hypotheses are exactly the
source's, quasi-compactness of `Proj S` and quasi-coherence of `ℱ`. -/
@[stacks 0AG5 "the comparison `M̃ ⟶ ℱ` of Tag 0B5I is an isomorphism, for `Proj S`
quasi-compact and `ℱ` quasi-coherent", ega "II 8.14.8" "special case"]
public theorem isIso_integerComparison
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F) :
    IsIso (ProjTwistIntegerComparison.integerComparison 𝒮 F
      (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F)) :=
  isIso_integerComparison_of_compactSpace 𝒮 F
    (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F) hqc

end Integer

/-! ### Tag 0AG5's second assertion: the induced maps `M_n → Γ(X, ℱ(n))` are the identities -/

section DegreeOne

open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen)
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover moduleTwistIso
  degreeNToTwistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery (ofTwistedSection)
open Stacks.AlgebraicGeometry.ProjShifted (moduleTwistMap)
open Stacks.AlgebraicGeometry.ModuleTwistIso (moduleTwistMap_tmul)
open Stacks.AlgebraicGeometry.ProjShiftedSections (degreeNToGlobalSections
  degreeNToGlobalSections_apply)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingSection trivializingFun)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (mulTrivSection bijective_mulTrivSection
  pow_mem_degree injective_hom_val_app)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  tensorSheafMap_app_toTensorSheafSection)
open Stacks.GradedModule (shiftedGrading)
open ProjTwistIntegerComparison (degreeComponent degreeComponent_smul_of smul_of_mem_grading
  integerComparison integerComparison_app localComparison positiveChartHom_eq_chartHom
  mulTrivSection_chartHom twistSheafMap_mulTrivSection)
open scoped TensorProduct

variable {g : S}

/-- **Multiplication by `g ^ b` carries the trivializing section `g ^ n` of `𝒪(n e)` to the
trivializing section `g ^ a` of `𝒪(a e)`**, for an *integer* exponent `n` and natural numbers
`a`, `b` with `b + n = a`.

`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistScalarSheafMap_trivializingSection` is the
same law with both exponents natural, which is all the ℕ-graded module of Tag 03GM needs; the
twists of Tag 0AG5's second assertion run over all of `ℤ`, so the first exponent here is an
arbitrary integer.  At a point of `W` the two sections are the fractions
`g ^ n⁺ / g ^ n⁻` and `g ^ a / 1`, so the law is the identity `b + n⁺ = n⁻ + a` of natural
numbers. -/
private theorem twistScalarSheafMap_trivializingSection_int {ee : ℕ} (hg : g ∈ 𝒮 ee) (n : ℤ)
    (a b : ℕ) (hab : (b : ℤ) + n = (a : ℤ))
    (hdeg : ((b * ee : ℕ) : ℤ) + n * (ee : ℤ) = (a : ℤ) * (ee : ℤ))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g) :
    (twistScalarSheafMap 𝒮 (b * ee) (n * (ee : ℤ)) ((a : ℤ) * (ee : ℤ)) hdeg
          ⟨g ^ b, pow_mem_degree 𝒮 hg b⟩).val.app (op W)
        (trivializingSection 𝒮 hg n hW) = trivializingSection 𝒮 hg (a : ℤ) hW := by
  apply Subtype.ext
  funext x
  change LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S (g ^ b)) (trivializingFun 𝒮 n hW x) =
    trivializingFun 𝒮 (a : ℤ) hW x
  rw [trivializingFun, trivializingFun]
  change LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S (g ^ b)) (LocalizedModule.mk _ _) = _
  rw [LocalizedModule.map_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.mk_smul, smul_eq_mul, LinearMap.mul_apply']
  rw [← mul_assoc, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **Multiplication by `g ^ b` carries `t ⊗ g ^ n` to `t ⊗ g ^ a`**, for an *integer* exponent
`n` and natural numbers `a`, `b` with `b + n = a`, and for an arbitrary sheaf of modules.

This is `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection` with
the first exponent an arbitrary integer; as there, the sheaf enters only through the identity on
its sections, so the content is the law on the trivializing sections above. -/
private theorem twistSheafScalarMap_mulTrivSection_int {ee : ℕ} (hg : g ∈ 𝒮 ee) (n : ℤ)
    (a b : ℕ) (hab : (b : ℤ) + n = (a : ℤ))
    (hdeg : ((b * ee : ℕ) : ℤ) + n * (ee : ℤ) = (a : ℤ) * (ee : ℤ))
    (G : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (t : G.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 G (b * ee) (n * (ee : ℤ)) ((a : ℤ) * (ee : ℤ)) hdeg
          ⟨g ^ b, pow_mem_degree 𝒮 hg b⟩).val.app (op W) (mulTrivSection 𝒮 hg n G hW t) =
      mulTrivSection 𝒮 hg (a : ℤ) G hW t := by
  refine Eq.trans (tensorSheafMap_app_toTensorSheafSection
    (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace G (twistingSheaf 𝒮 (n * (ee : ℤ))) G
    (twistingSheaf 𝒮 ((a : ℤ) * (ee : ℤ))) (𝟙 G) _ W t (trivializingSection 𝒮 hg n hW)) ?_
  exact congrArg (fun y => toTensorSheafSection (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace G
      (twistingSheaf 𝒮 ((a : ℤ) * (ee : ℤ))) (op W)
      (t ⊗ₜ[(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op W)] y))
    (twistScalarSheafMap_trivializingSection_int 𝒮 hg n a b hab hdeg hW)

/-- **Multiplication by `g ^ b` is injective on the sections of `ℱ(c)` over an open inside
`D₊(g)`**, for `b + n = a` and `c = n e` the degree of the trivializing section `g ^ n`.

Multiplication by `g ^ n` is a bijection onto the sections of `ℱ(c)` and multiplication by
`g ^ a` is injective, and the first followed by multiplication by `g ^ b` is the second. -/
private theorem injective_twistSheafScalarMap_app {ee : ℕ} (hg : g ∈ 𝒮 ee) (n : ℤ)
    (a b : ℕ) (hab : (b : ℤ) + n = (a : ℤ))
    (hdeg : ((b * ee : ℕ) : ℤ) + n * (ee : ℤ) = (a : ℤ) * (ee : ℤ))
    (G : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g) :
    Function.Injective fun y : (twistSheafOfModules 𝒮 G (n * (ee : ℤ))).val.obj (op W) =>
      (twistSheafScalarMap 𝒮 G (b * ee) (n * (ee : ℤ)) ((a : ℤ) * (ee : ℤ)) hdeg
        ⟨g ^ b, pow_mem_degree 𝒮 hg b⟩).val.app (op W) y := by
  intro y y' hyy'
  obtain ⟨t, rfl⟩ := (bijective_mulTrivSection 𝒮 hg n G hW).surjective y
  obtain ⟨t', rfl⟩ := (bijective_mulTrivSection 𝒮 hg n G hW).surjective y'
  refine congrArg (mulTrivSection 𝒮 hg n G hW)
    ((bijective_mulTrivSection 𝒮 hg (a : ℤ) G hW).injective ?_)
  refine Eq.trans (twistSheafScalarMap_mulTrivSection_int 𝒮 hg n a b hab hdeg G hW t).symm ?_
  exact hyy'.trans (twistSheafScalarMap_mulTrivSection_int 𝒮 hg n a b hab hdeg G hW t')

/-- **The trivializing fraction `g ^ n` cancels the fraction `g ^ n⁻ · m / g ^ n⁺`.**  Both
have value `m / 1`: the numerator gains `g ^ n⁺` and the denominator `g ^ n⁻ · g ^ n⁺`, so the
common factor `g ^ (n⁺ + n⁻)` cancels. -/
private theorem mk_smul_mk_pow {M : Type u} [AddCommGroup M] [Module S M] (P : Submonoid S)
    (x : S) (a b : ℕ) (m : M) (hb : x ^ b ∈ P) (ha : x ^ a ∈ P) :
    (Localization.mk (x ^ a) ⟨x ^ b, hb⟩ : Localization P) •
        (LocalizedModule.mk (x ^ b • m) ⟨x ^ a, ha⟩ : LocalizedModule P M) =
      LocalizedModule.mk m 1 := by
  rw [LocalizedModule.mk_smul_mk]
  exact LocalizedModule.mk_eq.mpr ⟨1, by simp [smul_smul, mul_comm]⟩

/-- **The fraction `g ^ n⁻ · m / g ^ n⁺` of `M̃` over `D₊(g)`, multiplied by the trivializing
section `g ^ n`, is the restriction of `u`**, for any global section `u` of `M̃(n)` whose image
under Equation 01MQ `M̃(n) ⟶ M(n)~` has the value `m / 1` at every point.

Both sides are sections of `M̃(n)` over `D₊(g)` and Equation 01MQ is injective on them, so it is
enough to compare their images, which are sections of `M(n)~` and so are compared point by
point: the left one is the trivializing value `g ^ n⁺ / g ^ n⁻` acting on the fraction, by
`Stacks.AlgebraicGeometry.ModuleTwistIso.moduleTwistMap_tmul`, and that product is `m / 1` by
`mk_smul_mk_pow`; the right one is `m / 1` by hypothesis. -/
private theorem mulTrivSection_degreeZeroFraction (D : TwistedGlobalSectionsModule 𝒮 F)
    (hcover : DegreeOneCover 𝒮) (hg : g ∈ 𝒮 1) (n : ℤ)
    (hle : ProjectiveSpectrum.basicOpen 𝒮 g ≤ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
    (m : twistedGlobalSections 𝒮 F)
    (hx' : letI := D.moduleInst; letI := D.gradedSMul
      g ^ (-n).toNat • m ∈ twistedGlobalSectionsGrading 𝒮 F (n.toNat • ((1 : ℕ) : ℤ)))
    (u : (twistSheafOfModules 𝒮 (twistedGlobalSectionsAssociatedSheaf 𝒮 F D)
      (n * ((1 : ℕ) : ℤ))).val.obj (op ⊤))
    (hu : letI := D.moduleInst; letI := D.gradedSMul
      ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)),
        (((moduleTwistMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
            (n * ((1 : ℕ) : ℤ))).val.app (op ⊤)).hom u).1 y =
          LocalizedModule.mk m (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl)) :
    letI := D.moduleInst
    letI := D.gradedSMul
    mulTrivSection 𝒮 hg n (twistedGlobalSectionsAssociatedSheaf 𝒮 F D)
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))
        (degreeZeroToSection 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g
          (degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
            (g ^ (-n).toNat • m) hx')) =
      (twistSheafOfModules 𝒮 (twistedGlobalSectionsAssociatedSheaf 𝒮 F D)
        (n * ((1 : ℕ) : ℤ))).val.map (homOfLE hle).op u := by
  let := D.moduleInst
  let := D.gradedSMul
  refine injective_hom_val_app
    (moduleTwistIso 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover (n * ((1 : ℕ) : ℤ)))
    (op (ProjectiveSpectrum.basicOpen 𝒮 g)) ?_
  refine Subtype.ext (funext fun y => ?_)
  refine Eq.trans (moduleTwistMap_tmul 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
    (n * ((1 : ℕ) : ℤ)) (ProjectiveSpectrum.basicOpen 𝒮 g) _
    (trivializingSection 𝒮 hg n (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))) y) ?_
  refine Eq.trans ?_ (congrArg (fun w => w.1 y) (PresheafOfModules.naturality_apply
    (moduleTwistMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F) (n * ((1 : ℕ) : ℤ))).val
    (homOfLE hle).op u)).symm
  refine Eq.trans ?_ (hu ⟨y.1, trivial⟩).symm
  have htriv : (trivializingSection 𝒮 hg n
        (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))).1 y =
      Localization.mk (g ^ n.toNat)
        ⟨g ^ (-n).toNat,
          y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
            (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g) y.2) _⟩ := rfl
  rw [degreeZeroToSection_fraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
    (g ^ (-n).toNat • m) hx' y, htriv]
  exact mk_smul_mk_pow _ g n.toNat (-n).toNat m _ _

/-- **The local half of Tag 0AG5's second assertion**, on the standard open of a degree-one
element `g`.

The data of the assertion are reduced to what the computation on `D₊(g)` uses: a section `u` of
`M̃(c)` over `X` whose image under Equation 01MQ `M̃(c) ⟶ M(c)~` has the value `m / 1` at every
point — which is what Equation 0AG3 produces from a homogeneous `m` of degree `n` — and a
section `s` of `ℱ(c)` over `X` whose product with `g ^ n⁻` is the degree-`n⁺` component of
`g ^ n⁻ · m`, which is what the identification `M_n = Γ(X, ℱ(n))` gives.

Writing `n = n⁺ - n⁻`, the fraction `z = g ^ n⁻ · m / g ^ n⁺` is a section of `M̃` over `D₊(g)`
whose product with the trivializing section `g ^ n` is `u`: both have the value `m / 1` at every
point, and Equation 01MQ is injective on sections.  The comparison of Tag 0B5I carries `z` to
the section of `ℱ` whose product with `g ^ n⁺` is the restriction of the degree-`n⁺` component
of `g ^ n⁻ · m`, and multiplying `t ⊗ g ^ n` by `g ^ n⁻` is `t ⊗ g ^ n⁺`, so that section
multiplied by `g ^ n` is the restriction of `s`. -/
private theorem localIdentity_of_pointwise (D : TwistedGlobalSectionsModule 𝒮 F)
    (hcover : DegreeOneCover 𝒮) (hg : g ∈ 𝒮 1) (n : ℤ) {c : ℤ} (hc : n * ((1 : ℕ) : ℤ) = c)
    (hdeg : (((-n).toNat * 1 : ℕ) : ℤ) + c = ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)))
    (hle : ProjectiveSpectrum.basicOpen 𝒮 g ≤ (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
    (m : twistedGlobalSections 𝒮 F)
    (u : (twistSheafOfModules 𝒮 (twistedGlobalSectionsAssociatedSheaf 𝒮 F D) c).val.obj (op ⊤))
    (hu : letI := D.moduleInst; letI := D.gradedSMul
      ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)),
        (((moduleTwistMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F) c).val.app (op ⊤)).hom u).1 y =
          LocalizedModule.mk m (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl))
    (s : twistedSectionsComponent 𝒮 F c)
    (hx : letI := D.moduleInst; letI := D.gradedSMul
      g ^ (-n).toNat • m ∈ twistedGlobalSectionsGrading 𝒮 F ((n.toNat * 1 : ℕ) : ℤ))
    (hs : letI := D.moduleInst; letI := D.gradedSMul
      degreeComponent 𝒮 F ((n.toNat * 1 : ℕ) : ℤ) (g ^ (-n).toNat • m) =
        (twistSheafScalarMap 𝒮 F ((-n).toNat * 1) c ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)) hdeg
          ⟨g ^ (-n).toNat, pow_mem_degree 𝒮 hg _⟩).val.app (op ⊤) s) :
    letI := D.moduleInst
    letI := D.gradedSMul
    (twistSheafOfModules 𝒮 F c).val.map (homOfLE hle).op
        ((twistSheafMap 𝒮 (integerComparison 𝒮 F D) c).val.app (op ⊤) u) =
      (twistSheafOfModules 𝒮 F c).val.map (homOfLE hle).op s := by
  subst hc
  let := D.moduleInst
  let := D.gradedSMul
  have hsmul := isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D
  refine Eq.trans (PresheafOfModules.naturality_apply
    (twistSheafMap 𝒮 (integerComparison 𝒮 F D) (n * ((1 : ℕ) : ℤ))).val
    (homOfLE hle).op u).symm ?_
  -- the degree-`n⁺` fraction `g ^ n⁻ · m / g ^ n⁺` as a section of `M̃` over `D₊(g)`
  have hx' : g ^ (-n).toNat • m ∈
      twistedGlobalSectionsGrading 𝒮 F (n.toNat • ((1 : ℕ) : ℤ)) := by
    simpa [nsmul_eq_mul] using hx
  have hzequiv : associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
        hg Nat.one_pos (degreeZeroToSection 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g
          (degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
            (g ^ (-n).toNat • m) hx')) =
      degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
        (g ^ (-n).toNat • m) hx' :=
    LinearEquiv.symm_apply_apply _ _
  have hzfrac : ((associatedModuleSheafStandardOpenEquiv 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          hg Nat.one_pos (degreeZeroToSection 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g
            (degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
              (g ^ (-n).toNat • m) hx')) :
        GradedModuleDegreeZeroLocalization 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g) :
        LocalizedModule.Away g (twistedGlobalSections 𝒮 F)) =
      LocalizedModule.mk (g ^ (-n).toNat • m) ⟨g ^ n.toNat, by exact ⟨n.toNat, rfl⟩⟩ := by
    rw [hzequiv]
    rfl
  -- the fraction, multiplied by the trivializing section `g ^ n`, is the restriction of `u`
  have hmul := mulTrivSection_degreeZeroFraction 𝒮 F D hcover hg n hle m hx' u hu
  refine Eq.trans (congrArg (fun x => ((twistSheafMap 𝒮 (integerComparison 𝒮 F D)
      (n * ((1 : ℕ) : ℤ))).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 g))) x) hmul.symm) ?_
  refine Eq.trans (twistSheafMap_mulTrivSection 𝒮 hg n (integerComparison 𝒮 F D)
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) _) ?_
  -- the comparison on `D₊(g)` is the chart comparison of Tag 0B5I
  have hchart : (integerComparison 𝒮 F D).val.app (op (ProjectiveSpectrum.basicOpen 𝒮 g))
        (degreeZeroToSection 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g
          (degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
            (g ^ (-n).toNat • m) hx')) =
      ProjTwistIntegerComparison.chartHom 𝒮 F hsmul hg Nat.one_pos
        (degreeZeroToSection 𝒮 (twistedGlobalSectionsGrading 𝒮 F) g
          (degreeZeroFraction 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hg n.toNat
            (g ^ (-n).toNat • m) hx')) := by
    refine Eq.trans (congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ).toFun)
      (integerComparison_app 𝒮 F D ⟨g, ⟨1, Nat.one_pos, hg⟩⟩)) _) ?_
    exact congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ).toFun)
      (positiveChartHom_eq_chartHom 𝒮 F hsmul ⟨g, ⟨1, Nat.one_pos, hg⟩⟩ hg Nat.one_pos)) _
  refine Eq.trans (congrArg (mulTrivSection 𝒮 hg n F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g))) hchart) ?_
  -- both sides, multiplied by `g ^ n⁻`, are the restriction of the degree-`n⁺` component
  refine injective_twistSheafScalarMap_app 𝒮 hg n n.toNat (-n).toNat (by omega) hdeg F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) ?_
  refine Eq.trans (twistSheafScalarMap_mulTrivSection_int 𝒮 hg n n.toNat (-n).toNat
    (by omega) hdeg F (le_refl (ProjectiveSpectrum.basicOpen 𝒮 g)) _) ?_
  refine Eq.trans (mulTrivSection_chartHom 𝒮 F hsmul hg Nat.one_pos _ n.toNat
    (g ^ (-n).toNat • m) hx hzfrac) ?_
  refine Eq.trans (congrArg ((twistSheafOfModules 𝒮 F ((n.toNat : ℤ) * ((1 : ℕ) : ℤ))).val.map
    (homOfLE hle).op) hs) ?_
  exact (PresheafOfModules.naturality_apply
    (twistSheafScalarMap 𝒮 F ((-n).toNat * 1) (n * ((1 : ℕ) : ℤ))
      ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)) hdeg ⟨g ^ (-n).toNat, pow_mem_degree 𝒮 hg _⟩).val
    (homOfLE hle).op s).symm

/-- **[Stacks, Tag 0AG5], second assertion.** Let `S` be a graded ring such that `X = Proj S` is
quasi-compact, let `ℱ` be a quasi-coherent `𝒪_X`-module and let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be
the graded `S`-module of Section 01MM, with a graded module structure `D` of Tag 03GK.  If `X`
is covered by the standard opens `D₊(f)` of the elements `f` of degree one, then the induced map
`M_n → Γ(X, ℱ(n))` is the identity map, for every `n : ℤ`.

The induced map is the composite of Equation 0AG3, `M_n → Γ(X, M̃(n))`, with the global sections
of the `n`-th twist of the comparison morphism `M̃ ⟶ ℱ` of Tag 0B5I; the identification
`M_n = Γ(X, ℱ(n))` under which it is the identity is the inclusion of the degree-`n` summand,
`Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.ofTwistedSection`.  The covering hypothesis
is load-bearing twice over: Equation 0AG3 is not defined without it, and it is what makes the
standard opens of the degree-one elements a cover on which the identity may be checked.

The source omits the proof.  The argument is `localIdentity_of_pointwise` on each `D₊(g)` with
`deg g = 1`, where `M̃(n)` and `ℱ(n)` are both trivialized by the section `g ^ n`: Equation 0AG3
sends `m` to the global section whose restriction is the fraction `g ^ n⁻ · m / g ^ n⁺` times
`g ^ n`, the chart comparison of Tag 0B5I carries that fraction to the section whose product
with `g ^ n⁺` is the restriction of the degree-`n⁺` component of `g ^ n⁻ · m`, and that
component is `g ^ n⁻` times `s` because `m` is the element of `M_n` named by `s`.  Quasi-compact-
ness and quasi-coherence are the source's standing hypotheses on the lemma and are not used by
this clause. -/
public theorem twistSheafMap_integerComparison_degreeNToTwistedGlobalSections_of_module
    (D : TwistedGlobalSectionsModule 𝒮 F)
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (_hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    (hcover : DegreeOneCover 𝒮) (n : ℤ) (s : twistedSectionsComponent 𝒮 F n) :
    letI := D.moduleInst
    letI := D.gradedSMul
    (twistSheafMap 𝒮 (integerComparison 𝒮 F D) n).val.app (op ⊤)
        (degreeNToTwistedGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n
          (ofTwistedSection 𝒮 F n s)) = s := by
  let := D.moduleInst
  let := D.gradedSMul
  have hsmul := isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D
  have hdeg : (((-n).toNat * 1 : ℕ) : ℤ) + n = ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)) := by
    push_cast
    omega
  -- the two local data, at every degree-one element
  have hx : ∀ (h : S), h ∈ 𝒮 1 →
      h ^ (-n).toNat • (ofTwistedSection 𝒮 F n s : twistedGlobalSections 𝒮 F) ∈
        twistedGlobalSectionsGrading 𝒮 F ((n.toNat * 1 : ℕ) : ℤ) := by
    intro h hh
    refine smul_of_mem_grading 𝒮 F hsmul (pow_mem_degree 𝒮 hh _) ?_ s
    push_cast
    omega
  have hs : ∀ (h : S) (hh : h ∈ 𝒮 1),
      degreeComponent 𝒮 F ((n.toNat * 1 : ℕ) : ℤ)
          (h ^ (-n).toNat • (ofTwistedSection 𝒮 F n s : twistedGlobalSections 𝒮 F)) =
        (twistSheafScalarMap 𝒮 F ((-n).toNat * 1) n ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)) hdeg
          ⟨h ^ (-n).toNat, pow_mem_degree 𝒮 hh _⟩).val.app (op ⊤) s :=
    fun _ hh => degreeComponent_smul_of 𝒮 F hsmul (pow_mem_degree 𝒮 hh _) hdeg s
  -- Equation 01MQ carries Equation 0AG3's global section to the section with value `m / 1`
  have hu : ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)),
      (((moduleTwistMap 𝒮 (twistedGlobalSectionsGrading 𝒮 F) n).val.app (op ⊤)).hom
          (degreeNToTwistedGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n
            (ofTwistedSection 𝒮 F n s))).1 y =
        LocalizedModule.mk (ofTwistedSection 𝒮 F n s : twistedGlobalSections 𝒮 F)
          (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
    intro y
    refine Eq.trans (congrArg (fun w => w.1 y)
      (Stacks.SheafOfModules.hom_val_app_inv_val_app
        (moduleTwistIso 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n) (op ⊤)
        (degreeNToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) n
          (ofTwistedSection 𝒮 F n s)))) ?_
    exact degreeNToGlobalSections_apply 𝒮 (twistedGlobalSectionsGrading 𝒮 F) n
      (ofTwistedSection 𝒮 F n s) y.1
  -- the identity is local on the cover by the standard opens of the degree-one elements
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover (twistSheafOfModules 𝒮 F n)
    (fun h : 𝒮 1 => ProjectiveSpectrum.basicOpen 𝒮 (h : S)) (fun _ => le_top)
    (fun y _ => ?_) _ s (fun h => ?_)
  · have hy : y ∈ (⨆ h : 𝒮 1, _root_.AlgebraicGeometry.Proj.basicOpen 𝒮 (h : S)) := by
      rw [hcover]
      trivial
    exact Opens.mem_iSup.mp hy
  · exact localIdentity_of_pointwise 𝒮 F D hcover h.2 n (by push_cast; ring) hdeg le_top
      (ofTwistedSection 𝒮 F n s : twistedGlobalSections 𝒮 F) _ hu s (hx (h : S) h.2)
      (hs (h : S) h.2)

/-- **[Stacks, Tag 0AG5], second assertion**, for the canonical graded module structure of
Tag 03GK: if `Proj S` is covered by the standard opens of the degree-one elements then the
induced maps `M_n → Γ(X, ℱ(n))` are the identity maps.

This is `twistSheafMap_integerComparison_degreeNToTwistedGlobalSections_of_module` at the
canonical graded module structure
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`, so nothing is
quantified over beyond the graded ring, the sheaf and the source's own hypotheses. -/
@[stacks 0AG5 "part (2): if `Proj S` is covered by the standard opens `D₊(f)` with `deg f = 1`
then the induced maps `M_n → Γ(X, ℱ(n))` are the identity maps"]
public theorem twistSheafMap_integerComparison_degreeNToTwistedGlobalSections
    [CompactSpace (_root_.AlgebraicGeometry.Proj 𝒮)]
    (hqc : SheafOfModules.IsQuasicoherent
      (R := (_root_.AlgebraicGeometry.Proj 𝒮).ringCatSheaf) F)
    (hcover : DegreeOneCover 𝒮) (n : ℤ) (s : twistedSectionsComponent 𝒮 F n) :
    letI := (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F).moduleInst
    letI := (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F).gradedSMul
    (twistSheafMap 𝒮
          (integerComparison 𝒮 F (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F))
          n).val.app (op ⊤)
        (degreeNToTwistedGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n
          (ofTwistedSection 𝒮 F n s)) = s :=
  twistSheafMap_integerComparison_degreeNToTwistedGlobalSections_of_module 𝒮 F
    (ProjTwistedSections.twistedGlobalSectionsModule 𝒮 F) hqc hcover n s

end DegreeOne

end Stacks.AlgebraicGeometry.ProjTwistComparisonCompact

end
