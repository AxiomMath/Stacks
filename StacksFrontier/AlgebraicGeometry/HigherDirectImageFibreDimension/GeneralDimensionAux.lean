module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.GlobalSheafCohomology
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafStalkSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# The cohomology of `ℱ / 𝔪 ⁿ ℱ` dies above the dimension of the fibre

This file supplies the geometric input to the proof of [Stacks, Tag 02V7] over an affine
Noetherian base `Spec A`: for a maximal ideal `𝔪` of `A` and a quasi-coherent `ℱ` on `X`, the
cohomology `Hᵖ(X, ℱ / 𝔪ⁿ ℱ)` vanishes for every `p` above the dimension of the fibre of
`f : X ⟶ Spec A` over `𝔪`, and for every `n`.

Three steps, each an existing result read at this situation.

* `ℱ / 𝔪ⁿ ℱ` is a direct image from the closed subscheme cut out by `𝔪ⁿ 𝒪_X`
  ([Stacks, Tag 0EL1], `Stacks.Algebraization.idealQuotientPushforwardIso`), and cohomology does
  not change along a closed immersion ([Stacks, Tag 02UV], in the form
  `Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward`). So the question moves to
  that subscheme.
* The subscheme is Noetherian and its underlying space lies in the fibre: a point of the support
  of `𝔪ⁿ 𝒪_X` lies over `V(𝔪ⁿ)`, which for `𝔪` maximal is the single point `𝔪`
  (`Stacks.Algebraization.support_baseIdealSheaf_le`). Its dimension is therefore at most that of
  the fibre.
* On a Noetherian scheme the cohomology of *any* sheaf of modules vanishes above the dimension:
  this is Grothendieck's theorem [Stacks, Tag 02UZ] for the underlying abelian sheaf
  (`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`) read
  through the comparison of [Stacks, Tag 01F1] (1)
  (`Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH`).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.FibreDimension`.

* `isZero_hgroup_of_topologicalKrullDim_le`: Grothendieck vanishing for sheaves of modules on a
  Noetherian scheme. No quasi-coherence is needed.
* `isZero_hgroup_idealPowerQuotient`: the vanishing for `ℱ / 𝒥ⁿ ℱ` above the dimension of the
  closed subscheme cut out by `𝒥ⁿ`, for an arbitrary quasi-coherent ideal sheaf `𝒥`.
* `support_pow_baseIdealSheaf_subset` and `topologicalKrullDim_subscheme_pow_baseIdealSheaf_le`:
  the support of `𝔪ⁿ 𝒪_X` lies in the fibre over `𝔪`, and so its dimension is bounded by the
  fibre's.
* `isZero_hgroup_idealPowerQuotient_baseIdealSheaf`: the three steps composed, which is what the
  proof over an affine base consumes.
* `topologicalKrullDim_le_of_isInducing_of_range_subset` and
  `isNoetherian_of_isClosedImmersion`: the two general facts used along the way.

## Implementation notes

Cohomology is `Hgroup X.ringCatSheaf ⊤ p ℱ`, the abelian-group-valued right derived functor of
global sections, because that is the spelling in which the closed-immersion comparison and
Grothendieck vanishing both live. The bridge to the module-valued
`((moduleGlobalSections X).rightDerived p).obj ℱ` of the rest of this directory is
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`, and it is
taken in `GeneralDimensionAffine.lean` rather than here.

`𝔪 ⁿ 𝒪_X` is `(baseIdealSheaf A 𝔪 f) ^ n`, equal to `baseIdealSheaf A (𝔪 ^ n) f` by
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow`; the two spellings are interchanged where
each is the one the cited lemma is stated for.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.FibreDimension

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 02UZ] for sheaves of modules on a Noetherian scheme.** If `X` is a Noetherian
scheme of topological Krull dimension at most `d`, then `Hᵖ(X, ℱ) = 0` for every sheaf of
`𝒪_X`-modules `ℱ` and every `p > d`. Neither quasi-coherence of `ℱ` nor any hypothesis on a
structure morphism of `X` is needed: the comparison of [Stacks, Tag 01F1] (1) identifies the
cohomology with that of the underlying abelian sheaf, where the statement is Grothendieck's
theorem on a Noetherian space. -/
theorem isZero_hgroup_of_topologicalKrullDim_le {X : Scheme.{u}} [IsNoetherian X]
    (F : X.Modules) {d p : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hp : d < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  rw [Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
  exact Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
    hdim hp _

/-- **The cohomology of `ℱ / 𝒥ⁿ ℱ` vanishes above the dimension of the closed subscheme cut out
by `𝒥ⁿ`.** By [Stacks, Tag 0EL1] the quotient is the direct image of its own restriction along
the closed immersion `V(𝒥ⁿ) ⟶ X`, and cohomology does not change along a closed immersion
([Stacks, Tag 02UV]); on `V(𝒥ⁿ)` the vanishing is Grothendieck's theorem. -/
theorem isZero_hgroup_idealPowerQuotient {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsQuasicoherent] [IsNoetherian ((J ^ n).subscheme)] {d p : ℕ}
    (hdim : topologicalKrullDim ((J ^ n).subscheme) ≤ (d : WithBot ℕ∞)) (hp : d < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Algebraization.idealPowerQuotient J n F)) := by
  have hv : ((J ^ n).subschemeι).ker = J ^ n := Scheme.IdealSheafData.ker_subschemeι _
  refine IsZero.of_iso ?_
    ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
      (Stacks.Algebraization.idealQuotientPushforwardIso J n F ((J ^ n).subschemeι) hv))
  exact (Stacks.Cohomology.ClosedImmersion.isZero_hgroup_iff_pushforward _ _ p).mp
    (isZero_hgroup_of_topologicalKrullDim_le _ hdim hp)

/-- **An inducing map whose range lies in `S` does not raise the Krull dimension beyond that of
`S`.** Corestricting the map to `S` is still inducing, and an inducing map never raises the
dimension (`Topology.IsInducing.topologicalKrullDim_le`). -/
theorem topologicalKrullDim_le_of_isInducing_of_range_subset
    {Y X : Type u} [TopologicalSpace Y] [TopologicalSpace X] {g : Y → X}
    (hg : Topology.IsInducing g) {S : Set X} (hS : Set.range g ⊆ S) :
    topologicalKrullDim Y ≤ topologicalKrullDim S := by
  have hcont : Continuous fun y : Y => (⟨g y, hS ⟨y, rfl⟩⟩ : S) :=
    Continuous.subtype_mk hg.continuous _
  have hk : Topology.IsInducing fun y : Y => (⟨g y, hS ⟨y, rfl⟩⟩ : S) :=
    Topology.IsInducing.of_comp hcont continuous_subtype_val hg
  exact hk.topologicalKrullDim_le

open Stacks.Cohomology.FormalFunctions in
/-- **The support of `𝔪ⁿ 𝒪_X` lies in the fibre over `𝔪`**, for `𝔪` a maximal ideal of the base
ring. A point of the support lies over `V(𝔪ⁿ)`
(`Stacks.Algebraization.support_baseIdealSheaf_le`), and a prime containing `𝔪ⁿ` contains `𝔪`,
hence equals it. For `n = 0` the ideal is the unit ideal and the support is empty. -/
theorem support_pow_baseIdealSheaf_subset {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (m : Ideal A) [m.IsMaximal] (y : Spec (.of A))
    (hy : y.asIdeal = m) (n : ℕ) :
    ((((baseIdealSheaf A m f) ^ n).support : Set X)) ⊆ f.base ⁻¹' {y} := by
  intro x hx
  rw [← baseIdealSheaf_pow A m f n] at hx
  have h : m ^ n ≤ (f.base x).asIdeal :=
    Stacks.Algebraization.support_baseIdealSheaf_le (m ^ n) f hx
  have hprime : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  have hm : m ≤ (f.base x).asIdeal := by
    rcases n with _ | k
    · rw [pow_zero, Ideal.one_eq_top] at h
      exact absurd (top_le_iff.mp h) hprime.ne_top
    · exact (Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero k)).mp h
  have : (f.base x).asIdeal = m := ((‹m.IsMaximal›.eq_of_le hprime.ne_top hm)).symm
  exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext (this.trans hy.symm))

/-- **The source of a closed immersion into a Noetherian scheme is Noetherian.** It is locally
Noetherian because a closed immersion is affine with surjective comorphism, and quasi-compact
because a closed subspace of a compact space is compact. -/
theorem isNoetherian_of_isClosedImmersion {V X : Scheme.{u}} (v : V ⟶ X)
    [IsClosedImmersion v] [IsNoetherian X] : IsNoetherian V :=
  have : IsLocallyNoetherian V :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion v
  have : CompactSpace V := v.isClosedEmbedding.compactSpace
  { }

open Stacks.Cohomology.FormalFunctions in
/-- **The closed subscheme cut out by `𝔪ⁿ 𝒪_X` has dimension at most that of the fibre over
`𝔪`.** Its underlying space embeds in `X` with image the support of `𝔪ⁿ 𝒪_X`, which lies in the
fibre, and the fibre of a morphism of schemes is homeomorphic to the set-theoretic fibre. -/
theorem topologicalKrullDim_subscheme_pow_baseIdealSheaf_le
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (m : Ideal A) [m.IsMaximal] (y : Spec (.of A)) (hy : y.asIdeal = m) (n : ℕ) :
    topologicalKrullDim (((baseIdealSheaf A m f) ^ n).subscheme) ≤
      topologicalKrullDim (f.fiber y) := by
  have hrange : Set.range (((baseIdealSheaf A m f) ^ n).subschemeι).base ⊆ f.base ⁻¹' {y} := by
    rw [show Set.range (((baseIdealSheaf A m f) ^ n).subschemeι).base =
        ((((baseIdealSheaf A m f) ^ n).support : Set X)) from
      Scheme.IdealSheafData.range_subschemeι _]
    exact support_pow_baseIdealSheaf_subset f m y hy n
  have h1 := topologicalKrullDim_le_of_isInducing_of_range_subset
    (((baseIdealSheaf A m f) ^ n).subschemeι).isClosedEmbedding.isInducing hrange
  have h2 : topologicalKrullDim (f.fiber y) = topologicalKrullDim (f.base ⁻¹' {y}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
  exact h2 ▸ h1

open Stacks.Cohomology.FormalFunctions in
/-- **The cohomology of `ℱ / 𝔪ⁿ ℱ` vanishes above the dimension of the fibre over `𝔪`.** This is
the geometric half of the proof of [Stacks, Tag 02V7] over an affine Noetherian base: the two
previous statements composed. -/
theorem isZero_hgroup_idealPowerQuotient_baseIdealSheaf
    {A : Type u} [CommRing A] {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    (m : Ideal A) [m.IsMaximal] (y : Spec (.of A)) (hy : y.asIdeal = m)
    (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] {d p : ℕ}
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) (hp : d < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (Stacks.Algebraization.idealPowerQuotient (baseIdealSheaf A m f) n F)) :=
  have := isNoetherian_of_isClosedImmersion (((baseIdealSheaf A m f) ^ n).subschemeι)
  isZero_hgroup_idealPowerQuotient _ n F
    ((topologicalKrullDim_subscheme_pow_baseIdealSheaf_le f m y hy n).trans hdim) hp

end Stacks.AlgebraicGeometry.FibreDimension

end
