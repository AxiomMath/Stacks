module

public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Fibre
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Bijective

/-!
# The module comparison of a degreewise localization is bijective on sections

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is, in each degree, the
localization away from a degree-zero element `g` of `𝒜`
(`Stacks.GradedLocalization.IsAwayDegreewise`), with `ℬ₊ ≤ 𝒜₊.map φ` so that
`AlgebraicGeometry.Proj.map φ` exists, and let `f : M → N` be a `φ`-semilinear map of graded
modules which is, in each degree, the localization away from `g`
(`Stacks.GradedLocalization.IsAwayDegreewiseModule`). This file proves that the comparison of
associated module sheaves `Stacks.ProjModuleComparison.sectionsMap` is a bijection over every
open of `Proj 𝒜` on which `g` does not vanish; that is, the sheaf attached to a degreewise
localization is the degreewise localization of the sheaf.

This is the module companion of `Stacks.ProjTwistComparison.bijective_sectionsMap`, which is the
case `M = A` with its grading shifted.

## Main results

* `Stacks.ProjModuleComparison.injective_sectionsMap` and
  `Stacks.ProjModuleComparison.surjective_sectionsMap`, assembled into
  `Stacks.ProjModuleComparison.bijective_sectionsMap`: over an open on which `g` does not vanish,
  the comparison of homogeneous fraction families of a graded module is a bijection.
* `Stacks.ProjModuleComparison.exists_fibre_localizedModuleMap_eq`: the pointwise preimage of a
  fraction family exists and is unique.
* `Stacks.ProjModuleComparison.locallyModuleFraction_of_localizedModuleMap_eq`: that pointwise
  preimage is again a family of local homogeneous fractions.

## Implementation notes

The comparison of points of `Proj ℬ` and `Proj 𝒜` (injectivity, surjectivity onto the
nonvanishing locus, openness of the image) is taken from `Stacks.ProjTwistComparison`, where it
is stated for an arbitrary `φ`. The characterising property of the pointwise preimage at a point
`x` of `Proj 𝒜` is stated for *every* point of the preimage open lying over `x`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. This is the comparison of the sheaves attached to a graded module on two
charts of a relative `Proj` over the overlap of the charts; nothing is glued here, and nothing is
proved about the relative `Proj` situation itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open scoped Stacks.GradedLocalization

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjModuleComparison

variable {A B M N : Type u} {σ τ μ ν : Type u}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  (f : M →ₛₗ[φ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i) {g : A}

/-! ### Lifting a homogeneous fraction -/

omit [AddSubgroupClass μ M] [DirectSum.Decomposition 𝒨] in
/-- **Multiplying by a power of a degree-zero element preserves module degrees.** -/
public theorem pow_smul_mem_grading (hg : g ∈ 𝒜 0) (j : ℕ) {x : M} {i : ℤ} (hx : x ∈ 𝒨 i) :
    g ^ j • x ∈ 𝒨 i := by
  have hgj : g ^ j ∈ 𝒜 0 := by simpa using SetLike.pow_mem_graded j hg
  have hmem : g ^ j • x ∈ 𝒨 ((0 : ℕ) +ᵥ i) := SetLike.GradedSMul.smul_mem hgj hx
  have hvadd : ((0 : ℕ) +ᵥ i) = i := by
    show ((0 : ℕ) : ℤ) + i = i
    simp
  rwa [hvadd] at hmem

/-- **Clearing denominators.** A fraction over `𝒜` whose numerator and denominator become
`φ g ^ i` times `m` and `s` is carried by the comparison of localized modules to the fraction
`m / s`. -/
public theorem localizedModuleMap_mk_eq {I : Ideal A} [I.IsPrime] {J : Ideal B} [J.IsPrime]
    (hIJ : I = J.comap φ.toRingHom) {m' : M} {s' : A} {m : N} {s : B} {i : ℕ}
    (hs' : s' ∈ I.primeCompl) (hs : s ∈ J.primeCompl)
    (hmeq : f m' = φ g ^ i • m) (hseq : φ s' = φ g ^ i * s) :
    localizedModuleMap φ f I J hIJ (LocalizedModule.mk m' ⟨s', hs'⟩)
      = LocalizedModule.mk m ⟨s, hs⟩ := by
  rw [localizedModuleMap_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, coe_localizedDenomMap, hmeq, hseq, smul_smul]
  exact congrArg (fun c : B => c • m) (mul_comm _ _)

/-! ### Inverting the comparison of fraction families -/

/-- If `y` maps to `x` under the comparison of points, then the prime of `x` is the preimage of
the prime of `y`. -/
private theorem asHomogeneousIdeal_eq_comap_of_comapFun_eq {x : ProjectiveSpectrum.top 𝒜}
    {y : ProjectiveSpectrum.top ℬ} (hxy : ProjectiveSpectrum.comapFun φ hφ y = x) :
    x.asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap φ.toRingHom := by
  rw [← hxy]; rfl

omit [SetLike.GradedSMul 𝒜 𝒨] in
/-- **The pointwise preimage of a fraction family.** Over an open on which `g` does not vanish,
every point `x` carries a unique element of the module fibre whose image under the comparison of
localized modules at *any* point of the preimage open above `x` is the given family `b`. -/
public theorem exists_fibre_localizedModuleMap_eq (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal)
    (b : moduleSections ℬ 𝒩 (W.comap (ProjectiveSpectrum.comap φ hφ)))
    (x : W) :
    ∃ z : ModuleFiber (M := M) 𝒜 x.1,
      ∀ (y : W.comap (ProjectiveSpectrum.comap φ hφ))
        (_ : ProjectiveSpectrum.comapFun φ hφ y.1 = x.1)
        (hIJ : x.1.asHomogeneousIdeal.toIdeal
          = y.1.asHomogeneousIdeal.toIdeal.comap φ.toRingHom),
        localizedModuleMap φ f x.1.asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal hIJ z = b.1 y := by
  obtain ⟨y₀, hy₀⟩ := Stacks.ProjTwistComparison.exists_comapFun_eq φ h hg hφ (hW x)
  have hy₀W : ProjectiveSpectrum.comapFun φ hφ y₀ ∈ W := by rw [hy₀]; exact x.2
  obtain ⟨z, hz⟩ := surjective_localizedModuleMap φ f x.1.asHomogeneousIdeal.toIdeal
    y₀.asHomogeneousIdeal.toIdeal h hmod (asHomogeneousIdeal_eq_comap_of_comapFun_eq φ hφ hy₀)
    (b.1 ⟨y₀, hy₀W⟩)
  refine ⟨z, fun y hxy hIJ => ?_⟩
  obtain rfl : y = ⟨y₀, hy₀W⟩ :=
    Subtype.ext (Stacks.ProjTwistComparison.injective_comapFun φ h hg hφ (hxy.trans hy₀.symm))
  exact hz

/-- The pointwise preimage of a fraction family is again a family of local homogeneous fractions
of the right degree. -/
public theorem locallyModuleFraction_of_localizedModuleMap_eq (h : IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g)
    (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal)
    (b : moduleSections ℬ 𝒩 (W.comap (ProjectiveSpectrum.comap φ hφ)))
    (a : ∀ x : W, ModuleFiber (M := M) 𝒜 x.1)
    (ha : ∀ (x : W) (y : W.comap (ProjectiveSpectrum.comap φ hφ)),
      ProjectiveSpectrum.comapFun φ hφ y.1 = x.1 →
      ∀ hIJ : x.1.asHomogeneousIdeal.toIdeal
          = y.1.asHomogeneousIdeal.toIdeal.comap φ.toRingHom,
        localizedModuleMap φ f x.1.asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal hIJ (a x) = b.1 y) :
    (locallyModuleFraction 𝒜 𝒨).pred a := by
  intro x
  obtain ⟨y₀, hy₀⟩ := Stacks.ProjTwistComparison.exists_comapFun_eq φ h hg hφ (hW x)
  have hy₀W : ProjectiveSpectrum.comapFun φ hφ y₀ ∈ W := by rw [hy₀]; exact x.2
  obtain ⟨V, hy₀V, iV, k, m, s, hm, hs, hns, hfrac⟩ := b.2 ⟨y₀, hy₀W⟩
  obtain ⟨m', s', i, hm', hs', hmeq, hseq⟩ :=
    hmod.exists_common_pow_smul_eq_map h hg (pow_smul_mem_grading hg) hm hs
  have hle : Stacks.ProjTwistComparison.imageOpens φ h hg hφ V ≤ W := by
    intro p hp
    obtain ⟨z, hzV, hz⟩ := (Stacks.ProjTwistComparison.mem_imageOpens φ h hg hφ V).mp hp
    rw [← hz]
    exact (iV ⟨z, hzV⟩).2
  have hns' : ∀ p : Stacks.ProjTwistComparison.imageOpens φ h hg hφ V,
      s' ∉ p.1.asHomogeneousIdeal := by
    intro p
    obtain ⟨z, hzV, hz⟩ := (Stacks.ProjTwistComparison.mem_imageOpens φ h hg hφ V).mp p.2
    exact h.mem_primeCompl_of_map_eq p.1.asHomogeneousIdeal.toIdeal
      z.asHomogeneousIdeal.toIdeal (asHomogeneousIdeal_eq_comap_of_comapFun_eq φ hφ hz)
      (hns ⟨z, hzV⟩) hseq
  refine ⟨Stacks.ProjTwistComparison.imageOpens φ h hg hφ V,
    (Stacks.ProjTwistComparison.mem_imageOpens φ h hg hφ V).mpr ⟨y₀, hy₀V, hy₀⟩, homOfLE hle,
    k, m', s', hm', hs', hns', fun p => ?_⟩
  obtain ⟨z, hzV, hz⟩ := (Stacks.ProjTwistComparison.mem_imageOpens φ h hg hφ V).mp p.2
  have hIJ := asHomogeneousIdeal_eq_comap_of_comapFun_eq φ hφ hz
  refine injective_localizedModuleMap φ f p.1.asHomogeneousIdeal.toIdeal
    z.asHomogeneousIdeal.toIdeal h hmod hIJ ?_
  refine Eq.trans (ha (homOfLE hle p) ⟨z, (iV ⟨z, hzV⟩).2⟩ hz hIJ) ?_
  exact Eq.trans (hfrac ⟨z, hzV⟩)
    (localizedModuleMap_mk_eq φ f hIJ (hns' p) (hns ⟨z, hzV⟩) hmeq hseq).symm

/-! ### The comparison of fraction families is bijective -/

include hf in
/-- The comparison of homogeneous fraction families of a graded module is injective over an open
on which `g` does not vanish. -/
public theorem injective_sectionsMap (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Injective (sectionsMap φ hφ f hf W) := by
  intro a a' hyp
  refine Subtype.ext (funext ?_)
  refine (Stacks.ProjTwistComparison.surjective_comapRestrict φ h hg hφ W hW).forall.mpr
    fun y => ?_
  exact injective_localizedModuleMap φ f
    (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal h hmod rfl (congrFun (congrArg Subtype.val hyp) y)

include hf in
/-- The comparison of homogeneous fraction families of a graded module is surjective over an open
on which `g` does not vanish. -/
public theorem surjective_sectionsMap (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Surjective (sectionsMap φ hφ f hf W) := by
  intro b
  choose a ha using exists_fibre_localizedModuleMap_eq φ hφ f h hg hmod W hW b
  exact ⟨⟨a, locallyModuleFraction_of_localizedModuleMap_eq φ hφ f h hg hmod W hW b a ha⟩,
    Subtype.ext (funext fun y =>
      ha ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ y rfl rfl)⟩

include hf in
/-- **The sheaf attached to a degreewise localization is the degreewise localization of the
sheaf.** Over an open of `Proj 𝒜` on which `g` does not vanish, the comparison of homogeneous
fraction families of a graded module is a bijection. -/
public theorem bijective_sectionsMap (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hmod : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Bijective (sectionsMap φ hφ f hf W) :=
  ⟨injective_sectionsMap φ hφ f hf h hg hmod W hW,
    surjective_sectionsMap φ hφ f hf h hg hmod W hW⟩

end Stacks.ProjModuleComparison

end
