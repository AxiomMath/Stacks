module

public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Criterion
public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Lift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Surjectivity of the comparison maps on twists, Tag 01N0

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is surjective on
homogeneous components of all sufficiently large degree, let `U(ψ) ⊆ Proj ℬ` be its domain of
definition and `mapHom : U(ψ) ⟶ Proj 𝒜` the induced morphism. This file proves that the
comparison map `θ n : mapHom* 𝒪_{Proj 𝒜}(n) ⟶ ι* 𝒪_{Proj ℬ}(n)` of Tag 01MY is an epimorphism
of sheaves of modules for every `n : ℤ`. This is Tag 01N0's twist assertion.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistEpi.fractionSection`: the section of a twist cut out by one
  homogeneous fraction.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistEpi.epi_twistMap_of_eventually_surjective`: the assertion
  for `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective`: the
  same for the twist maps of Tag 01MY's bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.isLocallySurjective_twistPushforwardMap`: local
  surjectivity of the adjoint form of `θ`.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.exists_fractionSection_eq`: near every point of the image
  of `mapHom`, a section of a twist on `Proj ℬ` is the comparison of a section on `Proj 𝒜`.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Filter
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.ProjTwistEpi

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### A section of a twist cut out by a single fraction -/

/-- The section of the `n`-th twist of the structure sheaf of `Proj 𝒜` over an open on which the
denominator does not vanish, given by one homogeneous fraction `β / c` with `β` of twisted
degree `K` and `c` of degree `K`. -/
public def fractionSection (n : ℤ) {K : ℕ} {β c : A}
    (hβ : β ∈ twistGrading (S := A) 𝒜 n (K : ℤ)) (hc : c ∈ 𝒜 K)
    {V : Opens (ProjectiveSpectrum.top 𝒜)} (hV : ∀ w : V, c ∉ w.1.asHomogeneousIdeal) :
    (twistingSheaf 𝒜 n).val.obj (.op V) :=
  ⟨fun w => LocalizedModule.mk β ⟨c, hV w⟩,
    fun w => ⟨V, w.2, 𝟙 _, K, β, c, hβ, hc, hV, fun _ => rfl⟩⟩

/-- The value of `fractionSection` at a point is the fraction it was built from. -/
public theorem fractionSection_val (n : ℤ) {K : ℕ} {β c : A}
    (hβ : β ∈ twistGrading (S := A) 𝒜 n (K : ℤ)) (hc : c ∈ 𝒜 K)
    {V : Opens (ProjectiveSpectrum.top 𝒜)} (hV : ∀ w : V, c ∉ w.1.asHomogeneousIdeal)
    (w : V) :
    (fractionSection 𝒜 n hβ hc hV).1 w = LocalizedModule.mk β ⟨c, hV w⟩ := rfl

/-! ### The local lifting step -/

/-- **The local form of Tag 01N0's twist assertion.** Let `ψ` be surjective on homogeneous
components of all degrees `≥ N`, and let `t` be a section of the `n`-th twist on `Proj ℬ` over
the image of `mapHom ⁻¹ᵁ U`. Near the image of any point `y` of the domain of definition, `t` is
the comparison of a section of the `n`-th twist on `Proj 𝒜`. -/
public theorem exists_fractionSection_eq (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (hind : Topology.IsInducing (mapHom 𝒜 ℬ ψ).base) (n : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf ℬ n).val.obj
      (.op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))))
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) (hyU : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) :
    ∃ V : Opens (ProjectiveSpectrum.top 𝒜), V ≤ U ∧ (mapHom 𝒜 ℬ ψ).base y ∈ V ∧
      ∃ s : (twistingSheaf 𝒜 n).val.obj (.op V),
        ∀ (z : ↥((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V)))
          (hz : (z.1 : ProjectiveSpectrum ℬ) ∈
            (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)),
          twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
              (s.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) =
            t.1 ⟨(z.1 : ProjectiveSpectrum ℬ), hz⟩ := by
  obtain ⟨V₀, hz₀V₀, i₀, k, b, s₀, hb, hs₀, hns₀, heq⟩ :=
    t.2 ⟨(y.1 : ProjectiveSpectrum ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyU⟩
  obtain ⟨m, g, hm, hg, hgy⟩ := exists_homogeneous_pos_notMem ℬ (ambientPoint 𝒜 ℬ ψ y)
  have hs₀y : s₀ ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal :=
    hns₀ ⟨(y.1 : ProjectiveSpectrum ℬ), hz₀V₀⟩
  obtain ⟨j, K, β, c, hβ, hc, hβe, hce⟩ :=
    exists_lift_twistGrading 𝒜 ℬ ψ hN n hb hs₀ hm hg
  have hψc : ψ c ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal := by
    rw [hce]
    intro hmem
    rcases (ambientPoint 𝒜 ℬ ψ y).isPrime.mem_or_mem hmem with h | h
    · exact hs₀y h
    · exact hgy ((ambientPoint 𝒜 ℬ ψ y).isPrime.mem_of_pow_mem j h)
  have hcnm : c ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal :=
    (notMem_mapHom_base_iff 𝒜 ℬ ψ y hc).mpr hψc
  obtain ⟨W₀, hW₀⟩ := exists_preimage_opens_of_isInducing (mapHom 𝒜 ℬ ψ) hind
    ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V₀)
  have hyW₀ : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ W₀ := by rw [hW₀]; exact hz₀V₀
  have hnv : ∀ w : (W₀ ⊓ U ⊓ Proj.basicOpen 𝒜 c : Opens (ProjectiveSpectrum.top 𝒜)),
      c ∉ w.1.asHomogeneousIdeal := fun w => (Proj.mem_basicOpen 𝒜 c w.1).mp w.2.2
  refine ⟨W₀ ⊓ U ⊓ Proj.basicOpen 𝒜 c, inf_le_left.trans inf_le_right,
    ⟨⟨hyW₀, hyU⟩, (Proj.mem_basicOpen 𝒜 c _).mpr hcnm⟩,
    fractionSection 𝒜 n hβ hc hnv, fun z hz => ?_⟩
  have hzV₀ : (z.1 : ProjectiveSpectrum ℬ) ∈ V₀ := by
    obtain ⟨wz, hwz, hwe⟩ := z.2
    have hw : wz ∈ (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V₀ := by rw [← hW₀]; exact hwz.1.1
    exact hwe ▸ hw
  have hψcz : ψ c ∉ (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal :=
    notMem_of_notMem 𝒜 ℬ ψ hc (liftPt 𝒜 ℬ ψ z)
      (hnv ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)
  rw [fractionSection_val, twistFibreMap_mk 𝒜 ℬ ψ _ β c _ hψcz]
  refine Eq.trans ?_ (heq ⟨(z.1 : ProjectiveSpectrum ℬ), hzV₀⟩).symm
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul]
  change s₀ • ψ β = ψ c • b
  rw [hβe, hce, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Local surjectivity of the adjoint comparison map -/

/-- **The adjoint comparison map is locally surjective.** If `ψ` is surjective on homogeneous
components of all degrees `≥ N` and `mapHom` is inducing on spaces with closed image, then the
adjoint form `twistPushforwardMap 𝒜 ℬ ψ n` of the comparison map on `n`-th twists is locally
surjective. -/
public theorem isLocallySurjective_twistPushforwardMap (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (hind : Topology.IsInducing (mapHom 𝒜 ℬ ψ).base)
    (hrange : IsClosed (Set.range (mapHom 𝒜 ℬ ψ).base)) (n : ℤ) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
      ((PresheafOfModules.toPresheaf _).map (twistPushforwardMap 𝒜 ℬ ψ n).val) := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
  intro U t x hx
  by_cases hxim : x ∈ Set.range (mapHom 𝒜 ℬ ψ).base
  · obtain ⟨y, hy⟩ := hxim
    have hyU : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U := show (mapHom 𝒜 ℬ ψ).base y ∈ U from hy ▸ hx
    obtain ⟨V, hVU, hyV, s, hs⟩ := exists_fractionSection_eq 𝒜 ℬ ψ hN hind n U
      (show (twistingSheaf ℬ n).val.obj
        (.op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) from t) y hyU
    refine ⟨V, hVU, ⟨s, ?_⟩, hy ▸ hyV⟩
    exact Subtype.ext (funext fun z => hs z _)
  · refine ⟨U ⊓ ⟨(Set.range (mapHom 𝒜 ℬ ψ).base)ᶜ, hrange.isOpen_compl⟩, inf_le_left,
      ⟨0, ?_⟩, hx, hxim⟩
    refine Subtype.ext (funext fun z => ?_)
    obtain ⟨wz, hwz, -⟩ := z.2
    exact absurd ⟨wz, rfl⟩ hwz.2

/-! ### Tag 01N0: the comparison maps on twists are epimorphisms -/

/-- If `ψ` is surjective on homogeneous components of all sufficiently large degree, then the
comparison map `twistMap 𝒜 ℬ ψ n` on `n`-th twists is an epimorphism of sheaves of modules. -/
public theorem epi_twistMap_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (n : ℤ) : Epi (twistMap 𝒜 ℬ ψ n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hψ
  have hcl : IsClosedImmersion (mapHom 𝒜 ℬ ψ) :=
    Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective
      𝒜 ℬ ψ hψ
  have hemb := (mapHom 𝒜 ℬ ψ).isClosedEmbedding
  have hind : Topology.IsInducing (mapHom 𝒜 ℬ ψ).base := hemb.isInducing
  have hepi : Epi (twistPushforwardMap 𝒜 ℬ ψ n) :=
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (isLocallySurjective_twistPushforwardMap 𝒜 ℬ ψ hN hind hemb.isClosed_range n)
  have hfaith : (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).Faithful :=
    faithful_pushforward (mapHom 𝒜 ℬ ψ) (exists_preimage_opens_of_isInducing _ hind)
  have h1 : Epi (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
      (twistingSheaf 𝒜 n) _).symm (twistPushforwardMap 𝒜 ℬ ψ n)) :=
    epi_homEquiv_symm_of_epi _ _ hepi
  have hiso : IsIso ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n)) := NatIso.isIso_app_of_isIso _ _
  have h2 : Epi ((((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
        (twistingSheaf 𝒜 n) _).symm (twistPushforwardMap 𝒜 ℬ ψ n)) ≫
      (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n)) := epi_comp _ _
  exact h2

/-- If `ψ` is surjective on homogeneous components of all sufficiently large degree, then the
twist maps of the bundle `projMapData 𝒜 ℬ ψ` are epimorphisms of sheaves of modules. -/
@[stacks 01N0 "twist_surjective"]
public theorem epi_projMapData_twistMap_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    (n : ℤ) : Epi ((projMapData 𝒜 ℬ ψ).twistMap n) := by
  rw [projMapData_twistMap]
  exact epi_twistMap_of_eventually_surjective 𝒜 ℬ ψ hψ n

end Stacks.AlgebraicGeometry.ProjTwistEpi

end
