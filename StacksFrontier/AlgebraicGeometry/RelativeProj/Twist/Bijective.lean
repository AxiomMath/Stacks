module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Degreewise
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Fibre
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.ProjAway

/-!
# The twist comparison of a degreewise localization is bijective

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is, in each degree, the
localization away from a degree-zero element `g` of `𝒜`
(`Stacks.GradedLocalization.IsAwayDegreewise`), and suppose `ℬ₊ ≤ 𝒜₊.map φ`, so that
`AlgebraicGeometry.Proj.map φ` exists. Then the comparison of twisting sheaves
`Stacks.ProjTwistComparison.sectionsMap` is a bijection over every open of `Proj 𝒜` on which `g`
does not vanish; that is, the twist of a degreewise localization is the degreewise localization
of the twist.

On points, `φ` identifies `Proj ℬ` with the nonvanishing locus of `g`; on fibres, the local rings
at corresponding points agree, because `φ g` is invertible; and a homogeneous fraction over `ℬ`
is the image of a homogeneous fraction over `𝒜` of the same degrees once numerator and
denominator are multiplied by one common power of `φ g`.

## Main results

* `Stacks.ProjTwistComparison.injective_comapFun` and
  `Stacks.ProjTwistComparison.exists_comapFun_eq`: on points, the comparison is a bijection from
  `Proj ℬ` onto the nonvanishing locus of `g` in `Proj 𝒜`.
* `Stacks.ProjTwistComparison.injective_sectionsMap` and
  `Stacks.ProjTwistComparison.surjective_sectionsMap`, assembled into
  `Stacks.ProjTwistComparison.bijective_sectionsMap`: over an open on which `g` does not vanish,
  the comparison of degree-`n` fraction families is a bijection.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) {g : A}

/-! ### The comparison of points -/

/-- For a degreewise localization away from a degree-zero `g`, the comparison of points is an
open embedding. -/
private theorem isOpenEmbedding_comapFun (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) :
    Topology.IsOpenEmbedding (ProjectiveSpectrum.comapFun φ hφ) := by
  have hoi := Stacks.ProjAway.isOpenImmersion_map h hg hφ
  exact (AlgebraicGeometry.Proj.map φ hφ).isOpenEmbedding

/-- If `y` lies above `x`, then the prime of `x` is the preimage of the prime of `y`. -/
private theorem ideal_eq_comap_of_comapFun_eq (hφ : ℬ₊ ≤ 𝒜₊.map φ) {x : ProjectiveSpectrum 𝒜}
    {y : ProjectiveSpectrum ℬ} (hxy : ProjectiveSpectrum.comapFun φ hφ y = x) :
    x.asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap φ.toRingHom := by
  rw [← hxy]; rfl

/-- For a degreewise localization away from a degree-zero `g`, the comparison of points is
injective. -/
public theorem injective_comapFun (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) :
    Function.Injective (ProjectiveSpectrum.comapFun φ hφ) :=
  (isOpenEmbedding_comapFun φ h hg hφ).injective

/-- For a degreewise localization away from a degree-zero `g`, every point of `Proj 𝒜` at which
`g` does not vanish is the image of a point of `Proj ℬ`: the image of `AlgebraicGeometry.Proj.map`
is the standard open of `g`. -/
public theorem exists_comapFun_eq (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) {x : ProjectiveSpectrum 𝒜}
    (hx : g ∉ x.asHomogeneousIdeal) :
    ∃ y : ProjectiveSpectrum ℬ, ProjectiveSpectrum.comapFun φ hφ y = x := by
  have hoi := Stacks.ProjAway.isOpenImmersion_map h hg hφ
  have hmem : x ∈ (AlgebraicGeometry.Proj.map φ hφ).opensRange := by
    rw [Stacks.ProjAway.opensRange_map h hg hφ]
    exact (AlgebraicGeometry.Proj.mem_basicOpen 𝒜 g x).mpr hx
  exact hmem

/-- For a degreewise localization away from a degree-zero `g`, the comparison of points is an open
map. -/
public theorem isOpenMap_comapFun (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) :
    IsOpenMap (ProjectiveSpectrum.comapFun φ hφ) :=
  (isOpenEmbedding_comapFun φ h hg hφ).isOpenMap

/-- The image in `Proj 𝒜` of an open of `Proj ℬ` under the comparison of points, as an open. -/
public def imageOpens (h : Stacks.GradedLocalization.IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hφ : ℬ₊ ≤ 𝒜₊.map φ) (V : Opens (ProjectiveSpectrum.top ℬ)) :
    Opens (ProjectiveSpectrum.top 𝒜) :=
  ⟨ProjectiveSpectrum.comapFun φ hφ '' V.1, isOpenMap_comapFun φ h hg hφ V.1 V.2⟩

/-- A point lies in the image of an open exactly when some point of that open lies above it. -/
public theorem mem_imageOpens (h : Stacks.GradedLocalization.IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hφ : ℬ₊ ≤ 𝒜₊.map φ) (V : Opens (ProjectiveSpectrum.top ℬ))
    {x : ProjectiveSpectrum.top 𝒜} :
    x ∈ imageOpens φ h hg hφ V ↔ ∃ y ∈ V, ProjectiveSpectrum.comapFun φ hφ y = x :=
  Iff.rfl

/-- The comparison of points, viewed as a map from the preimage of an open of `Proj 𝒜` to that
open. -/
public def comapRestrict (hφ : ℬ₊ ≤ 𝒜₊.map φ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (y : W.comap (ProjectiveSpectrum.comap φ hφ)) : W :=
  ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩

/-- Over an open on which `g` does not vanish, the comparison of points is onto that open. -/
public theorem surjective_comapRestrict (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Surjective (comapRestrict φ hφ W) := by
  intro x
  obtain ⟨y, hy⟩ := exists_comapFun_eq φ h hg hφ (hW x)
  exact ⟨⟨y, show ProjectiveSpectrum.comapFun φ hφ y ∈ W from hy ▸ x.2⟩, Subtype.ext hy⟩

/-! ### Lifting a homogeneous fraction -/

omit [GradedRing ℬ] in
/-- A numerator in an integer-graded piece of `ℬ` and a denominator in a homogeneous piece of `ℬ`
are simultaneously images of a numerator and a denominator of the same degrees over `𝒜`, after
multiplication by one common power of `φ g`. For a negative degree the graded piece is `⊥`, so the
numerator is zero and is lifted to zero. -/
public theorem exists_lift_integerGrading (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) {j : ℤ} {k : ℕ} {m s : B} (hm : m ∈ integerGrading (S := B) ℬ j)
    (hs : s ∈ ℬ k) :
    ∃ (m' s' : A) (i : ℕ), m' ∈ integerGrading (S := A) 𝒜 j ∧ s' ∈ 𝒜 k ∧
      φ m' = φ g ^ i * m ∧ φ s' = φ g ^ i * s := by
  rcases le_or_gt 0 j with hj | hj
  · simp only [integerGrading, hj, reduceIte, mem_homogeneousSubmodule] at hm ⊢
    exact h.exists_common_pow_mul_eq_map hg hm hs
  · rw [integerGrading_neg (S := B) ℬ j hj, Submodule.mem_bot] at hm
    obtain ⟨i, s', hs', hseq⟩ := h.surj k s hs
    refine ⟨0, s', i, ?_, hs', ?_, hseq⟩
    · rw [integerGrading_neg (S := A) 𝒜 j hj]
      exact Submodule.zero_mem _
    · rw [map_zero, hm, mul_zero]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- **Clearing denominators.** A fraction over `𝒜` whose numerator and denominator become
`φ g ^ i` times `m` and `s` is carried by the comparison of local rings to the fraction `m / s`:
the two extra factors `φ g ^ i` cancel. -/
public theorem localRingHom_mk_eq {I : Ideal A} [I.IsPrime] {J : Ideal B} [J.IsPrime]
    (hIJ : I = J.comap φ.toRingHom) {m' s' : A} {m s : B} {i : ℕ}
    (hs' : s' ∈ I.primeCompl) (hs : s ∈ J.primeCompl)
    (hmeq : φ m' = φ g ^ i * m) (hseq : φ s' = φ g ^ i * s) :
    Localization.localRingHom I J φ.toRingHom hIJ (LocalizedModule.mk m' ⟨s', hs'⟩)
      = LocalizedModule.mk m ⟨s, hs⟩ := by
  refine Eq.trans (Localization.localRingHom_mk I J φ.toRingHom hIJ m' ⟨s', hs'⟩) ?_
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.mk_smul, smul_eq_mul, GradedRingHom.coe_toRingHom, hmeq, hseq]
  ring

/-! ### Inverting the comparison of fraction families -/

/-- **The pointwise preimage of a fraction family.** Over an open on which `g` does not vanish,
every point `x` carries a unique element of the module fibre whose image under the comparison of
local rings at *any* point of the preimage open above `x` is the given family `b`. -/
public theorem exists_fibre_localRingHom_eq
    (h : Stacks.GradedLocalization.IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal)
    (b : moduleSections ℬ (twistGrading (S := B) ℬ n)
      (W.comap (ProjectiveSpectrum.comap φ hφ)))
    (x : W) :
    ∃ z : ModuleFiber (M := A) 𝒜 x.1,
      ∀ (y : W.comap (ProjectiveSpectrum.comap φ hφ))
        (_ : ProjectiveSpectrum.comapFun φ hφ y.1 = x.1)
        (hIJ : x.1.asHomogeneousIdeal.toIdeal
          = y.1.asHomogeneousIdeal.toIdeal.comap φ.toRingHom),
        Localization.localRingHom x.1.asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal φ.toRingHom hIJ z = b.1 y := by
  obtain ⟨y₀, hy₀⟩ := exists_comapFun_eq φ h hg hφ (hW x)
  have hy₀W : ProjectiveSpectrum.comapFun φ hφ y₀ ∈ W := hy₀ ▸ x.2
  obtain ⟨z, hz⟩ := h.surjective_localRingHom x.1.asHomogeneousIdeal.toIdeal
    y₀.asHomogeneousIdeal.toIdeal (ideal_eq_comap_of_comapFun_eq φ hφ hy₀) (b.1 ⟨y₀, hy₀W⟩)
  refine ⟨z, fun y hxy hIJ => ?_⟩
  obtain rfl : y = ⟨y₀, hy₀W⟩ :=
    Subtype.ext (injective_comapFun φ h hg hφ (hxy.trans hy₀.symm))
  exact hz

/-- Over an open on which `g` does not vanish, a family of fibre elements carried by the
comparison of local rings to a degree-`n` fraction family `b` is itself a family of local
homogeneous fractions of degree `n`. -/
public theorem locallyModuleFraction_of_localRingHom_eq
    (h : Stacks.GradedLocalization.IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal)
    (b : moduleSections ℬ (twistGrading (S := B) ℬ n)
      (W.comap (ProjectiveSpectrum.comap φ hφ)))
    (a : ∀ x : W, ModuleFiber (M := A) 𝒜 x.1)
    (ha : ∀ (x : W) (y : W.comap (ProjectiveSpectrum.comap φ hφ)),
      ProjectiveSpectrum.comapFun φ hφ y.1 = x.1 →
      ∀ hIJ : x.1.asHomogeneousIdeal.toIdeal
          = y.1.asHomogeneousIdeal.toIdeal.comap φ.toRingHom,
        Localization.localRingHom x.1.asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal φ.toRingHom hIJ (a x) = b.1 y) :
    (locallyModuleFraction 𝒜 (twistGrading (S := A) 𝒜 n)).pred a := by
  intro x
  obtain ⟨y₀, hy₀⟩ := exists_comapFun_eq φ h hg hφ (hW x)
  have hy₀W : ProjectiveSpectrum.comapFun φ hφ y₀ ∈ W := hy₀ ▸ x.2
  obtain ⟨V, hy₀V, iV, k, m, s, hm, hs, hns, hfrac⟩ := b.2 ⟨y₀, hy₀W⟩
  obtain ⟨m', s', i, hm', hs', hmeq, hseq⟩ := exists_lift_integerGrading φ h hg hm hs
  have hle : imageOpens φ h hg hφ V ≤ W := by
    intro p hp
    obtain ⟨z, hzV, hz⟩ := (mem_imageOpens φ h hg hφ V).mp hp
    rw [← hz]
    exact (iV ⟨z, hzV⟩).2
  have hns' : ∀ p : imageOpens φ h hg hφ V, s' ∉ p.1.asHomogeneousIdeal := by
    intro p
    obtain ⟨z, hzV, hz⟩ := (mem_imageOpens φ h hg hφ V).mp p.2
    exact h.mem_primeCompl_of_map_eq p.1.asHomogeneousIdeal.toIdeal
      z.asHomogeneousIdeal.toIdeal (ideal_eq_comap_of_comapFun_eq φ hφ hz) (hns ⟨z, hzV⟩) hseq
  refine ⟨imageOpens φ h hg hφ V,
    (mem_imageOpens φ h hg hφ V).mpr ⟨y₀, hy₀V, hy₀⟩, homOfLE hle,
    k, m', s', hm', hs', hns', fun p => ?_⟩
  obtain ⟨z, hzV, hz⟩ := (mem_imageOpens φ h hg hφ V).mp p.2
  have hIJ := ideal_eq_comap_of_comapFun_eq φ hφ hz
  refine h.injective_localRingHom p.1.asHomogeneousIdeal.toIdeal
    z.asHomogeneousIdeal.toIdeal hIJ ?_
  refine Eq.trans (ha (homOfLE hle p) ⟨z, (iV ⟨z, hzV⟩).2⟩ hz hIJ) ?_
  exact Eq.trans (hfrac ⟨z, hzV⟩)
    (localRingHom_mk_eq φ hIJ (hns' p) (hns ⟨z, hzV⟩) hmeq hseq).symm

/-! ### The comparison of fraction families is bijective -/

/-- The comparison of degree-`n` fraction families is injective over an open on which `g` does not
vanish. -/
public theorem injective_sectionsMap (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Injective (sectionsMap φ hφ n W) := by
  intro a a' hyp
  refine Subtype.ext (funext ?_)
  refine (surjective_comapRestrict φ h hg hφ W hW).forall.mpr fun y => ?_
  exact h.injective_localRingHom
    (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal rfl (congrFun (congrArg Subtype.val hyp) y)

/-- The comparison of degree-`n` fraction families is surjective over an open on which `g` does
not vanish. -/
public theorem surjective_sectionsMap (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Surjective (sectionsMap φ hφ n W) := by
  intro b
  choose a ha using exists_fibre_localRingHom_eq φ h hg hφ n W hW b
  exact ⟨⟨a, locallyModuleFraction_of_localRingHom_eq φ h hg hφ n W hW b a ha⟩,
    Subtype.ext (funext fun y =>
      ha ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩ y rfl rfl)⟩

/-- **The twist of a degreewise localization is the degreewise localization of the twist.** Over
an open of `Proj 𝒜` on which `g` does not vanish, the comparison of degree-`n` fraction families
is a bijection. -/
public theorem bijective_sectionsMap (h : Stacks.GradedLocalization.IsAwayDegreewise φ g)
    (hg : g ∈ 𝒜 0) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ) (W : Opens (ProjectiveSpectrum.top 𝒜))
    (hW : ∀ x : W, g ∉ x.1.asHomogeneousIdeal) :
    Function.Bijective (sectionsMap φ hφ n W) :=
  ⟨injective_sectionsMap φ h hg hφ n W hW, surjective_sectionsMap φ h hg hφ n W hW⟩

end Stacks.ProjTwistComparison

end
