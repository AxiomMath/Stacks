module

public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.Iso
public import StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic

/-!
# The comparison maps on the twists for an arbitrary inclusion of affine opens

Let `𝒜` be a quasi-coherent graded algebra over a scheme `S` and let `U ⊆ V` be an arbitrary
inclusion of affine opens of `S`, not necessarily a basic open inclusion. This file proves that
the comparison map `θ n` on the `n`-th twisting sheaf of the morphism of projective spectra
induced by restriction is an isomorphism, for every `n : ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_res_of_le_opens`: the comparison map
  on the `n`-th twist of an arbitrary inclusion of affine opens is an isomorphism, and
  `isIso_projMapData_twistMap_res_of_le_opens` the same for
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.injective_twistFibreMap_res` and
  `fractionLift_res`: the fibre comparison is injective and homogeneous fractions lift, at every
  point.
* `Stacks.AlgebraicGeometry.TwistBaseChange.exists_comap_eq_of_isLocalizationAway`: a point of
  `Proj 𝒜` at which an inverted element does not vanish lies under a point of the `Proj` of the
  localization.
* `Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` and
  `injective_fibreMap_of_injective_comp`: the fibre comparison of a composite of graded maps is
  the composite of the fibre comparisons, so a factor of an injective one is injective.
* `Stacks.AlgebraicGeometry.TwistBaseChange.exists_str_notMem`: at every point of the chart of
  `U` there is a section over `V` whose basic open lies inside `U` and whose degree-zero image
  does not vanish at the point.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isOpenImmersion_mapHom_of_mapHomOfTop`: the glued
  morphism is an open immersion when the everywhere-defined one is.

## Implementation notes

`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_inputs` reduces invertibility to
three inputs: the induced morphism is an open immersion, the fibre comparison is injective, and
homogeneous fractions lift. The last two are proved at a point `q` of `Proj Γ(U, 𝒜)` by choosing
a section `f` over `V` whose basic open `W` lies inside `U` and whose degree-zero image does not
vanish at `q`. Then `W` is a basic open of both `V` and `U`, so `Γ(W, 𝒜)` is a localization of
both `Γ(V, 𝒜)` and `Γ(U, 𝒜)`, and both inputs reduce to the known case of the basic open
inclusion `W ⊆ V`.

The affine open `W` is a universally quantified site object with its two presentations as
equational hypotheses, rather than a local definition, because `(U.basicOpen g).toOpens` and
`S.basicOpen g` are equal by `rfl` but not at `implicit` transparency; this is why the two inputs
each come in a parametrized and an instantiated form.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGeneral

namespace Stacks.AlgebraicGeometry.TwistBaseChange

universe u w w' w''

/-! ### The open immersion -/

section OpenImmersion

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- If the everywhere-defined morphism `Proj ℬ ⟶ Proj 𝒜` is an open immersion, so is the glued
morphism on the domain of definition. -/
public theorem isOpenImmersion_mapHom_of_mapHomOfTop (ψ : 𝒜 →+*ᵍ ℬ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (htop : IsOpenImmersion (mapHomOfTop 𝒜 ℬ ψ hdom)) :
    IsOpenImmersion (mapHom 𝒜 ℬ ψ) := by
  rw [mapHomOfTop] at htop
  have h1 : IsOpenImmersion
      (((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom ≫ mapHom 𝒜 ℬ ψ) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
      (Scheme.topIso (AlgebraicGeometry.Proj ℬ)).inv _).mp htop
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
    ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom _).mp h1

end OpenImmersion

/-! ### The point of the chart of a basic open -/

section ChartPoint

variable {A C : Type u} {σ : Type w} {ω : Type w''}
  [CommRing A] [CommRing C] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike ω C] [AddSubgroupClass ω C]
  (𝒜 : ℕ → σ) (𝒞 : ℕ → ω) [GradedRing 𝒜] [GradedRing 𝒞]

/-- If `φ : 𝒜 →+*ᵍ 𝒞` exhibits `C` as a localization of `A` away from an element `t`, then every
point of `Proj 𝒜` at which `t` does not vanish lies under a point of `Proj 𝒞`. -/
public theorem exists_comap_eq_of_isLocalizationAway (φ : 𝒜 →+*ᵍ 𝒞) (t : A) [Algebra A C]
    (halg : (algebraMap A C : A →+* C) = φ.toRingHom) [IsLocalization.Away t C]
    (q : ProjectiveSpectrum 𝒜) (ht : t ∉ q.asHomogeneousIdeal) :
    ∃ r : ProjectiveSpectrum 𝒞, q.asHomogeneousIdeal = r.asHomogeneousIdeal.comap φ := by
  have hd : Disjoint (Submonoid.powers t : Set A) (q.asHomogeneousIdeal.toIdeal : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨k, rfl⟩ ha
    exact ht (q.isPrime.mem_of_pow_mem k ha)
  have hmapeq : ∀ I : Ideal A, Ideal.map (algebraMap A C) I = Ideal.map φ I := fun I => by
    rw [halg]
    rfl
  have hcomapeq : ∀ J : Ideal C, Ideal.comap (algebraMap A C) J = Ideal.comap φ J := fun J => by
    rw [halg]
    rfl
  have hprime : (q.asHomogeneousIdeal.map φ).toIdeal.IsPrime := by
    rw [HomogeneousIdeal.toIdeal_map, ← hmapeq]
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) C _ q.isPrime hd
  have hcm : (q.asHomogeneousIdeal.map φ).comap φ = q.asHomogeneousIdeal := by
    refine HomogeneousIdeal.ext ?_
    rw [HomogeneousIdeal.toIdeal_comap, HomogeneousIdeal.toIdeal_map, ← hmapeq, ← hcomapeq]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) C q.isPrime hd
  have hnirr : ¬ HomogeneousIdeal.irrelevant 𝒞 ≤ q.asHomogeneousIdeal.map φ := by
    intro hle
    refine q.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr fun i hi x hx => ?_)
    have h1 : x ∈ (q.asHomogeneousIdeal.map φ).comap φ :=
      hle (HomogeneousIdeal.mem_irrelevant_of_mem 𝒞 hi (φ.map_mem hx))
    rwa [hcm] at h1
  exact ⟨⟨q.asHomogeneousIdeal.map φ, hprime, hnirr⟩, hcm.symm⟩

end ChartPoint

/-! ### Injectivity of a factor of the fibre comparison -/

section Factor

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {ω : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ω C] [AddSubgroupClass ω C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → ω) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- The fibre comparison of a composite of graded ring homomorphisms is the composite of the two
fibre comparisons. -/
public theorem fibreMap_comp (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) (x : ProjectiveSpectrum 𝒜)
    (y : ProjectiveSpectrum ℬ) (z : ProjectiveSpectrum 𝒞)
    (hxy : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap φ)
    (hyz : y.asHomogeneousIdeal = z.asHomogeneousIdeal.comap χ)
    (hxz : x.asHomogeneousIdeal = z.asHomogeneousIdeal.comap (χ.comp φ)) :
    fibreMap 𝒜 𝒞 (χ.comp φ) x z hxz =
      (fibreMap ℬ 𝒞 χ y z hyz).comp (fibreMap 𝒜 ℬ φ x y hxy) :=
  Localization.localRingHom_comp x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
    z.asHomogeneousIdeal.toIdeal (φ : A →+* B) (congrArg HomogeneousIdeal.toIdeal hxy)
    (χ : B →+* C) (congrArg HomogeneousIdeal.toIdeal hyz)

/-- If the fibre comparison of a composite `χ.comp φ` is injective, so is that of `φ`. -/
public theorem injective_fibreMap_of_injective_comp (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞)
    (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ) (z : ProjectiveSpectrum 𝒞)
    (hxy : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap φ)
    (hyz : y.asHomogeneousIdeal = z.asHomogeneousIdeal.comap χ)
    (hxz : x.asHomogeneousIdeal = z.asHomogeneousIdeal.comap (χ.comp φ))
    (hinj : Function.Injective (fibreMap 𝒜 𝒞 (χ.comp φ) x z hxz)) :
    Function.Injective (fibreMap 𝒜 ℬ φ x y hxy) := by
  rw [fibreMap_comp 𝒜 ℬ 𝒞 φ χ x y z hxy hyz hxz, RingHom.coe_comp] at hinj
  exact hinj.of_comp

end Factor

/-! ### The two inputs for an arbitrary inclusion of affine opens -/

section Relative

variable {S : Scheme.{u}} (𝒜 : RelativeProj.GradedAlgebra S)

/-- At any point of the chart of the smaller open there is a section of the bigger open whose
basic open lies inside the smaller one and whose degree-zero image does not vanish at that
point. -/
public theorem exists_str_notMem {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (q : ProjectiveSpectrum (𝒜.grading U)) :
    ∃ f : Γ(S, V.toOpens), S.basicOpen f ≤ U.toOpens ∧
      𝒜.str U (S.presheaf.map (homOfLE h).op f) ∉ q.asHomogeneousIdeal := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : Ideal.span {x : Γ(S, U.toOpens) | ∃ f : Γ(S, V.toOpens),
        S.basicOpen f ≤ U.toOpens ∧ S.presheaf.map (homOfLE h).op f = x} ≤
      Ideal.comap (𝒜.str U).hom q.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro x ⟨f, hfU, rfl⟩
    exact hcon f hfU
  rw [span_res_sections_eq_top (S := S) h] at hle
  have h1 : (1 : Γ(S, U.toOpens)) ∈
      Ideal.comap (𝒜.str U).hom q.asHomogeneousIdeal.toIdeal := hle Submodule.mem_top
  rw [Ideal.mem_comap, map_one] at h1
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The fibre comparison of an inclusion `U ⊆ V` of affine opens is injective at a point, given
an affine open `W` presented both as a basic open of `V` and as the basic open of a section `g` of
`U` whose degree-zero image does not vanish at the point. -/
public theorem injective_twistFibreMap_of_eq {U V W : S.AffineZariskiSite}
    (h : U.toOpens ≤ V.toOpens) (hWU : W.toOpens ≤ U.toOpens) (f : Γ(S, V.toOpens))
    (g : Γ(S, U.toOpens)) (hWf : W = V.basicOpen f) (hWg : W = U.basicOpen g)
    (y : (mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h)).toScheme)
    (hgy : 𝒜.str U g ∉
      (ambientPoint (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y).asHomogeneousIdeal) :
    Function.Injective (twistFibreMap (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y) := by
  let := 𝒜.algebra hWU
  let := 𝒜.algebra (hWU.trans h)
  have hlocU : IsLocalization.Away (𝒜.str U g) (𝒜.ring W) := isLocalization_res_of_eq 𝒜 g hWg hWU
  have hlocV : IsLocalization.Away (𝒜.str V f) (𝒜.ring W) :=
    isLocalization_res_of_eq 𝒜 f hWf (hWU.trans h)
  obtain ⟨r, hr⟩ := exists_comap_eq_of_isLocalizationAway (𝒜.grading U) (𝒜.grading W)
    (𝒜.res hWU) (𝒜.str U g) (𝒜.algebraMap_eq hWU) _ hgy
  have hxy := basePoint_asHomogeneousIdeal (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y
  have hxz : (basePoint (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y).asHomogeneousIdeal =
      r.asHomogeneousIdeal.comap ((𝒜.res hWU).comp (𝒜.res h)) := by
    rw [hxy, hr, HomogeneousIdeal.comap_comap]
  have halgc : (algebraMap (𝒜.ring V) (𝒜.ring W) : 𝒜.ring V →+* 𝒜.ring W) =
      ((𝒜.res hWU).comp (𝒜.res h)).toRingHom := by
    rw [← 𝒜.res_comp hWU h]
    exact 𝒜.algebraMap_eq (hWU.trans h)
  exact injective_fibreMap_of_injective_comp (𝒜.grading V) (𝒜.grading U) (𝒜.grading W)
    (𝒜.res h) (𝒜.res hWU) _ _ r hxy hr hxz
    (bijective_fibreMap (𝒜.grading V) (𝒜.grading W) ((𝒜.res hWU).comp (𝒜.res h)) _ r hxz
      (𝒜.str V f) halgc).1

/-- The fibre comparison of an arbitrary inclusion of affine opens is injective at every
point. -/
public theorem injective_twistFibreMap_res {U V : S.AffineZariskiSite}
    (h : U.toOpens ≤ V.toOpens)
    (y : (mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h)).toScheme) :
    Function.Injective (twistFibreMap (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y) := by
  obtain ⟨f, hfU, hfy⟩ := exists_str_notMem 𝒜 h
    (ambientPoint (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y)
  exact injective_twistFibreMap_of_eq 𝒜 h
    (W := U.basicOpen (S.presheaf.map (homOfLE h).op f)) (S.basicOpen_le _) f _
    (Subtype.ext (basicOpen_res_of_le h f hfU)) rfl y hfy

/-- Homogeneous fractions lift along an inclusion `U ⊆ V` of affine opens at a point `q`, given an
affine open `W` presented as the basic open of a section `f` of `V` and of a section `g` of `U`
with the same degree-zero image as `f`, not vanishing at `q`: a fraction `b / s` of `Γ(U, 𝒜)`,
with `b` of twisted degree `K` in the `m`-th twist and `s` of degree `K` not in `q`, is the image
of a fraction `β / c` of `Γ(V, 𝒜)` of the same degrees with `c` not vanishing at `q`. -/
public theorem exists_fraction_lift_of_eq {U V W : S.AffineZariskiSite}
    (h : U.toOpens ≤ V.toOpens) (hWU : W.toOpens ≤ U.toOpens) (f : Γ(S, V.toOpens))
    (g : Γ(S, U.toOpens)) (hWf : W = V.basicOpen f) (hWg : W = U.basicOpen g)
    (hg : 𝒜.str U g = 𝒜.res h (𝒜.str V f)) (q : ProjectiveSpectrum (𝒜.grading U))
    (hgq : 𝒜.str U g ∉ q.asHomogeneousIdeal) (m : ℤ) (K : ℕ) {b s : 𝒜.ring U}
    (hb : b ∈ twistGrading (S := 𝒜.ring U) (𝒜.grading U) m (K : ℤ))
    (hs : s ∈ 𝒜.grading U K) (hsq : s ∉ q.asHomogeneousIdeal) :
    ∃ β c : 𝒜.ring V, β ∈ twistGrading (S := 𝒜.ring V) (𝒜.grading V) m (K : ℤ) ∧
      c ∈ 𝒜.grading V K ∧ 𝒜.res h c ∉ q.asHomogeneousIdeal ∧
      s * 𝒜.res h β = 𝒜.res h c * b := by
  let := 𝒜.algebra hWU
  let := 𝒜.algebra (hWU.trans h)
  have hlocU : IsLocalization.Away (𝒜.str U g) (𝒜.ring W) := isLocalization_res_of_eq 𝒜 g hWg hWU
  have hlocV : IsLocalization.Away (𝒜.str V f) (𝒜.ring W) :=
    isLocalization_res_of_eq 𝒜 f hWf (hWU.trans h)
  have hcomp : ∀ x : 𝒜.ring V, 𝒜.res (hWU.trans h) x = 𝒜.res hWU (𝒜.res h x) := fun x => by
    rw [𝒜.res_comp hWU h]; rfl
  have hcancel : ∀ x z : 𝒜.ring U, 𝒜.res hWU x = 𝒜.res hWU z →
      ∃ N : ℕ, 𝒜.str U g ^ N * x = 𝒜.str U g ^ N * z := by
    intro x z hxz
    have key : algebraMap (𝒜.ring U) (𝒜.ring W) x = algebraMap (𝒜.ring U) (𝒜.ring W) z := by
      rw [𝒜.algebraMap_eq hWU]
      exact hxz
    obtain ⟨⟨u, N, rfl⟩, hu⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (𝒜.str U g)) key
    exact ⟨N, hu⟩
  obtain ⟨β, c, p, hβ, hc, hce, hfrac⟩ := exists_fraction_lift (𝒜.grading V) (𝒜.grading W)
    (𝒜.res (hWU.trans h)) (𝒜.str_mem V f) (𝒜.algebraMap_eq (hWU.trans h)) m K
    (map_mem_twistGrading (𝒜.grading U) (𝒜.grading W) (𝒜.res hWU) m (K : ℤ) hb)
    ((𝒜.res hWU).map_mem hs)
  have hstr : 𝒜.res (hWU.trans h) (𝒜.str V f) = 𝒜.res hWU (𝒜.str U g) := by
    rw [hcomp, ← hg]
  have hpowmem : ∀ N : ℕ, 𝒜.str V f ^ N ∈ 𝒜.grading V 0 := fun N => by
    simpa using SetLike.pow_mem_graded N (𝒜.str_mem V f)
  have hnm : ∀ n : ℕ, 𝒜.str U g ^ n ∉ q.asHomogeneousIdeal := fun n hn =>
    hgq (q.isPrime.mem_of_pow_mem n hn)
  have hmul : ∀ {a b : 𝒜.ring U}, a ∉ q.asHomogeneousIdeal → b ∉ q.asHomogeneousIdeal →
      a * b ∉ q.asHomogeneousIdeal := fun ha hb hab => (q.isPrime.mem_or_mem hab).elim ha hb
  have hcq : 𝒜.res h c ∉ q.asHomogeneousIdeal := by
    have he : 𝒜.res hWU (𝒜.res h c) = 𝒜.res hWU (s * 𝒜.str U g ^ p) := by
      rw [map_mul, map_pow, ← hcomp, hce, hstr]
      rfl
    obtain ⟨M, hM⟩ := hcancel _ _ he
    intro hcmem
    refine hmul (hnm M) (hmul hsq (hnm p)) ?_
    rw [← hM]
    exact Ideal.mul_mem_left _ _ hcmem
  have he2 : 𝒜.res hWU (s * 𝒜.res h β) = 𝒜.res hWU (𝒜.res h c * b) := by
    rw [map_mul, map_mul, ← hcomp, ← hcomp]
    exact hfrac
  obtain ⟨N, hN⟩ := hcancel _ _ he2
  refine ⟨𝒜.str V f ^ N * β, 𝒜.str V f ^ N * c,
    mul_mem_twistGrading (𝒜.grading V) (hpowmem N) hβ, ?_, ?_, ?_⟩
  · have hmem := SetLike.mul_mem_graded (hpowmem N) hc
    rwa [zero_add] at hmem
  · rw [map_mul, map_pow, ← hg]
    exact hmul (hnm N) hcq
  · rw [map_mul, map_mul, map_pow, ← hg]
    linear_combination hN

/-- Homogeneous fractions lift pointwise for an arbitrary inclusion of affine opens. -/
public theorem fractionLift_res {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    FractionLift (𝒜.grading V) (𝒜.grading U) (𝒜.res h) := by
  intro y m K b s hb hs hsy
  obtain ⟨f, hfU, hfy⟩ := exists_str_notMem 𝒜 h
    (ambientPoint (𝒜.grading V) (𝒜.grading U) (𝒜.res h) y)
  exact exists_fraction_lift_of_eq 𝒜 h
    (W := U.basicOpen (S.presheaf.map (homOfLE h).op f)) (S.basicOpen_le _) f _
    (Subtype.ext (basicOpen_res_of_le h f hfU)) rfl (𝒜.res_str h f).symm _ hfy m K hb hs hsy

/-! ### The isomorphism -/

/-- For affine opens `U ⊆ V` of the base, the comparison maps on all the twisting sheaves of the
restriction map of a quasi-coherent graded algebra are isomorphisms, for every `n : ℤ`. -/
public theorem isIso_twistMap_res_of_le_opens {U V : S.AffineZariskiSite}
    (h : U.toOpens ≤ V.toOpens) (n : ℤ) :
    IsIso (twistMap (𝒜.grading V) (𝒜.grading U) (𝒜.res h) n) :=
  have : IsOpenImmersion (mapHom (𝒜.grading V) (𝒜.grading U) (𝒜.res h)) :=
    isOpenImmersion_mapHom_of_mapHomOfTop (𝒜.grading V) (𝒜.grading U) (𝒜.res h)
      (mapDomain_res_eq_top_of_le_opens 𝒜 h)
      (isOpenImmersion_transition_of_le_opens 𝒜 h (mapDomain_res_eq_top_of_le_opens 𝒜 h))
  isIso_twistMap_of_inputs (𝒜.grading V) (𝒜.grading U) (𝒜.res h)
    (injective_twistFibreMap_res 𝒜 h) (fractionLift_res 𝒜 h) n

/-- For affine opens `U ⊆ V` of the base, the comparison map on the `n`-th twist of
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` of the restriction map is an
isomorphism. -/
public theorem isIso_projMapData_twistMap_res_of_le_opens {U V : S.AffineZariskiSite}
    (h : U.toOpens ≤ V.toOpens) (n : ℤ) :
    IsIso ((projMapData (𝒜.grading V) (𝒜.grading U) (𝒜.res h)).twistMap n) := by
  rw [projMapData_twistMap]
  exact isIso_twistMap_res_of_le_opens 𝒜 h n

end Relative

end Stacks.AlgebraicGeometry.TwistBaseChange

end
