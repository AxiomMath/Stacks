module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.AffineReduction
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact opens of a one-dimensional affine scheme are affine

[Stacks, Tag 09N9] says that a quasi-compact open `U` of an affine scheme `X` all of whose local
rings are Noetherian of dimension at most one is affine. It is proved here as
`AlgebraicGeometry.isAffineOpen_of_isCompact_of_krullDimLE_one`, and used to discharge the one
remaining hypothesis of [Stacks, Tag 09N8], so that, in the namespace
`Stacks.AlgebraicGeometry.OneDimensionalLocal`,
`Stacks.RetrocompactOneDimensional.isZero_rightDerived_pushforward_of_isRetrocompact`
states that tag unconditionally.

## The proof is not the source's

The source derives Tag 09N9 *from* Tag 09N8: the higher direct images `Rᵖ j_* ℱ` vanish, so
`Hᵖ(U, ℱ) = Hᵖ(X, j_* ℱ) = 0` for `p > 0`, and then Serre's criterion
([Stacks, Tag 01XF]) makes `U` affine. That route cannot be used here, because Tag 09N8 is what
we are trying to prove: its residual hypothesis is precisely the vanishing of `Hᵖ(U, ℱ)`.

The argument below is independent of all of that, and uses no cohomology whatever. Write
`U = ⋃ X_{gᵢ}` as a union of basic opens of `X` that are themselves affine — possible because `U`
is quasi-compact and the basic opens form a basis. By [Stacks, Tag 01QF]
(`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`) it is enough that such `gᵢ` *span*
`Γ(X, U)`. Suppose they do not; then they lie in a maximal ideal `𝔫` of `Γ(X, U)`, whose
contraction to `Γ(X, ⊤)` is a prime `Q`. At a point `x` of `X` realizing `Q`, the morphism
`Spec 𝒪_{X,x} ⟶ X` is flat (`AlgebraicGeometry.flat_fromSpecStalk`), so degree-zero flat base
change for sections over a quasi-compact quasi-separated open
(`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, Mathlib's form of
[Stacks, Tag 02KH] part (2) in degree zero) exhibits `Γ(Spec 𝒪_{X,x}, φ⁻¹ U)` as the localization
of `Γ(X, U)` at `Q`. Over the local ring the open `φ⁻¹ U` is affine — this is
`AlgebraicGeometry.isAffineOpen_of_krullDimLE_one`, where the one-dimensionality is used, and the
only place it is used — so there the pulled-back `gᵢ` span the unit ideal, because on an affine
scheme basic opens that cover generate everything. But `𝔫` is disjoint from the image of the
complement of `Q`, so its image in that localization is again prime, hence proper: a contradiction.

So the dependence is on the *local* case of affineness plus degree-zero base change, and not on
the Čech complex of the covering, on flat base change in positive degrees
([Stacks, Tag 02KH] part (1)), or on Serre's criterion.

## Main results

* `AlgebraicGeometry.isAffineOpen_of_isCompact_of_krullDimLE_one`: [Stacks, Tag 09N9].
* `Stacks.AlgebraicGeometry.OneDimensionalLocal.cohomologyVanishingQuasiCompactOpenInAffine`: the
  residual hypothesis of `AffineReduction`, discharged — a quasi-compact open of such an affine
  scheme being affine, its positive cohomology vanishes by [Stacks, Tag 01XB].
* `Stacks.AlgebraicGeometry.OneDimensionalLocal`'s
  `Stacks.RetrocompactOneDimensional.isZero_rightDerived_pushforward_of_isRetrocompact`:
  [Stacks, Tag 09N8], with
  no hypotheses beyond the tag's own.

## References

* [Stacks Project, Tag 09N9](https://stacks.math.columbia.edu/tag/09N9)
* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
* [Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace AlgebraicGeometry

/-! ### Points of an affine scheme realize the primes of its global functions -/

/-- **Every prime of `Γ(X, U)`, for `U` an affine open, is the prime of a point of `U`.** The
inverse of `AlgebraicGeometry.IsAffineOpen.isoSpec`, read on points: `IsAffineOpen.primeIdealOf`
is that isomorphism on points, so it is surjective. -/
theorem exists_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = P := by
  have h : ∀ y : (Spec Γ(X, U) : Scheme.{u}), hU.isoSpec.hom (hU.isoSpec.inv y) = y := by
    intro y
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  exact ⟨hU.isoSpec.inv.base P, h P⟩

/-! ### Global sections along the morphism from the spectrum of a local ring -/

/-- **On global sections, `Spec 𝒪_{X,x} ⟶ X` is the germ map read through `Γ(Spec -, ⊤) ≅ -`.**
This is `AlgebraicGeometry.Scheme.fromSpecStalk_app` at `⊤`, with the two restrictions to `⊤`
that appear there and in `Scheme.Hom.appLE` cancelled. -/
theorem germ_comp_ΓSpecIso_inv_eq_appLE {X : Scheme.{u}} (x : X)
    (h : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ (X.fromSpecStalk x) ⁻¹ᵁ (⊤ : X.Opens)) :
    (X.presheaf.germ ⊤ x trivial) ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv
      = Scheme.Hom.appLE (X.fromSpecStalk x) ⊤ ⊤ h := by
  simp only [Scheme.Hom.appLE]
  rw [Scheme.fromSpecStalk_app (x := x) (U := ⊤) trivial]
  simp only [Category.assoc]
  congr 1

/-- **A prime of `Γ(X, ⊤)` on an affine scheme is reached by a flat morphism from the spectrum of
a local ring, which on global sections is the localization at that prime.** The morphism is
`X.fromSpecStalk x` at a point `x` realizing the prime; flatness is
`AlgebraicGeometry.flat_fromSpecStalk` and the localization is
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`, transported along `Γ(Spec -, ⊤) ≅ -`.

The hypothesis `hloc` — that every open of the spectrum of every local ring of `X` is affine — is
carried along rather than used, so that the caller may use it on the scheme produced. -/
theorem exists_flat_isLocalization_of_prime {X : Scheme.{u}} [IsAffine X]
    (hloc : ∀ x : X, ∀ W : (Spec (X.presheaf.stalk x)).Opens, IsAffineOpen W)
    (Q : PrimeSpectrum Γ(X, ⊤)) :
    ∃ (O : CommRingCat.{u}) (φ : Spec O ⟶ X), AlgebraicGeometry.Flat φ ∧
      (∀ W : (Spec O).Opens, IsAffineOpen W) ∧
      (letI := (φ.appLE ⊤ ⊤ (le_preimage_top φ ⊤)).hom.toAlgebra
       IsLocalization Q.asIdeal.primeCompl Γ(Spec O, ⊤)) := by
  obtain ⟨x, hx⟩ := exists_primeIdealOf_eq (isAffineOpen_top X) Q
  refine ⟨X.presheaf.stalk x.1, X.fromSpecStalk x.1, flat_fromSpecStalk X x.1, hloc x.1, ?_⟩
  let algST : Algebra Γ(X, ⊤) Γ(Spec (X.presheaf.stalk x.1), ⊤) :=
    ((X.fromSpecStalk x.1).appLE ⊤ ⊤ (le_preimage_top (X.fromSpecStalk x.1) ⊤)).hom.toAlgebra
  let algRO : Algebra Γ(X, ⊤) (X.presheaf.stalk x.1) := (X.presheaf.germ ⊤ x.1 x.2).hom.toAlgebra
  have hlocO : IsLocalization Q.asIdeal.primeCompl (X.presheaf.stalk x.1) :=
    hx ▸ (isAffineOpen_top X).isLocalization_stalk x
  refine IsLocalization.isLocalization_of_algEquiv Q.asIdeal.primeCompl
    (AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso (X.presheaf.stalk x.1)).symm.commRingCatIsoToRingEquiv) ?_)
  intro r
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    ← germ_comp_ΓSpecIso_inv_eq_appLE x.1 (le_preimage_top _ ⊤)]
  rfl

/-! ### Affineness of a quasi-compact open -/

/-- **The affine basic opens of an open of an affine scheme cover it.** The basic opens of `X`
contained in `V` cover `V` because they form a basis
(`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`), and each of them is affine and is the
basic open of the restriction to `V` of the function cutting it out. -/
theorem iSup_basicOpen_isAffineOpen_eq {X : Scheme.{u}} [IsAffine X] (V : X.Opens) :
    (⨆ f : {g : Γ(X, V) // IsAffineOpen (X.basicOpen g)}, X.basicOpen f.1) = V := by
  refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
  obtain ⟨r, hrV, hr⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := V) ⟨x, hx⟩ (by trivial)
  have key : X.basicOpen (X.presheaf.map (homOfLE (le_top (a := V))).op r) = X.basicOpen r := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.mpr hrV
  exact le_iSup (fun f : {g : Γ(X, V) // IsAffineOpen (X.basicOpen g)} ↦ X.basicOpen f.1)
    ⟨X.presheaf.map (homOfLE (le_top (a := V))).op r, key ▸ (isAffineOpen_top X).basicOpen r⟩
    (by rw [key]; exact hr)

/-- **Sections whose basic opens cover a quasi-compact open of an affine scheme span, provided
every open of the spectrum of every local ring is affine.**

This is the whole content of [Stacks, Tag 09N9]; affineness follows from it by [Stacks, Tag 01QF].
If the sections did not span they would lie in a maximal ideal `𝔫`; the contraction of `𝔫` to
`Γ(X, ⊤)` is a prime `Q`, and base change along the flat morphism from `Spec 𝒪_{X,x}` for a point
`x` realizing `Q` turns `Γ(X, V)` into its localization at `Q`
(`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` together with
`Stacks.AlgebraicGeometry.SectionsBaseChange.algebraIsPushout_sections` and
`Algebra.isLocalization_iff_isPushout`). There the open is affine, so the images of the sections
generate the unit ideal; but the image of `𝔫` is prime by
`IsLocalization.isPrime_of_isPrime_disjoint`, hence proper. -/
theorem span_eq_top_of_isCompact {X : Scheme.{u}} [IsAffine X]
    (hloc : ∀ x : X, ∀ W : (Spec (X.presheaf.stalk x)).Opens, IsAffineOpen W)
    (V : X.Opens) (hV : IsCompact (V : Set X))
    (s : Set Γ(X, V)) (hcover : (⨆ g : s, X.basicOpen g.1) = V) :
    Ideal.span s = ⊤ := by
  classical
  by_contra hne
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hne
  let algRB : Algebra Γ(X, ⊤) Γ(X, V) :=
    (Scheme.Hom.appLE (𝟙 X) ⊤ V (le_preimage_top (𝟙 X) V)).hom.toAlgebra
  have : 𝔫.IsPrime := h𝔫.isPrime
  set Q : PrimeSpectrum Γ(X, ⊤) :=
    ⟨Ideal.comap (algebraMap Γ(X, ⊤) Γ(X, V)) 𝔫, Ideal.comap_isPrime _ _⟩ with hQdef
  obtain ⟨O, φ, hflat, hWaff, hlocA⟩ := exists_flat_isLocalization_of_prime hloc Q
  have := hflat
  let algST : Algebra Γ(X, ⊤) Γ(Spec O, ⊤) :=
    (φ.appLE ⊤ ⊤ (le_preimage_top φ ⊤)).hom.toAlgebra
  have hlocA' : IsLocalization Q.asIdeal.primeCompl Γ(Spec O, ⊤) := hlocA
  -- the sections square of the base change along `φ` is a pushout of rings
  have H : IsPullback φ (𝟙 (Spec O)) (𝟙 X) φ := IsPullback.of_vert_isIso ⟨by simp⟩
  have hiso : IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := V) (UY := φ ⁻¹ᵁ V)
      (le_preimage_top φ ⊤) (le_preimage_top (𝟙 X) V) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _
      (isAffineOpen_top X) (isAffineOpen_top _) hV (IsQuasiSeparated.of_quasiSeparatedSpace _)
  let algTY : Algebra Γ(Spec O, ⊤) Γ(Spec O, φ ⁻¹ᵁ V) :=
    (Scheme.Hom.appLE (𝟙 (Spec O)) ⊤ (φ ⁻¹ᵁ V)
      (le_preimage_top (𝟙 (Spec O)) (φ ⁻¹ᵁ V))).hom.toAlgebra
  let algXY : Algebra Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) := (φ.appLE V (φ ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  let algSY : Algebra Γ(X, ⊤) Γ(Spec O, φ ⁻¹ᵁ V) :=
    (φ.appLE ⊤ (φ ⁻¹ᵁ V) (le_preimage_top φ (φ ⁻¹ᵁ V))).hom.toAlgebra
  have ⟨tow1, tow2⟩ : IsScalarTower Γ(X, ⊤) Γ(Spec O, ⊤) Γ(Spec O, φ ⁻¹ᵁ V) ∧
      IsScalarTower Γ(X, ⊤) Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) := by
    constructor <;> refine IsScalarTower.of_algebraMap_eq' ?_ <;>
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.appLE_comp_appLE, Category.id_comp, Category.comp_id]
  have key : Algebra.IsPushout Γ(X, ⊤) Γ(Spec O, ⊤) Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) :=
    algebraIsPushout_sections H V (φ ⁻¹ᵁ V) (le_preimage_top φ ⊤)
      (le_preimage_top (𝟙 X) V) (by simp) hiso le_rfl
      (le_preimage_top (𝟙 (Spec O)) (φ ⁻¹ᵁ V))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hlocC : IsLocalization
      (Algebra.algebraMapSubmonoid Γ(X, V) Q.asIdeal.primeCompl) Γ(Spec O, φ ⁻¹ᵁ V) :=
    (Algebra.isLocalization_iff_isPushout Q.asIdeal.primeCompl Γ(Spec O, ⊤)).mpr key.symm
  -- over the local ring the open is affine, so the images of `s` generate the unit ideal
  have hC : Ideal.map (algebraMap Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V)) (Ideal.span s) = ⊤ := by
    rw [Ideal.map_span]
    refine ((hWaff (φ ⁻¹ᵁ V)).iSup_basicOpen_eq_self_iff).mp ?_
    have himg : ∀ g : Γ(X, V),
        (Spec O).basicOpen (algebraMap Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) g) = φ ⁻¹ᵁ X.basicOpen g := by
      intro g
      simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
      exact (Scheme.preimage_basicOpen φ g).symm
    have step : (⨆ f : ↥(algebraMap Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) '' s), (Spec O).basicOpen f.1)
        = ⨆ g : ↥s, φ ⁻¹ᵁ X.basicOpen g.1 := by
      refine le_antisymm (iSup_le ?_) (iSup_le ?_)
      · rintro ⟨y, g, hg, rfl⟩
        rw [himg g]
        exact le_iSup (fun g : ↥s ↦ φ ⁻¹ᵁ X.basicOpen g.1) ⟨g, hg⟩
      · rintro ⟨g, hg⟩
        rw [← himg g]
        exact le_iSup (fun f : ↥(algebraMap Γ(X, V) Γ(Spec O, φ ⁻¹ᵁ V) '' s) ↦
          (Spec O).basicOpen f.1) ⟨_, g, hg, rfl⟩
    rw [step, ← Scheme.Hom.preimage_iSup, hcover]
  -- but the image of `𝔫` is prime, hence proper
  have hdisj : Disjoint
      (↑(Algebra.algebraMapSubmonoid Γ(X, V) Q.asIdeal.primeCompl) : Set Γ(X, V))
      (↑𝔫 : Set Γ(X, V)) := by
    rw [Set.disjoint_left]
    rintro y ⟨r, hr, rfl⟩ hy
    exact hr (Ideal.mem_comap.mpr hy)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid Γ(X, V) Q.asIdeal.primeCompl) Γ(Spec O, φ ⁻¹ᵁ V) 𝔫
    h𝔫.isPrime hdisj
  exact hprime.ne_top (top_le_iff.mp (hC ▸ Ideal.map_mono hle))

/-- **[Stacks, Tag 09N9].** Let `X` be an affine scheme all of whose local rings are Noetherian of
dimension at most one. Then every quasi-compact open `V ⊆ X` is affine.

The sections of `𝒪_X` over `V` whose basic open is affine span `Γ(X, V)` by
`span_eq_top_of_isCompact`, and they cover `V` by `iSup_basicOpen_isAffineOpen_eq`, so
[Stacks, Tag 01QF] applies. The dimension hypothesis enters only through
`AlgebraicGeometry.isAffineOpen_of_krullDimLE_one`, which makes every open of the spectrum of a
local ring of `X` affine. -/
@[stacks 09N9, ega "IV 21.12.9" "more general"]
theorem isAffineOpen_of_isCompact_of_krullDimLE_one {X : Scheme.{u}} [IsAffine X]
    (hN : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (hD : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (V : X.Opens) (hV : IsCompact (V : Set X)) : IsAffineOpen V := by
  refine isAffineOpen_of_isAffineOpen_basicOpen V
    {g : Γ(X, V) | IsAffineOpen (X.basicOpen g)} ?_ (fun g hg => hg)
  refine span_eq_top_of_isCompact (fun x W => ?_) V hV _ (iSup_basicOpen_isAffineOpen_eq V)
  have := hN x
  have := hD x
  exact isAffineOpen_of_krullDimLE_one (X.presheaf.stalk x) W

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

open Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard

/-- **The absolute hypothesis of `AffineReduction` holds.** A quasi-compact open subscheme of an
affine scheme whose local rings are Noetherian of dimension at most one is affine
([Stacks, Tag 09N9], `AlgebraicGeometry.isAffineOpen_of_isCompact_of_krullDimLE_one`), so the
positive-degree cohomology of a quasi-coherent module on it vanishes by [Stacks, Tag 01XB] —
through `Stacks.Cohomology.AffineBase.rightAcyclic_moduleGlobalSections`, which is that tag read
as acyclicity of the module-valued global sections functor.

The source of the open immersion is affine because its image is the quasi-compact open
`q.opensRange` of the target: the target is affine, hence compact, so quasi-compactness of `q`
makes the source compact, and an open immersion is an isomorphism onto its image. -/
theorem cohomologyVanishingQuasiCompactOpenInAffine :
    CohomologyVanishingQuasiCompactOpenInAffine.{u} := by
  intro T A q hq hqc hA hN hD G hG n hn
  have := hq
  have := hqc
  have := hA
  have := hG
  have hAcpt : IsCompact (Set.univ : Set A) := by
    simpa using (isAffineOpen_top A).isCompact
  have hTcpt : IsCompact (Set.univ : Set T) := by
    simpa using QuasiCompact.isCompact_preimage (f := q) Set.univ isOpen_univ hAcpt
  have hrange : IsCompact (q.opensRange : Set A) := by
    have : CompactSpace T := ⟨hTcpt⟩
    simpa using isCompact_range (f := (q.base : T → A)) (by fun_prop)
  have : IsAffine (q.opensRange).toScheme :=
    isAffineOpen_of_isCompact_of_krullDimLE_one hN hD _ hrange
  have : IsAffine T :=
    IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq q (q.opensRange).ι (by simp)).hom
  exact ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (moduleGlobalSections T) G).2 inferInstance).mp
    (rightAcyclic_moduleGlobalSections T G) (n : ℤ) (by exact_mod_cast hn)

end Stacks.AlgebraicGeometry.OneDimensionalLocal

end
