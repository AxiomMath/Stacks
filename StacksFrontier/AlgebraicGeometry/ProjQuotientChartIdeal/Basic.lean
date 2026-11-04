module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientSaturationKer.Basic
public import StacksFrontier.AlgebraicGeometry.HomogeneousAwayMapCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison

/-!
# The chart kernel of `Proj (𝒮 / I) ⟶ Proj 𝒮`

Let `i : Z ⟶ Proj 𝒮` be a closed immersion and `I = idealOfClosedSubscheme 𝒮 i` its graded ideal
of equations. Over a standard open `D₊(f)`, with `f` homogeneous of positive degree, the fraction
`a / f ^ n` lies in the kernel of the map on sections of `ambientHom 𝒮 i : Proj (𝒮 / I) ⟶ Proj 𝒮`
exactly when `f ^ k * a ∈ I` for some `k`. From this,
`Stacks.ClosedSubschemeProjQuotient.SaturationIdentification` is reduced to a statement about the
map `i` on sections over a family of standard opens covering `Proj 𝒮`.

## Main results

* `Stacks.ProjQuotientChartIdeal.irrelevant_le_map_quotientMk`: the irrelevant ideal of `A ⧸ I`
  is contained in the image of the irrelevant ideal of `A`.
* `Stacks.ProjQuotientChartIdeal.ambientHom_eq_projMap`:
  `Stacks.ClosedSubschemeProjQuotient.ambientHom` is `AlgebraicGeometry.Proj.map` at the graded
  quotient map.
* `Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff`: the kernel of
  `AlgebraicGeometry.Proj.map ψ hψ` on sections over `D₊(f)` is the kernel of
  `HomogeneousLocalization.Away.map ψ f`.
* `Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_ambientHom_iff`: `a / f ^ n` lies in
  the kernel of `Γ(Proj 𝒮, D₊(f)) ⟶ Γ(Proj (𝒮 / I), D₊(ψ f))` if and only if
  `f ^ k * a ∈ idealOfClosedSubscheme 𝒮 i` for some `k`.
* `Stacks.ProjQuotientChartIdeal.ker_le_ker_of_app_awayMk`: an inclusion of the kernel ideal
  sheaves of two quasi-compact morphisms to `Proj 𝒜` may be checked on the degree-zero fractions
  over a covering family of standard opens.
* `Stacks.ProjQuotientChartIdeal.ker_ambientHom_le_ker_of_mem_ideal` and
  `Stacks.ProjQuotientChartIdeal.ker_le_ker_ambientHom_of_app`: the two inclusions between the
  ideal sheaves of `Z` and of `Proj (𝒮 / I)`, each from a statement about `i` on the standard
  charts.
* `Stacks.ProjQuotientChartIdeal.saturationIdentification_of_app_awayMk_eq_ideal`:
  `Stacks.ClosedSubschemeProjQuotient.SaturationIdentification 𝒮 i` holds if, on each chart of a
  covering family, a fraction `a / f ^ n` dies on `Z` exactly when `f ^ j * a ∈ I` for some `j`.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme
open Stacks.RingTheory.HomogeneousQuotient
open Stacks.ClosedSubschemeProjQuotient

universe u

namespace Stacks.ProjQuotientChartIdeal

/-! ### `ambientHom` is Mathlib's `Proj.map` -/

/-- For a homogeneous ideal `I` of a graded ring `A`, the irrelevant ideal of `A ⧸ I` is
contained in the image of the irrelevant ideal of `A` under the quotient map. -/
theorem irrelevant_le_map_quotientMk {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜) :
    HomogeneousIdeal.irrelevant (quotientGrading 𝒜 I) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (quotientMk 𝒜 I) := by
  refine (HomogeneousIdeal.irrelevant_le (quotientGrading 𝒜 I)).2 fun j hj x hx ↦ ?_
  obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff 𝒜 I).1 hx
  show Ideal.Quotient.mk I.toIdeal a ∈
    ((HomogeneousIdeal.irrelevant 𝒜).map (quotientMk 𝒜 I)).toAddSubmonoid
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hj ha)

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [GradedAlgebra 𝒮]

/-- The canonical morphism `ambientHom 𝒮 i : Proj (𝒮 / I) ⟶ Proj 𝒮`, for `I` the graded ideal of
equations of the closed immersion `i`, is `AlgebraicGeometry.Proj.map` at the graded quotient
map. -/
theorem ambientHom_eq_projMap {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    ambientHom 𝒮 i =
      Proj.map (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i))
        (irrelevant_le_map_quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _ _ _

/-! ### The chart kernel of `Proj.map` -/

/-- The canonical map `(A_f)₀ ⟶ Γ(Proj A, D₊(f))` is an isomorphism for `f` homogeneous of
positive degree. -/
theorem isIso_awayToSection {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    IsIso (Proj.awayToSection 𝒜 f) := by
  rw [← Proj.basicOpenIsoAway_hom 𝒜 f hf hm]
  infer_instance

/-- For a graded ring homomorphism `ψ : 𝒜 →+*ᵍ ℬ` with `ℬ₊ ≤ 𝒜₊.map ψ`, and `f ∈ 𝒜 m` with
`m > 0`, a degree-zero fraction over `D₊(f)` lies in the kernel of the map on sections of
`AlgebraicGeometry.Proj.map ψ hψ` if and only if it lies in the kernel of
`HomogeneousLocalization.Away.map ψ f`. -/
theorem awayToSection_mem_ker_app_projMap_iff {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    {m : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m) (z : Away 𝒜 f) :
    (Proj.awayToSection 𝒜 f).hom z ∈
        RingHom.ker ((Proj.map ψ hψ).app (Proj.basicOpen 𝒜 f)).hom ↔
      z ∈ RingHom.ker (Away.map ψ f) := by
  have := isIso_awayToSection (ψ.map_mem hf) hm
  have h := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE ψ hψ hf) z
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h
  have h' : ((Proj.map ψ hψ).app (Proj.basicOpen 𝒜 f)).hom ((Proj.awayToSection 𝒜 f).hom z) =
      (Proj.awayToSection ℬ (ψ f)).hom ((Away.map ψ f) z) := by
    rw [Scheme.Hom.app_eq_appLE]; exact h
  rw [RingHom.mem_ker, RingHom.mem_ker, h']
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Proj.awayToSection ℬ (ψ f))).1

/-! ### The comparison with the ideal of equations -/

/-- Let `i : Z ⟶ Proj 𝒮` be a closed immersion, `I` its graded ideal of equations, and `f ∈ 𝒮 m`
homogeneous with `m > 0`. Then the degree-zero fraction `a / f ^ n` over `D₊(f)`, for
`a ∈ 𝒮 (n • m)`, dies on `Proj (𝒮 / I)` if and only if `f ^ k * a ∈ idealOfClosedSubscheme 𝒮 i`
for some `k`. -/
theorem awayToSection_mem_ker_app_ambientHom_iff {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] {m : ℕ} {f : S} (hf : f ∈ 𝒮 m) (hm : 0 < m)
    (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • m)) :
    (Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n a ha) ∈
        RingHom.ker ((ambientHom 𝒮 i).app (Proj.basicOpen 𝒮 f)).hom ↔
      ∃ k : ℕ, f ^ k * a ∈ idealOfClosedSubscheme 𝒮 i := by
  rw [ambientHom_eq_projMap,
    awayToSection_mem_ker_app_projMap_iff _ _ hf hm,
    Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff]
  exact exists_congr fun k ↦ Ideal.Quotient.eq_zero_iff_mem

/-! ### Locality, and the two inclusions of ideal sheaves -/

/-- Let `p, q` be quasi-compact morphisms to `Proj 𝒜` and `f k` homogeneous elements of positive
degrees whose standard opens cover `Proj 𝒜`. If every degree-zero fraction over each `D₊(f k)`
that dies under `p` also dies under `q`, then `p.ker ≤ q.ker`. -/
theorem ker_le_ker_of_app_awayMk {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Z W : Scheme.{u}} (p : Z ⟶ Proj 𝒜) (q : W ⟶ Proj 𝒜)
    [QuasiCompact p] [QuasiCompact q] {ι : Type*} (f : ι → A) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒜 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, Proj.basicOpen 𝒜 (f k) = ⊤)
    (H : ∀ (k : ι) (z : Away 𝒜 (f k)),
      (p.app (Proj.basicOpen 𝒜 (f k))).hom ((Proj.awayToSection 𝒜 (f k)).hom z) = 0 →
      (q.app (Proj.basicOpen 𝒜 (f k))).hom ((Proj.awayToSection 𝒜 (f k)).hom z) = 0) :
    p.ker ≤ q.ker := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun k ↦ ⟨Proj.basicOpen 𝒜 (f k),
      Proj.isAffineOpen_basicOpen 𝒜 (f k) (hf k) (hd k)⟩)
    hcover fun k ↦ ?_
  rw [Scheme.Hom.ker_apply p _, Scheme.Hom.ker_apply q _]
  have := isIso_awayToSection (hf k) (hd k)
  intro x hx
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒜 (f k))).2 x
  exact RingHom.mem_ker.2 (H k z (RingHom.mem_ker.1 hx))

/-- If, over each chart `D₊(f k)` of a covering family, every fraction `a / f k ^ n` with
`f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i` for some `j` dies on `Z`, then the ideal sheaf of
`Proj (𝒮 / I)` is contained in that of `Z`. -/
theorem ker_ambientHom_le_ker_of_mem_ideal {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤)
    (H : ∀ (k : ι) (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d k)),
        (∃ j : ℕ, f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i) →
        (i.app (Proj.basicOpen 𝒮 (f k))).hom
          ((Proj.awayToSection 𝒮 (f k)).hom (Away.mk 𝒮 (hf k) n a ha)) = 0) :
    (ambientHom 𝒮 i).ker ≤ i.ker := by
  have : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  refine ker_le_ker_of_app_awayMk 𝒮 (ambientHom 𝒮 i) i f d hf hd hcover fun k z hz ↦ ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hf k) z
  exact H k n a ha ((awayToSection_mem_ker_app_ambientHom_iff 𝒮 i (hf k) (hd k) n a ha).1
    (RingHom.mem_ker.2 hz))

/-- If, over each chart `D₊(f k)` of a covering family, every fraction `a / f k ^ n` that dies on
`Z` has `f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i` for some `j`, then the ideal sheaf of `Z` is
contained in that of `Proj (𝒮 / I)`. -/
theorem ker_le_ker_ambientHom_of_app {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤)
    (H : ∀ (k : ι) (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d k)),
        (i.app (Proj.basicOpen 𝒮 (f k))).hom
            ((Proj.awayToSection 𝒮 (f k)).hom (Away.mk 𝒮 (hf k) n a ha)) = 0 →
          ∃ j : ℕ, f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i) :
    i.ker ≤ (ambientHom 𝒮 i).ker := by
  have : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  refine ker_le_ker_of_app_awayMk 𝒮 i (ambientHom 𝒮 i) f d hf hd hcover fun k z hz ↦ ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (hf k) z
  exact RingHom.mem_ker.1
    ((awayToSection_mem_ker_app_ambientHom_iff 𝒮 i (hf k) (hd k) n a ha).2 (H k n a ha hz))

/-- Let `f k` be homogeneous elements of positive degrees whose standard opens cover `Proj 𝒮`.
If, for every chart and every degree-zero fraction `a / f k ^ n` over it, that fraction dies on `Z`
exactly when `f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i` for some `j`, then
`SaturationIdentification 𝒮 i` holds. -/
theorem saturationIdentification_of_app_awayMk_eq_ideal {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, Proj.basicOpen 𝒮 (f k) = ⊤)
    (H : ∀ (k : ι) (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d k)),
        (i.app (Proj.basicOpen 𝒮 (f k))).hom
            ((Proj.awayToSection 𝒮 (f k)).hom (Away.mk 𝒮 (hf k) n a ha)) = 0 ↔
          ∃ j : ℕ, f k ^ j * a ∈ idealOfClosedSubscheme 𝒮 i) :
    SaturationIdentification 𝒮 i :=
  ProjQuotientSaturationKer.saturationIdentification_of_ker_eq 𝒮 i
    (le_antisymm
      (ker_le_ker_ambientHom_of_app 𝒮 i f d hf hd hcover fun k n a ha ↦ (H k n a ha).1)
      (ker_ambientHom_le_ker_of_mem_ideal 𝒮 i f d hf hd hcover fun k n a ha ↦ (H k n a ha).2))

end Stacks.ProjQuotientChartIdeal

end
