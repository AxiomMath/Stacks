module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.UniformVanishingDirectImage.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.UniformVanishingDirectImage.CohomologyBound

/-!
# A degree bound for higher direct images, uniform in the module and in the base change

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. Then there is an integer `n`, depending only on `f`, beyond which every higher
direct image of every quasi-coherent `𝒪_X`-module vanishes — and the same `n` works for every
base change of `f`. This last, uniform form is part (3) of [Stacks, Tag 01XJ]; part (2) is
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward` and
part (1), quasi-coherence of the higher direct images, is
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`.

The bound comes from a finite affine open covering `S = S₁ ∪ … ∪ S_m` and, for each `j`, a
finite affine open covering `f⁻¹(S_j) = U_{j1} ∪ … ∪ U_{jt_j}`; let
`d_j = max_I (|I| + t(⋂_{i ∈ I} U_{ji}) - 1)` be the degree bound of [Stacks, Tag 071L] for that
covering, and let `n = max_j d_j`. Vanishing of `R ᵖ f'_* F'` is checked on a basis of the base
(`Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage`),
and the basis to use consists of the affine opens `V` lying inside the preimage of a single
`S_j`. Over such a `V` the preimage `f'⁻¹(V)` is covered by the `t_j` opens
`pr⁻¹(U_{ji}) ∩ f'⁻¹(V)`, which are affine because `U_{ji}` and `V` both lie over the affine
`S_j`, and the finite intersections of those opens are covered by just as many affines as the
corresponding intersections of the `U_{ji}` — so [Stacks, Tag 071L] applies over `f'⁻¹(V)` with
the bound `d_j` unchanged.

## Main results

* `AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_of_affine_cover_bound`: vanishing of
  `R ᵖ f_* F` from affine coverings, with a degree bound, of the preimages of the members of a
  basis of the target.
* `AlgebraicGeometry.exists_isBasis_affine_cover_preimage_of_commSq` and
  `AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_of_commSq`: the covering of `X` over an
  affine covering of `S`, transported across a commutative square, and the bound of
  [Stacks, Tag 071L] it yields — the shared content of parts (2) and (3).
* `AlgebraicGeometry.exists_isBasis_isZero_cohomology_preimage`: a single degree beyond which the
  cohomology of every quasi-coherent module vanishes over the preimage of every member of some
  basis of `S`.
* `AlgebraicGeometry.exists_uniform_isZero_rightDerived_pushforward`: **[Stacks, Tag 01XJ] (3)**.

## Implementation notes

The hypothesis of `isZero_rightDerivedPlus_pushforward_of_affine_cover_bound` asks for an affine
covering of each finite intersection, of a size the degree bound controls, rather than for a
bound on `AlgebraicGeometry.Scheme.affineCoverNum` of that intersection. The two are equivalent
for a quasi-compact intersection, but the covering is what base change produces and it carries
quasi-compactness with it, so no quasi-separatedness of the total space is needed anywhere after
the data has been assembled. That matters: the base change `X ×_S S'` of a quasi-compact
quasi-separated `X` need not be quasi-separated as a space, since `S'` is arbitrary.

`isZero_rightDerivedPlus_pushforward_of_commSq` takes a bare commutative square rather than a
pullback square: all that the argument uses is `pr⁻¹(f⁻¹(S_j)) = f'⁻¹(g⁻¹(S_j))`, and keeping the
square general lets parts (2) and (3) be the two instances `pr = 𝟙` and `pr = pullback.fst`.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AffineHigherDirectImage
open Stacks.Cohomology.UniformVanishing

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Vanishing read off affine coverings of the preimages of a basis -/

/-- **Vanishing of `R ᵖ f_* F` from affine coverings of the preimages of a basis of the target.**
Suppose that for every member `V` of a basis of the opens of `S` the preimage `f⁻¹(V)` admits a
finite covering by affine opens `W 1, …, W k` such that every nonempty finite intersection
`⋂_{i ∈ I} W i` is covered by `c_I` affine opens with `|I| + c_I - 1 ≤ d`. Then
`R ᵖ f_* F = 0` for every `p ≥ d` and every quasi-coherent `𝒪_X`-module `F`.

This is [Stacks, Tag 071L] over `f⁻¹(V)` combined with the reduction of the vanishing of a higher
direct image to a basis of the target, which is [Stacks, Tag 01E4]. -/
theorem isZero_rightDerivedPlus_pushforward_of_affine_cover_bound {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {B : Set S.Opens} (hB : Opens.IsBasis B) (d : ℕ)
    (hcov : ∀ V ∈ B, ∃ (k : ℕ) (W : Fin k → X.Opens), (∀ i, IsAffineOpen (W i)) ∧
      (⨆ i, W i = f ⁻¹ᵁ V) ∧
      ∀ s : Finset (Fin k), s.Nonempty → ∃ (c : ℕ) (A : Fin c → X.Opens),
        (∀ a, IsAffineOpen (A a)) ∧ (⨆ a, A a = s.inf W) ∧ s.card + c - 1 ≤ d)
    (p : ℕ) (hp : d ≤ p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) := by
  refine isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage f F p hB fun V hV ↦ ?_
  obtain ⟨k, W, hWaff, hWcov, hWbd⟩ := hcov V hV
  exact isZero_cohomology_of_affine_cover_bound F d W hWaff hWcov hWbd p hp

/-! ### The bound of a covering of `X`, transported across a commutative square -/

/-- **A covering of `X` over an affine covering of `S` transports across a commutative square.**
Let `pr ≫ f = f' ≫ g` be a commutative square of schemes, let `S = S₁ ∪ … ∪ S_m` be a finite
affine open covering of the target of `f`, and let `f⁻¹(S_j) = U_{j1} ∪ … ∪ U_{jt_j}` be finite
affine open coverings whose nonempty finite intersections admit affine coverings of size bounded
by `d` in the sense of [Stacks, Tag 071L]. Assume that for each `j` the open
`pr⁻¹(A) ∩ f'⁻¹(V)` is affine whenever `A ⊆ f⁻¹(S_j)` and `V ⊆ g⁻¹(S_j)` are affine opens.

Then the affine opens of `S'` lying inside a single `g⁻¹(S_j)` form a basis, and over each of
them the preimage `f'⁻¹(V)` carries a covering with the same bound `d`: the opens
`pr⁻¹(U_{ji}) ∩ f'⁻¹(V)`, whose finite intersections are covered by exactly as many affines as
the corresponding intersections of the `U_{ji}`. -/
theorem exists_isBasis_affine_cover_preimage_of_commSq {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (pr : X' ⟶ X) (g : S' ⟶ S) (hsq : pr ≫ f = f' ≫ g)
    {m : ℕ} {S₀ : Fin m → S.Opens} (hS₀cov : ⨆ j, S₀ j = ⊤)
    (haff : ∀ (j : Fin m) (A : X.Opens) (V : S'.Opens), IsAffineOpen A → IsAffineOpen V →
      A ≤ f ⁻¹ᵁ S₀ j → V ≤ g ⁻¹ᵁ S₀ j → IsAffineOpen (pr ⁻¹ᵁ A ⊓ f' ⁻¹ᵁ V))
    {t : Fin m → ℕ} {U : ∀ j, Fin (t j) → X.Opens} (hUaff : ∀ j i, IsAffineOpen (U j i))
    (hUcov : ∀ j, ⨆ i, U j i = f ⁻¹ᵁ S₀ j) {d : ℕ}
    (hUbd : ∀ (j : Fin m) (s : Finset (Fin (t j))), s.Nonempty →
      ∃ (c : ℕ) (A : Fin c → X.Opens), (∀ a, IsAffineOpen (A a)) ∧
        (⨆ a, A a = s.inf (U j)) ∧ s.card + c - 1 ≤ d) :
    ∃ B : Set S'.Opens, Opens.IsBasis B ∧ ∀ V ∈ B,
      ∃ (k : ℕ) (W : Fin k → X'.Opens), (∀ i, IsAffineOpen (W i)) ∧ (⨆ i, W i = f' ⁻¹ᵁ V) ∧
        ∀ s : Finset (Fin k), s.Nonempty → ∃ (c : ℕ) (A : Fin c → X'.Opens),
          (∀ a, IsAffineOpen (A a)) ∧ (⨆ a, A a = s.inf W) ∧ s.card + c - 1 ≤ d := by
  classical
  have hcovS' : ⨆ j, g ⁻¹ᵁ S₀ j = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hS₀cov]; simp
  refine ⟨{V : S'.Opens | IsAffineOpen V ∧ ∃ j, V ≤ g ⁻¹ᵁ S₀ j}, ?_, ?_⟩
  · rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    have hxtop : x ∈ ⨆ j, g ⁻¹ᵁ S₀ j := by rw [hcovS']; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxtop
    obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_inter hx hj)
        (V ⊓ g ⁻¹ᵁ S₀ j).2
    exact ⟨A, ⟨hA, j, fun y hy ↦ (hAV hy).2⟩, hxA, fun y hy ↦ (hAV hy).1⟩
  · rintro V ⟨hVaff, j, hVj⟩
    have hUle := iSup_le_iff.mp (hUcov j).le
    refine ⟨t j, fun i ↦ pr ⁻¹ᵁ U j i ⊓ f' ⁻¹ᵁ V,
      fun i ↦ haff j _ _ (hUaff j i) hVaff (hUle i) hVj, ?_, fun s hs ↦ ?_⟩
    · rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, hUcov j, ← Scheme.Hom.comp_preimage, hsq,
        Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVj]
    · obtain ⟨c, A, hAaff, hAcov, hcard⟩ := hUbd j s hs
      obtain ⟨i₀, hi₀⟩ := hs
      have hAle : ∀ a, A a ≤ f ⁻¹ᵁ S₀ j := fun a ↦
        ((iSup_le_iff.mp hAcov.le a).trans (Finset.inf_le hi₀)).trans (hUle i₀)
      refine ⟨c, fun a ↦ pr ⁻¹ᵁ A a ⊓ f' ⁻¹ᵁ V,
        fun a ↦ haff j _ _ (hAaff a) hVaff (hAle a) hVj, ?_, hcard⟩
      rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, hAcov,
        finsetInf_inf (fun i ↦ pr ⁻¹ᵁ U j i) (f' ⁻¹ᵁ V) ⟨i₀, hi₀⟩,
        Scheme.Hom.finsetInf_preimage pr (U j) ⟨i₀, hi₀⟩]

/-- **The degree bound of a covering of `X` adapted to a commutative square.** Under the
hypotheses of `exists_isBasis_affine_cover_preimage_of_commSq`, `R ᵖ f'_* F' = 0` for every
`p ≥ d` and every quasi-coherent module `F'` on the source of `f'`. -/
theorem isZero_rightDerivedPlus_pushforward_of_commSq {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (pr : X' ⟶ X) (g : S' ⟶ S) (hsq : pr ≫ f = f' ≫ g)
    {m : ℕ} {S₀ : Fin m → S.Opens} (hS₀cov : ⨆ j, S₀ j = ⊤)
    (haff : ∀ (j : Fin m) (A : X.Opens) (V : S'.Opens), IsAffineOpen A → IsAffineOpen V →
      A ≤ f ⁻¹ᵁ S₀ j → V ≤ g ⁻¹ᵁ S₀ j → IsAffineOpen (pr ⁻¹ᵁ A ⊓ f' ⁻¹ᵁ V))
    {t : Fin m → ℕ} {U : ∀ j, Fin (t j) → X.Opens} (hUaff : ∀ j i, IsAffineOpen (U j i))
    (hUcov : ∀ j, ⨆ i, U j i = f ⁻¹ᵁ S₀ j) {d : ℕ}
    (hUbd : ∀ (j : Fin m) (s : Finset (Fin (t j))), s.Nonempty →
      ∃ (c : ℕ) (A : Fin c → X.Opens), (∀ a, IsAffineOpen (A a)) ∧
        (⨆ a, A a = s.inf (U j)) ∧ s.card + c - 1 ≤ d)
    (F : X'.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : d ≤ p) :
    IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).obj F) := by
  obtain ⟨B, hB, hcov⟩ := exists_isBasis_affine_cover_preimage_of_commSq f f' pr g hsq hS₀cov
    haff hUaff hUcov hUbd
  exact isZero_rightDerivedPlus_pushforward_of_affine_cover_bound f' F hB d hcov p hp

/-! ### The two uniform vanishing statements -/

/-- For a quasi-compact and quasi-separated `f : X ⟶ S` with `S` quasi-compact there are a finite
affine open covering `S₀` of `S`, finite affine open coverings `U j` of the preimages
`f⁻¹(S₀ j)`, and a single degree `d` dominating the bound of [Stacks, Tag 071L] for each of those
coverings, in the form of affine coverings of their nonempty finite intersections. -/
theorem exists_affine_cover_data {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] :
    ∃ (m : ℕ) (S₀ : Fin m → S.Opens) (t : Fin m → ℕ) (U : ∀ j, Fin (t j) → X.Opens) (d : ℕ),
      (∀ j, IsAffineOpen (S₀ j)) ∧ (⨆ j, S₀ j = ⊤) ∧ (∀ j i, IsAffineOpen (U j i)) ∧
      (∀ j, ⨆ i, U j i = f ⁻¹ᵁ S₀ j) ∧
      ∀ (j : Fin m) (s : Finset (Fin (t j))), s.Nonempty →
        ∃ (c : ℕ) (A : Fin c → X.Opens), (∀ a, IsAffineOpen (A a)) ∧
          (⨆ a, A a = s.inf (U j)) ∧ s.card + c - 1 ≤ d := by
  classical
  obtain ⟨m, S₀, hS₀aff, hS₀cov⟩ := exists_finite_affineOpen_cover (⊤ : S.Opens)
    (by simpa using isCompact_univ (X := (S : Type u)))
  have hchoice : ∀ j, ∃ (k : ℕ) (U : Fin k → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      ⨆ i, U i = f ⁻¹ᵁ S₀ j :=
    fun j ↦ exists_finite_affineOpen_cover _ (f.isCompact_preimage (hS₀aff j).isCompact)
  choose t U hUaff hUcov using hchoice
  refine ⟨m, S₀, t, U, Finset.univ.sup fun j ↦ X.coverDegreeBound (U j),
    hS₀aff, hS₀cov, hUaff, hUcov, fun j s hs ↦ ?_⟩
  have hUle := iSup_le_iff.mp (hUcov j).le
  obtain ⟨A, hAaff, hAcov⟩ := Scheme.exists_affineCover_affineCoverNum (s.inf (U j))
    (isCompact_finsetInf_of_isQuasiSeparated
      (f.isQuasiSeparated_preimage (hS₀aff j).isQuasiSeparated) (U j)
      (fun i ↦ (hUaff j i).isCompact) hUle hs)
  refine ⟨X.affineCoverNum (s.inf (U j)), A, hAaff, hAcov, ?_⟩
  have := X.le_coverDegreeBound (U j) hs
  have := Finset.le_sup (f := fun j ↦ X.coverDegreeBound (U j)) (Finset.mem_univ j)
  lia

/-- If `S₀ ⊆ S` is an affine open and `A ⊆ f⁻¹(S₀)` and `V ⊆ S₀` are affine opens, then
`A ∩ f⁻¹(V)` is affine, stated with the preimages under the identities of `X` and `S`. -/
private theorem isAffineOpen_inf_preimage_id {X S : Scheme.{u}} (f : X ⟶ S) {S₀ : S.Opens}
    (hS₀ : IsAffineOpen S₀) (A : X.Opens) (V : S.Opens) (hA : IsAffineOpen A)
    (hV : IsAffineOpen V) (hAle : A ≤ f ⁻¹ᵁ S₀) (hVle : V ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ S₀) :
    IsAffineOpen ((𝟙 X : X ⟶ X) ⁻¹ᵁ A ⊓ f ⁻¹ᵁ V) := by
  simpa using isAffineOpen_inf_preimage_of_le f hS₀ hV hA (by simpa using hVle) hAle

/-- **Uniform vanishing of the cohomology of quasi-coherent modules over the preimages of a basis
of the target.** For a quasi-compact and quasi-separated `f : X ⟶ S` with `S` quasi-compact there
are an `n` and a basis `B` of the opens of `S` such that `H^p(f⁻¹(V), F) = 0` for every `V ∈ B`,
every `p ≥ n` and every quasi-coherent `𝒪_X`-module `F`.

This is [Stacks, Tag 071L] applied over each `f⁻¹(V)`. -/
theorem exists_isBasis_isZero_cohomology_preimage {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ (n : ℕ) (B : Set S.Opens), Opens.IsBasis B ∧
      ∀ V ∈ B, ∀ (F : X.Modules) [F.IsQuasicoherent], ∀ p : ℕ, n ≤ p →
        IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) p F) := by
  obtain ⟨m, S₀, t, U, d, hS₀aff, hS₀cov, hUaff, hUcov, hUbd⟩ := exists_affine_cover_data f
  obtain ⟨B, hB, hcov⟩ := exists_isBasis_affine_cover_preimage_of_commSq f f (𝟙 X) (𝟙 S) (by simp)
    hS₀cov (fun j A V hA hV hAle hVle ↦
      isAffineOpen_inf_preimage_id f (hS₀aff j) A V hA hV hAle hVle) hUaff hUcov hUbd
  refine ⟨d, B, hB, fun V hV F hF p hp ↦ ?_⟩
  have : F.IsQuasicoherent := hF
  obtain ⟨k, W, hWaff, hWcov, hWbd⟩ := hcov V hV
  exact isZero_cohomology_of_affine_cover_bound F d W hWaff hWcov hWbd p hp

/-- **Stacks Project, Tag 01XJ (3).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes with `S` quasi-compact. There is an integer `n = n(X, S, f)` such that for
every morphism `g : S' ⟶ S` the base change `f' : X' = X ×_S S' ⟶ S'` satisfies
`R ᵖ f'_* F' = 0` for every `p ≥ n` and every quasi-coherent module `F'` on `X'`. -/
@[stacks 01XJ "base_change_uniform_vanishing",
  ega "IV 1.7.21" "base change vanishing",
  ega "III 1.4.12" "existence of r"]
theorem exists_uniform_isZero_rightDerived_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ n : ℤ, ∀ (S' : Scheme.{u}) (g : S' ⟶ S) (F : (pullback f g).Modules) [F.IsQuasicoherent],
      ∀ p : ℤ, n ≤ p →
        IsZero (((Scheme.Modules.pushforward (pullback.snd f g)).rightDerivedPlus p).obj F) := by
  obtain ⟨m, S₀, t, U, d, hS₀aff, hS₀cov, hUaff, hUcov, hUbd⟩ := exists_affine_cover_data f
  refine ⟨(d : ℤ), fun S' g F hF p hp ↦ ?_⟩
  have : F.IsQuasicoherent := hF
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, (P : ℤ) = p :=
    ⟨p.toNat, Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg d) hp)⟩
  refine isZero_rightDerivedPlus_pushforward_of_commSq f (pullback.snd f g) (pullback.fst f g) g
    pullback.condition hS₀cov (fun j A V hA hV hAle hVle ↦ ?_) hUaff hUcov hUbd F P
    (by exact_mod_cast hp)
  have : IsAffine A.toScheme := hA
  have : IsAffine V.toScheme := hV
  have : IsAffine (S₀ j).toScheme := hS₀aff j
  exact isAffineOpen_inf_preimage f g hAle hVle

end AlgebraicGeometry
