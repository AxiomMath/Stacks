module

public import StacksFrontier.AlgebraicGeometry.TwistedThickeningLift.Kernel
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.GradedUnitClosedSurjective
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.PushforwardPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# Lifting a section of a tensor power across a first-order thickening, after a power

Let `i : Z ⟶ X` be a first-order thickening — a closed immersion whose ideal sheaf `ℐ` has
`ℐ² = 0` — of a quasi-compact separated scheme `X`, let `L` be an invertible `𝒪_X`-module and let
`t` be a global section of `i^* L^{⊗ n}` whose nonvanishing locus `Z_t` is affine. This file
proves that some power of `t` is the restriction of a global section `T` of a tensor power of `L`,
in the form actually needed: `i^{-1}(X_T) = Z_t`.

This is the cohomological step of [Stacks Project, Tag 09MS] in its first-order case, which the
source proves by annihilating the obstruction class `∂t ∈ H¹(X, ℐ ⊗ L^{⊗ n})` with a power of `t`
([Stacks Project, Tag 01XR]) and the derivation rule `∂(t^{e+1}) = (e+1) t^e ∂t`
([Stacks Project, Tag 0B8S]). Here the obstruction class is never formed: only the Čech cocycle
representing it on a finite affine cover, and that cocycle is killed by hand. The argument of
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine` is run in
charts of `L`:

* cover `X` by finitely many affine charts `U_j` of `L` (`Stacks.TwistedThickeningLift.IsChart`),
  with unit `ε_j` of degree one; their pairwise intersections are affine, `X` being separated;
* lift `t` over each `U_j` to `b_j = β_j ε_j^n` and over the affine open `V` matching `Z_t` to
  `c = γ_j ε_j^n`, the unit `L^{⊗ n} ⟶ i_* i^* L^{⊗ n}` being surjective over affine opens; the
  differences die on `Z`, so `β_j - g_{jk}^n β_k` and `β_j - γ_j` vanish on `Z`, where
  `ε_k = g_{jk} ε_j`;
* `V ∩ U_j` is the basic open of `β_j`, both having inverse image `Z_t ∩ i^{-1} U_j`;
* from here the computation is the untwisted one, in the functions `β_j` and `g_{jk}^n β_k`: the
  corrected functions `θ_j = β_j^N - N β_j^K F_j` satisfy `θ_j = g_{jk}^{nN} θ_k`, so the sections
  `θ_j ε_j^{nN}` glue to a global section `T` of `L^{⊗ nN}`;
* `X_T ∩ U_j` is the basic open of `θ_j`, whose inverse image is that of `β_j`.

Square-zeroness of `ℐ` enters only through functions, by
`Stacks.Thickenings.mul_eq_zero_of_isFirstOrderThickening`, as in the untwisted case.

## Main results

* `Stacks.TwistedThickeningLift.exists_preimage_nonvanishingLocus_eq`: the lift.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample (IsInvertibleModule)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)

universe u

namespace Stacks.TwistedThickeningLift

/-! ### Nonvanishing loci of restricted sections -/

/-- The nonvanishing locus of the restriction of a global section to `V` is the part of its
nonvanishing locus inside `V`. -/
theorem nonvanishingLocusOn_res {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) (V : X.Opens) :
    nonvanishingLocusOn M V ((M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s) =
      (V : Set X) ∩ Stacks.Ample.nonvanishingLocus M s := by
  ext y
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun hc => h ?_⟩
    rwa [TopCat.Presheaf.germ_res_apply]
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun hc => h ?_⟩
    rwa [TopCat.Presheaf.germ_res_apply] at hc

variable {X Z : Scheme.{u}} {L : X.Modules} [IsInvertibleModule X L] {i : Z ⟶ X}

/-! ### Basic opens of corrected functions -/

/-- Subtracting a nilpotent function does not change the basic open. -/
theorem basicOpen_sub_of_isNilpotent {X : Scheme.{u}} {U : X.Opens} (f r : Γ(X, U))
    (hr : IsNilpotent r) : X.basicOpen (f - r) = X.basicOpen f := by
  have key : ∀ (a b : Γ(X, U)), IsNilpotent b → X.basicOpen (a + b) ≤ X.basicOpen a := by
    intro a b hb p hp
    have hpU : p ∈ U := X.basicOpen_le _ hp
    rw [Scheme.mem_basicOpen X _ p hpU] at hp ⊢
    have hb' : IsNilpotent ((X.presheaf.germ U p hpU).hom (-b)) := hb.neg.map _
    have h := hb'.isUnit_add_left_of_commute hp (Commute.all _ _)
    rwa [← map_add, add_neg_cancel_right] at h
  refine le_antisymm (by simpa [sub_eq_add_neg] using key f (-r) hr.neg) ?_
  simpa only [sub_add_cancel] using key (f - r) r hr

/-- **The basic open of a corrected power is the basic open of the function**, when the correction
has square zero. -/
theorem basicOpen_corrected {X : Scheme.{u}} {U : X.Opens} (β H c : Γ(X, U)) (hH : H * H = 0)
    {N : ℕ} (hN : 0 < N) (K : ℕ) : X.basicOpen (β ^ N - c * (β ^ K * H)) = X.basicOpen β := by
  have hnil : IsNilpotent (c * (β ^ K * H)) :=
    ⟨2, by rw [show (c * (β ^ K * H)) ^ 2 = c ^ 2 * β ^ (2 * K) * (H * H) by ring, hH, mul_zero]⟩
  rw [basicOpen_sub_of_isNilpotent _ _ hnil]
  exact X.toRingedSpace.basicOpen_pow β N hN

/-! ### A section dying on `Z`, in a chart -/

/-- **In a chart, a section dying on `Z` has chart function vanishing on `Z`.** -/
theorem app_eq_zero_of_dies_of_chart {W : X.Opens} {ε : LRing L W} (hε : IsChart L ε) {n : ℕ}
    {y : Γ(pow L n, W)} (hy : Dies L i y) {h : Γ(X, W)} (hyh : incl n y = alg L W h * ε ^ n) :
    (i.app W).hom h = 0 := by
  obtain ⟨-, ε', h2, h3⟩ := hε
  obtain ⟨E', hE'⟩ := h2.pow n
  have hmul : incl (L := L) 0 (show Γ(pow L 0, W) from h) =
      incl ((n : ℤ) + n * -1) (((situation L).laurentAlgebra.mul n (n * -1)).app (op W) y E') := by
    rw [incl_zero_eq_alg, ← incl_mul, hE', hyh, mul_assoc, ← mul_pow, h3, one_pow, mul_one]
  exact app_eq_zero_of_dies h (dies_of_incl_eq (by ring) hmul (hy.mul_right E'))

/-! ### The lift -/

variable (i) in
/-- The restriction of a global section of `i^* L^{⊗ n}` to `i^{-1} W`, read as a section of
`i_* i^* L^{⊗ n}` over `W`. -/
def tloc {n : ℕ} (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤)) (W : X.Opens) :
    Γ(ppiece L i n, W) :=
  ((Stacks.AmpleLocallyClosed.pullbackModule i (pow L n)).presheaf.map
    (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op).hom t

/-- The restriction of `tloc i t W` to an open `W' ≤ W` is `tloc i t W'`. -/
theorem tloc_res {n : ℕ} (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤))
    {W W' : X.Opens} (h : W' ≤ W) :
    ((Scheme.Modules.presheaf (ppiece L i n)).map (homOfLE h).op).hom (tloc i t W) =
      tloc i t W' := by
  change ((Stacks.AmpleLocallyClosed.pullbackModule i (pow L n)).presheaf.map
    (homOfLE (i.preimage_mono h)).op).hom (((Stacks.AmpleLocallyClosed.pullbackModule i
      (pow L n)).presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op).hom t) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- If a section `y` of `L^{⊗ n}` over `W` restricts on `Z` to `t`, then so does its restriction
to an open `W' ≤ W`. -/
theorem up_pres_of_up_eq {n : ℕ} {t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤)}
    {W W' : X.Opens} (h : W' ≤ W) {y : Γ(pow L n, W)} (hy : up i y = tloc i t W) :
    up i (pres h y) = tloc i t W' := by
  rw [up_pres, hy, tloc_res]

/-- **Over an affine open, `t` lifts.** The unit `L^{⊗ n} ⟶ i_* i^* L^{⊗ n}` is an epimorphism of
quasi-coherent modules (`Stacks.AmpleThickeningDevissage.epi_gradedUnit_app_of_isClosedImmersion`),
hence surjective on sections over an affine open. -/
theorem exists_up_eq [IsClosedImmersion i] {n : ℕ}
    (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤)) {W : X.Opens}
    (hW : IsAffineOpen W) : ∃ y : Γ(pow L n, W), up i y = tloc i t W := by
  have : Epi (unitApp L i n) :=
    Stacks.AmpleThickeningDevissage.epi_gradedUnit_app_of_isClosedImmersion i _ n
  have hq : (pow L n).IsQuasicoherent := (situation L).isQuasicoherent_tensorPower n
  have : (ppiece L i n).IsQuasicoherent :=
    Stacks.AmpleThickeningDevissage.isQuasicoherent_pushforwardPullbackGradedAlgebra_piece i _ n hq
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X (unitApp L i n) W hW _

/-- **The inverse image of the nonvanishing locus of a lift is that of `t`, over the open.** This
is [Stacks Project, Tag 0H78] for a section over an open
(`Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn`). -/
theorem preimage_nonvanishingLocusOn_eq {n : ℕ}
    {t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤)} {W : X.Opens}
    {y : Γ(pow L n, W)} (hy : up i y = tloc i t W) :
    i.base ⁻¹' nonvanishingLocusOn (pow L n) W y =
      ((i ⁻¹ᵁ W : Z.Opens) : Set Z) ∩ Stacks.Ample.nonvanishingLocus _ t := by
  rw [Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn, ← up_eq, hy]
  exact nonvanishingLocusOn_res _ t (i ⁻¹ᵁ W)

/-- Two overlapping chart decompositions of the restriction of one section give functions related
by the transition function: if `ε_b = g ε_a` and the section is `γ_a ε_a^n = γ_b ε_b^n`, then
`γ_a = g^n γ_b`. -/
theorem chart_transition {W : X.Opens} {εa εb : LRing L W} (hεa : IsChart L εa) {n : ℕ}
    {g γa γb : Γ(X, W)} (hg : εb = alg L W g * εa ^ 1)
    (h : alg L W γa * εa ^ n = alg L W γb * εb ^ n) : γa = g ^ n * γb := by
  refine hεa.eq_of_eq (k := n) ?_
  rw [h, hg, pow_one, mul_pow, ← mul_assoc, ← map_pow, ← map_mul, mul_comm (g ^ n)]

/-- **The lift of a section of `i^* L^{⊗ n}` with affine nonvanishing locus, after a power.** Let
`i : Z ⟶ X` be a first-order thickening of a quasi-compact separated scheme, `L` an invertible
`𝒪_X`-module, and `t` a global section of `i^* L^{⊗ n}` whose nonvanishing locus is an affine open
`W`. Then there are `N > 0` and a global section `T` of `L^{⊗ nN}` with `i^{-1}(X_T) = Z_t`. -/
theorem exists_preimage_nonvanishingLocus_eq [IsClosedImmersion i] (hker : i.ker ^ 2 = ⊥)
    [X.IsSeparated] [CompactSpace X] (n : ℕ)
    (t : Γ(Stacks.AmpleLocallyClosed.pullbackModule i (pow L n), ⊤)) (Wt : Z.Opens)
    (hWt : (Wt : Set Z) = Stacks.Ample.nonvanishingLocus _ t) (hWaff : IsAffineOpen Wt) :
    ∃ N : ℕ, 0 < N ∧ ∃ T : Γ(pow L ((n * N : ℕ) : ℤ), ⊤),
      i.base ⁻¹' Stacks.Ample.nonvanishingLocus (pow L ((n * N : ℕ) : ℤ)) T =
        Stacks.Ample.nonvanishingLocus _ t := by
  classical
  have hk : Stacks.Thickenings.IsFirstOrderThickening i := ⟨inferInstance, hker⟩
  have hT : Stacks.Thickenings.IsThickening i := hk.isThickening
  have hinj : ∀ {V₁ V₂ : X.Opens}, i ⁻¹ᵁ V₁ = i ⁻¹ᵁ V₂ → V₁ = V₂ := by
    intro V₁ V₂ h
    rw [← hT.opensCongr_preimage V₁, ← hT.opensCongr_preimage V₂, h]
  -- the open of `X` matching `Z_t`
  obtain ⟨V, hVpre⟩ : ∃ V : X.Opens, i ⁻¹ᵁ V = Wt :=
    ⟨hT.opensCongr Wt, hT.preimage_opensCongr _⟩
  have hVaff : IsAffineOpen V :=
    (Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage hT V).mpr
      (by rwa [hVpre])
  -- a finite cover by affine charts
  choose U0 hpU0 hU0aff hU0ch using fun p : X => exists_isAffineOpen_isChart (L := L) p
  choose ε0 hε0 using hU0ch
  obtain ⟨F, hF⟩ := (isCompact_univ (X := X)).elim_finite_subcover (fun p => (U0 p : Set X))
    (fun p => (U0 p).isOpen) (fun p _ => Set.mem_iUnion.mpr ⟨p, hpU0 p⟩)
  let ι := {p // p ∈ F}
  let U : ι → X.Opens := fun j => U0 j.1
  let ε : ∀ j, LRing L (U j) := fun j => ε0 j.1
  have hε : ∀ j, IsChart L (ε j) := fun j => hε0 j.1
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hU0aff j.1
  have hPaff : ∀ a b, IsAffineOpen (U a ⊓ U b) := fun a b => (hUaff a).inf (hUaff b)
  have hmemU : ∀ p : X, ∃ j, p ∈ U j := fun p => by
    obtain ⟨q, hq, h⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ p))
    exact ⟨⟨q, hq⟩, h⟩
  have hUcover : (⨆ j, U j) = ⊤ := top_le_iff.mp fun p _ => Opens.mem_iSup.mpr (hmemU p)
  -- the lifts of `t`, and their chart functions
  choose b hb using fun j => exists_up_eq t (hUaff j)
  obtain ⟨c, hc⟩ := exists_up_eq t hVaff
  choose β hβ using fun j => (hε j).exists_eq (k := n) ⟨b j, rfl⟩
  choose γ hγ using fun j =>
    ((hε j).res (inf_le_right : V ⊓ U j ≤ U j)).exists_eq (k := n)
      ⟨pres (inf_le_left : V ⊓ U j ≤ V) c, rfl⟩
  choose g hg using fun a b =>
    ((hε a).res (inf_le_left : U a ⊓ U b ≤ U a)).exists_eq (k := 1)
      (((hε b).1.res (inf_le_right : U a ⊓ U b ≤ U b)).of_eq (by norm_num))
  -- `V ∩ U j` is the basic open of `β j`
  have hpreβ : ∀ j, i ⁻¹ᵁ X.basicOpen (β j) = Wt ⊓ i ⁻¹ᵁ U j := by
    intro j
    refine Opens.ext ?_
    have h1 := preimage_nonvanishingLocusOn_eq (hb j)
    rw [(hε j).nonvanishingLocusOn_eq n (hβ j)] at h1
    change i.base ⁻¹' (X.basicOpen (β j) : Set X) = (Wt : Set Z) ∩ (i ⁻¹ᵁ U j : Set Z)
    rw [h1, hWt, Set.inter_comm]
  have hWeq : ∀ j, V ⊓ U j = X.basicOpen (β j) := by
    intro j
    refine hinj ?_
    rw [hpreβ j, Scheme.Hom.preimage_inf, hVpre]
  -- the differences of the lifts vanish on `Z`
  have hd0 : ∀ j, (i.app (V ⊓ U j)).hom
      (TopCat.Presheaf.restrictOpen (β j) (V ⊓ U j) inf_le_right - γ j) = 0 := by
    intro j
    refine app_eq_zero_of_dies_of_chart ((hε j).res inf_le_right)
      (y := pres (inf_le_right : V ⊓ U j ≤ U j) (b j) - pres inf_le_left c)
      (dies_sub_of_up_eq ((up_pres_of_up_eq _ (hb j)).trans (up_pres_of_up_eq _ hc).symm)) ?_
    rw [incl_sub, hγ j, ← res_incl, hβ j, res_alg_mul_pow, map_sub, sub_mul]
  have hdP : ∀ a d, (i.app (U a ⊓ U d)).hom
      (TopCat.Presheaf.restrictOpen (β a) (U a ⊓ U d) inf_le_left -
        g a d ^ n * TopCat.Presheaf.restrictOpen (β d) (U a ⊓ U d) inf_le_right)
        = 0 := by
    intro a d
    refine app_eq_zero_of_dies_of_chart ((hε a).res inf_le_left)
      (y := pres (inf_le_left : U a ⊓ U d ≤ U a) (b a) - pres inf_le_right (b d))
      (dies_sub_of_up_eq ((up_pres_of_up_eq _ (hb a)).trans (up_pres_of_up_eq _ (hb d)).symm))
      ?_
    rw [incl_sub, ← res_incl, ← res_incl, hβ a, hβ d, res_alg_mul_pow, res_alg_mul_pow, hg a d,
      map_sub, map_mul, map_pow]
    ring
  -- the correction over each chart, with a uniform exponent
  have hstep : ∀ j, ∃ m : ℕ, ∀ M, m ≤ M → ∃ G : Γ(X, U j), (i.app (U j)) G = 0 ∧
      G |_ (V ⊓ U j) = (β j |_ (V ⊓ U j)) ^ M * (β j |_ (V ⊓ U j) - γ j) := by
    intro j
    obtain ⟨n', y, hy⟩ := Stacks.Thickenings.exists_eq_pow_mul_of_isAffineOpen' (hUaff j) (β j)
      inf_le_right (hWeq j) (β j |_ (V ⊓ U j) - γ j)
    have hezero : (i.app (V ⊓ U j)) (β j |_ (V ⊓ U j) - γ j) = 0 := hd0 j
    have hy0 : TopCat.Presheaf.restrictOpen ((i.app (U j)) y) (i ⁻¹ᵁ (V ⊓ U j))
        (i.preimage_mono inf_le_right) = 0 := by
      rw [← Stacks.Thickenings.app_restrict i inf_le_right (i.preimage_mono inf_le_right) y, hy,
        map_mul, map_pow, hezero, mul_zero]
    have hWpre : i ⁻¹ᵁ (V ⊓ U j) = Z.basicOpen ((i.app (U j)) (β j)) := by
      rw [hWeq j, Scheme.preimage_basicOpen]
    obtain ⟨p, hp⟩ := Stacks.Thickenings.exists_pow_mul_eq_zero_of_res_eq_zero
      ((hUaff j).preimage i).isCompact ((i.app (U j)) y) ((i.app (U j)) (β j))
      (i.preimage_mono inf_le_right) hWpre hy0
    refine ⟨p + n', fun M hM => ⟨β j ^ (M - n') * y, ?_, ?_⟩⟩
    · rw [map_mul, map_pow, show M - n' = p + (M - n' - p) by omega, pow_add, mul_right_comm, hp,
        zero_mul]
    · rw [Stacks.Thickenings.restrict_mul inf_le_right,
        Stacks.Thickenings.restrict_pow inf_le_right,
        hy, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
  choose m hm using hstep
  obtain ⟨M, hM⟩ : ∃ M, ∀ j, m j ≤ M :=
    ⟨Finset.univ.sup m, fun j => Finset.le_sup (Finset.mem_univ j)⟩
  choose G hG0 hGe using fun j => hm j M (hM j)
  -- the transition of the functions `γ`
  have hQa : ∀ a d, V ⊓ (U a ⊓ U d) ≤ V ⊓ U a := fun _ _ => inf_le_inf le_rfl inf_le_left
  have hQd : ∀ a d, V ⊓ (U a ⊓ U d) ≤ V ⊓ U d := fun _ _ => inf_le_inf le_rfl inf_le_right
  have hγQ : ∀ a d, TopCat.Presheaf.restrictOpen (γ a) (V ⊓ (U a ⊓ U d))
        (inf_le_inf le_rfl inf_le_left) =
      (g a d |_ (V ⊓ (U a ⊓ U d))) ^ n *
        TopCat.Presheaf.restrictOpen (γ d) (V ⊓ (U a ⊓ U d)) (inf_le_inf le_rfl inf_le_right) := by
    intro a d
    have ha := congrArg (res (hQa a d)) (hγ a)
    have hd := congrArg (res (hQd a d)) (hγ d)
    rw [← res_incl, res_alg_mul_pow] at ha hd
    simp only [res_res] at ha hd
    have hgQ := congrArg (res (inf_le_right : V ⊓ (U a ⊓ U d) ≤ U a ⊓ U d)) (hg a d)
    rw [res_alg_mul_pow, res_res, res_res] at hgQ
    exact chart_transition ((hε a).res ((hQa a d).trans inf_le_right)) hgQ (ha.symm.trans hd)
  -- a power of the local lift kills the cocycle, with an exponent uniform over the pairs
  have hpair : ∀ a d, ∃ q : ℕ, (β a |_ (U a ⊓ U d)) ^ q *
      ((β a |_ (U a ⊓ U d)) ^ M * (β a |_ (U a ⊓ U d) - g a d ^ n * β d |_ (U a ⊓ U d))
        - (G a |_ (U a ⊓ U d) - (g a d ^ n) ^ (M + 1) * G d |_ (U a ⊓ U d))) = 0 := by
    intro a d
    have hQ : V ⊓ (U a ⊓ U d) = X.basicOpen (β a |_ (U a ⊓ U d)) := by
      rw [Stacks.Thickenings.basicOpen_restrict_eq, ← hWeq a]
      exact le_antisymm (le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans inf_le_left)))
        (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    refine Stacks.Thickenings.exists_pow_mul_sub_eq_zero hk (hPaff a d) inf_le_right _ _ _ _
      (TopCat.Presheaf.restrictOpen (γ a) (V ⊓ (U a ⊓ U d)) (hQa a d)) M hQ (hdP a d) ?_ ?_ ?_
    · have h0 := congrArg (fun z => TopCat.Presheaf.restrictOpen z (i ⁻¹ᵁ (V ⊓ (U a ⊓ U d)))
        (i.preimage_mono (hQd a d))) (hd0 d)
      simp only [Stacks.Thickenings.restrict_zero] at h0
      rw [← Stacks.Thickenings.app_restrict i (hQd a d) (i.preimage_mono (hQd a d)),
        Stacks.Thickenings.restrict_sub (hQd a d), TopCat.Presheaf.restrict_restrict] at h0
      rw [hγQ a d, Stacks.Thickenings.restrict_mul inf_le_right,
        Stacks.Thickenings.restrict_pow inf_le_right,
        TopCat.Presheaf.restrict_restrict, ← mul_sub, map_mul, h0, mul_zero]
    · simpa only [TopCat.Presheaf.restrict_restrict, Stacks.Thickenings.restrict_mul,
        Stacks.Thickenings.restrict_pow, Stacks.Thickenings.restrict_sub] using
        congrArg (fun z => TopCat.Presheaf.restrictOpen z (V ⊓ (U a ⊓ U d)) (hQa a d)) (hGe a)
    · have h2 := congrArg
        (fun z => TopCat.Presheaf.restrictOpen z (V ⊓ (U a ⊓ U d)) (hQd a d)) (hGe d)
      simp only [TopCat.Presheaf.restrict_restrict, Stacks.Thickenings.restrict_mul,
        Stacks.Thickenings.restrict_pow, Stacks.Thickenings.restrict_sub] at h2
      simp only [TopCat.Presheaf.restrict_restrict, Stacks.Thickenings.restrict_mul,
        Stacks.Thickenings.restrict_pow, h2, hγQ a d]
      ring
  choose q hq using hpair
  obtain ⟨K, hK⟩ : ∃ K, ∀ a d, q a d ≤ K :=
    ⟨Finset.univ.sup fun p : ι × ι => q p.1 p.2,
      fun a d => Finset.le_sup (f := fun p : ι × ι => q p.1 p.2) (Finset.mem_univ (a, d))⟩
  -- the corrected functions, and their transition
  let θ : ∀ j, Γ(X, U j) := fun j =>
    β j ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(X, U j)) * (β j ^ K * G j)
  have hθ : ∀ a d, θ a |_ (U a ⊓ U d) = (g a d ^ n) ^ (K + M + 1) * θ d |_ (U a ⊓ U d) := by
    intro a d
    have hgy0 : (i.app (U a ⊓ U d)) ((g a d ^ n) ^ (M + 1) * G d |_ (U a ⊓ U d)) = 0 := by
      rw [map_mul,
        Stacks.Thickenings.app_restrict i inf_le_right (i.preimage_mono inf_le_right) (G d),
        hG0 d, Stacks.Thickenings.restrict_zero, mul_zero]
    simp only [θ, Stacks.Thickenings.restrict_sub, Stacks.Thickenings.restrict_mul,
      Stacks.Thickenings.restrict_pow, Stacks.Thickenings.restrict_natCast]
    exact (corrected_pow_eq
      (Stacks.Thickenings.forall_mul_eq_zero_of_isFirstOrderThickening hk (hPaff a d)) K M
      (RingHom.mem_ker.mpr (hdP a d)) (RingHom.mem_ker.mpr hgy0)
      (Stacks.Thickenings.pow_mul_eq_zero_of_le (hK a d) (hq a d))).trans (by ring)
  -- the sections `θ_j ε_j^{nN}` glue
  have hhom : ∀ j, ∃ T : Γ(pow L ((n * (K + M + 1) : ℕ) : ℤ), U j),
      incl _ T = alg L (U j) (θ j) * ε j ^ (n * (K + M + 1)) := fun j =>
    (((hε j).1.pow (n * (K + M + 1))).alg_mul (θ j)).of_eq (by push_cast; ring)
  choose T hTj using hhom
  have hcompat : ∀ a d, pres (inf_le_left : U a ⊓ U d ≤ U a) (T a) =
      pres (inf_le_right : U a ⊓ U d ≤ U d) (T d) := by
    intro a d
    refine incl_injective _ ?_
    rw [← res_incl, ← res_incl, hTj a, hTj d, res_alg_mul_pow, res_alg_mul_pow, hg a d]
    change alg L _ (θ a |_ (U a ⊓ U d)) * _ = alg L _ (θ d |_ (U a ⊓ U d)) * _
    rw [hθ a d, map_mul, map_pow, map_pow, mul_pow, pow_one]
    ring
  obtain ⟨T₀, hT₀, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(pow L ((n * (K + M + 1) : ℕ) : ℤ)).presheaf, (pow L _).isSheaf⟩ : TopCat.Sheaf Ab X)
    U ⊤ (fun j => homOfLE le_top) hUcover.ge T (fun a d => hcompat a d)
  -- the nonvanishing locus of the glued section is `V`
  have hloc : ∀ j, nonvanishingLocusOn (pow L ((n * (K + M + 1) : ℕ) : ℤ)) (U j) (T j) =
      ((V ⊓ U j : X.Opens) : Set X) := by
    intro j
    rw [(hε j).nonvanishingLocusOn_eq _ (hTj j)]
    change ((X.basicOpen (β j ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(X, U j)) * (β j ^ K * G j)) :
      X.Opens) : Set X) = _
    rw [basicOpen_corrected (β j) (G j) _ (Stacks.Thickenings.mul_eq_zero_of_isFirstOrderThickening
      hk (hUaff j) (hG0 j) (hG0 j)) (Nat.succ_pos _) K, hWeq j]
  have hXT :
      Stacks.Ample.nonvanishingLocus (pow L ((n * (K + M + 1) : ℕ) : ℤ)) T₀ = (V : Set X) := by
    ext p
    obtain ⟨j, hj⟩ := hmemU p
    have h1 := nonvanishingLocusOn_res (pow L ((n * (K + M + 1) : ℕ) : ℤ)) T₀ (U j)
    rw [show ((Scheme.Modules.presheaf (pow L ((n * (K + M + 1) : ℕ) : ℤ))).map
      (homOfLE (le_top : U j ≤ ⊤)).op).hom T₀ = T j from hT₀ j, hloc j] at h1
    have h2 := congrArg (p ∈ ·) h1
    simp only [Opens.coe_inf, Set.mem_inter_iff, eq_iff_iff] at h2
    exact ⟨fun hp => (h2.mpr ⟨hj, hp⟩).1, fun hp => (h2.mp ⟨hp, hj⟩).2⟩
  refine ⟨K + M + 1, Nat.succ_pos _, T₀, ?_⟩
  rw [hXT, ← hWt, ← hVpre]
  rfl

end Stacks.TwistedThickeningLift


end
