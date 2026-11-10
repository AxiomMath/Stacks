module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumSeries
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# Power sums and Chern characters of modules of arbitrary rank and of complexes

Let `X` be locally of finite type over the base of chapter 42.

**Modules of arbitrary rank.** For a finite locally free `𝒪_X`-module `ℰ` whose rank need not be
constant, [Stacks, Tag 0ESW] and [Stacks, Tag 0FA7] define `P_p(ℰ) ∈ A^p(X)` on the rank loci
`X_r`, where `ℰ` has constant rank `r`, and assemble by [Stacks, Tag 0FDZ]; `P_0(ℰ) = r(ℰ)` is the
rank class. The Chern character is `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐`. [Stacks, Tag 0F9C]
holds for them: `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)` and `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` for a short exact
sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules.

**Complexes.** For a bounded complex `ℰ^•` of finite locally free modules of constant ranks,
Section 42.46 of the source (just before [Stacks, Tag 0ESZ]) sets
`P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)`. For a locally bounded complex, with ranks varying, the class is
assembled over the rank loci by Stacks 0FDZ, as in the proof of Stacks 0ESZ
(`Stacks.Chow.powerSumComplex`). On a complex vanishing outside a range of degrees it is the
alternating sum of the power sums of the terms, whatever their ranks
(`Stacks.Chow.powerSumComplex_eq_sum_Icc`).

## Main definitions

* `Stacks.Chow.powerSumOfFiniteLocallyFree` — `P_p(ℰ)` for `ℰ` of arbitrary rank.
* `Stacks.Chow.chernCharacterOfFiniteLocallyFree` — `ch_p(ℰ) = P_p(ℰ)/p!`.
* `Stacks.Chow.powerSumComplex` — `P_p(ℰ^•)` of a locally bounded complex.

## References

* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open TotalChowClass

/-! ### Power sums of modules of constant rank: two normalizations -/

section Normalization

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- Isomorphic modules have the same power sums, whatever ranks they are presented with. -/
theorem powerSumTotal_eq_of_iso {E E' : X.Modules} {r r' : ℕ}
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    (e : E ≅ E') (p : ℕ) : powerSumTotal C sX E r p = powerSumTotal C sX E' r' p := by
  have h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e hE
  exact (powerSumTotal_congr C sX e rfl p).trans (powerSumTotal_congr_rank C sX E' h hE' p)

/-- **The power sums of a module of rank `0` vanish.** Its Chern classes are those of `1`, which
is its own square, and the power sums are additive. -/
theorem powerSumTotal_of_rank_zero (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] (p : ℕ) :
    powerSumTotal C sX E 0 p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [powerSumTotal_zero, Nat.cast_zero]
  · rw [powerSumTotal_of_ne_zero C sX E 0 hp]
    have hconv : chernSeq C sX E 0 = fun n =>
        ∑ j ∈ Finset.range (n + 1), chernSeq C sX E 0 (n - j) * chernSeq C sX E 0 j := by
      funext n
      refine Subtype.ext ?_
      rw [show ((∑ j ∈ Finset.range (n + 1), chernSeq C sX E 0 (n - j) * chernSeq C sX E 0 j :
          chernRing C sX) : TotalChowClass C sX) = ∑ j ∈ Finset.range (n + 1),
            ((chernSeq C sX E 0 (n - j) : TotalChowClass C sX) * chernSeq C sX E 0 j) from
          map_sum (chernRing C sX).subtype _ _]
      change TotalChowClass.homComponent n (totalChern C sX E 0) = ∑ j ∈ Finset.range (n + 1),
        TotalChowClass.homComponent (n - j) (totalChern C sX E 0) *
          TotalChowClass.homComponent j (totalChern C sX E 0)
      rw [← TotalChowClass.homComponent_mul_sum, totalChern_of_rank_zero, one_mul]
    have h := AlgebraicGeometry.powerSumEval_convolution (chernSeq C sX E 0) (chernSeq C sX E 0)
      (chernSeq_zero C sX _ _) (chernSeq_zero C sX _ _) p
    rw [← hconv] at h
    have h0 : AlgebraicGeometry.powerSumEval (chernSeq C sX E 0) p = 0 :=
      by simpa using (left_eq_add.mp h)
    rw [h0]
    rfl

/-- **The power sums of a zero module vanish**, whatever rank it is presented with. -/
theorem powerSumTotal_of_isZero {E : X.Modules} {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hE : IsZero E)
    (p : ℕ) : powerSumTotal C sX E r p = 0 := by
  have := isFiniteLocallyFreeOfRank_zero_of_isZero hE
  rw [powerSumTotal_congr_rank C sX E ‹_› (isFiniteLocallyFreeOfRank_zero_of_isZero hE),
    powerSumTotal_of_rank_zero]

/-- **The total Chern class of a zero module is `1`**, whatever rank it is presented with. -/
theorem totalChern_of_isZero {E : X.Modules} {r : ℕ}
    [hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hE : IsZero E) : totalChern C sX E r = 1 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sX).elim _ _
  · obtain rfl := Scheme.Modules.isFiniteLocallyFreeOfRank_unique E hr
      (isFiniteLocallyFreeOfRank_zero_of_isZero hE) x
    exact totalChern_of_rank_zero C sX E

end Normalization

/-- A class restricts along `h` to `d` once it does so on every piece `h⁻¹ᵁ U i ⟶ U i` of a clopen
decomposition. -/
private theorem res_eq_of_res_piece_eq (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S}
    {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] {ι : Type u}
    {U : ι → Y.Opens} (hU : IsClopenDecomposition U) (h : Y' ⟶ Y) [LocallyOfFiniteType h]
    (hs : h ≫ sY = sY') (c : TotalChowClass C sY) (d : TotalChowClass C sY')
    (H : ∀ (i : ι) (m : (h ⁻¹ᵁ U i : Scheme.{u}) ⟶ U i) [LocallyOfFiniteType m]
      (_hfac : (h ⁻¹ᵁ U i).ι ≫ h = m ≫ (U i).ι) (hpm : m ≫ ((U i).ι ≫ sY) = (h ⁻¹ᵁ U i).ι ≫ sY'),
      TotalChowClass.res m hpm (TotalChowClass.res (U i).ι rfl c) =
        TotalChowClass.res (h ⁻¹ᵁ U i).ι rfl d) :
    TotalChowClass.res h hs c = d := by
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun i ↦ ?_
  have ha : ∀ i, h ⁻¹ᵁ U i ≤ h ⁻¹ᵁ U (id i) := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ U i).ι ≫ h = pieceMap h (fun i ↦ h ⁻¹ᵁ U i) U id ha i ≫ (U i).ι :=
    (pieceMap_comp_ι h _ _ id ha i).symm
  have hpm : pieceMap h (fun i ↦ h ⁻¹ᵁ U i) U id ha i ≫ ((U i).ι ≫ sY) =
      (h ⁻¹ᵁ U i).ι ≫ sY' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (U i).ι rfl _ hpm]
  exact H i _ hfac hpm

/-! ### Modules of arbitrary rank -/

section ArbitraryRank

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **The power sum `P_p(ℰ)` of a finite locally free module of arbitrary rank**, Stacks 0FA7 and
0F9B: the total class whose restriction to each rank locus `X_r` is the power sum
`P_p(ℰ|_{X_r})` of the constant-rank module `ℰ|_{X_r}`, assembled by Stacks 0FDZ. For `p = 0` it
is the rank `r(ℰ)` of Stacks 0ESW. -/
def powerSumOfFiniteLocallyFree (p : ℕ) : TotalChowClass C sX :=
  TotalChowClass.glue (isClopenDecomposition_rankLociFamily F) fun r ↦
    letI := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
    powerSumTotal C ((rankLociFamily F r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down p

/-- The restriction of `P_p(ℰ)` to the rank locus `X_r` is `P_p(ℰ|_{X_r})`. -/
theorem res_powerSumOfFiniteLocallyFree_rankLocus (r : ULift.{u} ℕ) (p : ℕ) :
    letI := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
    TotalChowClass.res (rankLociFamily F r).ι rfl (powerSumOfFiniteLocallyFree C sX F p) =
      powerSumTotal C ((rankLociFamily F r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down p :=
  TotalChowClass.res_glue (isClopenDecomposition_rankLociFamily F) _ r

/-- **Characterization of `P_p(ℰ)`**: along every `h : X' ⟶ X` locally of finite type along which
`h^*ℰ` has constant rank `s`, the restriction of `P_p(ℰ)` is `P_p(h^*ℰ)`. -/
theorem res_powerSumOfFiniteLocallyFree_of_rank {X' : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj F) s] (p : ℕ) :
    TotalChowClass.res h hs (powerSumOfFiniteLocallyFree C sX F p) =
      powerSumTotal C sX' ((Scheme.Modules.pullback h).obj F) s p := by
  have hU := isClopenDecomposition_rankLociFamily F
  refine res_eq_of_res_piece_eq C hU h hs _ _ fun r m _ hfac hpm ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  let hpr := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down m
  let hps := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback h).obj F) s (h ⁻¹ᵁ rankLociFamily F r).ι
  rw [powerSumOfFiniteLocallyFree, TotalChowClass.res_glue hU, res_powerSumTotal,
    res_powerSumTotal]
  exact powerSumTotal_eq_of_iso C _ (pullbackPullbackIsoOfComp hfac.symm F) p

/-- **On a module of constant rank `r`**, `P_p(ℰ)` is the power sum of
`Stacks.Chow.powerSumTotal`. -/
theorem powerSumOfFiniteLocallyFree_eq_powerSumTotal (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (p : ℕ) :
    powerSumOfFiniteLocallyFree C sX F p = powerSumTotal C sX F r p := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (𝟙 X)
  rw [← TotalChowClass.res_id (powerSumOfFiniteLocallyFree C sX F p),
    res_powerSumOfFiniteLocallyFree_of_rank C sX F (𝟙 X) (Category.id_comp sX) r]
  exact powerSumTotal_congr C sX (E' := F) ((Scheme.Modules.pullbackId X).app F) rfl p

/-- **Invariance of `P_p(ℰ)` under isomorphism.** -/
theorem powerSumOfFiniteLocallyFree_congr {F' : X.Modules}
    [hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F'] (e : F ≅ F')
    (p : ℕ) : powerSumOfFiniteLocallyFree C sX F p = powerSumOfFiniteLocallyFree C sX F' p := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily F) fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  let e' := (Scheme.Modules.pullback (rankLociFamily F r).ι).mapIso e
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F') r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e' ‹_›
  rw [res_powerSumOfFiniteLocallyFree_rankLocus C sX F r p,
    res_powerSumOfFiniteLocallyFree_of_rank C sX F' _ _ r.down p]
  exact powerSumTotal_congr C _ e' rfl p

/-- **Restriction of `P_p(ℰ)`**: `res_h P_p(ℰ) = P_p(h^*ℰ)` for every `h : X' ⟶ X` locally of
finite type. -/
theorem res_powerSumOfFiniteLocallyFree {X' : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX')
    (p : ℕ) :
    haveI := isFiniteLocallyFree_pullbackObj F h
    TotalChowClass.res h hs (powerSumOfFiniteLocallyFree C sX F p) =
      powerSumOfFiniteLocallyFree C sX' ((Scheme.Modules.pullback h).obj F) p := by
  have hF' := isFiniteLocallyFree_pullbackObj F h
  have hU := isClopenDecomposition_rankLociFamily ((Scheme.Modules.pullback h).obj F)
  refine TotalChowClass.eq_of_res_eq hU fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily ((Scheme.Modules.pullback h).obj F) r
  let e : (Scheme.Modules.pullback
        ((rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι ≫ h)).obj F ≅
      (Scheme.Modules.pullback (rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι).obj
        ((Scheme.Modules.pullback h).obj F) :=
    ((Scheme.Modules.pullbackComp
      (rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι h).app F).symm
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
        ((rankLociFamily ((Scheme.Modules.pullback h).obj F) r).ι ≫ h)).obj F) r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm ‹_›
  rw [TotalChowClass.res_res, res_powerSumOfFiniteLocallyFree_of_rank C sX F _ _ r.down,
    res_powerSumOfFiniteLocallyFree_rankLocus C sX' _ r]
  exact powerSumTotal_congr C _ e rfl p

/-- **`P_0(ℰ)` is the rank class** `r(ℰ)` of Stacks 0ESW: on the rank locus `X_r` it is `r`. -/
theorem res_powerSumOfFiniteLocallyFree_zero_rankLocus (r : ULift.{u} ℕ) :
    TotalChowClass.res (rankLociFamily F r).ι rfl (powerSumOfFiniteLocallyFree C sX F 0) =
      (r.down : TotalChowClass C ((rankLociFamily F r).ι ≫ sX)) := by
  rw [res_powerSumOfFiniteLocallyFree_rankLocus, powerSumTotal_zero]

omit hF in
/-- **Stacks 0F9C.** For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free
`𝒪_X`-modules, of ranks that need not be constant, `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)` for every `p`. -/
@[stacks 0F9C "the precise form: P_p(E) = P_p(E_1) + P_p(E_2) in A^p(X), for every p >= 0, for a \
short exact sequence of finite locally free modules of arbitrary ranks; P_p is the polynomial of \
Stacks 0F9B in the Chern classes of Stacks 0B7H, assembled over the rank loci (Stacks 0ESW, 0FA7)"]
theorem powerSumOfFiniteLocallyFree_eq_add_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (p : ℕ) :
    haveI := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
    powerSumOfFiniteLocallyFree C sX S.X₂ p =
      powerSumOfFiniteLocallyFree C sX S.X₁ p + powerSumOfFiniteLocallyFree C sX S.X₃ p := by
  have := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
  refine TotalChowClass.eq_of_res_eq_of_constantRank₂ C sX S.X₁ S.X₃
    fun {T sT _} g _ hs r s hr hs' ↦ ?_
  have hS' := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree g S hS
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₁ r := hr
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₃ s := hs'
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj S.X₂) (r + s) :=
    GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS' r s ‹_› ‹_›
  have := hr
  have := hs'
  rw [map_add, res_powerSumOfFiniteLocallyFree_of_rank C sX S.X₂ g hs (r + s),
    res_powerSumOfFiniteLocallyFree_of_rank C sX S.X₁ g hs r,
    res_powerSumOfFiniteLocallyFree_of_rank C sX S.X₃ g hs s]
  exact powerSumTotal_eq_add_of_shortExact C sT (S.map (Scheme.Modules.pullback g)) hS' r s p

/-- **`P_p(ℰ) ∈ A^p(X)`** for a finite locally free module of arbitrary rank. -/
def powerSumClassOfFiniteLocallyFree (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  powerSumOfFiniteLocallyFree C sX F p p

/-- **The Chern character** `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐` of a finite locally free module of
arbitrary rank, Stacks 0FA7. -/
def chernCharacterOfFiniteLocallyFree (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassOfFiniteLocallyFree C sX F p

omit hF in
/-- **Stacks 0F9C for the Chern character**: `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)`, degree by degree, for a
short exact sequence of finite locally free modules of arbitrary ranks. -/
@[stacks 0F9C "ch(E) = ch(E_1) + ch(E_2), read in every degree p as ch_p = P_p/p! in \
A^p(X) ⊗ Q, for a short exact sequence of finite locally free modules of arbitrary ranks"]
theorem chernCharacterOfFiniteLocallyFree_eq_add_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (p : ℕ) :
    haveI := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
    chernCharacterOfFiniteLocallyFree C sX S.X₂ p =
      chernCharacterOfFiniteLocallyFree C sX S.X₁ p +
        chernCharacterOfFiniteLocallyFree C sX S.X₃ p := by
  have := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
  rw [chernCharacterOfFiniteLocallyFree, chernCharacterOfFiniteLocallyFree,
    chernCharacterOfFiniteLocallyFree, powerSumClassOfFiniteLocallyFree,
    powerSumClassOfFiniteLocallyFree, powerSumClassOfFiniteLocallyFree,
    powerSumOfFiniteLocallyFree_eq_add_of_shortExact C sX S hS p, TotalChowClass.add_apply,
    TensorProduct.tmul_add]

end ArbitraryRank

/-! ### Complexes -/

section Complex

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **`P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)`** for a complex whose `n`-th term is finite locally free of
constant rank `ρ n`, with `ρ` finitely supported: the definition of Section 42.46 of the source,
the sum being over the degrees of nonzero rank. -/
def powerSumComplexBounded (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) : TotalChowClass C sY :=
  ∑ n ∈ ρ.support, ((n.negOnePow : ℤ) •
    (letI := hP n; powerSumTotal C sY (P.X n) (ρ n) p))

variable (P : CochainComplex Y.Modules ℤ)

/-- The sum may be taken over any finite set of degrees outside of which the ranks vanish. -/
theorem powerSumComplexBounded_eq_sum (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) (s : Finset ℤ) (hs : ∀ n ∉ s, ρ n = 0) :
    powerSumComplexBounded C sY P ρ hP p =
      ∑ n ∈ s, ((n.negOnePow : ℤ) • (letI := hP n; powerSumTotal C sY (P.X n) (ρ n) p)) := by
  refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
  · by_contra h
    exact (Finsupp.mem_support_iff.1 hn) (hs n h)
  · have h0 : ρ n = 0 := Finsupp.notMem_support_iff.1 hn
    let := hP n
    have hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) 0 :=
      h0 ▸ hP n
    rw [powerSumTotal_congr_rank C sY (P.X n) (hP n) hr, powerSumTotal_of_rank_zero, smul_zero]

/-- **Invariance under termwise isomorphism**, whatever rank functions the two complexes are
presented with. -/
theorem powerSumComplexBounded_congr {P' : CochainComplex Y.Modules ℤ} (e : ∀ n, P.X n ≅ P'.X n)
    (ρ σ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hP' : ∀ n,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n) (σ n))
    (p : ℕ) :
    powerSumComplexBounded C sY P ρ hP p = powerSumComplexBounded C sY P' σ hP' p := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sY).elim _ _
  · obtain rfl : ρ = σ := Finsupp.ext fun n ↦
      Scheme.Modules.isFiniteLocallyFreeOfRank_unique (P'.X n)
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e n) (hP n))
        (hP' n) y
    refine Finset.sum_congr rfl fun n _ => ?_
    let := hP n
    let := hP' n
    rw [powerSumTotal_congr C sY (e n) rfl]

/-- **Restriction**: `res_h P_p(ℰ^•) = P_p(h^*ℰ^•)` for a bounded complex of constant ranks. -/
theorem res_powerSumComplexBounded {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) :
    TotalChowClass.res h hs (powerSumComplexBounded C sY P ρ hP p) =
      powerSumComplexBounded C sY' (pullbackComplex h P) ρ
        (isFiniteLocallyFreeOfRank_pullbackComplex_X P h ρ hP) p := by
  rw [powerSumComplexBounded, powerSumComplexBounded, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  let := hP n
  rw [map_zsmul, res_powerSumTotal]
  rfl

variable {P} (hP : IsLocallyBoundedFiniteLocallyFree P)

/-- **The power sum `P_p(ℰ^•)` of a locally bounded complex of finite locally free modules**, the
ranks of the terms varying: on the rank locus `Y_ρ`, where the complex is bounded with constant
ranks `ρ`, it is `∑_n (-1)^n P_p(ℰ^n|_{Y_ρ})`; these classes are assembled by Stacks 0FDZ, as in
the proof of Stacks 0ESZ. -/
def powerSumComplex (p : ℕ) : TotalChowClass C sY :=
  TotalChowClass.glue (isClopenDecomposition_complexRankLoci hP) fun ρ ↦
    powerSumComplexBounded C ((complexRankLoci hP ρ).ι ≫ sY)
      (pullbackComplex (complexRankLoci hP ρ).ι P) ρ.down
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down) p

/-- The restriction of `P_p(ℰ^•)` to a rank locus `Y_ρ` is `∑_n (-1)^n P_p(ℰ^n|_{Y_ρ})`. -/
theorem res_powerSumComplex_complexRankLocus (ρ : ℤ →₀ ℕ) (p : ℕ) :
    TotalChowClass.res (complexRankLocus hP ρ).ι rfl (powerSumComplex C sY hP p) =
      powerSumComplexBounded C ((complexRankLocus hP ρ).ι ≫ sY)
        (pullbackComplex (complexRankLocus hP ρ).ι P) ρ
        (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ) p :=
  TotalChowClass.res_glue (isClopenDecomposition_complexRankLoci hP) _ (ULift.up ρ)

/-- **Characterization of `P_p(ℰ^•)`**: along every `h : Y' ⟶ Y` locally of finite type along which
`h^*ℰ^•` has constant ranks `σ`, the restriction of `P_p(ℰ^•)` is `∑_n (-1)^n P_p(h^*ℰ^n)`. -/
theorem res_powerSumComplex_eq_powerSumComplexBounded {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (σ : ℤ →₀ ℕ)
    (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex h P).X n) (σ n)) (p : ℕ) :
    TotalChowClass.res h hs (powerSumComplex C sY hP p) =
      powerSumComplexBounded C sY' (pullbackComplex h P) σ hσ p := by
  have hU := isClopenDecomposition_complexRankLoci hP
  refine res_eq_of_res_piece_eq C hU h hs _ _ fun ρ m _ hfac hpm ↦ ?_
  rw [powerSumComplex, TotalChowClass.res_glue hU, res_powerSumComplexBounded,
    res_powerSumComplexBounded]
  exact powerSumComplexBounded_congr C _ _ (fun n ↦ pullbackPullbackIsoOfComp hfac.symm (P.X n))
    _ _ _ _ p

/-- **`P_p(ℰ^•)` of a bounded complex of constant ranks** is `∑_n (-1)^n P_p(ℰ^n)`. -/
theorem powerSumComplex_eq_powerSumComplexBounded (ρ : ℤ →₀ ℕ)
    (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n)
      (ρ n)) (p : ℕ) :
    powerSumComplex C sY hP p = powerSumComplexBounded C sY P ρ hρ p := by
  rw [← TotalChowClass.res_id (powerSumComplex C sY hP p),
    res_powerSumComplex_eq_powerSumComplexBounded C sY hP (𝟙 Y) (Category.id_comp sY) ρ
      (isFiniteLocallyFreeOfRank_pullbackComplex_X P (𝟙 Y) ρ hρ)]
  exact powerSumComplexBounded_congr C sY _ (fun n ↦ (Scheme.Modules.pullbackId Y).app (P.X n))
    _ _ _ _ p

/-- **Restriction of `P_p(ℰ^•)`**: `res_h P_p(ℰ^•) = P_p(h^*ℰ^•)` for every `h : Y' ⟶ Y` locally of
finite type. -/
theorem res_powerSumComplex {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']
    (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (p : ℕ) :
    TotalChowClass.res h hs (powerSumComplex C sY hP p) =
      powerSumComplex C sY'
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP) p := by
  set hP' := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h P hP
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP') fun ρ ↦ ?_
  have e : ∀ n, (pullbackComplex ((complexRankLoci hP' ρ).ι ≫ h) P).X n ≅
      (pullbackComplex (complexRankLoci hP' ρ).ι (pullbackComplex h P)).X n := fun n ↦
    ((Scheme.Modules.pullbackComp (complexRankLoci hP' ρ).ι h).app (P.X n)).symm
  have hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex ((complexRankLoci hP' ρ).ι ≫ h) P).X n) (ρ.down n) := fun n ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e n).symm
      (isFiniteLocallyFreeOfRank_complexRankLocus hP' ρ.down n)
  rw [TotalChowClass.res_res, res_powerSumComplex_eq_powerSumComplexBounded C sY hP _ _ ρ.down hσ,
    res_powerSumComplex_complexRankLocus C sY' hP' ρ.down]
  exact powerSumComplexBounded_congr C _ _ e _ _ _ _ p

/-- **`P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)` for a bounded complex whose terms have arbitrary ranks**:
if the terms vanish outside the degrees `lo, …, hi`, then `P_p(ℰ^•)` is the alternating sum over
`lo ≤ n ≤ hi` of the power sums of Stacks 0FA7 of the terms. -/
theorem powerSumComplex_eq_sum_Icc (lo hi : ℤ)
    (hz : ∀ n : ℤ, (n < lo ∨ hi < n) → IsZero (P.X n)) (p : ℕ) :
    powerSumComplex C sY hP p = ∑ n ∈ Finset.Icc lo hi, ((n.negOnePow : ℤ) •
      (@powerSumOfFiniteLocallyFree C _ sY _ (P.X n) (hP.1 n) p)) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  have hρ := isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down
  rw [res_powerSumComplex_complexRankLocus C sY hP ρ.down, map_sum]
  rcases isEmpty_or_nonempty (complexRankLoci hP ρ : Scheme.{u}) with hE | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · have hs : ∀ n ∉ Finset.Icc lo hi, ρ.down n = 0 := by
      intro n hn
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      have hzero : IsZero ((pullbackComplex (complexRankLoci hP ρ).ι P).X n) :=
        Functor.map_isZero _ (hz n hn)
      exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ (hρ n)
        (isFiniteLocallyFreeOfRank_zero_of_isZero hzero) y
    rw [powerSumComplexBounded_eq_sum C _ _ ρ.down hρ p (Finset.Icc lo hi) hs]
    refine Finset.sum_congr rfl fun n _ => ?_
    let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (complexRankLoci hP ρ).ι).obj (P.X n)) (ρ.down n) := hρ n
    rw [map_zsmul, res_powerSumOfFiniteLocallyFree_of_rank C sY (P.X n) _ rfl (ρ.down n)]
    rfl

/-- **Invariance of `P_p(ℰ^•)` under termwise isomorphism.** -/
theorem powerSumComplex_congr {P' : CochainComplex Y.Modules ℤ}
    (hP' : IsLocallyBoundedFiniteLocallyFree P') (e : ∀ n, P.X n ≅ P'.X n) (p : ℕ) :
    powerSumComplex C sY hP p = powerSumComplex C sY hP' p := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  have e' : ∀ n, (pullbackComplex (complexRankLoci hP ρ).ι P).X n ≅
      (pullbackComplex (complexRankLoci hP ρ).ι P').X n := fun n ↦
    (Scheme.Modules.pullback (complexRankLoci hP ρ).ι).mapIso (e n)
  have hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (complexRankLoci hP ρ).ι P').X n) (ρ.down n) := fun n ↦
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (e' n)
      (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down n)
  rw [res_powerSumComplex_complexRankLocus C sY hP ρ.down p,
    res_powerSumComplex_eq_powerSumComplexBounded C sY hP' _ _ ρ.down hσ p]
  exact powerSumComplexBounded_congr C _ _ e' _ _ _ _ p

/-- **The power sums of a complex with zero terms vanish.** -/
theorem powerSumComplex_of_isZero_X (h : ∀ n, IsZero (P.X n)) (p : ℕ) :
    powerSumComplex C sY hP p = 0 := by
  rw [powerSumComplex_eq_powerSumComplexBounded C sY hP 0
    (fun n => isFiniteLocallyFreeOfRank_zero_of_isZero (h n)) p]
  simp [powerSumComplexBounded]

/-- **`P_p(ℰ^•) ∈ A^p(X)`** of a locally bounded complex of finite locally free modules. -/
def powerSumComplexClass (p : ℕ) : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p :=
  powerSumComplex C sY hP p p

/-- **The Chern character** `ch_p(ℰ^•) = P_p(ℰ^•)/p! ∈ A^p(X) ⊗ 𝐐` of a locally bounded complex of
finite locally free modules. -/
def chernCharacterComplex (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sY p :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumComplexClass C sY hP p

end Complex

end Stacks.Chow

end
