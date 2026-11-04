module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ShortExactMultiplicativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.InvertibleSubSplitting

/-!
# The total Chern class is multiplicative in short exact sequences, in the weak standing situation

For a `Stacks.WeilCohomology.Weak.ChernSituation` — the standing situation of Stacks Section
45.12 in which the projective bundle formula, condition (4), is only asked to be injective and to
resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class — the total Chern class `c^A` of a
finite locally free module of constant rank depends only on its isomorphism class, and is
multiplicative in short exact sequences: `c^A(𝓕) = c^A(ℰ) c^A(𝒢)` for `0 ⟶ ℰ ⟶ 𝓕 ⟶ 𝒢 ⟶ 0`.

## Main results

* `Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_eq_of_iso`: isomorphic modules of
  constant rank have the same total Chern class.
* `Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_mul_of_shortExact`: the total Chern
  class is multiplicative in short exact sequences of finite locally free modules.
* `Stacks.WeilCohomology.Weak.ChernSituation.pull_chernSeries_coeff_of_iso`: compatibility of
  the total Chern class with pullback, read at any module isomorphic to the pullback.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔗 : ChernSituation.{u, v, v₁, w} C S)

/-- A finite locally free module of rank one on a scheme is invertible. -/
private theorem isInvertible_of_rank_one {Y : Scheme.{u}} (L : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L :=
  @Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one
    Y.toRingedSpace L h

/-- **The total Chern class of a module of rank one depends only on its Picard class**, so two
isomorphic such modules have the same one. -/
theorem chernSeries_eq_of_iso_rank_one (X : C) (L L' : (S.obj X).Modules)
    (h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1)
    (h1' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L' 1)
    (e : L ≅ L') : 𝔗.chernSeries X L 1 h1 = 𝔗.chernSeries X L' 1 h1' := by
  refine UnitalCentralSeries.ext fun n => ?_
  rw [𝔗.chernSeries_coeff_invertible X L (isInvertible_of_rank_one L h1) h1 n,
    𝔗.chernSeries_coeff_invertible X L' (isInvertible_of_rank_one L' h1') h1' n,
    picardClassOf_eq_of_iso (S.obj X) L L' _ _ e]

/-- **The total Chern class is multiplicative in a short exact sequence with invertible
sub-module.** For `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` with `ℒ` invertible, `c^A(ℰ) = c^A(ℒ) c^A(𝓕)`. -/
theorem chernSeries_mul_of_invertibleSub (X : C) (T : ShortComplex (S.obj X).Modules)
    (hT : T.ShortExact)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (m t : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ m)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ t)
    (h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ 1) :
    𝔗.chernSeries X T.X₂ m hE = 𝔗.chernSeries X T.X₁ 1 h1 * 𝔗.chernSeries X T.X₃ t hF := by
  revert hF
  cases t with
  | zero =>
      intro hF
      have : Epi T.f := (ShortComplex.exact_iff_epi T
        ((isZero_of_isFiniteLocallyFreeOfRank_zero T.X₃ hF).eq_zero_of_tgt _)).1 hT.exact
      have := hT.mono_f
      have := isIso_of_mono_of_epi T.f
      have e₁ : T.X₁ ≅ T.X₂ := asIso T.f
      have hE1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ 1 :=
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e₁ h1
      rw [𝔗.chernSeries_rank_zero X T.X₃ hF, mul_one,
        𝔗.chernSeries_eq_of_rank X T.X₂ m 1 hE hE1]
      exact 𝔗.chernSeries_eq_of_iso_rank_one X T.X₂ T.X₁ hE1 h1 e₁.symm
  | succ r =>
      intro hF
      rcases isEmpty_or_nonempty (S.obj X) with hX | hX
      · exact (UnitalCentralSeries.subsingleton (𝔗.subsingleton_of_isEmpty X hX)).elim _ _
      obtain ⟨x⟩ := hX
      have hE2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          T.X₂ (r + 1 + 1) := by
        have hm : m = 1 + (r + 1) := by
          have := h1
          have := hE
          have := hF
          exact AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact T hT 1 m (r + 1) x
        exact (show m = r + 1 + 1 by omega) ▸ hE
      obtain ⟨i, hi, hitw, hdiv⟩ := 𝔗.exists_divisorDatum X T hT hL r hF hE2
      have hmain := ChernSetup.chernClass_add_one_of_invertibleSub 𝔗.toChernSetup X T.X₂ T.X₃
        (picardClassOf (S.obj X) T.X₁ hL) r hE2 hF i hi hitw _
        (𝔗.c₁_divisorClass X T.X₁ hL T.X₂ (r + 1) hE2) hdiv
      have hcL : ∀ j : ℕ, (𝔗.chernSeries X T.X₁ 1 h1).coeff j =
          if j = 0 then 1 else
            if j = 1 then 𝔗.c₁ X (picardClassOf (S.obj X) T.X₁ hL) else 0 :=
        fun j => 𝔗.chernSeries_coeff_invertible X T.X₁ hL h1 j
      rw [𝔗.chernSeries_eq_of_rank X T.X₂ m (r + 1 + 1) hE hE2]
      refine UnitalCentralSeries.ext fun n => ?_
      rw [UnitalCentralSeries.coeff_mul]
      cases n with
      | zero =>
          rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hcL 0,
            UnitalCentralSeries.coeff_zero, UnitalCentralSeries.coeff_zero, if_pos rfl, one_mul]
      | succ k =>
          have hvanish : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal k, q ≠ (0, k) →
              (𝔗.chernSeries X T.X₁ 1 h1).coeff (q.1 + 1) *
                (𝔗.chernSeries X T.X₃ (r + 1) hF).coeff q.2 = 0 := by
            intro q hq hne
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
            have hq1 : q.1 ≠ 0 := fun h0 => hne (Prod.ext h0 (show q.2 = k by omega))
            rw [hcL (q.1 + 1), if_neg (Nat.succ_ne_zero _), if_neg (by omega), zero_mul]
          rw [Finset.Nat.sum_antidiagonal_succ, hcL 0, if_pos rfl, one_mul,
            Finset.sum_eq_single_of_mem (0, k)
              (Finset.HasAntidiagonal.mem_antidiagonal.2 (Nat.zero_add k)) hvanish,
            𝔗.chernSeries_coeff_succ X T.X₂ (r + 1) hE2 (k + 1), hmain k,
            𝔗.chernSeries_coeff_succ X T.X₃ r hF (k + 1),
            𝔗.chernSeries_coeff_succ X T.X₃ r hF k, hcL (0 + 1)]
          norm_num

/-- **The total Chern class is multiplicative in every short exact sequence of finite locally
free modules of constant rank whose sub-module has positive rank**:
`c^A(𝓕) = c^A(ℰ) c^A(𝒢)` for `0 ⟶ ℰ ⟶ 𝓕 ⟶ 𝒢 ⟶ 0` with `ℰ` of rank `a + 1`. -/
theorem chernSeries_mul_of_shortExact_succ (a : ℕ) : ∀ (X : C)
    (T : ShortComplex (S.obj X).Modules), T.ShortExact → ∀ (b c : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ (a + 1))
      (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ b)
      (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ c),
      𝔗.chernSeries X T.X₂ b hF =
        𝔗.chernSeries X T.X₁ (a + 1) hE * 𝔗.chernSeries X T.X₃ c hG := by
  induction a with
  | zero =>
      intro X T hT b c hE hF hG
      exact 𝔗.chernSeries_mul_of_invertibleSub X T hT (isInvertible_of_rank_one _ hE) b c hF hG hE
  | succ r ih =>
      intro X T hT b c hE hF hG
      obtain ⟨P, p, hinj, L, E', F', hL, hE', s, hF', iE, qE, wE, iF, qF, wF, fQ, gQ, wQ,
        hTE, hTF, hTQ⟩ :=
        𝔗.exists_splitInvertibleSub X T hT r b c hE hF hG
      have h1L : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 := by
        have := hL
        infer_instance
      have hpE := @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p)
        T.X₁ (r + 1 + 1) hE
      have hpF := @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) T.X₂ b hF
      have hpG := @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map p) T.X₃ c hG
      have hsplitE := 𝔗.chernSeries_mul_of_invertibleSub P (ShortComplex.mk iE qE wE) hTE hL
        (r + 1 + 1) (r + 1) hpE hE' h1L
      have hsplitF := 𝔗.chernSeries_mul_of_invertibleSub P (ShortComplex.mk iF qF wF) hTF hL
        b s hpF hF' h1L
      have hind := ih P (ShortComplex.mk fQ gQ wQ) hTQ s c hE' hF' hpG
      have hcomb : 𝔗.chernSeries P ((Scheme.Modules.pullback (S.map p)).obj T.X₂) b hpF =
          𝔗.chernSeries P ((Scheme.Modules.pullback (S.map p)).obj T.X₁) (r + 1 + 1) hpE *
            𝔗.chernSeries P ((Scheme.Modules.pullback (S.map p)).obj T.X₃) c hpG := by
        rw [hsplitF, hind, hsplitE, mul_assoc]
      refine UnitalCentralSeries.ext fun n => hinj ?_
      rw [𝔗.pull_chernSeries_coeff X P p T.X₂ b hF hpF n,
        UnitalCentralSeries.coeff_mul, map_sum, hcomb, UnitalCentralSeries.coeff_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, 𝔗.pull_chernSeries_coeff X P p T.X₁ (r + 1 + 1) hE hpE q.1,
        𝔗.pull_chernSeries_coeff X P p T.X₃ c hG hpG q.2]

/-- **The total Chern class of a module of constant rank depends only on its isomorphism
class.** -/
theorem chernSeries_eq_of_iso (X : C) (E E' : (S.obj X).Modules) (m m' : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' m')
    (e : E ≅ E') : 𝔗.chernSeries X E m hE = 𝔗.chernSeries X E' m' hE' := by
  have hE'' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' m :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e hE
  rw [𝔗.chernSeries_eq_of_rank X E' m' m hE' hE'']
  revert hE hE''
  cases m with
  | zero =>
      intro hE hE''
      rw [𝔗.chernSeries_rank_zero X E hE, 𝔗.chernSeries_rank_zero X E' hE'']
  | succ r =>
      intro hE hE''
      have hzero : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (0 : (S.obj X).Modules) 0 :=
        AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero (isZero_zero _)
      have hT : (ShortComplex.mk e.hom (0 : E' ⟶ (0 : (S.obj X).Modules)) (by simp)).ShortExact :=
        { exact := (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
          mono_f := inferInstance
          epi_g := inferInstance }
      rw [𝔗.chernSeries_mul_of_shortExact_succ r X _ hT (r + 1) 0 hE hE'' hzero,
        𝔗.chernSeries_rank_zero X _ hzero, mul_one]

/-- **The total Chern class is multiplicative in every short exact sequence of finite locally
free modules of constant rank**: `c^A(𝓕) = c^A(ℰ) c^A(𝒢)` for `0 ⟶ ℰ ⟶ 𝓕 ⟶ 𝒢 ⟶ 0`. -/
theorem chernSeries_mul_of_shortExact (a : ℕ) : ∀ (X : C)
    (T : ShortComplex (S.obj X).Modules), T.ShortExact → ∀ (b c : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ a)
      (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ b)
      (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ c),
      𝔗.chernSeries X T.X₂ b hF = 𝔗.chernSeries X T.X₁ a hE * 𝔗.chernSeries X T.X₃ c hG := by
  rcases a with _ | a'
  · intro X T hT b c hE hF hG
    have : Mono T.g := (ShortComplex.exact_iff_mono T
      ((isZero_of_isFiniteLocallyFreeOfRank_zero T.X₁ hE).eq_zero_of_src _)).1 hT.exact
    have := hT.epi_g
    have := isIso_of_mono_of_epi T.g
    rw [𝔗.chernSeries_rank_zero X T.X₁ hE, one_mul]
    exact 𝔗.chernSeries_eq_of_iso X T.X₂ T.X₃ b c hF hG (asIso T.g)
  · exact 𝔗.chernSeries_mul_of_shortExact_succ a'

/-- **Compatibility of the total Chern class with pullback, read at any module isomorphic to
`f^*ℰ`.** For `e : f^*ℰ ≅ ℰ'`, `f^* c^A_n(ℰ) = c^A_n(ℰ')`. -/
theorem pull_chernSeries_coeff_of_iso (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules)
    (E' : (S.obj X').Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' m)
    (e : (Scheme.Modules.pullback (S.map f)).obj E ≅ E') (n : ℕ) :
    𝔗.pull f ((𝔗.chernSeries X E m hE).coeff n) = (𝔗.chernSeries X' E' m hE').coeff n := by
  have hp : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) m :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map f) E m hE
  rw [𝔗.pull_chernSeries_coeff X X' f E m hE hp n,
    𝔗.chernSeries_eq_of_iso X' _ E' m m hp hE' e]

end ChernSituation

end Stacks.WeilCohomology.Weak

end
