module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituationAtPoint
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzZeroSchemeImprovementHypotheses
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationCore
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationStalkComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerConeDepth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.VarbaroConnectedness
public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth
public import StacksCore.Tactic.StacksAttribute

/-!
# Algebraization along a blowup with small fibres: Stacks 0EJK

In Situation [Stacks, Tag 0EHC] (a Noetherian ring `A`, ideals `I ⊆ 𝔞`, `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)`, `U = X ∖ Z`) let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Assume

1. `A` has a dualizing complex,
2. all fibres of the blowing up `b : X' → X` of `I` have dimension `≤ d - 1`,
3. either `(ℱₙ)` satisfies the `(d + 1, d + 2)`-inequalities of [Stacks, Tag 0EJ3], or
   `depth((ℱ^∧_y)_𝔭) + dim(𝒪^∧_{X,y}/𝔭) + δ^Y_Z(y) > d + 2` for all `y ∈ U ∩ Y` and primes
   `𝔭 ∉ V(I𝒪^∧_{X,y})`.

Then `(ℱₙ)` extends to `X`. This is [Stacks, Tag 0EJK]
(`Stacks.Algebraization.extendsToX_of_blowUp_fiber_dim_lt`).

## The proof

As in the source. On `U' = b⁻¹(U)` the pullback `(b|_{U'}^*ℱₙ)` satisfies conditions (a)–(e) of
[Stacks, Tag 0EJF] with `d = 1` and `T' = {δ^{Y'}_{Z'} ≤ 1} ⊆ T = {δ^{Y'}_{Z'} ≤ 2}`:
(a) and (e) are in `BlowupAlgebraizationCore.lean`; (b), (c), (d) follow, by the case analysis of
the source, from the inequalities (0EJL)/(0EJM)
(`Stacks.Algebraization.exists_depthAddDimAddDistance_le_blowup`) together with two facts about
dimension: a prime of `𝒪^∧_{X',y'}` meeting `V(I)` only at the closed point has `dim ≤ 1`
because `I𝒪_{X'}` is invertible, and a prime of `𝒪^∧_{X,y}` of `dim ≤ 1` off `V(I)` meets
`V(I)` only at the closed point. Then [Stacks, Tag 0EJF], the canonical extensions on the charts
([Stacks, Tag 0EJI]) and the passage to the completion of `A` with Grothendieck's existence
theorem (`Stacks.Algebraization.extendsToX_of_blowup_extension`) conclude.

## Implementation notes

The dimension bound on the fibres is written `dim < d` for the natural number `d.toNat`, as in
[Stacks, Tag 0EHU] (`Stacks.LocalCohomology.cohomologicalDimension_le_of_blowUp_fibre_dim_lt`):
for an integer `d`, `dim ≤ d - 1` says exactly this (for `d ≤ 0` both say the fibres are
empty). The blowup is `AlgebraicGeometry.blowUp` of the ideal sheaf `Ĩ` on `Spec(A)`. The
dualizing complex lives in the derived category `HasDerivedCategory.standard`, as in
[Stacks, Tag 0EJJ] (`Stacks.Algebraization.extendsToX_of_cd_one_of_satisfiesDepthInequalities`),
written out with `@` instead of a local instance.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

/-- Mapping to `R ⧸ p` is strictly monotone on the ideals containing `p`. -/
private theorem map_quotientMk_lt_map_quotientMk {R : Type u} [CommRing R] {p a b : Ideal R}
    (ha : p ≤ a) (hab : a < b) :
    a.map (Ideal.Quotient.mk p) < b.map (Ideal.Quotient.mk p) := by
  refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
  have h' := congrArg (Ideal.comap (Ideal.Quotient.mk p)) h
  rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.mpr ha, sup_eq_left.mpr (ha.trans hab.le)] at h'

/-- In a local ring, if `J ⊆ 𝔪`, `J ⊄ 𝔭` and `dim R/𝔭 ≤ 1`, the only prime containing `𝔭` and `J`
is `𝔪`. -/
theorem setOf_isPrime_le_le_eq_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (J p : Ideal R) [p.IsPrime] (hJ : ¬ J ≤ p) (hJm : J ≤ maximalIdeal R)
    (hdim : ringKrullDim (R ⧸ p) ≤ 1) :
    {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} = {maximalIdeal R} := by
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq, hpq, hJq⟩
    have hlt : p < q := lt_of_le_of_ne hpq (fun h => hJ (h ▸ hJq))
    by_contra hne
    have hqm : q < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hq.ne_top) hne
    have : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
      have hsurj := Ideal.Quotient.mk_surjective (I := p)
      let P : ∀ a : Ideal R, a.IsPrime → p ≤ a → PrimeSpectrum (R ⧸ p) := fun a ha hpa =>
        ⟨a.map (Ideal.Quotient.mk p), Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])⟩
      let s : LTSeries (PrimeSpectrum (R ⧸ p)) :=
        ⟨2, ![P p inferInstance le_rfl, P q hq hpq,
          P (maximalIdeal R) (maximalIdeal.isMaximal R).isPrime
            (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))], by
          intro i
          fin_cases i
          · exact map_quotientMk_lt_map_quotientMk le_rfl hlt
          · exact map_quotientMk_lt_map_quotientMk hpq hqm⟩
      exact_mod_cast Order.LTSeries.length_le_krullDim s
    exact absurd (this.trans hdim) (by decide)
  · rintro rfl
    exact ⟨(maximalIdeal.isMaximal R).isPrime, le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›), hJm⟩

/-- **A prime of dimension at most one off `V(I)` meets `V(I)` only at the closed point.** -/
theorem adicClosedFibreThrough_eq_of_ringKrullDim_le_one (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hdim : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) ≤ 1) :
    adicClosedFibreThrough (idealOnOpen S) y p = {completedMaximalIdeal (idealOnOpen S) y} := by
  have := isLocalRing_completedLocalRing S y z hyz
  rw [completedMaximalIdeal_eq_maximalIdeal S y z hyz]
  refine setOf_isPrime_le_le_eq_maximalIdeal _ p.asIdeal hp ?_ hdim
  rw [← completedMaximalIdeal_eq_maximalIdeal S y z hyz]
  exact Ideal.map_mono (stalk_idealOnOpen_le_maximalIdeal S y z hyz)

/-- `enatToEInt` sends a natural number `n` to `n` regarded as an integer. -/
theorem enatToEInt_natCast' (n : ℕ) : enatToEInt (n : ℕ∞) = ((n : ℤ) : EInt) := rfl

/-- `enatToEInt` is an order embedding: it preserves and reflects `≤`. -/
theorem enatToEInt_le_iff (x y : ℕ∞) : enatToEInt x ≤ enatToEInt y ↔ x ≤ y := by
  cases x using ENat.recTopCoe <;> cases y using ENat.recTopCoe
  · simp
  · refine ⟨fun h => absurd h (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))),
      fun h => absurd h (by simp)⟩
  · simp only [le_top, iff_true]
    exact le_top
  · rw [enatToEInt_natCast', enatToEInt_natCast', WithBotTop.coe_le_coe]
    norm_cast

/-- `enatToEInt` preserves and reflects `<`. -/
theorem enatToEInt_lt_iff (x y : ℕ∞) : enatToEInt x < enatToEInt y ↔ x < y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, enatToEInt_le_iff, enatToEInt_le_iff]

/-- The arithmetic of the proof of [Stacks, Tag 0EJK] after (0EJL)/(0EJM). -/
theorem blowup_depth_arith (a a' δ δ' : ℕ∞) (D D' e : ℕ)
    (hL : a + D + δ ≤ a' + D' + δ' + e) (hM : D' ≤ D) :
    ((e + 3 < a + D + δ ∨ e + 2 < a + δ ∨ (e + 2 ≤ a + δ ∧ 2 ≤ D)) → D' ≤ 1 → 3 ≤ a' + δ') ∧
      ((e + 3 < a + D + δ ∨ e + 2 ≤ a + δ) → 2 ≤ a' + δ' ∨ 3 < a' + D' + δ') := by
  cases a' using ENat.recTopCoe with
  | top => simp
  | coe n' =>
  cases δ' using ENat.recTopCoe with
  | top => simp
  | coe k' =>
  cases a using ENat.recTopCoe with
  | top =>
    exfalso
    have : (⊤ : ℕ∞) ≤ (n' : ℕ∞) + D' + k' + e := by simp at hL
    exact absurd this (by norm_cast)
  | coe n =>
  cases δ using ENat.recTopCoe with
  | top =>
    exfalso
    have : (⊤ : ℕ∞) ≤ (n' : ℕ∞) + D' + k' + e := by simp at hL
    exact absurd this (by norm_cast)
  | coe k =>
  norm_cast at hL ⊢
  omega

/-- **A prime of `𝒪_{U',y'}^∧` meeting `V(I)` only at the closed point has `dim ≤ 1`**: there
`I𝒪_{U'}` is principal, so this is Krull's principal ideal theorem. -/
theorem ringKrullDim_le_one_of_adicClosedFibreThrough_blowup (S : AlgebraizationSituation.{u})
    (y' : (situationBlowUpU S).toScheme)
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hfib : adicClosedFibreThrough (blowupIdealU S) y' p' =
      {completedMaximalIdeal (blowupIdealU S) y'}) :
    ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) ≤ 1 := by
  obtain ⟨W, hyW, s, hs⟩ := exists_affineOpen_blowupIdealU_eq_span_singleton S y'
  obtain ⟨a, ha⟩ := exists_completedLocalIdeal_eq_span_singleton (blowupIdealU S) y' W hyW hs
  have hfg : (IdealSheafData.stalk (blowupIdealU S) y').FG :=
    Ideal.fg_of_isNoetherianRing _
  have := AdicCompletion.isAdicComplete_self _ hfg
  have hjac : Ideal.span {a} ≤ Ideal.jacobson ⊥ := by
    rw [← ha]
    exact IsAdicComplete.le_jacobson_bot _
  have hmem : ∀ P : Ideal (completedLocalRing (blowupIdealU S) y'), P.IsPrime → p'.asIdeal ≤ P →
      a ∈ P → P = completedMaximalIdeal (blowupIdealU S) y' := by
    intro P hP hpP haP
    have : P ∈ adicClosedFibreThrough (blowupIdealU S) y' p' :=
      ⟨hP, hpP, by rw [ha, Ideal.span_le]; simpa using haP⟩
    rwa [hfib] at this
  obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal p'.asIdeal p'.isPrime.ne_top
  have hMm := hmem M hM.isPrime hpM
    (Ideal.mem_sInf.mp (hjac (Ideal.mem_span_singleton_self a)) ⟨bot_le, hM⟩)
  have : (completedMaximalIdeal (blowupIdealU S) y').IsMaximal := hMm ▸ hM
  exact ringKrullDim_quotient_le_one_of_le_jacobson hjac p'.asIdeal _ hmem

/-- If `k + l ≤ a + δ` in `ℕ∞` and `δ ≤ l`, then `k ≤ a`. -/
theorem le_of_add_le_add_bound {a δ : ℕ∞} {k l : ℕ} (h : ((k + l : ℕ) : ℕ∞) ≤ a + δ)
    (hδ : δ ≤ l) : (k : ℕ∞) ≤ a := by
  cases a using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
  cases δ using ENat.recTopCoe with
  | top => exact absurd hδ (by simp)
  | coe m =>
  norm_cast at h hδ ⊢
  omega

/-- If `k + l < a + D + δ` in `ℕ∞` and `δ ≤ l`, then `k < a + D`. -/
theorem lt_of_add_lt_add_bound {a D δ : ℕ∞} {k l : ℕ} (h : ((k + l : ℕ) : ℕ∞) < a + D + δ)
    (hδ : δ ≤ l) : (k : ℕ∞) < a + D := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe n =>
  cases D using ENat.recTopCoe with
  | top => simp
  | coe n' =>
  cases δ using ENat.recTopCoe with
  | top => exact absurd hδ (by simp)
  | coe m =>
  norm_cast at h hδ ⊢
  omega

variable (S : AlgebraizationSituation.{u})

/-- `depthAddDistance S F y z p` is the image under `enatToEInt` of the sum of the depth of the
completed stalk of `F` at `p` and `S.distanceToZ z`. -/
theorem depthAddDistance_eq_enatToEInt (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y : S.U.toScheme) (z : S.Y) (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)) :
    depthAddDistance S F y z p =
      enatToEInt (completedStalkDepth (idealOnOpen S) F y p + S.distanceToZ z) :=
  (Stacks.SectionPowerConeDepth.enatToEInt_add _ _).symm

/-- If the quotient of the completed local ring by `p` has Krull dimension `D`, then
`depthAddDimAddDistance S F y z p` is the image under `enatToEInt` of the sum of the depth of the
completed stalk of `F` at `p`, `D`, and `S.distanceToZ z`. -/
theorem depthAddDimAddDistance_eq_enatToEInt
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y : S.U.toScheme) (z : S.Y) (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    {D : ℕ} (hD : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) = D) :
    depthAddDimAddDistance S F y z p =
      enatToEInt (completedStalkDepth (idealOnOpen S) F y p + D + S.distanceToZ z) := by
  rw [Stacks.SectionPowerConeDepth.enatToEInt_add, Stacks.SectionPowerConeDepth.enatToEInt_add,
    depthAddDimAddDistance, hD]
  rfl

/-- **(0EJL)/(0EJM) in natural-number form.** -/
theorem exists_blowup_depth_bound
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y' : (situationBlowUpU S).toScheme) (e' : situationExceptional S)
    (he' : situationExceptionalι S e' = (situationBlowUpU S).ι y')
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hp' : ¬ completedLocalIdeal (blowupIdealU S) y' ≤ p'.asIdeal) :
    ∃ (y : S.U.toScheme) (z : S.Y) (_ : S.U.ι.base y = S.Yι.base z)
      (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)) (e D D' : ℕ),
      ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal ∧ d = e + 1 ∧
      ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) = D ∧
      ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) = D' ∧ D' ≤ D ∧
      completedStalkDepth (idealOnOpen S) F y p + D + S.distanceToZ z ≤
        completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' + D' +
          exceptionalDistance S e' + e := by
  obtain ⟨y, z, hyz, p, hp, hL, hM⟩ :=
    exists_depthAddDimAddDistance_le_blowup S hdual d hfib F y' e' he' p' hp'
  have hd := one_le_of_blowup_point S d hfib e'
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 1 := ⟨(d - 1).toNat, by omega⟩
  have := isLocalRing_completedLocalRing S y z hyz
  obtain ⟨D, hD⟩ := exists_ringKrullDim_quotient_eq_natCast p.asIdeal p.isPrime.ne_top
  have : Nontrivial (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p'.isPrime.ne_top
  have hbot : (0 : WithBot ℕ∞) ≤
      ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hD] at hM
  obtain ⟨D', hD'⟩ : ∃ D' : ℕ,
      ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal) = D' := by
    cases h : ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)
      using WithBot.recBotCoe with
    | bot => rw [h] at hbot; exact absurd hbot (by decide)
    | coe x =>
      cases x using ENat.recTopCoe with
      | top =>
        rw [h] at hM
        exact absurd hM (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)))
      | coe n => exact ⟨n, rfl⟩
  rw [hD'] at hM hL
  refine ⟨y, z, hyz, p, e, D, D', hp, rfl, hD, hD', ?_, ?_⟩
  · have : enatToEInt (D' : ℕ∞) ≤ enatToEInt (D : ℕ∞) := hM
    exact_mod_cast (enatToEInt_le_iff _ _).1 this
  · rw [depthAddDimAddDistance_eq_enatToEInt S F y z p hD] at hL
    have hR : enatToEInt (completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p') +
        krullDimToEInt ((D' : ℕ) : WithBot ℕ∞) + enatToEInt (exceptionalDistance S e') +
          (((e : ℤ) + 1 - 1 : ℤ) : EInt) =
        enatToEInt (completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' + D' +
          exceptionalDistance S e' + e) := by
      rw [Stacks.SectionPowerConeDepth.enatToEInt_add, Stacks.SectionPowerConeDepth.enatToEInt_add,
        Stacks.SectionPowerConeDepth.enatToEInt_add, add_sub_cancel_right]
      rfl
    rw [hR] at hL
    exact (enatToEInt_le_iff _ _).1 hL

/-- Hypothesis (3) of [Stacks, Tag 0EJK]. -/
abbrev BlowupDepthHypothesis (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (d : ℤ) :
    Prop :=
  SatisfiesDepthInequalities S F (d + 1) (d + 2) ∨
    ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
        ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
        depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt)

/-- **The input of (0EJM) in the source's case analysis**, from hypothesis (3). -/
theorem blowupDepthHypothesis_premises (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (e : ℕ) (h3 : BlowupDepthHypothesis S F ((e : ℤ) + 1))
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal) (D : ℕ)
    (hD : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) = D) :
    ((e + 3 : ℕ) < completedStalkDepth (idealOnOpen S) F y p + D + S.distanceToZ z ∨
      ((e + 2 : ℕ) : ℕ∞) < completedStalkDepth (idealOnOpen S) F y p + S.distanceToZ z ∨
      (((e + 2 : ℕ) : ℕ∞) ≤ completedStalkDepth (idealOnOpen S) F y p + S.distanceToZ z ∧
        2 ≤ D)) ∧
    ((e + 3 : ℕ) < completedStalkDepth (idealOnOpen S) F y p + D + S.distanceToZ z ∨
      ((e + 2 : ℕ) : ℕ∞) ≤ completedStalkDepth (idealOnOpen S) F y p + S.distanceToZ z) := by
  have hDAD := depthAddDimAddDistance_eq_enatToEInt S F y z p hD
  have hDA := depthAddDistance_eq_enatToEInt S F y z p
  have c2 : (((e : ℤ) + 1 + 2 : ℤ) : EInt) = enatToEInt ((e + 3 : ℕ) : ℕ∞) := by
    rw [enatToEInt_natCast', show ((e : ℤ) + 1 + 2) = ((e + 3 : ℕ) : ℤ) by push_cast; ring]
  have c1 : (((e : ℤ) + 1 + 1 : ℤ) : EInt) = enatToEInt ((e + 2 : ℕ) : ℕ∞) := by
    rw [enatToEInt_natCast', show ((e : ℤ) + 1 + 1) = ((e + 2 : ℕ) : ℤ) by push_cast; ring]
  rcases h3 with h3 | h3
  · obtain ⟨h1, h2⟩ := h3 y z hyz p hp
    by_cases hf : adicClosedFibreThrough (idealOnOpen S) y p =
        {completedMaximalIdeal (idealOnOpen S) y}
    · have := h2 hf
      rw [hDA, c1] at this
      have := (enatToEInt_lt_iff _ _).1 this
      exact ⟨Or.inr (Or.inl this), Or.inr this.le⟩
    · rcases h1 hf with h | h
      · rw [hDA, c1] at h
        have h := (enatToEInt_le_iff _ _).1 h
        refine ⟨Or.inr (Or.inr ⟨h, ?_⟩), Or.inr h⟩
        by_contra hlt
        exact hf (adicClosedFibreThrough_eq_of_ringKrullDim_le_one S y z hyz p hp
          (by rw [hD]; exact_mod_cast (show D ≤ 1 by omega)))
      · rw [hDAD, c2] at h
        have h := (enatToEInt_lt_iff _ _).1 h
        exact ⟨Or.inl h, Or.inl h⟩
  · have h := h3 y z hyz p hp
    rw [hDAD, c2] at h
    have h := (enatToEInt_lt_iff _ _).1 h
    exact ⟨Or.inl h, Or.inl h⟩

/-- A prime `p' ≠ 𝔪` of `𝒪_{U',y'}^∧` meeting `V(I)` only at the closed point lies off `V(I)`. -/
private theorem not_completedLocalIdeal_blowupIdealU_le_of_adicClosedFibreThrough_eq
    {y' : (situationBlowUpU S).toScheme}
    {p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y')}
    (hne : p'.asIdeal ≠ completedMaximalIdeal (blowupIdealU S) y')
    (hf : adicClosedFibreThrough (blowupIdealU S) y' p' =
      {completedMaximalIdeal (blowupIdealU S) y'}) :
    ¬ completedLocalIdeal (blowupIdealU S) y' ≤ p'.asIdeal := fun h => by
  have : p'.asIdeal ∈ adicClosedFibreThrough (blowupIdealU S) y' p' := ⟨p'.isPrime, le_rfl, h⟩
  rw [hf] at this
  exact hne this

/-- The common input to conditions (b) and (d) of [Stacks, Tag 0EJF] on the blowup: at a point
`y'` of the exceptional divisor and a prime `p' ≠ 𝔪` meeting `V(I)` only at the closed point,
depth plus distance is at least `3`. -/
private theorem three_le_completedStalkDepth_add_exceptionalDistance
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (d : ℤ)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (h3 : BlowupDepthHypothesis S F d)
    (y' : (situationBlowUpU S).toScheme) (e' : situationExceptional S)
    (he' : situationExceptionalι S e' = (situationBlowUpU S).ι y')
    (p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'))
    (hne : p'.asIdeal ≠ completedMaximalIdeal (blowupIdealU S) y')
    (hf : adicClosedFibreThrough (blowupIdealU S) y' p' =
      {completedMaximalIdeal (blowupIdealU S) y'}) :
    3 ≤ completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' +
      exceptionalDistance S e' := by
  obtain ⟨y, z, hyz, p, e, D, D', hp, rfl, hD, hD', hDD, hL⟩ :=
    exists_blowup_depth_bound S hdual d hfib F y' e' he' p'
      (not_completedLocalIdeal_blowupIdealU_le_of_adicClosedFibreThrough_eq S hne hf)
  have hD'1 : D' ≤ 1 := by
    have := ringKrullDim_le_one_of_adicClosedFibreThrough_blowup S y' p' hf
    rw [hD'] at this
    exact_mod_cast this
  exact (blowup_depth_arith _ _ _ _ D D' e hL hDD).1
    (blowupDepthHypothesis_premises S F e h3 y z hyz p hp D hD).1 hD'1

/-- **Stacks Project, Tag 0EJK.** In Situation [Stacks, Tag 0EHC] let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)`. Assume

1. `A` has a dualizing complex,
2. all fibres of the blowing up `b : X' → X` of `I` have dimension `≤ d - 1`, and
3. one of the following is true:
   (a) `(ℱₙ)` satisfies the `(d + 1, d + 2)`-inequalities ([Stacks, Tag 0EJ3]), or
   (b) for `y ∈ U ∩ Y` and a prime `𝔭 ⊆ 𝒪^∧_{X,y}` with `𝔭 ∉ V(I𝒪^∧_{X,y})` we have
   `depth((ℱ^∧_y)_𝔭) + dim(𝒪^∧_{X,y}/𝔭) + δ^Y_Z(y) > d + 2`.

Then `(ℱₙ)` extends to `X`.

Here `d` is an integer and the fibre condition `dim ≤ d - 1` is written `dim < d` for the natural
number `d.toNat`, which is the same condition (for `d ≤ 0` both say every fibre is empty). The
dualizing complex lives in the derived category `HasDerivedCategory.standard`, as in
[Stacks, Tag 0EJJ]. -/
@[stacks 0EJK "the whole statement: under (1) a dualizing complex, (2) fibres of the blowup of I \
of dimension ≤ d - 1, (3) the (d + 1, d + 2)-inequalities or the bound depth + dim + δ > d + 2, \
the object (ℱₙ) of Coh(U, I𝒪_U) extends to X"]
theorem extendsToX_of_blowUp_fiber_dim_lt (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (d : ℤ)
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} S.A) _ _
      (HasDerivedCategory.standard (ModuleCat.{u} S.A)),
      @Dualizing.IsDualizingComplex S.A _ _ (HasDerivedCategory.standard (ModuleCat.{u} S.A)) K)
    (hfib : ∀ y : Spec (CommRingCat.of S.A), topologicalKrullDim ((AlgebraicGeometry.blowUpToBase
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber y) < ((d.toNat : ℕ) : WithBot ℕ∞))
    (h3 : SatisfiesDepthInequalities S F (d + 1) (d + 2) ∨
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt)) :
    ExtendsToX S (toKerSystem S F) := by
  have hb : ∀ y' ∈ blowupT S 2, ∀ p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'),
      p'.asIdeal ≠ completedMaximalIdeal (blowupIdealU S) y' →
      adicClosedFibreThrough (blowupIdealU S) y' p' =
        {completedMaximalIdeal (blowupIdealU S) y'} →
      0 < completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' := by
    rintro y' ⟨e', he', hδ'⟩ p' hne hf
    have key := three_le_completedStalkDepth_add_exceptionalDistance S hdual d hfib F h3 y' e' he'
      p' hne hf
    have h1 : ((1 : ℕ) : ℕ∞) ≤ _ := le_of_add_le_add_bound (k := 1) (l := 2)
      (by exact_mod_cast key) (by exact_mod_cast hδ')
    exact Order.one_le_iff_pos.mp (by exact_mod_cast h1)
  have hd : ∀ y' ∈ blowupT S 1, ∀ p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'),
      p'.asIdeal ≠ completedMaximalIdeal (blowupIdealU S) y' →
      adicClosedFibreThrough (blowupIdealU S) y' p' =
        {completedMaximalIdeal (blowupIdealU S) y'} →
      1 < completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' := by
    rintro y' ⟨e', he', hδ'⟩ p' hne hf
    have key := three_le_completedStalkDepth_add_exceptionalDistance S hdual d hfib F h3 y' e' he'
      p' hne hf
    have h2 : ((2 : ℕ) : ℕ∞) ≤ _ := le_of_add_le_add_bound (k := 2) (l := 1)
      (by exact_mod_cast key) (by exact_mod_cast hδ')
    exact_mod_cast (ENat.coe_lt_coe.mpr (show (1 : ℕ) < 2 by norm_num)).trans_le h2
  have hc : ∀ y' ∈ blowupT S 1, ∀ p' : PrimeSpectrum (completedLocalRing (blowupIdealU S) y'),
      ¬ completedLocalIdeal (blowupIdealU S) y' ≤ p'.asIdeal →
      adicClosedFibreThrough (blowupIdealU S) y' p' ≠
        {completedMaximalIdeal (blowupIdealU S) y'} →
      1 ≤ completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p' ∨
        enatToEInt (completedStalkDepth (blowupIdealU S) (blowupPullbackSystem S F) y' p') +
            krullDimToEInt (ringKrullDim (completedLocalRing (blowupIdealU S) y' ⧸ p'.asIdeal)) >
          ((1 + ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
    rintro y' ⟨e', he', hδ'⟩ p' hp' -
    obtain ⟨y, z, hyz, p, e, D, D', hp, rfl, hD, hD', hDD, hL⟩ :=
      exists_blowup_depth_bound S hdual d hfib F y' e' he' p' hp'
    rcases (blowup_depth_arith _ _ _ _ D D' e hL hDD).2
      (blowupDepthHypothesis_premises S F e h3 y z hyz p hp D hD).2 with h | h
    · left
      have h1 : ((1 : ℕ) : ℕ∞) ≤ _ := le_of_add_le_add_bound (k := 1) (l := 1)
        (by exact_mod_cast h) (by exact_mod_cast hδ')
      exact_mod_cast h1
    · right
      have h2 : ((2 : ℕ) : ℕ∞) < _ := lt_of_add_lt_add_bound (k := 2) (l := 1)
        (by exact_mod_cast h) (by exact_mod_cast hδ')
      rw [hD']
      show enatToEInt ((2 : ℕ) : ℕ∞) < enatToEInt _ + enatToEInt ((D' : ℕ) : ℕ∞)
      rw [← Stacks.SectionPowerConeDepth.enatToEInt_add, enatToEInt_lt_iff]
      exact h2
  obtain ⟨G, σ, hσ⟩ := exists_blowup_extension_of_pullback S hdual F hb hc hd
  exact extendsToX_of_blowup_extension S F G σ hσ

end Stacks.Algebraization

end
