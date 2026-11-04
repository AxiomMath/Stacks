module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.StrongLiftingEnvelope

/-!
# The retract of a divided power envelope along a change of presentation

In Situation [Stacks, Tag 07MD] let `A → P' → C` be ring maps with `A → P'` smooth and
`P' → C` surjective with kernel `J'`, and let `q : P ↠ P'` be a surjection of `A`-algebras, so
that `A → P → C` is a second presentation of `C` with kernel `J = q^{-1}(J')`.  Write
`D = D_{P, γ}(J)` and `D' = D_{P', γ}(J')` for the divided power envelopes.

This module proves the *retract* of [Stacks, Tag 07L5] at every finite level of the `p`-adic
tower: the canonical map `ρ : D → D'` of [Stacks, Tag 07HB] is surjective, and for every `e`
at which the divided powers of `D` descend to `D ⧸ (p)^e` there is a homomorphism of divided
power `A`-algebras `θ_e : D' → D ⧸ (p)^e` splitting the reduction `ρ_e` of `ρ`, compatibly
along the tower.  That is `Crystalline.exists_compatible_levelRetract`.

The construction is the source's.  Smoothness of `P'/A` enters only through the strong lifting
property of [Stacks, Tag 07K4], `Algebra.HasStrongLiftingProperty`, and it is used twice:

* once at a single level `n₀` high enough for the divided powers to descend, to lift
  `P' → D' ⧸ (p)^{n₀}` through the surjection `ρ_{n₀}`, whose kernel is locally nilpotent
  because `ker ρ` lies in the divided power ideal of `D` and `p` is nilpotent in `D ⧸ (p)^{n₀}`;
* and then once at each higher level, along the surjection
  `D ⧸ (p)^{e+1} ↠ D ⧸ (p)^e ×_{D' ⧸ (p)^e} D' ⧸ (p)^{e+1}`, whose kernel is square zero.
  That is `Crystalline.exists_lift_succ`; the fibre product is realised as an equalizer
  subalgebra of the product, its surjectivity is the surjectivity of `ρ` on the powers of
  `(p)`, and the kernel squares to zero because `2e ≥ e + 1`.

Iterating gives a compatible system of `A`-algebra maps `β_e : P' → D ⧸ (p)^e` lifting
`P' → D' ⧸ (p)^e`; that is `Crystalline.exists_compatible_lifts`.  Each `β_e` carries `J'` into
the divided power ideal, so the universal property of `D'` turns it into a divided power
morphism `θ_e : D' → D ⧸ (p)^e`, and the same universal property — used for *uniqueness* —
gives both the compatibility of the `θ_e` and the splitting identity `ρ_e ∘ θ_e = id`.

## Main definitions

* `Crystalline.levelQuot`, `Crystalline.levelMap`, `Crystalline.levelTrans` — the `p`-adic
  tower `R ⧸ (p)^e` of a ring, the reduction of a map along it, and its transition maps.

## Main results

* `Crystalline.exists_lift_succ` — one step of the successive lifting, the step whose kernel is
  square zero.
* `Crystalline.exists_compatible_lifts` — the compatible system of lifts up the whole tower.
* `Crystalline.exists_envelopeHom_of_lift` (with `Crystalline.envelopeHom_ext`) — the universal
  property of a divided power envelope in the two shapes the proof uses: a map on the
  presentation extends to the envelope, and it does so uniquely.
* `Crystalline.exists_compatible_levelRetract` — **the retract of [Stacks, Tag 07L5] at the
  finite levels of the `p`-adic tower.**
* `Crystalline.exists_completionRetract` — the passage of such a system of level splittings to
  the `p`-adic completions, for arbitrary divided power rings.
* `Crystalline.exists_completedEnvelopeRetract` — **the retract of the first assertion of
  [Stacks, Tag 07L5] for an arbitrary surjection `q : P ↠ P'`**: the maps `a : D̂ → D̂'`,
  `b : D̂' → D̂` between the completions with `a ∘ b = id`, with `b` a map over `A` and with
  `I_D` the full preimage of `I_{D'}` under `ρ` — the two facts beyond the retract identity
  that make the round trip `b ∘ a` the endomorphism the proof of
  [Stacks, Lemma 60.21.4, Tag 07LH] factors.  That first assertion as the source phrases it,
  with the polynomial `P` chosen from the smoothness of `A → P'` and with `a` and `b`
  compatible with the maps `D̂ → C` and `D̂' → C`, is
  `Crystalline.exists_presentation_completedEnvelopeRetract`.

## The two assertions of [Stacks, Tag 07L5]

[Stacks, Tag 07L5] has two assertions.

The first is the retract: there are a presentation `A → P → C` and homomorphisms of divided
power `A`-algebras `a : D → D'`, `b : D' → D` between the `p`-adic *completions* with
`a ∘ b = id_{D'}`.  Its retract half is proved here, for an arbitrary surjection `q : P ↠ P'`,
in two steps; the choice of `P` and the compatibility of `a` and `b` with the maps `D → C` and
`D' → C` — the two remaining clauses of the source's assertion — are added by
`Crystalline.exists_presentation_completedEnvelopeRetract`, which puts the three together.
All of the retract's mathematics is at the finite levels of the tower, where `ρ` is the
uncompleted `a` and `θ_e` the uncompleted `b` at level `e`; that step is
`Crystalline.exists_compatible_levelRetract`.  The passage to the limit is
`Crystalline.exists_completionRetract`, which is formal:

1. `a : D̂ → D̂'` and `b : D̂' → D̂` are assembled from `ρ_e` and `θ_e` by the inverse-limit
   universal property `DividedPowers.IsDividedPowerCompletionLimit` of [Stacks, Tag 07KD]
   part (4), available through `DividedPowers.eventually_isDividedPowerCompletionLimit`;
   `θ_e` kills `(p)^e`, so it descends to `D' ⧸ (p)^e → D ⧸ (p)^e` — that is
   `Crystalline.levelDescend` — and composes with the evaluation `D̂' → D' ⧸ (p)^e` to give the
   required cone;
2. `a ∘ b = id_{D̂'}` comes from the *uniqueness* half of that same property applied to the cone
   of evaluations, using `ρ_e ∘ θ_e = id` above;
3. the bound of [Stacks, Tag 07KD] for `D`, the one for `D'`, and the level `N` from which the
   `θ_e` exist need not agree, so each cone is read off at the level `max N₀ e`, where `N₀` is
   the maximum of the three.

`Crystalline.exists_completedEnvelopeRetract` produces `a` and `b` existentially, pinning `a`
as the completion of `ρ` and `b` as the limit of the `θ_e`, rather than as the map carried by a
particular `Algebra` instance on a completed envelope.

The second assertion of [Stacks, Tag 07L5] — that `a` and `b` induce an equivalence between the
categories of pairs `(M, ∇)` satisfying [Stacks, Tag 07JB], [Stacks, Tag 07JC],
[Stacks, Tag 07JD] and [Stacks, Tag 07JE] over `D` and over `D'` — is proved, together with the
first, by `Crystalline.exists_presentation_retract_pairEquivalence`.  The direction `F ∘ G ≅ 𝟭`
is the collapse `Crystalline.CompletedConnection.retractComparisonEquiv`; the direction
`G ∘ F ≅ 𝟭` is the Taylor comparison `c_{id_D, b ∘ a}`, summed over the completion by
`Crystalline.completeTaylorSum` and shown bijective and horizontal — the step the source omits
— by `Crystalline.taylorRoundTripEquiv` and `Crystalline.coordOp_taylorRoundTrip`, from Taylor's
formula for the completed envelope (`Crystalline.envelopeCompletion_taylor_levels`).  The
categories and the functors are assembled in `Crystalline.retractPairEquivalence`.

## References

* [Stacks Project, Tag 07HB](https://stacks.math.columbia.edu/tag/07HB)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public section

universe u v

namespace Crystalline

open DividedPowers

section SuccessiveLifting

variable {A : Type u} [CommRing A] {R R' : Type u} [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R']

/-- The `e`-th level `R ⧸ (p)^e` of the `p`-adic tower of `R`. -/
public abbrev levelQuot (R : Type u) [CommRing R] (p e : ℕ) : Type u :=
  R ⧸ pAdicIdeal (A := R) p ^ e

/-- The powers of `(p)` are carried into one another by any ring map. -/
public theorem levelPAdicIdeal_pow_le_comap (f : R →+* R') (p e : ℕ) :
    pAdicIdeal (A := R) p ^ e ≤ (pAdicIdeal (A := R') p ^ e).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, pAdicIdeal, Ideal.map_span,
    Set.image_singleton, map_natCast]

/-- The powers of `(p)` are carried *onto* one another by a surjective ring map. -/
public theorem pAdicIdeal_pow_map (f : R →+* R') (p e : ℕ) :
    Ideal.map f (pAdicIdeal (A := R) p ^ e) = pAdicIdeal (A := R') p ^ e := by
  rw [Ideal.map_pow, pAdicIdeal, Ideal.map_span, Set.image_singleton, map_natCast]

/-- The reduction of an `A`-algebra map modulo `(p)^e`. -/
public noncomputable def levelMap (ρ : R →ₐ[A] R') (p e : ℕ) :
    levelQuot R p e →ₐ[A] levelQuot R' p e :=
  Ideal.quotientMapₐ _ ρ (levelPAdicIdeal_pow_le_comap ρ.toRingHom p e)

/-- The reduction of `ρ` modulo `(p)^e` sends the class of `x` to the class of `ρ x`. -/
@[simp]
public theorem levelMap_mk (ρ : R →ₐ[A] R') (p e : ℕ) (x : R) :
    levelMap ρ p e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ρ x) := rfl

/-- The transition map `R ⧸ (p)^e → R ⧸ (p)^m` of the `p`-adic tower, for `m ≤ e`. -/
public noncomputable def levelTrans (A : Type u) [CommRing A] (R : Type u) [CommRing R]
    [Algebra A R] (p : ℕ) {m e : ℕ} (h : m ≤ e) :
    levelQuot R p e →ₐ[A] levelQuot R p m :=
  Ideal.quotientMapₐ _ (AlgHom.id A R) (by
    simpa using Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) p) h)

/-- The transition map of the `p`-adic tower sends the class of `x` to the class of `x`. -/
@[simp]
public theorem levelTrans_mk (p : ℕ) {m e : ℕ} (h : m ≤ e) (x : R) :
    levelTrans A R p h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

/-- An element killed by a transition map of the `p`-adic tower is represented by an element
of the corresponding power of `(p)`. -/
public theorem exists_of_levelTrans_eq_zero (p : ℕ) {m e : ℕ} (h : m ≤ e)
    (x : levelQuot R p e) (hx : levelTrans A R p h x = 0) :
    ∃ a ∈ pAdicIdeal (A := R) p ^ m, Ideal.Quotient.mk _ a = x := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levelTrans_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact ⟨b, hx, rfl⟩

/-- The transition map of the `p`-adic tower is the canonical map between the quotients. -/
public theorem levelTrans_toRingHom (p : ℕ) {m e : ℕ} (h : m ≤ e) :
    ((levelTrans A R p h : levelQuot R p e →ₐ[A] levelQuot R p m) :
        levelQuot R p e →+* levelQuot R p m) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) p) h) := by
  ext x
  rfl

/-- Reduction modulo a power of `(p)` commutes with a ring map. -/
public theorem levelTrans_comp_levelMap (ρ : R →ₐ[A] R') (p : ℕ) {m e : ℕ} (h : m ≤ e) :
    (levelTrans A R' p h).comp (levelMap ρ p e) =
      (levelMap ρ p m).comp (levelTrans A R p h) := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- An element of `(p)^e` in the target of a surjective ring map is the image of an element of
`(p)^e`. -/
private theorem exists_mem_pAdicIdeal_pow_map_eq (f : R →+* R') (hf : Function.Surjective f)
    (p e : ℕ) {y : R'} (hy : y ∈ pAdicIdeal (A := R') p ^ e) :
    ∃ w ∈ pAdicIdeal (A := R) p ^ e, f w = y :=
  (Ideal.mem_map_iff_of_surjective f hf).mp (by rwa [pAdicIdeal_pow_map f p e])

/-- **One step of the successive lifting construction in the proof of [Stacks, Tag 07L5].**

Let `ρ : R → R'` be a surjection of `A`-algebras and let `S` be an `A`-algebra with the strong
lifting property.  Given a map `β_e : S → R ⧸ (p)^e` and a map `c : S → R' ⧸ (p)^(e+1)` which
agree in `R' ⧸ (p)^e`, with `e ≥ 1`, there is a map `β_{e+1} : S → R ⧸ (p)^(e+1)` reducing to
`β_e` and mapping to `c`.

This is the step the source writes as "`D_{e+i+1} → D_{e+i} ×_{D'_{e+i}} D'_{e+i+1}` is
surjective with square zero kernel"; the hypothesis `1 ≤ e` is what makes the kernel square
zero. -/
public theorem exists_lift_succ {S : Type u} [CommRing S] [Algebra A S]
    (hS : Algebra.HasStrongLiftingProperty A S) (ρ : R →ₐ[A] R')
    (hρ : Function.Surjective ρ) (p : ℕ) {e : ℕ} (he : 1 ≤ e)
    (βe : S →ₐ[A] levelQuot R p e) (c : S →ₐ[A] levelQuot R' p (e + 1))
    (hc : (levelTrans A R' p (Nat.le_succ e)).comp c = (levelMap ρ p e).comp βe) :
    ∃ β : S →ₐ[A] levelQuot R p (e + 1),
      (levelTrans A R p (Nat.le_succ e)).comp β = βe ∧
        (levelMap ρ p (e + 1)).comp β = c := by
  classical
  set π : levelQuot R p (e + 1) →ₐ[A] levelQuot R p e := levelTrans A R p (Nat.le_succ e)
    with hπ
  set r : levelQuot R p (e + 1) →ₐ[A] levelQuot R' p (e + 1) := levelMap ρ p (e + 1) with hr
  set π' : levelQuot R' p (e + 1) →ₐ[A] levelQuot R' p e :=
    levelTrans A R' p (Nat.le_succ e) with hπ'
  -- The fibre product `R ⧸ (p)^e ×_{R' ⧸ (p)^e} R' ⧸ (p)^(e+1)`.
  set F : Subalgebra A (levelQuot R p e × levelQuot R' p (e + 1)) :=
    AlgHom.equalizer ((levelMap ρ p e).comp (AlgHom.fst A _ _)) (π'.comp (AlgHom.snd A _ _))
    with hF
  have hmemF : ∀ x : levelQuot R p (e + 1), (π x, r x) ∈ F := by
    intro x
    show levelMap ρ p e (π x) = π' (r x)
    exact congrArg (fun g : levelQuot R p (e + 1) →ₐ[A] levelQuot R' p e => g x)
      (levelTrans_comp_levelMap (A := A) ρ p (Nat.le_succ e)).symm
  set φ : levelQuot R p (e + 1) →ₐ[A] F := (π.prod r).codRestrict F hmemF with hφ
  have hmemg : ∀ x : S, (βe x, c x) ∈ F := by
    intro x
    show levelMap ρ p e (βe x) = π' (c x)
    exact (congrArg (fun g : S →ₐ[A] levelQuot R' p e => g x) hc).symm
  set g : S →ₐ[A] F := (βe.prod c).codRestrict F hmemg with hg
  -- `φ` is surjective: this is the surjectivity of `R → R'` on the powers of `(p)`.
  have hφsurj : Function.Surjective φ := by
    rintro ⟨⟨u, v⟩, huv⟩
    change levelMap ρ p e u = π' v at huv
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective (I := pAdicIdeal (A := R) p ^ e) u
    have hdiff : π' (v - r (Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ (e + 1)) a₀)) = 0 := by
      rw [map_sub, sub_eq_zero, ← huv]
      rfl
    obtain ⟨w', hw'mem, hw'⟩ :=
      exists_of_levelTrans_eq_zero (A := A) p (Nat.le_succ e) _ hdiff
    obtain ⟨w, hwmem, hwρ⟩ := exists_mem_pAdicIdeal_pow_map_eq ρ.toRingHom hρ p e hw'mem
    have h1 : π (Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ (e + 1)) (a₀ + w)) =
        Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ e) a₀ := by
      show Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ e) (a₀ + w) = _
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hwmem, add_zero]
    have h2 : r (Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ (e + 1)) (a₀ + w)) = v := by
      show Ideal.Quotient.mk (pAdicIdeal (A := R') p ^ (e + 1)) (ρ (a₀ + w)) = v
      have hww : Ideal.Quotient.mk (pAdicIdeal (A := R') p ^ (e + 1)) (ρ w) =
          v - Ideal.Quotient.mk (pAdicIdeal (A := R') p ^ (e + 1)) (ρ a₀) := by
        rw [show ρ w = w' from hwρ]
        exact hw'
      rw [map_add, map_add, hww]
      ring
    exact ⟨Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ (e + 1)) (a₀ + w),
      Subtype.ext (Prod.ext h1 h2)⟩
  -- The kernel of `φ` is square zero, hence locally nilpotent.
  have hsq : RingHom.ker (φ : levelQuot R p (e + 1) →+* F) ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_bot_iff.mp (Ideal.mul_le.mpr fun x hx y hy => ?_)
    have hxπ : π x = 0 := congrArg Prod.fst (congrArg Subtype.val (RingHom.mem_ker.mp hx))
    have hyπ : π y = 0 := congrArg Prod.fst (congrArg Subtype.val (RingHom.mem_ker.mp hy))
    obtain ⟨a, ha, rfl⟩ := exists_of_levelTrans_eq_zero (A := A) p (Nat.le_succ e) x hxπ
    obtain ⟨b, hb, rfl⟩ := exists_of_levelTrans_eq_zero (A := A) p (Nat.le_succ e) y hyπ
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have hab : a * b ∈ pAdicIdeal (A := R) p ^ (e + e) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul ha hb
    exact Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) p) (by omega) hab
  obtain ⟨β, hβ⟩ := hS.exists_lift_of_surjective φ hφsurj
    (fun x hx => Ideal.Nilpotent.locallyNilpotent
      (I := RingHom.ker (φ : levelQuot R p (e + 1) →+* F)) ⟨2, hsq⟩ x hx) g
  exact ⟨β,
    AlgHom.ext fun x ↦ congrArg (fun z : F ↦ (z : levelQuot R p e × levelQuot R' p (e + 1)).1)
      (DFunLike.congr_fun hβ x),
    AlgHom.ext fun x ↦ congrArg (fun z : F ↦ (z : levelQuot R p e × levelQuot R' p (e + 1)).2)
      (DFunLike.congr_fun hβ x)⟩

/-- The transition maps of the `p`-adic tower compose. -/
public theorem levelTrans_comp_levelTrans (p : ℕ) {l m e : ℕ} (hlm : l ≤ m) (hme : m ≤ e) :
    (levelTrans A R p hlm).comp (levelTrans A R p hme) = levelTrans A R p (hlm.trans hme) := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The transition map of the `p`-adic tower from a level to itself is the identity. -/
public theorem levelTrans_self (p e : ℕ) (h : e ≤ e) :
    levelTrans A R p h = AlgHom.id A (levelQuot R p e) := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- **The compatible system of lifts in the proof of [Stacks, Tag 07L5].**

Let `ρ : R → R'` be a surjection of `A`-algebras, let `S` be an `A`-algebra with the strong
lifting property, and let `c : S → R'`.  If the reduction of `c` modulo `(p)^{n₀}` lifts
through `ρ` for one level `n₀ ≥ 1`, then it lifts through `ρ` at *every* level of the `p`-adic
tower, compatibly: there is a system of maps `β_e : S → R ⧸ (p)^e`, compatible with the
transition maps of the tower, with `ρ ∘ β_e` the reduction of `c`.

This is the source's successive application of the lifting property to the diagrams

    P' ──────────────→ D_{e+i} ×_{D'_{e+i}} D'_{e+i+1}
    ↑                   ↑
    A ───────────────→ D_{e+i+1}

The levels below `n₀` are obtained by composing down the tower, so the system is defined at
every level even though the lifting starts at `n₀`. -/
public theorem exists_compatible_lifts {S : Type u} [CommRing S] [Algebra A S]
    (hS : Algebra.HasStrongLiftingProperty A S) (ρ : R →ₐ[A] R')
    (hρ : Function.Surjective ρ) (p : ℕ) (c : S →ₐ[A] R') {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hbase : ∃ β : S →ₐ[A] levelQuot R p n₀,
      (levelMap ρ p n₀).comp β = (Ideal.Quotient.mkₐ A (pAdicIdeal (A := R') p ^ n₀)).comp c) :
    ∃ β : (e : ℕ) → (S →ₐ[A] levelQuot R p e),
      (∀ m e (h : m ≤ e), (levelTrans A R p h).comp (β e) = β m) ∧
        (∀ e, (levelMap ρ p e).comp (β e) =
          (Ideal.Quotient.mkₐ A (pAdicIdeal (A := R') p ^ e)).comp c) := by
  classical
  set redc : (e : ℕ) → S →ₐ[A] levelQuot R' p e :=
    fun e => (Ideal.Quotient.mkₐ A (pAdicIdeal (A := R') p ^ e)).comp c with hredc
  have hredcTrans : ∀ (m e : ℕ) (h : m ≤ e),
      (levelTrans A R' p h).comp (redc e) = redc m :=
    fun _ _ _ ↦ AlgHom.ext fun _ ↦ rfl
  let T : ℕ → Type u := fun e =>
    {f : S →ₐ[A] levelQuot R p e // (levelMap ρ p e).comp f = redc e}
  have hstep : ∀ (n : ℕ) (x : T (n₀ + n)), ∃ y : T (n₀ + n + 1),
      (levelTrans A R p (Nat.le_succ (n₀ + n))).comp y.1 = x.1 := by
    intro n x
    have hcompat : (levelTrans A R' p (Nat.le_succ (n₀ + n))).comp (redc (n₀ + n + 1)) =
        (levelMap ρ p (n₀ + n)).comp x.1 := by
      rw [x.2]
      exact hredcTrans (n₀ + n) (n₀ + n + 1) (Nat.le_succ (n₀ + n))
    obtain ⟨β, hβ1, hβ2⟩ :=
      exists_lift_succ hS ρ hρ p (by omega : 1 ≤ n₀ + n) x.1 (redc (n₀ + n + 1)) hcompat
    exact ⟨⟨β, hβ2⟩, hβ1⟩
  obtain ⟨β0, hβ0⟩ := hbase
  let G : (n : ℕ) → T (n₀ + n) := fun n =>
    Nat.rec (motive := fun n => T (n₀ + n)) ⟨β0, hβ0⟩
      (fun k ih => Classical.choose (hstep k ih)) n
  have hG : ∀ n : ℕ,
      (levelTrans A R p (Nat.le_succ (n₀ + n))).comp (G (n + 1)).1 = (G n).1 :=
    fun n => Classical.choose_spec (hstep n (G n))
  have key : ∀ (m e : ℕ) (h : m ≤ e),
      (levelTrans A R p (by omega : n₀ + m ≤ n₀ + e)).comp (G e).1 = (G m).1 := by
    intro m e h
    induction e, h using Nat.le_induction with
    | base => rw [levelTrans_self]; rfl
    | succ k hk ih =>
        rw [← ih, ← hG k, ← AlgHom.comp_assoc,
          levelTrans_comp_levelTrans (A := A) p
            (by omega : n₀ + m ≤ n₀ + k) (Nat.le_succ (n₀ + k))]
  refine ⟨fun e => (levelTrans A R p (Nat.le_add_left e n₀)).comp (G e).1, ?_, ?_⟩
  · intro m e h
    show (levelTrans A R p h).comp ((levelTrans A R p (Nat.le_add_left e n₀)).comp (G e).1) =
      (levelTrans A R p (Nat.le_add_left m n₀)).comp (G m).1
    rw [← AlgHom.comp_assoc, levelTrans_comp_levelTrans (A := A) p h (Nat.le_add_left e n₀),
      ← key m e h, ← AlgHom.comp_assoc,
      levelTrans_comp_levelTrans (A := A) p (Nat.le_add_left m n₀)
        (by omega : n₀ + m ≤ n₀ + e)]
  · intro e
    show (levelMap ρ p e).comp ((levelTrans A R p (Nat.le_add_left e n₀)).comp (G e).1) =
      (Ideal.Quotient.mkₐ A (pAdicIdeal (A := R') p ^ e)).comp c
    rw [← AlgHom.comp_assoc, ← levelTrans_comp_levelMap (A := A) ρ p (Nat.le_add_left e n₀),
      AlgHom.comp_assoc, (G e).2]
    exact hredcTrans e (n₀ + e) (Nat.le_add_left e n₀)

end SuccessiveLifting

section LevelKernel

variable {A : Type u} [CommRing A] {R R' : Type u} [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R']

/-- **A surjection whose kernel lies in `I` and which carries `I` onto `I'` has `I` for the full
preimage of `I'`.**  For the canonical map `ρ : D → D'` of [Stacks, Tag 07HB] between the divided
power envelopes of two presentations these three facts are the content of
`Crystalline.dividedPowerEnvelope_quotient`, and the conclusion is what makes the map
`D ⧸ I_D → D' ⧸ I_{D'}` induced by `ρ` — the identity of the augmentation target `C` —
injective. -/
private theorem mem_of_map_mem_of_ker_le {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (I : Ideal R) (I' : Ideal R') (hsurj : Function.Surjective f)
    (hmap : Ideal.map f I = I') (hker : RingHom.ker f ≤ I) {u : R} (hu : f u ∈ I') : u ∈ I := by
  obtain ⟨v, hv, hvu⟩ := (Ideal.mem_map_iff_of_surjective f hsurj).mp (hmap ▸ hu)
  have hmem : u - v ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_sub, hvu, sub_self]
  have hsplit : v + (u - v) = u := by ring
  exact hsplit ▸ Ideal.add_mem _ hv (hker hmem)

/-- The reduction of a surjection modulo `(p)^e` is surjective. -/
public theorem levelMap_surjective (ρ : R →ₐ[A] R') (hρ : Function.Surjective ρ) (p e : ℕ) :
    Function.Surjective (levelMap ρ p e) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := hρ b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The kernel of the reduction of a surjection `ρ : R → R'` modulo `(p)^e` is the image of any
ideal containing `ker ρ`.  This is what makes the kernel of `D_e → D'_e` locally nilpotent in
the proof of [Stacks, Tag 07L5]: `ker ρ` lies in the divided power ideal, whose image in `D_e`
is locally nilpotent because `p` is nilpotent there. -/
public theorem ker_levelMap_le (ρ : R →ₐ[A] R') (hρ : Function.Surjective ρ) (p e : ℕ)
    (I : Ideal R) (hkerI : RingHom.ker ρ.toRingHom ≤ I) :
    RingHom.ker ((levelMap ρ p e : levelQuot R p e →ₐ[A] levelQuot R' p e) :
        levelQuot R p e →+* levelQuot R' p e) ≤
      I.map (Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ e)) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx0 : Ideal.Quotient.mk (pAdicIdeal (A := R') p ^ e) (ρ a) = 0 := RingHom.mem_ker.mp hx
  obtain ⟨b, hb, hbρ⟩ := exists_mem_pAdicIdeal_pow_map_eq ρ.toRingHom hρ p e
    (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  have hab : a - b ∈ I := hkerI ((RingHom.sub_mem_ker_iff _).mpr hbρ.symm)
  have heq : Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ e) a =
      Ideal.Quotient.mk (pAdicIdeal (A := R) p ^ e) (a - b) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hb, sub_zero]
  rw [heq]
  exact Ideal.mem_map_of_mem _ hab

end LevelKernel

section EnvelopeUniversal

/-- **The map out of a divided power envelope determined by a map on the presentation.**  A
ring map `b : B → E` into a divided power ring which carries `J` into the divided power ideal
and restricts to a given divided power morphism on the base extends to a divided power
morphism out of the envelope of `J`. -/
public theorem exists_envelopeHom_of_lift {A : DividedPowerRing.{u}} {B : Type v} [CommRing B]
    {J : Ideal B} {g : A →+* B} {hJ : A.ideal.map g ≤ J} (D : DividedPowerEnvelope A g J hJ)
    (E : DividedPowerRing.{max u v})
    (aE : DividedPowers.DPMorphism A.dividedPowers E.dividedPowers)
    (b : B →+* E) (hb : b.comp g = aE.toRingHom) (hbJ : ∀ x ∈ J, b x ∈ E.ideal) :
    ∃ θ : DividedPowers.DPMorphism D.object.dividedPowers E.dividedPowers,
      θ.comp D.structureMap = aE ∧ θ.toRingHom.comp D.algebraMap.toRingHom = b := by
  classical
  let pr : IdealPair.Hom J E.ideal :=
    IdealPair.Hom.ofRingHom b (Ideal.map_le_iff_le_comap.mpr hbJ)
  have hpr : IdealPair.Hom.comp pr (IdealPair.Hom.ofRingHom g hJ) =
      IdealPair.Hom.ofDPMorphism aE :=
    IdealPair.Hom.ext_toRingHom _ _ hb
  let data := (D.homEquiv E aE).symm ⟨pr, hpr⟩
  refine ⟨data.1, data.2, ?_⟩
  have hh := D.homEquiv_apply E aE data
  have hval : (D.homEquiv E aE data).1 = pr :=
    congrArg Subtype.val ((D.homEquiv E aE).apply_symm_apply ⟨pr, hpr⟩)
  have hpair : pr = IdealPair.Hom.comp (IdealPair.Hom.ofDPMorphism data.1) D.algebraMap :=
    hval.symm.trans hh
  have hr := congrArg IdealPair.Hom.toRingHom hpair.symm
  change data.1.toRingHom.comp D.algebraMap.toRingHom = pr.toRingHom at hr
  simpa only [pr, IdealPair.Hom.ofRingHom] using hr

end EnvelopeUniversal

section LevelIdeals

variable (s : AffineCrystallineSituation.{u, v})
variable {P' : Type u} [CommRing P'] [Algebra s.A P']
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra s.A R] [Algebra s.A R']

/-- An element of `R ⧸ (p)^e` whose image in `R' ⧸ (p)^e` lies in the image of the divided
power ideal of `R'` already lies in the image of the divided power ideal of `R`, provided
`(p)^e` lies in the divided power ideal of `R'` and `ρ` is a surjection whose kernel lies in
the divided power ideal of `R`.

This is what makes the lifts `β_e` of the proof of [Stacks, Tag 07L5] carry `J'` into the
divided power ideal, so that the universal property of the envelope applies to them. -/
public theorem mem_map_of_levelMap_mem (ρ : R →ₐ[s.A] R') (hρ : Function.Surjective ρ)
    (I : Ideal R) (I' : Ideal R') (hmap : I.map ρ.toRingHom = I')
    (hker : RingHom.ker ρ.toRingHom ≤ I) (e : ℕ) (hcont : pAdicIdeal (A := R') s.p ^ e ≤ I')
    (x : levelQuot R s.p e)
    (hx : levelMap ρ s.p e x ∈ I'.map (Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e))) :
    x ∈ I.map (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz, hzeq⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e)) Ideal.Quotient.mk_surjective).mp hx
  have hsub : ρ a - z ∈ pAdicIdeal (A := R') s.p ^ e := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact hzeq.symm
  have hρa : ρ a ∈ I' := sub_add_cancel (ρ a) z ▸ Ideal.add_mem _ (hcont hsub) hz
  exact Ideal.mem_map_of_mem _
    (mem_of_map_mem_of_ker_le ρ.toRingHom I I' hρ hmap hker hρa)

end LevelIdeals

section LevelRetract

variable (s : AffineCrystallineSituation.{u, v})
variable {P P' : Type u} [CommRing P] [Algebra s.A P] [CommRing P'] [Algebra s.A P']

/-- **The retract of [Stacks, Tag 07L5] at every finite level of the `p`-adic tower.**

Let `A → P' → C` be a smooth presentation in the affine situation of [Stacks, Tag 07MD] and
let `q : P ↠ P'` be any surjection of `A`-algebras, so that `A → P → C` is a second
presentation.  Write `D = D_{P, γ}(J)` and `D' = D_{P', γ}(J')` for the two divided power
envelopes.

Then the canonical map `ρ : D → D'` of [Stacks, Tag 07HB] is surjective, the divided power
ideal `I_D` is the **full preimage** of `I_{D'}` under it, and for every level `e` at which the
divided powers of `D` descend to `D ⧸ (p)^e` there is a homomorphism of divided power
`A`-algebras `θ_e : D' → D ⧸ (p)^e` with

* `ρ_e ∘ θ_e = (D' → D' ⧸ (p)^e)`, so that `θ_e` splits the reduction of `ρ`,
* `θ_m = (transition) ∘ θ_e` for `m ≤ e`, so that the splittings are compatible along the
  tower, and
* `θ_e ∘ (A → D') = (A → D → D ⧸ (p)^e)`, so that `θ_e` is a map over `A`.

This is the whole of the construction of the retract `b : D' → D`, `a ∘ b = id_{D'}` in the
proof of [Stacks, Tag 07L5] carried out at the finite levels: the maps `a` and `b` of the
source are the limits of `ρ_e` and `θ_e` over the tower, and `a ∘ b = id` is the limit of the
first displayed identity.  That passage to the limit is `Crystalline.exists_completionRetract`,
and `Crystalline.exists_completedEnvelopeRetract` is the two steps together.

The last two facts are the ones the proof of [Stacks, Lemma 60.21.4, Tag 07LH] needs of the
endomorphism `b ∘ a` of `D̂`, through
`Crystalline.isAugmentationCompatible_comp_of_retract` and
`Crystalline.map_algebraMap_comp_of_retract`: the preimage property makes the map induced by `a`
on the augmentation targets injective, and the compatibility of `θ_e` with `A` is what makes `b`
a map over `A` in the limit. -/
public theorem exists_compatible_levelRetract (q : P →ₐ[s.A] P') (f' : P' →ₐ[s.A] s.C)
    [Algebra.Smooth (s.A : Type u) P']
    (hq : Function.Surjective q) (hf' : Function.Surjective f') :
    ∃ ρ : DividedPowers.DPMorphism
        (presentationEnvelope s (f'.comp q)).object.dividedPowers
        (presentationEnvelope s f').object.dividedPowers,
      ρ.comp (presentationEnvelope s (f'.comp q)).structureMap =
          (presentationEnvelope s f').structureMap ∧
        ρ.toRingHom.comp (presentationEnvelope s (f'.comp q)).algebraMap.toRingHom =
          (presentationEnvelope s f').algebraMap.toRingHom.comp q.toRingHom ∧
        Function.Surjective ρ ∧
        (∀ u : (presentationEnvelope s (f'.comp q)).object,
          ρ u ∈ (presentationEnvelope s f').object.ideal →
            u ∈ (presentationEnvelope s (f'.comp q)).object.ideal) ∧
        ∃ (N : ℕ) (hlev : ∀ e, N ≤ e →
            pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p ^ e ≤
                (presentationEnvelope s (f'.comp q)).object.ideal ∧
              (presentationEnvelope s (f'.comp q)).object.dividedPowers.IsSubDPIdeal
                (pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p ^ e)),
          ∃ θ : ∀ (e : ℕ) (he : N ≤ e), DividedPowers.DPMorphism
              (presentationEnvelope s f').object.dividedPowers
              (DividedPowers.quotientDividedPowers
                (presentationEnvelope s (f'.comp q)).object.ideal
                (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p e
                (hlev e he).1 (hlev e he).2),
            (∀ e (he : N ≤ e),
              (Ideal.quotientMap
                  (pAdicIdeal (A := (presentationEnvelope s f').object) s.p ^ e) ρ.toRingHom
                  (levelPAdicIdeal_pow_le_comap ρ.toRingHom s.p e)).comp (θ e he).toRingHom =
                Ideal.Quotient.mk
                  (pAdicIdeal (A := (presentationEnvelope s f').object) s.p ^ e)) ∧
              (∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
                (Ideal.Quotient.factor (Ideal.pow_le_pow_right
                    (I := pAdicIdeal
                      (A := (presentationEnvelope s (f'.comp q)).object) s.p) hme)).comp
                  (θ e he).toRingHom = (θ m hm).toRingHom) ∧
              ∀ (e : ℕ) (he : N ≤ e),
                (θ e he).toRingHom.comp (presentationEnvelope s f').structureMap.toRingHom =
                  (Ideal.Quotient.mk
                      (pAdicIdeal
                        (A := (presentationEnvelope s (f'.comp q)).object) s.p ^ e)).comp
                    (presentationEnvelope s (f'.comp q)).structureMap.toRingHom := by
  classical
  have hSLP : Algebra.HasStrongLiftingProperty (s.A : Type u) P' :=
    Algebra.HasStrongLiftingProperty.of_smooth _ _
  set f : P →ₐ[s.A] s.C := f'.comp q with hf
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := hf' y
    obtain ⟨w, rfl⟩ := hq z
    exact ⟨w, rfl⟩
  set env : DividedPowerEnvelope s.A (algebraMap s.A P) (presentationKernel s f) _ :=
    presentationEnvelope s f with henv
  set env' : DividedPowerEnvelope s.A (algebraMap s.A P') (presentationKernel s f') _ :=
    presentationEnvelope s f' with henv'
  set R : DividedPowerRing.{u} := env.object with hR
  set R' : DividedPowerRing.{u} := env'.object with hR'
  -- the functoriality map `ρ : R → R'` of [Stacks, Tag 07HB]
  obtain ⟨ρ, hρstruct, hρalgmap, hρsurj, hρmap, hρker, hρuniq⟩ :=
    dividedPowerEnvelope_quotient s.A (algebraMap s.A P) (algebraMap s.A P')
      q.toRingHom (by ext x; exact q.commutes x) hq (presentationKernel s f')
      (by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        show f' (algebraMap s.A P' x) = 0
        rw [f'.commutes]
        have hx' : algebraMap s.A s.C x ∈ s.A.ideal.map (algebraMap s.A s.C) :=
          Ideal.mem_map_of_mem _ hx
        rw [s.ideal_map_eq_bot] at hx'
        exact hx')
      env' env
  -- the kernel of `ρ` lies in the divided power ideal of `R`
  have hkerle : RingHom.ker ρ.toRingHom ≤ R.ideal := by
    rw [hρker]
    refine Ideal.span_le.mpr ?_
    rintro x ⟨n, hn, k, hk, rfl⟩
    have hkJ : k ∈ presentationKernel s f := by
      show f k = 0
      rw [hf]
      show f' (q k) = 0
      rw [show q k = 0 from hk]
      exact map_zero f'
    exact R.dividedPowers.dpow_mem (Nat.ne_of_gt hn)
      (env.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hkJ))
  -- the divided power ideal of `R` is the FULL preimage of that of `R'` under `ρ`
  have hρpre : ∀ u : (R : Type u), ρ u ∈ R'.ideal → u ∈ R.ideal :=
    fun u hu => mem_of_map_mem_of_ker_le ρ.toRingHom R.ideal R'.ideal hρsurj hρmap hkerle hu
  -- the `s.A`-algebra structures on the two envelopes, and `ρ` as an algebra map
  let : Algebra (s.A : Type u) (R : Type u) := env.structureMap.toRingHom.toAlgebra
  let : Algebra (s.A : Type u) (R' : Type u) := env'.structureMap.toRingHom.toAlgebra
  let ρalg : (R : Type u) →ₐ[(s.A : Type u)] (R' : Type u) :=
    { ρ.toRingHom with
      commutes' := fun a =>
        congrArg (fun g : s.A →+* R' => g a)
          (congrArg DividedPowers.DPMorphism.toRingHom hρstruct) }
  let c : P' →ₐ[(s.A : Type u)] (R' : Type u) :=
    { env'.algebraMap.toRingHom with
      commutes' := fun a => congrArg (fun g : s.A →+* R' => g a) env'.algebraMap_comp }
  -- the levels at which the divided powers descend
  let : Algebra (DividedPowers.IntegersAtPrime s.p) (R : Type u) :=
    (env.structureMap.toRingHom.comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  let : Algebra (DividedPowers.IntegersAtPrime s.p) (R' : Type u) :=
    (env'.structureMap.toRingHom.comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  have hpR : IsNilpotent (Ideal.Quotient.mk R.ideal (s.p : R)) :=
    presentationEnvelope_prime_nilpotent s f hfsurj
  have hpR' : IsNilpotent (Ideal.Quotient.mk R'.ideal (s.p : R')) :=
    presentationEnvelope_prime_nilpotent s f' hf'
  obtain ⟨N, hlevel, hlimit⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u}
      R.ideal R.dividedPowers s.p hpR
  obtain ⟨N', hlevel', hlimit'⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u}
      R'.ideal R'.dividedPowers s.p hpR'
  let n₀ : ℕ := max (max N N') 1
  have hNn₀ : N ≤ n₀ := le_trans (le_max_left N N') (le_max_left _ _)
  have hN'n₀ : N' ≤ n₀ := le_trans (le_max_right N N') (le_max_left _ _)
  have h1n₀ : 1 ≤ n₀ := le_max_right _ _
  let Q : ∀ e, N ≤ e → DividedPowerRing.{u} := fun e he =>
    ⟨levelQuot R s.p e, R.ideal.map (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)),
      DividedPowers.quotientDividedPowers R.ideal R.dividedPowers s.p e
        (hlevel e he).1 (hlevel e he).2⟩
  have hQp : ∀ (e : ℕ) (he : N ≤ e), IsNilpotent ((s.p : ((Q e he : DividedPowerRing) :
      Type u))) := by
    intro e he
    refine ⟨e, ?_⟩
    show ((s.p : ℕ) : levelQuot R s.p e) ^ e = 0
    rw [← map_natCast (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)) s.p, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) e
  have hnilQ : ∀ (e : ℕ) (he : N ≤ e), (Q e he).ideal.IsLocallyNilpotent :=
    fun e he => locallyNilpotent_dpIdeal s.prime.out (Q e he) (hQp e he)
  -- the compatible system of lifts `β_e : P' → R ⧸ (p)^e`
  have hρalgsurj : Function.Surjective ρalg := hρsurj
  have hbase : ∃ b : P' →ₐ[(s.A : Type u)] levelQuot R s.p n₀,
      (levelMap ρalg s.p n₀).comp b =
        (Ideal.Quotient.mkₐ (s.A : Type u) (pAdicIdeal (A := R') s.p ^ n₀)).comp c :=
    hSLP.exists_lift_of_surjective (levelMap ρalg s.p n₀)
      (levelMap_surjective ρalg hρalgsurj s.p n₀)
      (fun x hx => hnilQ n₀ hNn₀ x
        (ker_levelMap_le ρalg hρalgsurj s.p n₀ R.ideal hkerle hx))
      ((Ideal.Quotient.mkₐ (s.A : Type u) (pAdicIdeal (A := R') s.p ^ n₀)).comp c)
  obtain ⟨β, hβcompat, hβlift⟩ :=
    exists_compatible_lifts hSLP ρalg hρalgsurj s.p c h1n₀ hbase
  -- each `β_e` carries `J'` into the divided power ideal of `R ⧸ (p)^e`
  have hβJ : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e) (x : P'),
      x ∈ presentationKernel s f' → β e x ∈ (Q e he).ideal := by
    intro e he he' x hx
    refine mem_map_of_levelMap_mem s ρalg hρalgsurj R.ideal R'.ideal hρmap hkerle e
      (hlevel' e he').1 (β e x) ?_
    have hval : levelMap ρalg s.p e (β e x) =
        Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e) (c x) :=
      congrArg (fun g : P' →ₐ[(s.A : Type u)] levelQuot R' s.p e => g x) (hβlift e)
    rw [hval]
    exact Ideal.mem_map_of_mem _
      (env'.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hx))
  -- the levels of `R'`, and the quotient divided power morphisms
  let Q' : ∀ e, N' ≤ e → DividedPowerRing.{u} := fun e he =>
    ⟨levelQuot R' s.p e, R'.ideal.map (Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e)),
      DividedPowers.quotientDividedPowers R'.ideal R'.dividedPowers s.p e
        (hlevel' e he).1 (hlevel' e he).2⟩
  have hqDPraw : ∀ (e : ℕ) (he : N ≤ e),
      R.dividedPowers.IsDPMorphism (Q e he).dividedPowers
        (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)) := fun e he =>
    DividedPowers.Quotient.isDPMorphism R.dividedPowers
      (IsPAdicLevel.inf_isSubDPIdeal (I := R.ideal) (hlevel e he))
  have hqDPraw' : ∀ (e : ℕ) (he : N' ≤ e),
      R'.dividedPowers.IsDPMorphism (Q' e he).dividedPowers
        (Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e)) := fun e he =>
    DividedPowers.Quotient.isDPMorphism R'.dividedPowers
      (IsPAdicLevel.inf_isSubDPIdeal (I := R'.ideal) (hlevel' e he))
  let qDP : ∀ (e : ℕ) (he : N ≤ e),
      DividedPowers.DPMorphism R.dividedPowers (Q e he).dividedPowers :=
    fun e he => DividedPowers.DPMorphism.mk' (hqDPraw e he)
  let qDP' : ∀ (e : ℕ) (he : N' ≤ e),
      DividedPowers.DPMorphism R'.dividedPowers (Q' e he).dividedPowers :=
    fun e he => DividedPowers.DPMorphism.mk' (hqDPraw' e he)
  let aQ : ∀ (e : ℕ) (he : N ≤ e),
      DividedPowers.DPMorphism s.A.dividedPowers (Q e he).dividedPowers :=
    fun e he => (qDP e he).comp env.structureMap
  -- the reduction of `ρ` is a divided power morphism at every level
  have hρlevel : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      DividedPowers.IsDPMorphism (Q e he).dividedPowers (Q' e he').dividedPowers
        (levelMap ρalg s.p e).toRingHom := by
    intro e he he'
    refine DividedPowers.IsDPMorphism.of_comp R.dividedPowers (Q e he).dividedPowers
      (Q' e he').dividedPowers (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e))
      (levelMap ρalg s.p e).toRingHom rfl (hqDPraw e he) ?_
    have hcomp : (levelMap ρalg s.p e).toRingHom.comp
        (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)) =
        (Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e)).comp ρ.toRingHom := by
      ext x
      rfl
    rw [hcomp]
    exact DividedPowers.IsDPMorphism.comp (Q' e he').dividedPowers (hqDPraw' e he')
      ρ.isDPMorphism
  let ρlevel : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      DividedPowers.DPMorphism (Q e he).dividedPowers (Q' e he').dividedPowers :=
    fun e he he' => DividedPowers.DPMorphism.mk' (hρlevel e he he')
  -- the divided power morphisms `θ_e : R' → R ⧸ (p)^e` out of the envelope
  have hθex : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      ∃ θ : DividedPowers.DPMorphism R'.dividedPowers (Q e he).dividedPowers,
        θ.comp env'.structureMap = aQ e he ∧
          θ.toRingHom.comp env'.algebraMap.toRingHom = (β e).toRingHom := by
    intro e he he'
    refine exists_envelopeHom_of_lift env' (Q e he) (aQ e he) (β e).toRingHom ?_ ?_
    · ext r
      exact (β e).commutes r
    · intro x hx
      exact hβJ e he he' x hx
  let θ : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      DividedPowers.DPMorphism R'.dividedPowers (Q e he).dividedPowers :=
    fun e he he' => Classical.choose (hθex e he he')
  have hθstruct : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      (θ e he he').comp env'.structureMap = aQ e he :=
    fun e he he' => (Classical.choose_spec (hθex e he he')).1
  have hθalg : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      (θ e he he').toRingHom.comp env'.algebraMap.toRingHom = (β e).toRingHom :=
    fun e he he' => (Classical.choose_spec (hθex e he he')).2
  -- `θ_e` is a section of the reduction of `ρ`: this is `a ∘ b = id` at level `e`
  have hretract : ∀ (e : ℕ) (he : N ≤ e) (he' : N' ≤ e),
      (ρlevel e he he').comp (θ e he he') = qDP' e he' := by
    intro e he he'
    refine envelopeHom_ext env' (Q' e he') _ _ ?_ ?_
    · apply DividedPowers.DPMorphism.ext
      funext x
      have hθx : (θ e he he') (env'.structureMap x) = (aQ e he) x :=
        DFunLike.congr_fun (hθstruct e he he') x
      have hρx : ρ (env.structureMap x) = env'.structureMap x :=
        DFunLike.congr_fun hρstruct x
      show (levelMap ρalg s.p e) ((θ e he he') (env'.structureMap x)) =
        Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e) (env'.structureMap x)
      rw [hθx]
      show Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e) (ρ (env.structureMap x)) = _
      rw [hρx]
    · apply RingHom.ext
      intro x
      have hβx : (θ e he he') (env'.algebraMap.toRingHom x) = (β e) x :=
        DFunLike.congr_fun (hθalg e he he') x
      have h3 : (levelMap ρalg s.p e) ((β e) x) =
          Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e) (c x) :=
        DFunLike.congr_fun (hβlift e) x
      show (levelMap ρalg s.p e) ((θ e he he') (env'.algebraMap.toRingHom x)) =
        Ideal.Quotient.mk (pAdicIdeal (A := R') s.p ^ e) (env'.algebraMap.toRingHom x)
      rw [hβx, h3]
      rfl
  -- the transition maps of the tower of `R` are divided power morphisms
  have htraw : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      DividedPowers.IsDPMorphism (Q e he).dividedPowers (Q m hm).dividedPowers
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) s.p) hme)) := by
    intro m e hm he hme
    refine DividedPowers.IsDPMorphism.of_comp R.dividedPowers (Q e he).dividedPowers
      (Q m hm).dividedPowers (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) s.p) hme))
      rfl (hqDPraw e he) ?_
    have hcomp : (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) s.p) hme)).comp
        (Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ e)) =
        Ideal.Quotient.mk (pAdicIdeal (A := R) s.p ^ m) := by
      ext x
      rfl
    rw [hcomp]
    exact hqDPraw m hm
  let tDP : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      DividedPowers.DPMorphism (Q e he).dividedPowers (Q m hm).dividedPowers :=
    fun m e hm he hme => DividedPowers.DPMorphism.mk' (htraw m e hm he hme)
  -- the system `θ_e` is compatible with the transition maps
  have hθcompat : ∀ (m e : ℕ) (hm : N ≤ m) (hm' : N' ≤ m) (he : N ≤ e) (he' : N' ≤ e)
      (hme : m ≤ e), (tDP m e hm he hme).comp (θ e he he') = θ m hm hm' := by
    intro m e hm hm' he he' hme
    refine envelopeHom_ext env' (Q m hm) _ _ ?_ ?_
    · apply DividedPowers.DPMorphism.ext
      funext x
      have h1 : (θ e he he') (env'.structureMap x) = (aQ e he) x :=
        DFunLike.congr_fun (hθstruct e he he') x
      have h2 : (θ m hm hm') (env'.structureMap x) = (aQ m hm) x :=
        DFunLike.congr_fun (hθstruct m hm hm') x
      show Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) s.p) hme)
          ((θ e he he') (env'.structureMap x)) = (θ m hm hm') (env'.structureMap x)
      rw [h1, h2]
      rfl
    · apply RingHom.ext
      intro x
      have h1 : (θ e he he') (env'.algebraMap.toRingHom x) = (β e) x :=
        DFunLike.congr_fun (hθalg e he he') x
      have h2 : (θ m hm hm') (env'.algebraMap.toRingHom x) = (β m) x :=
        DFunLike.congr_fun (hθalg m hm hm') x
      have h3 : (levelTrans (s.A : Type u) (R : Type u) s.p hme) ((β e) x) = (β m) x :=
        DFunLike.congr_fun (hβcompat m e hme) x
      have h4 := DFunLike.congr_fun
        (levelTrans_toRingHom (A := (s.A : Type u)) (R := (R : Type u)) s.p hme) ((β e) x)
      show Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := pAdicIdeal (A := R) s.p) hme)
          ((θ e he he') (env'.algebraMap.toRingHom x)) =
        (θ m hm hm') (env'.algebraMap.toRingHom x)
      rw [h1, h2, ← h3, ← h4]
      rfl
  refine ⟨ρ, hρstruct, hρalgmap, hρsurj, hρpre, n₀,
    fun e he => hlevel e (hNn₀.trans he),
    fun e he => θ e (hNn₀.trans he) (hN'n₀.trans he), fun e he => ?_,
    fun m e hm he hme => ?_, fun e he => ?_⟩
  · exact congrArg DividedPowers.DPMorphism.toRingHom
      (hretract e (hNn₀.trans he) (hN'n₀.trans he))
  · exact congrArg DividedPowers.DPMorphism.toRingHom
      (hθcompat m e (hNn₀.trans hm) (hN'n₀.trans hm) (hNn₀.trans he) (hN'n₀.trans he) hme)
  · exact congrArg DividedPowers.DPMorphism.toRingHom
      (hθstruct e (hNn₀.trans he) (hN'n₀.trans he))

end LevelRetract

section CompletionPassage

variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
  {A' : Type u} [CommRing A'] {I' : Ideal A'} (γ' : DividedPowers I')
  (p : ℕ)

/-- The reduction `A ⧸ (p)^k → A' ⧸ (p)^e` of a divided power morphism `(A, I, γ) → (A', I', γ')`
along two finite levels with `e ≤ k` is again a divided power morphism.  Both quotient divided
power structures are induced from above, so this reduces along the surjection `A ↠ A ⧸ (p)^k`
to the composite `A → A' → A' ⧸ (p)^e`. -/
private theorem isDPMorphism_levelQuotientMap (ρ : γ.DPMorphism γ') {k e : ℕ}
    (hle : pAdicIdeal (A := A) p ^ k ≤ (pAdicIdeal (A := A') p ^ e).comap ρ.toRingHom)
    (h1 : pAdicIdeal (A := A) p ^ k ≤ I)
    (h2 : γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ k))
    (k1 : pAdicIdeal (A := A') p ^ e ≤ I')
    (k2 : γ'.IsSubDPIdeal (pAdicIdeal (A := A') p ^ e)) :
    DividedPowers.IsDPMorphism (quotientDividedPowers I γ p k h1 h2)
      (quotientDividedPowers I' γ' p e k1 k2)
      (Ideal.quotientMap (pAdicIdeal (A := A') p ^ e) ρ.toRingHom hle) := by
  refine DividedPowers.IsDPMorphism.of_comp γ _ _
    (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ k)) _ rfl
    (pAdicLevelProj I γ p (⟨h1, h2⟩ : IsPAdicLevel I γ p k)).isDPMorphism ?_
  have hcomp : (Ideal.quotientMap (pAdicIdeal (A := A') p ^ e) ρ.toRingHom hle).comp
      (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ k)) =
      (Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e)).comp ρ.toRingHom := by
    ext x
    rfl
  rw [hcomp]
  exact DividedPowers.IsDPMorphism.comp _
    (pAdicLevelProj I' γ' p (⟨k1, k2⟩ : IsPAdicLevel I' γ' p e)).isDPMorphism ρ.isDPMorphism

/-- **A ring map `A' → A ⧸ (p)^e` kills `(p)^e`, so it descends to `A' ⧸ (p)^e`.**  This is what
turns the level retract `θ_e : D' → D ⧸ (p)^e` of [Stacks, Tag 07L5] into a map out of the
level-`e` quotient of `D'`, which is what the evaluation of the `p`-adic completion lands in. -/
private noncomputable def levelDescend (e : ℕ) (t : A' →+* A ⧸ pAdicIdeal (A := A) p ^ e) :
    A' ⧸ pAdicIdeal (A := A') p ^ e →+* A ⧸ pAdicIdeal (A := A) p ^ e :=
  Ideal.Quotient.lift _ t (by
    intro a ha
    have hmem : t a ∈ Ideal.map t (pAdicIdeal (A := A') p ^ e) := Ideal.mem_map_of_mem _ ha
    rw [pAdicIdeal_pow_map t p e] at hmem
    have hbot : pAdicIdeal (A := A ⧸ pAdicIdeal (A := A) p ^ e) p ^ e = ⊥ := by
      rw [← pAdicIdeal_pow_map (Ideal.Quotient.mk (pAdicIdeal (A := A) p ^ e)) p e]
      exact Ideal.map_quotient_self _
    rw [hbot] at hmem
    simpa using hmem)

@[simp]
private theorem levelDescend_mk (e : ℕ) (t : A' →+* A ⧸ pAdicIdeal (A := A) p ^ e) (y : A') :
    levelDescend p e t (Ideal.Quotient.mk _ y) = t y := rfl

/-- The descent of a divided power morphism `A' → A ⧸ (p)^e` to `A' ⧸ (p)^e` is again a divided
power morphism, the quotient map `A' ↠ A' ⧸ (p)^e` being a surjective divided power morphism
onto the divided power ideal of the quotient. -/
private theorem isDPMorphism_levelDescend (e : ℕ)
    (t : A' →+* A ⧸ pAdicIdeal (A := A) p ^ e)
    (h1 : pAdicIdeal (A := A) p ^ e ≤ I)
    (h2 : γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e))
    (k1 : pAdicIdeal (A := A') p ^ e ≤ I')
    (k2 : γ'.IsSubDPIdeal (pAdicIdeal (A := A') p ^ e))
    (ht : γ'.IsDPMorphism (quotientDividedPowers I γ p e h1 h2) t) :
    DividedPowers.IsDPMorphism (quotientDividedPowers I' γ' p e k1 k2)
      (quotientDividedPowers I γ p e h1 h2) (levelDescend p e t) := by
  refine DividedPowers.IsDPMorphism.of_comp γ' _ _
    (Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e)) _ rfl
    (pAdicLevelProj I' γ' p (⟨k1, k2⟩ : IsPAdicLevel I' γ' p e)).isDPMorphism ?_
  have hcomp : (levelDescend p e t).comp
      (Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e)) = t := by
    ext x
    rfl
  rw [hcomp]
  exact ht

/-- Two elements of a `p`-adic completion whose evaluations agree at every level are equal. -/
private theorem adicCompletion_ext_evalₐ {R : Type u} [CommRing R] (J : Ideal R)
    {x y : AdicCompletion J R}
    (h : ∀ n, AdicCompletion.evalₐ J n x = AdicCompletion.evalₐ J n y) : x = y := by
  refine AdicCompletion.ext fun n ↦ ?_
  have hEq : (J ^ n • (⊤ : Submodule R R) : Ideal R) = J ^ n := by
    ext z
    simp
  have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq hEq)) := by
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
      Ideal.map_mk_eq_bot_of_le (le_of_eq hEq.symm)
  refine hinj ?_
  show (Ideal.Quotient.factor (le_of_eq hEq)) (AdicCompletion.eval J R n x) =
    (Ideal.Quotient.factor (le_of_eq hEq)) (AdicCompletion.eval J R n y)
  simpa [← AdicCompletion.factor_eval_eq_evalₐ] using h n

/-- Two elements of a `p`-adic completion whose evaluations agree at every level from some `N` on
are equal. -/
private theorem adicCompletion_ext_evalₐ_of_le {R : Type u} [CommRing R] (J : Ideal R)
    {x y : AdicCompletion J R} (N : ℕ)
    (h : ∀ e, N ≤ e → AdicCompletion.evalₐ J e x = AdicCompletion.evalₐ J e y) : x = y :=
  adicCompletion_ext_evalₐ J fun n ↦ by
    rw [← AdicCompletion.factorPow_evalₐ J (le_max_right N n) x,
      ← AdicCompletion.factorPow_evalₐ J (le_max_right N n) y, h _ (le_max_left _ _)]

/-- **The passage of a level retract to the `p`-adic completions.**

Let `(A, I, γ)` and `(A', I', γ')` be divided power rings over `ℤ_(p)` in which `p` is nilpotent
modulo the divided power ideal, let `ρ : A → A'` be a morphism of divided power rings, and
suppose that from some level `N` on the reduction of `ρ` modulo `(p)^e` is split by a morphism
of divided power rings `θ_e : A' → A ⧸ (p)^e`, compatibly along the tower.  Then there are
morphisms of divided power rings `a : Â → Â'` and `b : Â' → Â` between the `p`-adic completions
with `a ∘ b = id`, where `a` is the completion of `ρ` and `b` reduces to `θ_e` at every level
`e ≥ N`.

This is the formal part of the proof of [Stacks, Lemma 60.17.5, Tag 07L5]: all of the mathematics
is in the construction of the `θ_e`, which for the divided power envelopes of two presentations
is `Crystalline.exists_compatible_levelRetract`.  Both `a` and `b` are produced by the
inverse-limit universal property `DividedPowers.IsDividedPowerCompletionLimit` of
[Stacks, Tag 07KD] part (4), available through
`DividedPowers.eventually_isDividedPowerCompletionLimit`: for `a` the cone is the reduction of
`ρ`, for `b` it is `θ_e` descended to `A' ⧸ (p)^e` and precomposed with the evaluation of `Â'`.
The identity `a ∘ b = id` is the *uniqueness* half of that property for `Â'`, both `a ∘ b` and
the identity inducing the evaluations.

The level at which [Stacks, Tag 07KD] applies to `A`, the level at which it applies to `A'`, and
`N` need not agree, so the two cones are re-indexed by composing down the tower: at level `e`
each is read off at the level `max (max (max N N_A) N_B) e`. -/
public theorem exists_completionRetract [Fact p.Prime]
    [Algebra (IntegersAtPrime p) A] [Algebra (IntegersAtPrime p) A']
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))
    (hp' : IsNilpotent (Ideal.Quotient.mk I' (p : A')))
    (ρ : γ.DPMorphism γ') (N : ℕ)
    (hlev : ∀ e, N ≤ e →
      pAdicIdeal (A := A) p ^ e ≤ I ∧ γ.IsSubDPIdeal (pAdicIdeal (A := A) p ^ e))
    (θ : ∀ (e : ℕ) (he : N ≤ e),
      γ'.DPMorphism (quotientDividedPowers I γ p e (hlev e he).1 (hlev e he).2))
    (hsplit : ∀ (e : ℕ) (he : N ≤ e),
      (Ideal.quotientMap (pAdicIdeal (A := A') p ^ e) ρ.toRingHom
          (levelPAdicIdeal_pow_le_comap ρ.toRingHom p e)).comp (θ e he).toRingHom =
        Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e))
    (hcompat : ∀ (m e : ℕ) (hm : N ≤ m) (he : N ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := pAdicIdeal (A := A) p) hme)).comp
          (θ e he).toRingHom = (θ m hm).toRingHom) :
    ∃ (a : (completedDividedPowers I γ p hp).1.DPMorphism
        (completedDividedPowers I' γ' p hp').1)
      (b : (completedDividedPowers I' γ' p hp').1.DPMorphism
        (completedDividedPowers I γ p hp).1),
      a.comp b = DividedPowers.DPMorphism.id _ ∧
      (∀ x : A, a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x) =
        algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') (ρ.toRingHom x)) ∧
      ∀ (e : ℕ) (he : N ≤ e) (y : A'),
        AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e
            (b.toRingHom (algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') y)) =
          (θ e he).toRingHom y := by
  classical
  obtain ⟨NA, hlevA, hlimA⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u} I γ p hp
  obtain ⟨NB, hlevB, hlimB⟩ :=
    DividedPowers.eventually_isDividedPowerCompletionLimit.{u, u} I' γ' p hp'
  change (∀ e (he : NA ≤ e), (completedDividedPowers I γ p hp).1.IsDPMorphism
      (quotientDividedPowers I γ p e (hlevA e he).1 (hlevA e he).2)
      (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e).toRingHom) ∧ _ at hlimA
  change (∀ e (he : NB ≤ e), (completedDividedPowers I' γ' p hp').1.IsDPMorphism
      (quotientDividedPowers I' γ' p e (hlevB e he).1 (hlevB e he).2)
      (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e).toRingHom) ∧ _ at hlimB
  set N₀ : ℕ := max (max N NA) NB with hN₀def
  set k : ℕ → ℕ := fun e => max N₀ e with hkdef
  have hN₀N : N ≤ N₀ := le_trans (le_max_left N NA) (le_max_left _ NB)
  have hN₀A : NA ≤ N₀ := le_trans (le_max_right N NA) (le_max_left _ NB)
  have hN₀B : NB ≤ N₀ := le_max_right _ NB
  have hkN : ∀ e, N ≤ k e := fun e => hN₀N.trans (le_max_left N₀ e)
  have hkNA : ∀ e, NA ≤ k e := fun e => hN₀A.trans (le_max_left N₀ e)
  have hkNB : ∀ e, NB ≤ k e := fun e => hN₀B.trans (le_max_left N₀ e)
  have hek : ∀ e, e ≤ k e := fun e => le_max_right N₀ e
  have hkmono : ∀ {m e : ℕ}, m ≤ e → k m ≤ k e := fun hme => max_le_max le_rfl hme
  -- the cone `Â → A' ⧸ (p)^e` whose limit is `a`
  have hleρ : ∀ e : ℕ, pAdicIdeal (A := A) p ^ k e ≤
      (pAdicIdeal (A := A') p ^ e).comap ρ.toRingHom := fun e =>
    le_trans (Ideal.pow_le_pow_right (hek e)) (levelPAdicIdeal_pow_le_comap ρ.toRingHom p e)
  let coneA : ∀ (e : ℕ) (he : NB ≤ e), (completedDividedPowers I γ p hp).1.DPMorphism
      (quotientDividedPowers I' γ' p e (hlevB e he).1 (hlevB e he).2) := fun e he =>
    DividedPowers.DPMorphism.comp
      (DividedPowers.DPMorphism.mk' (isDPMorphism_levelQuotientMap γ γ' p ρ (hleρ e)
        (hlevA (k e) (hkNA e)).1 (hlevA (k e) (hkNA e)).2 (hlevB e he).1 (hlevB e he).2))
      (DividedPowers.DPMorphism.mk' (hlimA.1 (k e) (hkNA e)))
  have hconeAval : ∀ (e : ℕ) (he : NB ≤ e) (x : AdicCompletion (pAdicIdeal (A := A) p) A),
      (coneA e he).toRingHom x =
        Ideal.quotientMap (pAdicIdeal (A := A') p ^ e) ρ.toRingHom (hleρ e)
          (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) (k e) x) := fun _ _ _ => rfl
  have hconeA : ∀ (m e : ℕ) (hm : NB ≤ m) (he : NB ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := pAdicIdeal (A := A') p) hme)).comp
          (coneA e he).toRingHom = (coneA m hm).toRingHom := by
    intro m e hm he hme
    refine RingHom.ext fun x ↦ ?_
    rw [RingHom.comp_apply, hconeAval e he x, hconeAval m hm x,
      ← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A) p) (hkmono hme) x]
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (pAdicIdeal (A := A) p) (k e) x)
    rw [← hw]
    rfl
  obtain ⟨a, ha, -⟩ := hlimB.2 (completionIdeal I p hp) (completedDividedPowers I γ p hp).1
    coneA hconeA
  -- the cone `Â' → A ⧸ (p)^e` whose limit is `b`
  have hdescB : ∀ e : ℕ, DividedPowers.IsDPMorphism
      (quotientDividedPowers I' γ' p (k e) (hlevB (k e) (hkNB e)).1 (hlevB (k e) (hkNB e)).2)
      (quotientDividedPowers I γ p (k e) (hlevA (k e) (hkNA e)).1 (hlevA (k e) (hkNA e)).2)
      (levelDescend p (k e) (θ (k e) (hkN e)).toRingHom) := fun e =>
    isDPMorphism_levelDescend γ γ' p (k e) (θ (k e) (hkN e)).toRingHom _ _ _ _
      (θ (k e) (hkN e)).isDPMorphism
  let coneB : ∀ (e : ℕ) (he : NA ≤ e), (completedDividedPowers I' γ' p hp').1.DPMorphism
      (quotientDividedPowers I γ p e (hlevA e he).1 (hlevA e he).2) := fun e he =>
    DividedPowers.DPMorphism.comp
      (DividedPowers.DPMorphism.mk' (isDPMorphism_factorPow I γ p
        (⟨(hlevA e he).1, (hlevA e he).2⟩ : IsPAdicLevel I γ p e)
        (⟨(hlevA (k e) (hkNA e)).1, (hlevA (k e) (hkNA e)).2⟩ : IsPAdicLevel I γ p (k e))
        (hek e)))
      (DividedPowers.DPMorphism.comp (DividedPowers.DPMorphism.mk' (hdescB e))
        (DividedPowers.DPMorphism.mk' (hlimB.1 (k e) (hkNB e))))
  have hconeBval : ∀ (e : ℕ) (he : NA ≤ e) (x : AdicCompletion (pAdicIdeal (A := A') p) A'),
      (coneB e he).toRingHom x =
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := pAdicIdeal (A := A) p) (hek e))
          (levelDescend p (k e) (θ (k e) (hkN e)).toRingHom
            (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) (k e) x)) := fun _ _ _ => rfl
  have hconeB : ∀ (m e : ℕ) (hm : NA ≤ m) (he : NA ≤ e) (hme : m ≤ e),
      (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := pAdicIdeal (A := A) p) hme)).comp
          (coneB e he).toRingHom = (coneB m hm).toRingHom := by
    intro m e hm he hme
    refine RingHom.ext fun x ↦ ?_
    rw [RingHom.comp_apply, hconeBval e he x, hconeBval m hm x,
      ← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A') p) (hkmono hme) x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) (k e) x)
    rw [← hy]
    have hθ := congrArg (fun g : A' →+* A ⧸ pAdicIdeal (A := A) p ^ k m => g y)
      (hcompat (k m) (k e) (hkN m) (hkN e) (hkmono hme))
    simp only [RingHom.comp_apply] at hθ
    show Ideal.Quotient.factor _ (Ideal.Quotient.factor _ ((θ (k e) (hkN e)).toRingHom y)) =
      Ideal.Quotient.factor _ ((θ (k m) (hkN m)).toRingHom y)
    rw [← hθ]
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((θ (k e) (hkN e)).toRingHom y)
    rw [← hw]
    rfl
  obtain ⟨b, hb, -⟩ := hlimA.2 (completionIdeal I' p hp')
    (completedDividedPowers I' γ' p hp').1 coneB hconeB
  -- `b` reduces to `θ_e` at every level at which both are defined
  have hbval : ∀ (e : ℕ) (heA : NA ≤ e) (heN : N ≤ e)
      (x : AdicCompletion (pAdicIdeal (A := A') p) A'),
      AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e (b.toRingHom x) =
        levelDescend p e (θ e heN).toRingHom
          (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e x) := by
    intro e heA heN x
    have h := congrArg (fun g : AdicCompletion (pAdicIdeal (A := A') p) A' →+*
      A ⧸ pAdicIdeal (A := A) p ^ e => g x) (hb e heA)
    simp only [RingHom.comp_apply] at h
    rw [show AdicCompletion.evalₐ (pAdicIdeal (A := A) p) e (b.toRingHom x) =
        (coneB e heA).toRingHom x from h, hconeBval e heA x,
      ← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A') p) (hek e) x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) (k e) x)
    rw [← hy]
    have hθ := congrArg (fun g : A' →+* A ⧸ pAdicIdeal (A := A) p ^ e => g y)
      (hcompat e (k e) heN (hkN e) (hek e))
    simp only [RingHom.comp_apply] at hθ
    show Ideal.Quotient.factor _ ((θ (k e) (hkN e)).toRingHom y) = (θ e heN).toRingHom y
    exact hθ
  refine ⟨a, b, ?_, ?_, ?_⟩
  · -- `a ∘ b = id`, by the uniqueness half of the universal property of `Â'`
    refine (hlimB.2 (completionIdeal I' p hp') (completedDividedPowers I' γ' p hp').1
      (fun e he => DividedPowers.DPMorphism.mk' (hlimB.1 e he))
      (fun m e hm he hme => RingHom.ext fun x ↦
        AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A') p) hme x)).unique ?_ (fun e he => rfl)
    intro e he
    refine RingHom.ext fun x ↦ ?_
    have hax := congrArg (fun g : AdicCompletion (pAdicIdeal (A := A) p) A →+*
      A' ⧸ pAdicIdeal (A := A') p ^ e => g (b.toRingHom x)) (ha e he)
    simp only [RingHom.comp_apply] at hax
    rw [RingHom.comp_apply]
    show AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e (a.toRingHom (b.toRingHom x)) =
      AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e x
    rw [show AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e (a.toRingHom (b.toRingHom x)) =
        (coneA e he).toRingHom (b.toRingHom x) from hax, hconeAval e he,
      hbval (k e) (hkNA e) (hkN e) x,
      ← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A') p) (hek e) x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (pAdicIdeal (A := A') p) (k e) x)
    rw [← hy]
    have hs := congrArg (fun g : A' →+* A' ⧸ pAdicIdeal (A := A') p ^ k e => g y)
      (hsplit (k e) (hkN e))
    simp only [RingHom.comp_apply] at hs
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((θ (k e) (hkN e)).toRingHom y)
    show Ideal.quotientMap _ ρ.toRingHom (hleρ e)
        (levelDescend p (k e) (θ (k e) (hkN e)).toRingHom (Ideal.Quotient.mk _ y)) =
      Ideal.Quotient.factor _ (Ideal.Quotient.mk _ y)
    rw [levelDescend_mk, ← hw]
    rw [← hw] at hs
    show Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e) (ρ.toRingHom w) =
      Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ e) y
    have hs' : Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ k e) (ρ.toRingHom w) =
        Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ k e) y := hs
    exact congrArg (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := pAdicIdeal (A := A') p) (hek e))) hs'
  · -- `a` is the completion of `ρ`
    intro x
    refine adicCompletion_ext_evalₐ_of_le _ NB fun e he ↦ ?_
    have hax := congrArg (fun g : AdicCompletion (pAdicIdeal (A := A) p) A →+*
      A' ⧸ pAdicIdeal (A := A') p ^ e =>
        g (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x)) (ha e he)
    simp only [RingHom.comp_apply] at hax
    rw [show AdicCompletion.evalₐ (pAdicIdeal (A := A') p) e
        (a.toRingHom (algebraMap A (AdicCompletion (pAdicIdeal (A := A) p) A) x)) =
        (coneA e he).toRingHom _ from hax, hconeAval e he]
    exact (congrArg _ (AdicCompletion.evalₐ_of (pAdicIdeal (A := A) p) (k e) x)).trans
      (AdicCompletion.evalₐ_of (pAdicIdeal (A := A') p) e (ρ.toRingHom x)).symm
  · -- `b` reduces to `θ_e` on the image of `A'`
    intro e he y
    rw [← AdicCompletion.factorPow_evalₐ (pAdicIdeal (A := A) p) (hek e)
      (b.toRingHom (algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') y)),
      hbval (k e) (hkNA e) (hkN e) _,
      show AdicCompletion.evalₐ (pAdicIdeal (A := A') p) (k e)
          (algebraMap A' (AdicCompletion (pAdicIdeal (A := A') p) A') y) =
          Ideal.Quotient.mk (pAdicIdeal (A := A') p ^ k e) y from
        AdicCompletion.evalₐ_of (pAdicIdeal (A := A') p) (k e) y, levelDescend_mk]
    have hθ := congrArg (fun g : A' →+* A ⧸ pAdicIdeal (A := A) p ^ e => g y)
      (hcompat e (k e) he (hkN e) (hek e))
    simp only [RingHom.comp_apply] at hθ
    exact hθ

end CompletionPassage

section CompletedRetract

variable (s : AffineCrystallineSituation.{u, v})
variable {P P' : Type u} [CommRing P] [Algebra s.A P] [CommRing P'] [Algebra s.A P']

/-- **The retract of [Stacks, Lemma 60.17.5, Tag 07L5] between the `p`-adic completions.**

Let `A → P' → C` be a smooth presentation in the affine situation of [Stacks, Tag 07MD] and let
`q : P ↠ P'` be any surjection of `A`-algebras, so that `A → P → C` is a second presentation.
Write `D = D_{P, γ}(J)` and `D' = D_{P', γ}(J')` for the two divided power envelopes and `D̂`,
`D̂'` for their `p`-adic completions.

Then the canonical map `ρ : D → D'` of [Stacks, Tag 07HB] is surjective, compatible with the
structure maps from `A` and with `q`, and has `I_D` for the full preimage of `I_{D'}`, and there
are morphisms of divided power rings `a : D̂ → D̂'` and `b : D̂' → D̂` with `a ∘ b = id_{D̂'}`, the
map `a` being the completion of `ρ` and the map `b` being a map **over `A`**.

Those last two facts beyond the retract identity itself are what the proof of
[Stacks, Lemma 60.21.4, Tag 07LH] needs of the endomorphism `ρ = b ∘ a` of `D̂` it applies its
factorization to, namely that it is compatible with the augmentation to `C` and with the
structure map from `A`; see `Crystalline.isAugmentationCompatible_comp_of_retract` and
`Crystalline.map_algebraMap_comp_of_retract`.  The compatibility of `b` with `A` is the limit
of the compatibility of the level splittings `θ_e` with the structure maps, which
`Crystalline.exists_compatible_levelRetract` records.

This is the first assertion of [Stacks, Tag 07L5].  Its mathematics is
`Crystalline.exists_compatible_levelRetract`, which produces the splittings `θ_e` of the
reductions of `ρ` at every finite level of the `p`-adic tower; the passage to the limit is
`Crystalline.exists_completionRetract`.

Of the second assertion of [Stacks, Tag 07L5] — that `a` and `b` induce an equivalence between
the categories of pairs over `D` and over `D'` — the source's proof derives one direction from
this first assertion: "Since `a ∘ b = id_{D'}` we see that `F ∘ G` is the identity functor".
Read on the completed de Rham complexes that is
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_comp_of_retract`, and read on the pairs
themselves it is `Crystalline.CompletedConnection.exists_horizontalEquiv_of_retract`.  For the
other direction the source reduces to the horizontality of the comparison `c_{id_D, b ∘ a}` of
the proof of [Stacks, Proposition 60.17.4, Tag 07JH] and then says "It remains to prove that
this map is horizontal, i.e., compatible with connections, which we omit."  That horizontality
is `Crystalline.nabla_taylorSum_eq`.  The equivalence itself is
`Crystalline.exists_presentation_retract_pairEquivalence`. -/
public theorem exists_completedEnvelopeRetract (q : P →ₐ[s.A] P') (f' : P' →ₐ[s.A] s.C)
    [Algebra.Smooth (s.A : Type u) P']
    (hq : Function.Surjective q) (hf' : Function.Surjective f') :
    ∃ ρ : DividedPowers.DPMorphism
        (presentationEnvelope s (f'.comp q)).object.dividedPowers
        (presentationEnvelope s f').object.dividedPowers,
      ρ.comp (presentationEnvelope s (f'.comp q)).structureMap =
          (presentationEnvelope s f').structureMap ∧
        ρ.toRingHom.comp (presentationEnvelope s (f'.comp q)).algebraMap.toRingHom =
            (presentationEnvelope s f').algebraMap.toRingHom.comp q.toRingHom ∧
          Function.Surjective ρ ∧
          (∀ u : (presentationEnvelope s (f'.comp q)).object,
            ρ u ∈ (presentationEnvelope s f').object.ideal →
              u ∈ (presentationEnvelope s (f'.comp q)).object.ideal) ∧
          ∃ (a : (DividedPowers.completedDividedPowers
                (presentationEnvelope s (f'.comp q)).object.ideal
                (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p
                (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))).1.DPMorphism
              (DividedPowers.completedDividedPowers
                (presentationEnvelope s f').object.ideal
                (presentationEnvelope s f').object.dividedPowers s.p
                (presentationEnvelope_prime_nilpotent s f' hf')).1)
            (b : (DividedPowers.completedDividedPowers
                (presentationEnvelope s f').object.ideal
                (presentationEnvelope s f').object.dividedPowers s.p
                (presentationEnvelope_prime_nilpotent s f' hf')).1.DPMorphism
              (DividedPowers.completedDividedPowers
                (presentationEnvelope s (f'.comp q)).object.ideal
                (presentationEnvelope s (f'.comp q)).object.dividedPowers s.p
                (presentationEnvelope_prime_nilpotent s (f'.comp q)
                  (hf'.comp hq))).1),
            a.comp b = DividedPowers.DPMorphism.id _ ∧
              (∀ x : (presentationEnvelope s (f'.comp q)).object,
                a.toRingHom (algebraMap _ _ x) = algebraMap _ _ (ρ.toRingHom x)) ∧
              ∀ x : (s.A : Type u), b.toRingHom
                  (algebraMap _ _ ((presentationEnvelope s f').structureMap.toRingHom x)) =
                algebraMap _ _
                  ((presentationEnvelope s (f'.comp q)).structureMap.toRingHom x) := by
  classical
  obtain ⟨ρ, hρstruct, hρalg, hρsurj, hρpre, N, hlev, θ, hsplit, hcompat, hθstruct⟩ :=
    exists_compatible_levelRetract s q f' hq hf'
  refine ⟨ρ, hρstruct, hρalg, hρsurj, hρpre, ?_⟩
  let : Algebra (DividedPowers.IntegersAtPrime s.p)
      ((presentationEnvelope s (f'.comp q)).object : Type u) :=
    (((presentationEnvelope s (f'.comp q)).structureMap.toRingHom).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  let : Algebra (DividedPowers.IntegersAtPrime s.p)
      ((presentationEnvelope s f').object : Type u) :=
    (((presentationEnvelope s f').structureMap.toRingHom).comp
      (algebraMap (DividedPowers.IntegersAtPrime s.p) s.A)).toAlgebra
  obtain ⟨a, b, hab, haρ, hbval⟩ :=
    exists_completionRetract (presentationEnvelope s (f'.comp q)).object.dividedPowers
      (presentationEnvelope s f').object.dividedPowers s.p
      (presentationEnvelope_prime_nilpotent s (f'.comp q) (hf'.comp hq))
      (presentationEnvelope_prime_nilpotent s f' hf') ρ N hlev θ hsplit hcompat
  refine ⟨a, b, hab, haρ, fun x => ?_⟩
  -- `b` reduces to `θ_e` on the image of `A'`, and `θ_e` is a map over `A`, so `b` is too
  refine adicCompletion_ext_evalₐ_of_le
    (pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p) N fun e he => ?_
  rw [hbval e he _]
  exact (DFunLike.congr_fun (hθstruct e he) x).trans
    (AdicCompletion.evalₐ_of
      (pAdicIdeal (A := (presentationEnvelope s (f'.comp q)).object) s.p) e _).symm

end CompletedRetract

end Crystalline

end
