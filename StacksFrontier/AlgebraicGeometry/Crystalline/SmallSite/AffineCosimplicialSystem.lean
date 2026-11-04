module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Coproduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEssSurj

/-!
# The cosimplicial system of thickenings `(X, T(n)_e, δ(n))`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and with `p`
nilpotent on `Γ(X, ⊤)`.  The source's section on cohomology in the affine case chooses a
polynomial presentation `P → C = Γ(X, ⊤)` over `A = Γ(S, ⊤)`, forms the `p`-adically completed
divided power envelopes `D(n)` of the kernels of the surjections `P ⊗_A ⋯ ⊗_A P → C` out of the
`(n + 1)`-fold tensor powers, sets `T(n)_e = Spec(D(n)/p^e D(n))`, and observes that each
`(X, T(n)_e, δ(n))` is an object of `Cris(X/S)`.  This file **constructs that system**, as a

`CategoryTheory.SimplicialObject (ℕ ⥤ CrystallineThickening S)`,

and proves that it satisfies
`Crystalline.GlobalCrystallineSituation.SmallSite.IsWholeSpaceSystem`, so that the cosimplicial
module `M(•)` and the complex `M(0) → M(1) → M(2) → ⋯` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean` can be formed on it.

## Which step of [Stacks, Tag 07JN] this is

[Stacks, Tag 07JN] asserts that, for `F` locally quasi-coherent with surjective comparison maps
along closed immersions, the complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)`; in
this library that conclusion is the predicate
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology` applied to a cosimplicial
system of thickenings.  This file supplies the system `(X, T(n)_e, δ(n))` itself, obtained by
transporting `D(n)` and its coprojections across the affine-to-global equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, so that
`ComputesCohomology` applies to an explicitly constructed system rather than to a parameter.  The
predicate is proved for that system as
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemCohomology.lean`, from the
following three ingredients:

* the descent of [Stacks, Tag 07JM] — the chaotic Čech computation, which runs on
  `Cris^∧(C/A)` where the generator `D` of [Stacks, Tag 07KI] lives — to the subcategory `𝒞` of
  thickenings of the whole space, along the morphism of topoi of [Stacks, Tag 07JL]; `𝒞` has no
  weakly terminal object of its own, as recorded in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalLimits.lean`;
* the vanishing `R^p g_*(F|_𝒞) = 0` for `p ≥ 1` along that morphism of topoi, and the assembly
  of it out of `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.isZero_cohomology_restriction_of_isAffine` ([Stacks, Tag 07JJ]) and
  `Stacks.acyclic_limit_of_acyclic_of_surjective` ([Stacks, Tag 0AAT]);
* the smallness bookkeeping of [Stacks, Tag 07JM], which asks for a small site.

The descent is `Crystalline.GlobalCrystallineSituation.SmallSite`
`.isDirectImageCohomologyComparison_of_leray` of `SmallSite/AffineChaoticCohomology.lean`; the
vanishing is `Crystalline.isZero_rightDerived_abelianSheafPushforward_of_surjective` of
`SmallSite/LevelLimitNaturality.lean`, with the surjectivity it needs derived from the tag's
hypotheses in `SmallSite/LevelRestrictionSurjectivity.lean`; the smallness is settled by the
small model `Crystalline.CompletedSmallSite` of `SmallSite/CompletedCechDescent.lean`.  The
products hypothesis of [Stacks, Tag 07JM] is met by the powers of `D`, which are the `D(n)` of
[Stacks, Tag 07L4] — `Crystalline.hasProduct_generator` — so no coproducts of arbitrary pairs of
objects of `Cris^∧(C/A)` are needed.

## Main definitions

In the namespace `Crystalline`, for an affine crystalline situation:

* `Crystalline.dpQuotientLevelRing`, `Crystalline.levelProj`, `Crystalline.levelHom` — the quotient
  `R/(p)^k` of a divided power ring at a `p`-adic level `k`, the projection onto it, and the map
  `R/(p)^k ⟶ R'/(p)^{k'}` induced by a morphism `R ⟶ R'` and a level drop `k' ≤ k`.
* `Crystalline.levelThickening` — the finite level `T_e` of a completed crystalline thickening,
  as an object of the little affine crystalline category `Cris(C/A)`.
* `Crystalline.uniformLevel` — a cutoff that is a `p`-adic level for **every** object of
  `Cris^∧(C/A)` at once; this is what makes the levels functorial in the thickening.
* `Crystalline.levelFunctor` — the resulting functor
  `Cris^∧(C/A) × ℕᵒᵖ ⥤ Cris(C/A)`, `(X, e) ↦ X/(p)^{N + e}`.
* `Crystalline.canonicalPresentation` — the tautological surjective polynomial presentation
  `A[x_c : c ∈ C] → C`, which is the presentation the construction below is run on.
* `Crystalline.envelopeCosimplicial` — **the cosimplicial object `D(0) → D(1) → D(2) → ⋯` of
  `Cris^∧(C/A)`**, built from [Stacks, Tag 07L4]: in degree `n` it is `D(n)`, and a morphism
  `φ : ⦋n⦌ ⟶ ⦋m⦌` of the simplex category acts by the map out of the coproduct whose `j`-th
  component is the `φ(j)`-th coprojection `D ⟶ D(m)`.
* `Crystalline.affineLevelSystem` — the composite
  `SimplexCategory ⥤ ℕᵒᵖ ⥤ Cris(C/A)`, `(n, e) ↦ D(n)/(p)^{N + e}`.

In the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`:

* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` — **the system
  `(X, T(n)_e, δ(n))`**, the transport of `affineLevelSystem` across the equivalence
  `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`, as a `SimplicialObject (ℕ ⥤ CrystallineThickening S)`.

## Main results

* `Crystalline.envelopeCosimplicial_coprojection_comp_map` — the structure map of
  `envelopeCosimplicial` in degree `φ` is characterised by `coproj j ≫ D(φ) = coproj (φ j)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isWholeSpaceSystem_wholeSpaceSystem` —
  **the system consists of thickenings of the whole of `X`**, so it lies in the subcategory `𝒞`
  of [Stacks, Tag 07JK] and `IsWholeSpaceSystem` holds for it.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem_obj_obj` — the object in
  bidegree `(n, e)` is the transport of `D(n)/(p)^{N + e}`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.cosimplicialSections_wholeSpaceSystem_obj` —
  **the identification of `M(n)`**: `M(n) = lim_e F(D(n)/(p)^{N + e})`, the limit being taken of
  the sections of `F` read on the affine site through the equivalence.
* `Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplex_wholeSpaceSystem_X` — the
  degree-`n` term of `M(0) → M(1) → M(2) → ⋯` for this system is that limit.

## Implementation notes

This file proves that the system exists, that it is a system of thickenings of the whole space,
and what its sections are.  Nothing is proved here about the cohomology of `Cris(X/S)`.  No tag
attribute is placed here: [Stacks, Tag 07L4] is already tagged where it is proved, and
[Stacks, Tag 07JN] is tagged on `...SmallSite.wholeSpaceSystemDerivedIso` of
`SmallSite/WholeSpaceSystemDerived.lean`.

The levels are indexed by `e ↦ N + e` for a cutoff `N` depending only on the affine situation,
rather than by `e ↦ e`.  This is forced and harmless.  It is forced because `(p)^k` is a sub
divided power ideal of the divided power ideal only for `k` large, so `X/(p)^k` is a divided
power ring only then, while the carrier type `ℕ ⥤ CrystallineThickening S` asks for an object at
every `e`; and a cutoff depending on the object would destroy functoriality in the simplicial
direction, where morphisms `D(n) ⟶ D(m)` exist for all `n` and `m`.  It is harmless because the
system `e ↦ X/(p)^{N + e}` is cofinal in `e ↦ X/(p)^e`, so the limit `M(n)` is unchanged; the
source itself says "for `e ≫ 0`".  The cutoff is uniform in the object because the condition
only needs `p^m ∈ J` for the nilpotency exponent `m` of `p` in `C`, which every object of
`Cris^∧(C/A)` satisfies with the same `m`, its quotient by its divided power ideal being `C`.

The presentation used is the tautological one, `A[x_c : c ∈ C] → C`, rather than an arbitrary
one; this is a choice of presentation, which [Stacks, Tag 07JN] also makes, and it keeps the
universe of the variables equal to the universe of `C`, which is what the affine-to-global
equivalence needs.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u v w

noncomputable section

namespace Crystalline

/-! ### A `p`-adic level criterion that is uniform in the ring -/

/-- **A `p`-adic level criterion depending only on a power of `p` lying in the divided power
ideal.**  If `p^m ∈ I` then every `e` with `2m ≤ e` is a `p`-adic level for
`(I, γ)`, that is, `(p)^e ⊆ I` and `(p)^e` is a sub divided power ideal.

Unlike `Crystalline.isPAdicLevel_of_nilpotencyExponent_lt`, whose bound is the opaque exponent
chosen out of the nilpotency hypothesis, the bound here is an explicit function of `m`; this is
what lets a single cutoff serve for a whole family of divided power rings. -/
theorem isPAdicLevel_of_pow_mem {A : Type w} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    (p : ℕ) {m e : ℕ} (hm : (p : A) ^ m ∈ I) (hme : 2 * m ≤ e) :
    IsPAdicLevel I γ p e := by
  have hsplit : (p : A) ^ e = (p : A) ^ (e - m) * (p : A) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have hmem : (p : A) ^ e ∈ I := by
    rw [hsplit]
    exact I.mul_mem_left _ hm
  refine ⟨?_, ?_⟩
  · show Ideal.span {(p : A)} ^ e ≤ I
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  · show γ.IsSubDPIdeal (Ideal.span {(p : A)} ^ e)
    rw [Ideal.span_singleton_pow]
    refine (DividedPowers.span_isSubDPIdeal_iff (by simpa using hmem)).2 ?_
    intro n hn t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hn) with h1 | h1
    · rw [← h1, γ.dpow_one hmem]
      exact Ideal.mem_span_singleton_self _
    · have h1' : 2 ≤ n := h1
      have key : γ.dpow n ((p : A) ^ e) =
          ((p : A) ^ (e - m)) ^ n * γ.dpow n ((p : A) ^ m) := by
        conv_lhs => rw [hsplit]
        exact γ.dpow_mul hm
      rw [key, ← pow_mul]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ ?_))
      have hmul : (e - m) * 2 ≤ (e - m) * n := Nat.mul_le_mul (le_refl (e - m)) h1'
      omega

/-! ### The quotient of a divided power ring at a `p`-adic level -/

section LevelRing

variable (p : ℕ)

/-- **The quotient `R/(p)^k` of a divided power ring at a `p`-adic level `k`**, with the
divided powers induced on the image of the divided power ideal.  Its spectrum is the finite
level `T_k` of the thickening whose ambient ring is `R`. -/
abbrev dpQuotientLevelRing (R : DividedPowerRing.{w}) (k : ℕ)
    (h : IsPAdicLevel R.ideal R.dividedPowers p k) : DividedPowerRing.{w} :=
  ⟨R ⧸ DividedPowers.pAdicIdeal (A := R) p ^ k,
    R.ideal.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k)),
    DividedPowers.quotientDividedPowers R.ideal R.dividedPowers p k h.1 h.2⟩

variable (R : DividedPowerRing.{w}) (k : ℕ) (h : IsPAdicLevel R.ideal R.dividedPowers p k)

/-- The intersection of `(p)^k` with the divided power ideal is a sub divided power ideal, at a
`p`-adic level `k`; this is the hypothesis under which the divided powers descend. -/
theorem isSubDPIdeal_inf_of_isPAdicLevel
    (hk : IsPAdicLevel R.ideal R.dividedPowers p k) :
    R.dividedPowers.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := R) p ^ k ⊓ R.ideal) := by
  rw [inf_eq_left.mpr hk.1]
  exact hk.2

/-- The quotient map onto a `p`-adic level is a morphism of divided power rings. -/
theorem isDPMorphism_levelMk :
    R.dividedPowers.IsDPMorphism (dpQuotientLevelRing p R k h).dividedPowers
      (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k)) :=
  DividedPowers.Quotient.isDPMorphism R.dividedPowers
    (isSubDPIdeal_inf_of_isPAdicLevel p R k h)

/-- **The projection `R ⟶ R/(p)^k` onto a `p`-adic level**, as a morphism of divided power
rings. -/
def levelProj : R ⟶ dpQuotientLevelRing p R k h :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_levelMk p R k h)

/-- The underlying ring map of `levelProj` is the quotient map `R → R/(p)^k`. -/
@[simp]
theorem levelProj_toRingHom :
    (levelProj p R k h).toRingHom =
      Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k) := rfl

/-- The map induced on the quotients by the divided power ideals by the projection onto a
`p`-adic level.  It is a bijection, by `levelQuotientMap_bijective`. -/
abbrev levelQuotientMap :
    (R ⧸ R.ideal) →+* (dpQuotientLevelRing p R k h ⧸ (dpQuotientLevelRing p R k h).ideal) :=
  Ideal.quotientMap (dpQuotientLevelRing p R k h).ideal
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k))
    (Ideal.map_le_iff_le_comap.mp (isDPMorphism_levelMk p R k h).ideal_comp)

/-- `levelQuotientMap` sends the class of `a` modulo `J` to the class of the image of `a` in
`R/(p)^k`. -/
@[simp]
theorem levelQuotientMap_mk (a : R) :
    levelQuotientMap p R k h (Ideal.Quotient.mk R.ideal a) =
      Ideal.Quotient.mk (dpQuotientLevelRing p R k h).ideal
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k) a) := rfl

/-- **Passing to a `p`-adic level does not change the quotient by the divided power ideal**:
`R/J ≅ (R/(p)^k)/(J/(p)^k)`, because `(p)^k ⊆ J`.  This is what makes a finite level of a
crystalline thickening again crystalline. -/
theorem levelQuotientMap_bijective : Function.Bijective (levelQuotientMap p R k h) := by
  refine ⟨Ideal.quotientMap_injective' ?_,
    Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  show Ideal.comap (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k))
    (R.ideal.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k))) ≤ R.ideal
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_le le_rfl h.1

/-- **The image of `p` is killed by its `k`-th power in a `p`-adic level quotient**, with the
exponent `k` read off the level and *not* depending on the divided power ring `R`.  This is
what makes a whole family of level quotients at one and the same level uniformly annihilated
by a single power of `p`. -/
theorem pow_natCast_eq_zero_levelRing :
    (p : dpQuotientLevelRing p R k h) ^ k = 0 := by
  show (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k) (p : R)) ^ k = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  show (p : R) ^ k ∈ DividedPowers.pAdicIdeal (A := R) p ^ k
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) k

/-- The image of `p` is nilpotent in a `p`-adic level quotient. -/
theorem isNilpotent_prime_levelRing : IsNilpotent (p : dpQuotientLevelRing p R k h) :=
  ⟨k, pow_natCast_eq_zero_levelRing p R k h⟩

end LevelRing

section LevelHom

variable (p : ℕ) {R R' : DividedPowerRing.{w}} {k k' : ℕ}
  (h : IsPAdicLevel R.ideal R.dividedPowers p k)
  (h' : IsPAdicLevel R'.ideal R'.dividedPowers p k')

/-- A morphism of divided power rings carries `(p)^k` into `(p)^{k'}` whenever `k' ≤ k`. -/
theorem pAdicIdeal_pow_le_comap (f : R ⟶ R') (hk : k' ≤ k) :
    DividedPowers.pAdicIdeal (A := R) p ^ k ≤
      (DividedPowers.pAdicIdeal (A := R') p ^ k').comap f.toRingHom := by
  rw [← Ideal.map_le_iff_le_comap]
  show Ideal.map f.toRingHom (Ideal.span {(p : R)} ^ k) ≤ Ideal.span {(p : R')} ^ k'
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, map_pow, map_natCast]
  exact Ideal.mem_span_singleton.2 (pow_dvd_pow _ hk)

/-- The map `R/(p)^k → R'/(p)^{k'}` induced by a morphism `R ⟶ R'` of divided power rings is a
morphism of divided power rings. -/
theorem isDPMorphism_levelQuotientMap (f : R ⟶ R') (hk : k' ≤ k) :
    (dpQuotientLevelRing p R k h).dividedPowers.IsDPMorphism
      (dpQuotientLevelRing p R' k' h').dividedPowers
      (Ideal.quotientMap (DividedPowers.pAdicIdeal (A := R') p ^ k') f.toRingHom
        (pAdicIdeal_pow_le_comap p f hk)) := by
  refine DividedPowers.IsDPMorphism.of_comp R.dividedPowers
    (dpQuotientLevelRing p R k h).dividedPowers (dpQuotientLevelRing p R' k' h').dividedPowers
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R) p ^ k))
    (Ideal.quotientMap (DividedPowers.pAdicIdeal (A := R') p ^ k') f.toRingHom
      (pAdicIdeal_pow_le_comap p f hk))
    rfl (isDPMorphism_levelMk p R k h) ?_
  rw [Ideal.quotientMap_comp_mk]
  exact DividedPowers.IsDPMorphism.comp (dpQuotientLevelRing p R' k' h').dividedPowers
    (isDPMorphism_levelMk p R' k' h') f.isDPMorphism

/-- **The map `R/(p)^k ⟶ R'/(p)^{k'}` induced by a morphism `R ⟶ R'` of divided power rings and
a level drop `k' ≤ k`.**  Taking `k = k'` this is functoriality of the level quotient in the
ring; taking `f = 𝟙` it is the transition map of the tower of levels. -/
def levelHom (f : R ⟶ R') (hk : k' ≤ k) :
    dpQuotientLevelRing p R k h ⟶ dpQuotientLevelRing p R' k' h' :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_levelQuotientMap p h h' f hk)

/-- The underlying ring map of `levelHom` is the map of quotients induced by `f`. -/
@[simp]
theorem levelHom_toRingHom (f : R ⟶ R') (hk : k' ≤ k) :
    (levelHom p h h' f hk).toRingHom =
      Ideal.quotientMap (DividedPowers.pAdicIdeal (A := R') p ^ k') f.toRingHom
        (pAdicIdeal_pow_le_comap p f hk) := rfl

/-- `levelHom` sends the class of `a` in `R/(p)^k` to the class of `f a` in `R'/(p)^{k'}`. -/
@[simp]
theorem levelHom_mk (f : R ⟶ R') (hk : k' ≤ k) (a : R) :
    levelHom p h h' f hk (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := R') p ^ k') (f.toRingHom a) := rfl

/-- The projection onto a level is natural: `R ⟶ R/(p)^k ⟶ R'/(p)^{k'}` is
`R ⟶ R' ⟶ R'/(p)^{k'}`. -/
theorem levelProj_comp_levelHom (f : R ⟶ R') (hk : k' ≤ k) :
    levelProj p R k h ≫ levelHom p h h' f hk = f ≫ levelProj p R' k' h' := by
  ext a
  rfl

end LevelHom

section LevelHomFunctorial

variable (p : ℕ)

/-- The map of levels induced by the identity and no level drop is the identity. -/
theorem levelHom_id (R : DividedPowerRing.{w}) (k : ℕ)
    (h : IsPAdicLevel R.ideal R.dividedPowers p k) :
    levelHom p h h (𝟙 R) le_rfl = 𝟙 (dpQuotientLevelRing p R k h) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The maps of levels compose: the map induced by `f ≫ g` is the composite of the maps induced
by `f` and by `g`. -/
theorem levelHom_comp {R R' R'' : DividedPowerRing.{w}} {k k' k'' : ℕ}
    (h : IsPAdicLevel R.ideal R.dividedPowers p k)
    (h' : IsPAdicLevel R'.ideal R'.dividedPowers p k')
    (h'' : IsPAdicLevel R''.ideal R''.dividedPowers p k'')
    (f : R ⟶ R') (g : R' ⟶ R'') (hk : k' ≤ k) (hk' : k'' ≤ k') :
    levelHom p h h'' (f ≫ g) (hk'.trans hk) =
      levelHom p h h' f hk ≫ levelHom p h' h'' g hk' := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end LevelHomFunctorial

/-! ### The finite levels of a completed crystalline thickening -/

section LevelThickening

variable {s : AffineCrystallineSituation.{u, v}}

/-- **The finite level `T_k` of a completed crystalline thickening**, as a divided power
thickening: the ambient divided power ring is `B/(p)^k` and the structural map `C → B/J` is
unchanged, by `Crystalline.levelQuotientMap_bijective`. -/
def levelThickeningObj (X : CompletedCrystallineThickening.{u, v, w} s) (k : ℕ)
    (h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k) :
    DividedPowerThickening.{u, v, w} s where
  ring := dpQuotientLevelRing s.p X.ring k h
  fromBase := (levelProj s.p X.ring k h).comp X.fromBase
  prime_nilpotent := isNilpotent_prime_levelRing s.p X.ring k h
  toQuotient := (levelQuotientMap s.p X.ring k h).comp X.toQuotient
  commutes := by
    refine RingHom.ext fun x => ?_
    have hx : Ideal.Quotient.mk X.ring.ideal (X.fromBase.toRingHom x) =
        X.toQuotient (algebraMap s.A s.C x) := RingHom.congr_fun X.commutes x
    change Ideal.Quotient.mk (dpQuotientLevelRing s.p X.ring k h).ideal
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k)
          (X.fromBase.toRingHom x)) =
      levelQuotientMap s.p X.ring k h (X.toQuotient (algebraMap s.A s.C x))
    rw [← hx, levelQuotientMap_mk]

/-- **A finite level of a completed crystalline thickening is an object of the little affine
crystalline category `Cris(C/A)`.** -/
def levelThickening (X : CompletedCrystallineThickening.{u, v, w} s) (k : ℕ)
    (h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k) :
    CrystallineThickening.{u, v, w} s :=
  ⟨levelThickeningObj X k h,
    (levelQuotientMap_bijective s.p X.ring k h).comp X.toQuotient_bijective⟩

/-- The ambient divided power ring of the level `levelThickening X k h` is `X.ring/(p)^k`. -/
@[simp]
theorem levelThickening_ring (X : CompletedCrystallineThickening.{u, v, w} s) (k : ℕ)
    (h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k) :
    (levelThickening X k h).obj.ring = dpQuotientLevelRing s.p X.ring k h := rfl

/-- **The morphism of finite levels induced by a morphism of completed crystalline thickenings
and a level drop.**  For `k' ≤ k` and `f : X ⟶ Y`, the map `X/(p)^k ⟶ Y/(p)^{k'}`. -/
def levelThickeningMap {X Y : CompletedCrystallineThickening.{u, v, w} s} {k k' : ℕ}
    (h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k)
    (h' : IsPAdicLevel Y.ring.ideal Y.ring.dividedPowers s.p k')
    (f : X ⟶ Y) (hk : k' ≤ k) :
    levelThickening X k h ⟶ levelThickening Y k' h' :=
  ⟨{ hom := levelHom s.p h h' f.hom hk
     fromBase_comp := by
       ext a
       have hfb : f.hom.toRingHom (X.fromBase.toRingHom a) = Y.fromBase.toRingHom a :=
         DFunLike.congr_fun f.fromBase_comp a
       change Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := Y.ring) s.p ^ k')
           (f.hom.toRingHom (X.fromBase.toRingHom a)) =
         Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := Y.ring) s.p ^ k')
           (Y.fromBase.toRingHom a)
       rw [hfb]
     toQuotient_comp := by
       refine RingHom.ext fun c => ?_
       obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (X.toQuotient c)
       have hY : Y.toQuotient c =
           Ideal.Quotient.mk Y.ring.ideal (f.hom.toRingHom a) := by
         rw [← RingHom.congr_fun f.toQuotient_comp c, RingHom.comp_apply, ← ha,
           DividedPowerRing.quotientRingHom_mk]
         rfl
       change DividedPowerRing.quotientRingHom (levelHom s.p h h' f.hom hk)
           (levelQuotientMap s.p X.ring k h (X.toQuotient c)) =
         levelQuotientMap s.p Y.ring k' h' (Y.toQuotient c)
       rw [← ha, hY, levelQuotientMap_mk, levelQuotientMap_mk,
         DividedPowerRing.quotientRingHom_mk]
       rfl }⟩

end LevelThickening

/-! ### A level that is uniform in the thickening -/

section UniformLevel

variable (s : AffineCrystallineSituation.{u, v})

/-- **A `p`-adic level cutoff that works for every object of `Cris^∧(C/A)` at once**: twice the
nilpotency exponent of `p` in `C` chosen out of `AffineCrystallineSituation.prime_nilpotent`.
Every object of the completed affine crystalline site has `C` as its quotient by its divided
power ideal, so the same cutoff serves for all of them, by
`Crystalline.isPAdicLevel_uniformLevel_add`. -/
def uniformLevel : ℕ := 2 * Classical.choose s.prime_nilpotent

variable {s}

/-- The nilpotency exponent of `p` in `C` is already a nilpotency exponent of `p` modulo the
divided power ideal of any completed crystalline thickening. -/
theorem pow_prime_mem_ideal (X : CompletedCrystallineThickening.{u, v, w} s) :
    (s.p : X.ring) ^ Classical.choose s.prime_nilpotent ∈ X.ring.ideal := by
  have hcomm : X.toQuotient (s.p : s.C) =
      Ideal.Quotient.mk X.ring.ideal (s.p : X.ring) := by simp
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  rw [map_pow, ← hcomm, ← map_pow, Classical.choose_spec s.prime_nilpotent, map_zero]

/-- **The uniform cutoff really is a `p`-adic level, for every object and every `e`.** -/
theorem isPAdicLevel_uniformLevel_add (X : CompletedCrystallineThickening.{u, v, w} s) (e : ℕ) :
    IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p (uniformLevel s + e) :=
  isPAdicLevel_of_pow_mem _ _ (pow_prime_mem_ideal X) (Nat.le_add_right _ _)

/-- **The finite levels of a completed crystalline thickening, as a functor of the thickening and
of the level**: `(X, e) ↦ X/(p)^{N + e}`, contravariant in `e` because `X/(p)^{N + e}` surjects
onto `X/(p)^{N + e'}` for `e' ≤ e`. -/
def levelFunctor (s : AffineCrystallineSituation.{u, v}) :
    CompletedCrystallineThickening.{u, v, w} s × ℕᵒᵖ ⥤ CrystallineThickening.{u, v, w} s where
  obj Xe := levelThickening Xe.1 (uniformLevel s + Xe.2.unop)
    (isPAdicLevel_uniformLevel_add Xe.1 Xe.2.unop)
  map {Xe Ye} fg := levelThickeningMap _ _ fg.1
    (Nat.add_le_add_left (leOfHom fg.2.unop) _)
  map_id Xe := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp {Xe Ye Ze} fg gh := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end UniformLevel

/-! ### The cosimplicial object `D(0) → D(1) → D(2) → ⋯` -/

section Cosimplicial

/-- **The tautological polynomial presentation of `C`**: the polynomial algebra on the set `C`
itself, mapping the variable `x_c` to `c`.  It is surjective, and its index type lives in the
universe of `C`, which is what keeps `D(n)` in the universe the affine-to-global equivalence
needs. -/
def canonicalPresentation (s : AffineCrystallineSituation.{u, v}) :
    MvPolynomial s.C s.A →ₐ[s.A] s.C :=
  MvPolynomial.aeval fun c => c

/-- The tautological presentation `A[x_c : c ∈ C] → C` is surjective. -/
theorem canonicalPresentation_surjective (s : AffineCrystallineSituation.{u, v}) :
    Function.Surjective (canonicalPresentation s) := fun c =>
  ⟨MvPolynomial.X c, by simp [canonicalPresentation]⟩

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- A choice, for each `n`, of the colimit datum exhibiting `D(n)` as the coproduct of `n + 1`
copies of `D` in `Cris^∧(C/A)`, which is [Stacks, Tag 07L4]. -/
def envelopeCoproductIsColimit (n : ℕ) :
    IsColimit (Cofan.mk (tensorPowerEnvelopeThickening s g hg n).thickening
      (completedEnvelopeCoprojection s g hg n)) :=
  (completedEnvelope_isCoproduct s g hg n).some

/-- **Morphisms out of `D(n)` are determined by their restrictions along the `n + 1`
coprojections**, `D(n)` being their coproduct. -/
theorem envelopeCoproduct_hom_ext {n : ℕ}
    {B : CompletedCrystallineThickening.{u, v, max u w} s}
    (a b : (tensorPowerEnvelopeThickening s g hg n).thickening ⟶ B)
    (hab : ∀ j, completedEnvelopeCoprojection s g hg n j ≫ a =
      completedEnvelopeCoprojection s g hg n j ≫ b) : a = b :=
  Cofan.IsColimit.hom_ext (envelopeCoproductIsColimit s g hg n) a b hab

/-- **The map out of `D(n)` with prescribed restrictions along the coprojections**, read on the
coprojections. -/
theorem coprojection_comp_desc {n : ℕ}
    {B : CompletedCrystallineThickening.{u, v, max u w} s}
    (k : Fin (n + 1) → ((completedEnvelopeThickening s g hg).thickening ⟶ B)) (j : Fin (n + 1)) :
    completedEnvelopeCoprojection s g hg n j ≫
        Cofan.IsColimit.desc (envelopeCoproductIsColimit s g hg n) k = k j :=
  Cofan.IsColimit.fac (envelopeCoproductIsColimit s g hg n) k j

/-- **The cosimplicial object `D(0) → D(1) → D(2) → ⋯` of `Cris^∧(C/A)`.**  In degree `n` it is
`D(n)`, the completed divided power envelope of the `(n + 1)`-fold tensor power presentation,
which [Stacks, Tag 07L4] exhibits as the coproduct of `n + 1` copies of `D`; a morphism
`φ : ⦋n⦌ ⟶ ⦋m⦌` acts by the map out of that coproduct whose `j`-th component is the `φ(j)`-th
coprojection `D ⟶ D(m)`. -/
def envelopeCosimplicial :
    CosimplicialObject (CompletedCrystallineThickening.{u, v, max u w} s) where
  obj n := (tensorPowerEnvelopeThickening s g hg n.len).thickening
  map {n m} φ := Cofan.IsColimit.desc (envelopeCoproductIsColimit s g hg n.len)
    fun j => completedEnvelopeCoprojection s g hg m.len (φ.toOrderHom j)
  map_id n := by
    refine envelopeCoproduct_hom_ext s g hg _ _ fun j => ?_
    rw [coprojection_comp_desc, Category.comp_id]
    rfl
  map_comp {n m l} φ ψ := by
    refine envelopeCoproduct_hom_ext s g hg _ _ fun j => ?_
    rw [coprojection_comp_desc, ← Category.assoc, coprojection_comp_desc,
      coprojection_comp_desc]
    rfl

/-- **The structure maps of `D(•)` are characterised by their effect on the coprojections**:
the `j`-th coprojection into `D(n)` followed by `D(φ)` is the `φ(j)`-th coprojection into
`D(m)`. -/
theorem envelopeCosimplicial_coprojection_comp_map {n m : SimplexCategory} (φ : n ⟶ m)
    (j : Fin (n.len + 1)) :
    completedEnvelopeCoprojection s g hg n.len j ≫ (envelopeCosimplicial s g hg).map φ =
      completedEnvelopeCoprojection s g hg m.len (φ.toOrderHom j) :=
  Cofan.IsColimit.fac (envelopeCoproductIsColimit s g hg n.len) _ j

/-- **The cosimplicial system of finite levels `(n, e) ↦ D(n)/(p)^{N + e}`** on the affine side,
as a functor `SimplexCategory ⥤ ℕᵒᵖ ⥤ Cris(C/A)`: the cosimplicial object `D(•)` of
`Cris^∧(C/A)` followed by the finite-level functor. -/
def affineLevelSystem :
    SimplexCategory ⥤ ℕᵒᵖ ⥤ CrystallineThickening.{u, v, max u w} s :=
  envelopeCosimplicial s g hg ⋙ Functor.curryObj (levelFunctor s)

/-- The object of `affineLevelSystem` in bidegree `(n, e)` is the finite level
`D(n)/(p)^{N + e}`. -/
@[simp]
theorem affineLevelSystem_obj_obj (n e : ℕ) :
    ((affineLevelSystem s g hg).obj ⦋n⦌).obj (op e) =
      levelThickening (tensorPowerEnvelopeThickening s g hg n).thickening
        (uniformLevel s + e) (isPAdicLevel_uniformLevel_add _ e) := rfl

end Cosimplicial

end Crystalline

/-! ### The system `(X, T(n)_e, δ(n))` on the global small crystalline site -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

/-- **The polynomial presentation the system `(X, T(n)_e, δ(n))` is built from**: a surjection
`g : A[x_i : i ∈ ι] → C` of `A = Γ(S, ⊤)`-algebras onto `C = Γ(X, ⊤)`, for any index type `ι`, as
in [Stacks, Section 60.17, Tag 07J7], which lets `P` be any polynomial algebra over `A` with a
surjection onto `C`.  Everything built from the system is stated for an arbitrary instance; the
global instance `instWholeSpacePresentation` is the tautological presentation
`Crystalline.canonicalPresentation`, `ι = C`. -/
class WholeSpacePresentation (S : GlobalCrystallineSituation.{u})
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) where
  /-- The index type of the variables. -/
  ι : Type u
  /-- The presentation `A[x_i : i ∈ ι] → C`. -/
  g : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A] (affineSituation S hp).C
  /-- The presentation is surjective. -/
  surjective : Function.Surjective g

/-- **The tautological presentation `A[x_c : c ∈ C] → C`, `x_c ↦ c`**, the default presentation of
the system. -/
instance instWholeSpacePresentation (S : GlobalCrystallineSituation.{u})
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) : WholeSpacePresentation S hp where
  ι := (affineSituation S hp).C
  g := canonicalPresentation _
  surjective := canonicalPresentation_surjective _

variable (S : GlobalCrystallineSituation.{u}) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]

/-- The index type `ι` of the variables of the presentation of the system. -/
abbrev wholeSpaceIndex : Type u := WholeSpacePresentation.ι (S := S) (hp := hp)

/-- The presentation `g : A[x_i : i ∈ ι] → C` of the system. -/
abbrev wholeSpacePresentation :
    MvPolynomial (wholeSpaceIndex S hp) (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
      (affineSituation S hp).C :=
  WholeSpacePresentation.g

/-- The presentation of the system is surjective. -/
theorem wholeSpacePresentation_surjective : Function.Surjective (wholeSpacePresentation S hp) :=
  WholeSpacePresentation.surjective

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- The transport of an object of the little affine crystalline category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))` into `Cris(X/S)ᵒᵖ`, along the inverse of the equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` followed by the inclusion of
the subcategory `𝒞` of thickenings of the whole space. -/
def affineToWholeSite :
    _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp) ⥤
      (CrystallineThickening S)ᵒᵖ :=
  (wholeSiteEquivLittleAffine hp).inverse ⋙ (wholeι S).op

/-- The transported system, before the opposites are sorted out: the affine cosimplicial system
of finite levels read in `Cris(X/S)ᵒᵖ`. -/
def wholeSpaceSystemAux :
    SimplexCategory ⥤ ℕᵒᵖ ⥤ (CrystallineThickening S)ᵒᵖ :=
  affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (affineToWholeSite S hp)

/-- **The cosimplicial system of thickenings `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN]**, for a
global crystalline situation with `X` and `S` affine and `p` nilpotent on `Γ(X, ⊤)`.

In bidegree `(n, e)` it is the object of `Cris(X/S)` corresponding, under the equivalence
`𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))` of
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, to the finite level
`D(n)/(p)^{N + e}` of the completed divided power envelope `D(n)` of the `(n + 1)`-fold tensor
power of the polynomial presentation `...SmallSite.wholeSpacePresentation` of `Γ(X, ⊤)` (by
default the tautological one).  It is simplicial in `n` and covariant in `e`, both directions
being reversed by the equivalence from the cosimplicial ring
`D(0) → D(1) → ⋯` and from the surjections `D(n)/(p)^{N + e + 1} → D(n)/(p)^{N + e}`. -/
def wholeSpaceSystem : SimplicialObject (ℕ ⥤ CrystallineThickening S) :=
  (wholeSpaceSystemAux S hp ⋙ Functor.opInv ℕ (CrystallineThickening S)).leftOp

/-- **The object of the system in bidegree `(n, e)`** is the transport of the finite level
`D(n)/(p)^{N + e}` across the affine-to-global equivalence. -/
theorem wholeSpaceSystem_obj_obj (n e : ℕ) :
    ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e =
      ((wholeSiteEquivLittleAffine hp).inverse.obj
        (levelThickening
          (tensorPowerEnvelopeThickening (affineSituation S hp) (wholeSpacePresentation S hp)
            (wholeSpacePresentation_surjective S hp) n).thickening
          (uniformLevel (affineSituation S hp) + e)
          (isPAdicLevel_uniformLevel_add _ e))).unop.obj := rfl

variable {S} in
/-- The object `T(n)_e` of the cosimplicial system of [Stacks, Tag 07JN]. -/
abbrev levelObj (n e : ℕ) : CrystallineThickening S :=
  ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e

/-- **The system `(X, T(n)_e, δ(n))` consists of thickenings of the whole of `X`**, so it lies in
the subcategory `𝒞` of [Stacks, Tag 07JK]: this is
`Crystalline.GlobalCrystallineSituation.SmallSite.IsWholeSpaceSystem` for it.  Every object of
the system is in the image of the inclusion `𝒞 ⥤ Cris(X/S)`, by construction. -/
theorem isWholeSpaceSystem_wholeSpaceSystem :
    IsWholeSpaceSystem (wholeSpaceSystem S hp) := fun _ _ =>
  ((wholeSiteEquivLittleAffine hp).inverse.obj _).unop.property

/-- The sections of an abelian presheaf on `Cris(X/S)` read on the little affine crystalline
category through the equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`.  This is the affine-side
presheaf whose limits over the finite levels are the terms of `M(•)`. -/
def affineSections (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp) ⥤
      AddCommGrpCat.{u + 1} :=
  affineToWholeSite S hp ⋙ F

/-- **The identification of `M(n)`.**  The degree-`n` term of the cosimplicial module `M(•)` of
[Stacks, Tag 07JN] attached to the system `(X, T(n)_e, δ(n))` is the limit over `e` of the
sections of `F` on the finite levels `D(n)/(p)^{N + e}` of `D(n)`, read on the affine site
through the equivalence.  This is what makes the system usable: it turns the global limit
`M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)` into a limit over the levels of the ring `D(n)`. -/
theorem cosimplicialSections_wholeSpaceSystem_obj
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (cosimplicialSections (wholeSpaceSystem S hp) F).obj ⦋n⦌ =
      limit ((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp)).obj ⦋n⦌ ⋙ affineSections S hp F) := rfl

/-- **The degree-`n` term of the complex `M(0) → M(1) → M(2) → ⋯`** of the system
`(X, T(n)_e, δ(n))` is that limit. -/
theorem sectionsComplex_wholeSpaceSystem_X
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) F).X n =
      limit ((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp)).obj ⦋n⦌ ⋙ affineSections S hp F) :=
  cosimplicialSections_wholeSpaceSystem_obj S hp F n

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
