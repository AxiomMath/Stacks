module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# The finite divided power levels of a divided power ring over `ℤ_(p)`

Let `p` be a prime, let `(A, I, γ)` be a divided power ring with `A` an algebra over `ℤ_(p)`
and `p` nilpotent in `A/I`.  For `e ≫ 0` the ideal `(p^e)` is contained in `I` and is preserved
by `γ`, so the divided powers descend to the quotient `A/p^eA` and `(A/p^eA, I/p^eA, γ̄)` is a
divided power ring; its spectrum is the base `S_e = Spec(A/p^eA)`.  These quotients form a tower
under the canonical surjections `A/p^eA → A/p^mA` for `m ≤ e`, each of which is a morphism of
divided power rings, and the tower receives `(A, I, γ)` compatibly.

## Main definitions

* `Crystalline.IsPAdicLevel` — the property of an exponent `e` that `(p^e) ⊆ I` and that `(p^e)`
  is a sub divided power ideal for `γ`.
* `Crystalline.pAdicLevelRing` — the divided power ring `(A/p^eA, I/p^eA, γ̄)` of which the base
  `S_e = Spec(A/p^eA)` is the spectrum.
* `Crystalline.pAdicLevelProj` — the morphism of divided power rings
  `(A, I, γ) → (A/p^eA, I/p^eA, γ̄)`.
* `Crystalline.pAdicLevelTransition` — the transition morphism of divided power rings
  `(A/p^eA, I/p^eA, γ̄) → (A/p^mA, I/p^mA, γ̄)` for `m ≤ e`.

## Main results

* `Crystalline.exists_forall_isPAdicLevel` — every sufficiently large exponent is a level,
  [Stacks, Tag 07MV].
* `Crystalline.isPAdicLevel_of_nilpotencyExponent_lt` — an explicit range of levels.
* `Crystalline.isDPMorphism_factorPow` — the canonical surjection `A/p^eA → A/p^mA` is a morphism
  of divided power rings.
* `Crystalline.pAdicLevelProj_comp_pAdicLevelTransition`,
  `Crystalline.pAdicLevelTransition_self` and `Crystalline.pAdicLevelTransition_comp` — the
  quotients form a tower of divided power rings under `(A, I, γ)`.

## Implementation notes

The quotient divided powers are `DividedPowers.quotientDividedPowers` of the divided power
algebra chapter, so that the tower built here is the one appearing in the inverse limit
description `DividedPowers.eventually_isDividedPowerCompletionLimit` of the completed divided
power ring.  The exponent `e` is carried as a parameter together with a proof that it is a level;
nothing is chosen out of the existence statement `Crystalline.exists_forall_isPAdicLevel`.

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Crystalline

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)

/-- **A finite divided power level.**  The ideal `(p^e)` is contained in the divided power ideal
`I` and is preserved by the divided powers `γ`. -/
def IsPAdicLevel (e : ℕ) : Prop :=
  DividedPowers.pAdicIdeal (A := A) p ^ e ≤ I ∧
    γ.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := A) p ^ e)

/-- **Stacks Project, Tag 07MV.**  For a divided power ring `(A, I, γ)` with `A` an algebra over
`ℤ_(p)` and `p` nilpotent in `A/I`, every sufficiently large exponent `e` has `(p^e) ⊆ I`
preserved by `γ`. -/
@[stacks 07MV "for e ≫ 0 the ideal (p^e) ⊆ I is preserved by γ"]
theorem exists_forall_isPAdicLevel [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A]
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) :
    ∃ N, ∀ e, N ≤ e → IsPAdicLevel I γ p e :=
  DividedPowers.exists_eventual_pAdicDPIdeal I γ p hp

/-- An exponent exceeding the nilpotency exponent of `p` modulo `I` and at least `2` is a finite
divided power level. -/
theorem isPAdicLevel_of_nilpotencyExponent_lt [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A]
    (hp : IsNilpotent (Ideal.Quotient.mk I (p : A))) {e : ℕ}
    (ht : DividedPowers.nilpotencyExponent I p hp < e) (he : 2 ≤ e) :
    IsPAdicLevel I γ p e :=
  ⟨(Ideal.pow_le_pow_right ht.le).trans
      (DividedPowers.pAdicIdeal_pow_nilpotencyExponent_le I p hp),
    DividedPowers.pAdicPow_isSubDPIdeal I γ p hp ht he⟩

namespace IsPAdicLevel

variable {I γ p} {e : ℕ}

/-- The ideal `(p^e)` meets `I` in a sub divided power ideal, which is the hypothesis under which
the divided powers descend to `A/p^eA`. -/
theorem inf_isSubDPIdeal (he : IsPAdicLevel I γ p e) :
    γ.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := A) p ^ e ⊓ I) := by
  simpa [inf_eq_left.mpr he.1] using he.2

end IsPAdicLevel

/-- The divided powers of `A/p^eA` are computed from those of `A` on the image of `I`. -/
theorem quotientDividedPowers_dpow_mk {e : ℕ} (he : IsPAdicLevel I γ p e) (n : ℕ) {a : A}
    (ha : a ∈ I) :
    (DividedPowers.quotientDividedPowers I γ p e he.1 he.2).dpow n
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e) a) =
      Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e) (γ.dpow n a) :=
  DividedPowers.Quotient.dpow_apply γ he.inf_isSubDPIdeal ha

/-- The quotient maps of two finite levels are compatible with the canonical surjection between
the two quotients. -/
theorem factorPow_comp_mk {m e : ℕ} (hme : m ≤ e) :
    (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := A) p) hme).comp
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e)) =
      Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ m) := by
  ext a
  rfl

/-- **The canonical surjection `A/p^eA → A/p^mA` is a morphism of divided power rings.**  Both
quotient divided power structures are induced by `γ`, and the surjection is compatible with the
two quotient maps out of `A`. -/
theorem isDPMorphism_factorPow {m e : ℕ} (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e)
    (hme : m ≤ e) :
    DividedPowers.IsDPMorphism (DividedPowers.quotientDividedPowers I γ p e he.1 he.2)
      (DividedPowers.quotientDividedPowers I γ p m hm.1 hm.2)
      (Ideal.Quotient.factorPow (DividedPowers.pAdicIdeal (A := A) p) hme) where
  ideal_comp := by
    rw [Ideal.map_map, factorPow_comp_mk (A := A) p hme]
  dpow_comp := by
    intro n x hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    rw [quotientDividedPowers_dpow_mk I γ p he n ha]
    exact quotientDividedPowers_dpow_mk I γ p hm n ha

/-- **Stacks Project, Tag 07MV.**  The divided power ring `(A/p^eA, I/p^eA, γ̄)` at a finite
divided power level `e`, of which the base `S_e = Spec(A/p^eA)` of the remark is the spectrum. -/
@[stacks 07MV "the divided power ring A/p^eA whose spectrum is the base S_e = Spec(A/p^eA)"]
noncomputable def pAdicLevelRing {e : ℕ} (he : IsPAdicLevel I γ p e) : DividedPowerRing.{u} :=
  .of (A ⧸ DividedPowers.pAdicIdeal (A := A) p ^ e)
    (I.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e)))
    (DividedPowers.quotientDividedPowers I γ p e he.1 he.2)

/-- **The projection onto a finite divided power level.**  The quotient map `A → A/p^eA` is a
morphism of divided power rings `(A, I, γ) → (A/p^eA, I/p^eA, γ̄)`. -/
noncomputable def pAdicLevelProj {e : ℕ} (he : IsPAdicLevel I γ p e) :
    DividedPowerRing.of A I γ ⟶ pAdicLevelRing I γ p he :=
  DividedPowers.DPMorphism.mk' (DividedPowers.Quotient.isDPMorphism γ he.inf_isSubDPIdeal)

/-- **The transition morphism of the tower of finite divided power levels.**  For `m ≤ e` the
canonical surjection `A/p^eA → A/p^mA` is a morphism of divided power rings. -/
noncomputable def pAdicLevelTransition {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) :
    pAdicLevelRing I γ p he ⟶ pAdicLevelRing I γ p hm :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_factorPow I γ p hm he hme)

/-- **The tower of finite divided power levels lies under `(A, I, γ)`.**  Projecting to level `e`
and then descending to level `m ≤ e` is projecting to level `m`. -/
@[reassoc]
theorem pAdicLevelProj_comp_pAdicLevelTransition {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) :
    pAdicLevelProj I γ p he ≫ pAdicLevelTransition I γ p hm he hme =
      pAdicLevelProj I γ p hm := by
  ext a
  rfl

/-- The transition morphism of a level to itself is the identity. -/
@[simp]
theorem pAdicLevelTransition_self {e : ℕ} (he : IsPAdicLevel I γ p e) :
    pAdicLevelTransition I γ p he he le_rfl = 𝟙 (pAdicLevelRing I γ p he) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The transition morphisms of the tower of finite divided power levels compose. -/
@[reassoc]
theorem pAdicLevelTransition_comp {k m e : ℕ} (hk : IsPAdicLevel I γ p k)
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hkm : k ≤ m) (hme : m ≤ e) :
    pAdicLevelTransition I γ p hm he hme ≫ pAdicLevelTransition I γ p hk hm hkm =
      pAdicLevelTransition I γ p hk he (hkm.trans hme) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end Crystalline

end
