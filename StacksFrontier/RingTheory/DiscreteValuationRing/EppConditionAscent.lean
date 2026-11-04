module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition

/-!
# Ascent of Epp's residue-field condition through a finite extension

Epp's theorem on elimination of wild ramification (Stacks Tag 09F9) is proved by induction on
extensions of discrete valuation rings, and the induction repeatedly replaces the ring upstairs by
a finite extension of it.  For that to be possible the residue-field hypothesis carried along has
to be stable under finite extension upstairs.  This file proves that
  `Stacks.EppTheorem.EppCondition` is.

## Why this is the right invariant

The algebraically-closed-residue-field case, Tag 09F8, is stated with a different hypothesis: that
the image of `κ_A` in `κ_B` is *exactly* `perfectCore κ_B p`.  That equality is **not** stable
under finite extension of `B` once `κ_A` is merely perfect rather than algebraically closed, and
the refutation is elementary: take `κ_A = 𝔽_p` and `κ_B = 𝔽_{p ^ 2}`.  Frobenius is bijective on a
finite field, so `perfectCore 𝔽_{p ^ 2} p = 𝔽_{p ^ 2}`, which strictly contains the image of
`𝔽_p`.  New constants enter through the *separable* part of the residue extension, exactly the part
the purely-inseparable replacements of the residue extension cannot reach.

Epp's condition — every element of `perfectCore κ_B p` is separable algebraic over `κ_A` — is
stable, and `EppCondition.of_module_finite` below is that stability.  Note that perfectness of
`κ_A` is a genuine hypothesis of the ascent rather than a consequence of Epp's condition:
`κ_A = κ_B = 𝔽_p(t)` satisfies Epp's condition (the perfect core of `𝔽_p(t)` is `𝔽_p`, which is
separable algebraic over `𝔽_p(t)`) while `𝔽_p(t)` is imperfect.

## Main results

* `mem_perfectCore_of_pow_eq`: the `p ^ n`-th roots of an element of the perfect core are
  themselves in the perfect core.  The perfect core is closed downwards under taking roots, which
  is what makes the separability argument below apply to every root at once.
* `isSeparable_of_mem_perfectCore`: for a finite extension `E / F`, every element of
  `perfectCore E p` is separable over `F`.  The perfect core cannot meet the purely inseparable
  part of a finite extension, because an element with `p ^ n`-th roots for every `n` survives
  raising to the exponent of `E` over `separableClosure F E`.
* `minpoly_coeff_mem_perfectCore_of_finite`: the version of
  `minpoly_coeff_mem_perfectCore` that needs only finiteness of `E / F` rather than separability,
  obtained by feeding the previous lemma the roots of the element.
* `isSeparable_of_mem_perfectCore_of_tower`: **the ascent, at the level of fields.**  For a tower
  `k ⊆ F ⊆ E` with `k` perfect and `E / F` finite, if every element of `perfectCore F p` is
  separable over `k` then so is every element of `perfectCore E p`.
* `Stacks.EppTheorem.EppCondition.of_module_finite`: **the ascent, at the level of local rings.**
  Epp's
  condition passes from `A → B` to `A → B'` for any module-finite local extension `B → B'`, given
  that `κ_A` is perfect.
* `Stacks.EppTheorem.perfectField_residueField_of_module_finite`: `κ_S` is perfect when `κ_R` is
  and `R → S` is a module-finite local homomorphism of local rings.

## Implementation notes

The proof of `isSeparable_of_mem_perfectCore_of_tower` does **not** try to exhibit the extension as
purely inseparable and appeal to
`PerfectField.surjective_algebraMap_of_isPurelyInseparable`; over a perfect `k` that would be
circular, since a purely inseparable extension of a perfect field is trivial and triviality is
what one is trying to prove.  Instead it shows that `x` is *algebraic* over `k` — the coefficients
of `minpoly F x` lie in `perfectCore F p`, hence are algebraic over `k` by hypothesis, and `x` is
integral over the subfield they generate — and then invokes perfectness of `k` only through
`PerfectField.separable_of_irreducible`, for which algebraicity is all that is needed.

Two auxiliary facts that the same repair needs are already in Mathlib and are deliberately not
restated here:

* transport of `PerfectField` along a `RingEquiv` is `PerfectField.of_ringEquiv`;
* `Module.Finite (ResidueField R) (ResidueField S)` for a module-finite local homomorphism is
  `IsLocalRing.ResidueField.finite_of_module_finite`, which is what makes
  `perfectField_residueField_of_module_finite` a one-liner.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09F8](https://stacks.math.columbia.edu/tag/09F8)
-/

@[expose] public section

open IsLocalRing

/-! ### The perfect core is closed under taking roots -/

/-- Every `p ^ n`-th root of an element of the perfect core again lies in the perfect core.

The witness for `y` being a `p ^ m`-th power is a `p ^ (m + n)`-th root of `x`; injectivity of the
`n`-th Frobenius iterate turns the identity of `p ^ n`-th powers into an identity of the roots. -/
theorem mem_perfectCore_of_pow_eq {E : Type*} [Field E] {p : ℕ} [ExpChar E p] {x y : E}
    (hx : x ∈ perfectCore E p) {n : ℕ} (hy : y ^ p ^ n = x) : y ∈ perfectCore E p := by
  refine mem_perfectCore_iff.mpr fun m => ?_
  obtain ⟨z, hz⟩ := mem_perfectCore_iff.mp hx (m + n)
  refine ⟨z, ?_⟩
  apply (iterateFrobenius E p n).injective
  show (z ^ p ^ m) ^ p ^ n = y ^ p ^ n
  rw [← pow_mul, ← pow_add, hz, hy]

/-! ### The perfect core of a finite extension is separable over the base -/

/-- **An element of the perfect core of a finite extension is separable over the base.**

The perfect core cannot meet the purely inseparable part of `E / F`: writing
`S = separableClosure F E`, the extension `E / S` is purely inseparable of some finite exponent
`e`, so `y ^ p ^ e ∈ S` for every `y : E`.  Taking `y` to be a `p ^ e`-th root of `x`, which exists
because `x` lies in the perfect core, puts `x` itself in `S`.

This is the ingredient that lets `minpoly_coeff_mem_perfectCore_of_finite` drop the separability
hypothesis of `minpoly_coeff_mem_perfectCore`. -/
theorem isSeparable_of_mem_perfectCore (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] {p : ℕ} [ExpChar E p] {x : E} (hx : x ∈ perfectCore E p) :
    IsSeparable F x := by
  let S := separableClosure F E
  have : Module.Finite S E := Module.Finite.right F S E
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp hx (IsPurelyInseparable.exponent S E)
  obtain ⟨z, hz⟩ := hy ▸ IsPurelyInseparable.exponent_def' S p y
  exact hz ▸ z.property

/-- The coefficients of the minimal polynomial over `F` of an element of `perfectCore E p` lie in
`perfectCore F p`, for `E / F` merely **finite**.

`minpoly_coeff_mem_perfectCore` assumes `E / F` separable; here separability of the single elements
that matter — the `p ^ n`-th roots of `x`, which lie in the perfect core by
`mem_perfectCore_of_pow_eq` — is supplied by `isSeparable_of_mem_perfectCore`. -/
theorem minpoly_coeff_mem_perfectCore_of_finite (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] {p : ℕ} [ExpChar F p] [ExpChar E p] {x : E}
    (hx : x ∈ perfectCore E p) (i : ℕ) : (minpoly F x).coeff i ∈ perfectCore F p := by
  refine mem_perfectCore_iff.mpr fun n => ?_
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp hx n
  refine ⟨(minpoly F y).coeff i, ?_⟩
  have h := minpoly.iterateFrobenius_of_isSeparable p n
    (isSeparable_of_mem_perfectCore F E (mem_perfectCore_of_pow_eq hx hy))
  rw [iterateFrobenius_def, hy] at h
  rw [h, Polynomial.coeff_map, iterateFrobenius_def]

/-! ### The ascent -/

/-- **Ascent of Epp's residue-field condition through a finite extension, for fields.**

Let `k ⊆ F ⊆ E` be a tower of fields with `k` perfect and `E / F` finite.  If every element of
`perfectCore F p` is separable algebraic over `k`, then every element of `perfectCore E p` is too.

The proof is in two halves.  Algebraicity: `x` is separable over `F`
(`isSeparable_of_mem_perfectCore`), the coefficients of `minpoly F x` lie in `perfectCore F p`
(`minpoly_coeff_mem_perfectCore_of_finite`) and are therefore algebraic over `k` by hypothesis, so
`x` is integral over the intermediate field of `E / k` those coefficients generate, which is itself
algebraic over `k`; `isIntegral_trans` concludes.  Separability: an algebraic element over a
perfect field is separable, since its minimal polynomial is irreducible and every irreducible
polynomial over a perfect field is separable.

Perfectness of `k` is used only in the second half, and only through
`PerfectField.separable_of_irreducible`.  It is not implied by the hypothesis on the perfect core:
`k = F = E = 𝔽_p(t)` satisfies the hypothesis and is imperfect. -/
theorem isSeparable_of_mem_perfectCore_of_tower (k F E : Type*) [Field k] [Field F] [Field E]
    [PerfectField k] [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Module.Finite F E] {p : ℕ} [ExpChar F p] [ExpChar E p]
    (hF : ∀ a : F, a ∈ perfectCore F p → IsSeparable k a)
    {x : E} (hx : x ∈ perfectCore E p) : IsSeparable k x := by
  have hxF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hcoeff : ∀ n : ℕ, IsIntegral k (algebraMap F E ((minpoly F x).coeff n)) := fun n =>
    (hF _ (minpoly_coeff_mem_perfectCore_of_finite F E hx n)).isIntegral.map
      (IsScalarTower.toAlgHom k F E)
  have halg : Algebra.IsAlgebraic k
      (IntermediateField.adjoin k (Set.range fun n : ℕ => algebraMap F E
        ((minpoly F x).coeff n))) :=
    IntermediateField.isAlgebraic_adjoin (by rintro y ⟨n, rfl⟩; exact hcoeff n)
  have hlifts : ∀ n : ℕ, ((minpoly F x).map (algebraMap F E)).coeff n ∈
      Set.range (algebraMap
        (IntermediateField.adjoin k (Set.range fun n : ℕ => algebraMap F E
          ((minpoly F x).coeff n))) E) := by
    intro n
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, IntermediateField.subset_adjoin k _ ⟨n, rfl⟩⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp ((Polynomial.lifts_iff_coeff_lifts _).mpr hlifts)
  have hfm : ((minpoly F x).map (algebraMap F E)).Monic := (minpoly.monic hxF).map _
  rw [← hq] at hfm
  have hqaeval : Polynomial.aeval x q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact minpoly.aeval F x
  exact PerfectField.separable_of_irreducible
    (minpoly.irreducible (isIntegral_trans x ⟨q, Polynomial.monic_map_iff.mp hfm, hqaeval⟩))

namespace Stacks.EppTheorem

/-- **The residue field upstairs of an *integral* local extension inherits perfectness.**

The generalisation of `perfectField_residueField_of_module_finite` from module-finite to integral,
which is what the complete perfect-residue case of Epp's theorem (obligation O1) needs: it replaces
its base by `integralClosure A K₁`, which is integral over `A` by construction and module-finite
over it only after the completeness argument has been run.

The residue extension is integral — a residue class is `residue S z`, and `z` is integral over `R`,
so its image is integral over `κ_R` — hence algebraic, and an algebraic extension of a perfect
field is perfect.

The integrality step alone is `Algebra.IsIntegral.residueField` in
`StacksFrontier.RingTheory.Henselian.QuasiFiniteRingMaps`; that module is a leaf whose import chain is
disproportionate here, so the three-line argument is repeated rather than imported. -/
theorem perfectField_residueField_of_isIntegral (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.IsIntegral R S] [PerfectField (ResidueField R)] : PerfectField (ResidueField S) := by
  have : Algebra.IsIntegral (ResidueField R) (ResidueField S) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨z, rfl⟩ := residue_surjective y
    exact ((Algebra.IsIntegral.isIntegral (R := R) z).map
      (IsScalarTower.toAlgHom R S (ResidueField S))).tower_top
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

/-- **The residue field upstairs of a module-finite local extension inherits perfectness.**

The module-finite special case of `perfectField_residueField_of_isIntegral`, kept because it is
what the callers in the repaired route to Tag 09F8 hold: they replace the base by a finite
extension and have to keep the perfectness hypothesis on the base residue field. -/
theorem perfectField_residueField_of_module_finite (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] [PerfectField (ResidueField R)] : PerfectField (ResidueField S) :=
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  perfectField_residueField_of_isIntegral R S

/-- **Epp's condition restricts to an intermediate ring.**

For a tower `A → B → C` of local rings with local structure maps, Epp's condition for `A → C`
implies Epp's condition for `A → B`.  This is the direction `EppCondition.of_module_finite` does
not give, and it needs **no** finiteness and **no** perfectness: a `p`-power root in `κ_B` maps to
one in `κ_C`, so the perfect core maps into the perfect core, and separability over `κ_A` descends
along `κ_B → κ_C` by `IsSeparable.tower_bot`.

Its use is the Cohen-ring interposition of Tag 09F9's proof, where an intermediate complete
discrete valuation ring `Λ` is inserted between `A` and `B` so that `B` becomes module-finite over
it.  Epp's condition is given for `A → B`, and what Tag 09F8 (and its perfect-residue analogue)
consumes is the condition at the *middle* of the tower — which is this lemma. -/
theorem EppCondition.of_tower {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] [IsLocalHom (algebraMap A C)]
    [IsScalarTower A B C]
    {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField C) p]
    (h : EppCondition A C p) : EppCondition A B p := by
  intro y hy
  have hmap : algebraMap (ResidueField B) (ResidueField C) y ∈ perfectCore (ResidueField C) p := by
    refine mem_perfectCore_iff.mpr fun n => ?_
    obtain ⟨z, hz⟩ := mem_perfectCore_iff.mp hy n
    exact ⟨algebraMap (ResidueField B) (ResidueField C) z, by rw [← map_pow, hz]⟩
  exact IsSeparable.tower_bot (h _ hmap)

/-- **Ascent of Epp's condition through a module-finite local extension upstairs.**

If `B → B'` is a module-finite local homomorphism of local rings and `κ_A` is perfect, then Epp's
condition for `A → B` gives Epp's condition for `A → B'`.

This is the stability property the equality hypothesis of Tag 09F8 lacks: with
`κ_A = 𝔽_p ⊆ κ_B = 𝔽_p` and `κ_{B'} = 𝔽_{p ^ 2}`, the image of `κ_A` in `κ_{B'}` is strictly
smaller than `perfectCore κ_{B'} p = 𝔽_{p ^ 2}`, while Epp's condition survives — every element of
`𝔽_{p ^ 2}` is separable algebraic over `𝔽_p`. -/
theorem EppCondition.of_module_finite {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing B']
    [Algebra A B] [Algebra B B'] [Algebra A B']
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B B')] [IsLocalHom (algebraMap A B')]
    [IsScalarTower A B B'] [Module.Finite B B'] [PerfectField (ResidueField A)]
    {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField B') p]
    (h : EppCondition A B p) : EppCondition A B' p := fun _ hx =>
  isSeparable_of_mem_perfectCore_of_tower (ResidueField A) (ResidueField B) (ResidueField B') h hx

/-- **Epp's condition ascends through a finite square of local rings.**

Suppose `A → B`, `A' → B'` form a commuting square, with `B' / B` module-finite.  If the
residue field of `A` is perfect, then Epp's condition for `A → B` implies Epp's condition for
`A' → B'`.

The target ascent is `EppCondition.of_module_finite`.  Enlarging the base from `κ_A` to
`κ_A'` then preserves separability: an element separable over the smaller field remains
separable over every intermediate base field.  This is the finite-square form used when Epp's
degree-`p` argument is restarted after a finite base change. -/
theorem EppCondition.of_finite_square
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A B)]
    [IsLocalHom (algebraMap A B')] [IsLocalHom (algebraMap A' B')]
    [IsLocalHom (algebraMap B B')]
    [IsScalarTower A A' B'] [IsScalarTower A B B'] [Module.Finite B B']
    [PerfectField (ResidueField A)]
    {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField B') p]
    (h : EppCondition A B p) : EppCondition A' B' p := fun x hx =>
  (h.of_module_finite x hx).tower_top (ResidueField A')

/-- **Epp's condition ascends, across a finite square, for a whole family at once.**

The family form of `EppCondition.of_finite_square`: one base change `A → A'`, a family of members
`B i` each going to `B' i` with `B' i / B i` module-finite, and Epp's condition at every member
transports to every post-base-change member.

This is what makes the *second* layer of a shared-`K₂` tower legitimate. The tower's two layers
cannot be chosen in parallel: the first is an orbit extension, which is totally ramified, so a
uniformizer of the post-orbit base is **not** the image of a uniformizer of the old base, and the
Artin--Schreier classes the second layer has to split are therefore not the ones the normalization
produced downstairs. They have to be recomputed over the new base, which means re-running the
constant-numerator preparation there — and that is sound exactly because its input, Epp's
condition, ascends. The preparation lemmas themselves need no change, being stated over an
arbitrary base with the tower hypotheses as instance arguments.

**`PerfectField (ResidueField A)` is not removable.** It is inherited from
`isSeparable_of_mem_perfectCore_of_tower`, where perfectness of the bottom field is used through
`PerfectField.separable_of_irreducible`, and it is *not* implied by the hypothesis on the perfect
core: `k = F = E = 𝔽_p(t)` satisfies that hypothesis and is imperfect. So this ascent is available
in the setting where the base residue field is perfect — which after the Cohen reduction is
`perfectCore κ_B p`, perfect by `perfectCore.perfectField` — and is not available in general. A
caller outside that setting has no re-entry and must not assume one. -/
theorem EppCondition.forall_of_finite_square
    {ι : Type*} {A A' : Type*} {B B' : ι → Type*}
    [CommRing A] [CommRing A'] [∀ i, CommRing (B i)] [∀ i, CommRing (B' i)]
    [IsLocalRing A] [IsLocalRing A'] [∀ i, IsLocalRing (B i)] [∀ i, IsLocalRing (B' i)]
    [Algebra A A'] [∀ i, Algebra A (B i)] [∀ i, Algebra A (B' i)]
    [∀ i, Algebra A' (B' i)] [∀ i, Algebra (B i) (B' i)]
    [IsLocalHom (algebraMap A A')]
    [∀ i, IsLocalHom (algebraMap A (B i))]
    [∀ i, IsLocalHom (algebraMap A (B' i))]
    [∀ i, IsLocalHom (algebraMap A' (B' i))]
    [∀ i, IsLocalHom (algebraMap (B i) (B' i))]
    [∀ i, IsScalarTower A A' (B' i)] [∀ i, IsScalarTower A (B i) (B' i)]
    [∀ i, Module.Finite (B i) (B' i)]
    [PerfectField (ResidueField A)]
    {p : ℕ} [∀ i, ExpChar (ResidueField (B i)) p] [∀ i, ExpChar (ResidueField (B' i)) p]
    (h : ∀ i, EppCondition A (B i) p) : ∀ i, EppCondition A' (B' i) p :=
  fun i => (h i).of_finite_square

end Stacks.EppTheorem
