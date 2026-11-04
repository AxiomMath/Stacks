module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition

/-!
# Where the descent clause of Tag 09ET breaks, and what Epp's hypothesis supplies

Tag 09ET produces, for an extension of discrete valuation rings `A → B`, a commutative square
`A → A'`, `B → B'` of extensions of discrete valuation rings whose fraction-field extensions
`K' / K` and `L' / L` are separable algebraic and whose residue fields are the separable algebraic
closures of `κ_A` and `κ_B`, and asserts in its clause (3) that a weak solution for `A' → B'`
produces one for `A → B`.  That clause is false: there is an `A ⊂ B` with no finite weak
solution at all, while *every* square permitted by clauses (1) and (2) admits one upstairs.
Tag 09ET is deliberately not formalized, and this file neither states nor proves it,
conditionally or otherwise.

What this file does is isolate the single sentence of the Stacks argument that fails, prove the
algebra that certifies the failure, and prove the one thing Epp's hypothesis
(`Stacks.EppTheorem.EppCondition`) genuinely supplies at that point.  The conditional descent
under Epp's hypothesis is **not** completed here.  The
analysis below says precisely what is still missing, and why the residue-field hypothesis is not
by itself enough to close it.

## The failing step, exactly

The Stacks proof of clause (3) descends a weak solution `K'₁ / K'` for `A' → B'` as follows.
`A'` is a filtered colimit of finite étale `A`-algebras, so `K'₁ = K' ⊗_F K₁` for some finite
étale `A ⊂ A'₁` with fraction field `F ⊆ K'` and some finite `K₁ / F`.  Then:

* **(i)** `B' ⊗_A A'₁` is a finite product of rings isomorphic to `B'`, because `A'₁ / A` is
  finite étale and `B'` is strictly henselian.  *This is correct.*
* **(ii)** "Hence `L' ⊗_K K₁ = L' ⊗_K F ⊗_F K₁` is a finite product of rings isomorphic to
  `L' ⊗_{K'} K'₁`."  **This is the false step.**

The product in (i) is a product of copies of `B'` *as rings*, but the copies carry pairwise
distinct `A'₁`-algebra structures: they are indexed by the `A`-algebra maps `A'₁ → B'`,
equivalently — passing to fraction fields — by the `K`-algebra maps `τ : F → L'`, and the `τ`-th
copy receives `F` through `τ`.  Writing `L'_τ` for `L'` carrying the `F`-structure `τ`, what (i)
gives is

`L' ⊗_K F ≅ ∏_{τ : F →ₐ[K] L'} L'_τ`,  hence  `L' ⊗_K K₁ ≅ ∏_τ (L'_τ ⊗_F K₁)`,

a product of `[F : K]` factors.  Only the factor at the *distinguished* `τ₀ : F ⊆ K' ⊆ L'` is
`L' ⊗_{K'} K'₁`, and the hypothesis that `K'₁` is a weak solution for `A' → B'` constrains that
factor alone.  The remaining `[F : K] - 1` factors are the Galois conjugates, and the hypothesis
says nothing whatsoever about them.  Step (ii) silently identifies `L'_τ` with `L'_{τ₀}`; that
identification is legitimate exactly when `τ = ρ ∘ τ₀` for some `K`-automorphism `ρ` of `L'`,
since then `ρ` carries the `τ₀`-factor onto the `τ`-factor.

The declarations `conjugateProjection`, `conjugateFactor` and `conjugateFactor_injective` below
are that decomposition in the only form needed to certify the gap: the factors of `L ⊗[K] F` are
separated by the `K`-algebra maps `F → L`, so there are at least as many of them as there are
such maps, one per conjugate.  `mem_ker_conjugateProjection_congr` is the transport along a
`K`-automorphism of `L`, i.e. the mechanism step (ii) needs and does not have.

In the counterexample this is where the argument dies, and the data are explicit.  There
`κ_B = f̄` is already algebraically closed, so `B' = B` and `L' = L₁`; `A' = A^{sh}` has fraction
field `K' = F₀ = K^{nr}`; the descended data are `F = f((t))`, `A'₁ = f[[t]]` (finite étale over
`A = k[[t]]` because `f / k` is separable quadratic) and `K₁ = F(z₁) = E₁`.  There are exactly two
`K`-algebra maps `F → L₁`, the inclusion `τ₀` and its twist by the nontrivial element `σ` of
`Gal(f / k)`, so `L₁ ⊗_K E₁` has two conjugate blocks, `L₁ ⊗_F E₁` and `(L₁)_σ ⊗_F E₁`.  The twist
`(L₁)_σ` is `F`-isomorphic to `L₂`, because `σ` extended to the algebraic closure carries `L₁` to
`L₂`; and `σ` does **not** extend to an automorphism of `L₁`, precisely because `L₂ ≠ L₁`.  The
upstairs weak solution gives `e(L₁E₁ / E₁) = 1`, while §4 of the counterexample note shows that
`e(L₂E₁ / E₁) = 1` is then impossible.  So `E₁` is a weak solution for `A' → B'` and not for
`A → B`, which is exactly the failure of clause (3).

Two corollaries of this diagnosis, matching the repair plan.  The failure is not caused by exotic
ramified horizontal arrows: the square above is the strict-henselization square.  And it cannot be
repaired by enlarging `K₁`, because `e = 1` at the conjugate factor is not merely unproved but
false, and weak solutions are not stable under finite enlargement.

## What a correct proof must control, and what would suffice

A correct descent must bound the ramification of *every* factor `L'_τ ⊗_F K₁`, not only the
distinguished one.  Two sufficient mechanisms are available in principle.

* **Conjugacy of the factors.**  If every `K`-algebra map `τ : F → L'` has the form `ρ ∘ τ₀` for
  some `ρ ∈ Aut(L' / K)`, then all factors are carried onto one another by isometries, one
  ramification index is all of them, and the step goes through;
  `mem_ker_conjugateProjection_congr` is that transport.  Since `A'₁ / A` is finite étale, the
  maps `τ` correspond bijectively to the `κ_A`-algebra maps `κ_{A'₁} → κ_{B'}`, whereas the
  available `ρ` come from `Aut(B' / B) = Gal(κ_B^{sep} / κ_B)`.  So the mechanism is available for
  every `F` when

  **(†)** the separable algebraic closure of `κ_A` inside `κ_B` is `κ_A` itself,

  for then `Gal(κ_B^{sep} / κ_B)` is transitive on `Hom_{κ_A}(κ_{A'₁}, κ_B^{sep})`.  The
  counterexample violates (†) as loudly as possible: `κ_A = k`, `κ_B = f̄ ⊇ f`, and the two
  `k`-embeddings of the separable quadratic extension `f` into `f̄` are fixed by the trivial group
  `Gal(f̄ / f̄)`, hence lie in two different orbits.
* **Normality of the solution over `K`.**  If the descended `K₁ / K` is normal, Tag 09EU
  (`IsDiscreteValuationRing.normal_extension_acts_transitively_on_maximalSpectrum_integralClosure`,
  in `StacksFrontier/RingTheory/DiscreteValuationRing/WeakSolution.lean`) makes `Aut(K₁ / K)` act
  transitively on the maximal ideals of `B₁`, so again one ramification index is all of them.
  This is how the proof of 09F9 handles conjugates elsewhere.  It is *not* available here: the
  normal closure of `K₁ / K` need not be a weak solution, which is the content of §4 of the
  counterexample note.

## What Epp's hypothesis supplies, and what it does not

Epp's hypothesis `Stacks.EppTheorem.EppCondition A B p` says every element of `⋂_{n ≥ 1} κ_B^{p^n}`
  is
separable algebraic over `κ_A`.  Its effect at the failing step is at the residue level, and it is
exactly this: after the enlargement the perfect core upstairs lies inside `κ_{A'} = κ_A^{sep}`
(`Stacks.EppTheorem.perfectCore_residueField_le_of_isSepClosure`), a field that is *normal* over
  `κ_A`,
and therefore the perfect core is stable under every `κ_A`-automorphism of `κ_{A'}`.  That is
`Stacks.EppTheorem.EppCondition.mem_perfectCore_residueField_of_aut` below, and the hypothesis is
  used
essentially: without it an element of the perfect core need not lie in `κ_{A'}` at all, and there
is then no automorphism to apply to it.  This is the property the counterexample violates in the
sharpest possible way — there `a^{1/2}` lies in the perfect core `f̄` of `κ_B` while its
`k`-conjugate `b^{1/2}` does not lie in `k^{sep}`, and the two inseparable towers
`Q₁ = R(b^{1/2^∞})` and `Q₂ = R(a^{1/2^∞})` that this produces are exactly what makes `L₁ ≠ L₂`.

It does **not** follow that Epp's hypothesis restores conjugacy.  Epp's hypothesis and (†) are
logically independent: for `κ_A = 𝔽_p(u)` and `κ_B` any nontrivial finite separable extension of
it, the perfect core of `κ_B` is a finite field, so Epp's hypothesis holds trivially, while (†)
fails.  So the conjugacy mechanism does not become available merely by assuming Epp's hypothesis,
and the conditional descent of Route 1 is not proved here.  Nothing below claims it.

The precise statement that remains open is:

**(★)** Let `A ⊂ B` satisfy `EppCondition A B p`, let `A → A'`, `B → B'` be a square as in clauses
(1) and (2) of 09ET, let `F / K` be finite separable arising from a finite étale `A'₁ ⊆ A'`, and
let `K₁ / F` be finite with `K' ⊗_F K₁` a weak solution for `A' → B'`.  Then for every
`τ : F →ₐ[K] L'`, every maximal ideal of the integral closure of `B` in `(L'_τ ⊗_F K₁)_red` has
ramification index one over the integral closure of `A` in `K₁`.

(★) is what step (ii) asserts without proof, and what the counterexample refutes once
`EppCondition` is dropped.  The analysis above says a proof of (★) cannot go through conjugacy
alone.  It also suggests where to go instead: Route 2 of the repair plan, Epp's own finite
*unramified* base change, is already built in
`StacksFrontier/RingTheory/DiscreteValuationRing/EppUnramifiedBaseChange.lean`; it absorbs the
perfect core into `κ_A` over a *finite* extension and so needs no descent along an infinite
separable closure at all.  An intermediate possibility not pursued here is to replace `A` first by
the finite weakly unramified extension realising the separable algebraic closure of `κ_A` inside
`κ_B`, when that closure is finite over `κ_A`: this makes (†) hold and hence makes the conjugacy
mechanism available.

## Main definitions

* `Stacks.WeakSolution.Obstruction.conjugateProjection`: for a `K`-algebra map `τ : F → L`, the
  `L`-algebra map
  `L ⊗[K] F → L` cutting out the conjugate factor indexed by `τ`.
* `Stacks.WeakSolution.Obstruction.conjugateFactor`: the corresponding maximal ideal of `L ⊗[K] F`.

## Main results

* `Stacks.WeakSolution.Obstruction.conjugateFactor_injective`: distinct `K`-algebra maps `F → L`
  cut out distinct
  maximal ideals of `L ⊗[K] F`.  This is the statement that step (ii) of the Stacks proof of
  Tag 09ET (3) overlooks: the distinguished compositum is one factor among `[F : K]` conjugates.
* `Stacks.WeakSolution.Obstruction.conjugateProjection_apply_congr` and
  `Stacks.WeakSolution.Obstruction.mem_ker_conjugateProjection_congr`: a `K`-automorphism `ρ` of
    `L` carries the factor
  indexed by `τ` onto the factor indexed by `ρ ∘ τ`.  This is the conjugacy transport a correct
  descent needs.
* `Stacks.EppTheorem.mem_perfectCore_of_isSepClosed_aut` and
  `Stacks.EppTheorem.EppCondition.mem_perfectCore_residueField_of_aut`: under Epp's hypothesis the
  perfect core of the residue field upstairs is stable under every automorphism of the base
  residue field over its own base.  This is the essential use of Epp's hypothesis at the failing
  step, and the property the counterexample violates.

## References

* [The Stacks Project, Tag 09ET](https://stacks.math.columbia.edu/tag/09ET)
* [The Stacks Project, Tag 09EU](https://stacks.math.columbia.edu/tag/09EU)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.WeakSolution.Obstruction

section ConjugateFactors

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]

/-- The conjugate factor of `L ⊗[K] F` indexed by a `K`-algebra map `τ : F → L`, presented as the
`L`-algebra map `L ⊗[K] F → L` sending `x ⊗ y` to `x * τ y`.

When `F / K` is finite separable and `L` splits it, `L ⊗[K] F` is a product of `[F : K]` copies of
`L`, and these maps are its projections.  The point of indexing them by `τ` is that the `i`-th
copy carries `F` through the `i`-th embedding rather than through a single distinguished one:
`conjugateProjection τ (1 ⊗ y) = τ y`.  Step (ii) of the Stacks proof of Tag 09ET (3) treats the
copies as if they all carried the distinguished embedding, which is where that proof fails. -/
noncomputable def conjugateProjection (τ : F →ₐ[K] L) : L ⊗[K] F →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) τ fun _ _ => Commute.all _ _

/-- The conjugate projection indexed by `τ` sends `x ⊗ y` to `x * τ y`. -/
@[simp]
theorem conjugateProjection_tmul (τ : F →ₐ[K] L) (x : L) (y : F) :
    conjugateProjection τ (x ⊗ₜ[K] y) = x * τ y :=
  rfl

/-- The `F`-algebra structure carried by the conjugate factor indexed by `τ` is `τ` itself. -/
@[simp]
theorem conjugateProjection_includeRight (τ : F →ₐ[K] L) (y : F) :
    conjugateProjection τ (Algebra.TensorProduct.includeRight y) = τ y := by
  simp

/-- Each conjugate projection restricts to the identity on the left factor. -/
@[simp]
theorem conjugateProjection_algebraMap (τ : F →ₐ[K] L) (x : L) :
    conjugateProjection τ (algebraMap L (L ⊗[K] F) x) = x := by
  simp

/-- Each conjugate projection is surjective, so its kernel is a maximal ideal. -/
theorem conjugateProjection_surjective (τ : F →ₐ[K] L) :
    Function.Surjective (conjugateProjection τ) := fun x =>
  ⟨algebraMap L (L ⊗[K] F) x, conjugateProjection_algebraMap τ x⟩

/-- The maximal ideal of `L ⊗[K] F` cut out by the conjugate factor indexed by `τ`. -/
noncomputable def conjugateFactor (τ : F →ₐ[K] L) : MaximalSpectrum (L ⊗[K] F) where
  asIdeal := RingHom.ker (conjugateProjection τ)
  isMaximal := RingHom.ker_isMaximal_of_surjective _ (conjugateProjection_surjective τ)

/-- The ideal of the conjugate factor indexed by `τ` is the kernel of the conjugate projection
indexed by `τ`. -/
@[simp]
theorem conjugateFactor_asIdeal (τ : F →ₐ[K] L) :
    (conjugateFactor τ).asIdeal = RingHom.ker (conjugateProjection τ) :=
  rfl

/-- Two `K`-algebra maps `F → L` with the same conjugate factor are equal.

The proof is that a surjective `L`-algebra map to `L` is determined by its kernel: for any `z`,
the element `z - (Φ z)` of `L ⊗[K] F` lies in `ker Φ`. -/
theorem eq_of_ker_conjugateProjection_eq {τ₁ τ₂ : F →ₐ[K] L}
    (h : RingHom.ker (conjugateProjection τ₁) = RingHom.ker (conjugateProjection τ₂)) :
    τ₁ = τ₂ := by
  have key : ∀ z : L ⊗[K] F, conjugateProjection τ₂ z = conjugateProjection τ₁ z := by
    intro z
    have h1 : z - algebraMap L (L ⊗[K] F) (conjugateProjection τ₁ z) ∈
        RingHom.ker (conjugateProjection τ₁) := by
      rw [RingHom.mem_ker, map_sub, conjugateProjection_algebraMap, sub_self]
    rw [h, RingHom.mem_ker, map_sub, conjugateProjection_algebraMap] at h1
    exact sub_eq_zero.mp h1
  ext y
  have hy := key (1 ⊗ₜ[K] y)
  simp only [conjugateProjection_tmul, one_mul] at hy
  exact hy.symm

/-- **Distinct `K`-embeddings of `F` into `L` cut out distinct factors of `L ⊗[K] F`.**

This is the fact that step (ii) of the Stacks proof of Tag 09ET (3) overlooks.  For `F / K` finite
separable, split by `L`, the number of these maps is `[F : K]` (`AlgHom.card_of_splits`), so
`L ⊗[K] F` has `[F : K]` distinct factors; a weak solution upstairs controls the one indexed by
the distinguished embedding `F ⊆ K' ⊆ L'` and no other. -/
theorem conjugateFactor_injective :
    Function.Injective (conjugateFactor : (F →ₐ[K] L) → MaximalSpectrum (L ⊗[K] F)) :=
  fun _ _ h => eq_of_ker_conjugateProjection_eq (congrArg MaximalSpectrum.asIdeal h)

/-- A `K`-automorphism `ρ` of `L` intertwines the conjugate projection at `τ` with the conjugate
projection at `ρ ∘ τ`, through the automorphism `ρ ⊗ id` of `L ⊗[K] F`.

This is the conjugacy transport that a correct proof of the descent clause of Tag 09ET needs and
that the Stacks argument assumes without comment: when `τ` differs from the distinguished
embedding by an automorphism of `L` over `K`, the two factors are carried onto one another, and a
single ramification index accounts for both. -/
theorem conjugateProjection_apply_congr (ρ : L ≃ₐ[K] L) (τ : F →ₐ[K] L) (z : L ⊗[K] F) :
    conjugateProjection ((ρ : L →ₐ[K] L).comp τ)
        (Algebra.TensorProduct.congr ρ (AlgEquiv.refl : F ≃ₐ[K] F) z) =
      ρ (conjugateProjection τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The factor indexed by `ρ ∘ τ` is the image of the factor indexed by `τ` under `ρ ⊗ id`. -/
theorem mem_ker_conjugateProjection_congr (ρ : L ≃ₐ[K] L) (τ : F →ₐ[K] L) (z : L ⊗[K] F) :
    Algebra.TensorProduct.congr ρ (AlgEquiv.refl : F ≃ₐ[K] F) z ∈
        RingHom.ker (conjugateProjection ((ρ : L →ₐ[K] L).comp τ)) ↔
      z ∈ RingHom.ker (conjugateProjection τ) := by
  rw [RingHom.mem_ker, RingHom.mem_ker, conjugateProjection_apply_congr]
  exact ⟨fun h => ρ.injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

end ConjugateFactors

end Stacks.WeakSolution.Obstruction

namespace Stacks.EppTheorem

section PerfectCoreStability

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
  [IsSepClosed K] {p : ℕ} [ExpChar L p]

/-- **Epp's hypothesis makes the perfect core upstairs stable under the base Galois action.**

Suppose `K` is separably closed, sits inside `L`, and every element of the perfect core of `L` is
separable algebraic over `K` — this last is Epp's hypothesis for the enlarged square, which
`Stacks.EppTheorem.EppCondition.of_isSepClosure` derives from Epp's hypothesis for the original
one. Then an element of `K` whose image lies in the perfect core of `L` keeps that property after
applying any automorphism of `K` over a subfield `k`.

The hypothesis is used essentially and exactly once: it puts every `p ^ n`-th root of the given
element back inside `K`, so that `σ` can be applied to the root at all.  Without it the roots live
only in `L`, `σ` does not act on them, and the conclusion fails — this is precisely the situation
in the counterexample to clause (3) of Tag 09ET, where `a ^ (1 / 2)` lies in the perfect core
`f̄` of `κ_B` but not in `κ_{A'} = k^{sep}`, and the `k`-conjugate `b ^ (1 / 2)` generates a
different inseparable tower. -/
theorem mem_perfectCore_of_isSepClosed_aut
    (hcore : ∀ x : L, x ∈ perfectCore L p → IsSeparable K x)
    (σ : K ≃ₐ[k] K) {x : K} (hx : algebraMap K L x ∈ perfectCore L p) :
    algebraMap K L (σ x) ∈ perfectCore L p := by
  have hrange : perfectCore L p ≤ (algebraMap K L).fieldRange :=
    perfectCore_le_fieldRange hcore
  rw [mem_perfectCore_iff]
  intro n
  obtain ⟨y, hymem, hy⟩ := exists_mem_perfectCore_pow_eq hx n
  obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp (hrange hymem)
  have hwx : w ^ p ^ n = x := by
    apply (algebraMap K L).injective
    rw [map_pow, hw, hy]
  refine ⟨algebraMap K L (σ w), ?_⟩
  have hσ : σ w ^ p ^ n = σ x := by rw [← map_pow, hwx]
  rw [← map_pow, hσ]

/-- The stability of `mem_perfectCore_of_isSepClosed_aut` packaged as a statement about the
subfield of `K` cut out by the perfect core of `L`. -/
theorem mapsTo_comap_perfectCore
    (hcore : ∀ x : L, x ∈ perfectCore L p → IsSeparable K x) (σ : K ≃ₐ[k] K) :
    Set.MapsTo σ (((perfectCore L p).comap (algebraMap K L) : Subfield K) : Set K)
      (((perfectCore L p).comap (algebraMap K L) : Subfield K) : Set K) := by
  intro x hx
  simp only [SetLike.mem_coe, Subfield.mem_comap] at hx ⊢
  exact mem_perfectCore_of_isSepClosed_aut hcore σ hx

end PerfectCoreStability

section ResidueFields

open IsLocalRing

variable {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
  [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B] [Algebra A B']
  [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap B B')]
  [IsLocalHom (algebraMap A' B')] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A B')]
  [IsScalarTower A A' B'] [IsScalarTower A B B']
  [IsSepClosure (ResidueField A) (ResidueField A')]
  [IsSepClosure (ResidueField B) (ResidueField B')]
  {p : ℕ} [ExpChar (ResidueField B) p] [ExpChar (ResidueField B') p]

/-- **Epp's hypothesis, transported to the enlarged square, makes the perfect core upstairs
stable under `Aut(κ_{A'} / κ_A)`.**

This is the form in which the previous lemma bears on the descent clause of Tag 09ET.  The square
is the one 09ET produces: the upper residue fields are separable algebraic closures of the lower
ones.  Epp's hypothesis for `A → B` gives it for `A' → B'`
(`Stacks.EppTheorem.EppCondition.of_isSepClosure`), hence the perfect core of `κ_{B'}` lies inside
`κ_{A'}`, and `κ_{A'} = κ_A^{sep}` is normal over `κ_A`; so the base Galois group acts on the
perfect core.

The counterexample to clause (3) of Tag 09ET fails this at the first step:
there `κ_B = f̄` is perfect, so its perfect core is all of `f̄`, which is not separable algebraic
over `κ_A = k`, and the perfect core is not contained in `κ_{A'} = k^{sep}` at all.  That failure
is what produces the two non-conjugate inseparable towers `Q₁` and `Q₂` and hence the two
non-isomorphic conjugate tensor factors of
  `Stacks.WeakSolution.Obstruction.conjugateFactor_injective`.

This lemma is *not* a proof of Route 1: see the module docstring.  Stability of the perfect core
under the base Galois group is a residue-level statement, and the conjugacy that the descent needs
is a statement about the fields `L'_τ`, which it does not imply. -/
theorem EppCondition.mem_perfectCore_residueField_of_aut (h : EppCondition A B p)
    (σ : ResidueField A' ≃ₐ[ResidueField A] ResidueField A') {x : ResidueField A'}
    (hx : algebraMap (ResidueField A') (ResidueField B') x ∈ perfectCore (ResidueField B') p) :
    algebraMap (ResidueField A') (ResidueField B') (σ x) ∈ perfectCore (ResidueField B') p := by
  have : IsSepClosed (ResidueField A') := IsSepClosure.sep_closed (ResidueField A)
  exact mem_perfectCore_of_isSepClosed_aut
    (EppCondition.of_isSepClosure (A := A) (B := B) h) σ hx

end ResidueFields

end Stacks.EppTheorem
