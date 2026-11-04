module

public import Mathlib.Algebra.Polynomial.Eval.Subring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The perfect core of a field

For a field `F` of exponential characteristic `p`, the *perfect core* is the subfield

$$\operatorname{perfectCore} F p = \bigcap_{n \ge 1} F^{p^n},$$

the largest perfect subfield of `F`. It is the field Epp's theorem on elimination of wild
ramification is stated in terms of: the hypothesis there is that every element of the perfect
core of the residue field upstairs is separable algebraic over the residue field downstairs.

This is not Mathlib's `perfectClosure F E`, which is the *relative* purely inseparable closure
of `F` in an extension `E`. The perfect core is absolute: it is a subfield of `F` itself, defined
as the infimum of the ranges of the iterated Frobenius endomorphisms, and it is the object
Kuhlmann calls the "largest perfect subfield".

## Main definitions

* `perfectCore F p`: the perfect core, as a `Subfield F`.

## Main results

* `mem_perfectCore_iff` and `mem_perfectCore_iff_forall_one_le`: membership is being a `p ^ n`-th
  power for every `n` (equivalently, for every `n ≥ 1`, which is the form Epp's hypothesis takes).
* `exists_pow_eq_and_not_pow_of_notMem_perfectCore`: an element outside the perfect core has a
  finite Frobenius depth — a last stage at which it is a `p`-power. This is Kuhlmann's `ν_x`, and
  it is what the tame/wild split of the degree-`p` step needs; taken against the perfect core it
  is free of any residue-field hypothesis.
* `perfectCore.perfectRing` and `perfectCore.perfectField`: the perfect core is perfect. This is
  what makes it the *largest* perfect subfield: `mem_perfectCore_of_perfectRing` shows every
  perfect subfield lands inside it.
* `perfectCore.isAlgClosed`: the perfect core of a *separably closed* field is algebraically
  closed. This is the reason the proof of Epp's theorem first enlarges the residue fields to
  their separable closures — it is what turns the perfect core into a field to which the
  algebraically-closed-residue-field case of the theorem applies.
* `perfectCore.isAlgClosed_of_exists_aeval_eq_zero` and
  `perfectCore.isAlgClosed_iff_exists_aeval_eq_zero`: separable closedness of `F` is *more* than
  that conclusion needs. All that is required — and it is equivalent to the conclusion — is that
  every separable polynomial with coefficients in the perfect core have a root somewhere in `F`.
* `minpoly_coeff_mem_perfectCore`: for a separable extension `E / F`, the minimal polynomial over
  `F` of an element of the perfect core of `E` has all its coefficients in the perfect core of
  `F`. This is the mechanism by which Epp's hypothesis transfers *upward* along a separable
  enlargement of the residue fields, via `perfectCore_mem_range_of_separable_square`.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

variable (F : Type*) [Field F] (p : ℕ) [ExpChar F p]

/-- The perfect core `⋂_{n ≥ 1} F ^ (p ^ n)` of a field `F` of exponential characteristic `p`,
namely its largest perfect subfield, realised as the infimum of the ranges of the iterated
Frobenius endomorphisms.

In characteristic zero (`p = 1`) every Frobenius iterate is the identity and the perfect core is
all of `F`. -/
def perfectCore : Subfield F :=
  ⨅ n : ℕ, (iterateFrobenius F p n).fieldRange

variable {F p}

/-- An element lies in the perfect core exactly when it is a `p ^ n`-th power for every `n`. -/
theorem mem_perfectCore_iff {x : F} :
    x ∈ perfectCore F p ↔ ∀ n : ℕ, ∃ y : F, y ^ p ^ n = x := by
  simp only [perfectCore, Subfield.mem_iInf, RingHom.mem_fieldRange, iterateFrobenius_def]

/-- Epp's form of membership in the perfect core: being a `p ^ n`-th power for every `n ≥ 1`.

The restriction to `n ≥ 1` is harmless, since `n = 0` is witnessed by the element itself. -/
theorem mem_perfectCore_iff_forall_one_le {x : F} :
    x ∈ perfectCore F p ↔ ∀ n : ℕ, 1 ≤ n → ∃ y : F, y ^ p ^ n = x := by
  rw [mem_perfectCore_iff]
  refine ⟨fun h n _ => h n, fun h n => ?_⟩
  cases n with
  | zero => exact ⟨x, by simp⟩
  | succ n => exact h (n + 1) (Nat.succ_pos n)

/-- **An element outside the perfect core has a finite Frobenius depth.**

If `x` is not a `p ^ n`-th power for every `n`, then there is a *last* stage of the Frobenius
tower at which it is one: some `r` and `y` with `y ^ (p ^ r) = x` and `y` not itself a `p`-th
power. This `r` is Kuhlmann's `ν_x`.

The degree-`p` step of Epp's theorem splits the Laurent coefficients of an Artin–Schreier
equation into a tame and a wild part, and for each wild coefficient it needs exactly this: the
largest stage at which the coefficient is a `p`-power. Made against the perfect core itself, the
split needs no residue-field hypothesis: being outside the perfect core is already, by definition,
the failure of roots at some stage, and `Nat.find` turns that into the last surviving stage.

Compare `bddAbove_setOf_mem_frobeniusPowRange` and `frobeniusDepth` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppKuhlmannCompleteCase`, which work with a
`Subfield`-valued Frobenius tower and produce a boundedness statement and a numerical invariant;
the existential form here — a root `y` together with the witness that it admits no further `p`-th
root — is the shape the Artin–Schreier argument uses. -/
theorem exists_pow_eq_and_not_pow_of_notMem_perfectCore
    {F : Type*} [Field F] (p : ℕ) [ExpChar F p] {x : F} (hx : x ∉ perfectCore F p) :
    ∃ (r : ℕ) (y : F), y ^ (p ^ r) = x ∧ ¬∃ z : F, z ^ p = y := by
  classical
  have H : ∃ n : ℕ, ¬∃ y : F, y ^ p ^ n = x := by
    by_contra! H
    exact hx (mem_perfectCore_iff_forall_one_le.mpr fun n _ => H n)
  have hn : ¬∃ y : F, y ^ p ^ Nat.find H = x := Nat.find_spec H
  have hpos : 0 < Nat.find H := by
    rcases Nat.eq_zero_or_pos (Nat.find H) with h | h
    · exact absurd ⟨x, by rw [h]; simp⟩ hn
    · exact h
  obtain ⟨y, hy⟩ : ∃ y : F, y ^ p ^ (Nat.find H - 1) = x :=
    not_not.mp (Nat.find_min H (Nat.sub_lt hpos Nat.zero_lt_one))
  refine ⟨Nat.find H - 1, y, hy, ?_⟩
  rintro ⟨z, rfl⟩
  refine hn ⟨z, ?_⟩
  rw [← pow_mul, ← pow_succ'] at hy
  simpa only [Nat.sub_add_cancel hpos] using hy

/-- The perfect core is a perfect ring: every element of it has a `p`-th root inside it. -/
instance perfectCore.perfectRing : PerfectRing (perfectCore F p) p := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp x.property 1
  have hy' : y ^ p = (x : F) := by simpa using hy
  have hmem : y ∈ perfectCore F p := by
    rw [mem_perfectCore_iff]
    intro n
    obtain ⟨z, hz⟩ := mem_perfectCore_iff.mp x.property (n + 1)
    refine ⟨z, ?_⟩
    apply frobenius_inj F p
    change (z ^ p ^ n) ^ p = y ^ p
    rw [← pow_mul, ← pow_succ, hz, hy']
  exact ⟨⟨y, hmem⟩, Subtype.ext hy'⟩

/-- The perfect core is a perfect field. -/
instance perfectCore.perfectField : PerfectField (perfectCore F p) :=
  PerfectRing.toPerfectField _ p

/-- **The perfect core is closed under `p ^ n`-th roots**, and the root can be taken inside it.

`mem_perfectCore_iff` already gives a `p ^ n`-th root in `F`; the content here is that it may be
chosen in the perfect core, which is what `perfectCore.perfectRing` provides. The degree-`p` step
of Epp's theorem needs exactly this form: it has to absorb a root of a Laurent coefficient at a
prescribed depth into the base, and the root has to stay in the perfect core for Epp's hypothesis
to apply to it. -/
theorem exists_mem_perfectCore_pow_eq {x : F} (hx : x ∈ perfectCore F p) (n : ℕ) :
    ∃ y, y ∈ perfectCore F p ∧ y ^ p ^ n = x := by
  obtain ⟨y, hy⟩ :=
    (bijective_iterateFrobenius (perfectCore F p) p n).surjective ⟨x, hx⟩
  refine ⟨(y : F), y.property, ?_⟩
  have := congrArg (Subtype.val (p := fun z => z ∈ perfectCore F p)) hy
  simpa only [iterateFrobenius_def, SubmonoidClass.coe_pow] using this

/-- The image of a perfect ring under any ring homomorphism lands in the perfect core.

Together with `perfectCore.perfectRing` this says the perfect core is the *largest* perfect
subfield: applied to the inclusion of a perfect subfield, it shows that subfield is contained in
the perfect core. -/
theorem mem_perfectCore_of_perfectRing {E : Type*} [Field E] [ExpChar E p] [PerfectRing E p]
    (f : E →+* F) (x : E) : f x ∈ perfectCore F p := by
  rw [mem_perfectCore_iff]
  intro n
  obtain ⟨y, hy⟩ := (bijective_iterateFrobenius E p n).surjective x
  exact ⟨f y, by rw [← map_pow]; exact congrArg f hy⟩

/-- The perfect core is integrally closed in `F`: an element of `F` integral over the perfect core
already lies in it. -/
theorem mem_perfectCore_of_isIntegral {x : F} (hx : IsIntegral (perfectCore F p) x) :
    x ∈ perfectCore F p := by
  let E := IntermediateField.adjoin (perfectCore F p) {x}
  have : FiniteDimensional (perfectCore F p) E := IntermediateField.adjoin.finiteDimensional hx
  have : PerfectField E := Algebra.IsAlgebraic.perfectField (perfectCore F p)
  have : ExpChar E p := inferInstance
  exact mem_perfectCore_of_perfectRing (algebraMap E F)
    (⟨x, IntermediateField.mem_adjoin_simple_self _ _⟩ : E)

/-- **The perfect core is algebraically closed as soon as `F` has roots of separable polynomials
over it.**

Only *separable* polynomials over `perfectCore F p` need a root, and the root need only lie in
`F`, not in the perfect core: `mem_perfectCore_of_isIntegral` puts it back. Since the perfect core
is perfect, every irreducible polynomial over it is separable, so this hypothesis covers every
irreducible polynomial and `IsAlgClosed.of_exists_root` applies.

`perfectCore.isAlgClosed` is the special case `IsSepClosed F`, and
`perfectCore.isAlgClosed_iff_exists_aeval_eq_zero` records that the hypothesis is not merely
sufficient but equivalent. -/
theorem perfectCore.isAlgClosed_of_exists_aeval_eq_zero
    (hroot : ∀ f : Polynomial (perfectCore F p), f.Separable → f.degree ≠ 0 →
      ∃ x : F, Polynomial.aeval x f = 0) :
    IsAlgClosed (perfectCore F p) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hirr
  obtain ⟨x, hx⟩ := hroot f (PerfectField.separable_of_irreducible hirr)
    (Polynomial.degree_pos_of_irreducible hirr).ne'
  refine ⟨⟨x, mem_perfectCore_of_isIntegral ⟨f, hf, hx⟩⟩, ?_⟩
  exact (perfectCore F p).subtype.injective (by rwa [map_zero, ← Polynomial.eval₂_at_apply])

/-- **The perfect core of a separably closed field is algebraically closed.**

This is the step that makes the separable-closure reduction in the proof of Epp's theorem worth
performing: after it, the perfect core of the residue field upstairs is algebraically closed, and
the algebraically-closed-residue-field case of the theorem becomes applicable.

The proof is that the perfect core is perfect, so every irreducible polynomial over it is
separable, hence has a root in the separably closed field `F`; that root is integral over the
perfect core and so lies in it by `mem_perfectCore_of_isIntegral`. Separable closedness is used
only to produce that root, which is what
`perfectCore.isAlgClosed_of_exists_aeval_eq_zero` isolates. -/
theorem perfectCore.isAlgClosed [IsSepClosed F] : IsAlgClosed (perfectCore F p) :=
  perfectCore.isAlgClosed_of_exists_aeval_eq_zero fun f hsep hdeg =>
    IsSepClosed.exists_aeval_eq_zero F f hdeg hsep

/-- Conversely, if the perfect core is algebraically closed then every polynomial over it of
positive degree already has a root in `F` — take the root in the perfect core and push it down.

Separability is not needed in this direction; it is carried in the statement only so that the
result composes with `perfectCore.isAlgClosed_of_exists_aeval_eq_zero` into the equivalence
`perfectCore.isAlgClosed_iff_exists_aeval_eq_zero`. -/
theorem perfectCore.exists_aeval_eq_zero_of_isAlgClosed [IsAlgClosed (perfectCore F p)]
    (f : Polynomial (perfectCore F p)) (hdeg : f.degree ≠ 0) :
    ∃ x : F, Polynomial.aeval x f = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (perfectCore F p) f hdeg
  refine ⟨(z : F), ?_⟩
  have h : Polynomial.aeval (Algebra.ofId (perfectCore F p) F z) f =
      Algebra.ofId (perfectCore F p) F (Polynomial.aeval z f) :=
    Polynomial.aeval_algHom_apply _ _ _
  rw [hz, map_zero] at h
  exact h

/-- **Algebraic closedness of the perfect core is exactly the existence in `F` of roots of
separable polynomials over it.**

The right-hand side is strictly weaker than `IsSepClosed F`: it constrains only polynomials with
coefficients in the perfect core, and only asks for roots in `F`. -/
theorem perfectCore.isAlgClosed_iff_exists_aeval_eq_zero :
    IsAlgClosed (perfectCore F p) ↔
      ∀ f : Polynomial (perfectCore F p), f.Separable → f.degree ≠ 0 →
        ∃ x : F, Polynomial.aeval x f = 0 :=
  ⟨fun _ f _ hdeg => perfectCore.exists_aeval_eq_zero_of_isAlgClosed f hdeg,
    perfectCore.isAlgClosed_of_exists_aeval_eq_zero⟩

/-- For a separable extension `E / F`, the minimal polynomial over `F` of an element of the
perfect core of `E` has every coefficient in the perfect core of `F`.

This is what propagates Epp's residue-field hypothesis upward through a separable enlargement:
the coefficients stay in the perfect core downstairs, where the hypothesis applies to them. -/
theorem minpoly_coeff_mem_perfectCore {E : Type*} [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [ExpChar E p] {x : E} (hx : x ∈ perfectCore E p) (i : ℕ) :
    (minpoly F x).coeff i ∈ perfectCore F p := by
  rw [mem_perfectCore_iff]
  intro n
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp hx n
  refine ⟨(minpoly F y).coeff i, ?_⟩
  have h := minpoly.iterateFrobenius_of_isSeparable p n (Algebra.IsSeparable.isSeparable F y)
  rw [iterateFrobenius_def, hy] at h
  rw [h, Polynomial.coeff_map, iterateFrobenius_def]

/-- Membership in the perfect core is invariant under a ring isomorphism. -/
theorem mem_perfectCore_ringEquiv_iff {E : Type*} [Field E] [ExpChar E p] (e : F ≃+* E) (x : F) :
    e x ∈ perfectCore E p ↔ x ∈ perfectCore F p := by
  simp only [mem_perfectCore_iff]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · obtain ⟨y, hy⟩ := h n
    exact ⟨e.symm y, by apply e.injective; simpa only [map_pow, e.apply_symm_apply] using hy⟩
  · obtain ⟨y, hy⟩ := h n
    exact ⟨e y, by rw [← map_pow, hy]⟩

/-! ### Transport through a separable extension -/

/-- A separable element whose `p ^ n`-th power lies in the base field already lies in the
base field.

Indeed, adjoining the element is purely inseparable because the displayed power lies in the
base, and it is separable by hypothesis.  An extension which is both purely inseparable and
separable is trivial. -/
theorem exists_algebraMap_eq_of_isSeparable_of_pow_eq
    {E : Type*} [Field E] [Algebra F E] {x : F} {y : E} (n : ℕ)
    (hysep : IsSeparable F y) (hy : y ^ p ^ n = algebraMap F E x) :
    ∃ z : F, algebraMap F E z = y := by
  have : IsPurelyInseparable F (IntermediateField.adjoin F {y}) :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E p).mpr
      ⟨n, ⟨x, hy.symm⟩⟩
  have : Algebra.IsSeparable F (IntermediateField.adjoin F {y}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).mpr hysep
  have hbot := IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    (IntermediateField.adjoin F {y})
  exact IntermediateField.mem_bot.mp (hbot ▸ IntermediateField.mem_adjoin_simple_self F y)

/-- A base-field element has a `p ^ n`-th root after a separable extension exactly when it
already has one in the base field. -/
theorem exists_pow_eq_algebraMap_iff_of_isSeparable
    {E : Type*} [Field E] [Algebra F E] [Algebra.IsSeparable F E]
    (n : ℕ) (x : F) :
    (∃ y : E, y ^ p ^ n = algebraMap F E x) ↔ ∃ z : F, z ^ p ^ n = x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := exists_algebraMap_eq_of_isSeparable_of_pow_eq n
      (Algebra.IsSeparable.isSeparable F y) hy
    refine ⟨z, (algebraMap F E).injective ?_⟩
    rw [map_pow, hz, hy]
  · rintro ⟨z, hz⟩
    exact ⟨algebraMap F E z, by rw [← map_pow, hz]⟩

/-- Membership in the perfect core is reflected by every separable field extension. -/
theorem mem_perfectCore_algebraMap_iff_of_isSeparable
    {E : Type*} [Field E] [Algebra F E] [Algebra.IsSeparable F E] [ExpChar E p]
    (x : F) :
    algebraMap F E x ∈ perfectCore E p ↔ x ∈ perfectCore F p := by
  simp only [mem_perfectCore_iff]
  exact forall_congr' fun n => exists_pow_eq_algebraMap_iff_of_isSeparable n x

/-- A base-field element fails to have a `p`-th root after a separable extension exactly when
it fails to have one in the base field.  This is the one-step obstruction carried by a terminal
Frobenius-depth witness. -/
theorem not_exists_pow_eq_algebraMap_iff_of_isSeparable
    {E : Type*} [Field E] [Algebra F E] [Algebra.IsSeparable F E] (x : F) :
    (¬ ∃ y : E, y ^ p = algebraMap F E x) ↔ ¬ ∃ z : F, z ^ p = x := by
  simpa only [pow_one] using
    not_congr (exists_pow_eq_algebraMap_iff_of_isSeparable (F := F) (p := p) 1 x)

section SeparablyClosed

/-- Over a separably closed field, a separable element of an extension already lies in the base. -/
theorem exists_algebraMap_eq_of_isSeparable {E : Type*} [Field E] [Algebra F E] [IsSepClosed F]
    {x : E} (hx : IsSeparable F x) : ∃ y : F, algebraMap F E y = x := by
  have hmem : x ∈ separableClosure F E := mem_separableClosure_iff.mpr hx
  rwa [IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure F E)] at hmem

/-- Over a separably closed field, a root of a separable polynomial whose coefficients come from
the base already lies in the base. -/
theorem exists_algebraMap_eq_of_eval_eq_zero {E : Type*} [Field E] [Algebra F E] [IsSepClosed F]
    (f : Polynomial E) (hf : f.Separable) {x : E} (hx : f.eval x = 0)
    (hcoeff : ∀ i, ∃ c : F, algebraMap F E c = f.coeff i) :
    ∃ y : F, algebraMap F E y = x := by
  obtain ⟨g, hg⟩ := (Polynomial.mem_map_range (algebraMap F E)).mpr hcoeff
  change g.map (algebraMap F E) = f at hg
  have hs : g.Separable := (Polynomial.separable_map (algebraMap F E)).mp (hg ▸ hf)
  have hroot : Polynomial.aeval x g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hg]; exact hx
  exact exists_algebraMap_eq_of_isSeparable (hs.of_dvd (minpoly.dvd F x hroot))

/-- A separable element over `k` stays separable over any `K` in the tower `k → l → L` after
mapping it to `L`. -/
private theorem isSeparable_algebraMap_tower_top {k l L : Type*} (K : Type*) [Field k] [Field l]
    [Field K] [Field L] [Algebra k l] [Algebra l L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k l L] [IsScalarTower k K L] {y : l} (hy : IsSeparable k y) :
    IsSeparable K (algebraMap l L y) :=
  (hy.map (IsScalarTower.toAlgHom k l L) (algebraMap l L).injective).tower_top K

/-- **Epp's hypothesis transfers upward along a separable enlargement.**

Consider a commutative square of fields
```
l → L
↑   ↑
k → K
```
with `L / l` separable and `K` separably closed. If every element of the perfect core of `l` is
separable algebraic over `k`, then every element of the perfect core of `L` comes from `K`.

Applied to the residue fields of a square of discrete valuation rings whose upper residue fields
are separable closures of the lower ones, this says that Epp's hypothesis for the original
extension implies Epp's hypothesis — indeed the stronger containment of the perfect core in the
base residue field — for the enlarged one. This is part of the separable-closure reduction in
the proof of Tag 09F9. -/
theorem perfectCore_mem_range_of_separable_square {k l K L : Type*} [Field k] [Field l] [Field K]
    [Field L] [Algebra k l] [Algebra l L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k l L] [IsScalarTower k K L] [Algebra.IsSeparable l L] [IsSepClosed K]
    [ExpChar l p] [ExpChar L p] (hresidue : ∀ x : l, x ∈ perfectCore l p → IsSeparable k x)
    {x : L} (hx : x ∈ perfectCore L p) : ∃ y : K, algebraMap K L y = x := by
  apply exists_algebraMap_eq_of_eval_eq_zero ((minpoly l x).map (algebraMap l L))
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable l x))
  · simpa only [Polynomial.eval_map, ← Polynomial.aeval_def] using minpoly.aeval l x
  · intro i
    rw [Polynomial.coeff_map]
    exact exists_algebraMap_eq_of_isSeparable
      (isSeparable_algebraMap_tower_top K (hresidue _ (minpoly_coeff_mem_perfectCore hx i)))

/-- If `k` is separably closed and every element of the perfect core of `F` is separable over
`k`, then the perfect core is contained in the image of `k`. -/
theorem perfectCore_le_fieldRange {k : Type*} [Field k] [Algebra k F] [IsSepClosed k]
    (hcore : ∀ x : F, x ∈ perfectCore F p → IsSeparable k x) :
    perfectCore F p ≤ (algebraMap k F).fieldRange :=
  fun x hx => exists_algebraMap_eq_of_isSeparable (hcore x hx)

/-- The containment of `perfectCore_le_fieldRange` upgraded to a ring homomorphism: the perfect
core factors through `k` over the inclusion into `F`.

This is what lets the proof of Epp's theorem choose a Cohen ring, or a power series ring, with
residue field the perfect core upstairs and a map into the base — the perfect core has to be
realised as a *ring* inside the base residue field, not merely as a subset of the image. -/
theorem exists_ringHom_perfectCore {k : Type*} [Field k] [Algebra k F] [IsSepClosed k]
    (hcore : ∀ x : F, x ∈ perfectCore F p → IsSeparable k x) :
    ∃ f : perfectCore F p →+* k, (algebraMap k F).comp f = (perfectCore F p).subtype := by
  classical
  choose f hf using fun x : perfectCore F p => perfectCore_le_fieldRange hcore x.property
  exact ⟨{ toFun := f
           map_one' := (algebraMap k F).injective (by rw [hf, map_one]; rfl)
           map_zero' := (algebraMap k F).injective (by rw [hf, map_zero]; rfl)
           map_add' := fun x y => (algebraMap k F).injective (by rw [hf, map_add, hf, hf]; rfl)
           map_mul' := fun x y => (algebraMap k F).injective (by rw [hf, map_mul, hf, hf]; rfl) },
    RingHom.ext hf⟩

end SeparablyClosed

/-- The perfect-core separability condition passes along a square of fields whose upper
horizontal map is surjective, hence an isomorphism.

The application is to the residue fields of a completion, or of a `ULift`, where the residue field
does not change: Epp's hypothesis for the original extension gives it for the completed one. -/
theorem isSeparable_of_mem_perfectCore_of_surjective {k l K L : Type*} [Field k] [Field l]
    [Field K] [Field L] [Algebra k l] [Algebra l L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k l L] [IsScalarTower k K L] [ExpChar l p] [ExpChar L p]
    (hsurj : Function.Surjective (algebraMap l L))
    (hcore : ∀ x : l, x ∈ perfectCore l p → IsSeparable k x)
    {x : L} (hx : x ∈ perfectCore L p) : IsSeparable K x := by
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ perfectCore l p :=
    (mem_perfectCore_ringEquiv_iff
      (RingEquiv.ofBijective (algebraMap l L) ⟨(algebraMap l L).injective, hsurj⟩) y).mp hx
  exact isSeparable_algebraMap_tower_top K (hcore y hy)
