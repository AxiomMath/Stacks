module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# The standing situation of Stacks Section 45.12 with a weakened projective bundle formula

The standing situation `Stacks.WeilCohomology.ChernSetup` of Section 45.12 (Tag 0FI4) asks the
projective bundle formula — condition (4) — to be *bijective*:
`(a_0, …, a_r) ↦ ∑ c₁^A(𝒪_P(1))^i ∪ p^*(a_i)` from `r + 1` copies of `A(X)` onto `A(𝐏(ℰ))`.
The construction of Chern classes and of the Chern character uses much less: that the map is
injective, and that `c₁^A(𝒪_P(1))^{r+1}` lies in its image with homogeneous coefficients, the
`i`-th of degree `r + 1 - i`.

This weaker form is what a cohomology theory as in Section 45.14 provides. There `H^*` takes
values in graded commutative algebras `⨁_{n ∈ 𝐙} H^n`, which may be nonzero in negative degrees,
and Tag 0FIE applies Tag 0FI9 to `A(X) = ⨁_{i ≥ 0} H^{2i}(X)(i)`. Axiom (A3) is the projective
bundle formula on all of `H^*`; restricted to `A` it stays injective and still resolves
`c₁(𝒪_P(1))^{r+1}`, whose coefficients sit in the positive degrees `2(r + 1 - i)`, but it need not
be surjective: a class `c₁(𝒪_P(1)) ∪ p^*t` with `t ∈ H^{-2}(X)(-1)` lies in `A^0(P)` without
lying in the image of `A(X)^{r+1}`. So Tag 0FIE needs the standing situation in the form of this
file. `Stacks.WeilCohomology.Weak.ChernSetup.ofSourceChernSetup` shows it is a generalization.

## Main definitions

* `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Section 45.12 with condition
  (4) replaced by its injectivity and the resolution of the top power of the twist class.
* `Stacks.WeilCohomology.Weak.ChernSetup.ofSourceChernSetup`: a standing situation with the
bijective projective bundle formula is one of these.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-! ### The standing situation -/

/-- **The standing situation of Stacks Section 45.12.** A contravariant functor `A` from a
category `𝒞` of quasi-compact schemes to graded rings, an additive first Chern class
`c₁^A : Pic(X) ⟶ A¹(X)` whose values are central, the projective bundle of every finite locally
free module of positive constant rank with the projective bundle formula, and the open and closed
subobjects with the splitting of `A` they index.

Which clauses of the source are transcribed, and what omitting the others costs, is recorded in
the module documentation. -/
structure ChernSetup (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u}) where
  /-- **Clause (1).** Every object of `𝒞` is quasi-compact. -/
  compactSpace : ∀ X : C, CompactSpace (S.obj X)
  /-- The graded ring `A(X)`. -/
  A : C → Type v
  /-- `A(X)` is a unital associative, not necessarily commutative, ring. -/
  [ring : ∀ X, Ring (A X)]
  /-- The grading `A(X) = ⨁_{i ≥ 0} A^i(X)`, as a family of additive subgroups. -/
  grade : ∀ X : C, ℕ → AddSubgroup (A X)
  /-- The unit is in degree zero. -/
  one_mem : ∀ X : C, (1 : A X) ∈ grade X 0
  /-- Multiplication adds degrees. -/
  mul_mem : ∀ (X : C) (i j : ℕ) {a b : A X}, a ∈ grade X i → b ∈ grade X j →
    a * b ∈ grade X (i + j)
  /-- **The grading is a direct sum decomposition**, `A(X) = ⨁_{i ≥ 0} A^i(X)`.

  This is the source's own reading of `A` as a functor to *graded* rings: its graded algebra is
  "a unital, associative, not necessarily commutative `𝐙`-algebra with a grading
  `A = ⨁_{i ≥ 0} A^i`". `DirectSum.IsInternal` is that, at the Mathlib spelling: the map
  `⨁_i A^i(X) ⟶ A(X)` is bijective.

  What it buys is the refinement of condition (4) that the target `∏_{i ≥ 0} A^i(X)` of Tag 0FI5
  needs — `Stacks.WeilCohomology.Weak.ChernSetup.mem_grade_of_bundleFormula`, that the tuple the
  projective bundle formula resolves a class of `A^n(P)` into is homogeneous of the complementary
  degrees. -/
  isInternal_grade : ∀ X : C, DirectSum.IsInternal (grade X)
  /-- The pullback `f^* : A(X) ⟶ A(X')` of a morphism `f : X' ⟶ X` of `𝒞`. -/
  pull : ∀ {X Y : C}, (X ⟶ Y) → (A Y →+* A X)
  /-- Pullback along an identity is the identity. -/
  pull_id : ∀ X : C, pull (𝟙 X) = RingHom.id (A X)
  /-- Pullback is contravariantly functorial. -/
  pull_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), pull (f ≫ g) = (pull f).comp (pull g)
  /-- Pullback preserves degrees. -/
  pull_grade : ∀ {X Y : C} (f : X ⟶ Y) (i : ℕ) {a : A Y}, a ∈ grade Y i →
    pull f a ∈ grade X i
  /-- The first Chern class `c₁^A : Pic(X) ⟶ A¹(X)`, an additive map. -/
  c₁ : ∀ X : C, (S.obj X).picardGroup →+ A X
  /-- Its values lie in degree one. -/
  c₁_mem : ∀ (X : C) (L : (S.obj X).picardGroup), c₁ X L ∈ grade X 1
  /-- **Axiom (1).** The first Chern class of an invertible module is central in `A(X)`. -/
  c₁_central : ∀ (X : C) (L : (S.obj X).picardGroup) (a : A X), c₁ X L * a = a * c₁ X L
  /-- **Clause (3)(a).** The projective bundle of a finite locally free module of rank `r + 1` is
  an object of `𝒞`, and its projection is a morphism of `𝒞`.

  This is the *closure property* the source states, and nothing else: the bundle, its twist, its
  tautological sequence, the rank of the kernel of that sequence and the flatness of the
  projection are all constructed from it, by
  `Stacks.WeilCohomology.BundleObject.toBundleDatum`, which
  `Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum` applies. -/
  bundleObject : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) →
      BundleObject S X E r
  /-- **Axiom (4), the projective bundle formula, injectivity.** For `ℰ` of constant rank `r + 1`
  with projective bundle `p : P ⟶ X`, the map `(a₀, …, a_r) ↦ ∑ c₁^A(𝒪_P(1))^i ∪ p^*(a_i)` from
  `r + 1` copies of `A(X)` to `A(P)` is injective.

  It is stated at the twist and the projection of the clause-(3)(a) datum `bundleObject`, because
  a field cannot mention `Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum`, which is a
  definition on the structure. `Stacks.WeilCohomology.Weak.ChernSetup.injective_bundleFormula` is
  the same statement read at that datum. -/
  injective_bundleFormula_bundleObject : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    Function.Injective fun a : Fin (r + 1) → A X =>
      ∑ i : Fin (r + 1),
        c₁ (bundleObject X E r hE).bundle (bundleObject X E r hE).twistClass ^ (i : ℕ) *
          pull (bundleObject X E r hE).proj (a i)
  /-- **Axiom (4), the projective bundle formula, at the top power.** The class
  `c₁^A(𝒪_P(1))^{r+1}` is `∑ c₁^A(𝒪_P(1))^i ∪ p^*(a_i)` for some `(a₀, …, a_r)`. This is the one
  element the construction of the Chern classes resolves. -/
  exists_bundleFormula_eq_pow_bundleObject : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    ∃ a : Fin (r + 1) → A X,
      ∑ i : Fin (r + 1),
          c₁ (bundleObject X E r hE).bundle (bundleObject X E r hE).twistClass ^ (i : ℕ) *
            pull (bundleObject X E r hE).proj (a i) =
        c₁ (bundleObject X E r hE).bundle (bundleObject X E r hE).twistClass ^ (r + 1)
  /-- **Clause (2).** An open and closed subscheme of an object of `𝒞` is again an object of `𝒞`,
  and its inclusion is a morphism of `𝒞`. -/
  clopenSubobject : ∀ (X : C) (U : (S.obj X).Opens), IsClopen (U : Set (S.obj X)) →
    ClopenSubobject S X U
  /-- **Condition (2), for a finite decomposition.** If `X` is the disjoint union of finitely many
  open and closed subschemes `U i`, then `A(X) = ∏ᵢ A(U i)` through restriction along their
  inclusions. The source states the two-piece case `A(U ⨿ V) = A(U) × A(V)`; this is its
  iteration, which is the form the source's proofs use — `A(X) = ∏ A(X_r)` for the rank
  decomposition — the decomposition being finite by clause (1). -/
  bijective_pull_clopenSubobject : ∀ (X : C) (ι : Type) [Finite ι] (U : ι → (S.obj X).Opens)
    (hU : ∀ i, IsClopen (U i : Set (S.obj X))), (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
      (⨆ i, U i) = ⊤ →
      Function.Bijective fun a : A X => fun i => pull (clopenSubobject X (U i) (hU i)).hom a
  /-- **Condition (2) is a splitting of graded rings.** `A` takes values in graded rings, so the
  splitting `A(X) = ∏ᵢ A(U i)` of condition (2) is one of graded rings: a class whose restriction
  to every piece lies in degree `n` lies in degree `n`. The other direction, that a class of
  degree `n` restricts to classes of degree `n`, is `pull_grade`. -/
  mem_grade_of_pull_clopenSubobject : ∀ (X : C) (ι : Type) [Finite ι] (U : ι → (S.obj X).Opens)
    (hU : ∀ i, IsClopen (U i : Set (S.obj X))), (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
      (⨆ i, U i) = ⊤ → ∀ (a : A X) (n : ℕ),
      (∀ i, pull (clopenSubobject X (U i) (hU i)).hom a ∈
          grade (clopenSubobject X (U i) (hU i)).obj n) →
        a ∈ grade X n

attribute [instance] ChernSetup.ring

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} (𝔚 : ChernSetup.{u, v, v₁, w} C S)

/-- **The tautological datum of the projective bundle `𝐏(ℰ)`: the bundle with its flat
projection, its invertible twist `𝒪_{𝐏(ℰ)}(1)` and the tautological short exact sequence
`0 ⟶ 𝓕 ⟶ p^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1) ⟶ 0` with `𝓕` of rank `r`.**

This is **not** an assumption. It is constructed from clause (3)(a) — the field `bundleObject`,
which says only that the already-built `𝐏(ℰ)` is an object of `𝒞` — by
`Stacks.WeilCohomology.BundleObject.toBundleDatum`, where each piece is attributed. -/
def bundleDatum (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    BundleDatum S X E r :=
  (𝔚.bundleObject X E r hE).toBundleDatum

/-- The projective bundle of `bundleDatum` is the projective bundle of `bundleObject`. -/
theorem bundleDatum_bundle (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    (𝔚.bundleDatum X E r hE).bundle = (𝔚.bundleObject X E r hE).bundle := rfl

/-- The projection `𝐏(ℰ) ⟶ X` of `bundleDatum` is the projection of `bundleObject`. -/
theorem bundleDatum_proj (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    (𝔚.bundleDatum X E r hE).proj = (𝔚.bundleObject X E r hE).proj := rfl

/-- The class of the twist `𝒪_{𝐏(ℰ)}(1)` in `bundleDatum` is the twist class of `bundleObject`. -/
theorem bundleDatum_twistClass (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    (𝔚.bundleDatum X E r hE).twistClass = (𝔚.bundleObject X E r hE).twistClass := rfl

/-- **Axiom (4), the projective bundle formula, injectivity**, read at the tautological datum
`Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum`: the bundle, the twist and the projection of
the constructed datum are those of the clause-(3)(a) datum. -/
theorem injective_bundleFormula' (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Injective fun a : Fin (r + 1) → 𝔚.A X =>
      ∑ i : Fin (r + 1),
        𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔚.pull (𝔚.bundleDatum X E r hE).proj (a i) :=
  𝔚.injective_bundleFormula_bundleObject X E r hE

/-- The projective bundle formula's map, named so that its injectivity can be applied to a
tuple. -/
def bundleFormula (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : Fin (r + 1) → 𝔚.A X) : 𝔚.A (𝔚.bundleDatum X E r hE).bundle :=
  ∑ i : Fin (r + 1),
    𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
      𝔚.pull (𝔚.bundleDatum X E r hE).proj (a i)

/-- **The projective bundle formula is injective.** -/
theorem injective_bundleFormula (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Injective (𝔚.bundleFormula X E r hE) :=
  𝔚.injective_bundleFormula' X E r hE

/-- **The projective bundle formula resolves `c₁^A(𝒪_P(1))^{r+1}`.** -/
theorem exists_bundleFormula_eq_pow (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    ∃ a : Fin (r + 1) → 𝔚.A X, 𝔚.bundleFormula X E r hE a =
      𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (r + 1) :=
  𝔚.exists_bundleFormula_eq_pow_bundleObject X E r hE

/-- The projective bundle formula is additive in the tuple. -/
theorem bundleFormula_add (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a b : Fin (r + 1) → 𝔚.A X) :
    𝔚.bundleFormula X E r hE (a + b) =
      𝔚.bundleFormula X E r hE a + 𝔚.bundleFormula X E r hE b := by
  simp [bundleFormula, mul_add, Finset.sum_add_distrib]

/-- The projective bundle formula commutes with integer multiples of the tuple. -/
theorem bundleFormula_zsmul (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (n : ℤ) (a : Fin (r + 1) → 𝔚.A X) :
    𝔚.bundleFormula X E r hE (n • a) = n • 𝔚.bundleFormula X E r hE a := by
  simp only [bundleFormula, Finset.smul_sum, Pi.smul_apply, map_zsmul, mul_smul_comm]

/-- The projective bundle formula sends the tuple `(a, 0, …, 0)` to `p^*a`: every term past the
first has a zero factor, and the first has `c₁^A(𝒪_P(1))^0 = 1`. -/
theorem bundleFormula_single (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : 𝔚.A X) :
    𝔚.bundleFormula X E r hE (Pi.single 0 a) = 𝔚.pull (𝔚.bundleDatum X E r hE).proj a := by
  classical
  rw [bundleFormula, Finset.sum_eq_single (0 : Fin (r + 1))]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Pullback along the projection of a projective bundle is injective on `A`.**

This is the clause of the projective bundle formula that the splitting principle uses, and it is
a consequence of condition (4) rather than a further assumption: `p^*a` is the image of the tuple
`(a, 0, …, 0)` under the formula, which is injective, so two classes with the same pullback have
equal tuples and are therefore equal. -/
theorem injective_pull_proj (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Injective (𝔚.pull (𝔚.bundleDatum X E r hE).proj) := by
  classical
  intro a b hab
  have h : 𝔚.bundleFormula X E r hE (Pi.single 0 a) = 𝔚.bundleFormula X E r hE (Pi.single 0 b) :=
    (𝔚.bundleFormula_single X E r hE a).trans
      (hab.trans (𝔚.bundleFormula_single X E r hE b).symm)
  have := 𝔚.injective_bundleFormula X E r hE h
  simpa using congrFun this (0 : Fin (r + 1))

/-- **Restriction to the pieces of a finite decomposition into open and closed subschemes is
injective on `A`.**

This is the half of condition (2) that the reduction of an arbitrary finite locally free module to
one of constant rank consumes, and it is a consequence of that condition rather than a further
assumption, exactly as `Stacks.WeilCohomology.Weak.ChernSetup.injective_pull_proj` is a consequence
of condition (4). -/
theorem injective_pull_clopenSubobject (X : C) (ι : Type) [Finite ι]
    (U : ι → (S.obj X).Opens) (hU : ∀ i, IsClopen (U i : Set (S.obj X)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcover : (⨆ i, U i) = ⊤) :
    Function.Injective fun a : 𝔚.A X => fun i => 𝔚.pull (𝔚.clopenSubobject X (U i) (hU i)).hom a :=
  (𝔚.bijective_pull_clopenSubobject X ι U hU hdisj hcover).injective

/-- **`A(X)` is the zero ring when `X` has no points.**

An object with no points is the disjoint union of the empty family of open and closed subschemes,
so condition (2) identifies `A(X)` with the empty product. This is a consequence of condition (2)
rather than a further assumption. -/
theorem subsingleton_of_isEmpty (X : C) (hX : IsEmpty (S.obj X)) : Subsingleton (𝔚.A X) := by
  have hbot : (⊥ : (S.obj X).Opens) = ⊤ :=
    TopologicalSpace.Opens.ext (by simpa using (Set.univ_eq_empty_iff.2 hX).symm)
  refine ⟨fun a b => (𝔚.bijective_pull_clopenSubobject X Empty (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) ?_).injective (funext fun i => i.elim)⟩
  rw [iSup_of_empty]
  exact hbot

/-- A natural number lies in degree zero: the unit does, by `one_mem`, and `A^0(X)` is an additive
subgroup. -/
theorem natCast_mem_grade_zero (X : C) (n : ℕ) : (n : 𝔚.A X) ∈ 𝔚.grade X 0 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ]; exact (𝔚.grade X 0).add_mem ih (𝔚.one_mem X)

/-- **A standing situation with the bijective projective bundle formula is one of these.** -/
def ofSourceChernSetup (𝔄 : Stacks.WeilCohomology.SourceChernSetup.{u, v, v₁, w} C S) :
    ChernSetup.{u, v, v₁, w} C S where
  compactSpace := 𝔄.compactSpace
  A := 𝔄.A
  grade := 𝔄.grade
  one_mem := 𝔄.one_mem
  mul_mem := 𝔄.mul_mem
  isInternal_grade := 𝔄.isInternal_grade
  pull := 𝔄.pull
  pull_id := 𝔄.pull_id
  pull_comp := 𝔄.pull_comp
  pull_grade := 𝔄.pull_grade
  c₁ := 𝔄.c₁
  c₁_mem := 𝔄.c₁_mem
  c₁_central := 𝔄.c₁_central
  bundleObject := 𝔄.bundleObject
  injective_bundleFormula_bundleObject X E r hE :=
    (𝔄.bijective_bundleFormula_bundleObject X E r hE).injective
  exists_bundleFormula_eq_pow_bundleObject X E r hE :=
    (𝔄.bijective_bundleFormula_bundleObject X E r hE).surjective _
  clopenSubobject := 𝔄.clopenSubobject
  bijective_pull_clopenSubobject := 𝔄.bijective_pull_clopenSubobject
  mem_grade_of_pull_clopenSubobject := 𝔄.mem_grade_of_pull_clopenSubobject

end ChernSetup

end Stacks.WeilCohomology.Weak

end
