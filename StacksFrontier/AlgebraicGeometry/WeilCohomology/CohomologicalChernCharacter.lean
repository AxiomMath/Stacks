module

public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass

/-!
# The cohomological Chern character of a Weil cohomology theory

Section 45.14 of the Stacks Project fixes data `(D0)`, `(D1)`, `(D2')` — a one-dimensional
`F`-vector space `F(1)`, a contravariant functor `H^*` from smooth projective schemes over `k`
to graded commutative `F`-algebras, and a first Chern class `c_1^H : Pic(X) → H^2(X)(1)` — and
Tag 0FIE asserts that, granted the axioms `(A1)` – `(A4)`, there is exactly one rule assigning
to every smooth projective `X` over `k` a ring homomorphism

`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`

compatible with pullbacks and satisfying `ch^H(ℒ) = exp(c_1^H(ℒ))` for every invertible
`𝒪_X`-module `ℒ`. This file constructs that rule and proves it unique. It is the input Tag 0FIF
consumes as the field `Stacks.WeilCohomology.CycleClassSetup.chH`.

## Main definitions

* `Stacks.WeilCohomology.expFirstChernClass`: `exp(c_1^H(ℒ))`, the power series whose `n`-th
  coefficient is `(1/n!) · c_1^H(ℒ)^n`.
* `Stacks.WeilCohomology.gradedPowerSeries`: `∏_{i ≥ 0} A^i(X)` inside `A(X)[[t]]`, the power
  series whose `n`-th coefficient lies in `A^n(X)`.

## Main results

* `Stacks.WeilCohomology.exists_cohomologicalChernCharacter`: **the existence half of Tag
  0FIE.** The cohomological Chern character of a single finite locally free module extends to a
  ring homomorphism on `K₀(Vect(X))` which is graded, compatible with pullbacks, and takes the
  value `exp(c_1^H(ℒ))` on an invertible module.
* `Stacks.WeilCohomology.eq_of_cohomologicalChernCharacter`: **the uniqueness half of Tag
  0FIE.** Two rules compatible with pullbacks and with that value on invertible modules agree on
  the class of every finite locally free module of constant rank.

## The dictionary

The statements are read against `Stacks.WeilCohomology.ChernSetup`, the standing situation of
Section 45.12 — Tag 0FI4 — which is the shape in which the source's proof uses the data:

* `𝒞` is the category of smooth projective schemes over `k`, presented as a functor
  `S : 𝒞 ⥤ Scheme`;
* `𝔄.A X` is `⨁_{i ≥ 0} H^{2i}(X)(i)`, the even Tate-twisted cohomology of `X`, a ring because
  its summands sit in even degrees, with `𝔄.grade X i` the summand `H^{2i}(X)(i)`;
* `𝔄.pull f` is `f^*` and `𝔄.c₁` is `c_1^H`, whose values lie in `H^2(X)(1)`, that is in
  `𝔄.grade X 1`;
* `𝔄.A X` is a `𝐐`-algebra because `F` has characteristic zero, which is what the exponential
  needs;
* `∏_{i ≥ 0} H^{2i}(X)(i)` is `Stacks.WeilCohomology.gradedPowerSeries 𝔄 X` inside
  `PowerSeries (𝔄.A X)`: the product of the graded pieces, whose multiplication is the
  convolution, is exactly the power series ring cut down to the series whose `n`-th coefficient
  is in degree `n`. Taking it inside a power series ring is what makes `ch^H` an honest ring
  homomorphism rather than a family of components, which is how Tag 0FIE states it and how Tag
  0FIF uses it;
* `κ f` is the pullback homomorphism `f^* : K₀(Vect(X)) ⟶ K₀(Vect(X'))`.

Axioms `(A1)` – `(A4)` of Section 45.14 enter only through the situation, as the conditions on
`A` of Section 45.12: `(A1)` gives condition (2), the splitting `A(U ⨿ V) = A(U) × A(V)`, `(A2)`
gives condition (3), `(A3)` gives condition (4), the projective bundle formula, and `(A4)` gives
condition (5). Of these `Stacks.WeilCohomology.ChernSetup` transcribes only the projective
bundle formula, as `𝔄.bijective_bundleFormula`, which is what the splitting principle of Tag
0FI7 consumes; none of the axioms is used directly below.

## What is a hypothesis, and why

* **The cohomological Chern character of a single module**, `chM X ℰ`. The source obtains Tag
  0FIE from Proposition 45.12.4, Tag 0FI9, whose existence half constructs `ch^A(ℰ)` as
  `r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))` from the locally constant rank `r^A`
  and the Chern classes of Tag 0FI5 on all of `K₀`. Neither is available in this repository —
  both rest on condition (2) of the situation, the splitting `A(U ⨿ V) = A(U) × A(V)`, which
  `Stacks.WeilCohomology.ChernSetup` does not transcribe — so `chM` and its three properties
  along short exact sequences, tensor products and the unit are carried as hypotheses. What is
  proved here is the passage from a module to `K₀(Vect(X))`, which is what Tag 0FIE is about,
  and the uniqueness, which the source leaves to Tag 0FI9 and which is proved outright.
* **The pullback homomorphism of `K₀(Vect(-))`.** It is not constructed in this repository — it
  needs the pullback of a short exact sequence of finite locally free modules to stay exact —
  and is a hypothesis, exactly as in Tag 0FEJ's own statement
  `AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator` and in Tag 0FIC's.
* **Constant rank in the uniqueness half.** The splitting principle of Tag 0FI7 needs a constant
  rank, and the source's reduction to that case is condition (2) again.

## Implementation notes

The extension from a module to `K₀(Vect(X))` is Tag 0FEM's
`AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative`, the same
statement for the Chow Chern character: both are the universal property of the Grothendieck ring
applied to an additive, multiplicative, unital assignment. The grading and the compatibility
with pullbacks are then transported from the generators to all of `K₀(Vect(X))`, the first
because the graded series form a subgroup and the second because both sides of the equation are
additive.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### The target of the cohomological Chern character -/

/-- **`∏_{i ≥ 0} A^i(X)` inside `A(X)[[t]]`**: the power series whose `n`-th coefficient lies in
`A^n(X)`. The product of the graded pieces, whose multiplication is the convolution, is exactly
this subgroup of the power series ring. -/
def gradedPowerSeries (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C) :
    AddSubgroup (PowerSeries (𝔄.A X)) where
  carrier := {φ | ∀ n : ℕ, PowerSeries.coeff n φ ∈ 𝔄.grade X n}
  add_mem' hφ hψ n := by simpa using add_mem (hφ n) (hψ n)
  zero_mem' n := by simp
  neg_mem' hφ n := by simpa using neg_mem (hφ n)

/-- A power series lies in `gradedPowerSeries 𝔄 X` exactly when its `n`-th coefficient lies in
`A^n(X)` for every `n`. -/
@[simp] theorem mem_gradedPowerSeries {𝔄 : ChernSetup.{u, v, v₁, w} C S} {X : C}
    {φ : PowerSeries (𝔄.A X)} :
    φ ∈ gradedPowerSeries 𝔄 X ↔ ∀ n : ℕ, PowerSeries.coeff n φ ∈ 𝔄.grade X n :=
  Iff.rfl

/-- **`exp(c_1^H(ℒ))`**, the value Tag 0FIE prescribes for the cohomological Chern character of
an invertible module: the power series whose `n`-th coefficient is `(1/n!) · c_1^H(ℒ)^n`. This
is where `A(X)` being a `𝐐`-algebra, that is `F` having characteristic zero, is used. -/
def expFirstChernClass (𝔄 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔄.A X)] (X : C)
    (L : (S.obj X).picardGroup) : PowerSeries (𝔄.A X) :=
  PowerSeries.mk fun n => algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) * 𝔄.c₁ X L ^ n

/-- The `n`-th coefficient of `expFirstChernClass 𝔄 X L` is `(1/n!) · c_1^H(ℒ)^n`. -/
@[simp] theorem coeff_expFirstChernClass {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔄.A X)] (X : C) (L : (S.obj X).picardGroup) (n : ℕ) :
    PowerSeries.coeff n (expFirstChernClass 𝔄 X L) =
      algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) * 𝔄.c₁ X L ^ n := by
  simp [expFirstChernClass]

/-! ### Two auxiliary facts -/

/-- A module that is finite locally free of some rank is finite locally free at the spelling the
Grothendieck ring is built over. -/
private theorem stacksFlf_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L r) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} L :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mpr h.isFiniteLocallyFree

/-- An invertible module is finite locally free at the spelling the Grothendieck ring is built
over: on a scheme it is finite locally free of rank one by Tag 0B8M. -/
private theorem stacksFlf_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} L :=
  stacksFlf_of_isFiniteLocallyFreeOfRank (r := 1) inferInstance

/-- An additive map out of `K₀(Vect(X))` whose values on the classes of finite locally free
modules lie in a subgroup takes all its values there, the classes of those modules generating
the group. -/
private theorem mem_of_classOf_mem {X : Scheme.{u}} {A : Type*} [AddCommGroup A]
    (f : VectorBundleKZero X →+ A) (G : AddSubgroup A)
    (h : ∀ M : X.Modules, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
      f (VectorBundleKZero.classOf X M) ∈ G) (a : VectorBundleKZero X) : f a ∈ G := by
  have key : (QuotientAddGroup.mk' G).comp f = 0 :=
    VectorBundleKZero.addHom_ext fun M hM => by
      simp [QuotientAddGroup.eq_zero_iff, h M hM]
  simpa [QuotientAddGroup.eq_zero_iff] using DFunLike.congr_fun key a

/-! ### The rule of Tag 0FIE -/

section

variable (𝔄 : ChernSetup.{u, v, v₁, w} C S) [∀ X : C, Algebra ℚ (𝔄.A X)]
  (κ : ∀ {X Y : C}, (X ⟶ Y) → (VectorBundleKZero (S.obj Y) →+* VectorBundleKZero (S.obj X)))

/-- The degree-`n` part of the pullback of a cohomological Chern character along the morphism the
splitting principle produces, computed from the filtration: the class of `p^*ℰ` is the sum of the
classes of the invertible successive quotients, so the character of `p^*ℰ` is the sum of their
exponentials. -/
private theorem pull_coeff_eq_sum
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    {ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (κ f α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄 X (picardClassOf (S.obj X) L hL))
    {X P : C} (p : P ⟶ X) {E : (S.obj X).Modules}
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E) {k : ℕ}
    (L : Fin k → (S.obj P).Modules)
    (hL : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
      (S.obj P).ringCatSheaf.2 (L j))
    (hsum : VectorBundleKZero.classOf (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj E) =
      ∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) (n : ℕ) :
    𝔄.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E))) =
      ∑ j, algebraMap ℚ (𝔄.A P) ((n.factorial : ℚ)⁻¹) *
        𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n := by
  calc 𝔄.pull p (PowerSeries.coeff n (ch X (VectorBundleKZero.classOf (S.obj X) E)))
      = PowerSeries.coeff n
          (PowerSeries.map (𝔄.pull p) (ch X (VectorBundleKZero.classOf (S.obj X) E))) := by
        simp
    _ = ∑ j, PowerSeries.coeff n (ch P (VectorBundleKZero.classOf (S.obj P) (L j))) := by
        rw [hpull p _, hκ p E hE, hsum, map_sum]
        simp
    _ = ∑ j, algebraMap ℚ (𝔄.A P) ((n.factorial : ℚ)⁻¹) *
          𝔄.c₁ P (picardClassOf (S.obj P) (L j) (hL j)) ^ n :=
        Finset.sum_congr rfl fun j _ => by rw [hinv P (L j) (hL j), coeff_expFirstChernClass]

/-- **The uniqueness half of Stacks Tag 0FIE.** Two rules assigning to every object `X` of `𝒞` a
ring homomorphism `K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)`, compatible with pullbacks and taking
the value `exp(c_1^H(ℒ))` on every invertible module, agree on the class of every finite locally
free module of constant rank.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the prescribed value
determine the character; compatibility with pullbacks identifies the result with
`p^*ch^H([ℰ])`, and `p^*` is injective. -/
@[stacks 0FIE "uniqueness, for the class of a finite locally free module of constant rank: two \
  rules compatible with pullbacks and taking the value `exp(c₁^H(ℒ))` on an invertible module \
  agree there. Constant rank is the source's reduction by condition (2) of the situation of \
  Section 45.12, which `ChernSetup` does not transcribe, and the pullback homomorphism of \
  `K₀(Vect(-))`, which this repository does not construct, is a hypothesis"]
theorem eq_of_cohomologicalChernCharacter
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X)}
    (hpull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (κ f α))
    (hpull' : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
      PowerSeries.map (𝔄.pull f) (ch' Y α) = ch' X (κ f α))
    (hinv : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄 X (picardClassOf (S.obj X) L hL))
    (hinv' : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      ch' X (VectorBundleKZero.classOf (S.obj X) L) =
        expFirstChernClass 𝔄 X (picardClassOf (S.obj X) L hL))
    (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) := by
  classical
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  have hEflf := stacksFlf_of_isFiniteLocallyFreeOfRank hE
  refine PowerSeries.ext fun n => hinj ?_
  rw [pull_coeff_eq_sum 𝔄 κ hκ hpull hinv p hEflf L hL hsum n,
    pull_coeff_eq_sum 𝔄 κ hκ hpull' hinv' p hEflf L hL hsum n]

/-- **The existence half of Stacks Tag 0FIE.** The cohomological Chern character of a single
finite locally free module extends to a ring homomorphism
`ch^H : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}(X)(i)` for every object `X` of `𝒞`, which is graded,
compatible with pullbacks, and takes the value `exp(c_1^H(ℒ))` on an invertible module.

The extension is Tag 0FEM's universal property of the Grothendieck ring, applied to the given
additive, multiplicative and unital assignment; the grading and the compatibility with pullbacks
pass from the generators to all of `K₀(Vect(X))` because the graded series form a subgroup and
because both sides of the pullback equation are additive. -/
@[stacks 0FIE "existence: the rule, as a ring homomorphism out of `K₀(Vect(X))` into \
  `∏_{i ≥ 0} H^{2i}(X)(i)`, together with its grading, its compatibility with pullbacks and its \
  value `exp(c₁^H(ℒ))` on an invertible module. The cohomological Chern character of a single \
  finite locally free module, which Tag 0FI9's existence half constructs from the locally \
  constant rank `r^A` and the Chern classes of Tag 0FI5 on all of `K₀` — neither available \
  here, both resting on condition (2) of the situation, which `ChernSetup` does not transcribe \
  — is a hypothesis, as is the pullback homomorphism of `K₀(Vect(-))`"]
theorem exists_cohomologicalChernCharacter
    (hκ : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        κ f (VectorBundleKZero.classOf (S.obj Y) E) =
          VectorBundleKZero.classOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj E))
    (chM : ∀ X : C, (S.obj X).Modules → PowerSeries (𝔄.A X))
    (hzero : ∀ (X : C) (M : (S.obj X).Modules),
      ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M → chM X M = 0)
    (hadd : ∀ (X : C) {E F G : (S.obj X).Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} F →
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} G →
            Mono f → Epi g → (ShortComplex.mk f g w).Exact →
              chM X F = chM X E + chM X G)
    (hmul : ∀ (X : C) (M N : (S.obj X).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N →
          chM X (Scheme.Modules.tensorObjRingedSpace (S.obj X) M N) = chM X M * chM X N)
    (hone : ∀ X : C, chM X (SheafOfModules.unit (S.obj X).ringCatSheaf) = 1)
    (hgrade : ∀ (X : C) (M : (S.obj X).Modules), chM X M ∈ gradedPowerSeries 𝔄 X)
    (hinvM : ∀ (X : C) (L : (S.obj X).Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
        (S.obj X).ringCatSheaf.2 L),
      chM X L = expFirstChernClass 𝔄 X (picardClassOf (S.obj X) L hL))
    (hpullM : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        PowerSeries.map (𝔄.pull f) (chM Y E) =
          chM X ((Scheme.Modules.pullback (S.map f)).obj E))
    (hflf : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
          ((Scheme.Modules.pullback (S.map f)).obj E)) :
    ∃ ch : ∀ X : C, VectorBundleKZero (S.obj X) →+* PowerSeries (𝔄.A X),
      (∀ (X : C) (M : (S.obj X).Modules),
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
          ch X (VectorBundleKZero.classOf (S.obj X) M) = chM X M) ∧
        (∀ (X : C) (α : VectorBundleKZero (S.obj X)), ch X α ∈ gradedPowerSeries 𝔄 X) ∧
          (∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)),
            PowerSeries.map (𝔄.pull f) (ch Y α) = ch X (κ f α)) ∧
            ∀ (X : C) (L : (S.obj X).Modules)
              (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
                (S.obj X).ringCatSheaf.2 L),
              ch X (VectorBundleKZero.classOf (S.obj X) L) =
                expFirstChernClass 𝔄 X (picardClassOf (S.obj X) L hL) := by
  classical
  choose ch hch _hchuniq using fun X : C =>
    AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative
      (S.obj X) (chM X) (hzero X) (fun f g w => hadd X f g w) (hmul X) (hone X)
  refine ⟨ch, hch, fun X α => ?_, fun {X Y} f α => ?_, fun X L hL => ?_⟩
  · refine mem_of_classOf_mem (ch X).toAddMonoidHom _ (fun M hM => ?_) α
    show ch X (VectorBundleKZero.classOf (S.obj X) M) ∈ gradedPowerSeries 𝔄 X
    rw [hch X M hM]
    exact hgrade X M
  · refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
      (φ := (PowerSeries.map (𝔄.pull f)).toAddMonoidHom.comp (ch Y).toAddMonoidHom)
      (ψ := (ch X).toAddMonoidHom.comp (κ f).toAddMonoidHom) fun E hE => ?_) α
    show PowerSeries.map (𝔄.pull f) (ch Y (VectorBundleKZero.classOf (S.obj Y) E)) =
      ch X (κ f (VectorBundleKZero.classOf (S.obj Y) E))
    rw [hch Y E hE, hκ f E hE, hch X _ (hflf f E hE), hpullM f E hE]
  · rw [hch X L (stacksFlf_of_isInvertible L hL), hinvM X L hL]

end

end Stacks.WeilCohomology

end
