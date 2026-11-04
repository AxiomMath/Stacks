module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# The staged lifting tower of a two-element cover, and the one step it does not supply

`StacksFrontier/Deformation/Examples/Linear/FlatAlgebraLiftCoprimeCover.lean` reduces the converse
of Stacks 0DZ7 at a principal multiplicative set to an auxiliary-free gluing principle: for a
comaximal pair `f, g` in a finite type flat `A`-algebra `B` with `A → B_h` syntomic for every
`h ∈ (f)`, and a surjection `A' → A` of Noetherian rings with nilpotent kernel `I`, a flat
`A'`-lift of `B_g` produces one of `B`. It is proved there at a square-zero kernel, and
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverDivisibleCorrection.lean` proves the
local-global algebra the nilpotent case asks for: the Čech splitting of the comparison class on
the overlap can be chosen with its `D(g)`-share divisible by any prescribed power of `f`, and a
variation map `δ + sq` with `δ` additive and `sq` homogeneous of degree two vanishes identically
on corrections divisible by a power of `f` that annihilates its target.

This file isolates what remains, as a statement about a tower of sets rather than about algebras.
Write `A_k = A'/I^(k+1)`, so that `A_0 = A` and `A_N = A'` when `I^(N+1) = 0`. The data the
deformation theory of the cover presents is: the stage-`k` lifts of `B`, the stage-`k` lifts of
`B_g`, the reduction maps between consecutive stages, the translation action of the deformation
module `T₁` on the fibres of a reduction, the obstruction in `T₂` whose vanishing is exactly
liftability by one stage, the variation of that obstruction along a translation — a Bockstein
plus a cup-square — the annihilation of `T₂` by `f ^ n`, and the one consequence of the Čech
splitting and Zariski descent that the gluing uses: a stage-`k` lift of `B` and a stage-`(k+1)`
lift of `B_g` above it assemble, after translating the latter by an `f ^ n`-divisible class, into
a stage-`(k+1)` lift of `B`. That bundle is `CoverLiftTower`.

**The induction, and the one step it does not supply.** The staged argument maintains at stage `k`
a lift of `B` over `A_k` whose restriction to `D(g)` still lifts all the way to `A'`, and advances
it by the gluing field. Advancing needs the invariant restored: the *translated* restriction must
again lift all the way to `A'`. Translating by an `f ^ n`-divisible class does not change the
obstruction (`CoverLiftTower.ob_tr_pow_smul`), so it does not change liftability by **one** stage
(`CoverLiftTower.liftsTo_one_tr_pow_smul`). Liftability by two or more stages is a different
matter, and nothing in the bundle delivers it: the variation formula compares two lifts of the
*same* object one stage down, while a lift of the translated object and a lift of the untranslated
one lie over different objects and are not comparable by it.

So the induction splits exactly in two. Where at most one stage remains it asks for nothing beyond
the bundle, which reaches the top of the tower when `N ≤ 2` — a kernel with `I³ = 0`, the first
case the tag leaves open (`CoverLiftTower.exists_gl_of_le_two`). Where two or more stages remain it
needs
`CoverLiftTower.WeakLink`, carried as an explicit hypothesis of
`CoverLiftTower.exists_gl_of_weakLink` and of nothing else.
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTowerIndependence.lean` builds a tower
satisfying every field of `CoverLiftTower` whose top stage is **empty**, so `WeakLink` is not a
consequence of the bundle: it is a further assertion about the deformation theory, and naming it
is the point of this file.

## Main definitions

* `Deformation.Examples.CoprimeCover.CoverLiftTower` — the staged lifting data of a two-element
  cover with one syntomic member.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.liftsTo` — being the reduction of a lift
  several stages up.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink` — the one step the bundle does not
  supply: an `f ^ n`-divisible translate of a class liftable by two or more stages is again
  liftable by that many stages.

## Main results

* `Deformation.Examples.CoprimeCover.CoverLiftTower.ob_tr_pow_smul` — an `f ^ n`-divisible
  translation does not change the obstruction. This is the abstract form of
  `Deformation.Examples.CoprimeCover.obstructionVariation_pow_smul_eq_zero`.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.liftsTo_one_tr_pow_smul` — hence it does not
  change liftability by one stage.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_weakLink` — the staged
  induction, granted `WeakLink`: the top stage is non-empty.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_le_two` — for `N ≤ 2` the same
  conclusion with **no** `WeakLink`, the weak link being needed only where two or more stages
  remain.
* `Deformation.Examples.CoprimeCover.exists_towerProj_eq_pow_smul` — the half of the natural repair
  of the weak link that does work: a class divisible by `f ^ (m * n)` rises `m` steps up a tower of
  coefficient modules whose obstructions are annihilated by `f ^ n`. See the implementation notes
  for why this does not close the gap.

## Implementation notes

**Why `T₁` and `T₂` do not depend on the stage.** In the deformation theory they do: the stage-`k`
translation module is `Ext¹(NL, · ⊗ I^k/I^(k+1))` and the stage-`k` obstruction module is the
corresponding `Ext²`. Carrying one module for all stages costs nothing, because a tower with
stage-dependent modules gives one of this shape by taking `T₁` and `T₂` to be their direct sums
and composing the Bockstein and the cup-square with the relevant projection: the fields quantify
over the stage, and nothing asks a class to be supported in one summand. Keeping the modules
stage-independent is what lets the instance arguments be ordinary instance arguments rather than
fields, which in turn is what makes the counterexample tower short.

**What the `glue` field abbreviates, and why it is not the gap.** It is the conclusion of the
local-global analysis: the syntomic member of the cover lifts freely at every stage, the two lifts
differ on the overlap by a class in `T₁`, that class splits with its `D(g)`-share divisible by
`f ^ n` (`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul`), and Zariski descent glues
the two corrected lifts. The three inputs are a proved lemma of this repository, a standard
consequence of syntomy, and descent along a two-element affine cover; the gap recorded here is not
there, which is why the field is stated as data rather than left to prose.

**The natural repair of the weak link, and where it stops.** It is worth recording, because it is
the first thing to try and it very nearly works. Write `I = ker(A' → A)` and let the stage-`k`
translation module have coefficients `I^(k+1)/I^(k+2)`. The correction to be carried up is
`f ^ n`-divisible, and the Čech splitting of
`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul` makes it divisible by *any* prescribed
power of `f`, so it may be taken divisible by `f ^ (m * n)` for any `m`. Now consider the tower of
coefficient modules `E_m = Ext¹(NL, · ⊗ I^(k+1)/I^(k+1+m))`: the obstruction to lifting a class one
step up it is a Bockstein into an `Ext²`, which `f ^ n` annihilates, so `f ^ n · E_m` lies in the
image of `E_(m+1)`, and iterating, a class divisible by `f ^ (m * n)` rises `m` steps. That is
`Deformation.Examples.CoprimeCover.exists_towerProj_eq_pow_smul`, proved below. So the chosen
correction *does* lift to a class with coefficients in the honest ideal `I^(k+1) ⊆ A'`, not merely
in one graded piece of it.

What that class does not do is move the lift. A class with coefficients in an ideal `J` twists the
lifts over a ring in which `J` is **square-zero**; for `J = I^(k+1)/I^(k+1+m)` inside
`A'/I^(k+1+m)` that asks `I^(2k+2) ⊆ I^(k+1+m)`, i.e. `m ≤ k + 1`. At the first filtration step,
`k = 0`, this permits exactly one extra stage — which is the one the variation formula already
gives — and the doubling `k + 1 ↦ 2k + 2` never gets started. So the deeper coefficients are
available and the operation that would use them is not, and that, concretely, is the gap. It is the
same place the cup-square term lives: `StacksFrontier/Deformation/ObstructionVariationQuadratic.lean`
records that the quadratic term dies from the second filtration step on and is present at the
first.

**What the bundle deliberately does not assume.** The translation is only assumed to act freely
and transitively on the fibres of a reduction (`tr_zero`, `tr_add`, `tr_eq_self`, `exists_tr`), the
obstruction only to detect liftability by one stage, and `f ^ n` only to annihilate `T₂`. No
finiteness, no exactness, no comparison between the fibres over two different objects — the last
being precisely what `WeakLink` would need, and precisely what the counterexample exploits.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Examples.CoprimeCover

/-! ### Lifting a divisible correction up a tower of coefficient modules -/

/-- The `m`-fold transition map of a tower of coefficient modules presented by one module and one
endomorphism. -/
def towerProj {B E : Type u} [CommRing B] [AddCommGroup E] [Module B E]
    (π : E →ₗ[B] E) : ℕ → (E →ₗ[B] E)
  | 0 => LinearMap.id
  | m + 1 => (towerProj π m).comp π

/-- **A class divisible by `f ^ (m * n)` rises `m` steps up a tower of coefficient modules whose
obstruction module is annihilated by `f ^ n`.**

Here `π` is the transition map of the tower, `δ` the obstruction to lifting one step along it — a
Bockstein, in the application — and `hrange` says that the obstruction cuts out the image of `π`
exactly. Each step costs one factor `f ^ n`: an obstruction class is annihilated by `f ^ n`, so
`f ^ n · x` always lifts one step, and `m` steps cost `f ^ (m * n)`.

This is the half of the natural repair of
`Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink` that does work. Applied to
`E_m = Ext¹(NL, · ⊗ I^(k+1)/I^(k+1+m))` it says that the `f`-divisible Čech correction supplied by
`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul` lifts to a class with coefficients in
the ideal `I^(k+1)` of `A'` itself, and not merely in one graded piece of it. What is missing is an
operation by which such a class moves a lift; see the implementation notes of this file. -/
theorem exists_towerProj_eq_pow_smul {B E F : Type u} [CommRing B] [AddCommGroup E] [Module B E]
    [AddCommGroup F] [Module B F] {f : B} {n : ℕ} (π : E →ₗ[B] E) (δ : E →ₗ[B] F)
    (hrange : ∀ x : E, (∃ y : E, π y = x) ↔ δ x = 0) (hann : ∀ t : F, f ^ n • t = 0)
    (m : ℕ) (x : E) : ∃ y : E, towerProj π m y = f ^ (m * n) • x := by
  induction m with
  | zero =>
    refine ⟨x, ?_⟩
    rw [Nat.zero_mul, pow_zero, one_smul]
    rfl
  | succ m ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := (hrange (f ^ n • y)).mpr (by rw [map_smul, hann])
    refine ⟨z, ?_⟩
    have hstep : towerProj π (m + 1) z = towerProj π m (π z) := rfl
    have hmn : (m + 1) * n = n + m * n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hmn, hstep, hz, map_smul, hy, smul_smul, ← pow_add]

/-! ### The staged lifting data -/

/-- **The staged lifting data of a two-element comaximal cover with one syntomic member.**

`B` is the algebra being lifted, `f` the equation of the syntomic member of the cover, `n` an
exponent with `f ^ n` annihilating the obstruction module, and `N` the number of stages of the
filtration of the kernel, so that stage `0` is the algebra itself and stage `N` is a lift over the
thickening. `T₁` is the module the lifts of a fixed object are a torsor under, and `T₂` the module
the obstruction to lifting one stage further lives in.

The fields are, in order: the stage-`k` lifts of `B` and of `B_g`; restriction to the member
`D(g)` and the two reduction maps, with their compatibility; the translation action of `T₁` on the
fibres of `redGg`, free and transitive; the obstruction, detecting liftability by one stage; the
Bockstein and cup-square parts of its variation along a translation; the annihilation of `T₂` by
`f ^ n`; and the gluing step furnished by the Čech splitting and Zariski descent. -/
structure CoverLiftTower (B : Type u) [CommRing B] (f : B) (n N : ℕ)
    (T₁ T₂ : Type u) [AddCommGroup T₁] [Module B T₁] [AddCommGroup T₂] [Module B T₂] where
  /-- The lifts of `B` over the `k`-th stage of the filtration of the kernel. -/
  Gl : ℕ → Type u
  /-- The lifts of `B_g` over the `k`-th stage of the filtration of the kernel. -/
  Gg : ℕ → Type u
  /-- Restriction of a lift of `B` to the member `D(g)` of the cover. -/
  res : ∀ {k : ℕ}, Gl k → Gg k
  /-- Reduction of a lift of `B` to the previous stage. -/
  redGl : ∀ {k : ℕ}, Gl (k + 1) → Gl k
  /-- Reduction of a lift of `B_g` to the previous stage. -/
  redGg : ∀ {k : ℕ}, Gg (k + 1) → Gg k
  /-- Restriction commutes with reduction. -/
  res_redGl : ∀ {k : ℕ} (x : Gl (k + 1)), res (redGl x) = redGg (res x)
  /-- The translation action of the deformation module on a fibre of `redGg`. -/
  tr : ∀ {k : ℕ}, T₁ → Gg (k + 1) → Gg (k + 1)
  /-- A translation does not move the reduction. -/
  redGg_tr : ∀ {k : ℕ} (c : T₁) (y : Gg (k + 1)), redGg (tr c y) = redGg y
  /-- Translating by zero does nothing. -/
  tr_zero : ∀ {k : ℕ} (y : Gg (k + 1)), tr (0 : T₁) y = y
  /-- Translation is an action. -/
  tr_add : ∀ {k : ℕ} (c d : T₁) (y : Gg (k + 1)), tr (c + d) y = tr c (tr d y)
  /-- The action is free. -/
  tr_eq_self : ∀ {k : ℕ} (c : T₁) (y : Gg (k + 1)), tr c y = y → c = 0
  /-- The action is transitive on each fibre of `redGg`. -/
  exists_tr : ∀ {k : ℕ} (y z : Gg (k + 1)), redGg y = redGg z → ∃ c : T₁, tr c y = z
  /-- The obstruction to lifting a lift of `B_g` one stage further. -/
  ob : ∀ {k : ℕ}, Gg k → T₂
  /-- The obstruction vanishes exactly when the lift extends one stage. -/
  ob_eq_zero_iff : ∀ {k : ℕ} (y : Gg k), ob y = 0 ↔ ∃ z : Gg (k + 1), redGg z = y
  /-- The additive, Bockstein part of the variation of the obstruction along a translation. -/
  bockstein : ℕ → (T₁ →ₗ[B] T₂)
  /-- The quadratic, cup-square part of that variation. -/
  cupSquare : ℕ → T₁ → T₂
  /-- The cup-square part is homogeneous of degree two. -/
  cupSquare_smul : ∀ (k : ℕ) (r : B) (c : T₁), cupSquare k (r • c) = r ^ 2 • cupSquare k c
  /-- **The variation of the obstruction along the torsor**, a Bockstein plus a cup-square. -/
  ob_tr : ∀ (k : ℕ) (c : T₁) (y : Gg (k + 1)),
    ob (tr c y) = ob y + bockstein k c + cupSquare k c
  /-- `f ^ n` annihilates the obstruction module, the syntomic member of the cover being
  unobstructed. -/
  pow_smul_eq_zero : ∀ t : T₂, f ^ n • t = 0
  /-- **The gluing step.** A lift of `B` at stage `k` and a lift of `B_g` at stage `k + 1` above
  its restriction assemble, after translating the latter by an `f ^ n`-divisible class, into a
  lift of `B` at stage `k + 1`. -/
  glue : ∀ (k : ℕ) (x : Gl k) (z : Gg (k + 1)), redGg z = res x →
    ∃ (b : T₁) (y : Gl (k + 1)), redGl y = x ∧ res y = tr (f ^ n • b) z

namespace CoverLiftTower

variable {B : Type u} [CommRing B] {f : B} {n N : ℕ} {T₁ T₂ : Type u}
  [AddCommGroup T₁] [Module B T₁] [AddCommGroup T₂] [Module B T₂]

/-- **Being the reduction of a lift `j` stages further up.** `D.liftsTo j k y` says that the
stage-`k` lift `y` of `B_g` is the image, under `j` successive reductions, of a stage-`(k + j)`
lift. For `j = 0` it is vacuous and for `j = 1` it is the vanishing of the obstruction
(`CoverLiftTower.liftsTo_one_iff`). -/
def liftsTo (D : CoverLiftTower B f n N T₁ T₂) : ℕ → (k : ℕ) → D.Gg k → Prop
  | 0, _, _ => True
  | j + 1, k, y => ∃ z : D.Gg (k + 1), D.redGg z = y ∧ liftsTo D j (k + 1) z

variable (D : CoverLiftTower B f n N T₁ T₂)

/-- Nothing is asked of a lift that need not rise at all. -/
theorem liftsTo_zero (k : ℕ) (y : D.Gg k) : D.liftsTo 0 k y := trivial

/-- Rising `j + 1` stages is rising one stage and then `j` more. -/
theorem liftsTo_succ (j k : ℕ) (y : D.Gg k) :
    D.liftsTo (j + 1) k y ↔ ∃ z : D.Gg (k + 1), D.redGg z = y ∧ D.liftsTo j (k + 1) z :=
  Iff.rfl

/-- Rising one stage is the vanishing of the obstruction. -/
theorem liftsTo_one_iff (k : ℕ) (y : D.Gg k) : D.liftsTo 1 k y ↔ D.ob y = 0 := by
  rw [D.ob_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨z, hz, -⟩ := h
    exact ⟨z, hz⟩
  · obtain ⟨z, hz⟩ := h
    exact ⟨z, hz, trivial⟩

/-- **A translation by an `f ^ n`-divisible class does not change the obstruction.** The Bockstein
part picks up a factor `f ^ n` from linearity and the cup-square part a factor `f ^ (2 * n)` from
homogeneity, and a single factor `f ^ n` already annihilates the obstruction module. This is the
abstract form of `Deformation.Examples.CoprimeCover.obstructionVariation_pow_smul_eq_zero`. -/
theorem ob_tr_pow_smul (k : ℕ) (b : T₁) (y : D.Gg (k + 1)) :
    D.ob (D.tr (f ^ n • b) y) = D.ob y := by
  rw [D.ob_tr, map_smul, D.pow_smul_eq_zero, D.cupSquare_smul, pow_two, mul_smul,
    D.pow_smul_eq_zero, add_zero, add_zero]

/-- **A translation by an `f ^ n`-divisible class does not change liftability by one stage.** This
is as far as the variation formula reaches: it compares two lifts of one and the same object, and
a lift of a translated object is not a lift of the untranslated one. -/
theorem liftsTo_one_tr_pow_smul (k : ℕ) (b : T₁) (y : D.Gg (k + 1))
    (hy : D.liftsTo 1 (k + 1) y) : D.liftsTo 1 (k + 1) (D.tr (f ^ n • b) y) := by
  rw [liftsTo_one_iff] at hy ⊢
  rw [D.ob_tr_pow_smul, hy]

/-- **The one step the staged induction does not supply.** It asserts that an `f ^ n`-divisible
translate of a class that rises `N - (k + 1)` stages again rises that many stages, in the range
where two or more stages remain — where one stage remains this is
`CoverLiftTower.liftsTo_one_tr_pow_smul` and where none remains it is vacuous.

Carrying it as a hypothesis is the honest form of the gluing argument for Stacks 0DZ7 past a
square-zero kernel: everything else the argument uses is a field of `CoverLiftTower`, and
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTowerIndependence.lean` exhibits a
tower in which every field holds and this fails.

Two things it is not. It is not minimal: the induction consumes it only at the classes the Čech
splitting of the comparison on the overlap actually produces, while it is stated for every
`f ^ n`-divisible class, so whoever proves it may assume less. And it is not necessary for the
gluing principle, only sufficient for this argument — a different route to the principle need not
pass through it. -/
def WeakLink : Prop :=
  ∀ k : ℕ, 2 ≤ N - (k + 1) → ∀ (b : T₁) (y : D.Gg (k + 1)),
    D.liftsTo (N - (k + 1)) (k + 1) y → D.liftsTo (N - (k + 1)) (k + 1) (D.tr (f ^ n • b) y)

/-- **The staged induction, granted the weak link.** Starting from a lift of `B` over `A` whose
restriction to `D(g)` rises all `N` stages — which is what a flat `A'`-lift of `B_g` provides —
the tower reaches its top stage.

At each stage the gluing field produces the next lift of `B`, at the cost of translating the
restriction by an `f ^ n`-divisible class; the invariant is that the restriction still rises to
the top. Restoring it needs no hypothesis where at most one stage remains, and needs `WeakLink`
where two or more do. -/
theorem exists_gl_of_weakLink (hWL : D.WeakLink) (x₀ : D.Gl 0)
    (h₀ : D.liftsTo N 0 (D.res x₀)) : Nonempty (D.Gl N) := by
  suffices H : ∀ k : ℕ, k ≤ N → ∃ x : D.Gl k, D.liftsTo (N - k) k (D.res x) by
    obtain ⟨x, -⟩ := H N le_rfl
    exact ⟨x⟩
  intro k
  induction k with
  | zero => exact fun _ => ⟨x₀, by simpa using h₀⟩
  | succ k ih =>
    intro hk
    obtain ⟨x, hx⟩ := ih (by omega)
    have hNk : N - k = N - (k + 1) + 1 := by omega
    rw [hNk, liftsTo_succ] at hx
    obtain ⟨z, hz, hz2⟩ := hx
    obtain ⟨b, y, -, hy2⟩ := D.glue k x z hz
    refine ⟨y, ?_⟩
    rw [hy2]
    rcases Nat.lt_or_ge (N - (k + 1)) 2 with hlt | hge
    · have h2 : N - (k + 1) = 0 ∨ N - (k + 1) = 1 := by omega
      rcases h2 with h1 | h1
      · rw [h1]
        exact D.liftsTo_zero _ _
      · rw [h1] at hz2 ⊢
        exact D.liftsTo_one_tr_pow_smul k b z hz2
    · exact hWL k hge b z hz2

/-- **At two stages the weak link is not needed.** With `N ≤ 2` — a kernel `I` with `I³ = 0`, the
first nilpotence index at which the converse of Stacks 0DZ7 is open — every application of the
weak link in `CoverLiftTower.exists_gl_of_weakLink` has at most one stage remaining, so it is
discharged by `CoverLiftTower.liftsTo_one_tr_pow_smul`.

So for such a kernel the gluing principle asks only for the staged lifting data itself, and the
one further assertion isolated here is not involved. -/
theorem exists_gl_of_le_two (hN : N ≤ 2) (x₀ : D.Gl 0)
    (h₀ : D.liftsTo N 0 (D.res x₀)) : Nonempty (D.Gl N) :=
  D.exists_gl_of_weakLink (fun k hk => absurd hk (by omega)) x₀ h₀

end CoverLiftTower

end Deformation.Examples.CoprimeCover

end
