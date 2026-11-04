module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Assembly
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.AugmentationDifferential
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.BoundaryRule
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.CycleModule

/-!
# A rule that kills the cycles of every degree resolves

The limiting family of a degree-by-degree recursion carries the limiting boundary, and the three
remaining fields of a Tate resolution — `augmentation_differential`, `exact_zero` and
`exact_positive` — hold for it as soon as the rule has four properties: every prescribed
boundary is a cycle, every boundary prescribed in degree zero is a coefficient lying in the
kernel of the presentation, those degree-zero boundaries span that kernel over the coefficients,
and in each positive degree the prescribed boundaries span the cycles of that degree.

The argument in positive degree `n` is the one the tower was built for. A cycle of degree `n` of
the limiting algebra comes from a cycle of degree `n` of the algebra after `n` rungs
(`exists_cycle_towerComparison`); the rung-`n` rule spans those cycles by the boundaries it
prescribes, so the cycle is a coefficient combination of them; the variables adjoined at rung
`n` have exactly those boundaries, pushed forward (`limitBoundary_rungVar`); and the same
combination of those variables is an element of degree `n + 1` whose differential is the cycle
(`chosenDifferential_sum_coefficient_mul_gen`).

Degree zero is the same argument with the kernel of `φ` in place of the cycles: the degree-zero
part of the algebra is the coefficients, the augmentation sends a coefficient to its image under
`φ`, and so a degree-zero element the augmentation kills is a coefficient lying over the kernel.
`augmentation_differential` is then one call to
`IndexedPresentation.augmentation_chosenDifferential_eq_zero`, whose only hypothesis on the
boundary is that the augmentation kills the boundaries of the variables of degree one — which it
does because those boundaries are coefficients of elements of the kernel.

## Main definitions

* `DividedPowers.TateResolution.IsResolvingRule` — the four conditions on a rule.

## Main results

* `DividedPowers.TateResolution.limitBoundary_rungVar` — the boundary the limiting family gives
  a variable adjoined at rung `k`.
* `DividedPowers.TateResolution.isResolvingBoundary_limitBoundary` — a resolving rule makes the
  limiting boundary of its tower a resolving boundary.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section Rule

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
  (ρ : BoundaryRule.{u, v, w} R P)

/-- The algebra on the limiting family of the tower of a rule. -/
public noncomputable abbrev ruleAlgebra :
    IndexedPresentation.{u, v, w} R P (towerLimit (ruleIdx R P ρ)) :=
  chosenPresentation R P (towerLimit (ruleIdx R P ρ))

/-- The boundary the limiting family of the tower of a rule carries. -/
public noncomputable abbrev ruleBoundary :
    (Σ n : ℕ, towerLimit (ruleIdx R P ρ) n) → (ruleAlgebra ρ).A :=
  limitBoundary R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ)

/-- The limiting boundary is homogeneous of the degree one below each variable's. -/
public theorem ruleBoundary_mem (j : Σ n : ℕ, towerLimit (ruleIdx R P ρ) n) :
    ruleBoundary ρ j ∈ (ruleAlgebra ρ).grade j.1 :=
  limitBoundary_mem R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) j

/-- The boundary the tower carries after `k` rungs. -/
public noncomputable abbrev rungBoundary (k : ℕ) :
    (Σ n : ℕ, towerIndices (ruleIdx R P ρ) k n) →
      (chosenPresentation R P (towerIndices (ruleIdx R P ρ) k)).A :=
  towerBoundary R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) k

/-- The boundary after `k` rungs is homogeneous. -/
public theorem rungBoundary_mem (k : ℕ)
    (j : Σ n : ℕ, towerIndices (ruleIdx R P ρ) k n) :
    rungBoundary ρ k j ∈ (chosenPresentation R P (towerIndices (ruleIdx R P ρ) k)).grade j.1 :=
  towerBoundary_mem R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) k j

/-- **The boundary the limiting family gives the `i`-th variable adjoined at rung `k`**: the
value the rule prescribed for it, pushed forward from the algebra after `k` rungs to the algebra
on the limiting family. -/
public theorem limitBoundary_rungVar (k : ℕ)
    (x : ruleIdx R P ρ (towerIndices (ruleIdx R P ρ) k) k) :
    ruleBoundary ρ ⟨k, cast (towerLimit_eq k).symm x⟩ =
      towerComparison R P (ruleIdx R P ρ) k
        (ρ.bdry (towerIndices (ruleIdx R P ρ) k) (rungBoundary ρ k) (rungBoundary_mem ρ k)
          k x.down.1) := by
  show towerComparison R P (ruleIdx R P ρ) (k + 1)
      (towerBoundary R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) (k + 1)
        ⟨k, cast (towerIndices_succ_self k).symm x⟩) = _
  rw [towerBoundary_succ_self, ← AlgHom.comp_apply, towerComparison_oneStepComparison]
  rfl

/-- Each degree of the limiting family is finite, since each rung adjoins finitely many
variables. -/
public theorem finite_ruleLimit (n : ℕ) : Finite (towerLimit (ruleIdx R P ρ) n) :=
  finite_towerLimit (fun f n => finite_ruleIdx R P ρ f n) n

/-- Each degree of the family after `k` rungs is finite. -/
public theorem finite_towerIndices_ruleIdx (k n : ℕ) :
    Finite (towerIndices (ruleIdx R P ρ) k n) :=
  finite_towerIndices (fun f n => finite_ruleIdx R P ρ f n) k n

/-- **A coefficient combination of the boundaries the rung-`k` rule prescribes, pushed forward to
the limiting algebra, is the differential of an element of degree `k + 1`.**

The element is the same combination of the variables adjoined at rung `k`, whose boundaries are
exactly those values pushed forward (`limitBoundary_rungVar`); its degree and its differential
are `chosenDifferential_sum_coefficient_mul_gen`. This is the step both the degree-zero and the
positive-degree exactness conditions reduce to. -/
public theorem exists_grade_succ_chosenDifferential_eq (k : ℕ) (c : ℕ → P)
    (y : (chosenPresentation R P (towerIndices (ruleIdx R P ρ) k)).A)
    (hy : y = ∑ i : Fin (ρ.size (towerIndices (ruleIdx R P ρ) k) (rungBoundary ρ k)
        (rungBoundary_mem ρ k) k),
      (chosenPresentation R P (towerIndices (ruleIdx R P ρ) k)).coefficient (c i.1) *
        ρ.bdry (towerIndices (ruleIdx R P ρ) k) (rungBoundary ρ k) (rungBoundary_mem ρ k) k i.1) :
    ∃ z : (ruleAlgebra ρ).A, z ∈ (ruleAlgebra ρ).grade (k + 1) ∧
      (ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ) z =
        towerComparison R P (ruleIdx R P ρ) k y := by
  set M := ρ.size (towerIndices (ruleIdx R P ρ) k) (rungBoundary ρ k)
    (rungBoundary_mem ρ k) k with hM
  set ja : Fin M → Σ n : ℕ, towerLimit (ruleIdx R P ρ) n := fun i =>
    ⟨k, cast (towerLimit_eq k).symm
      (ULift.up (Fin.cast (size_towerBoundary R P ρ k) i))⟩ with hja
  obtain ⟨hmem, hdiff⟩ := (ruleAlgebra ρ).chosenDifferential_sum_coefficient_mul_gen
    (ruleBoundary ρ) (ruleBoundary_mem ρ) Finset.univ (fun i : Fin M => c i.1) ja k
    (fun _ => rfl)
  refine ⟨_, hmem, ?_⟩
  rw [hdiff, hy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  exact congrArg₂ _ (IndexedPresentation.comparison_coefficient _ _ _ _).symm
    (limitBoundary_rungVar ρ k _)

/-- Pushing a coefficient forward along the comparison out of rung `k` gives the coefficient. -/
public theorem towerComparison_coefficient (k : ℕ) (p : P) :
    towerComparison R P (ruleIdx R P ρ) k
        ((chosenPresentation R P (towerIndices (ruleIdx R P ρ) k)).coefficient p) =
      (ruleAlgebra ρ).coefficient p :=
  IndexedPresentation.comparison_coefficient _ _ _ p

/-- Every variable of degree `n + 1` of the limiting family is one the rung-`n` rule adjoined. -/
public theorem cast_towerLimit_eq (n : ℕ) (v : towerLimit (ruleIdx R P ρ) n) :
    cast (towerLimit_eq n).symm (cast (towerLimit_eq n) v) = v :=
  eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

section Resolving

variable {S : Type w} [CommRing S] [Algebra R S] (φ : P →ₐ[R] S)

/-- **The conditions on a rule under which the limiting boundary of its tower is a resolving
boundary for `φ`**: every prescribed boundary is a cycle, every boundary prescribed in degree
zero is a coefficient of an element of the kernel of `φ`, those boundaries span the coefficients
of the kernel, and in each positive degree the prescribed boundaries span the cycles.

The spanning conditions are stated as explicit finite coefficient combinations rather than as
submodule spans, so that they need no module structure over the coefficient algebra. -/
public structure IsResolvingRule : Prop where
  /-- Every prescribed boundary is a cycle, so the algebra is a differential graded algebra. -/
  cycle : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (k i : ℕ),
    (chosenPresentation.{u, v, w} R P f).chosenDifferential b hb (ρ.bdry f b hb k i) = 0
  /-- Every boundary prescribed in degree zero is a coefficient of an element of `ker φ`. -/
  kernel : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (i : ℕ),
    ∃ p : P, φ p = 0 ∧
      ρ.bdry f b hb 0 i = (chosenPresentation.{u, v, w} R P f).coefficient p
  /-- The boundaries prescribed in degree zero span the coefficients of `ker φ`. -/
  span_zero : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1),
    (∀ n : ℕ, Finite (f n)) → ∀ p : P, φ p = 0 →
    ∃ c : ℕ → P, (chosenPresentation.{u, v, w} R P f).coefficient p =
      ∑ i : Fin (ρ.size f b hb 0),
        (chosenPresentation.{u, v, w} R P f).coefficient (c i.1) * ρ.bdry f b hb 0 i.1
  /-- The boundaries prescribed in a positive degree span the cycles of that degree. -/
  span_pos : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1),
    (∀ n : ℕ, Finite (f n)) → ∀ k : ℕ, 0 < k →
    ∀ y : (chosenPresentation.{u, v, w} R P f).A,
    y ∈ (chosenPresentation.{u, v, w} R P f).grade k →
    (chosenPresentation.{u, v, w} R P f).chosenDifferential b hb y = 0 →
    ∃ c : ℕ → P, y = ∑ i : Fin (ρ.size f b hb k),
      (chosenPresentation.{u, v, w} R P f).coefficient (c i.1) * ρ.bdry f b hb k i.1

/-- **A resolving rule makes the limiting boundary of its tower a resolving boundary.** This is
`IsResolvingBoundary` for the algebra on the limiting family, spelled out, so the whole of the
finite assertion of [Stacks, Tag 09PN] is reduced to exhibiting a resolving rule. -/
public theorem isResolvingBoundary_limitBoundary (h : IsResolvingRule ρ φ) :
    (∀ j : Σ n : ℕ, towerLimit (ruleIdx R P ρ) n,
        (ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ)
          (ruleBoundary ρ j) = 0) ∧
      ∀ a : (ruleAlgebra ρ).A →ₐ[R] S,
        (∀ p : P, a ((ruleAlgebra ρ).coefficient p) = φ p) →
        (∀ j : Σ n : ℕ, towerLimit (ruleIdx R P ρ) n, a ((ruleAlgebra ρ).gen j) = 0) →
        (∀ (n : ℕ) (x : (ruleAlgebra ρ).A), 0 < n → x ∈ (ruleAlgebra ρ).grade n → a x = 0) →
        (∀ x : (ruleAlgebra ρ).A,
          a ((ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ) x) = 0) ∧
        (∀ x : (ruleAlgebra ρ).A, x ∈ (ruleAlgebra ρ).grade 0 → a x = 0 →
          ∃ y : (ruleAlgebra ρ).A, y ∈ (ruleAlgebra ρ).grade 1 ∧
            (ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ) y = x) ∧
        (∀ (n : ℕ) (x : (ruleAlgebra ρ).A), 0 < n → x ∈ (ruleAlgebra ρ).grade n →
          (ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ) x = 0 →
          ∃ y : (ruleAlgebra ρ).A, y ∈ (ruleAlgebra ρ).grade (n + 1) ∧
            (ruleAlgebra ρ).chosenDifferential (ruleBoundary ρ) (ruleBoundary_mem ρ) y = x) := by
  have hrep : ∀ (n : ℕ) (v : towerLimit (ruleIdx R P ρ) n),
      ∃ x : ruleIdx R P ρ (towerIndices (ruleIdx R P ρ) n) n,
        v = cast (towerLimit_eq n).symm x :=
    fun n v => ⟨cast (towerLimit_eq n) v, (cast_towerLimit_eq ρ n v).symm⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨n, v⟩
    obtain ⟨x, rfl⟩ := hrep n v
    rw [limitBoundary_rungVar ρ n x]
    exact (IndexedPresentation.comparison_differential_eq_zero_iff
      (chosenPresentation R P (towerIndices (ruleIdx R P ρ) n)) (ruleAlgebra ρ)
      (towerEmbed (ruleIdx R P ρ) n) (rungBoundary ρ n) (rungBoundary_mem ρ n)
      (ruleBoundary ρ) (ruleBoundary_mem ρ) (towerRetract (ruleIdx R P ρ) n)
      (towerRetract_towerEmbed n)
      (limitBoundary_towerEmbed R P (ruleIdx R P ρ) (ruleBdry R P ρ)
        (ruleBdry_mem R P ρ) n) _).mpr
      (h.cycle (towerIndices (ruleIdx R P ρ) n) (rungBoundary ρ n) (rungBoundary_mem ρ n)
        n x.down.1)
  · intro a ha1 ha2 ha3
    have hzero : ∀ j : Σ n : ℕ, towerLimit (ruleIdx R P ρ) n, j.1 = 0 →
        a (ruleBoundary ρ j) = 0 := by
      rintro ⟨n, v⟩ hn
      subst hn
      obtain ⟨x, hxv⟩ := hrep 0 v
      obtain ⟨p, hp0, hpe⟩ := h.kernel (towerIndices (ruleIdx R P ρ) 0) (rungBoundary ρ 0)
        (rungBoundary_mem ρ 0) x.down.1
      rw [hxv, limitBoundary_rungVar ρ 0 x, hpe, towerComparison_coefficient ρ 0 p, ha1 p,
        hp0]
    refine ⟨fun x => (ruleAlgebra ρ).augmentation_chosenDifferential_eq_zero (ruleBoundary ρ)
      (ruleBoundary_mem ρ) a ha3 hzero x, ?_, ?_⟩
    · intro x hx hax
      obtain ⟨p, hp⟩ :=
        (mem_grade_zero_iff_exists_coefficient (ruleAlgebra ρ).polynomial x).mp hx
      have hφp : φ p = 0 := by
        rw [← ha1 p, hp]
        exact hax
      obtain ⟨c, hc⟩ := h.span_zero (towerIndices (ruleIdx R P ρ) 0) (rungBoundary ρ 0)
        (rungBoundary_mem ρ 0) (fun n => finite_towerIndices_ruleIdx ρ 0 n) p hφp
      obtain ⟨z, hz1, hz2⟩ := exists_grade_succ_chosenDifferential_eq ρ 0 c _ hc
      refine ⟨z, hz1, ?_⟩
      rw [hz2, towerComparison_coefficient ρ 0 p, hp]
    · intro n x hn hx hdx
      obtain ⟨y, hy1, hy2, hy3⟩ := exists_cycle_towerComparison R P (ruleIdx R P ρ)
        (ruleBdry R P ρ) (ruleBdry_mem R P ρ) n n le_rfl x hx hdx
      obtain ⟨c, hc⟩ := h.span_pos (towerIndices (ruleIdx R P ρ) n) (rungBoundary ρ n)
        (rungBoundary_mem ρ n) (fun m => finite_towerIndices_ruleIdx ρ n m) n hn y hy1 hy2
      obtain ⟨z, hz1, hz2⟩ := exists_grade_succ_chosenDifferential_eq ρ n c y hc
      exact ⟨z, hz1, by rw [hz2, hy3]⟩

end Resolving

end Rule

end DividedPowers.TateResolution

end
