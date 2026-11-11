module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Formula
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksCore.Tactic.StacksAttribute

/-!
# The dual-basis step of Stacks 0FHH, with the Künneth expansion carried

This file proves the linear-algebra step of Stacks 0FHH; Stacks 0FHH itself, for the actual
cycle class of the diagonal and the actual Künneth decomposition, under (D0)–(D3), (A), (B) and
(C), is `Stacks.WeilCohomology.WeilData.pairing_kunnethComponentTw_diagonal` and
`Stacks.WeilCohomology.WeilData.pairing_diagonalKunnethCoordinates`
(`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/DiagonalDualBasis.lean`), which derive
the identity `hdecomp` assumed here.

Let `X` be a nonempty smooth projective scheme over `k`, equidimensional of dimension `d`, and
choose a basis `e_{i, 1}, …, e_{i, β_i}` of `H^i(X)` over `F`. Writing the cycle class of the
diagonal through the Künneth decomposition as

`γ([Δ]) = ∑_i ∑_j e_{i, j} ⊗ e'_{2d - i, j}` in `⨁_i H^i(X) ⊗_F H^{2d - i}(X)(d)`,

the classes `e'_{2d - i, j}` form the dual basis up to the sign `(-1)^i`:

`∫_X e_{i, j} ∪ e'_{2d - i, j'} = (-1)^i δ_{jj'}`.

The source's argument runs as follows. Because `γ([Δ]) = Δ_*1` and pullback along the diagonal
is the cup product, the diagonal class pairs two classes by
`∫_{X × X} γ([Δ]) ∪ (a ⊗ b) = ∫_X a ∪ b`, while the Künneth expansion of `γ([Δ])` evaluates
the same pairing as `∑_j (∫_X a ∪ e_{i, j}) (∫_X e'_{2d - i, j} ∪ b)`. Comparing the two identifies
`e'_{2d - i, j}` as the dual basis vector of `e_{i, j}` for the trace pairing, and graded
commutativity then contributes the sign `(-1)^{i(2d - i)} = (-1)^i`. This file proves only the
last step, the comparison: the expansion through `e` and `e'` is the hypothesis `hdecomp`.

## Main results

* `Stacks.WeilCohomology.dualBasis_of_pairing_decomposition`: the linear-algebra core. If a
  pairing with injective flip is expanded through a basis `e` and a family `e'`, then `e'` is the
  dual basis of `e`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_mul_dualBasis`: the
  conclusion `∫_X e_{i, j} ∪ e'_{2d - i, j'} = (-1)^i δ_{jj'}` of the source, for any family
  `e'` satisfying the expansion `hdecomp`, which is assumed rather than derived from the diagonal
  class.

## Implementation notes

The cohomological data is the Poincaré duality package
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`, the data `(D1)`, `(D3)` and condition
`(A)` of Section 45.9. `X` is an object of `(SmoothProjective k).FullSubcategory`, so smoothness
and projectivity are part of its type, and the dimension `d` of the source is `S.dimension X`,
which `PoincareDualityPushforwardSetup.dimension_eq` certifies as the topological dimension of `X`.
Nonemptiness and equidimensionality are explicit hypotheses; as elsewhere in this directory they
are not consumed by the argument, which uses only the trace map in degree `2d` and perfectness of
the trace pairing in complementary degrees — exactly what the package supplies and what those two
conditions are there to guarantee.

Tate twists are carried inside the graded pieces, as everywhere in this directory: the group
`H^{2d - i}(X)(d)` of the source is `(S.H X).piece (2 * d - i)`, and no separate twist appears.
The integral `∫_X x ∪ y` of two classes of complementary degrees is written out as the trace map
applied to their product, transported by `ExternallyGraded.degreeCast` from the degree in which
the product lives to the degree `2d` on which the trace is defined.

The Künneth decomposition of the diagonal class enters as the hypothesis `hdecomp`, in the form
in which the source's proof uses it: the identity
`∫_X a ∪ b = ∑_j (∫_X a ∪ e_j) (∫_X e'_j ∪ b)` between pairings of `H^{2d - i}(X)(d)` with
`H^i(X)`. Only the degree-`i` component of the Künneth decomposition contributes to it, which is
why a single degree `i` appears rather than a sum over degrees. The inputs it summarises are
Stacks 0FHG for `γ([Δ]) = Δ_*1`, Stacks 0FHD for the diagonal description of the cup product,
Stacks 0FHB and 0FHC for the projection formula and the pushforward along a projection, and
condition `(B)(b)` for the behaviour of the trace on a product; the source notes that the two
interchanges of order needed there cancel, so `hdecomp` carries no sign.

## References

* [Stacks Project, Tag 0FHH](https://stacks.math.columbia.edu/tag/0FHH)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w t

namespace Stacks.WeilCohomology

/-- Transport between graded pieces of equal degree sends only zero to zero. -/
private theorem eq_zero_of_degreeCast_eq_zero {F : Type v} [Field F] {P : ℤ → Type w}
    [∀ m, AddCommGroup (P m)] [∀ m, Module F (P m)] {p q : ℤ} (h : p = q) {x : P p}
    (hx : ExternallyGraded.degreeCast (R := F) (X := P) h x = 0) : x = 0 := by
  cases h
  exact hx

/-- Two transports of heterogeneously equal elements into the same graded piece agree. -/
private theorem degreeCast_eq_degreeCast_of_heq {F : Type v} [Field F] {P : ℤ → Type w}
    [∀ m, AddCommGroup (P m)] [∀ m, Module F (P m)] {p q r : ℤ} (h : p = r) (h' : q = r)
    {x : P p} {y : P q} (hxy : x ≍ y) :
    ExternallyGraded.degreeCast (R := F) (X := P) h x =
      ExternallyGraded.degreeCast (R := F) (X := P) h' y :=
  eq_of_heq ((ExternallyGraded.degreeCast_heq (R := F) (X := P) h x).trans
    (hxy.trans (ExternallyGraded.degreeCast_heq (R := F) (X := P) h' y).symm))

/-- The sign `(-1)^(2s)` is trivial. -/
private theorem gradedSign_two_mul (F : Type v) [Ring F] (s : ℤ) :
    DifferentialGraded.gradedSign F (2 * s) = 1 := by
  simp [DifferentialGraded.gradedSign, Int.natAbs_mul, pow_mul]

/-- The Koszul sign attached to a pair of degrees complementary in an even top degree:
`(-1)^{i(2m - i)} = (-1)^i`, since `i(2m - i)` and `i` differ by the even number
`2im - i(i + 1)`. -/
private theorem gradedSign_mul_two_mul_sub (F : Type v) [Ring F] (i m : ℤ) :
    DifferentialGraded.gradedSign F (i * (2 * m - i)) = DifferentialGraded.gradedSign F i := by
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self i
  have h : i * (2 * m - i) = i + 2 * (i * m - s) := by linear_combination -hs
  rw [h, DifferentialGraded.gradedSign_add, gradedSign_two_mul, mul_one]

/-- The linear-algebra core of Stacks 0FHH (used in its proof, not the lemma itself). Let `pair`
be a pairing of `U` with `V` whose flip is injective, let `e` be a finite basis of `V` and
`e' : J → U` a family indexed by the same set. If `pair` expands as
`pair a b = ∑ j pair a (e j) * pair (e' j) b` then `e'` is the dual basis of `e`, that is
`pair (e' j) (e j') = δ_{jj'}`. -/
theorem dualBasis_of_pairing_decomposition {F : Type v} [Field F] {U V : Type w}
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    (pair : U →ₗ[F] V →ₗ[F] F) (hpair : Function.Injective pair.flip)
    {J : Type t} [Fintype J] [DecidableEq J] (e : Module.Basis J F V) (e' : J → U)
    (hdecomp : ∀ (a : U) (b : V), pair a b = ∑ l : J, pair a (e l) * pair (e' l) b)
    (j j' : J) :
    pair (e' j) (e j') = if j = j' then 1 else 0 := by
  have hli : LinearIndependent F fun l : J => pair.flip (e l) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    refine Fintype.linearIndependent_iff.mp e.linearIndependent g (hpair ?_)
    rw [map_zero, map_sum]
    simpa using hg
  have hrep : ∀ m : J, pair.flip (e m) = ∑ l : J, pair (e' l) (e m) • pair.flip (e l) := by
    intro m
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.flip_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hdecomp a (e m)]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hsingle : ∀ m : J,
      ∑ l : J, (if l = m then (1 : F) else 0) • pair.flip (e l) = pair.flip (e m) := by
    intro m
    simp
  have hzero : ∀ (m l : J), pair (e' l) (e m) - (if l = m then (1 : F) else 0) = 0 := by
    intro m
    refine Fintype.linearIndependent_iff.mp hli _ ?_
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hrep m, hsingle m, sub_self]
  have := hzero j' j
  rwa [sub_eq_zero] at this

/-- The dual-basis identity for the trace pairing of a graded commutative algebra with a
perfect pairing in complementary degrees: the graded form of
`Stacks.WeilCohomology.dualBasis_of_pairing_decomposition`, with graded commutativity
contributing the Koszul sign. -/
private theorem integration_mul_dualBasis_aux {F : Type v} [Field F]
    (A : ExternallyGradedAlgebra.{v, w} F) (hA : A.IsGradedCommutative) (d : ℕ)
    (integration : A.piece (2 * (d : ℤ)) ≃ₗ[F] F) (i : ℤ)
    (hperf : (A.tracePairing d integration.toLinearMap (2 * (d : ℤ) - i)).IsPerfPair)
    {J : Type t} [Fintype J] [DecidableEq J]
    (e : Module.Basis J F (A.piece i)) (e' : J → A.piece (2 * (d : ℤ) - i))
    (hdecomp : ∀ (a : A.piece (2 * (d : ℤ) - i)) (b : A.piece i),
      integration (ExternallyGraded.degreeCast (R := F) (X := A.piece)
          (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega)
          (A.mul (2 * (d : ℤ) - i) i a b)) =
        ∑ l : J,
          integration (ExternallyGraded.degreeCast (R := F) (X := A.piece)
              (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega)
              (A.mul (2 * (d : ℤ) - i) i a (e l))) *
            integration (ExternallyGraded.degreeCast (R := F) (X := A.piece)
              (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega)
              (A.mul (2 * (d : ℤ) - i) i (e' l) b)))
    (j j' : J) :
    integration (ExternallyGraded.degreeCast (R := F) (X := A.piece)
        (show i + (2 * (d : ℤ) - i) = 2 * (d : ℤ) by omega)
        (A.mul i (2 * (d : ℤ) - i) (e j) (e' j'))) =
      DifferentialGraded.gradedSign F i * (if j = j' then 1 else 0) := by
  obtain ⟨pair, hpair_apply⟩ :
      ∃ pair : A.piece (2 * (d : ℤ) - i) →ₗ[F] A.piece i →ₗ[F] F,
        ∀ (a : A.piece (2 * (d : ℤ) - i)) (b : A.piece i),
          pair a b = integration (ExternallyGraded.degreeCast (R := F) (X := A.piece)
            (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega)
            (A.mul (2 * (d : ℤ) - i) i a b)) :=
    ⟨(A.mul (2 * (d : ℤ) - i) i).compr₂
      (integration.toLinearMap.comp (ExternallyGraded.degreeCast (R := F) (X := A.piece)
        (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega))), fun _ _ => rfl⟩
  have hflip : Function.Injective pair.flip := by
    have hbridge : ∀ (a : A.piece (2 * (d : ℤ) - i)) (b : A.piece i),
        A.tracePairing d integration.toLinearMap (2 * (d : ℤ) - i) a
            (ExternallyGraded.degreeCast (R := F) (X := A.piece)
              (show i = 2 * (d : ℤ) - (2 * (d : ℤ) - i) by omega) b) = pair a b := by
      intro a b
      rw [hpair_apply]
      simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
      congr 1
      exact degreeCast_eq_degreeCast_of_heq _ _
        (ExternallyGradedAlgebra.mul_degreeCast_heq (A := A) (2 * (d : ℤ) - i) i
          (2 * (d : ℤ) - (2 * (d : ℤ) - i)) (by omega) a b)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    refine eq_zero_of_degreeCast_eq_zero (F := F) (P := A.piece)
      (show i = 2 * (d : ℤ) - (2 * (d : ℤ) - i) by omega) ?_
    have := hperf
    refine (LinearMap.IsPerfPair.bijective_right
      (A.tracePairing d integration.toLinearMap (2 * (d : ℤ) - i))).injective ?_
    rw [map_zero]
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.flip_apply, LinearMap.zero_apply]
    rw [hbridge a b]
    have h0 := LinearMap.congr_fun hb a
    simpa using h0
  have hdual := dualBasis_of_pairing_decomposition pair hflip e e'
    (fun a b => by simp only [hpair_apply]; exact hdecomp a b) j' j
  rw [hpair_apply] at hdual
  have hcomm : ExternallyGraded.degreeCast (R := F) (X := A.piece)
        (show i + (2 * (d : ℤ) - i) = 2 * (d : ℤ) by omega)
        (A.mul i (2 * (d : ℤ) - i) (e j) (e' j')) =
      DifferentialGraded.gradedSign F (i * (2 * (d : ℤ) - i)) •
        ExternallyGraded.degreeCast (R := F) (X := A.piece)
          (show 2 * (d : ℤ) - i + i = 2 * (d : ℤ) by omega)
          (A.mul (2 * (d : ℤ) - i) i (e' j') (e j)) := by
    rw [← map_smul]
    exact degreeCast_eq_degreeCast_of_heq _ _
      (hA.graded_comm i (2 * (d : ℤ) - i) (e j) (e' j'))
  rw [hcomm, map_smul, smul_eq_mul, gradedSign_mul_two_mul_sub F i (d : ℤ), hdual]
  by_cases h : j = j'
  · simp [h]
  · simp [h, Ne.symm h]

namespace PoincareDualityPushforwardSetup

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

/-- **The dual-basis step of Stacks 0FHH, with the Künneth expansion carried.** Let `X` be a
nonempty smooth projective scheme over `k`, equidimensional of dimension `d = S.dimension X`, let
`e` be a basis of `H^i(X)` over `F`, and let `e' : J → H^{2d - i}(X)(d)` be any family satisfying
the expansion `hdecomp`: `∫_X a ∪ b = ∑_j (∫_X a ∪ e_j)(∫_X e'_j ∪ b)`. Then
`∫_X e_{i, j} ∪ e'_{2d - i, j'} = (-1)^i δ_{jj'}`.

This is not Stacks 0FHH: the package `PoincareDualityPushforwardSetup` has no cycle class map,
diagonal or Künneth isomorphism, and `hdecomp` is the consequence of the Künneth decomposition of
`γ([Δ])` that the source's proof derives (from Stacks 0FHG, 0FHD, 0FHB and axiom (B)(b)). Stacks
0FHH, with `e'` the Künneth coordinates of the actual `γ([Δ])` and that identity derived, is
`Stacks.WeilCohomology.WeilData.pairing_kunnethComponentTw_diagonal`. -/
theorem integration_mul_dualBasis (X : (SmoothProjective k).FullSubcategory)
    (_hne : Nonempty X.obj.left)
    (_hequi : TopologicalSpace.Equidimensional X.obj.left) (i : ℤ)
    {J : Type t} [Fintype J] [DecidableEq J]
    (e : Module.Basis J F ((S.H X).piece i))
    (e' : J → (S.H X).piece (2 * (S.dimension X : ℤ) - i))
    (hdecomp : ∀ (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)) (b : (S.H X).piece i),
      S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
          (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by omega)
          ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i a b)) =
        ∑ l : J,
          S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
              (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by omega)
              ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i a (e l))) *
            S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
              (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by omega)
              ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i (e' l) b)))
    (j j' : J) :
    S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show i + (2 * (S.dimension X : ℤ) - i) = 2 * (S.dimension X : ℤ) by omega)
        ((S.H X).mul i (2 * (S.dimension X : ℤ) - i) (e j) (e' j'))) =
      DifferentialGraded.gradedSign F i * (if j = j' then 1 else 0) :=
  integration_mul_dualBasis_aux (S.H X) (S.gradedComm X) (S.dimension X) (S.integration X) i
    (S.perfect X (2 * (S.dimension X : ℤ) - i)) e e' hdecomp j j'

end PoincareDualityPushforwardSetup

end Stacks.WeilCohomology

end
