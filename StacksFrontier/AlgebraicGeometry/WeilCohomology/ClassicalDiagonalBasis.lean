module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalSecondProjection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTraceDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.DiagonalBasis

/-!
# The Künneth coordinates of the diagonal class are a signed dual basis

Stacks 0FGZ: let `H^*` be a classical Weil cohomology theory and `X` a smooth projective variety
of dimension `d`. Choose a basis `e_{i, 1}, …, e_{i, β_i}` of `H^i(X)` and write, using Künneth,

`γ([Δ]) = ∑_i ∑_j e_{i, j} ⊗ e'_{2d - i, j}` in `⨁_i H^i(X) ⊗_F H^{2d - i}(X)`.

Then `∫_X e_{i, j} ∪ e'_{2d - i, j'} = (-1)^i δ_{jj'}`.

The argument is the source's, in two halves.

* The cohomological half uses only Poincaré duality and the Künneth formula. Let `P` with
  projections `p, q : P ⟶ X` satisfy the Künneth formula, let `δ : X ⟶ P` be a common section of
  `p` and `q`, and let the trace of `P` factor as `∫_P p^*u ∪ q^*v = (∫_X u)(∫_X v)` on top
  classes. Pulling back along `δ` is the cup product, so the trace equation of the pushforward
  gives `∫_P (p^*a ∪ q^*b) ∪ δ_*1 = ∫_X a ∪ b`. Evaluating the same functional on the Künneth
  expansion of `δ_*1` gives `∑_j (∫_X a ∪ e_{i, j})(∫_X e'_{2d - i, j} ∪ b)`: the components of
  every other bidegree contribute nothing, and the two Koszul signs cancel. The resulting identity
  is the hypothesis of the base's
  `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_mul_dualBasis`, which
  concludes.
* The cycle half is for the Chow groups of Chapter 42
  (`Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`). There `γ([Δ]) = δ_*γ([X]) = δ_*1`
  by axiom `(C)(b)` for `δ`, the identity `δ_*[X] = [Δ]` of cycles
  (`Stacks.WeilCohomology.equidimensionalPushforward_fundamentalClass`) and `γ([X]) = 1`. The
  factorisation of the trace is Stacks 0FGX.

## Main results

* `PoincareDualityPushforwardSetup.integration_mul_kunnethCoordinate_pushforward_one`: the
  Künneth coordinates of `δ_*1` are the signed dual basis.
* `ChowClassicalWeilCohomologyTheory.cycleClass_diagonal_heq`: `γ([Δ]) = δ_*1`.
* `ChowClassicalWeilCohomologyTheory.integration_mul_diagonalKunnethCoordinate`:
  **Stacks 0FGZ**.

## Implementation notes

The product `X × X` is a smooth projective variety `P` with two morphisms exhibiting it as the
fibre product over `k`, as in the Künneth axiom of
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`. The diagonal is a morphism `δ : X ⟶ P`
with `δ ≫ p = δ ≫ q = 𝟙`, and it is a closed immersion
(`SmoothProjective.isClosedImmersion_of_section`). The class `[Δ] ∈ CH^d(P)` is
`Stacks.WeilCohomology.closedSubschemeClass` of `δ`.

The traces are read in every degree through `ExternallyGradedAlgebra.traceExtension`, which
vanishes off the top degree and takes heterogeneously equal arguments of equal degrees to the
same value; this lets the identities of the graded algebra, which hold only heterogeneously, be
used without transporting between graded pieces. The Künneth expansion is read through
`TensorProduct.directSum`, the identification of `H^*(X) ⊗_F H^*(X)` with
`⨁_{(i, j)} H^i(X) ⊗_F H^j(X)` that the Künneth map is built from. Only its `(i, 2d - i)`
component is constrained, which is the degree-`i` part of the source's decomposition and the
only part the conclusion for that `i` concerns.

## References

* [Stacks Project, Tag 0FGZ](https://stacks.math.columbia.edu/tag/0FGZ)
* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory DifferentialGraded
open scoped DirectSum TensorProduct

universe u v w t

namespace ExternallyGradedAlgebra

/-- Heterogeneously equal right factors of equal degrees have heterogeneously equal products with
a common left factor. -/
theorem mul_congr_right_heq {R : Type v} [CommRing R] {A : ExternallyGradedAlgebra.{v, w} R}
    {i j j' : ℤ} (h : j = j') (x : A.piece i) {y : A.piece j} {y' : A.piece j'} (hyy : y ≍ y') :
    A.mul i j x y ≍ A.mul i j' x y' := by
  subst h
  rw [eq_of_heq hyy]

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

namespace PoincareDualityPushforwardSetup

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

variable {X P : (SmoothProjective k).FullSubcategory} (p q : P ⟶ X)

/-- The trace of a product of two exterior products: moving `q^*y` past `p^*a` costs the Koszul
sign `(-1)^{j m}`, and the result is the exterior product of `x ∪ a` and `y ∪ b`,
`∫_{X × X} (p^*x ∪ q^*y) ∪ (p^*a ∪ q^*b) = (-1)^{jm} (∫_X x ∪ a)(∫_X y ∪ b)`. -/
theorem traceExtension_mul_mul_pullback (hP : S.dimension P = S.dimension X + S.dimension X)
    (hprod : ∀ u v : (S.H X).piece (2 * (S.dimension X : ℤ)),
      S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
          (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension X : ℤ) =
            2 * (S.dimension P : ℤ) by rw [hP]; push_cast; ring)
          ((S.H P).mul _ _ (S.pullback p _ u) (S.pullback q _ v))) =
        S.integration X u * S.integration X v)
    (i j m n : ℤ) (x : (S.H X).piece i) (y : (S.H X).piece j) (a : (S.H X).piece m)
    (b : (S.H X).piece n) :
    (S.H P).traceExtension (S.dimension P) (S.integration P).toLinearMap (i + j + (m + n))
        ((S.H P).mul (i + j) (m + n) ((S.H P).mul i j (S.pullback p i x) (S.pullback q j y))
          ((S.H P).mul m n (S.pullback p m a) (S.pullback q n b))) =
      gradedSign F (j * m) *
        ((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap (i + m)
            ((S.H X).mul i m x a) *
          (S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap (j + n)
            ((S.H X).mul j n y b)) := by
  set A := S.H P
  set X' := S.pullback p i x
  set Y' := S.pullback q j y
  set A' := S.pullback p m a
  set B' := S.pullback q n b
  have hinner : A.mul j (m + n) Y' (A.mul m n A' B') ≍
      gradedSign F (j * m) • A.mul m (j + n) A' (A.mul j n Y' B') := by
    refine (A.mul_assoc j m n Y' A' B').symm.trans ?_
    refine (ExternallyGradedAlgebra.mul_congr_left_heq (A := A) (by ring)
      ((S.gradedComm P).graded_comm j m Y' A') B').trans ?_
    rw [map_smul, LinearMap.smul_apply]
    exact ExternallyGraded.scalar_heq (by ring) rfl (A.mul_assoc m j n A' Y' B')
  have hall : A.mul (i + j) (m + n) (A.mul i j X' Y') (A.mul m n A' B') ≍
      gradedSign F (j * m) • A.mul (i + m) (j + n) (A.mul i m X' A') (A.mul j n Y' B') := by
    refine (A.mul_assoc i j (m + n) X' Y' _).trans ?_
    refine (ExternallyGradedAlgebra.mul_congr_right_heq (A := A) (by ring) X' hinner).trans ?_
    rw [map_smul]
    exact ExternallyGraded.scalar_heq (by ring) rfl
      (A.mul_assoc i m (j + n) X' A' (A.mul j n Y' B')).symm
  rw [ExternallyGradedAlgebra.traceExtension_congr _ _ _ (by ring) hall, map_smul, smul_eq_mul,
    ← S.pullback_mul, ← S.pullback_mul, S.traceExtension_mul_pullback p q hP hprod]

/-- Pairing against the pushforward of the unit is integration of the pullback:
`∫_P c ∪ δ_*1 = ∫_X δ^*c` for `c` of degree `2 dim X`. -/
theorem traceExtension_mul_pushforward_one (δ : X ⟶ P)
    (c : (S.H P).piece (2 * (S.dimension X : ℤ))) :
    (S.H P).traceExtension (S.dimension P) (S.integration P).toLinearMap
        (2 * (S.dimension X : ℤ) + (2 * (S.dimension P : ℤ) - 2 * (S.dimension X : ℤ)))
        ((S.H P).mul _ _ c (S.pushforward δ (2 * (S.dimension X : ℤ))
          (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
            (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension X : ℤ) by ring)
            (S.H X).one))) =
      (S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap (2 * (S.dimension X : ℤ))
        (S.pullback δ _ c) := by
  have h := S.integration_pullback_mul δ (2 * (S.dimension X : ℤ)) c
    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
      (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension X : ℤ) by ring) (S.H X).one)
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] at h
  rw [ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ (by ring),
    ExternallyGradedAlgebra.traceExtension_self, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← h]
  congr 1
  refine eq_of_heq ((ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_)
  refine (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H X) _ 0 _ (by ring) _ _).trans ?_
  exact (S.H X).mul_one _ _

omit [CharZero F] in
/-- The Koszul signs of the pairing computation cancel: `(-1)^{(2d - i)(2d - i)} (-1)^{i(2d - i)}
= 1`. -/
private theorem gradedSign_cancel (i d : ℤ) :
    gradedSign F ((2 * d - i) * (2 * d - i)) * gradedSign F (i * (2 * d - i)) = 1 := by
  rw [← gradedSign_add, show (2 * d - i) * (2 * d - i) + i * (2 * d - i) =
    2 * ((2 * d - i) * d) by ring, gradedSign_two_mul]

/-- The extended trace of a cup product changes by the Koszul sign when the factors are swapped. -/
private theorem traceExtension_mul_comm (Y : (SmoothProjective k).FullSubcategory) (i j : ℤ)
    (x : (S.H Y).piece i) (y : (S.H Y).piece j) :
    (S.H Y).traceExtension (S.dimension Y) (S.integration Y).toLinearMap (i + j)
        ((S.H Y).mul i j x y) =
      gradedSign F (i * j) *
        (S.H Y).traceExtension (S.dimension Y) (S.integration Y).toLinearMap (j + i)
          ((S.H Y).mul j i y x) := by
  rw [ExternallyGradedAlgebra.traceExtension_congr _ _ _ (add_comm i j)
    ((S.gradedComm Y).graded_comm i j x y), map_smul, smul_eq_mul]

/-- **The Künneth coordinates of `δ_*1` are the signed dual basis.** Let `P` with projections
`p, q : P ⟶ X` satisfy the Künneth formula, let `δ : X ⟶ P` be a common section of `p` and `q`,
and let the trace of `P` factor as `∫_P p^*u ∪ q^*v = (∫_X u)(∫_X v)` on top classes. If the
`(i, 2d - i)` Künneth coordinate of `δ_*1` is `∑_j e_j ⊗ e'_j` for a basis `e` of `H^i(X)`, then
`∫_X e_j ∪ e'_{j'} = (-1)^i δ_{jj'}`. -/
theorem integration_mul_kunnethCoordinate_pushforward_one
    (hP : S.dimension P = S.dimension X + S.dimension X)
    (hprod : ∀ u v : (S.H X).piece (2 * (S.dimension X : ℤ)),
      S.integration P (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
          (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension X : ℤ) =
            2 * (S.dimension P : ℤ) by rw [hP]; push_cast; ring)
          ((S.H P).mul _ _ (S.pullback p _ u) (S.pullback q _ v))) =
        S.integration X u * S.integration X v)
    (hK : Function.Bijective
      (Stacks.WeilCohomology.kunnethMap (S.H X) (S.H X) (S.H P) (fun i => S.pullback p i)
        fun j => S.pullback q j))
    (δ : X ⟶ P) (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X)
    (i : ℤ) {J : Type t} [Fintype J] [DecidableEq J]
    (e : Module.Basis J F ((S.H X).piece i))
    (e' : J → (S.H X).piece (2 * (S.dimension X : ℤ) - i))
    (hdecomp :
      DirectSum.component F (ℤ × ℤ) (fun ij => (S.H X).piece ij.1 ⊗[F] (S.H X).piece ij.2)
          (i, 2 * (S.dimension X : ℤ) - i)
          (TensorProduct.directSum F F (fun n : ℤ => (S.H X).piece n)
            (fun n : ℤ => (S.H X).piece n)
            ((LinearEquiv.ofBijective _ hK).symm
              (DirectSum.lof F ℤ (fun n => (S.H P).piece n) (2 * (S.dimension X : ℤ))
                (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
                  (show 2 * (S.dimension P : ℤ) - 2 * (S.dimension X : ℤ) =
                    2 * (S.dimension X : ℤ) by omega)
                  (S.pushforward δ (2 * (S.dimension X : ℤ))
                    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
                      (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension X : ℤ) by
                        ring)
                      (S.H X).one)))))) =
        ∑ j : J, e j ⊗ₜ[F] e' j)
    (j j' : J) :
    S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show i + (2 * (S.dimension X : ℤ) - i) = 2 * (S.dimension X : ℤ) by omega)
        ((S.H X).mul i (2 * (S.dimension X : ℤ) - i) (e j) (e' j'))) =
      gradedSign F i * (if j = j' then 1 else 0) := by
  have : IsIntegral X.obj.left := X.property.1.toIsIntegral
  refine S.integration_mul_dualBasis X inferInstance
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace _) i e e' ?_ j j'
  intro a b
  set D := S.pushforward δ (2 * (S.dimension X : ℤ))
    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
      (show (0 : ℤ) = 2 * (S.dimension X : ℤ) - 2 * (S.dimension X : ℤ) by ring)
      (S.H X).one) with hD
  set c := ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
    (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by ring)
    ((S.H P).mul (2 * (S.dimension X : ℤ) - i) i (S.pullback p _ a) (S.pullback q _ b)) with hc
  -- the functional `z ↦ ∫_P z ∪ (a × b)` on the cohomology of `P`
  let Φ : (⨁ n : ℤ, (S.H P).piece n) →ₗ[F] F :=
    DirectSum.toModule F ℤ F fun n =>
      ((S.H P).traceExtension (S.dimension P) (S.integration P).toLinearMap
        (n + 2 * (S.dimension X : ℤ))).comp
      (((S.H P).mul n (2 * (S.dimension X : ℤ))).flip c)
  -- the functional it becomes through the Künneth formula
  let Ψ : (⨁ ij : ℤ × ℤ, (S.H X).piece ij.1 ⊗[F] (S.H X).piece ij.2) →ₗ[F] F :=
    DirectSum.toModule F (ℤ × ℤ) F fun ij =>
      gradedSign F (ij.2 * (2 * (S.dimension X : ℤ) - i)) • TensorProduct.lift
      ((LinearMap.mul F F).compl₁₂
        (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
            (ij.1 + (2 * (S.dimension X : ℤ) - i))).comp
          (((S.H X).mul ij.1 (2 * (S.dimension X : ℤ) - i)).flip a))
        (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
            (ij.2 + i)).comp (((S.H X).mul ij.2 i).flip b)))
  have hΦK : ∀ z, Φ (Stacks.WeilCohomology.kunnethMap (S.H X) (S.H X) (S.H P)
      (fun i => S.pullback p i) (fun j => S.pullback q j) z) =
      Ψ (TensorProduct.directSum F F (fun n : ℤ => (S.H X).piece n)
        (fun n : ℤ => (S.H X).piece n) z) := by
    intro z
    suffices hext : Φ.comp (DirectSum.toModule F (ℤ × ℤ) _ fun ij =>
        (DirectSum.lof F ℤ (fun n => (S.H P).piece n) (ij.1 + ij.2)).comp
          (TensorProduct.lift ((((S.H P).mul ij.1 ij.2).comp (S.pullback p ij.1)).compl₂
            (S.pullback q ij.2)))) = Ψ from LinearMap.congr_fun hext _
    refine DirectSum.linearMap_ext F fun ij => TensorProduct.ext' fun x y => ?_
    simp only [Φ, Ψ, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul,
      LinearMap.compl₂_apply, LinearMap.flip_apply, LinearMap.smul_apply,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply', smul_eq_mul]
    rw [ExternallyGradedAlgebra.traceExtension_congr _ _ _
      (show _ = ij.1 + ij.2 + (2 * (S.dimension X : ℤ) - i + i) by ring)
      (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H P) _ _ _ _ _ _)]
    exact S.traceExtension_mul_mul_pullback p q hP hprod _ _ _ _ x y a b
  have hΨ : ∀ y, Ψ y =
      gradedSign F ((2 * (S.dimension X : ℤ) - i) * (2 * (S.dimension X : ℤ) - i)) *
      TensorProduct.lift ((LinearMap.mul F F).compl₁₂
        (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
            (i + (2 * (S.dimension X : ℤ) - i))).comp
          (((S.H X).mul i (2 * (S.dimension X : ℤ) - i)).flip a))
        (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
            ((2 * (S.dimension X : ℤ) - i) + i)).comp
          (((S.H X).mul (2 * (S.dimension X : ℤ) - i) i).flip b)))
        (DirectSum.component F (ℤ × ℤ) _ (i, 2 * (S.dimension X : ℤ) - i) y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, mul_add]
    | of ij t =>
      rw [← DirectSum.lof_eq_of F, DirectSum.component.of]
      simp only [Ψ, DirectSum.toModule_lof, LinearMap.smul_apply, smul_eq_mul]
      by_cases hij : ij = (i, 2 * (S.dimension X : ℤ) - i)
      · subst hij
        simp
      · rw [dite_eq_right hij, map_zero, mul_zero]
        have hzero : ∀ t, TensorProduct.lift ((LinearMap.mul F F).compl₁₂
            (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
                (ij.1 + (2 * (S.dimension X : ℤ) - i))).comp
              (((S.H X).mul ij.1 (2 * (S.dimension X : ℤ) - i)).flip a))
            (((S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
                (ij.2 + i)).comp (((S.H X).mul ij.2 i).flip b))) t = 0 := by
          intro t
          induction t using TensorProduct.inductionOn with
          | add t t' ht ht' => rw [map_add, ht, ht', add_zero]
          | tmul x y =>
            simp only [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.comp_apply,
              LinearMap.flip_apply, LinearMap.mul_apply']
            by_cases h1 : ij.1 = i
            · have h2 : ij.2 ≠ 2 * (S.dimension X : ℤ) - i := fun h2 => hij (Prod.ext h1 h2)
              rw [ExternallyGradedAlgebra.traceExtension_of_ne _ _ _ (n := ij.2 + i) (by omega),
                mul_zero]
            · rw [ExternallyGradedAlgebra.traceExtension_of_ne _ _ _
                (n := ij.1 + (2 * (S.dimension X : ℤ) - i))
                (by omega), zero_mul]
        rw [hzero, mul_zero]
  have hleft : Φ (DirectSum.lof F ℤ (fun n => (S.H P).piece n) (2 * (S.dimension X : ℤ))
      (ExternallyGraded.degreeCast (R := F) (X := (S.H P).piece)
        (show 2 * (S.dimension P : ℤ) - 2 * (S.dimension X : ℤ) = 2 * (S.dimension X : ℤ) by
          omega) D)) =
      S.integration X (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
        (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by omega)
        ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i a b)) := by
    simp only [Φ, DirectSum.toModule_lof, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [S.traceExtension_mul_comm P,
      show 2 * (S.dimension X : ℤ) * (2 * (S.dimension X : ℤ)) =
        2 * ((S.dimension X : ℤ) * (2 * (S.dimension X : ℤ))) by ring, gradedSign_two_mul,
      one_mul, ExternallyGradedAlgebra.traceExtension_congr _ _ _ (by omega)
        (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H P) _ _ _ _ c D),
      S.traceExtension_mul_pushforward_one δ c, hc, S.pullback_degreeCast, S.pullback_mul]
    have hδa : ∀ (f : P ⟶ X) (hf : δ ≫ f = 𝟙 X) (n : ℤ) (x : (S.H X).piece n),
        S.pullback δ n (S.pullback f n x) = x := by
      intro f hf n x
      rw [← LinearMap.comp_apply, ← S.pullback_comp, hf, S.pullback_id]
      rfl
    rw [hδa p hδp, hδa q hδq, ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ rfl]
    rfl
  have hswap : ∀ l, (S.H X).traceExtension (S.dimension X) (S.integration X).toLinearMap
      (i + (2 * (S.dimension X : ℤ) - i)) ((S.H X).mul i (2 * (S.dimension X : ℤ) - i) (e l) a) =
      gradedSign F (i * (2 * (S.dimension X : ℤ) - i)) * S.integration X
        (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
          (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by omega)
          ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i a (e l))) := by
    intro l
    rw [S.traceExtension_mul_comm X, ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ (by omega),
      LinearEquiv.coe_coe]
  rw [← hleft, ← (LinearEquiv.ofBijective _ hK).apply_symm_apply
    (DirectSum.lof F ℤ (fun n => (S.H P).piece n) (2 * (S.dimension X : ℤ)) _),
    LinearEquiv.ofBijective_apply,
    hΦK, hΨ, hdecomp, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.flip_apply, LinearMap.mul_apply',
    hswap, ExternallyGradedAlgebra.traceExtension_of_eq _ _ _ (by omega), LinearEquiv.coe_coe]
  have hs := gradedSign_cancel (F := F) i (S.dimension X : ℤ)
  linear_combination (exp := 1) (S.integration X (ExternallyGraded.degreeCast (R := F)
      (X := (S.H X).piece) (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by
        omega) ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i a (e l))) *
    S.integration X (ExternallyGraded.degreeCast (R := F)
      (X := (S.H X).piece) (show 2 * (S.dimension X : ℤ) - i + i = 2 * (S.dimension X : ℤ) by
        omega) ((S.H X).mul (2 * (S.dimension X : ℤ) - i) i (e' l) b))) * hs

end PoincareDualityPushforwardSetup

/-! ### Stacks 0FGZ -/

section Diagonal

open Stacks.Chow

variable {k : Type u} [Field k]

/-- The class of a closed subscheme respects transport of its codimension. -/
theorem closedSubschemeClass_heq {Y Z : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S)
    [Smooth sY] (i : Z ⟶ Y) [IsClosedImmersion i] {c c' : ℤ} (h : c = c') :
    closedSubschemeClass sY i c ≍ closedSubschemeClass sY i c' := by
  subst h
  rfl

/-- A common section `δ : X ⟶ P` of a morphism `p : P ⟶ X` of smooth projective varieties is a
closed immersion, `p` being separated. -/
theorem SmoothProjective.isClosedImmersion_of_section {X P : (SmoothProjective k).FullSubcategory}
    (p : P ⟶ X) (δ : X ⟶ P) (hδp : δ ≫ p = 𝟙 X) : IsClosedImmersion δ.hom.left := by
  have : IsSeparated P.obj.hom := P.property.1.toIsVariety.toIsSeparated
  have : IsSeparated (p.hom.left ≫ X.obj.hom) := by rw [Over.w p.hom]; infer_instance
  have : IsSeparated p.hom.left := IsSeparated.of_comp p.hom.left X.obj.hom
  exact Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section p.hom.left
    δ.hom.left (by rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, hδp]; rfl)

namespace ChowClassicalWeilCohomologyTheory

variable [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, w} k F)

/-- **`γ([Δ]) = δ_*1`.** For `P` a fibre product of `X` with itself and `δ : X ⟶ P` the diagonal,
the cycle class of the class `[Δ] ∈ CH^d(P)` of the closed subscheme `δ(X)` is the pushforward of
the unit, by axiom `(C)(b)` for `δ`, the identity `δ_*[X] = [Δ]` of cycles and `γ([X]) = 1`. -/
theorem cycleClass_diagonal_heq {X P : (SmoothProjective k).FullSubcategory} (p q : P ⟶ X)
    (hpq : IsPullback p.hom.left q.hom.left X.obj.hom X.obj.hom) (δ : X ⟶ P)
    (hδp : δ ≫ p = 𝟙 X) :
    haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
    T.cycleClass P (T.dimension X)
        (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
          (T.dimension X)) ≍
      T.pushforward δ (2 * (T.dimension X : ℤ))
        (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
          (show (0 : ℤ) = 2 * (T.dimension X : ℤ) - 2 * (T.dimension X : ℤ) by ring)
          (T.H X).one) := by
  have := SmoothProjective.isClosedImmersion_of_section p δ hδp
  have : IsClosedImmersion ((SmoothProjective.toSchemeCat k).map δ).hom.left :=
    inferInstanceAs (IsClosedImmersion δ.hom.left)
  have hdim := T.dimension_eq_add p q hpq
  have hpush := T.cycleClass_pushforward δ 0 ((chowCycleData k).fundamental X)
  rw [chowCycleData_pushforward, chowCycleData_fundamental,
    equidimensionalPushforward_fundamentalClass ((SmoothProjective.toSchemeCat k).map δ)
      (SmoothProjective.isNonemptyEquidimensional X (T.dimension_eq X))
      (SmoothProjective.isNonemptyEquidimensional P (T.dimension_eq P)) _ rfl] at hpush
  refine (T.cycleClass_heq P (show (T.dimension X : ℤ) =
      0 + (T.dimension P : ℤ) - (T.dimension X : ℤ) by omega)
    (closedSubschemeClass_heq _ _ (by omega))).trans ?_
  refine (ExternallyGraded.degreeCast_heq (R := F) (X := (T.H P).piece)
    (show 2 * (0 + (T.dimension P : ℤ) - (T.dimension X : ℤ)) =
      2 * (T.dimension P : ℤ) - (2 * (T.dimension X : ℤ) - 2 * 0) by ring) _).symm.trans ?_
  refine (heq_of_eq hpush.symm).trans ?_
  refine T.toPoincareDualityPushforwardSetup.pushforward_heq δ (by ring) ?_
  refine (ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_
  refine (T.cycleClass_fundamental X).trans ?_
  exact (ExternallyGraded.degreeCast_heq (R := F) _ _).symm

/-- **Stacks Project, Tag 0FGZ.** Let `H^*` be a classical Weil cohomology theory and `X` a smooth
projective variety of dimension `d`. Choose a basis `e_{i, j}` of `H^i(X)` over `F` and, using
Künneth, write `γ([Δ]) = ∑_i ∑_j e_{i, j} ⊗ e'_{2d - i, j}` in `⨁_i H^i(X) ⊗_F H^{2d - i}(X)`
with `e'_{2d - i, j} ∈ H^{2d - i}(X)`. Then `∫_X e_{i, j} ∪ e'_{2d - i, j'} = (-1)^i δ_{jj'}`.

The product `X × X` is a smooth projective variety `P` with projections `p, q : P ⟶ X`
exhibiting it as the fibre product over `k`, and the diagonal is `δ : X ⟶ P` with
`δ ≫ p = δ ≫ q = 𝟙`; `[Δ] ∈ CH^d(P)` is the class of the closed subscheme `δ(X)`, and the
decomposition of `γ([Δ])` is read through the inverse of the Künneth isomorphism of axiom `(B)`.
The hypothesis `hdecomp` is the `(i, 2d - i)` component of the source's decomposition, for the one
degree `i` the conclusion concerns; `(-1)^i` is `gradedSign F i`. -/
@[stacks 0FGZ]
theorem integration_mul_diagonalKunnethCoordinate {X P : (SmoothProjective k).FullSubcategory}
    (p q : P ⟶ X) (hpq : IsPullback p.hom.left q.hom.left X.obj.hom X.obj.hom) (δ : X ⟶ P)
    (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X) (i : ℤ) {J : Type t} [Fintype J] [DecidableEq J]
    (e : Module.Basis J F ((T.H X).piece i))
    (e' : J → (T.H X).piece (2 * (T.dimension X : ℤ) - i))
    (hdecomp :
      haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
      DirectSum.component F (ℤ × ℤ) (fun ij => (T.H X).piece ij.1 ⊗[F] (T.H X).piece ij.2)
          (i, 2 * (T.dimension X : ℤ) - i)
          (TensorProduct.directSum F F (fun n : ℤ => (T.H X).piece n)
            (fun n : ℤ => (T.H X).piece n)
            ((T.kunnethEquiv X X P p q hpq).symm
              (DirectSum.lof F ℤ (fun n => (T.H P).piece n) (2 * (T.dimension X : ℤ))
                (T.cycleClass P (T.dimension X)
                  (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left
          (T.dimension X)))))) =
        ∑ j : J, e j ⊗ₜ[F] e' j)
    (j j' : J) :
    T.integration X (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
        (show i + (2 * (T.dimension X : ℤ) - i) = 2 * (T.dimension X : ℤ) by omega)
        ((T.H X).mul i (2 * (T.dimension X : ℤ) - i) (e j) (e' j'))) =
      gradedSign F i * (if j = j' then 1 else 0) := by
  have hdim := T.dimension_eq_add p q hpq
  refine T.toPoincareDualityPushforwardSetup.integration_mul_kunnethCoordinate_pushforward_one
    p q hdim (fun u v => T.integration_mul_pullback hpq u v) (T.kunneth X X P p q hpq) δ hδp hδq
    i e e' ?_ j j'
  rw [← hdecomp]
  congr 4
  exact (eq_of_heq ((T.cycleClass_diagonal_heq p q hpq δ hδp).trans
    (ExternallyGraded.degreeCast_heq (R := F) _ _).symm)).symm

end ChowClassicalWeilCohomologyTheory

end Diagonal

end Stacks.WeilCohomology

end
