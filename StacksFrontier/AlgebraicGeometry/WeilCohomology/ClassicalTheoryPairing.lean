module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory

/-!
# Classical Weil cohomology data without (A)(c) and (A)(d)

Stacks 0FH1 produces, from a realization of Chow motives, data (D1), (D2), (D3) satisfying all of
the axioms (A), (B), (C) of a classical Weil cohomology theory (Stacks 0FGV) *except possibly
(A)(c) and (A)(d)*: the cohomology need not vanish outside the degrees `[0, 2d]`, and the trace
map `∫_X : H^{2d}(X) → F` need not be an isomorphism. This file packages exactly those data and
axioms, as the weakening of `Stacks.WeilCohomology.PoincareDualityPushforwardSetup` and of
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` in which these two clauses are dropped, and
relates the two families: a classical Weil cohomology theory forgets to one, and one satisfying
(A)(c) and (A)(d) is a classical Weil cohomology theory.

## Main definitions

* `Stacks.WeilCohomology.PoincarePairingSetup`: the data (D1), (D3) with axioms (A)(a), (A)(b):
  finite dimensional cohomology with perfect cup-product trace pairings in complementary degrees.
* `Stacks.WeilCohomology.PoincarePairingSetup.pushforward`: the pushforward these determine, the
  contragredient of pullback.
* `Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory`: data (D1), (D2), (D3) satisfying all
  of (A), (B), (C) except possibly (A)(c) and (A)(d).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toPre`: a classical Weil cohomology theory
  satisfies all of these.
* `Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory.toClassical`: conversely, granted
  (A)(c) and (A)(d), they form a classical Weil cohomology theory.

## References

* [Stacks Project, Tag 0FGV](https://stacks.math.columbia.edu/tag/0FGV)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w t

namespace Stacks.WeilCohomology

/-- The data `(D1)` and `(D3)` of a classical Weil cohomology theory together with axioms
`(A)(a)` and `(A)(b)`: a contravariant multiplicative graded-commutative cohomology theory on the
smooth projective varieties over `k` with finite dimensional cohomology groups, and linear trace
maps `∫_X : H^{2d}(X) → F` for which the cup-product trace pairings in complementary degrees are
perfect. Neither the vanishing of `H^i(X)` outside `[0, 2d]` nor the bijectivity of `∫_X` is
required. -/
structure PoincarePairingSetup (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F] where
  /-- The graded cohomology algebra of a smooth projective variety. -/
  H : (SmoothProjective k).FullSubcategory → ExternallyGradedAlgebra.{v, w} F
  /-- Cup product is graded commutative. -/
  gradedComm : ∀ X, (H X).IsGradedCommutative
  /-- The dimension of a smooth projective variety. -/
  dimension : (SmoothProjective k).FullSubcategory → ℕ
  /-- The chosen dimension is the topological dimension of the underlying space. -/
  dimension_eq : ∀ X, topologicalKrullDim X.obj.left = (dimension X : WithBot ℕ∞)
  /-- Cohomological pullback along a morphism of smooth projective varieties. -/
  pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory},
    (X ⟶ Y) → ∀ i : ℤ, (H Y).piece i →ₗ[F] (H X).piece i
  /-- Pullback along an identity is the identity. -/
  pullback_id : ∀ (X) (i : ℤ), pullback (𝟙 X) i = LinearMap.id
  /-- Pullback is contravariantly functorial. -/
  pullback_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ),
    pullback (f ≫ g) i = (pullback f i).comp (pullback g i)
  /-- Pullback preserves the unit class. -/
  pullback_one : ∀ {X Y} (f : X ⟶ Y), pullback f 0 (H Y).one = (H X).one
  /-- Pullback is multiplicative for the cup product. -/
  pullback_mul : ∀ {X Y} (f : X ⟶ Y) (i j : ℤ) (a : (H Y).piece i) (b : (H Y).piece j),
    pullback f (i + j) ((H Y).mul i j a b) =
      (H X).mul i j (pullback f i a) (pullback f j b)
  /-- The trace map `∫_X : H^{2d}(X) ⟶ F`. -/
  integration : ∀ X, (H X).piece (2 * (dimension X : ℤ)) →ₗ[F] F
  /-- Axiom `(A)(a)`: every cohomology group is finite dimensional. -/
  finite : ∀ X i, FiniteDimensional F ((H X).piece i)
  /-- Axiom `(A)(b)`: the cup-product trace pairing in complementary degrees is perfect. -/
  perfect : ∀ X i, ((H X).tracePairing (dimension X) (integration X) i).IsPerfPair

namespace PoincarePairingSetup

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincarePairingSetup.{u, v, w} k F) {X Y : (SmoothProjective k).FullSubcategory}

/-- The pushforward `f_* : H^{2d - i}(X) ⟶ H^{2e - i}(Y)` determined by the perfect pairings: the
contragredient of `f^* : H^i(Y) ⟶ H^i(X)` with respect to the cup-product trace pairings. -/
noncomputable def pushforward (f : X ⟶ Y) (i : ℤ) :
    (S.H X).piece (2 * (S.dimension X : ℤ) - i) →ₗ[F]
      (S.H Y).piece (2 * (S.dimension Y : ℤ) - i) :=
  haveI := S.perfect Y i
  Stacks.WeilCohomology.poincareDualPushforward
    ((S.H X).tracePairing (S.dimension X) (S.integration X) i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y) i)
    (S.pullback f i)

/-- The trace equation `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a` defining the pushforward. -/
theorem integration_pullback_mul (f : X ⟶ Y) (i : ℤ) (b : (S.H Y).piece i)
    (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)) :
    (S.H X).tracePairing (S.dimension X) (S.integration X) i (S.pullback f i b) a =
      (S.H Y).tracePairing (S.dimension Y) (S.integration Y) i b (S.pushforward f i a) :=
  have := S.perfect Y i
  Stacks.WeilCohomology.poincareDualPushforward_pairing
    ((S.H X).tracePairing (S.dimension X) (S.integration X) i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y) i)
    (S.pullback f i) b a

/-- A linear map is the pushforward exactly when it satisfies the trace equation against every
class of complementary degree. -/
theorem eq_pushforward_iff (f : X ⟶ Y) (i : ℤ)
    (g : (S.H X).piece (2 * (S.dimension X : ℤ) - i) →ₗ[F]
      (S.H Y).piece (2 * (S.dimension Y : ℤ) - i)) :
    g = S.pushforward f i ↔
      ∀ (b : (S.H Y).piece i) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)),
        (S.H X).tracePairing (S.dimension X) (S.integration X) i (S.pullback f i b) a =
          (S.H Y).tracePairing (S.dimension Y) (S.integration Y) i b (g a) :=
  have := S.perfect Y i
  Stacks.WeilCohomology.eq_poincareDualPushforward_iff
    ((S.H X).tracePairing (S.dimension X) (S.integration X) i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y) i)
    (S.pullback f i) g

end PoincarePairingSetup

/-- **Data `(D1)`, `(D2)`, `(D3)` satisfying all of `(A)`, `(B)`, `(C)` except possibly `(A)(c)`
and `(A)(d)`**, for a given theory of Chow groups: the conclusion of Stacks 0FH1. The fields are
those of `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`, over a
`Stacks.WeilCohomology.PoincarePairingSetup` in place of a
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`. -/
structure PreClassicalWeilCohomologyTheory (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F] (Ch : ChowCycleData.{u, t} k)
    extends PoincarePairingSetup.{u, v, w} k F where
  /-- The cycle class map `γ : CHʳ(X) → H^{2r}(X)`, a homomorphism of abelian groups. -/
  cycleClass : ∀ (X : (SmoothProjective k).FullSubcategory) (r : ℤ),
    Ch.group X r →+ (H X).piece (2 * r)
  /-- The Künneth formula: for `P` a fibre product of `X` and `Y` over `k`, the map
  `H^*(X) ⊗_F H^*(Y) → H^*(P)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, is an isomorphism. -/
  kunneth : ∀ (X Y P : (SmoothProjective k).FullSubcategory) (p : P ⟶ X) (q : P ⟶ Y),
    IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom →
      Function.Bijective
        (kunnethMap (H X) (H Y) (H P) (fun i => pullback p i) fun j => pullback q j)
  /-- Compatibility with the Gysin pullback: `γ(f^!β) = f^*γ(β)`. -/
  cycleClass_gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
    (β : Ch.group Y r),
    cycleClass X r (Ch.gysin f r β) = pullback f (2 * r) (cycleClass Y r β)
  /-- Compatibility with the proper pushforward: `γ(f_*α) = f_*γ(α)`, for the pushforward on
  cohomology determined by the perfect pairings. -/
  cycleClass_pushforward : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
    (α : Ch.group X r),
    toPoincarePairingSetup.pushforward f (2 * (dimension X : ℤ) - 2 * r)
        (ExternallyGraded.degreeCast (R := F) (X := (H X).piece)
          (show 2 * r = 2 * (dimension X : ℤ) - (2 * (dimension X : ℤ) - 2 * r) by ring)
          (cycleClass X r α)) =
      ExternallyGraded.degreeCast (R := F) (X := (H Y).piece)
        (show 2 * (r + (dimension Y : ℤ) - (dimension X : ℤ)) =
            2 * (dimension Y : ℤ) - (2 * (dimension X : ℤ) - 2 * r) by ring)
        (cycleClass Y (r + (dimension Y : ℤ) - (dimension X : ℤ))
          (Ch.pushforward f (dimension X) (dimension Y)
            (dimension_eq X) (dimension_eq Y) r α))
  /-- Compatibility with the intersection product: `γ(α · β) = γ(α) ∪ γ(β)`. -/
  cycleClass_mul : ∀ (X : (SmoothProjective k).FullSubcategory) (r s : ℤ)
    (α : Ch.group X r) (β : Ch.group X s),
    cycleClass X (r + s) (Ch.mul r s α β) =
      (H X).evenCup r s (cycleClass X r α) (cycleClass X s β)
  /-- Normalisation at a point: `∫_{Spec k} γ([Spec k]) = 1`. -/
  integration_cycleClass_fundamental : ∀ (X : (SmoothProjective k).FullSubcategory),
    IsIso X.obj.hom → ∀ h0 : dimension X = 0,
    integration X (ExternallyGraded.degreeCast (R := F) (X := (H X).piece)
      (show 2 * (0 : ℤ) = 2 * (dimension X : ℤ) by omega)
      (cycleClass X 0 (Ch.fundamental X))) = 1

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  {Ch : ChowCycleData.{u, t} k}

/-- A Poincaré duality setup satisfies `(A)(a)` and `(A)(b)`. -/
@[simps]
def PoincareDualityPushforwardSetup.toPoincarePairingSetup
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F) : PoincarePairingSetup.{u, v, w} k F where
  H := S.H
  gradedComm := S.gradedComm
  dimension := S.dimension
  dimension_eq := S.dimension_eq
  pullback := S.pullback
  pullback_id := S.pullback_id
  pullback_comp := S.pullback_comp
  pullback_one := S.pullback_one
  pullback_mul := S.pullback_mul
  integration X := (S.integration X).toLinearMap
  finite := S.finite
  perfect := S.perfect

/-- The pushforward of a Poincaré duality setup is the pushforward of its underlying pairing
setup. -/
theorem PoincareDualityPushforwardSetup.toPoincarePairingSetup_pushforward
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
    {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i : ℤ) :
    S.toPoincarePairingSetup.pushforward f i = S.pushforward f i :=
  rfl

/-- A classical Weil cohomology theory satisfies all of `(A)`, `(B)`, `(C)` except possibly
`(A)(c)` and `(A)(d)`. -/
def ClassicalWeilCohomologyTheory.toPre (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) :
    PreClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch where
  __ := T.toPoincarePairingSetup
  cycleClass := T.cycleClass
  kunneth := T.kunneth
  cycleClass_gysin := T.cycleClass_gysin
  cycleClass_pushforward := T.cycleClass_pushforward
  cycleClass_mul := T.cycleClass_mul
  integration_cycleClass_fundamental := T.integration_cycleClass_fundamental

/-- Data `(D1)`, `(D2)`, `(D3)` satisfying all of `(A)`, `(B)`, `(C)` except possibly `(A)(c)`
and `(A)(d)` form a classical Weil cohomology theory once `(A)(c)`, the vanishing of `H^i(X)`
outside `[0, 2d]`, and `(A)(d)`, the bijectivity of `∫_X`, hold. -/
noncomputable def PreClassicalWeilCohomologyTheory.toClassical
    (T : PreClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)
    (bounded : ∀ X i, (i < 0 ∨ 2 * (T.dimension X : ℤ) < i) → ∀ a : (T.H X).piece i, a = 0)
    (bijective : ∀ X, Function.Bijective (T.integration X)) :
    ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch where
  H := T.H
  gradedComm := T.gradedComm
  dimension := T.dimension
  dimension_eq := T.dimension_eq
  pullback := T.pullback
  pullback_id := T.pullback_id
  pullback_comp := T.pullback_comp
  pullback_one := T.pullback_one
  pullback_mul := T.pullback_mul
  integration X := LinearEquiv.ofBijective (T.integration X) (bijective X)
  finite := T.finite
  perfect := T.perfect
  bounded := bounded
  cycleClass := T.cycleClass
  kunneth := T.kunneth
  cycleClass_gysin := T.cycleClass_gysin
  cycleClass_pushforward := T.cycleClass_pushforward
  cycleClass_mul := T.cycleClass_mul
  integration_cycleClass_fundamental := T.integration_cycleClass_fundamental

/-- Adding `(A)(c)` and `(A)(d)` and then forgetting them returns the same data. -/
theorem PreClassicalWeilCohomologyTheory.toPre_toClassical
    (T : PreClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) (bounded bijective) :
    (T.toClassical bounded bijective).toPre = T :=
  rfl

end Stacks.WeilCohomology

end
