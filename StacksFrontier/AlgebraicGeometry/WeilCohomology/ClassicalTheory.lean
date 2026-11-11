module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Kunneth

/-!
# Classical Weil cohomology theories

Fix an algebraically closed field `k` and a coefficient field `F` of characteristic zero. A
*classical Weil cohomology theory* consists of three pieces of data: a contravariant functor
`H^*` from smooth projective varieties over `k` to graded commutative `F`-algebras, a cycle class
map `γ : CHʳ(X) → H^{2r}(X)` for each smooth projective `X`, and a trace map
`∫_X : H^{2d}(X) → F` for each smooth projective `X` of dimension `d`. These are subject to three
axioms: Poincaré duality, the Künneth formula, and compatibility of the cycle class maps with
Gysin pullback, proper pushforward, the intersection product and the class of a point.

The functor, the trace maps and the whole of Poincaré duality are
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`; this file adds the cycle class maps and
the two remaining axioms to it, and records the pushforward compatibility against the
pushforward that Poincaré duality already furnishes.

## Main definitions

* `ExternallyGradedAlgebra.evenCup`: the cup product of even-degree classes, graded by
  codimension, `H^{2r} × H^{2s} → H^{2(r + s)}`.
* `Stacks.WeilCohomology.kunnethMap`: the map `H^*(X) ⊗_F H^*(Y) → H^*(P)`,
  `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`.
* `Stacks.WeilCohomology.ChowCycleData`: Chow groups graded by codimension, with the
  intersection product, the Gysin pullback, the proper pushforward and the fundamental class.
* `Stacks.WeilCohomology.ChowCycleData.externalProduct`: the exterior product of cycle classes,
  `α × β = pr₁^!α · pr₂^!β`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`: a classical Weil cohomology theory.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.kunnethEquiv`: the Künneth isomorphism
  `H^*(X) ⊗_F H^*(Y) ≃ H^*(X ×_k Y)` supplied by the Künneth axiom.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullback_evenCup`: pullback is
  multiplicative for the codimension-graded cup product.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClass_externalProduct`: the cycle
  class map of a classical Weil cohomology theory is compatible with exterior products,
  `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`.
* `Stacks.WeilCohomology.cycleClass_mul_iff_cycleClass_externalProduct'`: conversely, granted
  compatibility with the Gysin pullback and the diagonal description `α · β = Δ^!(α × β)` of the
  intersection product, compatibility with the intersection product is *equivalent* to
  compatibility with exterior products, so the former may be checked in the latter form.
* `Stacks.WeilCohomology.cycleClass_mul_of_cycleClass_externalProduct`: the implication of that
  equivalence that produces compatibility with the intersection product.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.integration_pullback_mul_cycleClass`: the
  trace form `∫_X f^*b ∪ γ(α) = ∫_Y b ∪ γ(f_*α)` of compatibility with proper pushforward.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClass_fundamental_ne_zero`: the class
  of a point is nonzero, so the cycle class map is not the zero map.

## Implementation notes

Cohomology is an externally graded algebra, so a class of codimension `r` lives in the piece of
degree `2 * r` and equalities of degrees written two ways are mediated by
`ExternallyGraded.degreeCast`; `evenCup` packages the one such transport that the cycle class
axioms need, namely `2 * r + 2 * s = 2 * (r + s)`.

Chow groups are carried as data rather than constructed: a family of abelian groups indexed by a
smooth projective variety and a codimension, equipped with the four operations the axioms
mention and with no laws of their own, since the axioms relate those operations to cohomology
without using any identity among them. Only the cycle class map is required to be additive,
because that is the only additivity the source asserts. The proper pushforward raises
codimension by the relative dimension, so it takes the two dimensions as arguments together with
the proofs identifying them with the topological dimensions of the two varieties; the
cohomological axiom instantiates these at the dimensions recorded by the Poincaré duality setup.
The exterior product is not a further operation: it is defined by `α × β = pr₁^!α · pr₂^!β`, one
of the two identities that the source's discussion of the intersection product uses.

The Künneth axiom is stated for an arbitrary product diagram, a smooth projective variety `P`
with two morphisms to `X` and `Y` exhibiting it as the fibre product of the two structure
morphisms; this says what the source says while requiring no construction of products inside the
subcategory. Compatibility with proper pushforward is stated against
`PoincareDualityPushforwardSetup.pushforward`, the pushforward the duality axiom already
determines, so no second pushforward on cohomology is introduced. Compatibility with the class
of a point is stated for every variety isomorphic to `Spec k` over `k` whose recorded dimension
is zero: those are exactly the models of `Spec k`, and the vanishing of their dimension is a
hypothesis rather than a consequence because it is not available here.

## References

* [Stacks Project, Section 45.7 (Tag 0FGS)](https://stacks.math.columbia.edu/tag/0FGS)
* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped DirectSum TensorProduct

universe u v w t

/-- The cup product of even-degree classes of an externally graded algebra, graded by
codimension: `A^{2r} × A^{2s} → A^{2(r + s)}`. -/
def ExternallyGradedAlgebra.evenCup {F : Type v} [Field F] (A : ExternallyGradedAlgebra.{v, w} F)
    (r s : ℤ) : A.piece (2 * r) →ₗ[F] A.piece (2 * s) →ₗ[F] A.piece (2 * (r + s)) :=
  (A.mul (2 * r) (2 * s)).compr₂
    (ExternallyGraded.degreeCast (R := F) (X := A.piece) (by ring))

namespace Stacks.WeilCohomology

/-- The Künneth map `H^*(X) ⊗_F H^*(Y) → H^*(P)`, `a ⊗ b ↦ p^*a ∪ q^*b`, assembled from two
maps `p`, `q` of graded algebras into a third one. -/
noncomputable def kunnethMap {F : Type v} [Field F]
    (A B D : ExternallyGradedAlgebra.{v, w} F)
    (p : ∀ i : ℤ, A.piece i →ₗ[F] D.piece i) (q : ∀ j : ℤ, B.piece j →ₗ[F] D.piece j) :
    ((⨁ i : ℤ, A.piece i) ⊗[F] ⨁ j : ℤ, B.piece j) →ₗ[F] ⨁ n : ℤ, D.piece n :=
  (DirectSum.toModule F (ℤ × ℤ) _ fun ij =>
      (DirectSum.lof F ℤ (fun n => D.piece n) (ij.1 + ij.2)).comp
        (TensorProduct.lift (((D.mul ij.1 ij.2).comp (p ij.1)).compl₂ (q ij.2)))).comp
    (TensorProduct.directSum F F (fun i : ℤ => A.piece i) (fun j : ℤ => B.piece j)).toLinearMap

/-- Chow groups of smooth projective varieties over `k`, graded by codimension, together with the
intersection product, the Gysin pullback, the proper pushforward and the fundamental class. The
pushforward along a morphism of varieties of dimensions `d` and `e` raises codimension by
`e - d`, so it takes those dimensions, certified as the topological dimensions of the two
varieties, as arguments. -/
structure ChowCycleData (k : Type u) [Field k] where
  /-- The Chow group `CHʳ(X)` of codimension-`r` cycle classes. -/
  group : (SmoothProjective k).FullSubcategory → ℤ → Type t
  /-- Each Chow group is an abelian group. -/
  [addCommGroup : ∀ X r, AddCommGroup (group X r)]
  /-- The intersection product `CHʳ(X) × CHˢ(X) → CHʳ⁺ˢ(X)`. -/
  mul : ∀ {X : (SmoothProjective k).FullSubcategory} (r s : ℤ),
    group X r → group X s → group X (r + s)
  /-- The Gysin pullback `f^! : CHʳ(Y) → CHʳ(X)`. -/
  gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory}, (X ⟶ Y) → ∀ r : ℤ,
    group Y r → group X r
  /-- The proper pushforward `f_* : CHʳ(X) → CHʳ⁺ᵉ⁻ᵈ(Y)`. -/
  pushforward : ∀ {X Y : (SmoothProjective k).FullSubcategory}, (X ⟶ Y) → ∀ d e : ℕ,
    topologicalKrullDim X.obj.left = (d : WithBot ℕ∞) →
    topologicalKrullDim Y.obj.left = (e : WithBot ℕ∞) →
    ∀ r : ℤ, group X r → group Y (r + (e : ℤ) - (d : ℤ))
  /-- The fundamental class `[X] ∈ CH⁰(X)`. -/
  fundamental : ∀ X : (SmoothProjective k).FullSubcategory, group X 0

attribute [instance] ChowCycleData.addCommGroup

/-- The exterior product of cycle classes, `α × β = pr₁^!α · pr₂^!β`. -/
noncomputable def ChowCycleData.externalProduct {k : Type u} [Field k]
    [HasBinaryProducts ((SmoothProjective k).FullSubcategory)] (Ch : ChowCycleData.{u, t} k)
    {X Y : (SmoothProjective k).FullSubcategory} (r s : ℤ)
    (α : Ch.group X r) (β : Ch.group Y s) : Ch.group (X ⨯ Y) (r + s) :=
  Ch.mul r s (Ch.gysin (prod.fst : X ⨯ Y ⟶ X) r α) (Ch.gysin (prod.snd : X ⨯ Y ⟶ Y) s β)

/-- A classical Weil cohomology theory over an algebraically closed field `k` with coefficients
in a field `F` of characteristic zero, for a given theory of Chow groups: the contravariant
multiplicative graded-commutative cohomology theory and the trace maps satisfying Poincaré
duality, together with the cycle class maps, the Künneth formula, and compatibility of the cycle
class maps with Gysin pullback, proper pushforward, the intersection product and the class of a
point. -/
@[stacks 0FGV]
structure ClassicalWeilCohomologyTheory (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F] (Ch : ChowCycleData.{u, t} k)
    extends PoincareDualityPushforwardSetup.{u, v, w} k F where
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
  cohomology determined by Poincaré duality. -/
  cycleClass_pushforward : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
    (α : Ch.group X r),
    toPoincareDualityPushforwardSetup.pushforward f (2 * (dimension X : ℤ) - 2 * r)
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
  {X Y : (SmoothProjective k).FullSubcategory}

/-- Pullback commutes with transport between graded pieces of equal degree. -/
theorem PoincareDualityPushforwardSetup.pullback_degreeCast
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F) (f : X ⟶ Y) {i j : ℤ} (h : i = j)
    (a : (S.H Y).piece i) :
    S.pullback f j (ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece) h a) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece) h (S.pullback f i a) := by
  cases h
  rfl

/-- Pullback is multiplicative for the cup product of even-degree classes. -/
theorem PoincareDualityPushforwardSetup.pullback_evenCup
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F) (f : X ⟶ Y) (r s : ℤ)
    (a : (S.H Y).piece (2 * r)) (b : (S.H Y).piece (2 * s)) :
    S.pullback f (2 * (r + s)) ((S.H Y).evenCup r s a b) =
      (S.H X).evenCup r s (S.pullback f (2 * r) a) (S.pullback f (2 * s) b) := by
  simp only [ExternallyGradedAlgebra.evenCup, LinearMap.compr₂_apply]
  rw [S.pullback_degreeCast, S.pullback_mul]

/-- For a cycle class map `γ` from a `ChowCycleData` compatible with the Gysin pullback,
`γ(f^!β) = f^*γ(β)`, and a product satisfying `α · β = Δ^!(α × β)`, compatibility with the
product, `γ(α · β) = γ(α) ∪ γ(β)`, is equivalent to `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`.

The exterior product here is `ChowCycleData.externalProduct`, which is defined as
`pr₁^!α · pr₂^!β`, so this is a formal equivalence over abstract cycle data and says nothing about
the exterior product of cycles. The statements of Remark 0FGU for the actual Chow groups are
`Stacks.Chow.codimensionIntersectionProduct_eq_codimensionGysin_diag`,
`Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct`,
`Stacks.WeilCohomology.cycleClass_mul_iff_cycleClass_codimensionExteriorProduct` (for the data
of a classical Weil cohomology theory) and
`Stacks.WeilCohomology.WeilData.cycleClassMul_iff_cycleClass_codimensionExteriorProduct` (for
the data of Section 45.9). -/
theorem cycleClass_mul_iff_cycleClass_externalProduct'
    [HasBinaryProducts ((SmoothProjective k).FullSubcategory)]
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F) (Ch : ChowCycleData.{u, t} k)
    (cycleClass : ∀ (X : (SmoothProjective k).FullSubcategory) (r : ℤ),
      Ch.group X r →+ (S.H X).piece (2 * r))
    (cycleClass_gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
      (β : Ch.group Y r),
      cycleClass X r (Ch.gysin f r β) = S.pullback f (2 * r) (cycleClass Y r β))
    (mul_eq : ∀ {Z : (SmoothProjective k).FullSubcategory} (r s : ℤ)
      (α : Ch.group Z r) (β : Ch.group Z s), Ch.mul r s α β =
        Ch.gysin (prod.lift (𝟙 Z) (𝟙 Z) : Z ⟶ Z ⨯ Z) (r + s) (Ch.externalProduct r s α β)) :
    (∀ (Z : (SmoothProjective k).FullSubcategory) (r s : ℤ)
        (α : Ch.group Z r) (β : Ch.group Z s),
        cycleClass Z (r + s) (Ch.mul r s α β) =
          (S.H Z).evenCup r s (cycleClass Z r α) (cycleClass Z s β)) ↔
      ∀ (Z W : (SmoothProjective k).FullSubcategory) (r s : ℤ)
        (α : Ch.group Z r) (β : Ch.group W s),
        cycleClass (Z ⨯ W) (r + s) (Ch.externalProduct r s α β) =
          (S.H (Z ⨯ W)).evenCup r s
            (S.pullback (prod.fst : Z ⨯ W ⟶ Z) (2 * r) (cycleClass Z r α))
            (S.pullback (prod.snd : Z ⨯ W ⟶ W) (2 * s) (cycleClass W s β)) := by
  have hid : ∀ (V : (SmoothProjective k).FullSubcategory) (r : ℤ)
      (a : (S.H V).piece (2 * r)), S.pullback (𝟙 V) (2 * r) a = a := by
    intro V r a
    rw [S.pullback_id]
    rfl
  have hcomp : ∀ {U V W : (SmoothProjective k).FullSubcategory} (f : U ⟶ V) (g : V ⟶ W) (r : ℤ)
      (a : (S.H W).piece (2 * r)),
      S.pullback (f ≫ g) (2 * r) a = S.pullback f (2 * r) (S.pullback g (2 * r) a) := by
    intro U V W f g r a
    rw [S.pullback_comp]
    rfl
  exact cycleClass_mul_iff_cycleClass_externalProduct k
    (fun V r => (S.H V).piece (2 * r))
    (fun {V} r s a b => (S.H V).evenCup r s a b)
    (fun {U V} f r a => S.pullback f (2 * r) a) hid hcomp
    (fun {U V} f r s a b => S.pullback_evenCup f r s a b)
    Ch.group (fun {V} r s => Ch.mul r s) (fun {U V} f r => Ch.gysin f r)
    (fun {U V} r s => Ch.externalProduct r s) (fun V r => cycleClass V r)
    (fun {U V} f r β => cycleClass_gysin f r β) (fun {U V} r s α β => rfl)
    (fun {V} r s α β => mul_eq r s α β)

/-- Compatibility of a cycle class map with the intersection product can be checked on exterior
products instead: granted compatibility with the Gysin pullback and the diagonal description
`α · β = Δ^!(α × β)` of the intersection product, `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` implies
`γ(α · β) = γ(α) ∪ γ(β)`. -/
theorem cycleClass_mul_of_cycleClass_externalProduct
    [HasBinaryProducts ((SmoothProjective k).FullSubcategory)]
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F) (Ch : ChowCycleData.{u, t} k)
    (cycleClass : ∀ (X : (SmoothProjective k).FullSubcategory) (r : ℤ),
      Ch.group X r →+ (S.H X).piece (2 * r))
    (cycleClass_gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
      (β : Ch.group Y r),
      cycleClass X r (Ch.gysin f r β) = S.pullback f (2 * r) (cycleClass Y r β))
    (mul_eq : ∀ {Z : (SmoothProjective k).FullSubcategory} (r s : ℤ)
      (α : Ch.group Z r) (β : Ch.group Z s), Ch.mul r s α β =
        Ch.gysin (prod.lift (𝟙 Z) (𝟙 Z) : Z ⟶ Z ⨯ Z) (r + s) (Ch.externalProduct r s α β))
    (hext : ∀ (Z W : (SmoothProjective k).FullSubcategory) (r s : ℤ)
      (α : Ch.group Z r) (β : Ch.group W s),
      cycleClass (Z ⨯ W) (r + s) (Ch.externalProduct r s α β) =
        (S.H (Z ⨯ W)).evenCup r s
          (S.pullback (prod.fst : Z ⨯ W ⟶ Z) (2 * r) (cycleClass Z r α))
          (S.pullback (prod.snd : Z ⨯ W ⟶ W) (2 * s) (cycleClass W s β)))
    (Z : (SmoothProjective k).FullSubcategory) (r s : ℤ)
    (α : Ch.group Z r) (β : Ch.group Z s) :
    cycleClass Z (r + s) (Ch.mul r s α β) =
      (S.H Z).evenCup r s (cycleClass Z r α) (cycleClass Z s β) :=
  (cycleClass_mul_iff_cycleClass_externalProduct' S Ch cycleClass
    (fun {_ _} f r β => cycleClass_gysin f r β) (fun {_} r s α β => mul_eq r s α β)).2
    hext Z r s α β

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k} (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)

/-- The Künneth axiom as an isomorphism: for `P` a fibre product of `X` and `Y` over `k`, the
Künneth map is a linear equivalence `H^*(X) ⊗_F H^*(Y) ≃ H^*(P)`. -/
noncomputable def kunnethEquiv (X Y P : (SmoothProjective k).FullSubcategory)
    (p : P ⟶ X) (q : P ⟶ Y)
    (h : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    ((⨁ i : ℤ, (T.H X).piece i) ⊗[F] ⨁ j : ℤ, (T.H Y).piece j) ≃ₗ[F]
      ⨁ n : ℤ, (T.H P).piece n :=
  LinearEquiv.ofBijective _ (T.kunneth X Y P p q h)

/-- The trace form of compatibility with proper pushforward:
`∫_X f^*b ∪ γ(α) = ∫_Y b ∪ γ(f_*α)`. -/
theorem integration_pullback_mul_cycleClass (f : X ⟶ Y) (r : ℤ) (α : Ch.group X r)
    (b : (T.H Y).piece (2 * (T.dimension X : ℤ) - 2 * r)) :
    (T.H X).tracePairing (T.dimension X) (T.integration X).toLinearMap
        (2 * (T.dimension X : ℤ) - 2 * r)
        (T.pullback f (2 * (T.dimension X : ℤ) - 2 * r) b)
        (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
          (show 2 * r = 2 * (T.dimension X : ℤ) - (2 * (T.dimension X : ℤ) - 2 * r) by ring)
          (T.cycleClass X r α)) =
      (T.H Y).tracePairing (T.dimension Y) (T.integration Y).toLinearMap
        (2 * (T.dimension X : ℤ) - 2 * r) b
        (ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
          (show 2 * (r + (T.dimension Y : ℤ) - (T.dimension X : ℤ)) =
              2 * (T.dimension Y : ℤ) - (2 * (T.dimension X : ℤ) - 2 * r) by ring)
          (T.cycleClass Y (r + (T.dimension Y : ℤ) - (T.dimension X : ℤ))
            (Ch.pushforward f (T.dimension X) (T.dimension Y)
              (T.dimension_eq X) (T.dimension_eq Y) r α))) := by
  rw [← T.cycleClass_pushforward f r α]
  exact T.integration_pullback_mul f (2 * (T.dimension X : ℤ) - 2 * r) b _

/-- The class of a point is nonzero: in particular the cycle class map of a classical Weil
cohomology theory is not the zero map. -/
theorem cycleClass_fundamental_ne_zero (Z : (SmoothProjective k).FullSubcategory)
    (hZ : IsIso Z.obj.hom) (h0 : T.dimension Z = 0) :
    T.cycleClass Z 0 (Ch.fundamental Z) ≠ 0 := by
  intro h
  have h1 := T.integration_cycleClass_fundamental Z hZ h0
  rw [h] at h1
  simp at h1

/-- The cycle class map is compatible with exterior products:
`γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`. -/
theorem cycleClass_externalProduct
    [HasBinaryProducts ((SmoothProjective k).FullSubcategory)]
    (X Y : (SmoothProjective k).FullSubcategory) (r s : ℤ)
    (α : Ch.group X r) (β : Ch.group Y s) :
    T.cycleClass (X ⨯ Y) (r + s) (Ch.externalProduct r s α β) =
      (T.H (X ⨯ Y)).evenCup r s
        (T.pullback (prod.fst : X ⨯ Y ⟶ X) (2 * r) (T.cycleClass X r α))
        (T.pullback (prod.snd : X ⨯ Y ⟶ Y) (2 * s) (T.cycleClass Y s β)) := by
  rw [show Ch.externalProduct r s α β =
      Ch.mul r s (Ch.gysin (prod.fst : X ⨯ Y ⟶ X) r α)
        (Ch.gysin (prod.snd : X ⨯ Y ⟶ Y) s β) from rfl,
    T.cycleClass_mul, T.cycleClass_gysin, T.cycleClass_gysin]

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
