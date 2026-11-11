module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Formula
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of an external product along the second projection

Let `X` and `Y` be nonempty smooth projective varieties over `k`, equidimensional of dimensions
`d` and `e`.  The Poincaré-duality pushforward along the second projection

`pr_{2, *} : H^*(X × Y)(d + e) ⟶ H^*(Y)(e)`

integrates the first factor out of an external product: it sends `a × b = pr₁^*a ∪ pr₂^*b` to
`(∫_X a) b`, where `∫_X`, defined on the top degree `2d` only, is read as zero elsewhere.

This file works in the classical setting of
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup` (`k` algebraically closed, smooth
projective varieties, `F` of characteristic zero). Stacks 0FHC in the generality of the source,
over any field, for nonempty equidimensional smooth projective schemes and the data and axioms of
Section 0FHA, is `Stacks.WeilCohomology.WeilData.pushforward_snd_externalProduct` in
`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/SecondProjection.lean`.

## Main definitions

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.externalProduct`: the Künneth exterior
  product `a × b = pr₁^*a ∪ pr₂^*b`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.kunnethMap`: the map
  `⨁_{p + q = m} H^p(X) ⊗_F H^q(Y) ⟶ H^m(X × Y)` of axiom `(B)(a)`, in degree `m`.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.dimension_prod_eq`: the product of two
  such varieties is equidimensional of dimension `d + e`, derived from axiom `(B)(a)` and the
  Poincaré-duality package.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pullbackSnd_mul_externalProduct`: the
  identity `pr₂^*v ∪ (a × b) = (-1)^{jp} a × (v ∪ b)`, derived from multiplicativity of pullback
  and graded commutativity of the cup product.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_snd_externalProduct`: the
  formula `pr_{2, *}(a × b) = (∫_X a) b` for `a` of the top degree `2d`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward_snd_externalProduct_eq_zero`:
  the complementary clause, that `pr_{2, *}(a × b) = 0` when `a` is not of the top degree, which
  is the reading of `(∫_X a) b` outside the degree where `∫_X` is defined.

## Implementation notes

The data `(D1)`, `(D3)` and axiom `(A)` are the fields of
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`.  Axiom `(B)` is presented as explicit
arguments, this directory's convention for the source's "assume given `(D0)`-`(D3)` satisfying
`(A)` and `(B)`": `kunneth` is `(B)(a)`, that the Künneth map is an isomorphism, and
`integral_externalProduct` is `(B)(b)`, the factorization `∫_{X × Y} = ∫_X ⊗ ∫_Y` of the trace of
a product.  Nothing else is assumed.

In particular the two inputs that the source leaves implicit are *derived* here, not carried.

* The cup-product identity `pr₂^*v ∪ (a × b) = ± a × (v ∪ b)` is
  `pullbackSnd_mul_externalProduct`, obtained from the structure's own
  `PoincareDualityPushforwardSetup.pullback_mul` (multiplicativity of pullback) and
  `PoincareDualityPushforwardSetup.gradedComm` (graded commutativity) together with associativity
  of the cup product: `pr₂^*v` is moved past `pr₁^*a` at the cost of the Koszul sign `(-1)^{jp}`,
  and `pr₂^*v ∪ pr₂^*b = pr₂^*(v ∪ b)`.  In the application the first factor has the even degree
  `2d`, so the sign is `+1` and does not appear in the conclusion.
* Equidimensionality of the product, which the source records by writing `H^*(X × Y)(d + e)` and
  which is what makes `∫_{X × Y}` a functional on the degree where an exterior product of top
  classes lives, is `dimension_prod_eq`.  Its proof is the standard one: in degrees above
  `2d + 2e` every Künneth generator vanishes by `PoincareDualityPushforwardSetup.bounded`, so
  surjectivity of the Künneth map kills `H^{2 dim(X × Y)}(X × Y)`, which is `F` by `(D3)`; and the
  Künneth generator `a × c` of top classes is nonzero by injectivity, so `2d + 2e` is at most
  `2 dim(X × Y)` again by `bounded`.

Degree arithmetic goes through `ExternallyGraded.degreeCast`, as everywhere in this directory:
`2d + (2e - i)` and `2 dim(X × Y) - i` are the same integer written two ways.

Tate twists are absorbed into the grading, as in
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup` and hence in the sibling statements
Stacks 0FGT and 0FHB: the datum `(D0)` is a one-dimensional `F`-vector space, so a twist only
reindexes the graded pieces, and the structure's trace `∫_X` on the piece of degree `2 dim X` is
the source's `∫_X : H^{2d}(X)(d) ⟶ F`.  Thus the source's `H^*(X × Y)(d + e) ⟶ H^*(Y)(e)` is
`PoincareDualityPushforwardSetup.pushforward` for `pr₂`.

## References

* [Stacks Project, Tag 0FHC](https://stacks.math.columbia.edu/tag/0FHC)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGraded

open scoped DirectSum TensorProduct

universe u v w

namespace ExternallyGradedAlgebra

/-- Heterogeneously equal left factors of equal degrees have heterogeneously equal products with
a common right factor. -/
theorem mul_congr_left_heq {R : Type v} [CommRing R] {A : ExternallyGradedAlgebra.{v, w} R}
    {i i' j : ℤ} (h : i = i') {x : A.piece i} {y : A.piece i'} (hxy : x ≍ y) (z : A.piece j) :
    A.mul i j x z ≍ A.mul i' j y z := by
  subst h
  rw [eq_of_heq hxy]

end ExternallyGradedAlgebra

namespace ExternallyGraded

/-- Two transports of heterogeneously equal elements into the same graded piece agree. -/
theorem degreeCast_eq_degreeCast {R : Type v} [CommRing R] {P : ℤ → Type w}
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] {i i' j : ℤ} (h : i = j) (h' : i' = j)
    {x : P i} {y : P i'} (hxy : x ≍ y) :
    degreeCast (R := R) (X := P) h x = degreeCast (R := R) (X := P) h' y :=
  eq_of_heq ((degreeCast_heq (R := R) (X := P) h x).trans
    (hxy.trans (degreeCast_heq (R := R) (X := P) h' y).symm))

/-- The zero elements of two graded pieces of equal degree agree heterogeneously. -/
theorem zero_heq_zero {P : ℤ → Type w} [∀ n, Zero (P n)] {i j : ℤ} (h : i = j) :
    (0 : P i) ≍ (0 : P j) := by
  subst h
  rfl

end ExternallyGraded

namespace DifferentialGraded

/-- The Koszul sign of an even degree is `1`. -/
theorem gradedSign_two_mul {R : Type u} [Ring R] (n : ℤ) : gradedSign R (2 * n) = 1 := by
  rw [two_mul, gradedSign_add, gradedSign, ← pow_add, ← two_mul, pow_mul]
  simp

end DifferentialGraded

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  {X Y : (SmoothProjective k).FullSubcategory}

/-- The Künneth exterior product `(a, b) ↦ a × b = pr₁^*a ∪ pr₂^*b`, bilinearly. -/
noncomputable def PoincareDualityPushforwardSetup.externalProductMap [HasBinaryProduct X Y]
    (p q : ℤ) :
    (S.H X).piece p →ₗ[F] (S.H Y).piece q →ₗ[F] (S.H (X ⨯ Y)).piece (p + q) :=
  ((S.H (X ⨯ Y)).mul p q).compl₁₂ (S.pullback (prod.fst : X ⨯ Y ⟶ X) p)
    (S.pullback (prod.snd : X ⨯ Y ⟶ Y) q)

/-- The Künneth exterior product `a × b = pr₁^*a ∪ pr₂^*b` of a class on `X` of degree `p` and a
class on `Y` of degree `q`, a class on `X × Y` of degree `p + q`. -/
noncomputable def PoincareDualityPushforwardSetup.externalProduct [HasBinaryProduct X Y]
    (p q : ℤ) (a : (S.H X).piece p) (b : (S.H Y).piece q) : (S.H (X ⨯ Y)).piece (p + q) :=
  S.externalProductMap p q a b

/-- The exterior product is the cup product of the two pullbacks, by definition. -/
theorem PoincareDualityPushforwardSetup.externalProduct_eq_mul [HasBinaryProduct X Y]
    (p q : ℤ) (a : (S.H X).piece p) (b : (S.H Y).piece q) :
    S.externalProduct p q a b =
      (S.H (X ⨯ Y)).mul p q (S.pullback (prod.fst : X ⨯ Y ⟶ X) p a)
        (S.pullback (prod.snd : X ⨯ Y ⟶ Y) q b) :=
  rfl

/-- **The Künneth map in degree `m`**, the map of axiom `(B)(a)`: on the summand indexed by a
pair of degrees `(p, q)` with `p + q = m` it is `α ⊗ β ↦ pr₁^*α ∪ pr₂^*β`. -/
noncomputable def PoincareDualityPushforwardSetup.kunnethMap [HasBinaryProduct X Y] (m : ℤ) :
    (⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = m},
        (S.H X).piece pq.1.1 ⊗[F] (S.H Y).piece pq.1.2) →ₗ[F] (S.H (X ⨯ Y)).piece m :=
  DirectSum.toModule F _ _ fun pq =>
    (ExternallyGraded.degreeCast (R := F) (X := (S.H (X ⨯ Y)).piece) pq.2).comp
      (TensorProduct.lift (S.externalProductMap pq.1.1 pq.1.2))

/-- The Künneth map on the generator of the summand indexed by `(p, q)` is the exterior
product. -/
theorem PoincareDualityPushforwardSetup.kunnethMap_lof [HasBinaryProduct X Y] {m : ℤ}
    (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = m})
    (t : (S.H X).piece pq.1.1 ⊗[F] (S.H Y).piece pq.1.2) :
    S.kunnethMap m (DirectSum.lof F _ _ pq t) =
      ExternallyGraded.degreeCast (R := F) (X := (S.H (X ⨯ Y)).piece) pq.2
        (TensorProduct.lift (S.externalProductMap pq.1.1 pq.1.2) t) := by
  simp only [PoincareDualityPushforwardSetup.kunnethMap, DirectSum.toModule_lof,
    LinearMap.comp_apply]

/-- Above the degree `2 dim X + 2 dim Y` every Künneth generator already vanishes, because one of
its two factors lies above the top degree of its own variety. -/
theorem PoincareDualityPushforwardSetup.kunnethMap_eq_zero_of_lt [HasBinaryProduct X Y] {m : ℤ}
    (hm : 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) < m)
    (x : ⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = m},
      (S.H X).piece pq.1.1 ⊗[F] (S.H Y).piece pq.1.2) :
    S.kunnethMap m x = 0 := by
  refine DirectSum.induction_on x (by simp) (fun pq t ↦ ?_) (fun u u' hu hu' ↦ by simp [hu, hu'])
  rw [← DirectSum.lof_eq_of F, S.kunnethMap_lof]
  have ht : TensorProduct.lift (S.externalProductMap pq.1.1 pq.1.2) t = 0 := by
    refine TensorProduct.inductionOn t (fun a b ↦ ?_) (fun t t' h h' ↦ by simp [h, h'])
    rcases lt_or_ge (2 * (S.dimension X : ℤ)) pq.1.1 with h | h
    · rw [S.bounded X pq.1.1 (.inr h) a]
      simp
    · have hb : 2 * (S.dimension Y : ℤ) < pq.1.2 := by have := pq.2; omega
      rw [S.bounded Y pq.1.2 (.inr hb) b]
      simp
  rw [ht, map_zero]

/-- **An exterior product of top classes is nonzero**, by injectivity of the Künneth map
of axiom `(B)(a)`: the corresponding generator `a ⊗ c` is nonzero because the trace maps
separate it. -/
theorem PoincareDualityPushforwardSetup.externalProduct_top_ne_zero [HasBinaryProduct X Y]
    (kunneth : ∀ m, Function.Bijective (S.kunnethMap (X := X) (Y := Y) m))
    (a : (S.H X).piece (2 * (S.dimension X : ℤ)))
    (c : (S.H Y).piece (2 * (S.dimension Y : ℤ)))
    (ha : S.integration X a = 1) (hc : S.integration Y c = 1) :
    S.externalProduct (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ)) a c ≠ 0 := by
  intro hzero
  have htne : a ⊗ₜ[F] c ≠ 0 := by
    intro h
    have himg : (TensorProduct.lid F F)
        ((TensorProduct.map (S.integration X).toLinearMap (S.integration Y).toLinearMap)
          (a ⊗ₜ[F] c)) = 1 := by
      simp [ha, hc]
    rw [h] at himg
    simp at himg
  have hlof : DirectSum.lof F
      {pq : ℤ × ℤ // pq.1 + pq.2 = 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ)}
      (fun pq => (S.H X).piece pq.1.1 ⊗[F] (S.H Y).piece pq.1.2)
      ⟨(2 * (S.dimension X : ℤ), 2 * (S.dimension Y : ℤ)), rfl⟩ (a ⊗ₜ[F] c) = 0 := by
    refine (kunneth _).1 ?_
    rw [map_zero, S.kunnethMap_lof, TensorProduct.lift.tmul]
    exact hzero
  refine htne ?_
  simpa using congrArg (DirectSum.component F
    {pq : ℤ × ℤ // pq.1 + pq.2 = 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ)}
    (fun pq => (S.H X).piece pq.1.1 ⊗[F] (S.H Y).piece pq.1.2)
    ⟨(2 * (S.dimension X : ℤ), 2 * (S.dimension Y : ℤ)), rfl⟩) hlof

/-- **The product of `X` and `Y` is equidimensional of dimension `dim X + dim Y`**, derived
from axiom `(B)(a)` and the Poincaré-duality package, rather than assumed.  This is the content
of the source's notation `H^*(X × Y)(d + e)`, and it is what makes axiom `(B)(b)` meaningful: an
exterior product of top classes has degree `2 dim X + 2 dim Y`, while `∫_{X × Y}` is a functional
on the degree `2 dim(X × Y)`. -/
theorem PoincareDualityPushforwardSetup.dimension_prod_eq [HasBinaryProduct X Y]
    (kunneth : ∀ m, Function.Bijective (S.kunnethMap (X := X) (Y := Y) m)) :
    S.dimension (X ⨯ Y) = S.dimension X + S.dimension Y := by
  have hle : 2 * (S.dimension (X ⨯ Y) : ℤ) ≤
      2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) := by
    by_contra hcon
    have hlt := not_le.mp hcon
    obtain ⟨x, hx⟩ := (kunneth (2 * (S.dimension (X ⨯ Y) : ℤ))).2
      ((S.integration (X ⨯ Y)).symm 1)
    rw [S.kunnethMap_eq_zero_of_lt hlt x] at hx
    have : (1 : F) = 0 := by
      have := congrArg (S.integration (X ⨯ Y)) hx
      simpa using this.symm
    exact one_ne_zero this
  have hge : 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) ≤
      2 * (S.dimension (X ⨯ Y) : ℤ) := by
    by_contra hcon
    have hlt := not_le.mp hcon
    exact S.externalProduct_top_ne_zero kunneth ((S.integration X).symm 1)
      ((S.integration Y).symm 1) (by simp) (by simp)
      (S.bounded (X ⨯ Y) _ (.inr (by omega)) _)
  omega

/-- The exterior product respects transport of the degree of its right factor. -/
theorem PoincareDualityPushforwardSetup.externalProduct_degreeCast_heq [HasBinaryProduct X Y]
    (p : ℤ) {q q' : ℤ} (h : q = q') (a : (S.H X).piece p) (b : (S.H Y).piece q) :
    S.externalProduct p q' a (ExternallyGraded.degreeCast (R := F) h b) ≍
      S.externalProduct p q a b := by
  subst h
  rfl

/-- **Cup product with a class pulled back from the second factor.** For `v` of degree `j` on `Y`,
`a` of degree `p` on `X` and `b` of degree `q` on `Y`,

`pr₂^*v ∪ (a × b) = (-1)^{jp} a × (v ∪ b)`.

This is derived, not assumed: `pr₂^*v` is moved past `pr₁^*a` by graded commutativity of the cup
product, which produces the Koszul sign, and `pr₂^*v ∪ pr₂^*b = pr₂^*(v ∪ b)` is multiplicativity
of pullback. -/
theorem PoincareDualityPushforwardSetup.pullbackSnd_mul_externalProduct [HasBinaryProduct X Y]
    (j p q : ℤ) (v : (S.H Y).piece j) (a : (S.H X).piece p) (b : (S.H Y).piece q) :
    (S.H (X ⨯ Y)).mul j (p + q) (S.pullback (prod.snd : X ⨯ Y ⟶ Y) j v)
        (S.externalProduct p q a b) =
      gradedSign F (j * p) •
        ExternallyGraded.degreeCast (R := F) (show p + (j + q) = j + (p + q) by ring)
          (S.externalProduct p (j + q) a ((S.H Y).mul j q v b)) := by
  have hpb : S.pullback (prod.snd : X ⨯ Y ⟶ Y) (j + q) ((S.H Y).mul j q v b) =
      (S.H (X ⨯ Y)).mul j q (S.pullback (prod.snd : X ⨯ Y ⟶ Y) j v)
        (S.pullback (prod.snd : X ⨯ Y ⟶ Y) q b) :=
    S.pullback_mul (prod.snd : X ⨯ Y ⟶ Y) j q v b
  simp only [PoincareDualityPushforwardSetup.externalProduct_eq_mul, hpb]
  set A := S.H (X ⨯ Y) with hA
  set ν := S.pullback (prod.snd : X ⨯ Y ⟶ Y) j v with hν
  set α := S.pullback (prod.fst : X ⨯ Y ⟶ X) p a with hα
  set β := S.pullback (prod.snd : X ⨯ Y ⟶ Y) q b with hβ
  have key : A.mul j (p + q) ν (A.mul p q α β) ≍
      gradedSign F (j * p) • A.mul p (j + q) α (A.mul j q ν β) := by
    refine (A.mul_assoc j p q ν α β).symm.trans ?_
    refine (ExternallyGradedAlgebra.mul_congr_left_heq (A := A) (by ring)
      ((S.gradedComm (X ⨯ Y)).graded_comm j p ν α) β).trans ?_
    rw [map_smul, LinearMap.smul_apply]
    exact ExternallyGraded.scalar_heq (by ring) rfl (A.mul_assoc p j q α ν β)
  rw [← ExternallyGraded.degreeCast_smul]
  exact eq_of_heq (key.trans (ExternallyGraded.degreeCast_heq (R := F) _ _).symm)

/-- A class `x` on `X × Y` pushes forward to `z` as soon as `∫_{X × Y} (pr₂^*v ∪ x) = ∫_Y (v ∪ z)`
for every `v`, by perfectness of the Poincaré duality pairing on `Y`. -/
private theorem PoincareDualityPushforwardSetup.pushforward_snd_eq_of_integration_eq
    [HasBinaryProduct X Y] (i : ℤ)
    (x : (S.H (X ⨯ Y)).piece (2 * (S.dimension (X ⨯ Y) : ℤ) - i))
    (z : (S.H Y).piece (2 * (S.dimension Y : ℤ) - i))
    (h : ∀ v : (S.H Y).piece i,
      S.integration (X ⨯ Y)
          (ExternallyGraded.degreeCast (R := F)
            (show i + (2 * (S.dimension (X ⨯ Y) : ℤ) - i) = 2 * (S.dimension (X ⨯ Y) : ℤ) by omega)
            ((S.H (X ⨯ Y)).mul i (2 * (S.dimension (X ⨯ Y) : ℤ) - i)
              (S.pullback (prod.snd : X ⨯ Y ⟶ Y) i v) x)) =
        S.integration Y
          (ExternallyGraded.degreeCast (R := F)
            (show i + (2 * (S.dimension Y : ℤ) - i) = 2 * (S.dimension Y : ℤ) by omega)
            ((S.H Y).mul i (2 * (S.dimension Y : ℤ) - i) v z))) :
    S.pushforward (prod.snd : X ⨯ Y ⟶ Y) i x = z := by
  have hperf : ((S.H Y).tracePairing (S.dimension Y)
    (S.integration Y).toLinearMap i).IsPerfPair := S.perfect Y i
  refine (LinearMap.IsPerfPair.bijective_right ((S.H Y).tracePairing (S.dimension Y)
    (S.integration Y).toLinearMap i)).injective (LinearMap.ext fun v ↦ ?_)
  change (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i v _ =
    (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i v _
  rw [← S.integration_pullback_mul (prod.snd : X ⨯ Y ⟶ Y) i v]
  simpa only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using h v

/-- The Poincaré-duality pushforward along the second projection `pr₂ : X × Y ⟶ Y` integrates the
first factor out of an exterior product: for `a` of the top degree `2 dim X` on `X`,

`pr_{2, *}(a × b) = (∫_X a) b`.

This is the formula of Stacks 0FHC in the classical setting of
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup`: `k` algebraically closed, `F` of
characteristic zero, `X` and `Y` smooth projective varieties, and a trace map `∫_X` that is an
isomorphism. Stacks 0FHC itself, over any field and for nonempty equidimensional, possibly
disconnected, smooth projective schemes with the data and axioms of Section 0FHA, is
`Stacks.WeilCohomology.WeilData.pushforward_snd_externalProduct`.

Axiom `(B)` is the pair of explicit arguments `kunneth`, that the Künneth map is an isomorphism,
and `integral_externalProduct`, the factorization `∫_{X × Y} = ∫_X ⊗ ∫_Y`; the rest is the data
`(D1)`, `(D3)` and axiom `(A)` carried by `S`. -/
theorem PoincareDualityPushforwardSetup.pushforward_snd_externalProduct [HasBinaryProduct X Y]
    (kunneth : ∀ m, Function.Bijective (S.kunnethMap (X := X) (Y := Y) m))
    (integral_externalProduct : ∀ (c : (S.H X).piece (2 * (S.dimension X : ℤ)))
        (c' : (S.H Y).piece (2 * (S.dimension Y : ℤ))),
      S.integration (X ⨯ Y)
          (ExternallyGraded.degreeCast (R := F)
            (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) =
                2 * (S.dimension (X ⨯ Y) : ℤ) by
              rw [S.dimension_prod_eq kunneth]; push_cast; ring)
            (S.externalProduct (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ)) c c')) =
        S.integration X c * S.integration Y c')
    (i : ℤ) (a : (S.H X).piece (2 * (S.dimension X : ℤ)))
    (b : (S.H Y).piece (2 * (S.dimension Y : ℤ) - i)) :
    S.pushforward (prod.snd : X ⨯ Y ⟶ Y) i
        (ExternallyGraded.degreeCast (R := F)
          (show 2 * (S.dimension X : ℤ) + (2 * (S.dimension Y : ℤ) - i) =
              2 * (S.dimension (X ⨯ Y) : ℤ) - i by
            rw [S.dimension_prod_eq kunneth]; push_cast; ring)
          (S.externalProduct (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ) - i) a b)) =
      S.integration X a • b := by
  have hdim := S.dimension_prod_eq kunneth
  refine S.pushforward_snd_eq_of_integration_eq _ _ _ fun v ↦ ?_
  simp only [map_smul, smul_eq_mul]
  -- the left-hand side is `∫_{X × Y}` of `pr₂^*v ∪ (a × b)`, which the derived cup-product
  -- identity turns into the exterior product of `a` with `v ∪ b`
  have hcup := S.pullbackSnd_mul_externalProduct (X := X) (Y := Y) i
    (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ) - i) v a b
  rw [show i * (2 * (S.dimension X : ℤ)) = 2 * (i * (S.dimension X : ℤ)) by ring,
    gradedSign_two_mul, one_smul] at hcup
  have hleft : ExternallyGraded.degreeCast (R := F)
        (show i + (2 * (S.dimension (X ⨯ Y) : ℤ) - i) = 2 * (S.dimension (X ⨯ Y) : ℤ) by omega)
        ((S.H (X ⨯ Y)).mul i (2 * (S.dimension (X ⨯ Y) : ℤ) - i)
          (S.pullback (prod.snd : X ⨯ Y ⟶ Y) i v)
          (ExternallyGraded.degreeCast (R := F)
            (show 2 * (S.dimension X : ℤ) + (2 * (S.dimension Y : ℤ) - i) =
              2 * (S.dimension (X ⨯ Y) : ℤ) - i by omega)
            (S.externalProduct (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ) - i) a b))) =
      ExternallyGraded.degreeCast (R := F)
        (show 2 * (S.dimension X : ℤ) + 2 * (S.dimension Y : ℤ) =
          2 * (S.dimension (X ⨯ Y) : ℤ) by omega)
        (S.externalProduct (2 * (S.dimension X : ℤ)) (2 * (S.dimension Y : ℤ)) a
          (ExternallyGraded.degreeCast (R := F)
            (show i + (2 * (S.dimension Y : ℤ) - i) = 2 * (S.dimension Y : ℤ) by omega)
            ((S.H Y).mul i (2 * (S.dimension Y : ℤ) - i) v b))) := by
    refine ExternallyGraded.degreeCast_eq_degreeCast (R := F) _ _ ?_
    refine (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H (X ⨯ Y)) i
      (2 * (S.dimension X : ℤ) + (2 * (S.dimension Y : ℤ) - i))
      (2 * (S.dimension (X ⨯ Y) : ℤ) - i) (by omega) _ _).trans ?_
    rw [hcup]
    refine (ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_
    exact (S.externalProduct_degreeCast_heq (2 * (S.dimension X : ℤ)) (by omega) a _).symm
  rw [hleft, integral_externalProduct]

/-- The complementary clause of the formula `pr_{2, *}(a × b) = (∫_X a) b`: when `a` is not of
the top degree `2 dim X` the pushforward of the exterior product vanishes, which is that formula
read with `∫_X`, a functional on the top degree only, extended by zero.

This is in the classical setting of `Stacks.WeilCohomology.PoincareDualityPushforwardSetup`;
Stacks 0FHC in the generality of the source is
`Stacks.WeilCohomology.WeilData.pushforward_snd_externalProduct`.

Only Poincaré duality, axiom `(B)(a)` and the vanishing of cohomology outside `[0, 2 dim]` are
used; axiom `(B)(b)` does not enter, since the relevant exterior product is already zero. -/
theorem PoincareDualityPushforwardSetup.pushforward_snd_externalProduct_eq_zero
    [HasBinaryProduct X Y]
    (kunneth : ∀ m, Function.Bijective (S.kunnethMap (X := X) (Y := Y) m))
    (p q : ℤ) (hp : p ≠ 2 * (S.dimension X : ℤ))
    (a : (S.H X).piece p) (b : (S.H Y).piece q) :
    S.pushforward (prod.snd : X ⨯ Y ⟶ Y) (2 * (S.dimension (X ⨯ Y) : ℤ) - (p + q))
        (ExternallyGraded.degreeCast (R := F)
          (show p + q = 2 * (S.dimension (X ⨯ Y) : ℤ) -
            (2 * (S.dimension (X ⨯ Y) : ℤ) - (p + q)) by omega)
          (S.externalProduct p q a b)) = 0 := by
  have hdim := S.dimension_prod_eq kunneth
  set i := 2 * (S.dimension (X ⨯ Y) : ℤ) - (p + q) with hi
  refine S.pushforward_snd_eq_of_integration_eq _ _ _ fun v ↦ ?_
  simp only [map_zero]
  have hcup := S.pullbackSnd_mul_externalProduct (X := X) (Y := Y) i p q v a b
  -- the exterior product of `a` with `v ∪ b` vanishes: one of its two factors is already zero
  have hzero : S.externalProduct p (i + q) a ((S.H Y).mul i q v b) = 0 := by
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · have hvb : (S.H Y).mul i q v b = 0 := S.bounded Y (i + q) (.inr (by omega)) _
      simp only [PoincareDualityPushforwardSetup.externalProduct_eq_mul, hvb, map_zero]
    · have ha : a = 0 := S.bounded X p (.inr hgt) a
      simp only [PoincareDualityPushforwardSetup.externalProduct_eq_mul, ha, map_zero,
        LinearMap.zero_apply]
  rw [hzero, map_zero, smul_zero] at hcup
  have hmul : (S.H (X ⨯ Y)).mul i (2 * (S.dimension (X ⨯ Y) : ℤ) - i)
      (S.pullback (prod.snd : X ⨯ Y ⟶ Y) i v)
      (ExternallyGraded.degreeCast (R := F)
        (show p + q = 2 * (S.dimension (X ⨯ Y) : ℤ) - i by omega)
        (S.externalProduct p q a b)) = 0 := by
    refine eq_of_heq ?_
    refine (ExternallyGradedAlgebra.mul_degreeCast_heq (A := S.H (X ⨯ Y)) i (p + q)
      (2 * (S.dimension (X ⨯ Y) : ℤ) - i) (by omega) _ _).trans ?_
    rw [hcup]
    exact ExternallyGraded.zero_heq_zero (by omega)
  rw [hmul, map_zero, map_zero]

end Stacks.WeilCohomology

end
